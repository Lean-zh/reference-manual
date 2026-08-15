/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Monads.Core

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "提升单子" =>
%%%
tag := "lifting-monads"
file := "Lifting-Monads"
%%%

::::keepEnv

```lean -show
variable {m m' n : Type u → Type v} [Monad m] [Monad m'] [Monad n] [MonadLift m n]
variable {α β : Type u}
```

当一个单子的能力至少与另一个单子相当时，后者的动作便可用于期望前者动作的上下文中。
这称为将动作从一个单子{deftech (key := "lift")}_提升_到另一个单子。
有可用的提升时，Lean 会自动插入它们；提升由类型类 {name}`MonadLift` 定义。
自动单子提升会在通用的{tech (key := "coercion")}[强制转换]机制之前尝试。

{zhdocstring MonadLift Manual.ZhDocString.Monads.Core.MonadLift}

单子之间的{tech (key := "lift")}[提升]具有自反性和传递性：
 * 任意单子都能运行自己的动作。
 * 从 {lean}`m` 到 {lean}`m'` 的提升与从 {lean}`m'` 到 {lean}`n` 的提升可以复合，得到从 {lean}`m` 到 {lean}`n` 的提升。
辅助类型类 {name}`MonadLiftT` 通过 {name}`MonadLift` 实例的自反传递闭包构造提升。
用户不应定义新的 {name}`MonadLiftT` 实例；不过，当多态函数需要在用户提供的某个单子中运行多个单子的动作时，它很适合作为该函数的实例隐式参数。

{zhdocstring MonadLiftT Manual.ZhDocString.Monads.Core.MonadLiftT}

```lean -show
section
variable {m : Type → Type u}
```

:::example "函数签名中的单子提升"
函数 {name}`IO.withStdin` 具有以下签名：
```signature
IO.withStdin.{u} {m : Type → Type u} {α : Type}
  [Monad m] [MonadFinally m] [MonadLiftT BaseIO m]
  (h : IO.FS.Stream) (x : m α) :
  m α
```
由于它不要求参数严格位于 {name}`IO` 中，因此可用于许多单子，其函数体也无需局限于 {name}`IO`。
实例隐式参数 {lean}`MonadLiftT BaseIO m` 允许使用 {name}`MonadLift` 的自反传递闭包来组装提升。
:::

```lean -show
end
```


当期望类型为 {lean}`n β` 的项，但提供的项类型为 {lean}`m α`，且两种类型并非定义相等时，Lean 会先尝试插入提升和强制转换，再报告错误。
可能有以下几种情况：
 1. 如果 {lean}`m` 和 {lean}`n` 能统一为同一个单子，那么 {lean}`α` 和 {lean}`β` 并不相同。
    此时不需要单子提升，但必须对单子中的值进行{tech (key := "coercion")}[强制转换]。
    如果找到了适当的强制转换，就会插入对 {name}`Lean.Internal.coeM` 的调用，其签名如下：
    ```signature
    Lean.Internal.coeM.{u, v} {m : Type u → Type v} {α β : Type u}
      [(a : α) → CoeT α a β] [Monad m]
      (x : m α) :
      m β
    ```
 2. 如果 {lean}`α` 和 {lean}`β` 可以统一，那么不同的是两个单子。
    此时需要单子提升，将类型为 {lean}`m α` 的表达式变换为 {lean}`n α`。
    如果 {lean}`m` 可以提升到 {lean}`n`（即存在 {lean}`MonadLiftT m n` 的实例），就会插入对 {name}`liftM` 的调用；它是 {name}`MonadLiftT.monadLift` 的别名。
    ```signature
    liftM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      [self : MonadLiftT m n] {α : Type u} :
      m α → n α
    ```
 3. 如果 {lean}`m` 与 {lean}`n`、{lean}`α` 与 {lean}`β` 都无法统一，但 {lean}`m` 可以提升到 {lean}`n`，且 {lean}`α` 可以{tech (key := "coercion")}[强制转换]为 {lean}`β`，那么可以组合一次提升与一次强制转换。
    具体做法是插入对 {name}`Lean.Internal.liftCoeM` 的调用：
    ```signature
    Lean.Internal.liftCoeM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      {α β : Type u}
      [MonadLiftT m n] [(a : α) → CoeT α a β] [Monad n]
      (x : m α) :
      n β
    ```

顾名思义，{name}`Lean.Internal.coeM` 和 {name}`Lean.Internal.liftCoeM` 属于实现细节，并非公共 API 的一部分。
在最终生成的项中，出现的 {name}`Lean.Internal.coeM`、{name}`Lean.Internal.liftCoeM` 和强制转换都会被展开。

::::

::::keepEnv
:::example "提升 `IO` 单子"
存在 {lean}`MonadLift BaseIO IO` 的实例，因此任意 `BaseIO` 动作也可以在 `IO` 中运行：
```lean
def fromBaseIO (act : BaseIO α) : IO α := act
```
在幕后，系统插入了 {name}`liftM`：
```lean (name := fromBase)
#check fun {α} (act : BaseIO α) => (act : IO α)
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
:::
::::

:::::keepEnv
::::example "提升经过变换的单子"
标准库的大多数{tech (key := "monad transformers")}[单子变换器]也有 {name}`MonadLift` 实例，因此无需额外工作，便可在经过变换的单子中使用基础单子动作。
例如，状态单子动作可以跨越读取器变换器和异常变换器进行提升，从而自由混用兼容的单子：
```lean -keep
def incrBy (n : Nat) : StateM Nat Unit := modify (· + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```

禁用提升会导致错误：
```lean (name := noLift) +error
set_option autoLift false

def incrBy (n : Nat) : StateM Nat Unit := modify (. + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```
```leanOutput noLift
Type mismatch
  incrBy __do_lift✝
has type
  StateM Nat Unit
but is expected to have type
  ReaderT Nat (ExceptT String (StateM Nat)) Unit
```

::::
:::::


将选项 {option}`autoLift` 设为 {lean}`false` 可以禁用自动提升。

{zhOptionDocs autoLift Manual.ZhDocString.Monads.Core.autoLift}

# 反向提升
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Lifting-Monads--Reversing-Lifts"
%%%

```lean -show
variable {m n : Type u → Type v} {α ε : Type u}
```

单子提升并不总足以组合单子。
单子提供的许多操作都是高阶的，会接收_同一个单子中_的动作作为参数。
即使把这些操作提升到更强大的单子中，它们的实参仍受限于原单子。

有两个类型类支持这种“反向提升”：{name}`MonadFunctor` 和 {name}`MonadControl`。
{lean}`MonadFunctor m n` 的实例说明如何把 {lean}`m` 中的完全多态函数解释到 {lean}`n` 中。
这个多态函数必须适用于_所有_类型 {lean}`α`：其类型为 {lean}`{α : Type u} → m α → n α`。
可以认为这样的函数或许会产生效应，但不能依据所提供的具体值来产生效应。
{lean}`MonadControl m n` 的实例说明如何把 {lean}`m` 中的任意动作解释到 {lean}`n` 中，同时提供一个“反向解释器”，让该 {lean}`m` 动作能够运行 {lean}`n` 动作。

## 单子函子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Lifting-Monads--Reversing-Lifts--Monad-Functors"
%%%

{zhdocstring MonadFunctor Manual.ZhDocString.Monads.Core.MonadFunctor}

{zhdocstring MonadFunctorT Manual.ZhDocString.Monads.Core.MonadFunctorT}

## 使用 `MonadControl` 进行可逆提升
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Lifting-Monads--Reversing-Lifts--Reversible-Lifting-with--MonadControl"
%%%

{zhdocstring MonadControl Manual.ZhDocString.Monads.Core.MonadControl}

{zhdocstring MonadControlT Manual.ZhDocString.Monads.Core.MonadControlT}

{zhdocstring control Manual.ZhDocString.Monads.Core.control}

{zhdocstring controlAt Manual.ZhDocString.Monads.Core.controlAt}


::::keepEnv
:::example "异常与提升"
一个例子是 {name}`Except.tryCatch`：
```signature
Except.tryCatch.{u, v} {ε : Type u} {α : Type v}
  (ma : Except ε α) (handle : ε → Except ε α) :
  Except ε α
```
它的两个参数都位于 {lean}`Except ε` 中。
{name}`MonadLift` 可以提升处理器的整个应用。
函数 {lean}`getBytes` 使用状态和异常从 {lean}`Nat` 数组中提取各个字节；为了明确展示其结构，编写时没有使用 {keywordOf Lean.Parser.Term.do}`do` 记法或自动提升。
```lean
set_option autoLift false

def getByte (n : Nat) : Except String UInt8 :=
  if n < 256 then
    pure n.toUInt8
  else throw s!"Out of range: {n}"

def getBytes (input : Array Nat) :
    StateT (Array UInt8) (Except String) Unit := do
  input.forM fun i =>
    liftM (Except.tryCatch (some <$> getByte i) fun _ => pure none) >>=
      fun
        | some b => modify (·.push b)
        | none => pure ()
```

```lean (name := getBytesEval1)
#eval getBytes #[1, 58, 255, 300, 2, 1000000] |>.run #[] |>.map (·.2)
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
{name}`getBytes` 使用提升后的动作所返回的 `Option` 来表示所需的状态更新。
如果对内部动作有多种响应方式，例如保存已处理的异常，这种做法很快就会变得难以驾驭。
理想情况下，应当直接在 {name}`tryCatch` 调用内部执行状态更新。


然而，尝试保存字节和已处理的异常并不可行，因为 {name}`Except.tryCatch` 的实参类型为 {lean}`Except String Unit`：
```lean +error (name := getBytesErr) -keep
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    liftM
      (Except.tryCatch
        (getByte i >>= fun b =>
         modifyThe (Array UInt8) (·.push b))
        fun e =>
          modifyThe (Array String) (·.push e))
```
```leanOutput getBytesErr
failed to synthesize instance of type class
  MonadStateOf (Array String) (Except String)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

因为 {name}`StateT` 有一个 {name}`MonadControl` 实例，所以可以用 {name}`control` 代替 {name}`liftM`。
它为内部动作提供外部单子的解释器。
对于 {name}`StateT`，该解释器期望内部单子返回一个包含更新后状态的元组，并负责提供初始状态以及从元组中提取更新后的状态。

```lean
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    control fun run =>
      (Except.tryCatch
        (getByte i >>= fun b =>
         run (modifyThe (Array UInt8) (·.push b))))
        fun e =>
          run (modifyThe (Array String) (·.push e))
```

```lean (name := getBytesEval2)
#eval
  getBytes' #[1, 58, 255, 300, 2, 1000000]
  |>.run #[] |>.run #[]
  |>.map (fun (((), bytes), errs) => (bytes, errs))
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
```
:::
::::
