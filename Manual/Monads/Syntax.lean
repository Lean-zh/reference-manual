/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
-- set_option trace.SubVerso.Highlighting.Code true

set_option guard_msgs.diff true

#doc (Manual) "语法" =>
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax"
file := "Syntax"
%%%

Lean 通过特殊语法支持使用函子、应用函子和单子进行编程：
 * 为最常用的操作提供了中缀运算符。
 * 一种称为 {tech (key := "do-notation")}[{keywordOf Lean.Parser.Term.do}`do` 记法]的嵌入式语言，允许在单子中编写程序时使用命令式语法。

# 中缀运算符
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--Infix-Operators"
%%%

中缀运算符主要适用于较小的表达式，或不存在 {lean}`Monad` 实例的情况。

## 函子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--Infix-Operators--Functors"
%%%

```lean -show
section FOps
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {x : f α}
```
{name}`Functor.map` 有两个中缀运算符。

:::syntax term (title := "函子运算符")
{lean}`g <$> x` 是 {lean}`Functor.map g x` 的简写。
```grammar
$_ <$> $_
```

{lean}`x <&> g` 是 {lean}`Functor.map g x` 的简写。
```grammar
$_ <&> $_
```
:::

```lean -show
example : g <$> x = Functor.map g x := by rfl
example : x <&> g = Functor.map g x := by rfl
end FOps
```

## 应用函子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--Infix-Operators--Applicative-Functors"
%%%

```lean -show
section AOps
variable {f : Type u → Type v} [Applicative f] [Alternative f] {α β : Type u} {g : f (α → β)} {x e1 e e' : f α} {e2 : f β}
```

:::syntax term (title := "应用函子运算符")
{lean}`g <*> x` 是 {lean}`Seq.seq g (fun () => x)` 的简写。
插入该函数是为了延迟求值，因为控制流可能不会到达此参数。
```grammar
$_ <*> $_
```

{lean}`e1 *> e2` 是 {lean}`SeqRight.seqRight e1 (fun () => e2)` 的简写。
```grammar
$_ *> $_
```

{lean}`e1 <* e2` 是 {lean}`SeqLeft.seqLeft e1 (fun () => e2)` 的简写。
```grammar
$_ <* $_
```
:::

许多应用函子还通过 {name}`Alternative` 类型类支持失败与恢复。
这个类也有一个中缀运算符。

:::syntax term (title := "备选运算符")
{lean}`e <|> e'` 是 {lean}`OrElse.orElse e (fun () => e')` 的简写。
插入该函数是为了延迟求值，因为控制流可能不会到达此参数。
```grammar
$_ <|> $_
```
:::


```lean -show
example : g <*> x = Seq.seq g (fun () => x) := by rfl
example : e1 *> e2 = SeqRight.seqRight e1 (fun () => e2) := by rfl
example : e1 <* e2 = SeqLeft.seqLeft e1 (fun () => e2) := by rfl
example : (e <|> e') = (OrElse.orElse e (fun () => e')) := by rfl
end AOps
```

:::::keepEnv
```lean
structure User where
  name : String
  favoriteNat : Nat
def main : IO Unit := pure ()
```
::::example "`Functor` 与 `Applicative` 的中缀运算符"
函数式编程中一种常见的惯用法，是通过 {name}`Functor.map` 和 {name}`Seq.seq` 将纯函数应用于某个带效果的语境中。
函数通过 `<$>` 应用于一系列实参，各实参之间用 `<*>` 分隔。

在此示例中，{lean}`main` 的函数体使用这一惯用法来应用构造函数 {name}`User.mk`。
:::ioExample
```ioLean
def getName : IO String := do
  IO.println "What is your name?"
  return (← (← IO.getStdin).getLine).trimAsciiEnd.copy

partial def getFavoriteNat : IO Nat := do
  IO.println "What is your favorite natural number?"
  let line ← (← IO.getStdin).getLine
  if let some n := line.trimAscii.copy.toNat? then
    return n
  else
    IO.println "Let's try again."
    getFavoriteNat

structure User where
  name : String
  favoriteNat : Nat
deriving Repr

def main : IO Unit := do
  let user ← User.mk <$> getName <*> getFavoriteNat
  IO.println (repr user)
```
使用以下输入运行时：
```stdin
A. Lean User
None
42
```
会产生以下输出：
```stdout
What is your name?
What is your favorite natural number?
Let's try again.
What is your favorite natural number?
{ name := "A. Lean User", favoriteNat := 42 }
```
:::

::::
:::::

## 单子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--Infix-Operators--Monads"
%%%

单子主要通过 {tech (key := "do-notation")}[{keywordOf Lean.Parser.Term.do}`do` 记法]使用。
不过，有时用运算符描述单子计算会更方便。

```lean -show
section MOps
variable {m : Type u → Type v} [Monad m] {α β : Type u} {act : m α} {f : α → m β} {g : β → m γ}
```

:::syntax term (title := "单子运算符")

{lean}`act >>= f` 是 {lean}`Bind.bind act f` 的语法。
```grammar
$_ >>= $_
```

类似地，反向运算符 {lean}`f =<< act` 也是 {lean}`Bind.bind act f` 的语法。
```grammar
$_ =<< $_
```

Kleisli 复合运算符 {name}`Bind.kleisliRight` 和 {name}`Bind.kleisliLeft` 也有中缀形式。
```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

:::

```lean -show
example : act >>= f = Bind.bind act f := by rfl
example : f =<< act = Bind.bind act f := rfl
example : f >=> g = Bind.kleisliRight f g := by rfl
example : g <=< f = Bind.kleisliLeft g f := by rfl
end MOps
```


# `do` 记法
%%%
tag := "do-notation"
%%%

单子主要通过 {deftech (key := "do-notation")}[{keywordOf Lean.Parser.Term.do}`do` 记法]使用；这是一种以命令式风格编程的嵌入式语言。
它为依次执行带效果的操作、提前返回、局部可变变量、循环和异常处理提供了熟悉的语法。
所有这些功能都会翻译为 {lean}`Monad` 类型类的操作，其中少数功能还需要 {lean}`ForIn` 等类型类的额外实例，以规定如何遍历容器。
有关 {keywordOf Lean.Parser.Term.do}`do` 记法设计的更多细节，请参阅 {citet doUnchained}[]。

{keywordOf Lean.Parser.Term.do}`do` 项由关键字 {keywordOf Lean.Parser.Term.do}`do` 后接一系列 {deftech (key := "do elements")}_{keywordOf Lean.Parser.Term.do}`do` 元素_组成。

:::syntax term (title := "`do` 记法")
```grammar
do $stmt*
```
{keywordOf Lean.Parser.Term.do}`do` 中的元素可以用分号分隔；否则，每个元素应各占一行，并且缩进量相同。
:::

```lean -show
section
variable {m : Type → Type} [Monad m] {α β γ: Type} {e1 : m Unit} {e : β} {es : m α}
```

## 顺序计算
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--do--Notation--Sequential-Computations"
%%%

{tech (key := "do-element")}[{keywordOf Lean.Parser.Term.do}`do` 元素]的一种形式是项。

:::syntax Lean.Parser.Term.doSeqItem (title := "`do` 记法中的项")
```grammar
$e:term
```
:::


一个项后接一系列元素时，会被翻译为对 {name}`bind` 的使用；具体而言，{lean}`do e1; es` 会被翻译为 {lean}`e1 >>= fun () => do es`。


:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元素
  * 去糖
*
  * ```leanTerm
    do
    e1
    es
    ```
  * ```leanTerm
    e1 >>= fun () => do es
    ```
:::

```lean -show -keep
def ex1a := do e1; es
def ex1b := e1 >>= fun () => do es
example : @ex1a = @ex1b := by rfl
```

也可以为该项的计算结果命名，以便在后续步骤中使用。
这通过 {keywordOf Lean.Parser.Term.doLet}`let` 完成。

```lean -show
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```

:::syntax Lean.Parser.Term.doSeqItem (title := "`do` 记法中的数据依赖")
{keywordOf Lean.Parser.Term.do}`do` 块中的单子 {keywordOf Lean.Parser.Term.doLet}`let` 绑定有两种形式。
第一种将一个标识符绑定到结果，并可附带类型标注：
```grammar
let $x:ident$[:$e]? ← $e:term
```
第二种将一个模式绑定到结果。
以 `|` 开头的后备子句规定了模式与结果不匹配时的行为。
```grammar
let $x:term ← $e:term
  $[| $e]?
```
:::
这种语法也会被翻译为对 {name}`bind` 的使用。
{lean}`do let x ← e1; es` 会被翻译为 {lean}`e1 >>= fun x => do es`，而后备子句会被翻译为默认模式匹配。
{keywordOf Lean.Parser.Term.doLet}`let` 也可以使用标准定义语法 `:=`，而非 `←`。
这表示纯定义，而非单子定义：
:::syntax Lean.Parser.Term.doSeqItem (title := "`do` 记法中的局部定义")
```grammar
let $v := $e:term
```
:::
{lean}`do let x := e; es` 会被翻译为 {lean}`let x := e; do es`。

:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元素
  * 去糖
*
  * ```leanTerm
    do
    let x ← e1
    es
    ```
  * ```leanTerm
    e1 >>= fun x =>
      do es
    ```
*
  * ```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
  * ```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
*
  * ```leanTerm
    do
    let x := e
    es
    ```
  * ```leanTerm
    let x := e
    do es
    ```
:::

```lean -show -keep
-- 测试去糖结果
def ex1a := do
    let x ← e1
    es
def ex1b :=
    e1 >>= fun x =>
      do es
example : @ex1a = @ex1b := by rfl


def ex2a :=
    do
    let some x ← e1?
      | fallback
    es

def ex2b :=
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
example : @ex2a = @ex2b := by rfl

def ex3a :=
    do
    let x := e
    es
def ex3b :=
    let x := e
    do es
example : @ex3a = @ex3b := by rfl
```
在 {keywordOf Lean.Parser.Term.do}`do` 块中，`←` 可以用作前缀运算符。
它所作用的表达式会被一个新变量替换，并在当前步骤之前用 {name}`bind` 绑定该变量。
这样就能在原本可能需要纯值的位置使用单子效果，同时仍然区分对带效果计算的_描述_与对其效果的实际_执行_。
多个 `←` 按从左到右、从内到外的顺序处理。

::::figure "嵌套动作去糖示例"
:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元素示例
  * 去糖
*
  * ```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
  * ```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
*
  * ```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
  * ```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
:::
::::

```lean -show -keep
-- 测试去糖结果
def ex1a := do
  f (← e1) (← e2)
  es
def ex1b := do
  let x ← e1
  let y ← e2
  f x y
  es
example : @ex1a = @ex1b := by rfl
def ex2a := do
  let x := g (← h (← e1))
  es
def ex2b := do
  let y ← e1
  let z ← h y
  let x := g z
  es
example : @ex2a = @ex2b := by rfl
```

除了便利地支持具有数据依赖的顺序计算外，{keywordOf Lean.Parser.Term.do}`do` 记法还支持在局部加入多种效果，包括提前返回、局部可变状态以及可提前终止的循环。
这些效果通过变换整个 {keywordOf Lean.Parser.Term.do}`do` 块来实现，其方式类似于{tech (key := "monad transformers")}[单子变换器]，而不是通过局部去糖实现。

## 提前返回
%%%
tag := "early-return"
%%%

提前返回会立即以给定值终止计算。
该值从包含它的最近 {keywordOf Lean.Parser.Term.do}`do` 块返回；但这个块未必由最近的 `do` 关键字引入。
确定 {keywordOf Lean.Parser.Term.do}`do` 块范围的规则在{ref "closest-do-block"}[专门的一节]中介绍。

:::syntax Lean.Parser.Term.doSeqItem (title := "提前返回")
```grammar
return $e
```

```grammar
return
```
:::

并非所有单子都包含提前返回。
因此，当 {keywordOf Lean.Parser.Term.do}`do` 块包含 {keywordOf Lean.Parser.Term.doReturn}`return` 时，需要改写代码来模拟这一效果。
在单子 {lean}`m` 中使用提前返回来计算 {lean}`α` 类型值的程序，可以视为单子 {lean}`ExceptT α m α` 中的程序：提前返回的值走异常路径，普通返回则不走。
随后，外层处理器可以返回任一路径产生的值。
在内部，{keywordOf Lean.Parser.Term.do}`do` 精译器执行的翻译与此非常相似。

单独使用时，{keywordOf Lean.Parser.Term.doReturn}`return` 是 {keywordOf Lean.Parser.Term.doReturn}`return`​` `​{lean}`()` 的简写。

## 局部可变状态
%%%
tag := "let-mut"
%%%

局部可变状态是无法逸出其定义所在 {keywordOf Lean.Parser.Term.do}`do` 块的可变状态。
{keywordOf Lean.Parser.Term.doLet}`let mut` 绑定器引入局部可变绑定。
:::syntax Lean.Parser.Term.doSeqItem (title := "局部可变性")
可变绑定既可以用纯计算初始化，也可以用单子计算初始化：
```grammar
let mut $x := $e
```
```grammar
let mut $x ← $e
```

类似地，它们既可以用纯值更新，也可以用单子计算的结果更新：
```grammar (of := Lean.Parser.Term.doReassign)
$x:ident$[: $_]?  := $e:term
```
```grammar (of := Lean.Parser.Term.doReassign)
$x:term$[: $_]? := $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:ident$[: $_]? ← $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:term ← $e:term
  $[| $e]?
```
:::

这些局部可变绑定不如{tech (key := "state monad")}[状态单子]强大，因为它们在词法作用域之外不可变；这也使其更易于推理。
当 {keywordOf Lean.Parser.Term.do}`do` 块包含可变绑定时，{keywordOf Lean.Parser.Term.do}`do` 精译器会以类似 {lean}`StateT` 的方式变换表达式：构造一个新单子，并用正确的值将其初始化。

## 控制结构
%%%
tag := "do-control-structures"
%%%

有一些 {keywordOf Lean.Parser.Term.do}`do` 元素对应于 Lean 的大多数项级控制结构。
当它们作为 {keywordOf Lean.Parser.Term.do}`do` 块中的一个步骤出现时，会被解释为 {keywordOf Lean.Parser.Term.do}`do` 元素而不是项。
控制结构的每个分支都是一系列 {keywordOf Lean.Parser.Term.do}`do` 元素，而不是一个项；其中一些在语法上比对应的项更灵活。

:::syntax Lean.Parser.Term.doSeqItem (title := "条件语句")
在 {keywordOf Lean.Parser.Term.do}`do` 块中，{keywordOf Lean.Parser.Term.doIf}`if` 语句可以省略 {keywordOf Lean.Parser.Term.doIf}`else` 分支。
省略 {keywordOf Lean.Parser.Term.doIf}`else` 分支等价于以 {name}`pure`{lean}` ()` 作为该分支的内容。
```grammar
if $[$h :]? $e then
  $e*
$[else
  $_*]?
```
:::

从语法上说，{keywordOf Lean.Parser.Term.doIf}`then` 分支不能省略。
对于这类情况，{keywordOf Lean.Parser.Term.doUnless}`unless` 仅在条件为假时执行其主体。
{keywordOf Lean.Parser.Term.doUnless}`unless` 中的 {keywordOf Lean.Parser.Term.do}`do` 是其语法的一部分，不会引入嵌套的 {keywordOf Lean.Parser.Term.do}`do` 块。
:::syntax Lean.Parser.Term.doSeqItem (title := "反向条件语句")
```grammar
unless $e do
  $e*
```
:::


在 {keywordOf Lean.Parser.Term.do}`do` 块中使用 {keywordOf Lean.Parser.Term.doMatch}`match` 时，每个分支都被视为同一块的一部分。
除此之外，它等价于 {keywordOf Lean.Parser.Term.match}`match` 项。
:::syntax Lean.Parser.Term.doSeqItem (title := "模式匹配")
```grammar
match $[$[$h :]? $e],* with
  $[| $t,* => $e*]*
```
:::


## 迭代
%%%
tag := "monad-iteration-syntax"
%%%

在 {keywordOf Lean.Parser.Term.do}`do` 块中，{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环可用于遍历数据结构。
循环体是包含它的 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，因此可以使用提前返回和可变变量等局部效果。

:::syntax Lean.Parser.Term.doSeqItem (title := "遍历集合")
```grammar
for $[$[$h :]? $x in $y],* do
  $e*
```
:::

{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环至少需要一个规定如何迭代的子句；该子句由可选的成员关系证明名称及其后的冒号（`:`）、要绑定的模式、关键字 {keywordOf Lean.Parser.Term.doFor}`in` 和一个集合项组成。
该模式可以只是一个{tech (key := "identifier")}[标识符]，但必须能匹配集合中的任意元素；此处的模式不能用作隐式过滤器。
还可以用逗号分隔并提供更多子句。
各集合会同时迭代；任一集合耗尽元素时，迭代即停止。

:::example "同时遍历多个集合"
同时遍历多个集合时，任一集合耗尽元素，迭代即停止。
```lean (name := earlyStop)
#eval Id.run do
  let mut v := #[]
  for x in [0:43], y in ['a', 'b'] do
    v := v.push (x, y)
  return v
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
:::

::::keepEnv
:::example "使用 {keywordOf Lean.Parser.Term.doFor}`for` 遍历数组索引"

使用 {keywordOf Lean.Parser.Term.doFor}`for` 遍历数组的有效索引时，为成员关系证明命名，可以使搜索数组索引未越界证明的策略成功。
```lean -keep
def satisfyingIndices
    (p : α → Prop) [DecidablePred p]
    (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```

省略假设名称会导致数组查找失败，因为上下文中没有证明迭代变量处于指定范围内的证据。

```lean -keep -show
-- 测试
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
m : Type → Type
inst✝¹ : Monad m
α β γ : Type
e1✝ : m Unit
e : β
es : m α
e1 : m β
e1? : m (Option β)
fallback : m α
e2 : m γ
f : β → γ → m Unit
g : γ → α
h : β → m γ
p : α → Prop
inst✝ : DecidablePred p
xs : Array α
out✝ : Array Nat := #[]
i : Nat
out : Array Nat := __s✝
⊢ i < xs.size
-/
#check_msgs in
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
:::
::::

:::::keepEnv
::::leanSection

使用 `for` 循环的迭代会被翻译为对 `ForIn.forIn` 的使用；它类似于 `ForM.forM`，但增加了对局部修改和提前终止的支持。
{name}`ForIn.forIn` 接收局部可变状态的初始值、一个单子动作以及要遍历的集合作为参数。
传给 {name}`ForIn.forIn` 的单子动作以当前状态为参数，并在单子 {lean}`m` 中执行动作后返回 {name}`ForInStep.yield` 或 {name}`ForInStep.done`：前者表示应使用更新后的一组局部可变值继续迭代，后者表示执行了 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doReturn}`return`。
迭代完成时，{name}`ForIn.forIn` 返回各局部可变值的最终值。

循环的具体去糖方式取决于其主体如何使用状态和提前终止。
下面是一些示例：
```lean -show
axiom «<B>» : Type u
axiom «<b>» : β
variable [Monad m] (xs : Coll) [ForIn m Coll α] [instMem : Membership α Coll] [ForIn' m Coll α instMem]
variable (f : α → β → m β) (f' : (x : α) → x ∈ xs → β → m β)

macro "…" : term => `((«<b>» : β))
```

:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元素
  * 去糖
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.done b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.done b
    es
    ```
:::
::::
:::::


只要条件保持为真，{keywordOf Lean.doElemWhile_Do_}`while` 循环的主体就会重复执行。
可以在未标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数中使用它们编写无限循环。
这是因为 {keywordOf Lean.Parser.Command.declaration}`partial` 修饰符只适用于被定义函数自身导致的不终止或无限递归，而不适用于它所调用的函数所导致的情况。
{keywordOf Lean.doElemWhile_Do_}`while` 循环的翻译依赖一个单独的辅助函数。

:::syntax Lean.Parser.Term.doSeqItem (title := "条件循环")
```grammar
while $e do
  $e*
```
```grammar
while $h : $e do
  $e*
```
:::

{keywordOf Lean.doElemRepeat__Until_}`repeat`-{keywordOf Lean.doElemRepeat__Until_}`until` 循环的主体总会至少执行一次。
每次迭代后都会检查条件；条件为_假_时继续循环。
条件变为真时，迭代停止。

:::syntax Lean.Parser.Term.doSeqItem (title := "后测试循环")
```grammar
repeat
  $e*
until $_
```
:::


{keywordOf Lean.doElemRepeat_}`repeat` 循环的主体会重复执行，直至执行 {keywordOf Lean.Parser.Term.doBreak}`break` 语句。
与 {keywordOf Lean.doElemWhile_Do_}`while` 循环一样，这些循环也可用于未标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数。

:::syntax Lean.Parser.Term.doSeqItem (title := "无条件循环")
```grammar
repeat
  $e*
```
:::

{keywordOf Lean.Parser.Term.doContinue}`continue` 语句会跳过最近外层 {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 或 {keywordOf Lean.Parser.Term.doFor}`for` 循环主体的剩余部分，进入下一次迭代。
{keywordOf Lean.Parser.Term.doBreak}`break` 语句会终止最近外层的 {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 或 {keywordOf Lean.Parser.Term.doFor}`for` 循环，使迭代停止。

:::syntax Lean.Parser.Term.doSeqItem (title := "循环控制语句")
```grammar
continue
```
```grammar
break
```
:::

除了 {keywordOf Lean.Parser.Term.doBreak}`break`，循环始终可以由当前单子中的效果终止。
从循环中抛出异常会终止循环。

:::example "在 {lean}`Option` 单子中终止循环"
{name}`Alternative` 类的 {name}`failure` 方法可用于终止 {name}`Option` 单子中原本会无限运行的循环。

```lean (name := natBreak)
#eval show Option Nat from do
  let mut i := 0
  repeat
    if i > 1000 then failure
    else i := 2 * (i + 1)
  return i
```
```leanOutput natBreak
none
```
:::

## 识别 `do` 块
%%%
tag := "closest-do-block"
%%%

{keywordOf Lean.Parser.Term.do}`do` 记法的许多功能都会影响{deftech (key := "current do block")}[当前 {keywordOf Lean.Parser.Term.do}`do` 块]。
具体而言，提前返回会中止当前块，使其求值为返回值；而可变绑定只能在其定义所在的块中修改。
要理解这些功能，需要精确定义何谓处于“同一”块中。

在实际操作中，可以使用 Lean 语言服务器检查这一点。
当光标位于 {keywordOf Lean.Parser.Term.doReturn}`return` 语句上时，对应的 {keywordOf Lean.Parser.Term.do}`do` 关键字会高亮显示。
尝试在同一 {keywordOf Lean.Parser.Term.do}`do` 块之外修改可变绑定会产生错误消息。

:::figure "高亮显示 {keywordOf Lean.Parser.Term.do}`do`"

![从 return 高亮显示 do](/static/screenshots/do-return-hl-1.png)

![出现错误时从 return 高亮显示 do](/static/screenshots/do-return-hl-2.png)
:::

规则如下：
 * 直接嵌套在开启某个块的 {keywordOf Lean.Parser.Term.do}`do` 关键字下的每个元素都属于该块。
 * 如果一个 {keywordOf Lean.Parser.Term.do}`do` 关键字本身是外层 {keywordOf Lean.Parser.Term.do}`do` 块中的元素，那么直接嵌套在该关键字下的每个元素都属于外层块。
 * {keywordOf Lean.Parser.Term.doIf}`if`、{keywordOf Lean.Parser.Term.doMatch}`match` 或 {keywordOf Lean.Parser.Term.doUnless}`unless` 元素各分支中的元素，与包含它们的控制结构属于同一 {keywordOf Lean.Parser.Term.do}`do` 块。作为 {keywordOf Lean.Parser.Term.doUnless}`unless` 语法一部分的 {keywordOf Lean.Parser.Term.doUnless}`do` 关键字不会引入新的 {keywordOf Lean.Parser.Term.do}`do` 块。
 * {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 和 {keywordOf Lean.Parser.Term.doFor}`for` 主体中的元素，与包含它们的循环属于同一 {keywordOf Lean.Parser.Term.do}`do` 块。作为 {keywordOf Lean.doElemWhile_Do_}`while` 和 {keywordOf Lean.Parser.Term.doFor}`for` 语法一部分的 {keywordOf Lean.Parser.Term.doFor}`do` 关键字不会引入新的 {keywordOf Lean.Parser.Term.do}`do` 块。

```lean -show
-- 测试嵌套的 `do` 规则

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return

/--
warning: This `do` element and its control-flow region are dead code. Consider removing it.
---
info: ((), 6)
-/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return
  set 7
  return

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  if true then
    set 6
    do return
  set 7
  return
```

::::keepEnv
:::example "嵌套的 `do` 与分支"
以下示例输出 {lean}`6` 而不是 {lean}`7`：
```lean (name := nestedDo)
def test : StateM Nat Unit := do
  set 5
  if true then
    set 6
    do return
  set 7
  return

#eval test.run 0
```
```leanOutput nestedDo
((), 6)
```

这是因为 {keywordOf Lean.Parser.Term.doIf}`if` 下的 {keywordOf Lean.Parser.Term.doReturn}`return` 语句与其直接父级属于同一 {keywordOf Lean.Parser.Term.do}`do`，而该父级本身又与 {keywordOf Lean.Parser.Term.doIf}`if` 属于同一 {keywordOf Lean.Parser.Term.do}`do`。
如果作为其他 {keywordOf Lean.Parser.Term.do}`do` 块中元素出现的 {keywordOf Lean.Parser.Term.do}`do` 块会创建新块，那么该示例将输出 {lean}`7`。
:::
::::

```lean -show
end
```

```lean -show
-- 本节测试
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) PUnit.{1} α e1 fun (__r : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#check_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#check_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) PUnit.{1} α (f __do_lift __do_lift_1) fun (__r : PUnit.{1}) =>
      es : m α
-/
#check_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#check_msgs in
#check do let x := g (← h (← e1)); es

end


```

## 用于迭代的类型类
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Syntax--do--Notation--Type-Classes-for-Iteration"
%%%

若要在没有成员关系证明的 {keywordOf Lean.Parser.Term.doFor}`for` 循环中使用，集合必须实现 {name}`ForIn` 类型类。
额外实现 {lean}`ForIn'` 后，还可以使用带成员关系证明的 {keywordOf Lean.Parser.Term.doFor}`for` 循环。

{docstring ForIn}

{docstring ForIn'}

{docstring ForInStep}

{docstring ForInStep.value}

{docstring ForM}

{docstring ForM.forIn}
