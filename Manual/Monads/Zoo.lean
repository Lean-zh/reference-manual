/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Manual.Monads.Zoo.State
import Manual.Monads.Zoo.Reader
import Manual.Monads.Zoo.Except
import Manual.Monads.Zoo.Combined
import Manual.Monads.Zoo.Id
import Manual.Monads.Zoo.Option

/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
-- set_option trace.SubVerso.Highlighting.Code true

#doc (Manual) "单子的种类" =>
%%%
tag := "monad-varieties"
%%%

{lean}`IO` 单子具有非常多的作用，用于编写需要与外部世界交互的程序。
{ref "io"}[专门的一节]对它进行了介绍。
使用 {lean}`IO` 的程序本质上是黑箱：它们通常并不特别适合验证。

许多算法只需少得多的作用便能最方便地表达。
这些作用往往可以模拟；例如，可以通过传递同时包含程序值和状态的元组来模拟可变状态。
这些模拟出来的作用更容易进行形式化推理，因为它们是用普通代码而非新的语言原语定义的。

标准库提供了用于处理常见作用的抽象。
许多常用作用可归入少数几类：

: {deftech (key := "State monads")}[状态单子]具有可变状态

  若计算可以访问某些可能被计算的其他部分修改的数据，它就使用了_可变状态_。
  状态有多种实现方式，详见{ref "state-monads"}[状态单子]一节，并由 {name}`MonadState` 类型类刻画。

: {deftech (key := "Reader monads")}[读取器单子]是参数化计算

  大多数编程语言都存在能够读取上下文所提供参数值的计算，但许多将状态和异常作为一等特性的语言并没有内置定义新参数化计算的设施。
  通常，调用这类计算时会向它提供一个参数值，有时还可以局部覆盖该值。
  参数值具有_动态作用域_：使用的是调用栈中最近提供的值。
  可以在一连串函数调用中原样传递某个值来模拟它们；但这种技巧会使代码更难阅读，还可能不慎把错误的值传给后续调用。
  也可以借助可变状态来模拟，但必须谨慎约束状态的修改。
  维护一个参数、并可能允许在调用栈某段中覆盖该参数的单子称为_读取器单子_。
  读取器单子由 {lean}`MonadReader` 类型类刻画。
  此外，允许局部覆盖参数值的读取器单子由 {lean}`MonadWithReader` 类型类刻画。

: {deftech (key := "Exception monads")}[异常单子]具有异常

  可能以异常值提前终止的计算使用_异常_。
  通常用和类型对其建模：一个构造器表示正常终止，另一个构造器表示因错误而提前终止。
  {ref "exception-monads"}[异常单子]一节介绍了异常单子，它们由 {name}`MonadExcept` 类型类刻画。


# 单子类型类

使用 {lean}`MonadState` 和 {lean}`MonadExcept` 这样的类型类，可以让客户端代码对单子具有多态性。
结合自动提升，程序便能在许多不同的单子中复用，也更能适应重构。

必须注意，单子中的作用并不一定只有一种交互方式。
例如，同时具有状态和异常的单子在抛出异常时可能回滚状态变更，也可能不回滚。
如果这会影响函数的正确性，就应使用更具体的签名。

::::keepEnv
:::example "作用的顺序"
函数 {name}`sumNonFives` 使用状态单子对列表内容求和，遇到 {lean}`5` 时提前终止。
```lean
def sumNonFives {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Unit := do
  for x in xs do
    if x == 5 then
      throw "Five was encountered"
    else
      modify (· + x)
```

在一种单子中运行它，会返回遇到 {lean}`5` 时的状态：
```lean (name := exSt)
#eval
  sumNonFives (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run 0
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```

在另一种单子中，状态会被丢弃：
```lean (name := stEx)
#eval
  sumNonFives (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run 0
```
```leanOutput stEx
Except.error "Five was encountered"
```

在第二种情况下，异常处理器会把状态回滚到 {keywordOf Lean.Parser.Term.termTry}`try` 开始时的值。
因此，下列函数并不正确：
```lean
/-- 计算列表中首个 5 之前前缀的元素之和。 -/
def sumUntilFive {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Nat := do
  MonadState.set 0
  try
    sumNonFives xs
  catch _ =>
    pure ()
  get
```

在一种单子中，答案正确：
```lean (name := exSt2)
#eval
  sumUntilFive (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run' 0
```
```leanOutput exSt2
Except.ok 10
```

在另一种单子中，答案不正确：
```lean (name := stEx2)
#eval
  sumUntilFive (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run' 0
```
```leanOutput stEx2
Except.ok 0
```
:::
::::

一个单子可以支持同一种作用的多个版本。
例如，可以同时有可变的 {lean}`Nat` 和可变的 {lean}`String`，也可以有两个独立的读取器参数。
只要它们类型不同，就应当能方便地访问二者。
在典型用法中，类型类所重载的某些单子操作拥有可供{tech (key := "synthesis")}[实例合成]使用的类型信息，而另一些操作则没有。
例如，传给 {name MonadState.set}`set` 的参数决定了要使用的状态类型，而 {name MonadState.get}`get` 不接受这样的参数。
当存在多个状态时，可以利用 {name MonadState.set}`set` 应用中的类型信息选择正确实例。这表明可变状态的类型应当是输入参数或{tech (key := "semi-output parameter")}[半输出参数]，以便用它选择实例。
另一方面，{name MonadState.get}`get` 的使用中缺少类型信息，这表明可变状态的类型在 {lean}`MonadState` 中应当是{tech (key := "output parameter")}[输出参数]，从而让类型类合成根据单子本身确定状态类型。

许多作用类型类都提供两个版本，以此解决这种两难。
带半输出参数的版本以后缀 `-Of` 命名，其操作会按需显式接收类型。
例如 {name}`MonadStateOf`、{name}`MonadReaderOf` 和 {name}`MonadExceptOf`。
带显式类型参数的操作以 `-The` 结尾，例如 {name}`getThe`、{name}`readThe` 和 {name}`tryCatchThe`。
带输出参数的版本名称不加修饰。
标准库会根据典型用法中推断行为的优劣，从各类型类的 `-Of` 版本和无修饰版本中混合导出操作。

:::table +header
  *
   * 操作
   * 来源类型类
   * 说明
  *
   * {name}`get`
   * {name}`MonadState`
   * 输出参数改善类型推断
  *
   * {name}`set`
   * {name}`MonadStateOf`
   * 半输出参数使用 {name}`set` 实参中的类型信息
  *
   * {name}`modify`
   * {name}`MonadState`
   * 需要输出参数，以允许不带标注的函数
  *
   * {name}`modifyGet`
   * {name}`MonadState`
   * 需要输出参数，以允许不带标注的函数
  *
   * {name}`read`
   * {name}`MonadReader`
   * 实参没有提供类型信息，因此需要输出参数
  *
   * {name}`readThe`
   * {name}`MonadReaderOf`
   * 半输出参数使用所提供的类型引导合成
  *
   * {name}`withReader`
   * {name}`MonadWithReader`
   * 输出参数免去了在函数上添加类型标注的需要
  *
   * {name}`withTheReader`
   * {name}`MonadWithReaderOf`
   * 半输出参数使用所提供的类型引导合成
  *
   * {name}`throw`
   * {name}`MonadExcept`
   * 输出参数使异常可以使用构造器点记法
  *
   * {name}`throwThe`
   * {name}`MonadExceptOf`
   * 半输出参数使用所提供的类型引导合成
  *
   * {name}`tryCatch`
   * {name}`MonadExcept`
   * 输出参数使异常可以使用构造器点记法
  *
   * {name}`tryCatchThe`
   * {name}`MonadExceptOf`
   * 半输出参数使用所提供的类型引导合成
:::

```lean -show
example : @get = @MonadState.get := by rfl
example : @set = @MonadStateOf.set := by rfl
example {inst} (f : σ → σ) : @modify σ m inst f = @MonadState.modifyGet σ m inst PUnit fun (s : σ) => (PUnit.unit, f s) := by rfl
example : @modifyGet = @MonadState.modifyGet := by rfl
example : @read = @MonadReader.read := by rfl
example : @readThe = @MonadReaderOf.read := by rfl
example : @withReader = @MonadWithReader.withReader := by rfl
example : @withTheReader = @MonadWithReaderOf.withReader := by rfl
example : @throw = @MonadExcept.throw := by rfl
example : @throwThe = @MonadExceptOf.throw := by rfl
example : @tryCatch = @MonadExcept.tryCatch := by rfl
example : @tryCatchThe = @MonadExceptOf.tryCatch := by rfl
```

:::example "状态类型"
状态单子 {name}`M` 有两个独立状态：一个 {lean}`Nat` 和一个 {lean}`String`。
```lean
abbrev M := StateT Nat (StateM String)
```

由于 {name}`get` 是 {name}`MonadState.get` 的别名，状态类型是输出参数。
这意味着 Lean 会自动选择状态类型；在此例中，它选择最外层单子变换器的状态类型：
```lean (name := getM)
#check (get : M _)
```
```leanOutput getM
get : M Nat
```

因为状态类型是输出参数，所以只能使用最外层的状态。
```lean (name := getMStr) +error
#check (get : M String)
```
```leanOutput getMStr
failed to synthesize instance of type class
  MonadState String M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

使用 {name}`MonadStateOf` 中的 {name}`getThe` 显式提供状态类型，就可以读取两种状态。
```lean (name := getTheM)
#check ((getThe String, getThe Nat) : M String × M Nat)
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```

两种类型的状态都可以设置，因为状态类型在 {name}`MonadStateOf` 上是{tech (key := "semi-output parameter")}[半输出参数]。
```lean (name := setNat)
#check (set 4 : M Unit)
```
```leanOutput setNat
set 4 : M PUnit
```

```lean (name := setStr)
#check (set "Four" : M Unit)
```
```leanOutput setStr
set "Four" : M PUnit
```

:::


# 单子变换器
%%%
tag := "monad-transformers"
%%%

{deftech (key := "monad transformer")}_单子变换器_是一个函数：给它一个单子，它会返回一个新单子。
通常，新单子具有原单子的全部作用，并附加一些作用。

```lean -show
variable {α : Type u} (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)

```
单子变换器由以下部分组成：
 * 函数 {lean}`T`，从已有单子构造新单子的类型
 * `run` 函数，将 {lean}`T m α` 转换为 {lean}`m` 的某种形式；它通常需要额外参数，并返回 {lean}`m` 下更具体的类型
 * {lean}`[Monad m] → Monad (T m)` 的实例，使变换后的单子可作为单子使用
 * {lean}`MonadLift` 的实例，使原单子的代码可在变换后的单子中使用
 * 如果可能，还包括 {lean}`MonadControl m (T m)` 的实例，使变换后单子中的动作可在原单子中使用

通常，单子变换器还会提供一个或多个类型类的实例，用以描述它所引入的作用。
变换器的 {name}`Monad` 和 {name}`MonadLift` 实例使得在变换后的单子中编写代码切实可行，而类型类实例则允许将变换后的单子用于多态函数。

::::keepEnv
```lean -show
universe u v
variable {m : Type u → Type v} {α : Type u}
```
:::example "恒等单子变换器"
恒等单子变换器既不增加也不移除被变换单子的能力。
它的定义是适当特化后的恒等函数：
```lean
def IdT (m : Type u → Type v) : Type u → Type v := m
```
同样，{name IdT.run}`run` 函数不需要额外实参，只返回一个 {lean}`m α`：
```lean
def IdT.run (act : IdT m α) : m α := act
```

该单子实例依赖被变换单子的单子实例，并通过{tech (key := "type ascriptions")}[类型注明]选择它：
```lean
instance [Monad m] : Monad (IdT m) where
  pure x := (pure x : m _)
  bind x f := (x >>= f : m _)
```

因为 {lean}`IdT m` 在定义上等于 {lean}`m`，所以 {lean}`MonadLift m (IdT m)` 实例无需修改被提升的动作：
```lean
instance : MonadLift m (IdT m) where
  monadLift x := x
```

{lean}`MonadControl` 实例也同样简单。
```lean
instance [Monad m] : MonadControl m (IdT m) where
  stM α := α
  liftWith f := f (fun x => Id.run <| pure x)
  restoreM v := v
```

:::
::::

Lean 标准库为许多不同的单子提供了变换器版本，包括 {name}`ReaderT`、{name}`ExceptT` 和 {name}`StateT`，以及使用其他表示的变体，如 {name}`StateCpsT`、{name StateRefT'}`StateRefT` 和 {name}`ExceptCpsT`。
此外，{name}`EStateM` 单子等价于组合 {name}`ExceptT` 与 {name}`StateT`，但它可以使用更专门的表示来提升性能。

{include 0 Monads.Zoo.Id}

{include 0 Monads.Zoo.State}

{include 0 Monads.Zoo.Reader}

{include 0 Monads.Zoo.Option}

{include 0 Monads.Zoo.Except}

{include 0 Monads.Zoo.Combined}
