/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Monads.State

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "状态" =>
%%%
tag := "state-monads"
%%%

{tech (key := "State monads")}[状态单子]提供对可变值的访问。
底层实现可以使用元组模拟可变性，也可以使用 {name}`ST.Ref` 之类的机制确保发生修改。
即便是使用元组的实现，由于 Lean 会在值具有唯一引用时采用修改，其运行时实际上也可能使用修改；但这要求编程风格优先使用 {name}`modify` 和 {name}`modifyGet`，而非 {name}`get` 和 {name}`set`。

# 通用状态接口
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--State--General-State-API"
%%%

{zhdocstring MonadState ZhDoc.Monads.State.MonadState}

{zhdocstring get ZhDoc.Monads.State.get}

{zhdocstring modify ZhDoc.Monads.State.modify}

{zhdocstring modifyGet ZhDoc.Monads.State.modifyGet}

{zhdocstring getModify ZhDoc.Monads.State.getModify}

{zhdocstring MonadStateOf ZhDoc.Monads.State.MonadStateOf}

{zhdocstring getThe ZhDoc.Monads.State.getThe}

{zhdocstring modifyThe ZhDoc.Monads.State.modifyThe}

{zhdocstring modifyGetThe ZhDoc.Monads.State.modifyGetThe}

# 基于元组的状态单子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--State--Tuple-Based-State-Monads"
%%%

```lean -show
variable {α σ : Type u}
```

基于元组的状态单子把状态类型为 {lean}`σ`、产生 {lean}`α` 类型值的计算表示为函数：它接受初始状态，并产生一个值与最终状态组成的二元组，例如 {lean}`σ → α × σ`。
{name}`Monad` 操作会在计算中正确地传递状态。

{zhdocstring StateM ZhDoc.Monads.State.StateM}

{zhdocstring StateT ZhDoc.Monads.State.StateT}

{zhdocstring StateT.run ZhDoc.Monads.State.StateT.run}

{zhdocstring StateT.get ZhDoc.Monads.State.StateT.get}

{zhdocstring StateT.set ZhDoc.Monads.State.StateT.set}

{zhdocstring StateT.orElse ZhDoc.Monads.State.StateT.orElse}

{zhdocstring StateT.failure ZhDoc.Monads.State.StateT.failure}

{zhdocstring StateT.run' ZhDoc.Monads.State.StateT.run'}

{zhdocstring StateT.bind ZhDoc.Monads.State.StateT.bind}

{zhdocstring StateT.modifyGet ZhDoc.Monads.State.StateT.modifyGet}

{zhdocstring StateT.lift ZhDoc.Monads.State.StateT.lift}

{zhdocstring StateT.map ZhDoc.Monads.State.StateT.map}

{zhdocstring StateT.pure ZhDoc.Monads.State.StateT.pure}

# 延续传递风格的状态单子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--State--State-Monads-in-Continuation-Passing-Style"
%%%

延续传递风格的状态单子把有状态计算表示为函数：对于任意类型，该函数接受初始状态和一个延续（建模为函数），而延续接受一个值和更新后的状态。
这种类型的一个例子是 {lean}`(δ : Type u) → σ → (α → σ → δ) → δ`，不过 {lean}`StateCpsT` 是可应用于任意单子的变换器。
延续传递风格的状态单子与基于元组的状态单子具有不同的性能特征；对某些应用而言，值得对它们进行基准测试。


```lean -show
/-- info: (δ : Type u) → σ → (α → σ → Id δ) → δ -/
#check_msgs in
#reduce (types := true) StateCpsT σ Id α
```
{zhdocstring StateCpsT ZhDoc.Monads.State.StateCpsT}

{zhdocstring StateCpsT.lift ZhDoc.Monads.State.StateCpsT.lift}

{zhdocstring StateCpsT.runK ZhDoc.Monads.State.StateCpsT.runK}

{zhdocstring StateCpsT.run' ZhDoc.Monads.State.StateCpsT.run'}

{zhdocstring StateCpsT.run ZhDoc.Monads.State.StateCpsT.run}

# 基于可变引用的状态单子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--State--State-Monads-from-Mutable-References"
%%%

```lean -show
variable {m : Type → Type} {σ ω : Type} [STWorld σ m]
```

单子 {lean}`StateRefT σ m` 是专门的状态单子变换器；当 {lean}`m` 是可以提升 {name}`ST` 计算的单子时，便可使用它。
它使用 {name}`ST.Ref` 而非纯函数来实现 {name}`MonadState` 的操作。
这确保了运行时确实会使用修改。

{name}`ST` 和 {name}`EST` 需要一个幽灵类型参数，它与 {name}`runST` 的多态函数实参共同用于封装可变性。
与其要求把它作为变换器的参数，不如使用辅助类型类 {name}`STWorld`，直接从 {lean}`m` 传播该参数。

变换器本身被定义为{ref "syntax-ext"}[语法扩展]和{ref "elaborators"}[精译器]，而非普通函数。
这是因为 {name}`STWorld` 没有方法：它的存在只是为了把信息从内层单子传播到变换后的单子。
尽管如此，它的实例仍是项；保留这些实例可能导致类型不必要地增大。

{zhdocstring STWorld ZhDoc.Monads.State.STWorld}

:::syntax term (title := "`StateRefT`")
{lean}`StateRefT σ m` 的语法接受两个实参：

```grammar
StateRefT $_ $_
```

它的精译器会合成 {lean}`STWorld ω m` 的实例，以确保 {lean}`m` 支持可变引用。
发现 {lean}`ω` 的值后，它会生成项 {lean}`StateRefT' ω σ m`，并丢弃所合成的实例。
:::

{zhdocstring StateRefT' ZhDoc.Monads.State.StateRefT'}

{zhdocstring StateRefT'.get ZhDoc.Monads.State.StateRefT'.get}

{zhdocstring StateRefT'.set ZhDoc.Monads.State.StateRefT'.set}

{zhdocstring StateRefT'.modifyGet ZhDoc.Monads.State.StateRefT'.modifyGet}

{zhdocstring StateRefT'.run ZhDoc.Monads.State.StateRefT'.run}

{zhdocstring StateRefT'.run' ZhDoc.Monads.State.StateRefT'.run'}

{zhdocstring StateRefT'.lift ZhDoc.Monads.State.StateRefT'.lift}
