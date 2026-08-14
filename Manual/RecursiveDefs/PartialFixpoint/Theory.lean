/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity
import Manual.ZhDocString.RecursiveDefs

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "理论与构造" =>
%%%
tag := "partial-fixpoint-theory"
%%%

该构造建立在 Knaster–Tarski 定理的一个变体之上：在链完备偏序中，每个单调函数都有最小不动点。

所需理论位于 `Lean.Order` 命名空间中。
它并非旨在成为通用的序理论结果库。
相反，`Lean.Order` 中的定义和定理仅用作 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 功能的实现细节，应将其视为可能随时变更而不另行通知的私有 API。

偏序和链完备偏序的概念分别由类型类 {name}`Lean.Order.PartialOrder` 和 {name}`Lean.Order.CCPO` 表示。

{zhdocstring Lean.Order.PartialOrder ZhDoc.RecursiveDefs.Order.PartialOrder}

{zhdocstring Lean.Order.CCPO ZhDoc.RecursiveDefs.Order.CCPO}

```lean -show
section
open Lean.Order
variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β] (f : α → β) (x y : α)
```

如果函数保持偏序关系，它就是单调的。
也就是说，若 {lean}`x ⊑ y`，则 {lean}`f x ⊑ f y`。
运算符 `⊑` 表示 {name}`Lean.Order.PartialOrder.rel`。

{zhdocstring Lean.Order.monotone ZhDoc.RecursiveDefs.Order.monotone}

可使用 {name}`fix` 取得单调函数的不动点；如 {name}`fix_eq` 所示，它确实构造了一个不动点。

{zhdocstring Lean.Order.fix ZhDoc.RecursiveDefs.Order.fix}

{zhdocstring Lean.Order.fix_eq ZhDoc.RecursiveDefs.Order.fix_eq}

:::paragraph

为了构造偏不动点，Lean 首先合成合适的 {name}`CCPO` 实例。

```lean -show
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```

* 如果函数的结果类型有专用实例，例如 {name}`Option` 的 {name}`instCCPOOption`，就将其与函数类型的实例 {name}`instCCPOPi` 一起使用，为整个函数类型构造实例。

* 否则，如果可以证明函数类型由见证 {lean}`w` 居留，则使用包装类型 {lean}`FlatOrder w` 的实例 {name}`FlatOrder.instCCPO`。在此序中，{lean}`w` 是最小元素，所有其他元素彼此不可比。

```lean -show
end
```

:::

接下来，将函数定义右侧的递归调用抽象出来；它们会成为 {name}`fix` 的参数 `f`。单调性要求由 {tactic}`monotonicity` 策略解决，该策略以语法驱动的方式应用组合式单调性引理。

```lean -show
section
set_option linter.unusedVariables false
variable {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β] (more : (x : α) → β) (x : α)

local macro "…" x:term:arg "…" : term => `(more $x)
```

该策略通过以下步骤解决形如 {lean}`monotone (fun x => … x …)` 的目标：

* 当不再依赖 {lean}`x` 时，应用 {name}`monotone_const`。
* 对 {keywordOf Lean.Parser.Term.match}`match` 表达式分情况。
* 对 {keywordOf termIfThenElse}`if` 表达式分情况。
* 如果值和类型均不依赖 {lean}`x`，则将 {keywordOf Lean.Parser.Term.let}`let` 表达式移入上下文。
* 当值和类型确实依赖 {lean}`x` 时，对 {keywordOf Lean.Parser.Term.let}`let` 表达式进行 zeta 归约。
* 应用以 {attr}`partial_fixpoint_monotone` 标注的引理

```lean -show
end
```

系统注册了以下单调性引理；它们应当允许递归调用出现在给定高阶函数中以 `·` 标示的参数位置（但不允许出现在以 `_` 标示的其他参数位置）。


{monotonicityLemmas}

这里描述的序理论框架也是{ref "coinductive-predicates"}[余归纳与归纳谓词]的基础。
对于取值于 {lean}`Prop` 的函数，{name}`Lean.Order.CompleteLattice` 实例同时提供最小与最大不动点，从而允许使用 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 和 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 子句进行定义。
