/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600


#doc (Manual) "`coinductive` 命令" =>
%%%
tag := "coinductive-command"
%%%

{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令提供一种定义{tech (key := "lattice-theoretic coinductive predicate")}[余归纳谓词]的语法，其形式与 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明的语法相仿。
无需使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 编写递归函数，而是像归纳类型那样以构造器来编写声明。

:::syntax command (title := "余归纳谓词")
```grammar
coinductive $_ $_* : $_ where
  $_*
```
{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令通过指定构造器来定义余归纳谓词。
它只能用于定义谓词，即取值于 {lean}`Prop` 的类型。
:::

{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令定义的谓词与对应的 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 定义相同。
此外，它还会生成构造器和分情况分析原理，很像普通的 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明。

:::example "通过 `coinductive` 定义余归纳谓词"
前述示例中的谓词 {lean}`InfSeq` 也可以等价地使用 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 命令定义：

```lean
variable (α : Type)

coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```

这会生成一个构造器和一个{tech (key := "coinduction principle")}[余归纳原理]：

```signature
InfSeq.step (α : Type) (r : α → α → Prop) {a b : α} :
  r a b → InfSeq α r b → InfSeq α r a
```

```signature
InfSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ b, r a b ∧ pred b) →
  ∀ (a : α), pred a → InfSeq α r a
```

还会生成一个分情况分析原理：
```signature
InfSeq.casesOn (α : Type) (r : α → α → Prop)
    {motive : (a : α) → InfSeq α r a → Prop} {a : α} (t : InfSeq α r a) :
  (∀ {a b} (a_1 : r a b) (a_2 : InfSeq α r b),
    motive a (InfSeq.step α r a_1 a_2)) →
  motive a t
```

在证明中，可以通过 {tactic}`cases` 策略使用分情况分析：

```lean
theorem InfSeq.casesOnTest (r : α → α → Prop)
    (a : α) : InfSeq α r a → ∃ b, r a b := by
  intro h
  cases h
  case step b _ hr => exists b
```
:::


# 精译
%%%
tag := "coinductive-elaboration"
%%%

在底层，{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令会分若干步进行精译。
首先，将其当作普通的 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明进行处理。
不过，在向内核注册类型之前，会创建一个{deftech (key := "flat inductive")}_平坦归纳类型_（也称为_函子_）：构造器前提中余归纳谓词的每次递归出现都会替换为一个显式参数。


:::example "平坦归纳类型"
此示例使用无限序列的余归纳规约：
```lean -show
variable (α : Type)
```
```lean
coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```
对于 {lean}`InfSeq`，生成的平坦归纳类型为：

```signature
InfSeq._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
```

其构造器使用谓词参数取代递归调用：

```lean (name := printFunctor) -keep
set_option pp.proofs true in
#print InfSeq._functor
```

```leanOutput printFunctor
inductive InfSeq._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
InfSeq._functor.step : ∀ (α : Type) (r : α → α → Prop) (InfSeq._functor.call : α → Prop) {a b : α},
  r a b → InfSeq._functor.call b → InfSeq._functor α r InfSeq._functor.call a
```
:::

随后构造等价的{deftech (key := "existential form")}_存在形式_，将每个构造器表示为依赖积（即存在量词与合取）的析取。
此形式用于单调性检查以及生成易读的余归纳原理。

:::example "存在形式"
```lean -show
variable (α : Type)
```
```lean
coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```

```lean (name := printExist)
set_option pp.proofs true in
#print InfSeq._functor.existential
```

```leanOutput printExist
def InfSeq._functor.existential : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop :=
fun α r InfSeq._functor.call a => ∃ b, r a b ∧ InfSeq._functor.call b
```

这两种形式由一个等价定理联系起来：

```lean (name := checkExistEquiv) -keep
#check @InfSeq._functor.existential_equiv
```
```leanOutput checkExistEquiv
InfSeq._functor.existential_equiv : ∀ (α : Type) (r : α → α → Prop) (InfSeq._functor.call : α → Prop) (a : α),
  InfSeq._functor α r InfSeq._functor.call a ↔ ∃ b, r a b ∧ InfSeq._functor.call b
```
:::

随后，使用{ref "partial-fixpoint"}[偏不动点]机制和 {name}`Lean.Order.ReverseImplicationOrder` 完备格实例，将存在形式注册为余归纳谓词。
利用平坦归纳类型与存在形式之间的对应关系，系统会像处理普通归纳类型一样生成构造器和分情况分析消去器。

:::paragraph
对于名为 `P` 的余归纳谓词，会生成以下声明：

 * `P._functor`：{tech (key := "flat inductive")}[平坦归纳类型]
 * `P._functor.existential`：{tech (key := "existential form")}[存在形式]
 * `P._functor.existential_equiv`：两种形式之间的等价定理
 * `P.functor_unfold`：联系余归纳谓词与其平坦归纳类型的定理
 * 构造器（例如 `P.step`）：与声明中的各构造器相对应
 * `P.casesOn`：分情况分析原理
 * `P.coinduct`：{tech (key := "coinduction principle")}[余归纳原理]
:::

# 余归纳与归纳互递归块
%%%
tag := "mutual-coinductive-syntax"
%%%

在包含 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 定义的{tech (key := "mutual block")}[互递归块]中，{keywordOf Lean.Parser.Command.inductive}`inductive` 关键字会被重新解释：它不会注册为普通的内核归纳类型，而是通过格理论的{tech (key := "lattice-theoretic inductive predicate")}[归纳不动点]机制进行精译。
这允许在同一互递归块中混合余归纳与归纳谓词。

:::example "余归纳—归纳互递归块"
谓词 {lean}`Tick` 与 {lean}`Tock` 互相定义，其中 {lean}`Tick` 是余归纳谓词，{lean}`Tock` 是归纳谓词：

```lean
mutual
  coinductive Tick : Prop where
  | mk : ¬Tock → Tick

  inductive Tock : Prop where
  | mk : ¬Tick → Tock
end
```

两个构造器都可用：
```lean (name := checkTickMk)
#check @Tick.mk
```
```leanOutput checkTickMk
Tick.mk : ¬Tock → Tick
```
```lean (name := checkTockMk)
#check @Tock.mk
```
```leanOutput checkTockMk
Tock.mk : ¬Tick → Tock
```

系统会生成一个互归纳原理：
```lean (name := checkMutualInduct)
#check @Tick.mutual_induct
```
```leanOutput checkMutualInduct
Tick.mutual_induct : ∀ (pred_1 pred_2 : Prop),
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) → (pred_1 → Tick) ∧ (Tock → pred_2)
```
:::

# 限制
%%%
tag := "coinductive-restrictions"
%%%

:::paragraph
{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令有以下限制：

 * 它只能定义谓词，即取值于 {lean}`Prop` 的类型。
   尝试在 {lean}`Type` 或更高宇宙中定义余归纳类型会导致错误。

 * 正在定义的谓词不能带有{tech (key := "macro scopes")}[宏作用域]。

 * 尚不支持通过 {keywordOf Lean.Parser.Term.match}`match` 进行模式匹配；请改用 {tactic}`cases` 策略。

:::

:::example "仅限谓词"
尝试定义一个并非谓词的余归纳类型会导致错误：

```lean +error (name := notPredErr)
coinductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
```
```leanOutput notPredErr
`coinductive` keyword can only be used to define predicates
```
:::
