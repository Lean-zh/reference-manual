/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta
import Manual.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax
import Manual.RecursiveDefs.CoinductivePredicates.Theory

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600


#doc (Manual) "余归纳与归纳谓词" =>
%%%
tag := "coinductive-predicates"
%%%

:::paragraph
Lean 的类型论并不直接支持余归纳类型。
不过，{deftech (key := "lattice-theoretic coinductive predicate")}[余归纳谓词]——也就是取值于 {lean}`Prop` 的递归定义——可以借助命题上的完备格结构来定义。
这些谓词提供了一种余归纳推理原理：若能证明某个对象满足某个更小的谓词，且该谓词本身与余归纳谓词的定义相容，就可以证明该对象满足这个余归纳谓词。
这与归纳推理对偶：在归纳推理中，一个已知事实可以通过可能递归的分类讨论被分解。
余归纳谓词使得人们能够刻画并推理无限域。
计算机科学中的一些例子包括：

 * 允许环路的状态迁移系统上的互模拟
 * 小步操作语义中的发散
 * 活性性质

对偶地，{deftech (key := "lattice-theoretic inductive predicate")}[归纳谓词] 也可以借助同样的机制，通过最小不动点来定义。
由于它们使用的是同一套底层机制，这种替代普通 {tech (key := "inductive types")}[归纳类型] 的方案，与归纳—余归纳混合的互递归块相兼容。
:::

::::::example "无限序列" (open := true)

::::leanSection
```lean -show
variable {R : α → α → Prop} (x y : α) {pred : α → Prop}
```
:::paragraph
给定 {lean}`α` 上的一个关系 {lean}`R`（即其类型为 {lean}`α → α → Prop`），如果满足下列条件，就存在一个从 {lean}`x` 出发的、由 {lean}`α` 中值组成的无限序列：

 * 存在某个 {lean}`y` 使得 {lean}`R x y` 成立；
 * 并且从 {lean}`y` 出发也存在一个无限序列。

这是一个典型的余归纳谓词：它描述的是一种潜在无限的行为，并且可以表达为一条没有基例的单一推理规则。
:::
::::

这个递归规格是良定义的，但它不能作为普通递归函数来定义，因为定义中的递归部分并没有减小。
不过，把它定义成余归纳定义却完全合理：
```lean
coinductive InfSeq (R : α → α → Prop) : α → Prop where
  | step (y : α) : R x y →  InfSeq R y → InfSeq R x
```

:::leanSection
```lean -show
variable {R : α → α → Prop} (a : α) {pred : α → Prop}
```

余归纳推理原理接受一个谓词 {lean}`pred`。
要证明 {lean}`a` 是某条无限 {lean}`R`-序列的起点，只需证明：对每个满足 {lean}`pred` 的元素，{lean}`R` 都会把它关联到另一个同样满足该谓词的元素。
换言之，无限序列的存在可以通过直接给出这样一条序列来证明：
```signature
InfSeq.coinduct (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ y, R a y ∧ pred y) →
  ∀ (a : α), pred a → InfSeq R a
```
:::
::::::




在 Lean 中，有两种方式定义余归纳谓词：

 1. 在取值于 {lean}`Prop` 的递归 {keywordOf Lean.Parser.Command.declaration}`def` 上使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 终止性子句，它会取最大不动点。等价地，{keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句则把归纳谓词定义为最小不动点。

 2. 使用 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 命令，它提供了一种与 {keywordOf Lean.Parser.Command.inductive}`inductive` 声明相呼应的声明式语法。


# 不动点终止性子句
%%%
tag := "fixpoint-clauses"
%%%

取值于 {lean}`Prop` 的递归函数，可以通过为其添加 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`（用于余归纳定义，即最大不动点）或 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint`（用于归纳定义，即最小不动点）标注，来定义为一个不动点。
这些终止性子句与 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 扮演相同角色，但它们利用 {ref "lattice-prop"}[`Prop` 上的完备格结构] 来计算相应的不动点。

## 余归纳不动点
%%%
tag := "coinductive-fixpoint-clause"
%%%

:::leanSection
```lean -show
variable {P Q : ReverseImplicationOrder}
```
{keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 子句把一个谓词定义为其定义方程的最大不动点。
该函数必须相对于 {name}`Lean.Order.ReverseImplicationOrder` 是单调的；在这个顺序中，{lean}`P ⊑ Q` 表示 {lean}`Q → P`。
:::

:::leanSection
```lean -show
variable {P Q : α → ReverseImplicationOrder}
example : (P ⊑ Q) = (∀ x, P x ⊑ Q x) := rfl
example : (∀ x, P x ⊑ Q x) = (∀ x, Q x → P x) := rfl
```
这个顺序会按点扩展到谓词的定义域上。
给定 {lean}`α` 上的谓词 {lean}`P` 与 {lean}`Q`，{lean}`P ⊑ Q` 表示 {lean}`∀ x : α, P x ⊑ Q x`（也就是 {lean}`∀ x, Q x → P x`）。
:::

::::example "无限序列的单调性"
```lean -show
variable (R : α → α → Prop) {a : α}
```
当存在一条从 {lean}`a` 出发、由 {lean}`R` 关联起来的无限链时，命题 {lean}`InfSeq R a` 为真。
这可以用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 写成：

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

在精译过程中，第一步是把这个递归定义对递归调用做抽象，得到一个与 {lean}`F` 等价的定义：
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable (P Q : α → Prop) (R : α → α → Prop)
```
要使这个函数相对于反向蕴含顺序是单调的，它就必须保持 {lean}`P` 与 {lean}`Q` 之间的反向蕴含顺序。
也就是说，{lean}`∀ (x : α), Q x → P x` 必须推出 {lean}`∀ (x : α), F R x Q → F R x P`：
:::
```lean
theorem F_monotone
    (h : ∀ (x : α), Q x → P x) :
    ∀ (x : α), F R x Q → F R x P := by
  grind [F]
```
::::

:::example "单调性失败"

如果某个元素不存在一条通向它的无限链，那么它对于该关系就是可达的。
标准库中将这一性质归纳地定义为 {name}`Acc`。
下面这个把它尝试定义为余归纳谓词的做法会失败：
```lean +error (name := nonmono)
def NoInfChain (R : α → α → Prop) (x : α) : Prop :=
  ∀ y, R x y → ¬NoInfChain R y
coinductive_fixpoint
```

```leanOutput nonmono
Could not prove 'NoInfChain' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    NoInfChain R y✝
```

对应的函数是：
```lean
def F (R : α → α → Prop) (x : α) (P : α → Prop) : Prop :=
  ∀ y, R x y → ¬P y
```

Lean 之所以无法证明这个函数单调，是因为它事实上确实不单调：
```lean
theorem F_nonmonotone :
    ¬(∀ α R P Q,
      (∀ (x : α), Q x → P x) →
      (∀ (x : α), F R x Q → F R x P)) := by
  suffices ∃ α R P Q,
      ¬((∀ (x : α), Q x → P x) →
        (∀ (x : α), F R x Q → F R x P)) by
    simpa
  -- α = PUnit, R always true
  refine ⟨PUnit, fun _ _ => True, ?_⟩
  -- P 恒为真，而 Q 恒为假
  refine ⟨fun _ => True, fun _ => False, ?_⟩
  simp [F]
```
:::

:::example "非谓词"

某个命题的无限合取可以定义为一个余归纳不动点：
```lean
def InfConj (p : Prop) : Prop := p ∧ InfConj p
coinductive_fixpoint
```

不过，这不能用来定义一个无限积：
```lean +error (name := nonprop)
def InfProd (α : Type) : Prop := α × InfProd α
coinductive_fixpoint
```
错误消息表明，此处本来期望的是一个命题：
```leanOutput nonprop
Application type mismatch: The argument
  InfProd α
has type
  Prop
of sort `Type` but is expected to have type
  Type ?u.6
of sort `Type (?u.6 + 1)` in the application
  α × InfProd α
```

:::

与通过偏不动点给出的定义一样，余归纳谓词的定义方程并不在定义上成立。
不过，精译器会证明等式引理，从而允许把该谓词重写为其展开式。

:::example "定义相等与余归纳谓词"
{lean}`InfSeq` 是一个余归纳断言：某个关系从某点开始存在一条无限链：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

由于它是借助 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 定义的，因此它与其展开式并不在定义上相等：
```lean +error (name := nondefeq)
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rfl
```
```leanOutput nondefeq
Tactic `rfl` failed: The left-hand side
  InfSeq R a
is not definitionally equal to the right-hand side
  ∃ b, R a b ∧ InfSeq R b

α : Sort u_1
R : α → α → Prop
a : α
⊢ InfSeq R a = ∃ b, R a b ∧ InfSeq R b
```

不过，它带有可将其重写为展开式的等式引理：
```lean
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rw [InfSeq]
```

:::

除了等式引理外，Lean 还会生成一条 {deftech (key := "coinduction principle")}[余归纳原理]。
这条余归纳原理说明：只要给出另一个谓词，并证明它是该单调函数的一个后不动点，就可以证明相应的余归纳谓词。

::::example "无限序列的余归纳原理"
{lean}`InfSeq` 是一个余归纳断言：某个关系从某点开始存在一条无限链：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

对应的单调函数是：
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α} {P : α → Prop}
```
由于 {lean}`InfSeq` 是 {lean}`F` 的_最大_不动点，只要存在_任意_一个谓词，它小于自己在 {lean}`F` 下的像，就足以说明：凡满足该谓词的元素，也都满足 {lean}`InfSeq`。
换言之，要证明 {lean}`InfSeq R a`，只需给出一个谓词 {lean}`P`，使得 {lean}`∀ (a : α), P a → F R a P`，也就是 {lean}`∀ (a : α), P a → ∃ b, R a b ∧ P b`，然后再证明 {lean}`P a`。
:::
这条余归纳原理名为 {lean}`InfSeq.coinduct`：
```signature
InfSeq.coinduct {α} (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ b, R a b ∧ pred b) →
  ∀ (a : α), pred a → InfSeq R a
```
::::

::::example "余归纳的简单证明"
{lean}`InfSeq` 断言：在给定起点处，某个关系中存在一条由元素组成的无限序列：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α}
```
如果 {lean}`R a a` 成立，那么就存在一条在 {lean}`a` 处自环的平凡无限链：

```lean
theorem cycle_InfSeq {R : α → α → Prop} (a : α) :
    R a a → InfSeq R a := by
  apply InfSeq.coinduct (pred := fun m => R m m)
  intro x h
  exact ⟨x, h, h⟩
```
:::
::::

:::example "小于关系的无限链"
{lean}`InfSeq` 断言：在给定起点处，某个关系中存在一条由元素组成的无限序列：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

对于关系 {lean (type := "Nat → Nat → Prop")}`(· < ·)`，自然数上存在无限链。
每个自然数都可以作为这样一条链的起点，因此这里的谓词可以取成平凡谓词：
```lean
theorem lt_InfSeq {n : Nat} : InfSeq (· < ·) n := by
  apply InfSeq.coinduct (pred := fun x => True)
  . intro k _
    refine ⟨k + 1, ?_⟩
    simp
  . trivial
```
:::

::::example "DFA 语言等价性"
余归纳谓词天然适合刻画类似互模拟的概念。

:::leanSection
```lean -show
variable {Q : Type} {A : Type} {q : Q}
```
一个确定有限自动机由如下数据给出：状态集合 {lean}`Q`、字母表 {lean}`A`、位于 {lean}`Q` 中的初始状态 {lean}`q`、用来定义接受状态的 {lean}`Q` 的一个子集，以及一个把状态和字母表元素映射到新状态的迁移函数：
:::
```lean
structure DFA (Q : Type) (A : Type) : Type where
  q₀ : Q
  δ : Q → A → Q
  accepting : Q → Bool
```

对于同一字母表上的两个自动机，如果从给定的一对状态出发，它们对“这些状态是否为接受状态”的判断一致，并且按照各自的迁移函数，从所有后继状态出发得到的语言也都等价，那么它们在这对状态上的语言就是等价的：
```lean
def languageEquivalent (M : DFA Q A) (M' : DFA Q' A)
    (q : Q) (q' : Q') : Prop :=
  M.accepting q = M'.accepting q' ∧
    ∀ (a : A), languageEquivalent M M' (M.δ q a) (M'.δ q' a)
coinductive_fixpoint
```

余归纳原理刻画了确定自动机的标准互模拟概念：
```signature
languageEquivalent.coinduct {Q A Q' : Type}
  (M : DFA Q A) (M' : DFA Q' A) (pred : Q → Q' → Prop) :
  (∀ (q : Q) (q' : Q'), pred q q' →
    M.accepting q = M'.accepting q' ∧
    ∀ (a : A), pred (M.δ q a) (M'.δ q' a)) →
  ∀ (q : Q) (q' : Q'), pred q q' →
    languageEquivalent M M' q q'
```

它可以用来证明下面这两个 DFA 的语言等价：
:::row (align := "top")
```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "ok") |>.atop
(cfg.state 1 "fail") |>.atop
(cfg.loop 0 "a") |>.atop
(cfg.loop 1 "a, b") |>.atop
(cfg.edge 0 1 "b")
```

```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "start") |>.atop
(cfg.accept 1 "ok") |>.atop
(cfg.state 2 "fail") |>.atop
(cfg.arc 0 1 "a" 30) |>.atop
(cfg.arc 1 0 "a" (-30)) |>.atop
(cfg.edge 1 2 "b") |>.atop
(cfg.arc 0 2 "b" (-140)) |>.atop
(cfg.loop 2 "a, b")
```
:::

这两个 DFA 可以用如下定义表示：
```lean
inductive Alphabet where | a | b

inductive Q1 where | ok | fail

def loop : DFA Q1 Alphabet where
  q₀ := .ok
  δ
    | .ok, .a => .ok
    | _, _ => .fail
  accepting
    | .ok => True
    | _ => False

inductive Q2 where | start | ok | fail

def cycle : DFA Q2 Alphabet where
  q₀ := .start
  δ
    | .start, .a => .ok
    | .ok, .a => .start
    | _, _ => .fail
  accepting
    | .start | .ok => True
    | .fail => False
```

为了证明它们等价，第一步是定义一个关系，用来刻画它们的等价状态。
然后，余归纳会把“它们在该关系下确实等价”的证明提升为语言等价：
```lean
theorem loop_equiv_cycle :
    languageEquivalent loop cycle loop.q₀ cycle.q₀ := by
  let r : Q1 → Q2 → Prop
  | .ok, .start
  | .ok, .ok
  | .fail, .fail => True
  | _, _ => False
  apply languageEquivalent.coinduct (pred := r)
  . simp only [loop, cycle] <;>
    grind
  . simp [r, loop, cycle]
```
::::

## 归纳不动点
%%%
tag := "inductive-fixpoint-clause"
%%%

{keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句把一个谓词定义为其定义方程的最小不动点。
该函数必须相对于 {name}`Lean.Order.ImplicationOrder` 是单调的；这是 {lean}`Prop` 上的一个顺序，其中 `P ⊑ Q` 表示 `P → Q`。
这为谓词提供了普通 {keywordOf Lean.Parser.Command.declaration}`inductive` 类型声明之外的另一种选择，并且与 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 对偶。

在大多数情况下，普通的归纳类型声明会更方便。
不过，归纳不动点定义相较于普通归纳类型声明有两个关键优势，因此更适合某些专门用途：
 * 普通归纳类型声明带有一个_句法性的_正性条件：归纳类型的递归出现不能位于负位置。而归纳不动点要求的则是单调性，这是一条_语义性的_条件。
 * 归纳不动点可以与余归纳不动点互相定义，从而允许归纳—余归纳混合谓词。

对于每个归纳不动点定义，系统都会自动证明一条归纳原理。
这条归纳原理在逻辑强度上与归纳类型声明会生成的对应归纳原理相同，但其表述方式略有不同，而且必须显式应用。

与余归纳不动点一样，归纳不动点定义也不会在定义上归约。
它们可以借助自动生成的等式引理来展开，而其归纳原理则允许在证明中使用它们。

:::example "作为归纳不动点的自反传递闭包"
一个关系的自反传递闭包可以定义为归纳谓词：
```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

同一个谓词也可以定义为最小不动点。
```lean
def StarInd (tr : α → α → Prop) (q₁ q₂ : α) : Prop :=
  q₁ = q₂ ∨ ∃ (z : α), (tr q₁ z ∧ StarInd tr z q₂)
inductive_fixpoint
```

系统会生成一条归纳原理：
```signature
StarInd.induct (tr : α → α → Prop) (q₂ : α) (pred : α → Prop)
  (hyp : ∀ (q₁ : α), (q₁ = q₂ ∨ ∃ z, tr q₁ z ∧ pred z) → pred q₁)
  (q₁ : α) :
  StarInd tr q₁ q₂ → pred q₁
```

这条归纳原理可以用来证明这两种表述彼此等价：
```lean -keep
theorem star_implies_starInd (R : α → α → Prop) :
    ∀ a b : α, Star R a b = StarInd R a b := by
  intro a b
  ext
  constructor
  . intro h
    induction h <;> grind [StarInd]
  . apply StarInd.induct R b (Star R · b) ?_ a
    grind [Star]
```
:::

## 互递归块中的归纳-余归纳混合谓词
%%%
tag := "mixed-mutual-fixpoint"
%%%

{tech (key := "mutual block")}[互递归块] 可以混用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 与 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句。
块中的每个定义都必须使用这两种子句之一。
该构造会使用 `Prop` 上的两种{ref "lattice-prop"}[格结构]：归纳定义使用 {name Lean.Order.ImplicationOrder}`ImplicationOrder`，余归纳定义使用 {name Lean.Order.ReverseImplicationOrder}`ReverseImplicationOrder`。
在这两种情况下，系统计算的都是相应格上的最小不动点；而在反向蕴含顺序下，这个最小不动点恰好对应标准顺序下的最大不动点。
之所以可行，是因为遇到否定或蕴含时，{ref "coinductive-monotonicity"}[单调性] 引理会在这两种顺序之间翻转方向。

:::example "归纳-余归纳混合互递归块"
这个互递归块包含互相递归的余归纳谓词与归纳谓词：
```lean
mutual
  def tick : Prop :=
    ¬tock
  coinductive_fixpoint

  def tock : Prop :=
    ¬tick
  inductive_fixpoint
end
```

系统会为互递归块中的第一个定义生成一条互归纳原理：
```signature
tick.mutual_induct (pred_1 pred_2 : Prop) :
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) →
  (pred_1 → tick) ∧ (tock → pred_2)
```
:::


# 更多示例
%%%
tag := "coinductive-predicate-examples"
%%%

:::example "由全可达性推出的无限链" (open := true)
```lean -show
variable {a : α}
```
一个关系的自反传递闭包可以用归纳方式刻画：
```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```
无限序列则用余归纳方式刻画：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

如果从起始状态 {lean}`a` 出发，经由自反传递闭包可达的每个状态都有后继，那么从 {lean}`a` 出发就存在一条无限链。
谓词 {lean}`AllSeqInf` 表示每个可达状态都有后继：
```lean
def AllSeqInf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, Star R x y → ∃ z, R y z
```
证明这件事蕴含存在无限链，可以通过余归纳完成：
```lean
theorem infSeq_of_allSeqInf (R : α → α → Prop) :
    ∀ x, AllSeqInf R x → InfSeq R x := by
  apply InfSeq.coinduct
  intro x H
  unfold AllSeqInf at H
  have H' := H x (.refl x)
  obtain ⟨y, Rxy⟩ := H'
  exact ⟨y, Rxy,
    fun y' Ryy' =>
      H y' (.step x y y' Rxy Ryy')⟩
```
:::


:::example "到传递闭包为止的余归纳" (open := true)
一个强化后的余归纳原理允许把余归纳假设应用到传递闭包为止。
给定一个谓词 {lean}`X`，若每个 {lean}`X`-状态都能经过一步或多步 {lean}`R` 迁移到另一个 {lean}`X`-状态，那么每个 {lean}`X`-状态都满足 {lean}`InfSeq R`：

```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

```lean
variable {α : Sort _} {R : α → α → Prop}

inductive Plus (R : α → α → Prop) :
    α → α → Prop where
  | left : ∀ a b c,
      R a b → Star R b c → Plus R a c

theorem plusStar (a b : α) :
    Plus R a b → Star R a b := by
  intro h; cases h
  case left _ h₂ h₃ =>
    exact Star.step _ _ _ h₂ h₃

theorem plusStarTrans (a b c : α) :
    Star R a b → Plus R b c →
    Plus R a c := by
  intro s p; induction s
  case refl => exact p
  case step d e _ rel _ ih =>
    exact Plus.left _ _ _ rel
      (plusStar _ _ (ih p))

variable (X : α → Prop)

theorem infSeqCoinductionUpTo :
    (∀ (a : α), X a →
      ∃ b, Plus R a b ∧ X b) →
    ∀ (a : α), X a → InfSeq R a := by
  intro h₁ a rel
  apply @InfSeq.coinduct _ _
    (fun a => ∃ b, Star R a b ∧ X b)
  case x =>
    obtain ⟨a', h₁, h₂⟩ := h₁ a rel
    exact ⟨a', plusStar _ _ h₁, h₂⟩
  case hyp =>
    intro a0 ⟨a1, h₃, h₄⟩
    obtain ⟨mid, h₅, h₆⟩ := h₁ a1 h₄
    have t := plusStarTrans a0 a1 mid h₃ h₅
    cases t
    case left mid2 rel2 s =>
      exact ⟨mid2, rel2, mid, s, h₆⟩
```
:::



{include 0 Manual.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax}

{include 0 Manual.RecursiveDefs.CoinductivePredicates.Theory}
