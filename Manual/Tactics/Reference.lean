/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers
import Manual.Tactics.Reference.Simp


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 250000

#doc (Manual) "策略参考" =>
%%%
tag := "tactic-ref"
file := "Tactic-Reference"
%%%

# 经典逻辑
%%%
tag := "tactic-ref-classical"
file := "Classical Logic"
%%%

:::tactic "classical"
:::


# 假设
%%%
tag := "tactic-ref-assumptions"
file := "Assumptions"
%%%

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "apply_assumption"
:::

# 量词
%%%
tag := "tactic-ref-quantifiers"
file := "Quantifiers"
%%%

:::tactic "exists"
:::

:::tactic "intro"
:::


:::tactic "intros"
:::

:::tactic "rintro"
:::


# 关系
%%%
tag := "tactic-ref-relations"
file := "Relations"
%%%

:::tactic "rfl"
:::

:::tactic "rfl'"
:::


:::tactic Lean.Parser.Tactic.applyRfl
:::

:::syntax attr (title := "自反关系")
{attr}`refl` 属性将引理标记为某个关系的自反性证明。
这些引理由 {tactic}`rfl`、{tactic}`rfl'` 和 {tactic}`apply_rfl` 策略使用。

```grammar
refl
```
:::

:::tactic "symm"
:::

:::tactic "symm_saturate"
:::

:::syntax attr (title := "对称关系")
{attr}`symm` 属性将引理标记为某个关系具有对称性的证明。
这些引理由 {tactic}`symm` 和 {tactic}`symm_saturate` 策略使用。

```grammar
symm
```
:::

:::tactic "calc"
:::

{docstring Trans}

## 相等关系
%%%
tag := "tactic-ref-equality"
file := "Equality"
%%%

:::tactic "subst"
:::

:::tactic "subst_eqs"
:::

:::tactic "subst_vars"
:::

:::tactic "congr"
:::

:::tactic "eq_refl"
:::

:::tactic "ac_rfl"
:::

# 结合性与交换性
%%%
tag := "tactic-ref-associativity-commutativity"
file := "Associativity and Commutativity"
%%%

:::tactic "ac_nf"
:::

:::tactic "ac_nf0"
:::


# 引理
%%%
tag := "tactic-ref-lemmas"
file := "Lemmas"
%%%

:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
:::

:::tactic "refine'"
:::

:::tactic "solve_by_elim"
:::

:::tactic "apply_rules"
:::

:::tactic "as_aux_lemma"
:::


# 假命题
%%%
tag := "tactic-ref-false"
file := "Falsehood"
%%%

:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic "false_or_by_contra"
:::


# 目标管理
%%%
tag := "tactic-ref-goals"
file := "Goal Management"
%%%

:::tactic "suffices"
:::

:::tactic "change"
:::

:::tactic "generalize"
:::

:::tactic "specialize"
:::

:::tactic "obtain"
:::

:::tactic "show"
:::

:::tactic Lean.Parser.Tactic.showTerm
:::


# 类型转换管理
%%%
tag := "tactic-ref-casts"
file := "Cast Management"
%%%

本节中的策略有助于避免因{deftech (key := "casts")}_类型转换_而卡住。类型转换是将数据从一种类型强制转换为另一种类型的函数，例如将自然数转换为相应的整数。
{citet castPaper}[] 对其有更详细的介绍。

:::tactic Lean.Parser.Tactic.tacticNorm_cast__
:::

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast_
:::

# 管理 `let` 表达式
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Managing--let--Expressions"
file := "Managing `let` Expressions"
%%%

:::tactic "extract_lets"
:::

:::tactic "lift_lets"
:::

:::tactic "let_to_have"
:::

:::tactic "clear_value"
:::


# 外延性
%%%
tag := "tactic-ref-ext"
file := "Extensionality"
%%%

:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

# 受 SMT 启发的自动化
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--SMT-Inspired-Automation"
file := "SMT-Inspired Automation"
%%%
:::tactic "grind"
:::

:::tactic "grind?"
:::

:::tactic "lia"
:::

:::tactic "grobner"
:::


{include 0 Manual.Tactics.Reference.Simp}

# 重写
%%%
tag := "tactic-ref-rw"
file := "Rewriting"
%%%

:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

{docstring Lean.Meta.Rewrite.Config +allowMissing}

{docstring Lean.Meta.Occurrences}

{docstring Lean.Meta.TransparencyMode +allowMissing}

{docstring Lean.Meta.Rewrite.NewGoals +allowMissing}


:::tactic "unfold"

由 {name}`Lean.Elab.Tactic.evalUnfold` 实现。
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


# 归纳类型
%%%
tag := "tactic-ref-inductive"
file := "Inductive Types"
%%%

## 引入
%%%
tag := "tactic-ref-inductive-intro"
file := "Introduction"
%%%

:::tactic "constructor"
:::


:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::

## 消去
%%%
tag := "tactic-ref-inductive-elim"
file := "Elimination"
%%%

消去策略使用{ref "recursors"}[递归器]和自动派生的{ref "recursor-elaboration-helpers"}[`casesOn` 辅助函数]来实现归纳与分类讨论。
这些策略产生的{tech (key := "subgoals")}[子目标]由消去器各次要前提的类型决定；通过 {keyword}`using` 选项使用不同的消去器会产生不同的子目标。

:::::leanSection
```lean -show
variable {n : Nat}
```
::::example "选择消去器" (file := "Choosing Eliminators")

:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

尝试证明 {lean}`∀(i : Fin (n + 1)), 0 + i = i` 时，引入假设后，策略 {tacticStep}`induction i` 会得到：

```post
case mk
n val✝ : Nat
isLt✝ : val✝ < n + 1
⊢ 0 + ⟨val✝, isLt✝⟩ = ⟨val✝, isLt✝⟩
```

这是因为 {name}`Fin` 是一个只有单个非递归构造器的{tech (key := "structure")}[结构体]。
它的递归器具有一个与该构造器对应的次要前提：
```signature
Fin.rec.{u} {n : Nat} {motive : Fin n → Sort u}
  (mk : (val : Nat) →
    (isLt : val < n) →
    motive ⟨val, isLt⟩)
  (t : Fin n) : motive t
```
:::
:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

改用策略 {tacticStep}`induction i using Fin.induction` 则会得到：

```post
case zero
n : Nat
⊢ 0 + 0 = 0

case succ
n : Nat
i✝ : Fin n
a✝ : 0 + i✝.castSucc = i✝.castSucc
⊢ 0 + i✝.succ = i✝.succ
```

{name}`Fin.induction` 是一种替代消去器，它对底层的 {name}`Nat` 实施归纳：
```signature
Fin.induction.{u} {n : Nat}
  {motive : Fin (n + 1) → Sort u}
  (zero : motive 0)
  (succ : (i : Fin n) →
    motive i.castSucc →
    motive i.succ)
  (i : Fin (n + 1)) : motive i
```
:::

::::
:::::

可以使用 {attr}`induction_eliminator` 和 {attr}`cases_eliminator` 属性注册{deftech (key := "Custom eliminators")}[自定义消去器]。
消去器会针对其显式目标注册（即作为消去器函数显式参数而非隐式参数的目标）；对这些类型的目标使用 {tactic}`induction` 或 {tactic}`cases` 时，将应用该消去器。
自定义消去器存在时优先于递归器。
将 {option}`tactic.customEliminators` 设为 {lean}`false` 可禁用自定义消去器。

:::syntax attr (title := "自定义消去器")
{attr}`induction_eliminator` 属性注册一个供 {tactic}`induction` 策略使用的消去器。
```grammar
induction_eliminator
```

{attr}`cases_eliminator` 属性注册一个供 {tactic}`cases` 策略使用的消去器。
```grammar
cases_eliminator
```
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "fun_cases"
:::

:::tactic "induction"
:::

:::tactic "fun_induction"
:::


:::tactic "nofun"
:::

:::tactic "nomatch"
:::


# 库搜索
%%%
tag := "tactic-ref-search"
file := "Library Search"
%%%

库搜索策略旨在交互式使用。
运行时，它们会在 Lean 库中搜索可能适用于当前情形的引理或重写规则，并给出一个新策略建议。
不应将这些策略留在证明中，而应采用它们给出的建议。

:::tactic "exact?"
:::

:::tactic "apply?"
:::




:::tacticExample
{goal -show}`∀ (i j k : Nat), i < j → j < k → i < k`
```setup
intro i j k h1 h2
```
在此证明状态下：
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```

调用 {tacticStep}`apply?` 会给出如下建议：

```tacticOutput
Try this:
  [apply] exact Nat.lt_trans h1 h2
```

```post -show

```
:::


:::tactic "rw?"
:::

# 分类讨论
%%%
tag := "tactic-ref-cases"
file := "Case Analysis"
%%%


:::tactic "split"
:::

:::tactic "by_cases"
:::

# 判定过程
%%%
tag := "tactic-ref-decision"
file := "Decision Procedures"
%%%


:::tactic Lean.Parser.Tactic.decide (show := "decide")
:::

:::tactic Lean.Parser.Tactic.nativeDecide (show := "native_decide")
:::

:::tactic "omega"
:::

:::tactic "bv_omega"
:::


## SAT 求解器集成
%%%
tag := "tactic-ref-sat"
file := "SAT Solver Integration"
%%%

:::tactic "bv_decide"
:::

:::tactic "bv_normalize"
:::

:::tactic "bv_check"
:::

:::tactic Lean.Parser.Tactic.bvTrace
:::

# 传值求值
%%%
tag := "tactic-ref-cbv"
file := "Call-by-Value Evaluation"
%%%

{tactic}`cbv` 策略通过模拟传值求值来归约项。
在{deftech (key := "call-by-value evaluation")}[传值求值]中，函数调用归约之前会先将函数的实参归约为值。
粗略来说，_值_要么是函数，要么是构造器对值的应用；函数体本身不必是值，该函数也可算作值。
这种求值策略与 Lean 编译器生成代码的执行顺序一致，因此很适合为获得良好运行时性能而编写的代码。

{tactic}`cbv` 使用定义的{tech (key := "equational lemmas")}[等式引理]展开定义，并应用为{tech (key := "matcher functions")}[匹配器函数]自动证明的类似定理，在每一步产生命题相等性证明。
由于这种展开是命题上的而非定义上的，{tactic}`cbv` 可以归约通过{ref "well-founded-recursion"}[良基递归]或{ref "partial-fixpoint"}[部分不动点]定义的函数。
一般来说，这些函数与其展开式并非定义相等，因此内核的定义归约不会归约其递归调用。

{tactic}`cbv` 产生的证明只使用三个标准公理（{name}`propext`、{name}`Quot.sound` 和 {name}`Classical.choice`）。
特别地，与 {tactic}`native_decide` 不同，它们不要求信任代码生成器的正确性。

由于 {tactic}`cbv` 通过 {name}`congrArg` 和 {name}`congrFun` 重写子项，它无法重写出现在依赖位置的子项。
重写依赖函数的实参会改变后续实参的类型；即使使用异质相等，也不存在适用于任意依赖函数的恰当同余引理。

:::paragraph
归约常量应用时，{tactic}`cbv` 会依次尝试以下策略：

 1. 自定义 {attr}`cbv_eval` 重写规则
 2. {tech (key := "Equational lemmas")}[等式引理]（例如 `foo.eq_1`、`foo.eq_2`）
 3. 展开方程
 4. 内核匹配器归约

除非提供匹配的 {attr}`cbv_eval` 重写规则，否则绝不会展开标有 {attr}`cbv_opaque` 的声明。
:::

:::syntax tactic (title := "传值求值")
```grammar
cbv $[at $[$h]*]?
```
:::

:::tactic Lean.Parser.Tactic.cbv (show := "cbv")
:::

```lean -show
-- `cbv` 策略目前仍处于实验阶段，使用时会发出警告。
-- 此选项会禁用该警告：
set_option cbv.warning false
```

:::example "归约良基递归函数" (file := "Reducing Well-Founded Recursive Functions")
函数 {lean}`countdown` 使用良基递归定义，因此它与其展开式并非定义相等。
普通的 {tactic}`rfl` 无法关闭该目标：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean +error (name := countdownRfl)
example : countdown 3 = [3, 2, 1, 0] := by rfl
```
```leanOutput countdownRfl
Tactic `rfl` failed: The left-hand side
  countdown 3
is not definitionally equal to the right-hand side
  [3, 2, 1, 0]

⊢ countdown 3 = [3, 2, 1, 0]
```
{tactic}`cbv` 策略可以通过命题重写归约 {lean}`countdown 3`，然后用 {tactic}`rfl` 关闭相等目标：
```lean
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
:::

:::example "归约假设" (file := "Reducing Hypotheses")
{tactic}`cbv` 策略支持标准的 `at` 位置语法。
与 `at h` 一起使用时，它会归约假设 `h` 的类型。
与 `at *` 一起使用时，它会归约所有非依赖的命题
假设以及目标。
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
example (x : List Nat) (h : x = countdown 2) :
    x = [2, 1, 0] := by
  cbv at h
  exact h
```
:::

:::example "作为非终结策略的 `cbv`" (file := "`cbv` as a Non-Finishing Tactic")
与 {tactic}`decide` 不同，{tactic}`cbv` 不是终结策略。
它会尽可能化简目标，但可能留下需要进一步推理的目标。
这里，{tactic}`cbv` 归约了对 {lean}`countdown` 的调用，但留下了成员关系目标：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean +error (name := cbvNonFinishing)
example : 1 ∈ countdown 2 := by
  cbv
```
```leanOutput cbvNonFinishing
unsolved goals
⊢ List.Mem 1 [2, 1, 0]
```
:::

:::example "依赖位置" (file := "Dependent Positions")
```imports -show
import Std.Data.DTreeMap
import Std.Data.TreeMap
```

函数 {name}`wfLength` 是 {name}`List.length` 的一个版本，它通过{tech (key := "well-founded recursion")}[良基递归]而非{ref "structural-recursion"}[结构递归]定义。
因此，它是{tech (key := "irreducible")}[不可归约的]：
```lean
def wfLength : List Nat → Nat
  | [] => 0
  | _ :: xs => wfLength xs + 1
termination_by xs => xs
```
```lean -show
set_option cbv.warning false
```

在非依赖的 {name}`Std.TreeMap` 中，{tactic}`cbv` 可以归约计算所得的键 {lean}`wfLength [1, 2]`：
```lean
def myTreeMap : Std.TreeMap Nat Nat :=
  .empty |>.insert (wfLength [1, 2]) 42

example : myTreeMap.toList = [⟨2, 42⟩] := by
  cbv
```
然而，考虑一个依赖树映射 {lean}`FinMap`，它将每个键 `n` 映射到一个类型为 `Fin (n + 1)` 的值：
```lean
abbrev FinMap :=
  Std.DTreeMap Nat (fun n => Fin (n + 1))
```
此处 {tactic}`cbv` 会卡住，因为值类型 `Fin (n + 1)` 依赖于键：
```lean +error (name := depPosition)
example :
    let m : FinMap :=
      .empty |>.insert (wfLength [1, 2])
        ⟨0, by decide_cbv⟩
    m.toList = [⟨2, ⟨0, by omega⟩⟩] := by
  cbv
```
```leanOutput depPosition
unsolved goals
⊢ [⟨wfLength [1, 2], ⟨0, ⋯⟩⟩] = [⟨2, ⟨0, ⋯⟩⟩]
```
:::

## {tactic}`decide_cbv`
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Call-by-Value-Evaluation--decide_cbv"
file := "{tactic}`decide_cbv`"
%%%

:::tactic Lean.Parser.Tactic.decide_cbv (show := "decide_cbv")
:::

:::example "`decide_cbv`" (file := "`decide_cbv`")
{tactic}`decide_cbv` 策略通过{tech (key := "call-by-value evaluation")}[传值求值]归约 {name}`Decidable` 实例，从而关闭属于可判定命题的目标：
```lean
example : 2 + 3 = 5 ∧ 10 < 20 := by
  decide_cbv
```
与 {tactic}`native_decide` 不同，{tactic}`decide_cbv` 不要求信任代码生成器。
使用定义归约的 {tactic}`decide` 无法做到这一点，而 {tactic}`decide_cbv` 可以处理通过{ref "well-founded-recursion"}[良基递归]定义的函数：
```lean
def isAllPositive : List Int → Bool
  | [] => true
  | x :: xs => x > 0 && isAllPositive xs
termination_by xs => xs

example : isAllPositive [1, 2, 3] = true := by
  decide_cbv
```
:::

::::example "使用 `decide_cbv` 检验素数幂" (file := "Prime Power Testing with `decide_cbv`")
由于 {tactic}`decide_cbv` 使用命题展开，它可以求值涉及{ref "well-founded-recursion"}[良基递归]函数的复杂判定过程。
这里，{lean}`Nat.minFac` 找出一个数的最小除数，而辅助函数 {lean}`minFacAux` 搜索最小奇除数：
```lean
def minFacAux (n k : Nat) : Nat :=
  if h : n < k * k then n
  else
    if h' : k ∣ n then k
    else
      have : k ≤ n := by
        have := Nat.le_mul_self k; grind
      minFacAux n (k + 2)
termination_by n + 2 - k

def Nat.minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3
```
:::leanSection
```lean -show
variable {b n : Nat}
```
{lean}`Nat.log b n` 通过反复平方计算 {lean}`n` 以 {lean}`b` 为底的对数的下取整：
:::
```lean
def Nat.log (b n : Nat) : Nat :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : Nat → Nat → Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then
        (q, 2 * e)
      else
        (q / b, 2 * e + 1)
```
此处，即使存在自由变量 `k`，{tactic}`decide_cbv` 仍能归约判定过程的结果：
```lean
example : ¬∃ k,
    k ≤ Nat.log 2 15151515151515 ∧
    0 < k ∧
    15151515151515 =
      Nat.minFac 15151515151515 ^ k := by
  decide_cbv

```
::::

## 控制 {tactic}`cbv` 的行为
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Call-by-Value-Evaluation--Controlling--cbv--Behavior"
file := "Controlling {tactic}`cbv` Behavior"
%%%

:::syntax attr (title := "自定义 `cbv` 重写规则")
{attr}`cbv_eval` 属性将一个定理注册为自定义重写规则，{tactic}`cbv` 会在尝试{tech (key := "equational lemmas")}[等式引理]之前应用它。
该定理必须是无条件相等式；其中一边（通常是左边）必须是常量的应用。

```grammar
cbv_eval
```

`←` 修饰符指示 {tactic}`cbv` 从右向左应用规则：
```grammar
cbv_eval ←
```
:::

:::example "`cbv_eval`" (file := "`cbv_eval`")
可以使用自定义重写规则控制 {tactic}`cbv` 如何求值特定函数。
例如，朴素的反转定义 {lean}`slowReverse` 因反复使用 {name}`List.append` 而具有二次复杂度。
通过 {lean}`fastReverse` 提供尾递归刻画后，{tactic}`cbv` 可以高效地求值 {lean}`slowReverse`：
```lean
def slowReverse : List Nat → List Nat
  | [] => []
  | x :: xs => slowReverse xs ++ [x]

def fastReverse (xs : List Nat) : List Nat :=
  go [] xs
where
  go (acc : List Nat) : List Nat → List Nat
  | [] => acc
  | x :: xs => go (x :: acc) xs

theorem reverse_spec_aux (xs acc : List Nat) :
    fastReverse.go acc xs =
      slowReverse xs ++ acc := by
  fun_induction fastReverse.go
    <;> grind [slowReverse]

@[cbv_eval] theorem slowReverse_cbv
    (xs : List Nat) :
    slowReverse xs = fastReverse xs := by
  simp [fastReverse, reverse_spec_aux]
```
```lean
example : slowReverse [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1] := by
  cbv
```
:::

:::syntax attr (title := "对 `cbv` 不透明的声明")
{attr}`cbv_opaque` 属性阻止 {tactic}`cbv` 使用声明的{tech (key := "equational lemmas")}[等式引理]或展开定理来展开它。
不过，{attr}`cbv_eval` 重写规则始终优先于 {attr}`cbv_opaque`：如果某声明存在匹配的 {attr}`cbv_eval` 规则，即使该声明标有 {attr}`cbv_opaque`，也会应用此规则。
这样便可用一组受控的求值规则替换默认展开行为。

```grammar
cbv_opaque
```
:::

::::example "使用 `@[cbv_opaque]` 的不透明定义" (file := "Opaque Definitions with `@[cbv_opaque]`")
将 {lean}`countdown` 标记为 {attr}`cbv_opaque` 会阻止 {tactic}`cbv` 展开它，因此先前由 {tactic}`cbv` 关闭的目标现在仍未解决：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
attribute [cbv_opaque] countdown
```
```lean +error (name := opaqueError)
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
```leanOutput opaqueError
unsolved goals
⊢ countdown 3 = [3, 2, 1, 0]
```
::::

### 自定义化简过程
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Call-by-Value-Evaluation--Controlling--cbv--Behavior--Custom-Simplification-Procedures"
file := "Custom Simplification Procedures"
%%%

:::paragraph
{deftech (key := "cbv simplification procedure")}[`cbv` 化简过程]（{tactic}`cbv` simproc）是一种用户定义的元程序，{tactic}`cbv` 会在匹配给定模式的子表达式上调用它。
{attr}`cbv_eval` 规则仅限于静态相等式，而 {tactic}`cbv` simproc 可以执行任意计算，以决定如何重写子表达式。
常见用途包括定义对字面值上的函数进行求值的过程，或使控制流短路。

{tactic}`cbv` 使用的 simproc 类型为 {name}`Lean.Meta.Sym.Simp.Simproc`，不同于 {tactic}`simp` 策略使用的 {name}`Lean.Meta.Simp.Simproc` 类型。
这两个系统彼此独立：注册 {tactic}`cbv` simproc 不会影响 {tactic}`simp`，反之亦然。
:::

:::syntax command (title := "自定义 `cbv` 化简过程")
```lean -show
open Lean Lean.Meta.Sym.Simp
```
主体的类型必须是 {name}`Simproc`（即 {lean}`Expr → SimpM Result`）。
模式是一个带有空位（`_`）的表达式，它决定哪些子表达式会触发该过程。
展开可归约定义，并对两边应用 {tech (key := "β")}[β]、{tech (key := "η-equivalence")}[η] 和 {tech (key := "ζ")}[ζ] 归约之后，模式会与子表达式进行结构匹配。
匹配以 α 等价为模（忽略绑定变量名），模式中的证明实参和实例实参被视为通配符。
可选的阶段说明符控制该过程在规范化期间何时触发。
未指定阶段时，默认为 `↑`（后置）。

: `↓`（前置）

   在 {tactic}`cbv` 归约每个子表达式_之前_触发。此时实参仍未归约。使用此阶段可以覆盖 {tactic}`cbv` 默认的传值求值顺序。典型用途是惰性求值实参或使求值短路（如内置的 {name}`ite` 和 {name}`Or` 过程）。

: `cbv_eval`（求值）

  在实参已归约为值_之后_、函数展开_之前_触发。使用此阶段可提供高效的闭项求值过程。

: `↑`（后置，默认）

  在 {tactic}`cbv` 尝试标准归约（等式引理、展开、内核匹配）_之后_触发。应优先尝试标准归约时使用此阶段。

```grammar
cbv_simproc name (pattern) := body
```

可以在名称之前放置可选的阶段说明符：

```grammar
cbv_simproc ↓ name (pattern) := body
```

```grammar
cbv_simproc cbv_eval name (pattern) := body
```

`cbv_simproc_decl` 变体声明该过程但不将其激活。
之后可以用 {attr}`cbv_simproc` 将其激活。

```grammar
cbv_simproc_decl name (pattern) := body
```
:::

:::syntax attr (title := "`cbv` 的化简过程属性")
{attr}`cbv_simproc` 属性激活先前声明（用 `cbv_simproc_decl` 定义）的化简过程，供 {tactic}`cbv` 使用。
可选的阶段说明符控制该过程在规范化期间何时触发。

```grammar
cbv_simproc
```

阶段说明符控制该过程何时触发：

```grammar
cbv_simproc ↓
```

```grammar
cbv_simproc ↑
```

```grammar
cbv_simproc cbv_eval
```
:::


::::example "声明 `cbv_simproc`" (file := "Declaring a `cbv_simproc`")

```imports -show
import Lean.Meta.Tactic.Cbv.CbvSimproc
```

化简过程通过提供模式和类型为 {name}`Lean.Meta.Sym.Simp.Simproc` 的主体来声明。
模式是带有空位（`_`）的表达式，它决定哪些子表达式会触发该过程。
这里的模式是（`myConst _`），它匹配 {name}`myConst` 的任意应用。
该过程（{lean (type := "Simproc")}`fun _e => do return .rfl`）忽略表达式，并返回一个表示不执行重写的结果。

```lean
opaque myConst : Nat → Nat

open Lean Meta Sym.Simp in
cbv_simproc evalMyConst (myConst _) := fun _e => do
  -- 真正的 simproc 会检查 `e`、计算结果，
  -- 并返回 `.step result proof`。
  return .rfl
```

{keywordOf Lean.Parser.«command_Cbv_simproc_decl_(_):=_»}`cbv_simproc_decl` 变体声明该过程但不将其激活。
之后可以使用 {attr}`cbv_simproc` 属性将其激活，并可选择指定阶段：

```lean
open Lean Meta Sym.Simp in
cbv_simproc_decl evalMyConst2 (myConst _) := fun _e =>
  return .rfl

attribute [cbv_simproc cbv_eval] evalMyConst2
```

::::

::::example "列表头部的惰性求值" (file := "Lazy evaluation of a head of the list")
```imports -show
import Lean.Meta.Sym.Simp
```
```lean -show
open Lean Meta Sym.Simp
variable (α : Type)
variable (a : α)
variable (as : List α)
```

这是一个前置阶段化简过程的示例，它打破常规传值求值顺序来实现惰性求值。
`↓` 修饰符确保 {name}`evalListHead` 在求值 {name}`List.head?` 的实参之前触发。
它使用 {name}`List.head?_cons` 将 {lean}`List.head? (a :: as)` 重写为 {lean}`some a`，丢弃尾部 {lean}`as` 而不对其求值。
之后只有头部元素 {lean}`a` 会被 {tactic}`cbv` 归约。

```lean
cbv_simproc ↓ evalListHead (List.head? _) := fun e => do
  let_expr List.head? α listExpr := e | return .rfl
  let_expr List.cons _ a as := listExpr | return .rfl
  let Level.succ u ← Sym.getLevel α | return .rfl
  let result ← Sym.share <| mkApp2 (mkConst ``Option.some [u]) α a
  let proof := mkApp3 (mkConst ``List.head?_cons [u]) α a as
  return .step result proof

theorem cbv_simproc_test : [5 + 5,6].head? = .some 10 := by cbv
```
检查证明项可以确认化简过程已经触发：{name}`List.head?_cons` 直接出现在证明中，表明 {tactic}`cbv` 使用了 simproc 的重写，而不是通过展开 {name}`List.head?` 的定义来归约它。

```lean -show (name := cbvSimprocTest)
#print cbv_simproc_test
```
```leanOutput cbvSimprocTest
theorem cbv_simproc_test : [5 + 5, 6].head? = some 10 :=
of_eq_true
  (Eq.trans (congrFun' (congrArg Eq (Eq.trans List.head?_cons (congrArg some (Eq.refl 10)))) (some 10))
    (eq_self (some 10)))
```

::::

:::paragraph
Lean 为 {tactic}`cbv` 提供了许多内置化简过程。
它们处理控制流（`ite`、`dite`、`cond`、`Decidable.decide`、`Decidable.rec`）、逻辑联结词（`Or`、`And`）以及数据结构操作（数组索引、字符串操作）。
控制流过程使用 `↓`（前置）阶段实现短路求值，而数组和字符串过程使用 `cbv_eval` 阶段直接归约闭项应用。
:::

## 选项
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Call-by-Value-Evaluation--Options"
file := "Options"
%%%

{optionDocs cbv.maxSteps}

{optionDocs cbv.warning}

# 控制归约
%%%
tag := "tactic-reducibility"
file := "Controlling Reduction"
%%%

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic "with_unfolding_all"
:::

:::tactic "with_unfolding_none"
:::


# 控制流
%%%
tag := "tactic-ref-control"
file := "Control Flow"
%%%


:::tactic "skip"
:::


:::tactic Lean.Parser.Tactic.guardHyp
:::

:::tactic Lean.Parser.Tactic.guardTarget
:::

:::tactic Lean.Parser.Tactic.guardExpr
:::

:::tactic "done"
:::

:::tactic "sleep"
:::

:::tactic "stop"
:::


# 项精译后端
%%%
tag := "tactic-ref-term-helpers"
file := "Term Elaboration Backends"
%%%


这些策略在项的精译过程中使用，以解决期间产生的待证目标。

:::tactic tacticDecreasing_with_
:::

:::tactic "get_elem_tactic"
:::

:::tactic "get_elem_tactic_trivial"
:::


# 调试工具
%%%
tag := "tactic-ref-debug"
file := "Debugging Utilities"
%%%


:::tactic "sorry"
:::

:::tactic "admit"
:::

:::tactic "dbg_trace"
:::

:::tactic Lean.Parser.Tactic.traceState
:::

:::tactic Lean.Parser.Tactic.traceMessage
:::

# 建议
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Suggestions"
file := "Suggestions"
%%%

:::tactic "∎"
:::

:::tactic "suggestions"
:::


# 其他
%%%
tag := "tactic-ref-other"
file := "Other"
%%%

:::tactic "trivial"
:::

:::tactic "solve"
:::

:::tactic "and_intros"
:::

:::tactic "infer_instance"
:::

:::tactic "expose_names"
:::

:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::

:::tactic Lean.Parser.Tactic.runTac
:::

# 验证条件生成
%%%
tag := "tactic-ref-mvcgen"
file := "Verification Condition Generation"
%%%

:::tactic "mvcgen"
:::

## 用于 `Std.Do.SPred` 有状态目标的策略
%%%
tag := "tactic-ref-spred"
file := "Tactics for Stateful Goals in `Std.Do.SPred`"
%%%

### 启动与停止证明模式
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Verification-Condition-Generation--Tactics-for-Stateful-Goals-in--Std___Do___SPred--Starting-and-Stopping-the-Proof-Mode"
file := "Starting and Stopping the Proof Mode"
%%%

:::tactic "mstart"
:::

:::tactic "mstop"
:::

:::tactic "mleave"
:::

### 证明有状态目标
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Verification-Condition-Generation--Tactics-for-Stateful-Goals-in--Std___Do___SPred--Proving-a-Stateful-Goal"
file := "Proving a Stateful Goal"
%%%

:::tactic "mspec"
:::

:::tactic Lean.Parser.Tactic.mintroMacro
:::

:::tactic "mexact"
:::

:::tactic "massumption"
:::

:::tactic "mrefine"
:::

:::tactic "mconstructor"
:::

:::tactic "mleft"
:::

:::tactic "mright"
:::

:::tactic "mexists"
:::

:::tactic "mpure_intro"
:::

:::tactic "mexfalso"
:::

### 操作有状态假设
%%%
tag := "The-Lean-Language-Reference--Tactic-Proofs--Tactic-Reference--Verification-Condition-Generation--Tactics-for-Stateful-Goals-in--Std___Do___SPred--Manipulating-Stateful-Hypotheses"
file := "Manipulating Stateful Hypotheses"
%%%

:::tactic "mclear"
:::

:::tactic "mdup"
:::

:::tactic "mhave"
:::

:::tactic "mreplace"
:::

:::tactic "mspecialize"
:::

:::tactic "mspecialize_pure"
:::

:::tactic "mcases"
:::

:::tactic "mrename_i"
:::

:::tactic "mpure"
:::

:::tactic "mframe"
:::
