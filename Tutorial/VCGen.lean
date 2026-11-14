/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual
import VersoTutorial

import Manual.Meta
import Manual.Papers

import Std.WP
import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)
open Verso.Genre.Tutorial

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option experimental.vcgen true

#doc (Tutorial) "使用 `vcgen` 验证命令式程序" =>
%%%
tag := "vcgen-tactic-tutorial"
slug := "vcgen"
summary := inlines!"演示如何使用 Lean 的验证条件生成器，以方便且可组合的方式证明程序性质。"
exampleStyle := .inlineLean `VCGenTutorial
%%%

本教程自顶向下介绍 {tactic}`vcgen` 最重要的概念。
{tactic}`vcgen` 可以证明任何具有最弱前置条件语义的程序的性质，从单子计算到小型命令式语言的语法树都包括在内。
本教程重点讨论用 {keywordOf Lean.Parser.Term.do}`do` 记法编写的单子程序，因为这是 Lean 用户最常需要证明性质的可执行程序形式。
运行这些示例前，记得导入 {module}`Std.WP` 与 {module}`Std.Tactic.Do`，并打开命名空间 {namespace}`Std.WP` 和 {namespace}`Lean.Order`：

:::codeOnly
```imports
import Std.Data.HashMap
import Std.Data.HashSet
```
:::
```imports
import Std.WP
import Std.Tactic.Do
```
:::codeOnly
```lean
set_option experimental.vcgen true
```
```lean
namespace VCGenTutorial
```
```lean
section
```
:::
```lean
open Std.WP Lean.Order
```

# 前置条件与后置条件
%%%
slug := "Preconditions-and-Postconditions"
tag := "Tutorial-VCGen-Preconditions-and-Postconditions"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

一种编写程序规约的方式是提供{tech (key := "precondition") (remote := "reference")}_前置条件_ $`P`，要求程序 $`\mathit{prog}` 的调用方确保它成立，并提供{tech (key := "postcondition") (remote := "reference")}_后置条件_ $`Q`，要求 $`\mathit{prog}` 确保它成立。
如果在前置条件 $`P` 成立时运行程序 $`\mathit{prog}`，总能使后置条件 $`Q` 成立，就称程序满足该规约。

通常有许多不同的前置条件足以让程序确保后置条件成立。
毕竟，将前置条件 $`P_1` 替换为 $`P_1 \wedge P_2` 就能生成新的前置条件。
程序 $`\mathit{prog}` 与后置条件 $`Q` 的{tech (key := "weakest precondition") (remote := "reference")}_最弱前置条件_ $`\textbf{wp}⟦\mathit{prog}⟧(Q)`，是能使 $`\mathit{prog}` 确保 $`Q` 成立、且被所有其他这样的前置条件蕴含的前置条件。

证明程序结果性质的一种方法，是找出保证预期结果的最弱前置条件，再证明该条件直接为真。
这意味着后置条件无论如何都会成立。


# 循环与不变式
%%%
slug := "Loops-and-Invariants"
tag := "Tutorial-VCGen-Loops-and-Invariants"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

:::leanFirst
作为 {tactic}`vcgen` 的第一个示例，函数 {name}`mySum` 使用{ref "let-mut" (remote := "reference")}[局部可变状态]和 {keywordOf Lean.Parser.Term.doFor}`for` 循环计算数组元素之和：

```lean
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out
```
:::

若 {name}`mySum` 正确，它就等于 {name}`Array.sum`。
陈述 `mySum l = l.sum` 不提及单子，因为 {keywordOf Lean.Parser.Term.do}`do` 是 {name}`mySum` 的内部实现细节。
因此，下面的证明首先使用引理 {name}`Id.of_run_eq_wp`，将目标变为 {tactic}`vcgen` 可处理的最弱前置条件形式。
该引理说明：对于正常终止的 {name}`Id` 单子计算（`Id` 计算从不抛出异常），若能证明保证预期结果的{tech (key := "weakest precondition") (remote := "reference")}[最弱前置条件]为真，就能证明关于运行结果的事实。
随后，证明使用 {tactic}`vcgen` 将最弱前置条件表述替换为一组{tech (key := "verification conditions") (remote := "reference")}[验证条件]。

虽然 {tactic}`vcgen` 基本是自动的，但循环仍需要不变式。
{tech (key := "loop invariant") (remote := "reference")}_循环不变式_是循环体既假设又保证成立的陈述；如果在循环开始时为真，则在循环结束时也为真。

```lean
theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_run_eq_wp h
  -- Break down into verification conditions
  vcgen
  -- Specify the invariant which should hold throughout the loop.
  -- It is a function of three arguments:
  -- * `pref` is the list of elements that the loop has already visited
  -- * `suff` is the list of elements that the loop has yet to visit
  -- * `out` is the current value of the `let mut` variable
  -- Our invariant is that `out` holds the sum of the prefix.
  case inv1 => exact fun pref suff out => pref.sum = out
  -- Prove that the invariant is true at the start
  case vc1 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc2 =>
    grind
  -- Prove that our invariant is preserved at each step of the loop
  case vc3 =>
    grind
```

:::paragraph
情形标签 `vc1`、`vc2`、……按生成时出现的顺序为{tech (key := "VCs") (remote := "reference")}[验证条件]编号。
在本证明中：

* `vc1` 证明循环开始时不变式成立。
* `vc2` 证明最后一次迭代后的不变式蕴含预期性质。
* `vc3` 证明每次循环体迭代都保持不变式。
:::

:::paragraph
指定循环不变式后，证明可以缩短为仅使用 {keyword}`all_goals grind`。
```lean
theorem mySum_correct_short (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_run_eq_wp h
  vcgen
  case inv1 => exact fun pref suff out => pref.sum = out
  all_goals grind
```
这种模式十分常见，因此 {tactic}`vcgen` 为其提供专门语法：
```lean
theorem mySum_correct_shorter (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_run_eq_wp h
  vcgen invariants
  · fun pref suff out => pref.sum = out
  with finish
```
{multiCode}[{keyword}`vcgen invariants `{lit}`...`{keyword}` with `{lit}`...`] 形式提供不变式，再对每个剩余验证条件运行给定的 `grind` 步骤；`finish` 使用 `grind` 的完整自动化关闭每个条件。后文都将采用这种形式。
:::

:::paragraph
将 {name}`mySum_correct_shorter` 的证明与传统正确性证明比较很有帮助：

```lean
theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- Turn the array into a list
  cases l with | mk l =>
  -- Unfold `mySum` and rewrite `forIn` to `foldl`
  simp [mySum]
  -- Generalize the inductive hypothesis
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- Grind away
  induction l with grind
```
:::

:::paragraph
此证明与 {name}`mySum_correct_shorter` 中使用 {tactic}`vcgen` 的证明同样简短。
不过，传统方法依赖程序的若干重要性质：

* {keywordOf Lean.Parser.Term.doFor}`for` 循环不会提前 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doReturn}`return`；否则无法将 {name}`forIn` 重写为 {name Array.foldl}`foldl`。
* 循环体 {lean (type := "Nat → Nat → Nat")}`(· + ·)` 足够小，可以在证明中重复写出。
* 循环体不执行底层单子中的任何效应（即只有 {keywordOf Lean.Parser.Term.do}`do` 记法引入的效应）。
  {name}`Id` 单子没有效应，因此其所有计算都是纯的。
  虽然仍能将 {name}`forIn` 重写为 {name Array.foldlM}`foldlM`，但对单子循环体推理可能让 {tactic}`grind` 很为难。

后续各节将通过若干示例介绍 {tactic}`vcgen` 及其支持库，同时展示传统证明在何处变得困难。
困难通常来自：

* {keywordOf Lean.Parser.Term.do}`do` 块使用 {keywordOf Lean.Parser.Term.doFor}`for` 循环、{keywordOf Lean.Parser.Term.doBreak}`break` 和提前 {keywordOf Lean.Parser.Term.doReturn}`return` 等控制流构造。
* 在非 {name}`Id` 单子中使用效应，会以必须在循环不变式中反映的方式影响隐式单子上下文（状态、异常）。

{tactic}`vcgen` 能以合理的工作量应对这些挑战。

:::

# 控制流
%%%
slug := "Control-Flow"
tag := "Tutorial-VCGen-Control-Flow"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

:::leanFirst
再看一个将 {keywordOf Lean.Parser.Term.doFor}`for` 循环与提前返回组合的示例。
{name}`List.Nodup` 是断言给定列表不含重复元素的谓词。
下面的函数 {name}`nodup` 判定此谓词：

```lean
def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true
```
:::

::::paragraph

如果此函数对满足 {name}`List.Nodup` 的每个列表返回 {name}`true`，对不满足它的每个列表返回 {name}`false`，则函数正确。
与 {name}`mySum` 一样，{keywordOf Lean.Parser.Term.do}`do` 记法和 {name}`Id` 单子是 {name}`nodup` 的内部实现细节。
因此，证明先使用 {name}`Id.of_run_eq_wp` 将证明状态转换为适于 {tactic}`vcgen` 的形式：
```lean
-- A future 4.36 release adds these annotations to the library.
attribute [local grind norm]
  Lean.Order.ofProp_prop_eq Lean.Order.meet_prop_eq_and
  Lean.Order.join_prop_eq_or Lean.Order.iSup_prop_eq_exists

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ret = false ∧ ¬l.Nodup)
      (onContinue := fun pref suff seen =>
        (∀ x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup)
  with finish
```
::::


:::paragraph
```lean -show
section
variable {l : List Int} {ret : Bool} {seen : Std.HashSet Int} {pref suff : List Int}
axiom onReturn : Bool → Std.HashSet Int → Prop
axiom onContinue : List Int → List Int → Std.HashSet Int → Prop
```
证明与 {name}`mySum` 的证明结构相同：{tactic}`grind` 使用已有的 {name}`List.Nodup` 自动化解决全部验证条件，只有{tech (key := "loop invariant") (remote := "reference")}[循环不变式]不同。
由于循环有{ref "early-return" (remote := "reference")}[提前返回]，我们用支持{ref "do-elab" (remote := "reference")}[可扩展 `do` 记法精译器]的辅助函数 {lean}`Invariant.withEarlyReturnNewDo` 构造不变式。
此函数允许将不变式分为两部分：

* 循环通过提前返回值 {lean}`ret` 离开后，{lean}`onReturn ret seen` 成立。
  对 {name}`nodup`，唯一会返回的值是 {name}`false`，表示 {name}`nodup` 已确定列表_确实存在_重复。
* {lean}`onContinue pref suff seen` 是每次正常迭代后成立的不变式。
  与 {name}`mySum` 一样，列表 {lean}`pref` 保存循环已访问的元素，{lean}`suff` 保存尚未访问的元素。
  此例断言集合 {lean}`seen` 包含此前循环迭代的所有元素，并断言至今没有重复。
```lean -show
end
```
:::

:::paragraph
现在考虑以下不使用 {tactic}`vcgen` 的直接证明（刻意追求极短写法）：

```lean
theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]
```
:::

:::paragraph
几点观察：

* 它比使用 {tactic}`vcgen` 的证明还短。
* 用 {tactic}`generalize` 泛化累加器，依赖恰好只有一处 {lean (type := "Std.HashSet Int")}`∅` 可泛化；否则必须将部分程序复制进证明。对于较大函数，这不可接受。
* 给出适当引理后，{tactic}`grind` 可以按函数控制流拆分，并对 {name}`Id` 推理。
  虽然 {name}`Id.run_pure` 和 {name}`Id.run_bind` 可以这样使用，但 {name}`Id.run_seq` 不行，因为该引理不支持{tech (key := "E-matching") (remote := "reference")}[E-匹配]。
  如果 {tactic}`grind` 失败，就只能手动完成全部控制流拆分和单子推理，直到它能够再次接手。
:::

避免在证明中重复定义控制流的常见方法是使用 {tactic}`fun_cases` 或 {tactic}`fun_induction`。
遗憾的是，{tactic}`fun_cases` 无助于处理 {name}`forIn` 应用内部的控制流。
而使用 {tactic}`vcgen` 的证明从不需要复制原程序的任何部分。
{tactic}`vcgen` 自带对许多 {name}`forIn` 实现的支持；对自定义 {name}`forIn`，可以用标注 {attrs}`@[spec]` 的规约引理提供支持。
编写此类引理需要相当多工作，因为循环规约以不变式为参数，且必须证明循环保持它。
{name}`Std.Internal.PureForIn` 实例所需工作较少：它声明容器上的循环就是其元素列表 {name}`ForIn.toList` 上的循环。
有了此实例，{tactic}`vcgen` 自带的循环规约就适用于该容器。

# 使用霍尔三元组对有效应程序进行组合式推理
%%%
slug := "Compositional-Reasoning-About-Effectful-Programs-Using-Hoare-Triples"
tag := "Tutorial-VCGen-Compositional-Reasoning-About-Effectful-Programs-Using-Hoare-Triples"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

:::leanSection
```lean -show
variable (M : Type u → Type v) [Monad M] (α : Type u)
axiom M.run : M α → β → α
```
前面的示例对用 {multiCode}[{lean}`Id.run`{lit}` `{keywordOf Lean.Parser.Term.do}`do`{lit}` <prog>`] 定义的函数进行推理，以使用 {lit}`<prog>` 中的局部可变性和提前返回。
但实际程序常使用 {keywordOf Lean.Parser.Term.do}`do` 记法和单子 {lean}`M`，将状态与失败条件隐藏为隐式“效应”。
此时，函数通常省略 {name}`M.run`。
它们改为具有单子返回类型 {lean}`M α`，并能与返回该类型的其他函数良好组合。
换言之，单子属于函数的_接口_，而非仅属于实现。
:::

:::leanFirst
这里的示例包含有状态函数 {name}`mkFresh`，返回自动递增的计数器值：

```lean
structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList
```
:::

::::leanFirst
:::leanSection
```lean -show
variable (n : Nat)
```

{lean}`mkFreshN n` 返回 {lean}`n` 个“新鲜”数字，通过 {name}`mkFresh` 修改内部 {name}`Supply` 状态。
“新鲜”表示此前生成的所有数字都与下一个生成的数字不同。
可以用 {name}`List.Nodup` 表述并证明正确性性质 {name}`mkFreshN_correct`：返回的数字列表不应包含重复。
此证明中的 {name}`StateM.of_run'_eq_wp` 承担此前示例中 {name}`Id.of_run_eq_wp` 的角色。
:::

```lean
theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_run'_eq_wp h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments make `vcgen` unfold
  -- these definitions.
  vcgen [mkFreshN, mkFresh] invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · fun pref suff acc state =>
      (∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup
  with finish
```
::::

此证明展开了 {name}`mkFreshN` 和 {name}`mkFresh`。
在更大的程序中，许多函数会调用 {name}`mkFresh`，每个像上述那样的证明都会再次展开它。
我们可以改为只陈述并证明一次 {name}`mkFresh` 的行为，然后在每次调用时使用它。
只使用函数规约而从不使用其代码的证明，称为_模块化_证明。
霍尔三元组是有效应程序规约的标准形式，使这种模块化推理成为可能。

## 霍尔三元组
%%%
slug := "Hoare-Triples"
tag := "Tutorial-VCGen-Hoare-Triples"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

::::::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {α σ ε : Type u} {Pred : Type u} {EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {P : Pred} {Q : α → Pred} {epost : EPred} {prog : m α} {c : Nat}
```

{tech (key := "Hoare triple") (remote := "reference")}_霍尔三元组_由前置条件、语句和后置条件组成；它断言：若前置条件成立，则运行语句后后置条件成立。
Lean 语法写作 {lean}`⦃ P ⦄ prog ⦃ Q ⦄`，其中 {lean}`P` 是前置条件，{typed}`prog : m α` 是语句，{lean}`Q` 是后置条件。
{lean}`P` 与 {lean}`Q` 使用由具体单子 {lean}`m` 决定的断言语言。{margin}[具体来说，单子的 {name}`WP` 类型类实例规定断言如何引用单子状态或其可能抛出的异常。]
可以在分号后显式提供异常后置条件，例如 `⦃ P ⦄ prog ⦃ Q; E ⦄`。
省略异常后置条件时，默认为底元断言 `⊥`，断言程序不会抛出异常。
下文“异常”一节展示抛出异常的程序的后置条件。

:::::paragraph
将 {name}`mkFreshN_correct` 转写为霍尔三元组，就得到 {name}`mkFreshN` 的一种合适规约：
::::displayOnly
:::leanSection
```lean -show
variable {n : Nat}
```
```leanTerm
⦃fun _ => True⦄ mkFreshN n ⦃fun r _ => r.Nodup⦄
```
:::
::::
对于 {name}`StateM` 程序，断言是状态上的谓词，后置条件还以返回值作为首个参数。
前置条件 {lean}`fun (_ : Supply) => True` 对调用程序时的状态不提出任何要求。
后置条件说明结果值是不含重复元素的列表，与最终状态无关。
:::::

:::::paragraph
单步函数 {name}`mkFresh` 的规约描述其对单子状态的影响：
::::displayOnly
:::leanSection
```lean -show
variable {n : Nat}
```
```leanTerm
∀ (c : Nat),
⦃fun state => state.counter = c⦄
mkFresh
⦃fun r state => r = c ∧ c < state.counter⦄
```
全称量化的 {lean}`c` 是{tech (key := "logical variable") (remote := "reference")}[逻辑变量]，关联初始状态、结果及最终状态。
此霍尔三元组表示：

> 若 {lean}`c` 表示前状态 {name}`Supply` 的 {name}`Supply.counter` 字段，则运行 {name}`mkFresh` 会返回 {lean}`c`，并使后状态的 {name}`Supply.counter` 大于 {lean}`c`。

注意该规约损失了部分信息：{name}`mkFresh` 将状态增加任意非负量，仍能满足规约。
这是一件好事，因为规约可以_抽象掉_不重要的实现细节，使证明稳健且简短。
:::
::::
:::::


::::paragraph
三元组 {lean}`⦃ P ⦄ prog ⦃ Q ⦄` 表示 {lean}`P ⊑ wp prog Q ⊥`：前置条件蕴含本教程开头介绍的{tech (key := "weakest precondition") (remote := "reference")}[最弱前置条件]。
最弱前置条件语义 {name}`wp` 将程序解释为将后置条件映射为前置条件的{tech (key := "predicate transformer semantics") (remote := "reference")}_谓词变换器_。
霍尔三元组语法是 {name}`Std.WP.Triple` 的记法，其定义如下，省略了部分绑定：

```
structure Triple ... (x : Prog) [WP Prog Value Pred EPred]
    (pre : Pred) (post : Value → Pred) (epost : EPred) : Prop where
  intro ::
  le_wp : pre ⊑ wp x post epost
```
::::

```lean -show
variable {σ : Type u}
```
:::paragraph
{name}`WP` 类型类将结果类型为 `Value` 的程序类型 `Prog` 解释为断言类型 `Pred` 和异常断言类型 `EPred` 上的谓词变换器。
{name}`StateT`、{name}`ReaderT`、{name}`ExceptT` 等许多标准单子和单子变换器都有典范的 {name}`WP` 实例。
例如，{lean}`StateT σ` 的 {name}`WP` 实例给每个断言添加一个 {lean}`σ` 参数。
定义中的蕴涵 `⊑` 是断言格的序关系；对 {name}`StateM`，它是逐点蕴涵。
对 {name}`StateM` 程序，以下类型等价于 {name}`Std.WP.Triple`：

```lean
def StateMTriple {α σ : Type} (prog : StateM σ α)
    (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ s, P s → let (a, s') := prog.run s; Q a s'
```
```lean -show
example {α σ : Type} (prog : StateM σ α) (P : σ → Prop) (Q : α → σ → Prop) :
    Std.WP.Triple prog P Q ⊥ ↔ StateMTriple prog P Q :=
  ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩
```
:::

:::leanSection
```lean -show
variable {stmt1 stmt2 : m PUnit} {R : Pred} {Q : PUnit → Pred}
```

霍尔三元组形式的规约具有组合性，因为它们允许语句依次执行。
由 {lean}`⦃P⦄ stmt1 ⦃fun _ => R⦄` 和 {lean}`⦃R⦄ stmt2 ⦃Q⦄` 可得 {lean}`⦃P⦄ (do stmt1; stmt2) ⦃Q⦄`。
正如普通函数的证明可依赖其调用函数的引理，单子程序的证明也可以使用以霍尔三元组给出规约的引理。
:::

::::::

## 组合规约
%%%
slug := "Composing-Specifications"
tag := "Tutorial-VCGen-Composing-Specifications"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

上一节的规约会成为{tech (key := "specification lemmas") (remote := "reference")}_规约引理_。
规约引理是一个霍尔三元组，在{tech (key := "verification condition") (remote := "reference")}[验证条件]生成期间自动使用，以取得 {keywordOf Lean.Parser.Term.do}`do` 块中各条语句的前置条件和后置条件。
系统无法自动证明某条语句的后置条件蕴含下一条语句的前置条件时，这一缺失推理步骤就成为验证条件。

:::paragraph
规约引理可以作为实参传给 {tactic}`vcgen`，也可以通过 {attrs}`@[spec]` 属性注册到全局（或 {keyword}`scoped`、{keyword}`local`）规约数据库：

```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => state.counter = c⦄
    mkFresh
    ⦃fun r state => r = c ∧ c < state.counter⦄ := by
  -- Unfold `mkFresh` and blast away:
  vcgen [mkFresh] with finish

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃fun _ => True⦄ mkFreshN n ⦃fun r _ => r.Nodup⦄ := by
  -- `vcgen [mkFreshN, mkFresh_spec]` if `mkFresh_spec` were not
  -- registered with `@[spec]`
  vcgen [mkFreshN] invariants
  -- As before:
  · fun pref suff acc state =>
      (∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup
  with finish
```
:::

:::paragraph
现在，仅用 {tactic}`vcgen` 就能证明原来的正确性定理：
```lean
theorem mkFreshN_correct_modular (n : Nat) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_run'_eq_wp h
  vcgen
```
{tactic}`vcgen` 自动使用规约引理 {name}`mkFreshN_spec`。
:::

# 单子变换器与提升
%%%
slug := "Monad-Transformers-and-Lifting"
tag := "Tutorial-VCGen-Monad-Transformers-and-Lifting"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

实际程序常使用由多个{tech (key := "monad transformers") (remote := "reference")}[单子变换器]构成的单子，运算也经常从一个单子{ref "lifting-monads" (remote := "reference")}[提升]到另一个单子。
验证这些程序时必须考虑这一点。
稍作修改前一个示例即可展示这一情况。

:::codeOnly
```lean
namespace Transformers
```
```lean -show
variable {m : Type → Type} {α : Type}
attribute [-instance] Lake.instMonadLiftTOfMonadLift_lake
```
:::

::::paragraph
:::leanFirst
现在，应用包含两个分别由变换器构建的单子：
```lean
abbrev CounterM := StateT Supply (ReaderM String)

abbrev AppM := StateT Bool CounterM
```

{name}`mkFresh` 不再使用 {lean}`StateM Supply`，而使用 {lean}`CounterM`：
```lean
def mkFresh : CounterM Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n
```

{name}`mkFreshN` 使用 {name}`AppM` 定义，后者包含多个状态和读取器效应。
{name}`mkFreshN` 的定义将 {name}`mkFresh` 提升到 {name}`AppM`：
```lean
def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← mkFresh
    acc := acc.push n
  return acc.toList
```
:::
::::

::::paragraph
规约引理只有两处变化：纯命题部分用角括号包裹，不变式为 {name}`AppM` 的 {lean}`Bool` 状态增加一个实参：
```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃fun r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  vcgen [mkFresh] with finish

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃fun r => ⌜r.Nodup⌝⦄ := by
  vcgen [mkFreshN] invariants
  · fun pref suff acc _ state =>
      ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  with finish
```
角括号 `⌜p⌝` 将命题 `p` 作为_纯_断言嵌入断言语言，其成立与状态无关。
在 {name}`CounterM` 中，断言先接收 {name}`Supply` 状态，再接收读取器的 {lean}`String` 环境。
{name}`mkFresh_spec` 的前置条件只绑定状态；`⌜state.counter = c⌝` 是关于环境的纯断言：若 `state.counter = c` 成立，则它对每个环境都成立。
::::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u} {prog : m α}
```
这些证明看起来可能并不比只涉及单个单子的证明更精彩。
不过，在用户看不到的地方，证明依赖一连串 {name}`MonadLift` 实例的规约。
它们也依赖 {name}`StateT` 和 {name}`ReaderT` 的 {name}`WPMonad` 实例，使 {name Pure.pure}`pure` 与 {name Bind.bind}`bind` 的规约在每层都可用。
{name}`WPMonad` 实例只要求 {name Pure.pure}`pure` 与 {name Bind.bind}`bind` 的最弱前置条件至少与谓词变换器单子计算出的条件一样弱。
换言之，{name}`wp` 是有序单子之间的松态射。

:::

:::codeOnly
```lean
end Transformers
```
:::

# 异常
%%%
slug := "Exceptions"
tag := "Tutorial-VCGen-Exceptions"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

::::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {P : Pred} {α : Type u} {prog : m α} {Q' : α → Pred}
```

若 {keyword}`let mut` 是 {keywordOf Lean.Parser.Term.do}`do` 中对应 {name}`StateT` 的构造，那么提前 {keywordOf Lean.Parser.Term.doReturn}`return` 就对应 {name}`ExceptT`。
前面已看到 {tactic}`vcgen` 如何处理 {name}`StateT`；现在看看程序逻辑如何支持 {name}`ExceptT`。

异常是三元组除成功后置条件外还要携带异常后置条件的原因。
为理解原因，假设只有成功后置条件，且程序 {lean}`prog` 在满足 {lean}`P` 的前状态中抛出异常。
此时应当能证明 {lean}`⦃P⦄ prog ⦃Q'⦄` 吗？
由于不存在结果值，这个证明对 {lean}`Q'` 意味着什么并不清楚！

受传统程序逻辑中不终止情况的启发，有两种合理的选择：

: {tech (key := "total correctness interpretation") (remote := "reference")}_全正确性解释_

  {lean}`⦃P⦄ prog ⦃Q'⦄` 断言：若 {lean}`P` 成立，则 {lean}`prog` 正常终止，_且_结果满足 {lean}`Q'`。

: {tech (key := "partial correctness interpretation") (remote := "reference")}_部分正确性解释_

  {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` 断言：若 {lean}`P` 成立，_且_ {lean}`prog` 正常终止，_则_结果满足 {lean}`Q'`。

不显式提供异常后置条件的三元组使用底元断言 {lean}`(⊥ : EPred)`，因此采用全正确性解释：异常必须使 `⊥` 成立，所以不允许抛出异常。
顶元断言 {lean}`(⊤ : EPred)` 允许所有异常，产生部分正确性解释。

对上述例子，{lean}`⦃P⦄ prog ⦃Q'⦄` 无法证明，但 {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` 可平凡证明。
在 {lean}`(⊥ : EPred)` 与 {lean}`(⊤ : EPred)` 之间，异常后置条件表达一_系列_不同的正确性性质。

::::

:::codeOnly
```lean
namespace Exceptions
```
:::


例如，假设生成新数字的 {name}`Supply` 有界，并希望耗尽时抛出异常。
那么 {name}`mkFresh` 应_仅在_供应确实耗尽时抛出异常，如以下实现：
```lean
structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set { supply with counter := n + 1, property := by grind }
    pure n
```

以下正确性性质表达了这一点：
```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => state.counter = c⦄
    mkFresh
    ⦃fun r state => r = c ∧ c < state.counter;
      fun _ state => c = state.counter ∧ c = state.limit⦄ := by
  vcgen [mkFresh] with finish
```

分号后的异常后置条件在 {name}`mkFresh` 抛出异常时适用。
单子的 {name}`WP` 实例决定两种后置条件的类型：异常后置条件接收抛出的异常而非结果值，每层状态再提供一个额外参数。

:::leanFirst
在新单子中，除类型签名外，{name}`mkFreshN` 的实现不变：
```lean
def mkFreshN (n : Nat) : EStateM String Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList
```
:::

:::paragraph
不过，规约引理必须同时考虑正常终止与抛出异常；循环不变式则保持不变：
```lean
@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃fun _ => True⦄
    mkFreshN n
    ⦃fun r _ => r.Nodup;
      fun _msg state => state.counter = state.limit⦄ := by
  vcgen [mkFreshN] invariants
  · fun pref suff acc state =>
      (∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup
  with finish
```
:::

:::paragraph
最终证明与此前一样，使用规约引理和 {tactic}`vcgen`：
```lean
theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_run_eq_wp h
  vcgen with finish
```
:::

:::codeOnly
```lean
end Exceptions
```
:::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type} {σ ε : Type}
```

{lean}`StateT σ` 层将断言类型 `Pred` 变为 `σ → Pred`，异常后置条件类型不变。
{lean}`ExceptT ε` 层保持断言类型不变，将异常后置条件类型 `EPred` 变为 {lean}`(ε → Pred) × EPred`，增加一个 `ε → Pred` 类型的异常分支。
{lean}`EStateM ε σ` 的 {name}`WP` 实例使用 `σ → Prop` 类型的断言与 `ε → σ → Prop` 类型的异常后置条件，对应等价变换器栈 {lean}`ExceptT ε (StateM σ)` 的单个异常分支。
:::


# 扩展 `vcgen` 以支持自定义单子
%%%
slug := "Extending--vcgen--With-Support-for-Custom-Monads"
tag := "Verifying-Imperative-Programs-Using--vcgen--Extending--vcgen--With-Support-for-Custom-Monads"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

{tactic}`vcgen` 框架被设计为可扩展。
此前介绍的单子都没有以任何方式硬编码进 {tactic}`vcgen`。
相反，{tactic}`vcgen` 依赖 {name}`WP`、{name}`WPMonad` 类型类实例和用户提供的规约，生成{tech (key := "verification conditions") (remote := "reference")}[验证条件]。
每个程序类型需要 {name}`WP` 实例，单子还需要 {name}`WPMonad` 实例。
本节为一个自定义单子构造这两个实例。

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type} [Assertion Pred] [Assertion EPred] {α : Type u}
```

{name}`WP` 实例定义单子 {lean}`m` 到谓词变换器 {lean}`PredTrans Pred EPred α` 的最弱前置条件解释，
对应的 {name}`WPMonad` 实例则断言此转换对 {name Pure.pure}`pure` 与 {name Bind.bind}`bind` 可靠。
:::

:::::paragraph
::::leanFirst
假设希望用 `vcgen` 为 [`Aeneas`](https://github.com/AeneasVerif/aeneas) 生成的程序生成验证条件。
`Aeneas` 将 Rust 程序转换为以下 {name}`Result` 单子中的 Lean 程序：

```lean
inductive Error where
  | integerOverflow: Error
  -- ... more error kinds ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
```
:::codeOnly
```lean
instance Result.instMonad : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance Result.instLawfulMonad : LawfulMonad Result := by
  apply LawfulMonad.mk' _
  all_goals (dsimp [Functor.map, bind, pure]; grind)
```
:::
::::
:::::

:::paragraph
{inst}`Monad Result` 和 {inst}`LawfulMonad Result` 实例都已提供。
使 {tactic}`vcgen` 支持该单子需要：

1. 为 {name}`Result` 添加 {name}`WP` 与 {name}`WPMonad` 实例。
2. 为加法等基本 Rust 原语的转换结果注册规约引理。
:::

:::::paragraph
::::leanSection

```lean -show
universe u v
variable {α : Type u} {v : α} {e : Error}
```
{name}`Result` 的 {name}`WP` 实例指定断言类型为 {lean}`Prop`，因为没有类似状态的效应；异常后置条件类型为 {lean}`Error → Prop`，因为只有一种类型为 {lean}`Error` 的异常。
{name}`WP` 实例将 {lean}`Result α` 中的程序转换为 {lean}`PredTrans Prop (Error → Prop) α` 中的谓词变换器。
也就是将后置条件与异常后置条件映射到最弱前置条件的函数。
{name}`WP.wp` 的实现类似于 {lean}`Except Error` 的实现。
{name}`Result` 的每种情形直接决定前置条件：
* {lean}`Result.ok v` 产生在 {lean}`v` 处的成功后置条件。
* {lean}`Result.fail e` 产生在 {lean}`e` 处的异常后置条件。
* {name}`Result.div` 产生 {lean}`False`，意味着所有规约都断言程序不会发散。
::::
```lean
instance : WP (Result α) α Prop (Error → Prop) where
  trans
    | .ok v => ⟨fun post _ => post v⟩
    | .fail e => ⟨fun _ epost => epost e⟩
    | .div => ⟨fun _ _ => False⟩
  trans_monotone x := by
    intro post post' epost epost' hepost hpost
    cases x <;> simp_all [PartialOrder.rel]
```
:::::

:::paragraph
{name}`WPMonad` 实例在字段 {name}`WPMonad.pure_le_wp_pure` 和 {name}`WPMonad.bind_le_wp_bind` 中证明此解释对 {name Pure.pure}`pure` 和 {name Bind.bind}`bind` 可靠。
对于 {name}`bind`，需要展开 {name}`wp` 和 {name}`bind` 的定义，以暴露嵌套的 {keyword}`match` 结构；情形拆分和 {tactic}`simp` 就能轻松解决。
```lean
instance Result.instWPMonad : WPMonad Result Prop (Error → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure x post epost := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := by
    cases x <;> simp [wp, WP.trans, bind, PartialOrder.rel]
```
:::

::: paragraph
最后，还为 {lean}`Result` 证明一个类似 {name}`Except.of_eq_wp` 的可靠性引理。
```lean
theorem Result.of_eq_wp {α} {x prog : Result α}
    (h : prog = x) (P : Result α → Prop)
    (hwp : wp prog (fun a => P (.ok a)) (fun e => P (.fail e))) :
      P x := by
  subst h
  match prog with
  | .ok a   => simpa [wp, WP.trans] using hwp
  | .fail e => simpa [wp, WP.trans] using hwp
  | .div    => simp [wp, WP.trans] at hwp
```
:::

{name}`WP` 解释的定义决定可通过 {name}`Result.of_eq_wp` 从已证明的规约推导出哪些性质。
该引理将最弱前置条件与运行程序所得的结果联系起来。

:::paragraph
第二步为 Rust 原语注册规约引理。
例如，下面定义 {name}`Result` 中的 {name}`UInt32` 加法，建模整数溢出：

```lean
instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)
```
:::

:::paragraph
需要注册两个相关规约引理：

```lean
@[spec]
theorem Result.throw_spec {α} {post : α → Prop}
    {epost : Error → Prop} (e : Error) :
    ⦃epost e⦄ throw (m := Result) (α := α) e ⦃post; epost⦄ :=
  ⟨PartialOrder.rel_refl⟩

@[spec]
theorem addOp_ok_spec {x y} (h : x.toNat + y.toNat < UInt32.size) :
    ⦃True⦄
    addOp x y
    ⦃fun r => r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⦄ := by
  vcgen [addOp]
  all_goals simp_all; try grind
```
:::

:::paragraph
这些就已足以证明以下示例：

```lean
example :
  ⦃True⦄
  (do let mut x ← addOp 1 3
      for _ in [:4] do
        x ← addOp x 5
      return x : Result UInt32)
  ⦃fun r => r.toNat = 24⦄ := by
  vcgen invariants
  · fun pref suff x => x.toNat = 4 + 5 * pref.length
  all_goals simp_all
  all_goals grind
```
:::

# 解决验证条件
%%%
slug := "Discharging-Verification-Conditions"
tag := "Tutorial-VCGen-Discharging-Verification-Conditions"
summary := inlines!""
exampleStyle := .inlineLean `VCGenTutorial
%%%

{tactic}`vcgen` 的首要目标之一，是将程序分解为易于理解的{tech (key := "verification conditions") (remote := "reference")}[验证条件]。
验证条件是普通 Lean 目标，因此可以使用任何策略解决。
当断言语言具体时（如 {name}`Id` 或 {name}`StateM` 程序），目标直接描述结果值和状态，可使用 {tactic}`grind`。

生成验证条件时，{tactic}`vcgen` 将目标上下文内部化到 `grind` 的 E-图中。
`with` 子句在该共享上下文中对每个剩余验证条件运行一个 `grind` 模式步骤，避免对各个条件重复内部化上下文。
`finish` 使用 `grind` 的完整自动化关闭验证条件。

:::codeOnly
```lean
end
```
```lean
end VCGenTutorial
```
:::
