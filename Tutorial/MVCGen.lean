/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual
import VersoTutorial

import Manual.Meta
import Manual.Papers

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

set_option linter.deprecated.syntax false

#doc (Tutorial) "使用 `mvcgen` 验证命令式程序" =>
%%%
tag := "mvcgen-tactic-tutorial"
slug := "mvcgen"
summary := inlines!"演示如何使用 Lean 的验证条件生成器，方便地对单子程序性质进行组合式证明。"
exampleStyle := .inlineLean `MVCGenTutorial
%%%

本教程自顶向下介绍 {tactic}`mvcgen` 最重要的概念。
运行这些示例前，记得导入 {module}`Std.Tactic.Do` 并打开 {namespace}`Std.Do`：

:::codeOnly
```imports
import Std.Data.HashMap
import Std.Data.HashSet
```
:::
```imports
import Std.Tactic.Do
```
:::codeOnly
```lean
set_option linter.deprecated.syntax false
```
:::
```lean
open Std.Do
```

# 前置条件与后置条件
%%%
slug := "Preconditions-and-Postconditions"
tag := "Tutorial-MVCGen-Preconditions-and-Postconditions"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

一种编写程序规约的方式是提供{tech (key := "mvcgen precondition") (remote := "reference")}_前置条件_ $`P`，要求程序 $`\mathit{prog}` 的调用方确保它成立，并提供{tech (key := "mvcgen postcondition") (remote := "reference")}_后置条件_ $`Q`，要求 $`\mathit{prog}` 确保它成立。
如果在前置条件 $`P` 成立时运行程序 $`\mathit{prog}`，总能使后置条件 $`Q` 成立，就称程序满足该规约。

通常有许多不同的前置条件足以让程序确保后置条件成立。
毕竟，将前置条件 $`P_1` 替换为 $`P_1 \wedge P_2` 就能生成新的前置条件。
程序 $`\mathit{prog}` 与后置条件 $`Q` 的{tech (key := "mvcgen weakest precondition") (remote := "reference")}_最弱前置条件_ $`\textbf{wp}⟦\mathit{prog}⟧(Q)`，是能使 $`\mathit{prog}` 确保 $`Q` 成立、且被所有其他这样的前置条件蕴含的前置条件。

证明程序结果性质的一种方法，是找出保证预期结果的最弱前置条件，再证明该条件直接为真。
这意味着后置条件无论如何都会成立。


# 循环与不变式
%%%
slug := "Loops-and-Invariants"
tag := "Tutorial-MVCGen-Loops-and-Invariants"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

:::leanFirst
作为 {tactic}`mvcgen` 的第一个示例，函数 {name}`mySum` 使用{ref "let-mut" (remote := "reference")}[局部可变状态]和 {keywordOf Lean.Parser.Term.doFor}`for` 循环计算数组元素之和：

```lean
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out
```
:::

若 {name}`mySum` 正确，它就等于 {name}`Array.sum`。
在 {name}`mySum` 中，{keywordOf Lean.Parser.Term.do}`do` 属于内部实现细节，函数签名并未提及任何单子。
因此，证明首先使用引理 {name}`Id.of_wp_run_eq` 将目标变为适合 {tactic}`mvcgen` 的形式。
该引理说明：对于正常终止的 {name}`Id` 单子计算（`Id` 计算从不抛出异常），证明保证预期结果的{tech (key := "mvcgen weakest precondition") (remote := "reference")}[最弱前置条件]为真，即可证明关于运行结果的事实。
随后使用 {tactic}`mvcgen` 将最弱前置条件表述替换为一组{tech (key := "mvcgen verification conditions") (remote := "reference")}[验证条件]。

虽然 {tactic}`mvcgen` 基本是自动的，但循环仍需要不变式。
{tech (key := "mvcgen loop invariant") (remote := "reference")}_循环不变式_是循环体既假设又保证成立的陈述；如果在循环开始时为真，则在循环结束时也为真。

```lean
theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which should hold throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into `xs.prefix` and `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals
  -- by "leaving the proof mode". `mleave` is just
  -- `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1 ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of
    -- the cursor passed to the invariant. Unpacking the
    -- (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case vc2 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc3 h =>
    grind
```

:::paragraph
注意，情形标签实际上是完整标签的唯一前缀。
引用情形时应只用此前缀；后缀仅提示用户该{tech (key := "mvcgen VC") (remote := "reference")}[验证条件]的来源。
例如：

* `vc1.step` 表示此{tech (key := "mvcgen VC") (remote := "reference")}[验证条件]证明循环的归纳步骤。
* `vc2.a.pre` 用于证明目标假设蕴含某个规约（这里为 {name}`forIn`）的前置条件。
* `vc3.a.post.success` 用于证明某个规约（这里为 {name}`forIn`）的后置条件蕴含预期性质。
:::

:::paragraph
指定循环不变式后，证明可以缩短为 {keyword}`all_goals mleave; grind`（其中 {tactic}`mleave` 离开有状态证明模式并清理证明状态）。
```lean
theorem mySum_correct_short (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  all_goals mleave; grind
```
这种模式十分常见，因此 {tactic}`mvcgen` 为其提供专门语法：
```lean
theorem mySum_correct_shorter (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  with grind
```
{multiCode}[{keyword}`mvcgen invariants `{lit}`...`{keyword}` with `{lit}`...`] 是上面
策略序列 {multiCode}[{keyword}`mvcgen; case`{lit}` inv1 => ...`{keyword}`; all_goals mleave; grind`]
的简写。后文都将采用这种形式。
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
此证明与 {name}`mySum_correct_shorter` 中使用 {tactic}`mvcgen` 的证明同样简短。
不过，传统方法依赖程序的若干重要性质：

* {keywordOf Lean.Parser.Term.doFor}`for` 循环不会提前 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doReturn}`return`；否则无法将 {name}`forIn` 重写为 {name Array.foldl}`foldl`。
* 循环体 {lean (type := "Nat → Nat → Nat")}`(· + ·)` 足够小，可以在证明中重复写出。
* 循环体不执行底层单子中的任何效应（即只有 {keywordOf Lean.Parser.Term.do}`do` 记法引入的效应）。
  {name}`Id` 单子没有效应，因此其所有计算都是纯的。
  虽然仍能将 {name}`forIn` 重写为 {name Array.foldlM}`foldlM`，但对单子循环体推理可能让 {tactic}`grind` 很为难。

后续各节将通过若干示例介绍 {tactic}`mvcgen` 及其支持库，同时展示传统证明在何处变得困难。
困难通常来自：

* {keywordOf Lean.Parser.Term.do}`do` 块使用 {keywordOf Lean.Parser.Term.doFor}`for` 循环、{keywordOf Lean.Parser.Term.doBreak}`break` 和提前 {keywordOf Lean.Parser.Term.doReturn}`return` 等控制流构造。
* 在非 {name}`Id` 单子中使用效应，会以必须在循环不变式中反映的方式影响隐式单子上下文（状态、异常）。

{tactic}`mvcgen` 能以合理的工作量应对这些挑战。

:::

# 控制流
%%%
slug := "Control-Flow"
tag := "Tutorial-MVCGen-Control-Flow"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
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
因此，证明先使用 {name}`Id.of_wp_run_eq` 将证明状态变为适于 {tactic}`mvcgen` 的形式：
```lean
theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind
```
::::


:::paragraph
```lean -show
section
variable {l : List Int} {ret : Bool} {seen : Std.HashSet Int} {xs : l.Cursor}
axiom onReturn : Bool → Std.HashSet Int → SPred PostShape.pure.args
axiom onContinue : l.Cursor → Std.HashSet Int → SPred PostShape.pure.args
axiom onExcept : ExceptConds PostShape.pure
```
证明具有与最初 {name}`mySum` 示例相同的简短结构，因为我们再次将全部证明交给 {tactic}`grind` 及其已有的 {name}`List.Nodup` 自动化。
因此，唯一差别在于{tech (key := "mvcgen loop invariant") (remote := "reference")}[循环不变式]。
由于循环有{ref "early-return" (remote := "reference")}[提前返回]，我们用支持{ref "do-elab" (remote := "reference")}[可扩展 `do` 记法精译器]的辅助函数 {lean}`Invariant.withEarlyReturnNewDo` 构造不变式。
此函数允许将不变式分为三部分：

* 循环通过提前返回值 {lean}`ret` 离开后，{lean}`onReturn ret seen` 成立。
  对 {name}`nodup`，唯一会返回的值是 {name}`false`，表示 {name}`nodup` 已确定列表_确实存在_重复。
* {lean}`onContinue xs seen` 是常规归纳步骤，证明每次迭代都保持不变式。
  迭代状态由游标 {lean}`xs` 表示。
  此例断言集合 {lean}`seen` 包含此前循环迭代的所有元素，并断言至今没有重复。
* 循环抛出异常时，{lean}`onExcept` 必须成立。
  {lean}`Id` 不含异常，因此这里省略它以使用默认值。
  （后面将讨论异常。）
```lean -show
end
```
:::

:::paragraph
注意，`mvcgen invariants?` 会建议一个初始不变式，因此无需记住指定不变式的精确语法：
```lean (name := invariants?)
example (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants? <;> sorry
```
该策略会建议一个起始不变式。
这一起点不能使证明成功——毕竟，如果系统能推断出所需不变式，就不需要用户指定了——但它能提示在当前单子中书写断言的正确语法：
```leanOutput invariants?
Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => ⌜(r = true ↔ l.Nodup) ∧ l.Nodup⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = ∅ ∨ xs.suffix = [] ∧ l.Nodup⌝)
```
:::

:::paragraph
现在考虑以下不使用 {tactic}`mvcgen` 的直接证明（刻意追求极短写法）：

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

* 它比使用 {tactic}`mvcgen` 的证明还短。
* 用 {tactic}`generalize` 泛化累加器，依赖恰好只有一处 {lean (type := "Std.HashSet Int")}`∅` 可泛化；否则必须将部分程序复制进证明。对于较大函数，这不可接受。
* 给出适当引理后，{tactic}`grind` 可以按函数控制流拆分，并对 {name}`Id` 推理。
  虽然 {name}`Id.run_pure` 和 {name}`Id.run_bind` 可以这样使用，但 {name}`Id.run_seq` 不行，因为该引理不支持{tech (key := "E-matching") (remote := "reference")}[E-匹配]。
  如果 {tactic}`grind` 失败，就只能手动完成全部控制流拆分和单子推理，直到它能够再次接手。
:::

避免在证明中重复定义控制流的常见方法是使用 {tactic}`fun_cases` 或 {tactic}`fun_induction`。
遗憾的是，{tactic}`fun_cases` 无助于处理 {name}`forIn` 应用内部的控制流。
另一方面，{tactic}`mvcgen` 自带对许多 {name}`forIn` 实现的支持。
通过 {attrs}`@[spec]` 标注，可以方便地扩展到自定义 {name}`forIn` 实现。
此外，使用 {tactic}`mvcgen` 的证明从不需要复制原程序的任何部分。

# 使用霍尔三元组对有效应程序进行组合式推理
%%%
slug := "Compositional-Reasoning-About-Effectful-Programs-Using-Hoare-Triples"
tag := "Tutorial-MVCGen-Compositional-Reasoning-About-Effectful-Programs-Using-Hoare-Triples"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
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
此证明中的 {name}`StateM.of_wp_run'_eq` 承担此前示例中 {name}`Id.of_wp_run_eq` 的角色。
:::

```lean
theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments to `mvcgen` add to an
  -- internal `simp` set and makes `mvcgen` unfold these definitions.
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```
::::

## 霍尔三元组
%%%
slug := "Hoare-Triples"
tag := "Tutorial-MVCGen-Hoare-Triples"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

::::::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [Monad m] [WP m ps] {α σ ε : Type u} {P : Assertion ps} {Q : PostCond α ps} {prog : m α} {c : Nat}
```

{tech (key := "mvcgen Hoare triple") (remote := "reference")}_霍尔三元组_由前置条件、语句和后置条件组成；它断言：若前置条件成立，则运行语句后后置条件成立。
Lean 语法写作 {lean}`⦃ P ⦄ prog ⦃ Q ⦄`，其中 {lean}`P` 是前置条件，{typed}`prog : m α` 是语句，{lean}`Q` 是后置条件。
{lean}`P` 与 {lean}`Q` 使用由具体单子 {lean}`m` 决定的断言语言。{margin}[具体来说，单子的 {name}`WP` 实例规定断言如何引用单子状态或其可能抛出的异常。]

:::leanSection
```lean -show
variable  {stmt1 stmt2 : m PUnit} {ps : PostShape.{0}} {P : Assertion ps} {Q : PostCond Unit ps} {P' : Assertion ps} {Q' : PostCond Unit ps}
```

霍尔三元组形式的规约具有组合性，因为它们允许语句依次执行。
若有 {lean}`⦃P⦄ stmt1 ⦃Q⦄` 与 {lean}`⦃P'⦄ stmt2 ⦃Q'⦄`，且 {lean}`Q` 蕴含 {lean}`P'`，则有 {lean}`⦃P⦄ (do stmt1; stmt2) ⦃Q'⦄`。
正如普通函数的证明可依赖其调用函数的引理，单子程序的证明也可以使用以霍尔三元组给出规约的引理。
:::

:::::paragraph
将 {name}`mkFreshN_correct` 转写为霍尔三元组，就得到 {name}`mkFresh` 的一种合适规约：
::::displayOnly
:::leanSection
```lean -show
variable {n : Nat}
```
```leanTerm
⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄
```
:::
::::
```lean -show
variable {p : Prop}
```
角括号将命题嵌入单子断言语言，因此 {lean}`⌜p⌝` 是关于命题 {lean}`p` 的断言。
前置条件 {lean}`⌜True⌝` 断言 {lean}`True` 为真；用这个平凡前置条件表示规约对调用时的状态没有要求。
后置条件表示结果是不含重复元素的列表。
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
⦃fun state => ⌜state.counter = c⌝⦄
mkFresh
⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄
```
在状态单子中，前置条件可以运行代码前的状态值为参数。
这里全称量化的 {name}`Nat` 用于_关联_初始与最终状态；前置条件将其关联到初始状态。
类似地，后置条件也可以接收最终状态作为参数。
此霍尔三元组表示：

> 若 {lean}`c` 表示前状态 {name}`Supply` 的 {name}`Supply.counter` 字段，则运行 {name}`mkFresh` 会返回 {lean}`c`，并使后状态的 {name}`Supply.counter` 大于 {lean}`c`。

注意该规约损失了部分信息：{name}`mkFresh` 将状态增加任意非负量，仍能满足规约。
这是一件好事，因为规约可以_抽象掉_不重要的实现细节，使证明稳健且简短。
:::
::::
:::::


:::paragraph
霍尔三元组基于有状态谓词逻辑，以及将单子程序转换到该逻辑中的{tech (key := "mvcgen weakest precondition") (remote := "reference")}[最弱前置条件]语义 {lean}`wp⟦prog⟧` 定义。
最弱前置条件语义将程序解释为从后置条件到程序保证它所需的最弱前置条件的映射；在此解释下，程序被理解为{tech (key := "mvcgen predicate transformer semantics") (remote := "reference")}_谓词变换器_。
霍尔三元组语法是 {name}`Std.Do.Triple` 的记法：

```lean -keep
-- This is the definition of Std.Do.Triple:
def Triple [WP m ps] {α : Type u} (prog : m α)
    (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦prog⟧ Q
```
:::

```lean -show
variable {σ : Type u}
```
:::paragraph
{name}`WP` 类型类将单子 {lean}`m` 映射为 {name}`PostShape` {lean}`ps`；该 {name}`PostShape` 决定 {name}`Std.Do.Triple` 的确切形状。
{name}`StateT`、{name}`ReaderT`、{name}`ExceptT` 等许多标准单子变换器都有典范的 {name}`WP` 实例。
例如，{lean}`StateT σ` 的 {name}`WP` 实例给每个 {name}`Assertion` 添加一个 {lean}`σ` 参数。
有状态蕴涵 `⊢ₛ` 会沿这些额外的 {lean}`σ` 参数进行 η-展开。
对于 {name}`StateM` 程序，以下类型与 {name}`Std.Do.Triple` 定义等价：

```lean
def StateMTriple {α σ : Type u} (prog : StateM σ α)
    (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := prog.run s; (Q.1 a s').down
```
```lean -show
example : @StateMTriple α σ = Std.Do.Triple (m := StateM σ) := rfl
```
:::


```lean -show
variable {p : Prop}
```

常用的后置条件记法 `⇓ r => ...` 将类型为 {lean}`α → Assertion ps` 的断言注入到
{lean}`PostCond α ps` 中（`⇓` 应像 `fun` 那样理解）；对于 {name}`StateM`，通过与空元组 {name}`PUnit.unit` 配对实现。
引入异常后，后置条件的形状会更加丰富。
记法 {lean}`⌜p⌝` 将纯假设 {lean}`p` 嵌入有状态断言。
反过来，若有状态假设 {lean}`P` 与某个 {lean}`p` 的 {lean}`⌜p⌝` 等价，
则称它为_纯_假设。
纯的有状态假设可以自由移入普通 Lean 上下文，再移回来。
（可以用 {tactic}`mpure` 策略手动进行。）

::::::

## 组合规约
%%%
slug := "Composing-Specifications"
tag := "Tutorial-MVCGen-Composing-Specifications"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

像 {multiCode}[{tactic}`mvcgen`{lit}` [`{name}`mkFreshN`{lit}`, `{name}`mkFresh`{lit}`]`] 这样嵌套展开定义，虽然直接，却对小程序有效。
更具组合性的方式是为每个单子函数建立独立的{tech (key := "mvcgen specification lemmas") (remote := "reference")}_规约引理_。
规约引理是一个霍尔三元组，在{tech (key := "mvcgen verification condition") (remote := "reference")}[验证条件]生成期间自动使用，以获得 {keywordOf Lean.Parser.Term.do}`do` 块各语句的前置条件和后置条件。
系统无法自动证明某条语句的后置条件蕴含下一条语句的前置条件时，这一缺失推理步骤就成为验证条件。

:::paragraph
规约引理可以作为实参传给 {tactic}`mvcgen`，也可以通过 {attrs}`@[spec]` 属性注册到全局（或 {keyword}`scoped`、{keyword}`local`）规约数据库：

```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- Unfold `mkFresh` and blast away:
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mvcgen [mkFreshN, mkFresh_spec]` if `mkFresh_spec` were not
  -- registered with `@[spec]`
  mvcgen [mkFreshN]
  invariants
  -- As before:
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```
:::

:::paragraph
现在，仅用 {tactic}`mvcgen` 就能证明原来的正确性定理：
```lean
theorem mkFreshN_correct_compositional (n : Nat) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  mvcgen
```
{tactic}`mvcgen` 自动使用规约引理 {name}`mkFreshN_spec`。
:::


## 关于纯前置条件与框架规则的进阶说明
%%%
slug := "An-Advanced-Note-About-Pure-Preconditions-and-a-Notion-of-Frame-Rule"
tag := "Verifying-Imperative-Programs-Using--mvcgen--Compositional-Reasoning-About-Effectful-Programs-Using-Hoare-Triples--An-Advanced-Note-About-Pure-Preconditions-and-a-Notion-of-Frame-Rule"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

本小节略有旁逸，初次阅读可以跳过。

::::leanSection

:::codeOnly
```lean
axiom M : Type → Type
variable {x y : UInt8} [Monad M] [WP M .pure]
def addQ (x y : UInt8) : M UInt8 := pure (x + y)
local infix:1023 " +? " => addQ
```
```lean -show
axiom dots {α} : α
local notation "…" => dots
```
:::

假设受 [`Aeneas`](https://github.com/AeneasVerif/aeneas) 启发的某个单子加法函数 {typed}`x +? y : M UInt8` 的规约
要求加法不溢出，即 `h : x.toNat + y.toNat ≤ UInt8.size`。
应将此要求编码为规约的普通 Lean 假设（`add_spec_hyp`），还是用 `⌜·⌝` 记法编码为霍尔三元组的纯前置条件（`add_spec_pre`）？

:::displayOnly
```lean
theorem add_spec_hyp (x y : UInt8)
    (h : x.toNat + y.toNat ≤ UInt8.size) :
    ⦃⌜True⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := …

theorem add_spec_pre (x y : UInt8) :
    ⦃⌜x.toNat + y.toNat ≤ UInt8.size⌝⦄
    x +? y
    ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := …
```
:::

::::

推荐第一种方式，虽然实际中通常没有区别。
验证条件生成器会将纯假设从有状态上下文移入普通 Lean 上下文，因此第二种形式实际上会变成第一种。
这称为将假设{deftech (key := "mvcgen framing")}_框架化_（参见 {tactic}`mpure` 和 {tactic}`mframe` 策略）。
Lean 上下文中的假设属于有状态逻辑不可变的{deftech (key := "mvcgen frame")}_框架_，因为与有状态假设不同，它们经过后果规则后仍然保留。

# 单子变换器与提升
%%%
slug := "Monad-Transformers-and-Lifting"
tag := "Tutorial-MVCGen-Monad-Transformers-and-Lifting"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

实际程序常使用由多个{tech (key := "monad transformers") (remote := "reference")}[单子变换器]构成的单子，运算也经常从一个单子{ref "lifting-monads" (remote := "reference")}[提升]到另一个单子。
验证这些程序时必须考虑这一点。
稍作修改前一个示例即可展示这一情况。

:::codeOnly
```lean
namespace Transformers
```
```lean -show
variable {m : Type → Type} {α : Type} {ps : PostShape.{0}}
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
随后，基于 {tactic}`mvcgen` 的证明无需修改即可通过：
```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `liftCounterM` here ensures unfolding
  mvcgen [mkFreshN]
  invariants
  · ⇓⟨xs, acc⟩ _ state =>
      ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```
::::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {α  : Type u}  {prog : m α}
```
{name}`WPMonad` 类型类断言 {lean}`wp⟦prog⟧` 对 {name}`Monad` 运算保持分配关系（即“单子态射”）。
此证明看起来可能并不比只涉及一个单子时更精彩。
不过，在用户看不到的地方，证明依赖一连串 {name}`MonadLift` 实例的规约。

:::

:::codeOnly
```lean
end Transformers
```
:::

# 异常
%%%
slug := "Exceptions"
tag := "Tutorial-MVCGen-Exceptions"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

::::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α  : Type u}  {prog : m α} {Q' : α → Assertion ps}
```

若 {keyword}`let mut` 是 {keywordOf Lean.Parser.Term.do}`do` 中对应 {name}`StateT` 的构造，那么提前 {keywordOf Lean.Parser.Term.doReturn}`return` 就对应 {name}`ExceptT`。
前面已看到 {tactic}`mvcgen` 如何处理 {name}`StateT`；现在看程序逻辑如何支持 {name}`ExceptT`。

异常是后置条件类型 {lean}`PostCond α ps` 不仅是成功情形下的单个 {lean}`α → Assertion ps` 条件的原因。
为理解原因，假设它仅包含该条件，且程序 {lean}`prog` 在满足 {lean}`P` 的前状态中抛出异常。
此时应能证明 {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 吗？
（回想一下，`⇓` 在语法上类似 `fun`。）
没有结果 `r`，因此这个证明对 {lean}`Q'` 意味着什么并不清楚！

受传统程序逻辑中不终止情况的启发，有两种合理的选择：

: {tech (key := "mvcgen total correctness interpretation") (remote := "reference")}_全正确性解释_

  {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 断言：若 {lean}`P` 成立，则 {lean}`prog` 终止，_且_结果满足 {lean}`Q'`。

: {tech (key := "mvcgen partial correctness interpretation") (remote := "reference")}_部分正确性解释_

  {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 断言：若 {lean}`P` 成立，_且_ {lean}`prog` 终止，_则_结果满足 {lean}`Q'`。

记法 {lean}`⇓ r => Q' r` 具有全正确性解释，而 {lean}`⇓? r => Q' r` 具有部分正确性解释。

在上述例子中，{lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 无法证明，但 {lean}`⦃P⦄ prog ⦃⇓? r => Q' r⦄` 可以平凡证明。
不过，这种二选一的情形提示我们，实际存在一_系列_可表达的正确性性质。
`Std.Do` 的后置条件概念 {name}`PostCond` 支持这一系列性质。

::::

:::codeOnly
```lean
namespace Exceptions
```
:::


例如，假设生成新数字的 {name}`Supply` 有界，并希望耗尽时抛出异常。
那么 {name}`mkFreshN` 应_仅在_供应确实耗尽时抛出异常，如下实现所示：
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
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝,
          fun _ state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh] with grind
```

此性质中的后置条件有两个分支：首个处理正常终止，第二个处理抛出异常。
单子的 {name}`WP` 实例既决定后置条件有多少分支，也决定每个分支的参数数量：每种可能触发的异常增加一个分支，每层状态增加一个参数。

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
但规约引理必须在后置条件和循环不变式中同时考虑正常终止及抛出异常：
```lean
@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝,
          fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN]
  invariants
  · post⟨fun ⟨xs, acc⟩ state =>
           ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
         fun _msg state => ⌜state.counter = state.limit⌝⟩
  with grind
```
:::

:::paragraph
最终证明与此前一样，使用规约引理和 {tactic}`mvcgen`：
```lean
theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_wp_run_eq h
  mvcgen
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
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α σ ε : Type u}  {prog : m α} {Q' : α → Assertion ps}
```

正如 {lean}`StateT σ` 一类单子变换器使 {name}`WP` 映射到的 {lean}`ps` 中增加一层 {lean}`PostShape.arg σ`，每个 {lean}`ExceptT ε` 一类的层也增加一层 {lean}`PostShape.except ε`。

每个 {lean}`PostShape.arg σ` 在 {lean}`Assertion` 语言中增加一层 `σ → ...`。
每个 {lean}`PostShape.except ε` 保持 {lean}`Assertion` 语言不变，但在后置条件中
增加一个异常条件。
因此，{lean}`EStateM ε σ` 的 {name}`WP` 实例映射到 {name}`PostShape` {lean}`PostShape.except ε (.arg σ .pure)`，
与 {lean}`ExceptT ε (StateM σ)` 相同。
:::


# 扩展 `mvcgen` 以支持自定义单子
%%%
slug := "Extending--mvcgen--With-Support-for-Custom-Monads"
tag := "Verifying-Imperative-Programs-Using--mvcgen--Extending--mvcgen--With-Support-for-Custom-Monads"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

{tactic}`mvcgen` 框架被设计为可扩展。
此前介绍的单子都没有以任何方式硬编码进 {tactic}`mvcgen`。
相反，{tactic}`mvcgen` 依赖 {name}`WP`、{name}`WPMonad` 类型类实例及用户提供的规约，生成{tech (key := "mvcgen verification conditions") (remote := "reference")}[验证条件]。

:::leanSection
```lean -show
variable {m : Type u → Type v} [Monad m] {ps : PostShape.{u}}
```

{name}`WP` 实例定义单子 {lean}`m` 到谓词变换器 {lean}`PredTrans ps` 的最弱前置条件解释，
对应的 {name}`WPMonad` 实例则断言此转换对 {name}`Monad` 运算保持分配关系。
:::

:::::paragraph
::::leanFirst
假设希望用 `mvcgen` 为 [`Aeneas`](https://github.com/AeneasVerif/aeneas) 生成的程序生成验证条件。
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
使 {tactic}`mvcgen` 支持该单子需要：

1. 为 {name}`Result` 添加 {name}`WP` 与 {name}`WPMonad` 实例。
2. 为加法等基本 Rust 原语的转换结果注册规约引理。
:::

:::::paragraph
::::leanSection

```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α σ ε : Type u}  {prog : m α} {Q' : α → Assertion ps}
```
{name}`Result` 的 {name}`WP` 实例指定后置条件形状为 {lean (type := "PostShape.{0}")}`.except Error .pure`，因为没有类似状态的效应，但存在唯一一种 {lean}`Error` 类型的异常。
{name}`WP` 实例将 {lean}`Result α` 中的程序转换为 {lean}`PredTrans ps α` 中的谓词变换器。
也就是 {lean}`PostCond α ps → Assertion ps` 类型的函数，将后置条件映射到最弱前置条件。
{name}`WP.wp` 的实现类似于 {lean}`Except Error` 的实现。
{name}`Result` 的每种情形都由现有谓词变换器实现：
* {lean}`Result.ok` 使用 {name}`PredTrans.pure`；
* {lean}`Result.fail` 使用 {name}`PredTrans.throw`；
* {lean}`Result.div` 使用 {lean}`PredTrans.const ⌜False⌝`，意味着所有规约都断言程序不会发散。
::::
```lean
instance : WP Result (.except Error .pure) where
  wp
    | .ok v => PredTrans.pure v
    | .fail e => PredTrans.throw e
    | .div => PredTrans.const ⌜False⌝
```
:::::

:::paragraph
{name}`WP.wp` 的实现应对基本单子运算保持分配关系。
分别为 {name}`pure` 和 {name}`bind` 证明此性质。
对于 {name}`bind`，需要展开 {name}`wp` 与 {name}`bind` 的定义，
暴露嵌套的 {keyword}`match` 结构，{tactic}`grind` 就能轻松解决。
当谓词变换器应用于后置条件时，就会触发针对它的
{tactic}`simp` 与 {tactic}`grind` 理论。
使用 {tactic}`ext` 可将 {name}`WPMonad.wp_pure` 与 {name}`WPMonad.wp_bind` 的目标变为这种形式。
```lean
theorem Result.apply_wp_pure {α} {a : α} {Q} :
  wp⟦pure (f := Result) a⟧ Q = Q.1 a := by rfl

theorem Result.apply_wp_bind {α β} {x} {f : α → Result β} {Q} :
  wp⟦do let a ← x; f a⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by
  simp only [wp, bind]
  grind

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure _ := by ext Q : 1; apply Result.apply_wp_pure
  wp_bind x f := by ext Q : 1; apply Result.apply_wp_bind
```
:::

::: paragraph
最后，为 {lean}`Result` 证明一个类似 {name}`Except.of_wp_eq` 的充分性引理。
```lean
theorem Result.of_wp_eq {α} {x prog : Result α}
    (h : prog = x) (P : Result α → Prop)
    (hspec : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝,
                              fun e => ⌜P (.fail e)⌝⟩) :
      P x := by
  subst h
  match prog with
  | .ok a   => simpa [wp] using hspec
  | .fail e => simpa [wp] using hspec
  | .div    => simp [wp] at hspec
```
:::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α σ ε : Type u}  {prog : m α} {Q' : α → Assertion ps}
```

{name}`WP` 实例的定义决定能够通过 {lean}`Result.of_wp_eq` 从已证明规约中推导哪些性质。
该引理定义“最弱前置条件”的含义。
:::

:::paragraph
作为第二部分的示例，以下定义 {name}`Result` 中的 {name}`UInt32` 加法，建模整数溢出：

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
theorem Result.throw_spec {α Q} (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_ok_spec {x y} (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄
    addOp x y
    ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] with (simp_all; try grind)
```
:::

:::paragraph
这些就已足以证明以下示例：

```lean
example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  invariants
  · ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  with (simp_all [UInt32.size]; try grind)
```
:::

# 有状态目标的证明模式
%%%
slug := "Proof-Mode-for-Stateful-Goals"
tag := "Verifying-Imperative-Programs-Using--mvcgen--Proof-Mode-for-Stateful-Goals"
summary := inlines!""
exampleStyle := .inlineLean `MVCGenTutorial
%%%

```lean -show
variable {σs : List (Type u)} {H T : SPred σs}
```

{tactic}`mvcgen` 的首要目标之一，是将单子程序分解为易于理解的{tech (key := "mvcgen verification conditions") (remote := "reference")}[验证条件]。
例如，单子为单态且所有循环不变式已实例化时，调用 {multiCode}[{tactic}`all_goals`{lit}` `{tactic}`mleave`] 应能简化掉所有 {name}`Std.Do.SPred` 专用构造，留下人类与 {tactic}`grind` 容易理解的目标。
循环不变式实例化后，{tactic}`mvcgen` 会自动执行这个 {multiCode}[{tactic}`all_goals`{lit}` `{tactic}`mleave`] 步骤。

然而，有时 {tactic}`mleave` 无法去除全部 {name}`Std.Do.SPred` 构造。
这时会留下形如 {lean}`H ⊢ₛ T` 的验证条件。
断言语言 {name}`Assertion` 按以下方式转换为 {name}`Std.Do.SPred`：

```lean -keep
abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)
```


:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α σ ε : Type u}  {prog : m α} {Q' : α → Assertion ps}
```

留下形如 {lean}`H ⊢ₛ T` 的验证条件的一种常见情况，是底层单子 {lean}`m` 为多态。
此时，证明依赖控制到 {name}`Assertion` 语言转换的 {lean}`WP m ps` 实例，但与 `σs : List (Type u)` 的确切对应关系尚不明确。
为了成功解决这种验证条件，`mvcgen` 提供了受 Iris 并发分离逻辑启发的完整证明模式。
（事实上，该证明模式大部分改编自其 Lean 实现 [`iris-lean`](https://github.com/leanprover-community/iris-lean)。）
{ref "tactic-ref-spred" (remote := "reference")}[策略参考]列出全部证明模式策略。

:::
