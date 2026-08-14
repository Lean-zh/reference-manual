/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.RecursiveDefs

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "理论与构造" =>
%%%
tag := "coinductive-theory"
%%%

余归纳与归纳谓词的构造建立在完备格上的 Knaster–Tarski 不动点定理之上。
{ref "partial-fixpoint-theory"}[偏不动点递归]依赖链完备偏序（{name}`Lean.Order.CCPO`），而余归纳与归纳谓词使用更强的{deftech (key := "complete lattice")}_完备格_概念。

关键思想是，{lean}`Prop` 带有一个按蕴涵排序的{ref "complete-lattices"}[完备格]结构（当 `P → Q` 时 `P ⊑ Q`）；根据 Knaster–Tarski 定理，完备格上的任意单调自映射同时具有最小与最大不动点。
余归纳谓词使用{ref "lattice-prop"}[反向蕴涵序]（当 `Q → P` 时 `P ⊑ Q`），因此该反向序中的最小不动点就是标准序中的最大不动点。
对于形如 `α → Prop` 的谓词，将此格结构逐点提升到函数类型即可提供所需环境。
对于互递归块，完备格的积仍是完备格。
该构造与{ref "partial-fixpoint"}[偏不动点]机制共享内部实现。


# 完备格
%%%
tag := "complete-lattices"
%%%

{tech (key := "complete lattice")}[完备格]是一种偏序，其中每个子集（而不仅是每条链）都有最小上界。

{zhdocstring Lean.Order.CompleteLattice ZhDoc.RecursiveDefs.Order.CompleteLattice}

每个完备格都会给出一个链完备偏序，因为每条链尤其也是一个子集；但反过来一般并不成立。
例如，居留类型上的平坦序（{ref "partial-fixpoint"}[偏不动点]用于尾递归函数）是链完备偏序，却不是完备格。

根据 Knaster–Tarski 定理，在完备格中，单调函数的最小不动点可以直接构造为所有前不动点的下确界：

{zhdocstring Lean.Order.lfp ZhDoc.RecursiveDefs.Order.lfp}

{zhdocstring Lean.Order.lfp_fix ZhDoc.RecursiveDefs.Order.lfp_fix}

对应的归纳原理是 Park 归纳：要证明某个性质对最小不动点的所有元素成立，只需证明应用一次定义函数会保持该性质。

{zhdocstring Lean.Order.lfp_le_of_le_monotone ZhDoc.RecursiveDefs.Order.lfp_le_of_le_monotone}

# 命题上的格结构
%%%
tag := "lattice-prop"
%%%

类型 {lean}`Prop` 具有两种自然的完备格结构，分别产生不同种类的不动点：

:::paragraph

 * {name}`Lean.Order.ImplicationOrder` 按蕴涵对命题排序：`P ⊑ Q` 意味着 `P → Q`。
   该序中的最小不动点给出在定义规则下闭合的最小谓词，对应于{tech (key := "lattice-theoretic inductive predicate")}_归纳谓词_。
   这是 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 使用的序。

 * {name}`Lean.Order.ReverseImplicationOrder` 按反向蕴涵对命题排序：`P ⊑ Q` 意味着 `Q → P`。
   该_反向_序中的最小不动点是标准序中的_最大_不动点，由此得到与定义规则相容的最大谓词。
   这对应于{tech (key := "lattice-theoretic coinductive predicate")}_余归纳谓词_。
   这是 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 使用的序。

:::

以完备格为值域的箭头类型继承完备格结构，完备格的积也是完备格。
这些闭包性质使该构造能够扩展到任意元数的谓词和互递归块。

# 单调性
%%%
tag := "coinductive-monotonicity"
%%%

将谓词定义为不动点，要求定义方程相对于适当的序是单调的。
对于 {keywordOf Lean.Parser.Command.declaration}`coinductive` 命令，以及 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 和 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 终止子句，单调性要求都是语义上的，而非语法上的。
{tactic}`monotonicity` 策略通过组合以 {attr}`partial_fixpoint_monotone` 属性注册的引理来证明单调性。
这种方法比严格正性更宽松。
例如，通过在 {name}`Lean.Order.ImplicationOrder` 与 {name}`Lean.Order.ReverseImplicationOrder` 之间翻转序，可以正确处理否定和蕴涵。
这正是同一{tech (key := "mutual block")}[互递归块]中能够混合归纳与余归纳不动点的原因。

{tactic}`monotonicity` 策略所能处理的构造是可扩展的：注册额外的 {attr}`partial_fixpoint_monotone` 引理，可让该策略学会处理新的逻辑联结词或高阶函数。
或者，在使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 时，可以通过 {keyword}`monotonicity` 子句提供显式单调性证明项。

已注册单调性引理的完整列表以及单调性策略的更多细节，请参阅{ref "partial-fixpoint-theory"}[偏不动点的理论一节]。
