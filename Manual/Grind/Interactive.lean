/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Upstream

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

#doc (Manual) "交互模式" =>
%%%
file := "Interactive-Mode"
tag := "grind-interactive"
%%%

由于 {tactic}`grind` 依赖当前的{ref "e-matching"}[已标注引理]集合，库中的标注变化后，证明可能失效或变慢。
此外，搜索证明时，{tactic}`grind` 可能尝试许多对最终结果没有贡献的步骤，这也需要时间。
可以用脚本替代 {tactic}`grind` 的搜索，直接沿着成功的证明路径前进，并且只实例化真正对证明有贡献的引理。
重新检查这样的证明既更快，也更能适应库的变化。
这一脚本功能称为 {tactic}`grind` 的{deftech (key := "interactive mode")}_交互模式_，脚本使用专用策略语言编写。

{tactic}`grind` 交互模式脚本由 {keywordOf Lean.Parser.Tactic.grind}`grind =>` 及其后缩进的 {tactic}`grind` 策略块组成。
每个策略会运行 {tactic}`grind` 的某个引擎、实例化定理、拆分情形、检查共享状态或管理剩余目标。
这些步骤操作自动搜索所使用的同一块“白板”：此前各步骤发现的等式、不等式、布尔事实及由它们导出的等价类。

交互模式也能帮助理解 {tactic}`grind` 为何无法完成证明。
{ref "grind-interactive-inspect"}[检查策略]揭示白板的当前状态，可能让用户发现缺失的定理实例化或情形拆分；这些可以通过若干显式步骤或库中的额外标注补足。
显式脚本也可以帮助读者理解 {tactic}`grind` 成功的_原因_。

:::example "阅读 `grind?` 证明"

结构体 {lean}`Two` 可视为用 {name}`Bool` 而非 {name}`Nat` 索引的双元素数组。
```lean
structure Two α where
  fst : α
  snd : α

namespace Two

def get (xs : Two α) (i : Bool) : α :=
  if i then xs.fst else xs.snd
```

{name}`Two` 的 API 包含若干标注为供 {tactic}`grind` 使用的引理：
```lean
def both (x : α) : Two α := ⟨x, x⟩

def map (f : α → β) (xs : Two α) : Two β := ⟨f xs.fst, f xs.snd⟩

@[ext, grind ext]
theorem ext_get {xs ys : Two α}
    (h : ∀ i, xs.get i = ys.get i) : xs = ys := by
  cases xs; cases ys
  simp_all [get]

@[grind =]
theorem get_def {xs : Two α} {i} :
    xs.get i = if i then xs.fst else xs.snd := rfl

@[grind =]
theorem map_fst {f : α → β} {xs} :
    (map f xs).fst = f xs.fst := rfl

@[grind =]
theorem map_snd {f : α → β} {xs} :
    (map f xs).snd = f xs.snd := rfl

@[grind =]
theorem both_fst {x : α} : (both x).fst = x := rfl

@[grind =]
theorem both_snd {x : α} : (both x).snd = x := rfl

@[grind =]
theorem both_fst_eq_snd {x : α} :
    (both x).fst = (both x).snd := rfl
```

借助这些引理，{tactic}`grind` 可以证明 {name}`Two.map` 对 {name}`Two.both` 满足分配律。
调用 {tactic}`grind?` 会得到多个更具体的 {tactic}`grind` 调用建议，其中之一就是交互脚本：
```lean (name := mapBoth)
theorem map_both {x : α} {f : α → β} :
    (both x).map f = both (f x) := by
  grind?
```
```leanOutput mapBoth
Try these:
  [apply] grind only [= get_def, = both_fst, = map_fst, = both_snd, = map_snd, #1362, #ba8b]
  [apply] grind only [= get_def, = both_fst, = map_fst, = both_snd, = map_snd]
  [apply] grind =>
    cases #1362
    instantiate only [= get_def]
    cases #ba8b
    · instantiate only [= both_fst, = map_fst]
      instantiate only [= both_fst]
    · instantiate only [= both_snd, = map_snd]
      instantiate only [= both_snd]
```

该脚本显式展示了证明内部的两次{ref "grind-interactive-cases"}[情形拆分]。

搜索期间，{tactic}`grind` 还实例化了 {name}`Two.both_fst_eq_snd`，尽管该等式对证明没有贡献。
由于它最终未对结果作出贡献，所有建议的 {tactic}`grind` 调用都不会提及它；重新检查这些建议版本时，就避免了无用实例化的开销。
设置 {option}`diagnostics` 选项可以报告各个定理被实例化的次数：
```lean (name := mapBothDiag)
set_option diagnostics true in
set_option diagnostics.threshold 1 in
example {x : α} {f : α → β} : (both x).map f = both (f x) := by
  grind
```
```leanOutput mapBothDiag (expandTrace := grind) (expandTrace := thm) (expandTrace := ematch)
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] both_snd ↦ 3
      [thm] both_fst ↦ 2
      [thm] both_fst_eq_snd ↦ 2
      [thm] get_def ↦ 2
      [thm] map_fst ↦ 1
      [thm] map_snd ↦ 1
  [split] Case splits
  [app] Applications
  [grind] Simplifier
    [simp] tried theorems (max: 15, num: 1):
    [simp] tried congruence theorems (max: 2, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```

建议的交互模式 {tactic}`grind` 不会实例化 {name}`Two.both_fst_eq_snd`：
```lean (name := mapBothDiag2)
set_option diagnostics true in
set_option diagnostics.threshold 1 in
example {x : α} {f : α → β} : (both x).map f = both (f x) := by
  grind =>
    cases #1362
    instantiate only [= get_def]
    cases #ba8b
    · instantiate only [= both_fst, = map_fst]
      instantiate only [= both_fst]
    · instantiate only [= both_snd, = map_snd]
      instantiate only [= both_snd]
```
```leanOutput mapBothDiag2 (expandTrace := grind) (expandTrace := thm) (expandTrace := ematch)
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] both_fst ↦ 2
      [thm] both_snd ↦ 2
      [thm] get_def ↦ 2
      [thm] map_fst ↦ 1
      [thm] map_snd ↦ 1
  [split] Case splits
  [app] Applications
  [grind] Simplifier
    [simp] tried theorems (max: 13, num: 1):
    [simp] tried congruence theorems (max: 2, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```
:::

# 入口
%%%
file := "Entry-Points"
tag := "grind-interactive-entry"
%%%

{tactic}`grind` 的交互模式有两个版本。
第一个用 {keywordOf Lean.Parser.Tactic.grind}`grind =>` 引入，旨在控制 {tactic}`grind`，会自动执行大多数证明所需的某些步骤。
另一个用 {tactic}`sym` 引入，允许更细致的手动控制，面向符号模拟工作流。

使用脚本时，{tactic}`grind` 会先引入所有假设，再使用反证法初始化证明，因此初始目标总是 {name}`False`。
随后运行脚本。

:::syntax tactic (title := "交互式 `grind`")
```grammar
grind $_:optConfig $[only]? $[ [ $[$p],* ] ]? => $steps
```
:::

与 {tactic}`grind` 不同，{tactic}`sym` 不会先引入假设或使用反证法。
脚本作者可以完全控制上下文与目标。

:::syntax tactic (title := "符号模拟")
```grammar
sym $_:optConfig $[only]? $[ [ $[$p],* ] ]? => $steps
```
:::

两个策略接受相同的配置选项、{keywordOf Lean.Parser.Tactic.grind}`only` 修饰符，以及普通 {tactic}`grind` 接受的方括号中的定理和参数列表。
某些功能由 {tactic}`grind` 自动调用，在 {tactic}`sym` 中则需手动调用；它们具有专用策略，在{ref "grind-sym"}[符号模拟模式一节]介绍。

{tactic}`grind?` 接受与 {tactic}`grind` 相同的实参，但不支持进入交互模式。
它会{ref "grind-minimizing"}[建议]等价的 {keywordOf Lean.Parser.Tactic.grind}`grind only` 调用和等价脚本。
在交互式 {tactic}`grind` 脚本内，{grindTactic}`finish?` 和 {grindTactic}`cases?` 同样会建议脚本。

# `grind` 策略语言
%%%
file := "The--grind--Tactic-Language"
tag := "grind-interactive-steps"
%%%

{keywordOf Lean.Parser.Tactic.grind}`grind =>` 后的步骤序列写在缩进块中，每行一步；多个步骤也可以用 `;` 分隔。
也可以使用花括号包围步骤序列，以代替缩进。
这种序列由语法类别 {name Lean.Parser.Tactic.Grind.grindSeq}`grindSeq` 表示。

与普通 Lean 策略脚本一样，{tactic}`grind` 策略操作由一系列{tech (key := "goals")}[目标]组成的{tech (key := "proof state")}[证明状态]；每个目标又由一系列假设和一个结论组成。
没有剩余目标时，证明就完成了。
多数策略操作{tech (key := "main goal")}[主目标]，而{ref "grind-interactive-goals"}[目标管理策略]会像普通策略中的对应策略一样，在步骤之间重新分配目标。
此外，{tactic}`grind` 策略可以访问“白板”。

## 锚点
%%%
file := "Anchors"
tag := "Lean-__________________--grind--______--Interactive-Mode--The--grind--Tactic-Language--Anchors"
%%%

若干策略通过{deftech (key := "anchor")}_锚点_引用白板条目，写作 `#` 后接十六进制数，例如 `#1a`。
锚点代替名称，用于标识特定事实、等价类或情形拆分候选项。
锚点会出现在检查策略的输出或筛选后的状态中。
{grindTactic}`cases?` 和 {grindTactic}`show_cases` 会报告 {grindTactic}`cases` 可操作的锚点。

锚点是所引用项的稳定哈希。
它根据项的结构计算，并刻意忽略内部名称和实例实参等不稳定的实现细节。
因此，许多无关的证明变化不会影响锚点；但被引用项的结构改变时，锚点仍可能变化。
所以，只要引用候选项的结构保持不变，就可以将 {grindTactic}`cases?` 产生的锚点保存在脚本文件中。

```lean (name := anchorCanary) -show
-- Regression test: the anchor of `p ∨ q` is a stable hash; this pins its value so that any change
-- to the anchoring scheme is caught by the build.
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  sym =>
    internalize_all
    show_cases
    cases_next
    all_goals finish
```
```leanOutput anchorCanary -show
[splits] Case split candidates
  [split] #4283 := p ∨ q
```

某些情况下，多个项可能具有同一锚点。
用锚点实例化时，会实例化共享该锚点的所有项；情形拆分则需要更精确的控制。
若多个情形拆分候选项共享锚点，则会为其分配{deftech (key := "ordinal disambiguators")}_序号消歧标记_：用连续数字记录它们加入白板的顺序。
这些数字写在 `/` 后，例如 `#7a83/2` 表示锚点为 `#7a83` 的第二个项。
具有给定锚点的首个项编号为 `1`，因此 `#7a83/1` 等价于 `#7a83`。
由于按顺序分配，序号不如锚点稳定；调整假设顺序就可能改变序号。

:::example "序号消歧标记"
该定理陈述：若存在两个值，函数将它们分别映射到 `0` 或 `1`，且两个函数值之和为 `2`，则存在一点被函数映射到 `1`。
两个析取都映射到同一底层锚点 `#4f8c`。
用 {tactic}`obtain` 将它们暴露后，{grindTactic}`cases?` 显示两个选项，各自带有序号消歧标记：
```lean +error (name := ordinals)
example (f : Nat → Nat)
    (h : ∃ a b,
      (f a = 0 ∨ f a = 1) ∧
      (f b = 0 ∨ f b = 1) ∧
      f a + f b = 2) :
    ∃ a, f a = 1 := by
  obtain ⟨_, _, ha, hb, hab⟩ := h
  grind =>
    cases?
```
```leanOutput ordinals
Try these:
  [apply] cases #4f8c for
    f w✝ = 0 ∨ f w✝ = 1
  [apply] cases #4f8c/2 for
    f w✝¹ = 0 ∨ f w✝¹ = 1
```
:::


## 筛选器
%%%
file := "Filters"
tag := "Lean-__________________--grind--______--Interactive-Mode--The--grind--Tactic-Language--Filters"
%%%

任何 {tactic}`grind` 策略后都可接 `|` 和{deftech (key := "filter")}_筛选器_，从 {tactic}`grind` 状态中选择部分数据。
筛选后的状态会在该步骤运行前后显示，方便观察步骤如何改变白板。
若 `|` 后的筛选器为空，则整个状态均匹配。

:::syntax grind_filter (title := "生成层级筛选器") (label := "grind 筛选器")
```grammar
gen < $n
```
```grammar
gen ≤ $n
```
```grammar
gen <= $n
```
```grammar
gen = $n
```
```grammar
gen != $n
```
```grammar
gen ≥ $n
```
```grammar
gen >= $n
```
```grammar
gen > $n
```
当条目的{tech (key := "generation")}[生成层级]与给定数字满足所示比较关系时，这些筛选器就会匹配。
  较低的生成层级对应搜索中较早发现的事实。
:::

:::syntax grind_filter (title := "名称筛选器") (label := "grind 筛选器")
```grammar
$x:ident
```
当标识符是局部假设或全局常量的名称，并且出现在该项中时，此筛选器匹配。
:::

:::syntax grind_filter (title := "筛选表达式") (label := "grind 筛选器")
```grammar
($f)
```
```grammar
$f && $f
```
```grammar
$f || $f
```
```grammar
!$f
```
筛选器可以用圆括号分组、取反，以及用合取和析取组合。
合取与析取都是左结合且优先级相同，因此应显式使用圆括号分组。
:::

:::example "筛选器"
```lean
inductive Color where | red | green
inductive Fruit where | cherry | lime

example (peel pulp : Fruit → Color)
    (h1 : peel .cherry = pulp .cherry)
    (h2 : ∀ f, pulp f = .red) :
    peel .cherry = .red := by
  grind =>
    instantiate | pulp
```

步骤后接 `|` 和{tech (key := "filter")}[筛选器]，会在编辑器中显示步骤运行前后与筛选器匹配的 {tactic}`grind` 状态部分。
筛选器 `| pulp` 只保留提及 `pulp` 的条目。
在这一轮前，它们是 `h2` 以及来自 `h1` 的等价类 `{peel .cherry, pulp .cherry}`：
```
[grind] Grind state
  [facts] Asserted facts
  [props] True propositions
    [_] ∀ (f : Fruit), pulp f = Color.red
  [eqc] Equivalence classes
    [eqc] {peel Fruit.cherry, pulp Fruit.cherry}
```

假命题 `peel .cherry = .red` 未提及 `pulp`，因此被省略。
在 `.cherry` 处实例化 `h2` 会断言 `pulp .cherry = .red` 并关闭目标，因此步骤之后显示 `no grind state`。
:::



# 目标管理与步骤串联
%%%
file := "Goal-Management-and-Sequencing"
tag := "grind-interactive-goals"
%%%

这些策略不调用求解器，也不修改 {tactic}`grind` 状态。
它们对应主策略语言中的{ref "tactic-language-control"}[控制结构与策略]。

:::zhgrindTactic "skip"
:::

:::zhgrindTactic "done"
:::

可以用圆括号将序列分组，写作 `( steps )`；它会在当前目标上运行括号内的步骤，没有其他额外效果。
这种分组用于限定 {grindTactic}`first` 或 {grindTactic}`repeat` 等控制结构的作用范围。

:::zhgrindTactic "case"
:::

:::zhgrindTactic "focus"
:::

:::zhgrindTactic "next" (show := "next =>")
:::

:::zhgrindTactic "." (show := "·")
:::

圆点记号是 {grindTactic}`next` 的简写。
它聚焦于主目标，并暂时隐藏其他目标。
若内部策略脚本未能成功证明所聚焦的目标，则会报错。

:::zhgrindTactic "all_goals"
:::

:::zhgrindTactic "any_goals"
:::

:::zhgrindTactic "first"
:::

:::zhgrindTactic "try"
:::

:::zhgrindTactic "repeat"
:::

:::zhgrindTactic "fail_if_success"
:::

:::zhgrindTactic "fail"
:::

:::zhgrindTactic "<;>"

若策略在任何{tech (key := "subgoals")}[子目标]上失败，则整个 {grindTactic}`<;>` 策略失败。
:::


# 完成证明
%%%
file := "Completing-Proofs"
tag := "grind-interactive-finish"
%%%

这些策略通过将控制权交回 {tactic}`grind` 的自动搜索，或转入普通 Lean 策略语言来关闭目标。
目标也可以通过{ref "grind-interactive-solvers"}[理论求解器]关闭。

:::zhgrindTactic "finish"
:::

:::zhgrindTactic "finish?"
:::

{grindTactic}`finish?` 关闭目标时，会提供代码操作，将该调用替换为发现的脚本，正如 {tactic}`grind?` 会建议 {keywordOf Lean.Parser.Tactic.grind}`grind only` 调用。
由此可以交互地使用 {tactic}`grind` 发现部分证明，再在需要时手动修改。

:::example "将 `grind` 证明记录为交互脚本"
```lean -show
variable (pred : Nat → Prop)
```
{lean}`WithSucc` 对后继运算封闭：
```lean
@[grind]
inductive WithSucc (pred : Nat → Prop): Nat → Prop where
  | base : pred n → WithSucc pred n
  | step : WithSucc pred n → WithSucc pred (n + 1)
```

{tactic}`grind` 将 {name}`WithSucc.step` 实例化两次，从 {lean}`WithSucc pred 0` 的证明得到 {lean}`WithSucc pred 2`：
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind
```

改为在目标后接 {keyword}`=> finish?`，会关闭目标并报告可重现该证明的脚本：
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind => finish?
```

应用建议脚本后，每次实例化都变得显式：
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind =>
    instantiate only [→ WithSucc.step]
    instantiate only [→ WithSucc.step]
```
:::

:::zhgrindTactic "sorry"
:::

:::zhgrindTactic "admit"
:::

:::zhgrindTactic "tactic" (show := "tactic =>")
:::

:::zhgrindTactic "exact"
:::

# 理论求解器
%%%
file := "Theory-Solvers"
tag := "grind-interactive-solvers"
%%%

以下每个策略都会在当前状态上运行 {tactic}`grind` 的一种判定过程。

:::zhgrindTactic "lia"
:::

:::zhgrindTactic "linarith"
:::

:::zhgrindTactic "ring"
:::

:::zhgrindTactic "ac"
:::

# 定理实例化
%%%
file := "Theorem-Instantiation"
tag := "grind-interactive-instantiate"
%%%

这些策略通过实例化定理向 {tactic}`grind` 状态（即“白板”）添加新事实。

:::zhgrindTactic "instantiate"
:::

{grindTactic}`instantiate` 运行一轮 E-匹配。
默认使用 {tactic}`grind` 当前所有活跃定理；方括号列表提供同时实例化的额外定理，{tech (key := "anchor")}[锚点]则添加状态中的特定局部定理。
运行 {grindTactic}`show_local_thms` 可显示局部定理的锚点。
方括号列表还可通过 {keyword}`namespace` 关键字指定命名空间，从而使用该命名空间中具有局部作用域 {attr}`grind` 属性的定理。
{keywordOf Lean.Parser.Tactic.Grind.instantiate}`only` 修饰符将该轮限制为所列定理。

{keywordOf Lean.Parser.Tactic.Grind.instantiate}`approx` 修饰符不影响步骤的运行方式。
它是出现在 {tactic}`grind?`、{grindTactic}`finish?` 等自动生成脚本中的标记，表示 {tactic}`grind` 无法为该步骤确定精确的定理列表。
它说明列出的定理仅是近似，可能需要手动调整。

:::example "实例化局部假设"
全称量化陈述形式的假设会成为 {tactic}`grind` 状态中的局部定理。
由于此假设没有全局名称，需要使用 {grindTactic}`show_local_thms` 报告的{tech (key := "anchor")}[锚点]来实例化：
```lean (name := instAnchor)
example (f : Nat → Nat) (h : ∀ n, f n ≤ n * n) :
    f 3 ≤ 9 := by
  grind =>
    show_local_thms
    instantiate [#7468]
```
```leanOutput instAnchor
[thms] Local theorems
  [thm] #7468 := ∀ (n : Nat), f n ≤ n * n
```

```lean -show
variable (f : Nat → Nat) (h : ∀ n, f n ≤ n * n)
```
在 {lean}`3` 处实例化 {lean}`h`，会向状态添加事实 {lean}`f 3 ≤ 3 * 3`，{tactic}`grind` 据此得到 {lean}`f 3 ≤ 9`。
:::

:::zhgrindTactic "use"
:::

:::example "命名空间"
谓词 {name}`IsEmpty` 以迂回的方式陈述列表为空。
在命名空间 `A` 内，{tactic}`grind` 使用定理 {name}`A.nil_IsEmpty` 证明 {lean}`IsEmpty []`。
```lean
def IsEmpty (xs : List α) : Prop := xs.length = 0

namespace A
@[scoped grind .]
theorem nil_IsEmpty : IsEmpty ([] : List α) := rfl

example : IsEmpty ([] : List String) := by grind
end A
```

在命名空间外，该定理不会被使用：
```lean +error (name := nogrind)
example : IsEmpty ([] : List String) := by grind
```
```leanOutput nogrind
`grind` failed
case grind
h : ¬IsEmpty []
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
```

在 {grindTactic}`instantiate` 中指定命名空间 `A`，就会重新启用 {name}`A.nil_IsEmpty`：
```lean
example : IsEmpty ([] : List String) := by
  grind =>
    instantiate [namespace A]
```

:::

:::zhgrindTactic "mbtc"
:::

# 情形分析
%%%
file := "Case-Analysis"
tag := "grind-interactive-cases"
%%%

这些策略调用 {tactic}`grind` 的{ref "grind-split"}[情形拆分]。

:::zhgrindTactic "cases"
:::

:::zhgrindTactic "cases?"
:::

:::zhgrindTactic "cases_next"
:::

# 状态检查
%%%
file := "State-Inspection"
tag := "grind-interactive-inspect"
%%%

本节许多策略接受可选的{tech (key := "filter")}[筛选器]参数。
提供筛选器时_不要_带 `|` 字符，否则会调用通用状态显示机制，而非定制该策略的显示。

:::example "检查白板"
{grindTactic}`show_state` 打印断言的事实、真假命题，以及目前发现的等价类：
```lean (name := showState)
inductive Color where | red | green
inductive Fruit where | cherry | lime

example (peel pulp : Fruit → Color)
    (h1 : peel .cherry = pulp .cherry)
    (h2 : ∀ f, pulp f = .red) :
    peel .cherry = .red := by
  grind =>
    show_state
    finish
```
```leanOutput showState
[grind] Grind state
  [facts] Asserted facts
  [props] True propositions
    [_] ∀ (f : Fruit), pulp f = Color.red
  [props] False propositions
    [_] peel Fruit.cherry = Color.red
  [eqc] Equivalence classes
    [eqc] {peel Fruit.cherry, pulp Fruit.cherry}
```

等价类 `{peel .cherry, pulp .cherry}` 来自 `h1`。
全称量化陈述 `h2` 尚未实例化，因此必须由 {grindTactic}`finish` 将控制权交回 {tactic}`grind` 的搜索才能完成证明。
配套策略 {grindTactic}`show_asserted`、{grindTactic}`show_true`、{grindTactic}`show_false` 和 {grindTactic}`show_eqcs` 分别显示该状态的各个部分。
:::

:::zhgrindTactic "show_state"
:::

:::zhgrindTactic "show_asserted"
:::

:::zhgrindTactic "show_true"
:::

:::zhgrindTactic "show_false"
:::

:::zhgrindTactic "show_eqcs"
:::

:::zhgrindTactic "show_cases"
:::

:::zhgrindTactic "show_local_thms"
:::

:::zhgrindTactic "show_goals"
:::

:::zhgrindTactic "show_term"
:::

# 局部上下文与命名
%%%
file := "Local-Context-and-Naming"
tag := "grind-interactive-context"
%%%

这些策略向局部上下文添加假设，并使后续步骤能使用原本不可访问的名称。

:::zhgrindTactic Grind.«have» (show := "have")
:::

{keywordOf Lean.Parser.Tactic.Grind.haveSilent}`have` 的另一种形式写作不带值的 `have h : t`：它使用默认搜索策略从当前 {tactic}`grind` 状态证明 `t`，然后将其添加为假设。

:::zhgrindTactic haveSilent (show := "have")
:::

:::zhgrindTactic "rename_i"
:::

:::zhgrindTactic "expose_names"
:::

# 配置
%%%
file := "Configuration"
tag := "grind-interactive-config"
%%%

这些策略在修改选项或配置后运行一系列 {tactic}`grind` 策略。

:::zhgrindTactic "set_option"
:::

:::zhgrindTactic "set_config"
:::

# 符号模拟模式
%%%
file := "Symbolic-Simulation-Mode"
tag := "grind-sym"
%%%

{tactic}`sym` 是 {keywordOf Lean.Parser.Tactic.grind}`grind =>` 的更底层版本，允许更精细地手动控制状态。
运行 {tactic}`sym` 会进入交互模式，但不会像 {tactic}`grind` 那样立即引入假设并使用反证法。

使用 {tactic}`sym` 时，必须像标准证明策略语言那样手动引入假设。
引入假设会将其从目标结论移到新的假设中。
通常还需要将假设加入“白板”，让它参与同余闭包及 {tactic}`grind` 的其他处理过程。
将假设或项加入白板称为{deftech (key := "internalization")}_内部化_。
内部化之后，假设参与同余推理、{tech (key := "constraint propagation")}[约束传播]和理论求解器；在此之前，{tactic}`grind` 不会对其进行推理。

以下策略仅在 {tactic}`sym` 之后可用；普通的交互式 {tactic}`grind` 中不可用，因为后者会在需要时自动执行相应操作。

:::zhgrindTactic symIntro (show := "intro")
:::

::::example "引入与内部化"
引入假设会改变目标，并默认将假设加入白板：

:::grindTacticExample +sym
{grindGoal}`∀ (a b : Nat), a = b → b = a`
```grindPrefix
intro a b
```

当前目标为蕴涵且 {tactic}`grind` 状态为空时，运行 {grindTactic Lean.Parser.Tactic.Grind.symIntro}`intro`，既会将前件加入假设，又会将其并入白板。
若初始目标和 grind 状态如下：
```grindProofState
case grind
a b : Nat
⊢ a = b → b = a
```
```grindState
[grind] Grind state
```
那么运行
```grindStep
intro h
```
会得到新假设：
```grindProofState
case grind
a b : Nat
h : a = b
⊢ b = a
```
该新假设同时修改了 {tactic}`grind` 状态，现在为：
```grindState
[grind] Grind state
  [facts] Asserted facts
    [_] a = b
  [eqc] Equivalence classes
    [eqc] {a, b}
```
:::
:::grindTacticExample +sym
{grindGoal}`∀ (a b : Nat), a = b → b = a`
```grindPrefix
intro a b
```

对于相同目标和空状态：
```grindProofState
case grind
a b : Nat
⊢ a = b → b = a
```
```grindState
[grind] Grind state
```
引入假设而不内部化：
```grindStep
intro (internalize := false) h
```
会改变目标，但状态仍为空：
```grindProofState
case grind
a b : Nat
h : a = b
⊢ b = a
```
```grindState
[grind] Grind state
```
:::

::::

简写 `intro~` 引入绑定而不内部化，等价于 `intro (internalize := false)`。

:::zhgrindTactic symIntros (show := "intros")
:::

简写 `intros~` 引入所有剩余绑定而不内部化。

:::zhgrindTactic "apply"
:::

:::zhgrindTactic "internalize"
:::

:::zhgrindTactic "internalize_all"
:::

:::zhgrindTactic "by_contra"
:::

:::zhgrindTactic "rw"
:::

:::zhgrindTactic "cbv"
:::

{tactic}`sym` 脚本中的 {grindTactic}`simp` 和 {grindTactic}`dsimp` 使用 {tactic}`grind` 自身的简化器；它是针对内部项表示专门构建的独立实现，具有自己的性能特征与功能集。
该简化器直接操作此表示，避免测试定义相等性。
它不使用{tech (key := "simp sets")}[简化集]，而使用{deftech (key := "named variants")}_具名变体_：带名称的 simproc 组合（分别在简化前后运行）及配置覆盖。
具名变体将在{ref "grind-sym-simp-variants"}[下一节]详细介绍。

:::zhgrindTactic "simp"
:::

:::zhgrindTactic "dsimp"
:::

位向量判定过程也可以使用。
它们在 {tactic}`grind` 与 {tactic}`sym` 脚本中均可用，并作用于目标。
在 {tactic}`grind` 或 {tactic}`sym` 脚本中，若 {grindTactic}`bv_normalize` 未关闭目标，则会失败。

:::zhgrindTactic "bv_decide"
:::

:::zhgrindTactic "bv_decide?"
:::

:::zhgrindTactic "bv_normalize"
:::

:::zhgrindTactic "bv_check"
:::

## 注册简化变体
%%%
file := "Registering-Simplification-Variants"
tag := "grind-sym-simp-variants"
%%%

{tactic}`sym` 版本的 {grindTactic}`simp` 与 {grindTactic}`dsimp` 使用的具名变体，通过 {keywordOf Lean.Parser.Command.registerSymSimp}`register_sym_simp` 和 {keywordOf Lean.Parser.Command.registerSymDSimp}`register_sym_dsimp` 命令声明。
注册后，在 {grindTactic}`simp` 或 {grindTactic}`dsimp` 后接变体名称即可选择它。

:::syntax command (title := "注册 `Sym.simp` 变体")
```grammar
register_sym_simp $name:ident where
  $fields*
```

{zhincludeDocstringFrom Lean.Parser.Command.registerSymSimp}
:::

:::syntax command (title := "注册 `Sym.dsimp` 变体")
```grammar
register_sym_dsimp $name:ident where
  $fields*
```

{zhincludeDocstringFrom Lean.Parser.Command.registerSymDSimp}
:::

`where` 块中的字段均为可选：

: `pre` 和 `post`

  分别在简化前后应用的 simproc 链。

: `maxSteps`

  限制简化步数。

: `maxDischargeDepth`

  限制递归证明旁目标的深度。
  仅适用于 {keywordOf Lean.Parser.Command.registerSymSimp}`register_sym_simp`。
