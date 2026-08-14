/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers

import Manual.Grind.ConstraintPropagation
import Manual.Grind.CongrClosure
import Manual.Grind.CaseAnalysis
import Manual.Grind.EMatching
import Manual.Grind.Cutsat
import Manual.Grind.Algebra
import Manual.Grind.Linarith
import Manual.Grind.Annotation
import Manual.Grind.ExtendedExamples

-- if-then-else 规范化示例需要此导入。
import Std.Data.TreeMap
import Std.Data.HashMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true

-- TODO (@kim-em)：尚未记录 `Lean.Grind.AddCommMonoid` 和 `Lean.Grind.AddCommGroup`。
set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

-- Verso 默认最大行长为 60，限制很严。
-- TODO：与 David 讨论。
set_option verso.code.warnLineLength 72

open Manual (comment)

#doc (Manual) "`grind` 策略" =>
%%%
tag := "grind-tactic"
%%%

:::tutorials
 * {ref "grind-index-map" (remote := "tutorials")}[使用 `grind` 处理有序映射]
:::

```lean -show
-- 为示例打开若干命名空间。
open Lean Lean.Grind Lean.Meta.Grind
```

{tactic}`grind` 策略使用受现代 SMT 求解器启发的技术自动构造证明。
它逐步收集事实集，并利用一组相互协作的技术从已有事实推导新事实，以此生成证明。
在幕后，所有证明都使用反证法，因此在操作上预期结论与前提并无区别；{tactic}`grind` 始终尝试导出矛盾。

想象一块虚拟白板。
每当 {tactic}`grind` 发现新的等式、不等式或布尔文字时，它都会把该事实写到白板上，将等价的项归入同一组，并让每个引擎从共享白板读取信息、再向其中添加信息。
特别地，由于所有真命题都等于 {lean}`True`，所有假命题都等于 {lean}`False`，{tactic}`grind` 在跟踪等价类的同时也跟踪一组已知事实。

:::paragraph
相互协作的引擎包括：

* {tech (key := "congruence closure")}[同余闭包]、
* {tech (key := "constraint propagation")}[约束传播]、
* {tech (key := "E‑matching")}[E‑匹配]、
* 引导式{ref "grind-split"}[情形分析]，以及
* 一组卫星理论求解器，包括{ref "cutsat"}[线性整数算术]和{ref "grind-ring"}[交换环]求解器。

与其他策略一样，{tactic}`grind` 会为它添加的每个事实生成普通的 Lean 证明项。
Lean 标准库已经带有 `@[grind]` 属性标注，因此常用引理会被自动发现。
:::

{tactic}`grind` *并非*为搜索空间发生组合爆炸的目标而设计，例如大 `n` 的鸽巢原理实例、图着色归约、高阶 N 皇后棋盘，或编码为布尔约束的 200 变量数独。
这类编码需要成千上万（甚至数百万）次情形拆分，会压垮 {tactic}`grind` 的分支搜索。
对于位级或纯布尔组合问题，请使用 {tactic}`bv_decide`。{tactic}`bv_decide` 策略会调用先进的 SAT 求解器（例如 CaDiCaL 或 Kissat），然后返回紧凑且可由机器检查的证书。
所有繁重搜索都在 Lean 外部进行；证书会在 Lean 内部重放并验证，因此仍然保持可信（验证时间随证书大小增长）。

:::TODO
待功能可用后纳入以下内容：
* 对于*需要跨多种理论进行大量情形分析的完整 SMT 问题*（数组、位向量、丰富的算术、量词等），请使用即将推出的 *`lean‑smt`* 策略——它是 CVC5 的紧密 Lean 前端，可在 Lean 内部重放不可满足核或模型。
:::


:::example "同余闭包" (open := true)

这个证明使用{tech (key := "congruence closure")}[同余闭包]立即成功；同余闭包会发现由相等项组成的集合。

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  grind
```

:::

:::example "代数推理" (open := true)

这个证明使用 {tactic}`grind` 的交换环求解器。

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```
:::

:::example "有限域推理" (open := true)
{name}`Fin` 上的算术运算会溢出：当结果超出界限时，会回绕到 {lean  (type := "Fin 11")}`0`。
{tactic}`grind` 可以利用这一事实证明如下定理：

```lean
example (x y : Fin 11) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "结合情形分析的线性整数算术" (open := true)

```lean
example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
```

:::

# 错误消息
%%%
tag := "grind-errors"
%%%

{tactic}`grind` 失败时，会先打印剩余子目标，再打印其各子系统返回的全部信息，也就是“共享白板”上的内容。
具体而言，它会展示由已判定相等的项构成的等价类。
最大的两个类显示为 `True propositions` 和 `False propositions`，分别列出当前已知可证明或可证伪的每个文字。
检查这些列表，可以找出缺失的事实或相互矛盾的假设。

# 最小化 `grind` 调用

`grind only [...]` 策略使用受限的定理集合调用 {tactic}`grind`，从而可能提升性能。
可以使用 {tactic}`grind?` 方便地构造 `grind only` 调用；它会自动记录 {tactic}`grind` 使用的定理，并建议合适的 `grind only`。

这些定理通常带有 `=`、`←` 或 `→` 等符号前缀，用来表示
触发实例化的模式。详情参见{ref "e-matching"}[关于 E-匹配的章节]。
有些定理可能带有 `usr` 前缀，表示使用了自定义模式。

{include 1 Manual.Grind.CongrClosure}

{include 1 Manual.Grind.ConstraintPropagation}

{include 1 Manual.Grind.CaseAnalysis}

{include 1 Manual.Grind.EMatching}

{include 1 Manual.Grind.Cutsat}

{include 1 Manual.Grind.Algebra}

{include 1 Manual.Grind.Linarith}

{include 1 Manual.Grind.Annotation}

# 可约性

{tactic}`grind` 会及早展开项中的{tech (key := "Reducible")}[可约]定义。
这使定义相等性比较和索引更高效。

:::example "可约性与同余闭包"
{name}`one` 的定义不是{tech (key := "Reducible")}[可约]的：
```lean
def one := 1
```
这意味着 {tactic}`grind` 不会展开它：
```lean +error (name := noUnfold)
example : one = 1 := by grind
```
```leanOutput noUnfold
`grind` failed
case grind
h : ¬one = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [cutsat] Assignment satisfying linear constraints
```

另一方面，{name}`two` 是缩写，因此可约：
```lean
abbrev two := 2
```

{tactic}`grind` 在将 {name}`two` 加入“白板”前先展开它，从而可以立即完成证明：
```lean
example : two = 2 := by grind
```
:::

E-匹配模式也会展开可约定义。
为涉及缩写的定理生成的模式会用展开后的缩写来表示。
缩写通常不应递归；特别是在使用 {tactic}`grind` 时，递归缩写可能导致索引性能不佳以及模式不可预测。

:::example "E-匹配与展开缩写"
为定理添加 {attr}`grind` 标注时，会根据定理陈述生成 E-匹配模式。
这些模式决定何时实例化该定理。
定理 {name}`one_eq_1` 提到了{tech (key := "semireducible")}[半可约]定义 {name}`one`，生成的模式也同样是 {name}`one`：
```lean (name := one_eq_1)
def one := 1

@[grind? =]
theorem one_eq_1 : one = 1 := by rfl
```
```leanOutput one_eq_1
one_eq_1: [one]
```

将相同标注应用于涉及{tech (key := "reducible")}`可约`缩写 {name}`two` 的定理，会得到一个展开了 {name}`two` 的模式：
```lean (name := two_eq_2)
abbrev two := 2

@[grind? =]
theorem two_eq_2: two = 2 := by grind
```
```leanOutput two_eq_2
two_eq_2: [@OfNat.ofNat `[Nat] `[2] `[instOfNatNat 2]]
```

:::

:::example "递归缩写与 `grind`"
使用 {attr}`grind` 属性为递归缩写的{tech (key := "equational lemmas")}[等式引理]添加 E-匹配模式，并不能为递归缩写生成有用的模式。
这个斐波那契函数定义上的 {attrs}`@[grind?]` 属性会生成三个模式，分别对应三种可能情况：
```lean (name := fib1) -keep
@[grind?]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib1
fib.eq_1: [fib `[0]]
```
```leanOutput fib1
fib.eq_2: [fib `[1]]
```
```leanOutput fib1
fib.eq_3: [fib (#0 + 2)]
```
将该定义替换为缩写后，生成的模式会展开其中出现的函数。
这些模式并没有多大用处：
```lean (name := fib2) -keep
@[grind?]
abbrev fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib2
fib.eq_1: [@OfNat.ofNat `[Nat] `[0] `[instOfNatNat 0]]
```
```leanOutput fib2
fib.eq_2: [@OfNat.ofNat `[Nat] `[1] `[instOfNatNat 1]]
```
```leanOutput fib2
fib.eq_3: [@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] (fib #0) (fib (#0 + 1))]
```
:::



```comment
# 诊断
待定
阈值通知、学到的等价类、整数赋值、代数基、已执行的拆分、实例统计。

# 故障排除与常见问题
待定
```

{include 1 Manual.Grind.ExtendedExamples}
