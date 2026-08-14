/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

-- 由于 Lean.Grind.Semiring.nsmul_eq_natCast_mul
set_option verso.docstring.allowMissing true

open Lean.Grind

#doc (Manual) "线性算术求解器" =>
%%%
tag := "grind-linarith"
%%%

{tactic}`grind` 策略内置了一个面向任意类型的线性算术求解器 `linarith`，用于处理 {ref "cutsat"}`cutsat` 不支持的类型。
和 {ref "grind-ring"}`ring` 求解器一样，只要某个类型拥有若干类型类实例，就可以使用它。
它会根据这些类型类实例的可用性自行配置，因此并不需要提供全部实例才能使用该求解器；不过，可用实例越多，它的能力也就越强。
这个求解器适合用来推理实数、有序向量空间，以及其他无法嵌入到 {name}`Int` 中的类型。


`linarith` 的核心功能，是一个用于处理整数系数线性不等式的基于模型的求解器。
它可以用选项 `grind -linarith` 禁用。


:::example "由 `linarith` 判定的目标" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
下面这些例子都依赖于下列序关系记号以及 `linarith` 相关类型类的实例：
```lean
variable [LE α] [LT α] [Std.LawfulOrderLT α]  [Std.IsLinearOrder α]
variable [IntModule α] [OrderedAdd α]
```

整数模（{name}`IntModule`）是带有零、加法、取负、减法以及整数标量乘法的类型，并满足这些运算应有的性质。
线性序（{name}`Std.IsLinearOrder`）要求任意两个元素都可比较，而 {name}`OrderedAdd` 表示在不等式两边同时加上一个常量会保持序关系。

```lean
example {a b : α} : 2 • a + b ≥ b + a + a := by grind

example {a b : α} (h : a ≤ b) : 3 • a + b ≤ 4 • b := by grind

example {a b c : α} :
    a = b + c →
    2 • b ≤ c →
    2 • a ≤ 3 • c := by
  grind

example {a b c d e : α} :
    2 • a + b ≥ 0 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0 →
    a ≥ 3 • c → c ≥ 6 • e → d - 5 • e ≥ 0 →
    a + b + 3 • c + d + 2 • e < 0 →
    False := by
  grind
```
:::

:::example "由 `linarith` 判定的交换环目标" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
对于带有 {name}`CommRing` 实例的交换环类型（也就是乘法满足交换律的类型），`linarith` 具备更强的能力。

```lean
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
variable [CommRing R] [OrderedRing R]
```

{inst}`CommRing R` 实例允许 `linarith` 进行基础规范化，例如识别线性原子 `a * b` 与 `b * a`，并处理等式或不等式两边的标量乘法。
{inst}`OrderedRing R` 实例则让求解器能够支持常量，因为它可以利用 {lean}`(0 : R) < 1` 这一事实。

```lean
example (a b : R) (h : a * b ≤ 1) : b * 3 • a + 1 ≤ 4 := by grind

example (a b c d e f : R) :
    2 • a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e • f ≥ 0 →
    a ≥ 3 • c →
    c ≥ 6 • e • f → d - f * e * 5 ≥ 0 →
    a + b + 3 • c + d + 2 • e • f < 0 →
    False := by
  grind
```
:::

:::TODO
计划中的未来功能
* 支持 `NatModule`（通过嵌入到 Grothendieck 包络中，就像我们已经对半环所做的那样），
* 改进 `ring` 与 `linarith` 求解器之间的通信。
  目前这两个求解器之间的通信还很少。
* 有序环上的非线性算术。
:::

# 支持 `linarith`
%%%
tag := "grind-linarith-classes"
%%%

若要让 `linarith` 支持一种新类型，第一步是在可能时实现 {name}`IntModule`，否则实现 {name}`NatModule`。
每个 {name}`Ring` 都已经是 {name}`IntModule`，每个 {name}`Semiring` 都已经是 {name}`NatModule`，因此实现其中任一实例也已足够。
接下来，还应实现某个序类型类（{name}`Std.IsPreorder`、{name}`Std.IsPartialOrder` 或 {name}`Std.IsLinearOrder`）。
通常来说，当上下文中已经包含矛盾时，{name Std.IsPreorder}`IsPreorder` 实例就够用；但若要证明线性不等式目标，则需要 {name Std.IsLinearOrder}`IsLinearOrder` 实例。
此外，若实现 {name}`OrderedAdd`（表达模的加法结构与序相容）以及 {name}`OrderedRing`（改进对常量的支持），还可以启用更多功能。


{docstring Lean.Grind.NatModule}

{docstring Lean.Grind.IntModule}

{docstring Lean.Grind.OrderedAdd}

{docstring Lean.Grind.OrderedRing}
