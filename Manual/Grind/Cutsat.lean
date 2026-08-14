/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Grind
import Manual.Papers


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External (lit)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "线性整数算术" =>
%%%
file := "Linear-Integer-Arithmetic"
tag := "cutsat"
%%%

:::paragraph
线性整数算术求解器实现了一个针对线性整数算术的基于模型的判定过程。
该求解器能够处理四类线性多项式约束（其中 `p` 是一个[线性多项式](https://en.wikipedia.org/wiki/Degree_of_a_polynomial)）：

: 等式

 `p = 0`

: 整除性

 `d ∣ p`

: 不等式

  `p ≤ 0`

: 不等关系

  `p ≠ 0`

它对于线性整数算术是完备的，并且通过用 {name}`Int.ofNat` 将自然数转换成整数，也支持自然数。
对于其他能够嵌入到 {lean}`Int` 中的类型，可以通过提供 {name}`Lean.Grind.ToInt` 的实例来增加支持。
非线性项（例如 `x * x`）也是允许的，但会被表示为变量。
此外，该求解器还能把信息传播回比喻意义上的 {tactic}`grind` 白板，从而触发其他子系统进一步推进证明。
默认情况下它是启用的；可以用标志 {lit}`-lia` 将其禁用。
:::



::::example "线性整数算术示例" (open := true)

下面这些命题都可以用线性整数算术求解器证明。
在第一个例子中，左边必定是 2 的倍数，因此不可能等于 5：
```lean
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind
```

求解器支持混合使用等式与不等式：
```lean
example {x y : Int} :
    2 * x + 3 * y = 0 →
    1 ≤ x →
    y < 1 := by
  grind
```

它也支持线性的整除约束：
```lean
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind
```


如果没有 `lia`，{tactic}`grind` 就无法证明该命题：

```lean +error (name := noLia)
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind -lia
```
```leanOutput noLia
`grind` failed
case grind
a b : Int
h : 2 ∣ a + 1
h_1 : 2 ∣ a + b
h_2 : 2 ∣ 2 * a + b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [linarith] Linarith assignment for `Int`
```
::::

# 有理数解
%%%
tag := "cutsat-qlia"
%%%

该求解器对线性整数算术是完备的。
不过，即使约束很少，搜索空间也可能迅速变得极大，而这个求解器并不是为大规模分类讨论而设计的。
{tactic}`grind` 的 `qlia` 选项通过允许求解器接受有理数解来缩小搜索空间。
使用该选项后，求解器通常会更快，但它就不再完备。

:::example "有理数解但无整数解"
下面这个例子有有理数解，但没有整数解：
```lean
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind
```

由于它使用的是有理数解，因此在指定 `+qlia` 时，{tactic}`grind` 无法驳倒目标的否定：
```lean +error (name := withqlia)
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind +qlia
```
```leanOutput withqlia (expandTrace := cutsat)
`grind` failed
case grind
x y : Int
h : -13 * x + -11 * y + 27 ≤ 0
h_1 : 13 * x + 11 * y + -30 ≤ 0
h_2 : -9 * x + 7 * y + -10 ≤ 0
h_3 : 9 * x + -7 * y + -4 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 62/117
    [assign] y := 2
```

求解器构造出的有理模型，出现在目标诊断里的 `Assignment satisfying linear constraints` 一节中。
:::

# 非线性约束
%%%
tag := "grind-nonlinear-constraints"
%%%

该求解器目前并不真正求解非线性约束，而是把 `x * x` 这样的非线性项当作变量处理。

::::example "非线性项" (open := true)
线性整数算术求解器无法证明这个定理：

```lean +error (name := nonlinear)
example (x : Int) : x * x ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

从线性整数算术求解器的视角来看，这等价于：

```lean +error (name := nonlinear2)
example {y : Int} (x : Int) : y ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

:::paragraph
这一点可以通过把选项 {option}`trace.grind.lia.assert` 设为 {lean}`true` 看出来；这样会追踪求解器处理的所有约束。

```lean +error (name := liaDiag)
example (x : Int) : x*x ≥ 0 := by
  set_option trace.grind.lia.assert true in
  grind
```
```leanOutput liaDiag
[grind.lia.assert] -1*「x ^ 2 + 1」 + 「x ^ 2」 + 1 = 0
[grind.lia.assert] 「x ^ 2」 + 1 ≤ 0
```
在 `「x ^ 2」 + 1 ≤ 0` 中，项 `x ^ 2` 被“加引号”显示，以表明 `x ^ 2` 被当作一个变量处理。
:::
::::

# 除法与模
%%%
tag := "grind-division-and-modulus"
%%%

该求解器支持线性的除法与取模运算。

:::example "线性除法与取模"
```lean
example (x y : Int) :
    x = y / 2 →
    y % 2 = 0 →
    y - 2 * x = 0 := by
  grind
```
:::

# 代数处理
%%%
tag := "grind-algebraic-processing"
%%%

该求解器会对交换（半）环表达式做规范化。

:::example "交换（半）环规范化"
交换环规范化使得下面这个目标可被证明：
```lean
example (a b : Nat)
    (h₁ : a + 1 ≠ a * b * a)
    (h₂ : a * a * b ≤ a + 1) :
    b * a ^ 2 < a + 1 := by
  grind
```
:::

# 传播信息
%%%
tag := "cutsat-mbtc"
%%%

该求解器还实现了 {deftech (key := "model-based theory combination")}_基于模型的理论组合_，这是一种把等式传播回共享白板的机制。
这些新增的等式又可能进一步触发新的同余。
基于模型的理论组合会扩大搜索空间；可以使用选项 `grind -mbtc` 将其禁用。

::::example "传播等式"
在上面的例子里，线性不等式与不等关系蕴含 `y = 0`：
```lean
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind
```
因此 `x = x + y`，于是由 {tech (key := "congruence closure")}[同余] 得到 `f x = f (x + y)`。
如果没有基于模型的理论组合，证明就会卡住：
```lean +error (name := noMbtc)
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind -mbtc
```
```leanOutput noMbtc
`grind` failed
case grind
f : Int → Int
x y : Int
h : f x = 0
h_1 : -1 * y ≤ 0
h_2 : y + -1 ≤ 0
h_3 : ¬y = 1
h_4 : ¬f (x + y) = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Int`
```
::::

# 其他类型
%%%
tag := "cutsat-ToInt"
%%%

LIA 求解器也可以处理包含自然数的线性约束。
它会使用 `Int.ofNat` 将其转换为整数约束。

:::example "作为线性整数算术的自然数"
```lean
example (x y z : Nat) :
    x < y + z →
    y + 1 < z →
    z + x < 3 * z := by
  grind
```
:::

通过 {lean}`Lean.Grind.ToInt` 类型类，有一种可扩展机制可以告诉求解器某个类型能够嵌入到整数中。
借助这一机制，我们可以求解如下目标：

```lean
example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

{zhdocstring Lean.Grind.ToInt ZhDoc.ToInt}

{zhdocstring Lean.Grind.IntInterval ZhDoc.IntInterval}

# 实现说明
%%%
tag := "grind-implementation-notes"
%%%

::::leanSection
```lean -show
variable {x y : Int}
```

:::paragraph
线性整数算术求解器的实现受到了 {citet cuttingToTheChase}[] 第 4 节的启发。
与论文相比，它还包含若干增强与修改，例如：

* 扩展了约束支持（等式与不等关系），

* 对 `Cooper-Left` 规则进行了优化编码，使用一个“大”析取而不是新鲜变量，以及

* 对分类讨论中的决策变量进行跟踪（不等关系、`Cooper-Left`、`Cooper-Right`）。
:::

:::paragraph
该求解过程会逐步构造一个模型（也就是对项中变量的赋值），并通过生成约束来解决冲突。
例如，给定部分模型 `{x := 1}` 和约束 {lean}`3 ∣ 3 * y + x + 1`：

- 求解器无法把该模型扩展到 {lean}`y`，因为 {lean}`3 ∣ 3 * y + 2` 不可满足。

- 因此，它会通过生成蕴含约束 {lean}`3 ∣ x + 1` 来消解冲突。

- 这个新约束迫使求解器为 {lean}`x` 寻找新的赋值。
:::


:::paragraph
在为变量 `y` 赋值时，求解器会考虑：

- 最佳的上界与下界（不等式）。

- 一个整除约束。

- 所有以 `y` 为最大变量的不等关系约束。
:::
::::

`Cooper-Left` 与 `Cooper-Right` 规则负责处理不等式与整除性的组合。
对于不可满足的不等关系 `p ≠ 0`，求解器会生成如下分类讨论：`p + 1 ≤ 0 ∨ -p + 1 ≤ 0`。


:::comment
计划中的未来功能：改进约束传播。
:::
