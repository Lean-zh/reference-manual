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

-- Due to Lean.Grind.Semiring.nsmul_eq_natCast_mul
set_option verso.docstring.allowMissing true
set_option maxHeartbeats 300000

#doc (Manual) "代数求解器（交换环、域）" =>
%%%
tag := "grind-ring"
%%%

{tactic}`grind` 中的 `ring` 求解器受 Gröbner 基计算过程和项重写完备化的启发。
它将多元多项式视为重写规则。
例如，多项式等式 `x * y + x - 2 = 0` 会被视为重写规则 `x * y ↦ -x + 2`。
它使用叠加来确保重写系统具有汇合性。

以下示例展示了 `ring` 求解器能够判定的目标。
在这些示例中，命名空间 `Lean` 和 `Lean.Grind` 均已打开：
```lean
open Lean Grind
```

:::example "交换环" (open := true)
```lean -show
open Lean.Grind
```
```lean
example [CommRing α] (x : α) : (x + 1) * (x - 1) = x ^ 2 - 1 := by
  grind
```
:::
:::example "环的特征" (open := true)
求解器“知道” `16*16 = 0`，因为[环的特征](https://en.wikipedia.org/wiki/Characteristic_%28algebra%29)（即若干个乘法单位元相加得到加法单位元时，所需份数的最小值）为 `256`；这一信息由 {name}`IsCharP` 实例提供。

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16)*(x - 16) = x^2 := by
  grind
```
:::

:::example "标准库类型" (open := true)
```lean -show
open Lean.Grind
```
求解器开箱即用地支持标准库中的类型。
`UInt8` 是特征为 `256` 的交换环，因此具有 {inst}`CommRing UInt8` 和 {inst}`IsCharP UInt8 256` 实例。
```lean
example (x : UInt8) : (x + 16) * (x - 16) = x ^ 2 := by
  grind
```
:::

:::example "更多交换环证明" (open := true)
```lean -show
open Lean.Grind
```
交换环的公理足以证明以下命题。

```lean
example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```

```lean
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "特征为零" (open := true)
```lean -show
open Lean.Grind
```
`ring` 证明 `a + 1 = 2 + a` 不可满足，因为已知其特征为 0。

```lean
example [CommRing α] [IsCharP α 0] (a : α) :
    a + 1 = 2 + a → False := by
  grind
```
:::

:::example "推断特征" (open := true)
```lean -show
open Lean.Grind
```
即使最初不知道特征，当 `grind` 发现某个数值 `n` 满足 `n = 0` 时，也会对特征作出推断：
```lean
example [CommRing α] (a b c : α)
    (h₁ : a + 6 = a) (h₂ : c = c + 9) (h : b + 3*c = 0) :
    27*a + b = 0 := by
  grind
```
:::

# 求解器类型类
%%%
tag := "grind-ring-classes"
%%%

:::paragraph
用户可以为自己的类型提供下列{tech (key := "type class")}[类型类]的实例，以启用 `ring` 求解器；这些类型类均位于 `Lean.Grind` 命名空间中：

* {name Lean.Grind.Semiring}`Semiring`

* {name Lean.Grind.Ring}`Ring`

* {name Lean.Grind.CommSemiring}`CommSemiring`

* {name Lean.Grind.CommRing}`CommRing`

* {name Lean.Grind.IsCharP}`IsCharP`

* {name Lean.Grind.AddRightCancel}`AddRightCancel`

* {name Lean.Grind.NoNatZeroDivisors}`NoNatZeroDivisors`

* {name Lean.Grind.Field}`Field`


代数求解器会根据这些实例是否可用来自行配置，因此不必提供全部实例。
当然，缺少某些实例时，代数求解器的能力也会相应降低。
:::

Lean 标准库为其中定义的类型提供了适用的实例。
其他库也可以通过提供这些实例来启用 {tactic}`grind` 的 `ring` 求解器。
例如，Mathlib 的 `CommRing` 类型类实现了 `Lean.Grind.CommRing`，从而确保 `ring` 求解器开箱即用。

## 代数结构

要启用代数求解器，一个类型应当具有该求解器所支持的、尽可能具体的代数结构实例。
按具体程度递增的顺序，依次为 {name Lean.Grind.Semiring}`Semiring`、{name Lean.Grind.Ring}`Ring`、{name Lean.Grind.CommSemiring}`CommSemiring`、{name Lean.Grind.CommRing}`CommRing` 和 {name Lean.Grind.Field}`Field`。

{docstring Lean.Grind.Semiring}

{docstring Lean.Grind.CommSemiring}

{docstring Lean.Grind.Ring}

{docstring Lean.Grind.CommRing}

### 域
%%%
tag := "grind-ring-field"
%%%

:::leanSection
```lean -show
variable {a b p : α} [Field α]
```
`ring` 求解器也支持 {name}`Field`。
如果有可用的 {name}`Field` 实例，求解器会将项 `a / b` 预处理为 `a * b⁻¹`。
它还会将每个不等式 `p ≠ 0` 重写为等式 `p * p⁻¹ = 1`。
:::

::::example "域与 `grind`"
```lean -show
open Lean.Grind
```
此示例需要 {name}`Field` 实例：

```lean
example [Field α] (a : α) :
    a ^ 2 = 0 →
    a = 0 := by
  grind
```
::::

{docstring Lean.Grind.Field}

## 环的特征

:::TODO

待撰写

:::

{docstring Lean.Grind.IsCharP}


## 自然数零因子
%%%
tag := "NoNatZeroDivisors"
%%%


`NoNatZeroDivisors` 类用于控制系数增长。
例如，多项式 `2 * x * y + 4 * z = 0` 会被化简为 `x * y + 2 * z = 0`。
处理不等式时也会使用该类。

:::example "使用 `NoNatZeroDivisors`"
```lean -show
open Lean.Grind
```
在此示例中，{tactic}`grind` 依赖 {name}`NoNatZeroDivisors` 实例来化简目标：
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
没有该实例，证明就会失败：
```lean (name := NoNatZero) +error
example [CommRing α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
```leanOutput NoNatZero
`grind` failed
case grind
α : Type u_1
inst : CommRing α
a b : α
h : 2 * a + 2 * b = 0
h_1 : ¬b = -a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
```
:::

{docstring Lean.Grind.NoNatZeroDivisors}

{docstring Lean.Grind.NoNatZeroDivisors.mk'}

`ring` 模块还会根据 `a` 是否为零，对项 `a⁻¹` 进行情形分析。
在以下示例中，如果 `2*a` 为零，那么 `a` 也为零，因为
有 `NoNatZeroDivisors α`，于是所有项都为零，等式成立。否则，
`ring` 会添加等式 `a*a⁻¹ = 1` 和 `2*a*(2*a)⁻¹ = 1`，并关闭目标。

```lean
example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

没有 `NoNatZeroDivisors` 时，`grind` 会按需对数值是否为零进行情形拆分：
```lean
example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind
```

在以下示例中，`ring` 无需进行任何情形拆分，因为
目标包含不等式 `y ≠ 0` 和 `w ≠ 0`。

```lean
example [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  grind (splits := 0)
```

可以使用选项 `grind -ring` 禁用 `ring` 求解器。

```lean +error (name := noRing)
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind -ring
```
```leanOutput noRing
`grind` failed
case grind
α : Type u_1
inst : CommRing α
x y : α
h : x ^ 2 * y = 1
h_1 : x * y ^ 2 = y
h_2 : ¬y * x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [linarith] Linarith assignment for `α`
```

### 右消去加法
%%%
tag := "AddRightCancel"
%%%

`ring` 求解器会自动将 `CommSemiring` 嵌入一个 `CommRing` 包络中（使用构造 `Lean.Grind.Ring.OfSemiring.Q`）。
不过，只有当 `CommSemiring` 实现类型类 `AddRightCancel` 时，该嵌入才是单射。
`Nat` 是实现了 `AddRightCancel` 的交换半环示例。

```lean
example (x y : Nat) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```

{docstring Lean.Grind.AddRightCancel}

# 资源限制

Gröbner 基计算可能非常昂贵。可以使用选项 `grind (ringSteps := <num>)` 限制 `ring` 求解器执行的步数。

:::example "限制 `ring` 的步数"
```lean -show
open Lean.Grind
```
最多执行 100 步无法求解此示例：
```lean +error (name := ring100)
example [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α) :
    d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0 →
    -d ^ 4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t^4 +
      2 * d^2 * t^4 - c * (d + t + d * t)) = 0 →
    d * d_inv = 1 →
    (d + t - d * t - 2) * PSO3_inv = 1 →
    t^2 = t + 1 := by
  grind (ringSteps := 100)
```
```leanOutput ring100
`grind` failed
case grind
α : Type u_1
inst : CommRing α
inst_1 : IsCharP α 0
d t c d_inv PSO3_inv : α
h : d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0
h_1 : -d ^ 4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t ^ 4 + 2 * d ^ 2 * t ^ 4 - c * (d + t + d * t)) =
  0
h_2 : d * d_inv = 1
h_3 : (d + t - d * t - 2) * PSO3_inv = 1
h_4 : ¬t ^ 2 = t + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [ring] Ring `α`
  [limits] Thresholds reached
```
:::

`ring` 求解器使用计算出的 Gröbner 基对项进行规范化，从而将等式传播回 `grind` 核心。
在以下示例中，方程 `x ^ 2 * y = 1` 和 `x * y ^ 2 = y` 蕴含等式 `x = 1` 和 `y = 1`。
因此，项 `x * y` 与 `1` 相等，进而由同余性可得 `some (x * y) = some 1`。

```lean
example (x y : Int) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    some (y * x) = some 1 := by
  grind
```

:::comment
未来计划支持非交换环和半环。
:::
