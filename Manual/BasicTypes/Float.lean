/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "浮点数" =>
%%%
tag := "Float"
%%%

浮点数是对实数的一种近似，并且能在计算机硬件中高效实现。
使用浮点数的计算通常非常高效；不过，它们逼近实数的方式本身很复杂，存在许多边界情况。
IEEE 754 标准定义了现代计算机使用的浮点格式，它允许硬件设计者和编程语言实现做出某些选择，而真实系统在这些细节上并不完全相同。
硬件、操作系统、C 编译器、库版本乃至编译选项的任意组合，都可能导致不同的行为。
例如，表示结果未定义的 `NaN` 就有许多不同的位表示，而且有些平台在“两个 `NaN` 相加时究竟返回哪个 `NaN`”这一点上并不一致。

为了能够对浮点数进行推理，Lean 暴露出了一个用于证明的 {name}`Float` 逻辑模型。
具体来说，{name}`Float` 与 {name}`Float32` 都是围绕该逻辑模型实现的包装器。
在编译后的代码中，这个逻辑模型会被高效的原生代码取代。
平台之间的差异通过两种方式解决：一是选择特定表示（例如，只要某个运算请求位表示，所有 `NaN` 值都会被替换为单一的规范 `NaN`），二是只为所有受支持平台上实现完全一致的那一部分浮点运算建立模型。
其他运算（例如三角函数）则在 Lean 的逻辑中表示为不透明函数。

该逻辑模型已在所有受支持平台上与浮点运算进行了广泛的经验性测试。
只要 FFI 代码不修改浮点环境，Lean 运行时的浮点原语就符合该模型的规约。

{docstring Float}

{docstring Float32}

# 逻辑模型

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--Logical-Model"
%%%
Lean 提供两种浮点类型：{name}`Float` 表示 64 位浮点值，而 {name}`Float32` 表示 32 位浮点值。
{name}`Float` 的精度不会随着 Lean 所运行的平台而变化。

## 模型细节

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--Logical-Model--Model-Details"
%%%
{lean}`Float` 与 {lean}`Float32` 的逻辑模型由带有有效性谓词的无符号整数组成。
每个已定义的运算都会先把该整数解释为 {lean}`Float.Model.UnpackedFloat`，这是一个不依赖具体位宽的更高层模型。
然后，用 {name Float.Model.UnpackedFloat}`UnpackedFloat` 来实现该运算，并将结果重新打包。
这些定义构成了一个用于推理的_逻辑规约_。
尽管它们可以执行，但运行速度会明显慢于原生代码。
并非所有运算都有定义；有些运算则被表示为不透明函数，其行为无法在 Lean 的逻辑中进行推理。

该模型并不打算作为更大型浮点数库的基础。
它仅用于支持 Lean 中可用的推理工具，并不适合更大规模的开发。
不要把这个模型当作更大型浮点数库的基础。
正确做法是实现一个合适的模型，证明其运算与该模型上的运算等价，然后借助这种等价转移引理。

{docstring Float.Model}

{docstring Float32.Model}

{docstring Float.Model.pack}

{docstring Float32.Model.pack}

{docstring Float.Model.unpack}

{docstring Float32.Model.unpack}

{docstring Float.Model.UnpackedFloat}

## 模型运算

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--Logical-Model--Model-Operations"
%%%
下列运算为浮点值提供了规约。
其他运算符则表示为不透明函数，不能在内核中规约。

{docstring Float.Model.UnpackedFloat.add}

{docstring Float.Model.UnpackedFloat.sub}

{docstring Float.Model.UnpackedFloat.mul}

{docstring Float.Model.UnpackedFloat.div}

{docstring Float.Model.UnpackedFloat.sqrt}

{docstring Float.Model.UnpackedFloat.neg}

{docstring Float.Model.UnpackedFloat.abs}

{docstring Float.Model.UnpackedFloat.isNaN}

{docstring Float.Model.UnpackedFloat.isInf}

{docstring Float.Model.UnpackedFloat.isFinite}

{docstring Float.Model.UnpackedFloat.compare}

{docstring Float.Model.UnpackedFloat.beq}

{docstring Float.Model.UnpackedFloat.lt}

{docstring Float.Model.UnpackedFloat.le}

{docstring Float.Model.UnpackedFloat.ofNat}

{docstring Float.Model.UnpackedFloat.ofInt}

{docstring Float.Model.UnpackedFloat.ofScientific}

{docstring Float.Model.UnpackedFloat.toInt8}

{docstring Float.Model.UnpackedFloat.ofInt8}

{docstring Float.Model.UnpackedFloat.toInt16}

{docstring Float.Model.UnpackedFloat.ofInt16}

{docstring Float.Model.UnpackedFloat.toInt32}

{docstring Float.Model.UnpackedFloat.ofInt32}

{docstring Float.Model.UnpackedFloat.toInt64}

{docstring Float.Model.UnpackedFloat.ofInt64}

{docstring Float.Model.UnpackedFloat.toISize}

{docstring Float.Model.UnpackedFloat.ofISize}

{docstring Float.Model.UnpackedFloat.toUInt8}

{docstring Float.Model.UnpackedFloat.ofUInt8}

{docstring Float.Model.UnpackedFloat.toUInt16}

{docstring Float.Model.UnpackedFloat.ofUInt16}

{docstring Float.Model.UnpackedFloat.toUInt32}

{docstring Float.Model.UnpackedFloat.ofUInt32}

{docstring Float.Model.UnpackedFloat.toUInt64}

{docstring Float.Model.UnpackedFloat.ofUInt64}

{docstring Float.Model.UnpackedFloat.toUSize}

{docstring Float.Model.UnpackedFloat.ofUSize}

:::example "内核推理"
Lean 内核可以按句法相等比较类型为 {lean}`Float` 的表达式，因此 {lean  (type := "Float")}`0.0` 与其自身定义等价。
```lean
example : (0.0 : Float) = (0.0 : Float) := by rfl
```

此外，如果若干项需要经过规约后才能在句法上相等，那么只要它们只使用了在 Lean 逻辑中建模的运算，内核也可以检查它们：
```lean
example : (0.0 : Float) = (0.0 + 0.0 : Float) := by rfl
```
内核无法规约使用了未被直接建模运算的项，例如三角函数：
```lean (name := sin0) +error
example : (0.0 : Float).sin = (0.0 : Float) := by rfl
```
```leanOutput sin0
Tactic `rfl` failed: The left-hand side
  Float.sin 0.0
is not definitionally equal to the right-hand side
  0.0

⊢ Float.sin 0.0 = 0.0
```


不过，{tactic}`native_decide` 策略可以调用 Lean 在运行时程序中使用的底层平台浮点原语：
```lean
theorem Float.sin_zero_eq_zero :
    ((0.0 : Float).sin == (0.0 : Float)) = true := by
  native_decide
```
该策略会把判定过程作为编译后的原生代码执行。
这意味着，除内核外，还必须信任 Lean 编译器、解释器以及内建运算符的底层实现。
为了精确地说明这一依赖，该策略会生成公理 {name}`Float.sin_zero_eq_zero._native.native_decide.ax_1`：
```lean (name := ofRed)
#print axioms Float.sin_zero_eq_zero
```
```leanOutput ofRed
'Float.sin_zero_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Float.sin_zero_eq_zero._native.native_decide.ax_1]
```
:::

:::example "浮点相等并非自反"
浮点运算可能产生表示结果未定义的 `NaN` 值。
这些值彼此不可比较；特别地，凡是涉及 `NaN` 的比较都会返回 `false`，包括相等比较。
```lean
#eval ((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0)
```
:::

:::example "浮点相等不是同余关系"
把同一个函数应用到两个相等的浮点数上，结果未必仍然相等。
特别地，正零与负零是不同的值，但浮点相等会把它们判为相等；然而用正零或负零作除数时，却会分别得到正无穷或负无穷。
```lean (name := divZeroPosNeg)
def neg0 : Float := -0.0

def pos0 : Float := 0.0

#eval (neg0 == pos0, 1.0 / neg0 == 1.0 / pos0)
```
```leanOutput divZeroPosNeg
(true, false)
```
:::


# 语法

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--Syntax"
%%%
Lean 没有专门的浮点数字面量。
相反，浮点数字面量是通过 {name}`OfScientific` 与 {name}`Neg` 类型类的相应实例来解析的。

:::example "浮点数字面量"

项
```leanTerm
(-2.523 : Float)
```
是下列写法的语法糖：
```leanTerm
(Neg.neg (OfScientific.ofScientific 22523 true 4) : Float)
```
而项
```leanTerm
(413.52 : Float32)
```
是下列写法的语法糖：
```leanTerm
(OfScientific.ofScientific 41352 true 2 : Float32)
```

```lean -show
example : (-2.2523 : Float) = (Neg.neg (OfScientific.ofScientific 22523 true 4) : Float) := by simp [OfScientific.ofScientific]
example : (413.52 : Float32) = (OfScientific.ofScientific 41352 true 2 : Float32) := by simp [OfScientific.ofScientific]
```
:::

# 接口参考
%%%
tag := "Float-api"
%%%

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Properties"
%%%
浮点数属于以下三类之一：

 * 有限数是普通的浮点值。

 * 无穷大可能是正的也可能是负的，它们来源于除以零。

 * `NaN` 不是数，它来源于其他未定义运算，例如对负数取平方根。

{docstring Float.isInf}

{docstring Float32.isInf}

{docstring Float.isNaN}

{docstring Float32.isNaN}

{docstring Float.isFinite}

{docstring Float32.isFinite}


## 转换

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Conversions"
%%%
{docstring Float.toBits}

{docstring Float32.toBits}

{docstring Float.ofBits}

{docstring Float32.ofBits}

{docstring Float.toFloat32}

{docstring Float32.toFloat}

{docstring Float.toString}

{docstring Float32.toString}

{docstring Float.toUInt8}

{docstring Float.toInt8}

{docstring Float32.toUInt8}

{docstring Float32.toInt8}

{docstring Float.toUInt16}

{docstring Float.toInt16}

{docstring Float32.toUInt16}

{docstring Float32.toInt16}

{docstring Float.toUInt32}

{docstring Float32.toUInt32}

{docstring Float.toInt32}

{docstring Float32.toInt32}

{docstring Float.toUInt64}

{docstring Float.toInt64}

{docstring Float32.toUInt64}

{docstring Float32.toInt64}

{docstring Float.toUSize}

{docstring Float32.toUSize}

{docstring Float.toISize}

{docstring Float32.toISize}

{docstring Float.ofInt}

{docstring Float32.ofInt}

{docstring Float.ofNat}

{docstring Float32.ofNat}

{docstring Float.frExp}

{docstring Float32.frExp}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Comparisons"
%%%
{docstring Float.beq}

{docstring Float32.beq}

### 不等关系

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Comparisons--Inequalities"
%%%
不等关系的判定过程在逻辑中是不透明常量。
它们只能借助 {name}`Lean.ofReduceBool` 公理来使用，例如通过 {tactic}`native_decide` 策略。

{docstring Float.le}

{docstring Float32.le}

{docstring Float.lt}

{docstring Float32.lt}

{docstring Float.decLe}

{docstring Float32.decLe}

{docstring Float.decLt}

{docstring Float32.decLt}

## 算术

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Arithmetic"
%%%
浮点值上的算术运算通常通过 {inst}`Add Float`、{inst}`Sub Float`、{inst}`Mul Float`、{inst}`Div Float` 和 {inst}`HomogeneousPow Float` 实例来调用，{name}`Float32` 也有对应实例。

{docstring Float.add}

{docstring Float32.add}

{docstring Float.sub}

{docstring Float32.sub}

{docstring Float.mul}

{docstring Float32.mul}

{docstring Float.div}

{docstring Float32.div}

{docstring Float.pow}

{docstring Float32.pow}

{docstring Float.exp}

{docstring Float32.exp}

{docstring Float.exp2}

{docstring Float32.exp2}

### 根

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Arithmetic--Roots"
%%%
对负数计算平方根会得到 `NaN`。

{docstring Float.sqrt}

{docstring Float32.sqrt}

{docstring Float.cbrt}

{docstring Float32.cbrt}

## 对数

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Logarithms"
%%%
{docstring Float.log}

{docstring Float32.log}

{docstring Float.log10}

{docstring Float32.log10}

{docstring Float.log2}

{docstring Float32.log2}

## 缩放

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Scaling"
%%%
{docstring Float.scaleB}

{docstring Float32.scaleB}

## 取整

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Rounding"
%%%
{docstring Float.round}

{docstring Float32.round}

{docstring Float.floor}

{docstring Float32.floor}

{docstring Float.ceil}

{docstring Float32.ceil}

## 三角函数

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry"
%%%
### 正弦

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Sine"
%%%
{docstring Float.sin}

{docstring Float32.sin}

{docstring Float.sinh}

{docstring Float32.sinh}

{docstring Float.asin}

{docstring Float32.asin}

{docstring Float.asinh}

{docstring Float32.asinh}

### 余弦

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Cosine"
%%%
{docstring Float.cos}

{docstring Float32.cos}

{docstring Float.cosh}

{docstring Float32.cosh}

{docstring Float.acos}

{docstring Float32.acos}

{docstring Float.acosh}

{docstring Float32.acosh}

### 正切

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Tangent"
%%%
{docstring Float.tan}

{docstring Float32.tan}

{docstring Float.tanh}

{docstring Float32.tanh}

{docstring Float.atan}

{docstring Float32.atan}

{docstring Float.atanh}

{docstring Float32.atanh}

{docstring Float.atan2}

{docstring Float32.atan2}

## 取负与绝对值

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Negation-and-Absolute-Value"
%%%
{docstring Float.abs}

{docstring Float32.abs}

{docstring Float.neg}

{docstring Float32.neg}
