/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G2

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

{zhdocstring Float Manual.ZhDocString.Ch19Ch20.G2.c001}

{zhdocstring Float32 Manual.ZhDocString.Ch19Ch20.G2.c002}

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

{zhdocstring Float.Model Manual.ZhDocString.Ch19Ch20.G2.c003}

{zhdocstring Float32.Model Manual.ZhDocString.Ch19Ch20.G2.c004}

{zhdocstring Float.Model.pack Manual.ZhDocString.Ch19Ch20.G2.c005}

{zhdocstring Float32.Model.pack Manual.ZhDocString.Ch19Ch20.G2.c006}

{zhdocstring Float.Model.unpack Manual.ZhDocString.Ch19Ch20.G2.c007}

{zhdocstring Float32.Model.unpack Manual.ZhDocString.Ch19Ch20.G2.c008}

{zhdocstring Float.Model.UnpackedFloat Manual.ZhDocString.Ch19Ch20.G2.c009}

## 模型运算

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--Logical-Model--Model-Operations"
%%%
下列运算为浮点值提供了规约。
其他运算符则表示为不透明函数，不能在内核中规约。

{zhdocstring Float.Model.UnpackedFloat.add Manual.ZhDocString.Ch19Ch20.G2.c010}

{zhdocstring Float.Model.UnpackedFloat.sub Manual.ZhDocString.Ch19Ch20.G2.c011}

{zhdocstring Float.Model.UnpackedFloat.mul Manual.ZhDocString.Ch19Ch20.G2.c012}

{zhdocstring Float.Model.UnpackedFloat.div Manual.ZhDocString.Ch19Ch20.G2.c013}

{zhdocstring Float.Model.UnpackedFloat.sqrt Manual.ZhDocString.Ch19Ch20.G2.c014}

{zhdocstring Float.Model.UnpackedFloat.neg Manual.ZhDocString.Ch19Ch20.G2.c015}

{zhdocstring Float.Model.UnpackedFloat.abs Manual.ZhDocString.Ch19Ch20.G2.c016}

{zhdocstring Float.Model.UnpackedFloat.isNaN Manual.ZhDocString.Ch19Ch20.G2.c017}

{zhdocstring Float.Model.UnpackedFloat.isInf Manual.ZhDocString.Ch19Ch20.G2.c018}

{zhdocstring Float.Model.UnpackedFloat.isFinite Manual.ZhDocString.Ch19Ch20.G2.c019}

{zhdocstring Float.Model.UnpackedFloat.compare Manual.ZhDocString.Ch19Ch20.G2.c020}

{zhdocstring Float.Model.UnpackedFloat.beq Manual.ZhDocString.Ch19Ch20.G2.c021}

{zhdocstring Float.Model.UnpackedFloat.lt Manual.ZhDocString.Ch19Ch20.G2.c022}

{zhdocstring Float.Model.UnpackedFloat.le Manual.ZhDocString.Ch19Ch20.G2.c023}

{zhdocstring Float.Model.UnpackedFloat.ofNat Manual.ZhDocString.Ch19Ch20.G2.c024}

{zhdocstring Float.Model.UnpackedFloat.ofInt Manual.ZhDocString.Ch19Ch20.G2.c025}

{zhdocstring Float.Model.UnpackedFloat.ofScientific Manual.ZhDocString.Ch19Ch20.G2.c026}

{zhdocstring Float.Model.UnpackedFloat.toInt8 Manual.ZhDocString.Ch19Ch20.G2.c027}

{zhdocstring Float.Model.UnpackedFloat.ofInt8 Manual.ZhDocString.Ch19Ch20.G2.c028}

{zhdocstring Float.Model.UnpackedFloat.toInt16 Manual.ZhDocString.Ch19Ch20.G2.c029}

{zhdocstring Float.Model.UnpackedFloat.ofInt16 Manual.ZhDocString.Ch19Ch20.G2.c030}

{zhdocstring Float.Model.UnpackedFloat.toInt32 Manual.ZhDocString.Ch19Ch20.G2.c031}

{zhdocstring Float.Model.UnpackedFloat.ofInt32 Manual.ZhDocString.Ch19Ch20.G2.c032}

{zhdocstring Float.Model.UnpackedFloat.toInt64 Manual.ZhDocString.Ch19Ch20.G2.c033}

{zhdocstring Float.Model.UnpackedFloat.ofInt64 Manual.ZhDocString.Ch19Ch20.G2.c034}

{zhdocstring Float.Model.UnpackedFloat.toISize Manual.ZhDocString.Ch19Ch20.G2.c035}

{zhdocstring Float.Model.UnpackedFloat.ofISize Manual.ZhDocString.Ch19Ch20.G2.c036}

{zhdocstring Float.Model.UnpackedFloat.toUInt8 Manual.ZhDocString.Ch19Ch20.G2.c037}

{zhdocstring Float.Model.UnpackedFloat.ofUInt8 Manual.ZhDocString.Ch19Ch20.G2.c038}

{zhdocstring Float.Model.UnpackedFloat.toUInt16 Manual.ZhDocString.Ch19Ch20.G2.c039}

{zhdocstring Float.Model.UnpackedFloat.ofUInt16 Manual.ZhDocString.Ch19Ch20.G2.c040}

{zhdocstring Float.Model.UnpackedFloat.toUInt32 Manual.ZhDocString.Ch19Ch20.G2.c041}

{zhdocstring Float.Model.UnpackedFloat.ofUInt32 Manual.ZhDocString.Ch19Ch20.G2.c042}

{zhdocstring Float.Model.UnpackedFloat.toUInt64 Manual.ZhDocString.Ch19Ch20.G2.c043}

{zhdocstring Float.Model.UnpackedFloat.ofUInt64 Manual.ZhDocString.Ch19Ch20.G2.c044}

{zhdocstring Float.Model.UnpackedFloat.toUSize Manual.ZhDocString.Ch19Ch20.G2.c045}

{zhdocstring Float.Model.UnpackedFloat.ofUSize Manual.ZhDocString.Ch19Ch20.G2.c046}

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

{zhdocstring Float.isInf Manual.ZhDocString.Ch19Ch20.G2.c047}

{zhdocstring Float32.isInf Manual.ZhDocString.Ch19Ch20.G2.c048}

{zhdocstring Float.isNaN Manual.ZhDocString.Ch19Ch20.G2.c049}

{zhdocstring Float32.isNaN Manual.ZhDocString.Ch19Ch20.G2.c050}

{zhdocstring Float.isFinite Manual.ZhDocString.Ch19Ch20.G2.c051}

{zhdocstring Float32.isFinite Manual.ZhDocString.Ch19Ch20.G2.c052}


## 转换

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Conversions"
%%%
{zhdocstring Float.toBits Manual.ZhDocString.Ch19Ch20.G2.c053}

{zhdocstring Float32.toBits Manual.ZhDocString.Ch19Ch20.G2.c054}

{zhdocstring Float.ofBits Manual.ZhDocString.Ch19Ch20.G2.c055}

{zhdocstring Float32.ofBits Manual.ZhDocString.Ch19Ch20.G2.c056}

{zhdocstring Float.toFloat32 Manual.ZhDocString.Ch19Ch20.G2.c057}

{zhdocstring Float32.toFloat Manual.ZhDocString.Ch19Ch20.G2.c058}

{zhdocstring Float.toString Manual.ZhDocString.Ch19Ch20.G2.c059}

{zhdocstring Float32.toString Manual.ZhDocString.Ch19Ch20.G2.c060}

{zhdocstring Float.toUInt8 Manual.ZhDocString.Ch19Ch20.G2.c061}

{zhdocstring Float.toInt8 Manual.ZhDocString.Ch19Ch20.G2.c062}

{zhdocstring Float32.toUInt8 Manual.ZhDocString.Ch19Ch20.G2.c063}

{zhdocstring Float32.toInt8 Manual.ZhDocString.Ch19Ch20.G2.c064}

{zhdocstring Float.toUInt16 Manual.ZhDocString.Ch19Ch20.G2.c065}

{zhdocstring Float.toInt16 Manual.ZhDocString.Ch19Ch20.G2.c066}

{zhdocstring Float32.toUInt16 Manual.ZhDocString.Ch19Ch20.G2.c067}

{zhdocstring Float32.toInt16 Manual.ZhDocString.Ch19Ch20.G2.c068}

{zhdocstring Float.toUInt32 Manual.ZhDocString.Ch19Ch20.G2.c069}

{zhdocstring Float32.toUInt32 Manual.ZhDocString.Ch19Ch20.G2.c070}

{zhdocstring Float.toInt32 Manual.ZhDocString.Ch19Ch20.G2.c071}

{zhdocstring Float32.toInt32 Manual.ZhDocString.Ch19Ch20.G2.c072}

{zhdocstring Float.toUInt64 Manual.ZhDocString.Ch19Ch20.G2.c073}

{zhdocstring Float.toInt64 Manual.ZhDocString.Ch19Ch20.G2.c074}

{zhdocstring Float32.toUInt64 Manual.ZhDocString.Ch19Ch20.G2.c075}

{zhdocstring Float32.toInt64 Manual.ZhDocString.Ch19Ch20.G2.c076}

{zhdocstring Float.toUSize Manual.ZhDocString.Ch19Ch20.G2.c077}

{zhdocstring Float32.toUSize Manual.ZhDocString.Ch19Ch20.G2.c078}

{zhdocstring Float.toISize Manual.ZhDocString.Ch19Ch20.G2.c079}

{zhdocstring Float32.toISize Manual.ZhDocString.Ch19Ch20.G2.c080}

{zhdocstring Float.ofInt Manual.ZhDocString.Ch19Ch20.G2.c081}

{zhdocstring Float32.ofInt Manual.ZhDocString.Ch19Ch20.G2.c082}

{zhdocstring Float.ofNat Manual.ZhDocString.Ch19Ch20.G2.c083}

{zhdocstring Float32.ofNat Manual.ZhDocString.Ch19Ch20.G2.c084}

{zhdocstring Float.frExp Manual.ZhDocString.Ch19Ch20.G2.c085}

{zhdocstring Float32.frExp Manual.ZhDocString.Ch19Ch20.G2.c086}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Comparisons"
%%%
{zhdocstring Float.beq Manual.ZhDocString.Ch19Ch20.G2.c087}

{zhdocstring Float32.beq Manual.ZhDocString.Ch19Ch20.G2.c088}

### 不等关系

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Comparisons--Inequalities"
%%%
不等关系的判定过程在逻辑中是不透明常量。
它们只能借助 {name}`Lean.ofReduceBool` 公理来使用，例如通过 {tactic}`native_decide` 策略。

{zhdocstring Float.le Manual.ZhDocString.Ch19Ch20.G2.c089}

{zhdocstring Float32.le Manual.ZhDocString.Ch19Ch20.G2.c090}

{zhdocstring Float.lt Manual.ZhDocString.Ch19Ch20.G2.c091}

{zhdocstring Float32.lt Manual.ZhDocString.Ch19Ch20.G2.c092}

{zhdocstring Float.decLe Manual.ZhDocString.Ch19Ch20.G2.c093}

{zhdocstring Float32.decLe Manual.ZhDocString.Ch19Ch20.G2.c094}

{zhdocstring Float.decLt Manual.ZhDocString.Ch19Ch20.G2.c095}

{zhdocstring Float32.decLt Manual.ZhDocString.Ch19Ch20.G2.c096}

## 算术

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Arithmetic"
%%%
浮点值上的算术运算通常通过 {inst}`Add Float`、{inst}`Sub Float`、{inst}`Mul Float`、{inst}`Div Float` 和 {inst}`HomogeneousPow Float` 实例来调用，{name}`Float32` 也有对应实例。

{zhdocstring Float.add Manual.ZhDocString.Ch19Ch20.G2.c097}

{zhdocstring Float32.add Manual.ZhDocString.Ch19Ch20.G2.c098}

{zhdocstring Float.sub Manual.ZhDocString.Ch19Ch20.G2.c099}

{zhdocstring Float32.sub Manual.ZhDocString.Ch19Ch20.G2.c100}

{zhdocstring Float.mul Manual.ZhDocString.Ch19Ch20.G2.c101}

{zhdocstring Float32.mul Manual.ZhDocString.Ch19Ch20.G2.c102}

{zhdocstring Float.div Manual.ZhDocString.Ch19Ch20.G2.c103}

{zhdocstring Float32.div Manual.ZhDocString.Ch19Ch20.G2.c104}

{zhdocstring Float.pow Manual.ZhDocString.Ch19Ch20.G2.c105}

{zhdocstring Float32.pow Manual.ZhDocString.Ch19Ch20.G2.c106}

{zhdocstring Float.exp Manual.ZhDocString.Ch19Ch20.G2.c107}

{zhdocstring Float32.exp Manual.ZhDocString.Ch19Ch20.G2.c108}

{zhdocstring Float.exp2 Manual.ZhDocString.Ch19Ch20.G2.c109}

{zhdocstring Float32.exp2 Manual.ZhDocString.Ch19Ch20.G2.c110}

### 根

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Arithmetic--Roots"
%%%
对负数计算平方根会得到 `NaN`。

{zhdocstring Float.sqrt Manual.ZhDocString.Ch19Ch20.G2.c111}

{zhdocstring Float32.sqrt Manual.ZhDocString.Ch19Ch20.G2.c112}

{zhdocstring Float.cbrt Manual.ZhDocString.Ch19Ch20.G2.c113}

{zhdocstring Float32.cbrt Manual.ZhDocString.Ch19Ch20.G2.c114}

## 对数

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Logarithms"
%%%
{zhdocstring Float.log Manual.ZhDocString.Ch19Ch20.G2.c115}

{zhdocstring Float32.log Manual.ZhDocString.Ch19Ch20.G2.c116}

{zhdocstring Float.log10 Manual.ZhDocString.Ch19Ch20.G2.c117}

{zhdocstring Float32.log10 Manual.ZhDocString.Ch19Ch20.G2.c118}

{zhdocstring Float.log2 Manual.ZhDocString.Ch19Ch20.G2.c119}

{zhdocstring Float32.log2 Manual.ZhDocString.Ch19Ch20.G2.c120}

## 缩放

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Scaling"
%%%
{zhdocstring Float.scaleB Manual.ZhDocString.Ch19Ch20.G2.c121}

{zhdocstring Float32.scaleB Manual.ZhDocString.Ch19Ch20.G2.c122}

## 取整

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Rounding"
%%%
{zhdocstring Float.round Manual.ZhDocString.Ch19Ch20.G2.c123}

{zhdocstring Float32.round Manual.ZhDocString.Ch19Ch20.G2.c124}

{zhdocstring Float.floor Manual.ZhDocString.Ch19Ch20.G2.c125}

{zhdocstring Float32.floor Manual.ZhDocString.Ch19Ch20.G2.c126}

{zhdocstring Float.ceil Manual.ZhDocString.Ch19Ch20.G2.c127}

{zhdocstring Float32.ceil Manual.ZhDocString.Ch19Ch20.G2.c128}

## 三角函数

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry"
%%%
### 正弦

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Sine"
%%%
{zhdocstring Float.sin Manual.ZhDocString.Ch19Ch20.G2.c129}

{zhdocstring Float32.sin Manual.ZhDocString.Ch19Ch20.G2.c130}

{zhdocstring Float.sinh Manual.ZhDocString.Ch19Ch20.G2.c131}

{zhdocstring Float32.sinh Manual.ZhDocString.Ch19Ch20.G2.c132}

{zhdocstring Float.asin Manual.ZhDocString.Ch19Ch20.G2.c133}

{zhdocstring Float32.asin Manual.ZhDocString.Ch19Ch20.G2.c134}

{zhdocstring Float.asinh Manual.ZhDocString.Ch19Ch20.G2.c135}

{zhdocstring Float32.asinh Manual.ZhDocString.Ch19Ch20.G2.c136}

### 余弦

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Cosine"
%%%
{zhdocstring Float.cos Manual.ZhDocString.Ch19Ch20.G2.c137}

{zhdocstring Float32.cos Manual.ZhDocString.Ch19Ch20.G2.c138}

{zhdocstring Float.cosh Manual.ZhDocString.Ch19Ch20.G2.c139}

{zhdocstring Float32.cosh Manual.ZhDocString.Ch19Ch20.G2.c140}

{zhdocstring Float.acos Manual.ZhDocString.Ch19Ch20.G2.c141}

{zhdocstring Float32.acos Manual.ZhDocString.Ch19Ch20.G2.c142}

{zhdocstring Float.acosh Manual.ZhDocString.Ch19Ch20.G2.c143}

{zhdocstring Float32.acosh Manual.ZhDocString.Ch19Ch20.G2.c144}

### 正切

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Trigonometry--Tangent"
%%%
{zhdocstring Float.tan Manual.ZhDocString.Ch19Ch20.G2.c145}

{zhdocstring Float32.tan Manual.ZhDocString.Ch19Ch20.G2.c146}

{zhdocstring Float.tanh Manual.ZhDocString.Ch19Ch20.G2.c147}

{zhdocstring Float32.tanh Manual.ZhDocString.Ch19Ch20.G2.c148}

{zhdocstring Float.atan Manual.ZhDocString.Ch19Ch20.G2.c149}

{zhdocstring Float32.atan Manual.ZhDocString.Ch19Ch20.G2.c150}

{zhdocstring Float.atanh Manual.ZhDocString.Ch19Ch20.G2.c151}

{zhdocstring Float32.atanh Manual.ZhDocString.Ch19Ch20.G2.c152}

{zhdocstring Float.atan2 Manual.ZhDocString.Ch19Ch20.G2.c153}

{zhdocstring Float32.atan2 Manual.ZhDocString.Ch19Ch20.G2.c154}

## 取负与绝对值

%%%
tag := "Lean-__________________--Basic-Types--Floating-Point-Numbers--API-Reference--Negation-and-Absolute-Value"
%%%
{zhdocstring Float.abs Manual.ZhDocString.Ch19Ch20.G2.c155}

{zhdocstring Float32.abs Manual.ZhDocString.Ch19Ch20.G2.c156}

{zhdocstring Float.neg Manual.ZhDocString.Ch19Ch20.G2.c157}

{zhdocstring Float32.neg Manual.ZhDocString.Ch19Ch20.G2.c158}
