/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G2

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v

/--
64 位浮点数。

`Float` 对应 IEEE 754 的 *binary64* 格式（C 中的 `double` 或 Rust 中的 `f64`）。
浮点数以有限形式表示实数的一个子集，并扩充了额外的“哨兵”值，用于表示未定义结果、无穷结果以及彼此分离的正零和负零。浮点算术会把结果舍入到可表示的数，从而近似实数上的相应运算，并传播错误值与无穷值。

浮点数包括[次正规数](https://en.wikipedia.org/wiki/Subnormal_number)。
其特殊值包括：
 * `NaN`，表示一类“非数”值，由零除以零等运算产生；以及
 * `Inf` 和 `-Inf`，分别表示正无穷与负无穷，由非零值除以零产生。

与其他底层类型一样，Lean 编译器会特殊处理 `Float`，使其对应 C 的 `double` 类型。从 Lean 逻辑的角度看，`Float` 等价于 `Float.Model`（通过函数 `Float.toModel` 和 `Float.ofModel`），而后者本身是 `UInt64` 的子类型。`Float` 上的一些运算根据其 `Float.Model` 对应项定义，另一些运算则对 Lean 内核不透明。
-/
structure c001 where
  ofModel ::
  /--
把 `Float` 转换为 `Float.Model`。
-/
  toModel : Float.Model

/--
从 `Float.Model` 构造 `Float`。
-/
add_decl_doc c001.ofModel

/--
32 位浮点数。

`Float32` 对应 IEEE 754 的 *binary32* 格式（C 中的 `float` 或 Rust 中的 `f32`）。
浮点数以有限形式表示实数的一个子集，并扩充了额外的“哨兵”值，用于表示未定义结果、无穷结果以及彼此分离的正零和负零。浮点算术会把结果舍入到可表示的数，从而近似实数上的相应运算，并传播错误值与无穷值。

浮点数包括[次正规数](https://en.wikipedia.org/wiki/Subnormal_number)。
其特殊值包括：
 * `NaN`，表示一类“非数”值，由零除以零等运算产生；以及
 * `Inf` 和 `-Inf`，分别表示正无穷与负无穷，由非零值除以零产生。

与其他底层类型一样，Lean 编译器会特殊处理 `Float32`，使其对应 C 的 `float` 类型。从 Lean 逻辑的角度看，`Float32` 等价于 `Float32.Model`（通过函数 `Float32.toModel` 和 `Float32.ofModel`），而后者本身是 `UInt32` 的子类型。`Float32` 上的一些运算根据其 `Float32.Model` 对应项定义，另一些运算则对 Lean 内核不透明。
-/
structure c002 where
  ofModel ::
  /--
把 `Float32` 转换为 `Float32.Model`。
-/
  toModel : Float32.Model

/--
从 `Float32.Model` 构造 `Float32`。
-/
add_decl_doc c002.ofModel

/--
`Float` 类型的逻辑模型。

它定义为 `UInt64` 的一种类型，并附加限制：编码 `NaN` 的位模式必须恰好是选定的规范 `NaN`。

大多数 `Float.Model` 函数会先把 `Float.Model` 解包为归纳类型 `UnpackedFloat`，在那里执行运算，然后把结果重新打包成 `Float.Model`。

本开发并不以成为通用浮点数库的基础为目标，也不打算直接为它编写任何引理。希望获得浮点数库的用户应完全独立地开发这样的库；希望证明涉及 `Float` 的程序性质的用户，则应证明此处定义的运算等价于独立库中定义的运算，再把该库的引理转移到 `Float` 和 `Float32` 类型上。
-/
structure c003 where
  /--
`Float.Model` 的底层位模式。
-/
  toBits : UInt64
  /--
底层位模式按照 IEEE `binary64` 格式是有效的。
-/
  valid : Float.Model.Format.binary64.Valid toBits.toBitVec

/--
`Float32` 类型的逻辑模型。

它定义为 `UInt32` 的一种类型，并附加限制：编码 `NaN` 的位模式必须恰好是选定的规范 `NaN`。

大多数 `Float32.Model` 函数会先把 `Float32.Model` 解包为归纳类型 `UnpackedFloat`，在那里执行运算，然后把结果重新打包成 `Float32.Model`。

本开发并不以成为通用浮点数库的基础为目标，也不打算直接为它编写任何引理。希望获得浮点数库的用户应完全独立地开发这样的库；希望证明涉及 `Float32` 的程序性质的用户，则应证明此处定义的运算等价于独立库中定义的运算，再把该库的引理转移到 `Float` 和 `Float32` 类型上。
-/
structure c004 where
  /--
`Float32.Model` 的底层位模式。
-/
  toBits : UInt32
  /--
底层位模式按照 IEEE `binary32` 格式是有效的。
-/
  valid : Float.Model.Format.binary32.Valid toBits.toBitVec

/--
把 `UnpackedFloat` 打包为相应的 `Float.Model`。
只有当该浮点数已经按 `Format.binary64` 格式正确舍入时，此运算的结果才有意义。
-/
def c005 := @_root_.Float.Model.pack

/--
把 `UnpackedFloat` 打包为相应的 `Float32.Model`。
只有当该浮点数已经按 `Format.binary32` 格式正确舍入时，此运算的结果才有意义。
-/
def c006 := @_root_.Float32.Model.pack

/--
把 `Float.Model` 解包为相应的 `UnpackedFloat`。
-/
def c007 := @_root_.Float.Model.unpack

/--
把 `Float32.Model` 解包为相应的 `UnpackedFloat`。
-/
def c008 := @_root_.Float32.Model.unpack

/--
一种表示浮点数的归纳类型，其构造子分别表示带符号无穷、不带载荷的非数、带符号零，以及由符号、正自然数尾数和整数指数构成的有限浮点数。

有限浮点数在此格式中没有唯一表示：尾数乘以二、指数减一后，所得有限浮点数仍表示同一个有理数。

对于给定的 `Format`，若指数等于该格式规定的 `targetExponent`，就称解包后的浮点数处于规范形式。`UnpackedFloat` 上的某些运算（例如 `compare`）假定所有输入都对同一格式处于规范形式。

请注意，对给定格式处于规范形式的解包浮点数未必能由该格式实际表示，因为指数可能太大而无法容纳。此时，`pack` 函数会使浮点数上溢为无穷。

此类型仅用于支持 `Float.Model` 和 `Float32.Model`。本开发并不以成为通用浮点数库的基础为目标，也不打算直接为它编写任何引理。希望获得浮点数库的用户应完全独立地开发这样的库；希望证明涉及 `Float` 的程序性质的用户，则应证明此处定义的运算等价于独立库中定义的运算，再把该库的引理转移到 `Float` 和 `Float32` 类型上。
-/
inductive c009 where
  /--
带符号无穷。
-/
  | infinity : Float.Model.UnpackedFloat.Sign → c009
  /--
非数。此格式中的 NaN 不附带载荷。
-/
  | notANumber : c009
  /--
带符号零。
-/
  | zero : Float.Model.UnpackedFloat.Sign → c009
  /--
由符号位、正自然数尾数和指数构成的有限浮点数。
-/
  | finite : Float.Model.UnpackedFloat.Sign → (mantissa : Nat) → Int → 0 < mantissa → c009

/--
计算两个浮点数之和，并按照给定规约舍入结果。
-/
def c010 := @_root_.Float.Model.UnpackedFloat.add

/--
计算两个浮点数之差，并按照给定规约舍入结果。
-/
def c011 := @_root_.Float.Model.UnpackedFloat.sub

/--
计算两个浮点数之积，并按照给定规约舍入结果。
-/
def c012 := @_root_.Float.Model.UnpackedFloat.mul

/--
计算两个浮点数之商，并按照给定规约舍入结果。
-/
def c013 := @_root_.Float.Model.UnpackedFloat.div

/--
计算浮点数的平方根，并按照给定规约舍入结果。
-/
def c014 := @_root_.Float.Model.UnpackedFloat.sqrt

/--
对给定浮点数取负。
-/
def c015 := @_root_.Float.Model.UnpackedFloat.neg

/--
返回具有正号的给定浮点数。
-/
def c016 := @_root_.Float.Model.UnpackedFloat.abs

/--
返回 `true`，当且仅当该浮点数为 `NaN`。
-/
def c017 := @_root_.Float.Model.UnpackedFloat.isNaN

/--
若该浮点数为正无穷或负无穷，则返回 `true`。
-/
def c018 := @_root_.Float.Model.UnpackedFloat.isInf

/--
返回 `true`，当该浮点数表示实数，即它既非无穷也非 `NaN`。
-/
def c019 := @_root_.Float.Model.UnpackedFloat.isFinite

/--
按照 IEEE 规定计算两个浮点数的次序。返回 `Option Ordering`，以体现 `NaN` 与任何值都不可比较这一事实。正零与负零也视为相等。

重要：仅当两个输入都对同一格式处于规范形式时，此运算才能正确工作（详情参见 `UnpackedFloat` 的文档字符串）。
-/
def c020 := @_root_.Float.Model.UnpackedFloat.compare

/--
按照 IEEE 规则判断 `a` 是否等于 `b`。

该关系不具自反性。
-/
def c021 := @_root_.Float.Model.UnpackedFloat.beq

/--
按照 IEEE 规则判断 `a` 是否小于 `b`。

这不是全序。
-/
def c022 := @_root_.Float.Model.UnpackedFloat.lt

/--
按照 IEEE 规则判断 `a` 是否小于或等于 `b`。

这不是全序，并且 `≤` 不具自反性。
-/
def c023 := @_root_.Float.Model.UnpackedFloat.le

/--
把 `Nat` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c024 := @_root_.Float.Model.UnpackedFloat.ofNat

/--
把 `Int` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c025 := @_root_.Float.Model.UnpackedFloat.ofInt

/--
计算 `m * 10 ^ e`。
-/
def c026 := @_root_.Float.Model.UnpackedFloat.ofScientific

/--
把 `UnpackedFloat` 转换为 `Int8`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c027 := @_root_.Float.Model.UnpackedFloat.toInt8

/--
把 `Int8` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c028 := @_root_.Float.Model.UnpackedFloat.ofInt8

/--
把 `UnpackedFloat` 转换为 `Int16`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c029 := @_root_.Float.Model.UnpackedFloat.toInt16

/--
把 `Int16` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c030 := @_root_.Float.Model.UnpackedFloat.ofInt16

/--
把 `UnpackedFloat` 转换为 `Int32`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c031 := @_root_.Float.Model.UnpackedFloat.toInt32

/--
把 `Int32` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c032 := @_root_.Float.Model.UnpackedFloat.ofInt32

/--
把 `UnpackedFloat` 转换为 `Int64`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c033 := @_root_.Float.Model.UnpackedFloat.toInt64

/--
把 `Int64` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c034 := @_root_.Float.Model.UnpackedFloat.ofInt64

/--
把 `UnpackedFloat` 转换为 `ISize`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c035 := @_root_.Float.Model.UnpackedFloat.toISize

/--
把 `ISize` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c036 := @_root_.Float.Model.UnpackedFloat.ofISize

/--
把 `UnpackedFloat` 转换为 `UInt8`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c037 := @_root_.Float.Model.UnpackedFloat.toUInt8

/--
把 `UInt8` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c038 := @_root_.Float.Model.UnpackedFloat.ofUInt8

/--
把 `UnpackedFloat` 转换为 `UInt16`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c039 := @_root_.Float.Model.UnpackedFloat.toUInt16

/--
把 `UInt16` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c040 := @_root_.Float.Model.UnpackedFloat.ofUInt16

/--
把 `UnpackedFloat` 转换为 `UInt32`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c041 := @_root_.Float.Model.UnpackedFloat.toUInt32

/--
把 `UInt32` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c042 := @_root_.Float.Model.UnpackedFloat.ofUInt32

/--
把 `UnpackedFloat` 转换为 `UInt64`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c043 := @_root_.Float.Model.UnpackedFloat.toUInt64

/--
把 `UInt64` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c044 := @_root_.Float.Model.UnpackedFloat.ofUInt64

/--
把 `UnpackedFloat` 转换为 `USize`：截去小数点后的部分，把 `NaN` 转换为 `0`，并将越界值和无穷值钳制到范围内。
-/
def c045 := @_root_.Float.Model.UnpackedFloat.toUSize

/--
把 `USize` 转换为 `UnpackedFloat`；输入为零时返回正零。
-/
def c046 := @_root_.Float.Model.UnpackedFloat.ofUSize

/--
检查浮点数是否为正无穷或负无穷，而不是有限数或 `NaN`。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 运算符 `isinf`。
-/
def c047 := @_root_.Float.isInf

/--
检查浮点数是否为正无穷或负无穷，而不是有限数或 `NaN`。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 运算符 `isinf`。
-/
def c048 := @_root_.Float32.isInf

/--
检查浮点数是否为 `NaN`（“非数”）值。

`NaN` 值由原本可能成为错误的运算产生，例如零除以零。

此函数返回 `true` 当且仅当输入在命题上等于 `Float.nan`。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 运算符 `isnan`。
-/
def c049 := @_root_.Float.isNaN

/--
检查浮点数是否为 `NaN`（“非数”）值。

`NaN` 值由原本可能成为错误的运算产生，例如零除以零。

此函数返回 `true` 当且仅当输入在命题上等于 `Float32.nan`。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 运算符 `isnan`。
-/
def c050 := @_root_.Float32.isNaN

/--
检查浮点数是否有限，即它是正规数、次正规数或零，而不是无穷或 `NaN`。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 运算符 `isfinite`。
-/
def c051 := @_root_.Float.isFinite

/--
检查浮点数是否有限，即它是正规数、次正规数或零，而不是无穷或 `NaN`。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 运算符 `isfinite`。
-/
def c052 := @_root_.Float32.isFinite

/--
逐位转换为 `UInt64`。把 `Float` 解释为 `UInt64`，忽略数值，仅将 `Float` 的位模式视为 `UInt64`。

在所有受支持平台上，`Float` 与 `UInt64` 的字节序相同。IEEE 754 非常精确地规定了浮点数的位布局。

此函数不同于 `Float.toUInt64`；后者试图保持数值，而不是重新解释位模式。
-/
def c053 := @_root_.Float.toBits

/--
逐位转换为 `UInt32`。把 `Float32` 解释为 `UInt32`，忽略数值，仅将 `Float32` 的位模式视为 `UInt32`。

在所有受支持平台上，`Float32` 与 `UInt32` 的字节序相同。IEEE 754 非常精确地规定了浮点数的位布局。

此函数不同于 `Float.toUInt32`；后者试图保持数值，而不是重新解释位模式。
-/
def c054 := @_root_.Float32.toBits

/--
从 `UInt64` 逐位转换。把 `UInt64` 解释为 `Float`，忽略数值，仅将 `UInt64` 的位模式视为 `Float`。

在所有受支持平台上，`Float` 与 `UInt64` 的字节序相同。IEEE 754 非常精确地规定了浮点数的位布局。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c055 := @_root_.Float.ofBits

/--
从 `UInt32` 逐位转换。把 `UInt32` 解释为 `Float32`，忽略数值，仅将 `UInt32` 的位模式视为 `Float32`。

在所有受支持平台上，`Float32` 与 `UInt32` 的字节序相同。IEEE 754 非常精确地规定了浮点数的位布局。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c056 := @_root_.Float32.ofBits

/--
把 64 位浮点数转换为 32 位浮点数。
这可能损失精度。

此函数不在内核中规约。
-/
def c057 := @_root_.Float.toFloat32

/--
把 32 位浮点数转换为 64 位浮点数。

此函数不在内核中规约。
-/
def c058 := @_root_.Float32.toFloat

/--
把浮点数转换为字符串。

此函数不在内核中规约。
-/
def c059 := @_root_.Float.toString

/--
把浮点数转换为字符串。

此函数不在内核中规约。
-/
def c060 := @_root_.Float32.toString

/--
把浮点数转换为8 位无符号整数。

若给定的 `Float` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt8` 的范围。返回 `0`，当 `Float` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt8` 值（即 `UInt8.size - 1`）。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c061 := @_root_.Float.toUInt8

/--
把浮点数向零舍入，截断为最接近的8 位有符号整数。

若 `Float` 大于 `Int8` 的最大值（包括 `Inf`），则返回 `Int8` 的最大值（即 `Int8.maxValue`）。若它小于 `Int8` 的最小值（包括 `-Inf`），则返回 `Int8` 的最小值（即 `Int8.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c062 := @_root_.Float.toInt8

/--
把浮点数转换为8 位无符号整数。

若给定的 `Float32` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt8` 的范围。返回 `0`，当 `Float32` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt8` 值（即 `UInt8.size - 1`）。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c063 := @_root_.Float32.toUInt8

/--
把浮点数向零舍入，截断为最接近的8 位有符号整数。

若 `Float` 大于 `Int8` 的最大值（包括 `Inf`），则返回 `Int8` 的最大值（即 `Int8.maxValue`）。若它小于 `Int8` 的最小值（包括 `-Inf`），则返回 `Int8` 的最小值（即 `Int8.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c064 := @_root_.Float32.toInt8

/--
把浮点数转换为16 位无符号整数。

若给定的 `Float` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt16` 的范围。返回 `0`，当 `Float` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt16` 值（即 `UInt16.size - 1`）。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c065 := @_root_.Float.toUInt16

/--
把浮点数向零舍入，截断为最接近的16 位有符号整数。

若 `Float` 大于 `Int16` 的最大值（包括 `Inf`），则返回 `Int16` 的最大值（即 `Int16.maxValue`）。若它小于 `Int16` 的最小值（包括 `-Inf`），则返回 `Int16` 的最小值（即 `Int16.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c066 := @_root_.Float.toInt16

/--
把浮点数转换为16 位无符号整数。

若给定的 `Float32` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt16` 的范围。返回 `0`，当 `Float32` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt16` 值（即 `UInt16.size - 1`）。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c067 := @_root_.Float32.toUInt16

/--
把浮点数向零舍入，截断为最接近的16 位有符号整数。

若 `Float` 大于 `Int16` 的最大值（包括 `Inf`），则返回 `Int16` 的最大值（即 `Int16.maxValue`）。若它小于 `Int16` 的最小值（包括 `-Inf`），则返回 `Int16` 的最小值（即 `Int16.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c068 := @_root_.Float32.toInt16

/--
把浮点数转换为32 位无符号整数。

若给定的 `Float` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt32` 的范围。返回 `0`，当 `Float` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt32` 值（即 `UInt32.size - 1`）。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c069 := @_root_.Float.toUInt32

/--
把浮点数转换为32 位无符号整数。

若给定的 `Float32` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt32` 的范围。返回 `0`，当 `Float32` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt32` 值（即 `UInt32.size - 1`）。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c070 := @_root_.Float32.toUInt32

/--
把浮点数向零舍入，截断为最接近的32 位有符号整数。

若 `Float` 大于 `Int32` 的最大值（包括 `Inf`），则返回 `Int32` 的最大值（即 `Int32.maxValue`）。若它小于 `Int32` 的最小值（包括 `-Inf`），则返回 `Int32` 的最小值（即 `Int32.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c071 := @_root_.Float.toInt32

/--
把浮点数向零舍入，截断为最接近的32 位有符号整数。

若 `Float` 大于 `Int32` 的最大值（包括 `Inf`），则返回 `Int32` 的最大值（即 `Int32.maxValue`）。若它小于 `Int32` 的最小值（包括 `-Inf`），则返回 `Int32` 的最小值（即 `Int32.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c072 := @_root_.Float32.toInt32

/--
把浮点数转换为64 位无符号整数。

若给定的 `Float` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt64` 的范围。返回 `0`，当 `Float` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt64` 值（即 `UInt64.size - 1`）。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c073 := @_root_.Float.toUInt64

/--
把浮点数向零舍入，截断为最接近的64 位有符号整数。

若 `Float` 大于 `Int64` 的最大值（包括 `Inf`），则返回 `Int64` 的最大值（即 `Int64.maxValue`）。若它小于 `Int64` 的最小值（包括 `-Inf`），则返回 `Int64` 的最小值（即 `Int64.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c074 := @_root_.Float.toInt64

/--
把浮点数转换为64 位无符号整数。

若给定的 `Float32` 非负，则向下舍入，把值截断为正整数，并钳制到 `UInt64` 的范围。返回 `0`，当 `Float32` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `UInt64` 值（即 `UInt64.size - 1`）。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c075 := @_root_.Float32.toUInt64

/--
把浮点数向零舍入，截断为最接近的64 位有符号整数。

若 `Float` 大于 `Int64` 的最大值（包括 `Inf`），则返回 `Int64` 的最大值（即 `Int64.maxValue`）。若它小于 `Int64` 的最小值（包括 `-Inf`），则返回 `Int64` 的最小值（即 `Int64.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c076 := @_root_.Float32.toInt64

/--
把浮点数转换为机器字长无符号整数。

若给定的 `Float` 非负，则向下舍入，把值截断为正整数，并钳制到 `USize` 的范围。返回 `0`，当 `Float` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `USize` 值（即 `USize.size - 1`）。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c077 := @_root_.Float.toUSize

/--
把浮点数转换为机器字长无符号整数。

若给定的 `Float32` 非负，则向下舍入，把值截断为正整数，并钳制到 `USize` 的范围。返回 `0`，当 `Float32` 为负数或 `NaN`；若浮点数大于该最大值，则返回最大的 `USize` 值（即 `USize.size - 1`）。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c078 := @_root_.Float32.toUSize

/--
把浮点数向零舍入，截断为最接近的机器字长有符号整数。

若 `Float` 大于 `ISize` 的最大值（包括 `Inf`），则返回 `ISize` 的最大值（即 `ISize.maxValue`）。若它小于 `ISize` 的最小值（包括 `-Inf`），则返回 `ISize` 的最小值（即 `ISize.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float.Model` 的逻辑模型。
-/
def c079 := @_root_.Float.toISize

/--
把浮点数向零舍入，截断为最接近的机器字长有符号整数。

若 `Float` 大于 `ISize` 的最大值（包括 `Inf`），则返回 `ISize` 的最大值（即 `ISize.maxValue`）。若它小于 `ISize` 的最小值（包括 `-Inf`），则返回 `ISize` 的最小值（即 `ISize.minValue`）。若它为 `NaN`，则返回 `0`。

此函数具有基于 `Float32.Model` 的逻辑模型。
-/
def c080 := @_root_.Float32.toISize

/--
把整数转换为最接近的 64 位浮点数；若超出 `Float` 的范围，则转换为正无穷或负无穷浮点值。
-/
def c081 := @_root_.Float.ofInt

/--
把整数转换为最接近的 32 位浮点数；若超出 `Float32` 的范围，则转换为正无穷或负无穷浮点值。
-/
def c082 := @_root_.Float32.ofInt

/--
把自然数转换为最接近的 64 位浮点数；若超出 `Float` 的范围，则转换为无穷浮点值。
-/
def c083 := @_root_.Float.ofNat

/--
把自然数转换为最接近的 32 位浮点数；若超出 `Float32` 的范围，则转换为无穷浮点值。
-/
def c084 := @_root_.Float32.ofNat

/--
把给定浮点数 `x` 拆分为有效数/指数对 `(s, i)`，满足 `x = s * 2^i`，其中 `s ∈ (-1;-0.5] ∪ [0.5; 1)`。若 `x` 不是有限数，则返回未定义值。

此函数不在内核中规约。编译后代码由 C 函数 `frexp` 实现。
-/
def c085 := @_root_.Float.frExp

/--
把给定浮点数 `x` 拆分为有效数/指数对 `(s, i)`，满足 `x = s * 2^i`，其中 `s ∈ (-1;-0.5] ∪ [0.5; 1)`。若 `x` 不是有限数，则返回未定义值。

此函数不在内核中规约。编译后代码由 C 函数 `frexp` 实现。
-/
def c086 := @_root_.Float32.frExp

/--
按照 IEEE 754 检查两个浮点数是否相等。

浮点相等与命题等式并不对应。特别地，由于 `NaN != NaN`，它不具自反性；又由于 `0.0 == -0.0` 但 `1.0 / 0.0 != 1.0 / -0.0`，它也不是同余关系。

此函数不在内核中规约，并被编译为 C 相等运算符。
-/
def c087 := @_root_.Float.beq

/--
按照 IEEE 754 检查两个浮点数是否相等。

浮点相等与命题等式并不对应。特别地，由于 `NaN != NaN`，它不具自反性；又由于 `0.0 == -0.0` 但 `1.0 / 0.0 != 1.0 / -0.0`，它也不是同余关系。

此函数不在内核中规约，并被编译为 C 相等运算符。
-/
def c088 := @_root_.Float32.beq

/--
浮点数的非严格不等关系。通常通过 `≤` 运算符使用。
-/
def c089 := @_root_.Float.le

/--
浮点数的非严格不等关系。通常通过 `≤` 运算符使用。
-/
def c090 := @_root_.Float32.le

/--
浮点数的严格不等关系。通常通过 `<` 运算符使用。
-/
def c091 := @_root_.Float.lt

/--
浮点数的严格不等关系。通常通过 `<` 运算符使用。
-/
def c092 := @_root_.Float32.lt

/--
比较两个浮点数是否满足非严格不等关系。

此函数不在内核中规约，并被编译为 C 不等运算符。
-/
def c093 := @_root_.Float.decLe

/--
比较两个浮点数是否满足非严格不等关系。

此函数不在内核中规约，并被编译为 C 不等运算符。
-/
def c094 := @_root_.Float32.decLe

/--
比较两个浮点数是否满足严格不等关系。

此函数不在内核中规约，并被编译为 C 不等运算符。
-/
def c095 := @_root_.Float.decLt

/--
比较两个浮点数是否满足严格不等关系。

此函数不在内核中规约，并被编译为 C 不等运算符。
-/
def c096 := @_root_.Float32.decLt

/--
按照 IEEE 754 将两个 64 位浮点数相加。通常通过 `+` 运算符使用。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 加法运算符。
-/
def c097 := @_root_.Float.add

/--
按照 IEEE 754 将两个 32 位浮点数相加。通常通过 `+` 运算符使用。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 加法运算符。
-/
def c098 := @_root_.Float32.add

/--
按照 IEEE 754 将两个 64 位浮点数相减。通常通过 `-` 运算符使用。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 减法运算符。
-/
def c099 := @_root_.Float.sub

/--
按照 IEEE 754 将两个 32 位浮点数相减。通常通过 `-` 运算符使用。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 减法运算符。
-/
def c100 := @_root_.Float32.sub

/--
按照 IEEE 754 将两个 64 位浮点数相乘。通常通过 `*` 运算符使用。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 乘法运算符。
-/
def c101 := @_root_.Float.mul

/--
按照 IEEE 754 将两个 32 位浮点数相乘。通常通过 `*` 运算符使用。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 乘法运算符。
-/
def c102 := @_root_.Float32.mul

/--
按照 IEEE 754 将两个 64 位浮点数相除。通常通过 `/` 运算符使用。

在 Lean 中，除以零通常得到零；但对 `Float` 而言，结果会是 `Inf`、`-Inf` 或 `NaN`。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 除法运算符。
-/
def c103 := @_root_.Float.div

/--
按照 IEEE 754 将两个 32 位浮点数相除。通常通过 `/` 运算符使用。

在 Lean 中，除以零通常得到零；但对 `Float32` 而言，结果会是 `Inf`、`-Inf` 或 `NaN`。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 除法运算符。
-/
def c104 := @_root_.Float32.div

/--
把一个浮点数提升到另一个浮点数次幂。通常通过 `^` 运算符使用。

此函数不在内核中规约。编译后代码由 C 函数 `pow` 实现。
-/
def c105 := @_root_.Float.pow

/--
把一个浮点数提升到另一个浮点数次幂。通常通过 `^` 运算符使用。

此函数不在内核中规约。编译后代码由 C 函数 `powf` 实现。
-/
def c106 := @_root_.Float32.pow

/--
计算浮点数的指数 `e^x`。

此函数不在内核中规约。编译后代码由 C 函数 `exp` 实现。
-/
def c107 := @_root_.Float.exp

/--
计算浮点数的指数 `e^x`。

此函数不在内核中规约。编译后代码由 C 函数 `expf` 实现。
-/
def c108 := @_root_.Float32.exp

/--
计算浮点数以 2 为底的指数 `2^x`。

此函数不在内核中规约。编译后代码由 C 函数 `exp2` 实现。
-/
def c109 := @_root_.Float.exp2

/--
计算浮点数以 2 为底的指数 `2^x`。

此函数不在内核中规约。编译后代码由 C 函数 `exp2f` 实现。
-/
def c110 := @_root_.Float32.exp2

/--
计算浮点数的平方根。

此函数具有基于 `Float.Model` 的逻辑模型。编译后代码由 C 函数 `sqrt` 实现。
-/
def c111 := @_root_.Float.sqrt

/--
计算浮点数的平方根。

此函数具有基于 `Float32.Model` 的逻辑模型。编译后代码由 C 函数 `sqrtf` 实现。
-/
def c112 := @_root_.Float32.sqrt

/--
计算浮点数的立方根。

此函数不在内核中规约。编译后代码由 C 函数 `cbrt` 实现。
-/
def c113 := @_root_.Float.cbrt

/--
计算浮点数的立方根。

此函数不在内核中规约。编译后代码由 C 函数 `cbrtf` 实现。
-/
def c114 := @_root_.Float32.cbrt

/--
计算浮点数的自然对数 `ln x`。

此函数不在内核中规约。编译后代码由 C 函数 `log` 实现。
-/
def c115 := @_root_.Float.log

/--
计算浮点数的自然对数 `ln x`。

此函数不在内核中规约。编译后代码由 C 函数 `logf` 实现。
-/
def c116 := @_root_.Float32.log

/--
计算浮点数以 10 为底的对数。

此函数不在内核中规约。编译后代码由 C 函数 `log10` 实现。
-/
def c117 := @_root_.Float.log10

/--
计算浮点数以 10 为底的对数。

此函数不在内核中规约。编译后代码由 C 函数 `log10f` 实现。
-/
def c118 := @_root_.Float32.log10

/--
计算浮点数以 2 为底的对数。

此函数不在内核中规约。编译后代码由 C 函数 `log2` 实现。
-/
def c119 := @_root_.Float.log2

/--
计算浮点数以 2 为底的对数。

此函数不在内核中规约。编译后代码由 C 函数 `log2f` 实现。
-/
def c120 := @_root_.Float32.log2

/--
高效计算 `x * 2^i`。

此函数不在内核中规约。
-/
def c121 := @_root_.Float.scaleB

/--
高效计算 `x * 2^i`。

此函数不在内核中规约。
-/
def c122 := @_root_.Float32.scaleB

/--
舍入到最近的整数；恰好位于中点时，向远离零的方向舍入。

此函数不在内核中规约。编译后代码由 C 函数 `round` 实现。
-/
def c123 := @_root_.Float.round

/--
舍入到最近的整数；恰好位于中点时，向远离零的方向舍入。

此函数不在内核中规约。编译后代码由 C 函数 `roundf` 实现。
-/
def c124 := @_root_.Float32.round

/--
计算浮点数的下取整，即不大于给定数的最大整数。

此函数不在内核中规约。编译后代码由 C 函数 `floor` 实现。

示例：
 * `Float.floor 1.5 = 1`
 * `Float.floor (-1.5) = (-2)`
-/
def c125 := @_root_.Float.floor

/--
计算浮点数的下取整，即不大于给定数的最大整数。

此函数不在内核中规约。编译后代码由 C 函数 `floorf` 实现。

示例：
 * `Float32.floor 1.5 = 1`
 * `Float32.floor (-1.5) = (-2)`
-/
def c126 := @_root_.Float32.floor

/--
计算浮点数的上取整，即不小于给定数的最小整数。

此函数不在内核中规约。编译后代码由 C 函数 `ceil` 实现。

示例：
 * `Float.ceil 1.5 = 2`
 * `Float.ceil (-1.5) = (-1)`
-/
def c127 := @_root_.Float.ceil

/--
计算浮点数的上取整，即不小于给定数的最小整数。

此函数不在内核中规约。编译后代码由 C 函数 `ceilf` 实现。

示例：
 * `Float32.ceil 1.5 = 2`
 * `Float32.ceil (-1.5) = (-1)`
-/
def c128 := @_root_.Float32.ceil

/--
计算浮点数的正弦（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `sin` 实现。
-/
def c129 := @_root_.Float.sin

/--
计算浮点数的正弦（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `sinf` 实现。
-/
def c130 := @_root_.Float32.sin

/--
计算浮点数的双曲正弦。

此函数不在内核中规约。编译后代码由 C 函数 `sinh` 实现。
-/
def c131 := @_root_.Float.sinh

/--
计算浮点数的双曲正弦。

此函数不在内核中规约。编译后代码由 C 函数 `sinhf` 实现。
-/
def c132 := @_root_.Float32.sinh

/--
计算浮点数的反正弦（正弦的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `asin` 实现。
-/
def c133 := @_root_.Float.asin

/--
计算浮点数的反正弦（正弦的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `asinf` 实现。
-/
def c134 := @_root_.Float32.asin

/--
计算浮点数的反双曲正弦（双曲正弦的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `asinh` 实现。
-/
def c135 := @_root_.Float.asinh

/--
计算浮点数的反双曲正弦（双曲正弦的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `asinhf` 实现。
-/
def c136 := @_root_.Float32.asinh

/--
计算浮点数的余弦（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `cos` 实现。
-/
def c137 := @_root_.Float.cos

/--
计算浮点数的余弦（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `cosf` 实现。
-/
def c138 := @_root_.Float32.cos

/--
计算浮点数的双曲余弦。

此函数不在内核中规约。编译后代码由 C 函数 `cosh` 实现。
-/
def c139 := @_root_.Float.cosh

/--
计算浮点数的双曲余弦。

此函数不在内核中规约。编译后代码由 C 函数 `coshf` 实现。
-/
def c140 := @_root_.Float32.cosh

/--
计算浮点数的反余弦（余弦的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `acos` 实现。
-/
def c141 := @_root_.Float.acos

/--
计算浮点数的反余弦（余弦的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `acosf` 实现。
-/
def c142 := @_root_.Float32.acos

/--
计算浮点数的反双曲余弦（双曲余弦的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `acosh` 实现。
-/
def c143 := @_root_.Float.acosh

/--
计算浮点数的反双曲余弦（双曲余弦的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `acoshf` 实现。
-/
def c144 := @_root_.Float32.acosh

/--
计算浮点数的正切（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `tan` 实现。
-/
def c145 := @_root_.Float.tan

/--
计算浮点数的正切（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `tanf` 实现。
-/
def c146 := @_root_.Float32.tan

/--
计算浮点数的双曲正切。

此函数不在内核中规约。编译后代码由 C 函数 `tanh` 实现。
-/
def c147 := @_root_.Float.tanh

/--
计算浮点数的双曲正切。

此函数不在内核中规约。编译后代码由 C 函数 `tanhf` 实现。
-/
def c148 := @_root_.Float32.tanh

/--
计算浮点数的反正切（正切的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `atan` 实现。
-/
def c149 := @_root_.Float.atan

/--
计算浮点数的反正切（正切的反函数）（以弧度计）。

此函数不在内核中规约。编译后代码由 C 函数 `atanf` 实现。
-/
def c150 := @_root_.Float32.atan

/--
计算浮点数的反双曲正切（双曲正切的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `atanh` 实现。
-/
def c151 := @_root_.Float.atanh

/--
计算浮点数的反双曲正切（双曲正切的反函数）。

此函数不在内核中规约。编译后代码由 C 函数 `atanhf` 实现。
-/
def c152 := @_root_.Float32.atanh

/--
计算 `y / x` 的反正切（以弧度计），结果范围为 `-π`–`π`。实参的符号决定结果所在的象限。

此函数不在内核中规约。编译后代码由 C 函数 `atan2` 实现。
-/
def c153 := @_root_.Float.atan2

/--
计算 `y / x` 的反正切（以弧度计），结果范围为 `-π`–`π`。实参的符号决定结果所在的象限。

此函数不在内核中规约。编译后代码由 C 函数 `atan2f` 实现。
-/
def c154 := @_root_.Float32.atan2

/--
计算浮点数的绝对值。

此函数具有基于 `Float.Model` 的逻辑模型。编译后代码由 C 函数 `fabs` 实现。
-/
def c155 := @_root_.Float.abs

/--
计算浮点数的绝对值。

此函数具有基于 `Float32.Model` 的逻辑模型。编译后代码由 C 函数 `fabsf` 实现。
-/
def c156 := @_root_.Float32.abs

/--
按照 IEEE 754 对 64 位浮点数取负。通常通过前缀 `-` 运算符使用。

此函数具有基于 `Float.Model` 的逻辑模型，并被编译为 C 取负运算符。
-/
def c157 := @_root_.Float.neg

/--
按照 IEEE 754 对 32 位浮点数取负。通常通过前缀 `-` 运算符使用。

此函数具有基于 `Float32.Model` 的逻辑模型，并被编译为 C 取负运算符。
-/
def c158 := @_root_.Float32.neg

/--
`True` 是一个命题，只有一条引入规则 `True.intro : True`。
换言之，`True` 就是真的，并具有规范证明 `True.intro`。
更多信息：[命题逻辑](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive c159 : Prop where
  /--
`True` 为真，`True.intro`（更常用的是 `trivial`）就是其证明。
-/
  | intro : c159

/--
`False` 是空命题，因此没有引入规则。
它表示矛盾。`False` 的消去规则 `False.rec` 表达了从矛盾可推出任何命题这一事实。
该规则有时称为 *ex falso*（*ex falso sequitur quodlibet* 的简称），或爆炸原理。
更多信息：[命题逻辑](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive c160 : Prop

/--
`False.elim : False → C` 表示由 `False` 可推出任意所需命题 `C`。它也称为 *ex falso quodlibet*（EFQ）或爆炸原理。

目标类型实际上是 `C : Sort u`，因此它对命题和类型都适用。执行时，它类似于“不可达”指令：运行它属于**未定义行为**，但很可能打印“unreachable code”。（无论如何，必须先构造假命题的证明才能运行它，而这只能借助 `sorry` 或不可靠的公理做到。）
-/
def c161 := @_root_.False.elim

/--
`And a b`（或 `a ∧ b`）是命题的合取。它可以像一对值一样构造和解构：若 `ha : a` 且 `hb : b`，则 `⟨ha, hb⟩ : a ∧ b`；若 `h : a ∧ b`，则 `h.left : a` 且 `h.right : b`。


标识符中记法的约定：

 * 标识符中 `∧` 的推荐拼写是 `and`。
-/
structure c162 (a b : Prop) : Prop where
  intro ::
  /--
从合取中提取左合取项。若 `h : a ∧ b`，则 `h.left`（也记作 `h.1`）是 `a` 的证明。
-/
  left : a
  /--
从合取中提取右合取项。若 `h : a ∧ b`，则 `h.right`（也记作 `h.2`）是 `b` 的证明。
-/
  right : b

/--
`And.intro : a → b → a ∧ b` 是 And 运算的构造子。
-/
add_decl_doc c162.intro

/--
`And` 的非依赖消去器。
-/
def c163 := @_root_.And.elim

/--
`Or a b`（或 `a ∨ b`）是命题的析取。`Or` 有两个构造子，分别是 `Or.inl : a → a ∨ b` 和 `Or.inr : b → a ∨ b`；可使用 `match` 或 `cases` 把一个 `Or` 假设解构成两种情形。


标识符中记法的约定：

 * 标识符中 `∨` 的推荐拼写是 `or`。
-/
inductive c164 : Prop → Prop → Prop where
  /--
`Or.inl` 是向 `Or` 的“左注入”。若 `h : a`，则 `Or.inl h : a ∨ b`。
-/
  | inl : ∀ {a b : Prop}, a → c164 a b
  /--
`Or.inr` 是向 `Or` 的“右注入”。若 `h : b`，则 `Or.inr h : a ∨ b`。
-/
  | inr : ∀ {a b : Prop}, b → c164 a b

/--
当左析取项可判定时，按 `Or` 的情形构造一个非 Prop 值。
-/
def c165 := @_root_.Or.by_cases

/--
当右析取项可判定时，按 `Or` 的情形构造一个非 Prop 值。
-/
def c166 := @_root_.Or.by_cases'

/--
`Not p`（或 `¬p`）是 `p` 的否定。它定义为 `p → False`，因此若目标为 `¬p`，可使用 `intro h` 将目标变为 `h : p ⊢ False`；若已有 `hn : ¬p` 和 `h : p`，则 `hn h : False`，而 `(hn h).elim` 可证明任何命题。
更多信息：[命题逻辑](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)


标识符中记法的约定：

 * 标识符中 `¬` 的推荐拼写是 `not`。
-/
def c167 := @_root_.Not

/--
任何命题都可由两个互相矛盾的假设推出。示例：
```
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```
更多信息：[命题逻辑](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
def c168 := @_root_.absurd

/--
否定的 *ex falso*：由 `¬a` 和 `a` 可推出任何命题。它等同于交换实参后的 `absurd`，但位于 `Not` 命名空间中，因而可使用投影记法。
-/
def c169 := @_root_.Not.elim

/--
当且仅当，即逻辑双蕴含。`a ↔ b` 表示 `a` 蕴含 `b`，反之亦然。
由 `propext` 可知，这意味着 `a` 与 `b` 相等，因此任何包含 `a` 的表达式都等价于把其中 a 换成 `b` 后的对应表达式。


标识符中记法的约定：

 * 标识符中 `↔` 的推荐拼写是 `iff`。

 * 标识符中 `<->` 的推荐拼写是 `iff`（应优先使用 `↔`，而不是 `<->`）。
-/
structure c170 (a b : Prop) : Prop where
  intro ::
  /--
当且仅当的肯定前件式。若 `a ↔ b` 且 `a`，则 `b`。
-/
  mp : a → b
  /--
反向的当且仅当肯定前件式。若 `a ↔ b` 且 `b`，则 `a`。
-/
  mpr : b → a

/--
若 `a → b` 且 `b → a`，则 `a` 与 `b` 等价。
-/
add_decl_doc c170.intro

/--
`Iff` 的非依赖消去器。
-/
def c171 := @_root_.Iff.elim

/--
存在量化。若 `p : α → Prop` 是谓词，则 `∃ x : α, p x` 断言存在某个 `x`，其类型为 `α`，并且 `p x` 成立。
要创建存在性证明，可使用 `exists` 策略，或匿名构造子记法 `⟨x, h⟩`。
要解包存在量词，可使用 `cases h`，其中 `h` 是 `∃ x : α, p x` 的证明，或使用 `let ⟨x, hx⟩ := h`。

由于 Lean 具有证明无关性，任意两个存在性证明都定义相等。其后果之一是，无法仅从见证存在这一事实恢复存在量词的见证。
例如，以下代码无法编译：
```
example (h : ∃ x : Nat, x = x) : Nat :=
  let ⟨x, _⟩ := h  -- fail, because the goal is `Nat : Type`
  x
```
错误消息 `recursor 'Exists.casesOn' can only eliminate into Prop` 表示，只有当前目标也是命题时，这样做才有效：
```
example (h : ∃ x : Nat, x = x) : True :=
  let ⟨x, _⟩ := h  -- ok, because the goal is `True : Prop`
  trivial
```
-/
inductive c172 : {α : Sort u} → (α → Prop) → Prop where
  /--
存在量词引入。若 `a : α` 且 `h : p a`，则 `⟨a, h⟩` 是 `∃ x : α, p x` 的证明。
-/
  | intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → c172 p

/--
使用 `Classical.choose` 从存在性陈述中提取元素。
-/
noncomputable def c173 := @_root_.Exists.choose

/--
等式关系。它只有一条引入规则 `Eq.refl`。
使用 `a = b` 作为 `Eq a b` 的记法。
等式的一项基本性质是它构成等价关系。
```
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```
不过，等式远不只是一种等价关系。它还具有一项重要性质：每个断言都尊重这种等价，即可以替换相等的表达式而不改变真值。
也就是说，给定 `h1 : a = b` 和 `h2 : p a`，可构造 `p b` 的证明，所用替换为 `Eq.subst h1 h2`。
示例：
```
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```
第二种写法中的三角符号是建立在 `Eq.subst` 和 `Eq.symm` 之上的宏，可输入 `\t` 得到它。
更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)


标识符中记法的约定：

 * 标识符中 `=` 的推荐拼写是 `eq`。
-/
inductive c174 : {α : Sort u} → α → α → Prop where
  /--
`Eq.refl a : a = a` 是自反性，也是等式类型唯一的构造子。另见通常优先使用的 `rfl`。
-/
  | refl : ∀ {α : Sort u} (a : α), c174 a a

/--
`rfl : a = a` 是等式类型唯一的构造子。它与 `Eq.refl` 相同，只不过隐式而非显式地接受 `a`。

这一定理比初看上去更强，因为尽管其陈述是 `a = a`，Lean 也会接受与该类型定义相等的任何类型。例如，在 Lean 中，`2 + 2 = 4` 可用 `rfl` 证明，因为等式两边在定义等价意义下相同。
-/
def c175 := @_root_.rfl

/--
等式具有对称性：若 `a = b`，则 `b = a`。

因为它位于 `Eq` 命名空间中，若有变量 `h : a = b`，则可用 `h.symm` 作为 `Eq.symm h` 的简写来证明 `b = a`。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c176 := @_root_.Eq.symm

/--
等式具有传递性：若 `a = b` 且 `b = c`，则 `a = c`。

因为它位于 `Eq` 命名空间中，若有变量或表达式 `h₁ : a = b` 和 `h₂ : b = c`，则可用 `h₁.trans h₂ : a = c` 作为 `Eq.trans h₁ h₂` 的简写。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c177 := @_root_.Eq.trans

/--
等式的替换原理。若 `a = b ` 且 `P a` 成立，则 `P b` 也成立。这里依惯例用名称 `motive` 表示 `P`；若无法正确推断它，可用例如 `Eq.subst (motive := fun x => x < 5)` 显式指定。

这一定理是 `rw` 策略的底层机制；该策略本质上是一种精巧算法，用于寻找合适的 `motive` 实参，从而有效应用本定理，将目标或假设中出现的 `a` 替换为 `b`。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c178 := @_root_.Eq.subst

/--
沿类型等式进行强制转换。若 `h : α = β` 是类型等式且 `a : α`，则直接写 `a : β` 通常无法通过类型检查；此函数可绕过这一限制，把 `a` 嵌入类型 `β`，写作 `cast h a : β`。

最好尽可能避免使用此函数，因为含有强制转换的项更难推理；但当类型并非定义相等时，有时没有更好的做法。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c179 := @_root_.cast

/--
函数与实参两方面的同余性。若 `f₁ = f₂` 且 `a₁ = a₂`，则 `f₁ a₁ = f₂ a₂`。这仅适用于非依赖函数；在依赖情形下，定理陈述更为复杂。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c180 := @_root_.congr

/--
函数应用中函数部分的同余性：若 `f = g`，则 `f a = g a`。
-/
def c181 := @_root_.congrFun

/--
函数实参的同余性：若 `a₁ = a₂`，则 `f a₁ = f a₂`，其中 `f` 为任意非依赖函数。这比初看上去更强，因为还可以用 lambda 表达式作为 `f`，证明 `<something containing a₁> = <something containing a₂>`。`congr` 和 `simp` 等策略在子项内部应用等式时，会在内部使用此函数。

更多信息：[等式](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
def c182 := @_root_.congrArg

/--
若 `h : α = β` 是类型等式的证明，则 `h.mp : α → β` 是由它诱导的“强制转换”运算，把 `α` 的元素映射到 `β` 的元素。

可对 `h` 归纳来证明结果元素的定理，因为 `rfl.mp` 定义上就是恒等函数。
-/
def c183 := @_root_.Eq.mp

/--
若 `h : α = β` 是类型等式的证明，则 `h.mpr : β → α` 是由它诱导的反向“强制转换”运算，把 `β` 的元素映射到 `α` 的元素。

可对 `h` 归纳来证明结果元素的定理，因为 `rfl.mpr` 定义上就是恒等函数。
-/
def c184 := @_root_.Eq.mpr

/--
异构等式。`a ≍ b` 断言 `a` 与 `b` 具有相同类型，并且沿该等式强制转换 `a` 会得到 `b`，反之亦然。

应尽可能避免使用此类型。异构等式不具有 `Eq` 的全部性质，因为仅假定 `a` 与 `b` 的类型相等，通常不足以证明所需定理。一个重要的公知反例是 `congr` 的类似命题：若 `f ≍ g` 且 `x ≍ y`，并且 `f x` 与 `g y` 都类型正确，也不能推出 `f x ≍ g y`。（若改为 `f = g`，则可以推出。）不过，若 `a` 与 `b` 类型相同，则 `a = b` 与 `a ≍ b` 等价。


标识符中记法的约定：

 * 标识符中 `≍` 的推荐拼写是 `heq`。
-/
inductive c185 : {α : Sort u} → α → {β : Sort u} → β → Prop where
  /--
异构等式的自反性。
-/
  | refl : ∀ {α : Sort u} (a : α), c185 a a

/--
隐式接受实参的 `HEq.refl` 版本。
-/
def c186 := @_root_.HEq.rfl

/--
`HEq.ndrec` 的变体。
-/
noncomputable def c187 := @_root_.HEq.elim

/--
`HEq` 的非依赖递归器。
-/
noncomputable def c188 := @_root_.HEq.ndrec

/--
`HEq.ndrec` 的变体。
-/
noncomputable def c189 := @_root_.HEq.ndrecOn

/--
使用异构等式进行替换。
-/
def c190 := @_root_.HEq.subst

/--
若两个异构相等的项具有相同类型，则它们在命题上相等。
-/
def c191 := @_root_.eq_of_heq

/--
命题上相等的项也异构相等。
-/
def c192 := @_root_.heq_of_eq

/--
若使用 `Eq.rec` 把一项强制转换到另一类型后，它等于另一个项，则这两项异构相等。
-/
def c193 := @_root_.heq_of_eqRec_eq

/--
在 `φ` 内使用 `Eq.recOn` 重写所得的项，与原项异构相等。
-/
def c194 := @_root_.eqRec_heq

/--
使用 `cast` 强制转换一项所得的结果，与原项异构相等。
-/
def c195 := @_root_.cast_heq

/--
异构等式可在前面复合命题等式。
-/
def c196 := @_root_.heq_of_heq_of_eq

/--
若两项异构相等，则它们的类型在命题上相等。
-/
def c197 := @_root_.type_eq_of_heq

/--
延迟求值。被延迟的代码至多求值一次。

惰性计算是一段代码，在通过 `Thunk.get`、`Thunk.map` 或 `Thunk.bind` 请求值时构造该值。所得值会被缓存，因此代码至多执行一次。这也称为惰性求值或按需调用求值。

Lean 运行时对 `Thunk` 类型提供特殊支持，以实现缓存行为。
-/
structure c198 (α : Type u) where
  /--
从惰性计算中提取取值函数。请改用 `Thunk.get`。
-/
  fn : Unit → α

/--
构造新的惰性计算，其中函数 `Unit → α` 会在首次强制求值时调用。

结果会被缓存，并在再次强制求值时复用。
-/
add_decl_doc c198.mk

/--
获取惰性计算的值。若值已缓存，则在常数时间内返回；否则计算该值。

计算出的值会被缓存，因此不会重复计算。
-/
def c199 := @_root_.Thunk.get

/--
构造一个新的惰性计算，它会强制求值 `x`，再把 `x` 应用于所得结果。强制求值时，`f` 的结果会被缓存，并丢弃对惰性计算 `x` 的引用。
-/
def c200 := @_root_.Thunk.map

/--
把已经计算出的值存入惰性计算。

由于该值已经算出，因此没有惰性。
-/
def c201 := @_root_.Thunk.pure

/--
构造一个新的惰性计算；强制求值时，将 `f` 应用于 `x` 的结果。
-/
def c202 := @_root_.Thunk.bind

end Manual.ZhDocString.Ch19Ch20.G2
