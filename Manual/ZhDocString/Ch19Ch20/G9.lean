/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G9

set_option linter.unusedVariables false
set_option autoImplicit true

/-- 字大小无符号整数的非严格不等式，定义为相应自然数的不等式。通常通过 `≤` 操作员访问。 -/
def c001 := @_root_.USize.le

/-- 字长有符号整数的非严格不等式，定义为相应整数的不等式。通常通过 `≤` 操作员访问。 -/
def c002 := @_root_.ISize.le

/-- 8 位无符号整数的非严格不等式，定义为相应自然数的不等式。通常通过 `≤` 操作员访问。 -/
def c003 := @_root_.UInt8.le

/-- 8 位有符号整数的非严格不等式，定义为相应整数的不等式。通常通过 `≤` 操作员访问。 -/
def c004 := @_root_.Int8.le

/-- 16 位无符号整数的非严格不等式，定义为相应自然数的不等式。通常通过 `≤` 操作员访问。 -/
def c005 := @_root_.UInt16.le

/-- 16 位有符号整数的非严格不等式，定义为相应整数的不等式。通常通过 `≤` 操作员访问。 -/
def c006 := @_root_.Int16.le

/-- 32 位无符号整数的非严格不等式，定义为相应自然数的不等式。通常通过 `≤` 操作员访问。 -/
def c007 := @_root_.UInt32.le

/-- 32 位有符号整数的非严格不等式，定义为相应整数的不等式。通常通过 `≤` 操作员访问。 -/
def c008 := @_root_.Int32.le

/-- 64 位无符号整数的非严格不等式，定义为相应自然数的不等式。通常通过 `≤` 操作员访问。 -/
def c009 := @_root_.UInt64.le

/-- 64 位有符号整数的非严格不等式，定义为相应整数的不等式。通常通过 `≤` 操作员访问。 -/
def c010 := @_root_.Int64.le

/-- 字长无符号整数的严格不等式，定义为相应自然数的不等式。通常通过 `<` 操作员访问。 -/
def c011 := @_root_.USize.lt

/-- 字长有符号整数的严格不等式，定义为相应整数的不等式。通常通过 `<` 操作员访问。 -/
def c012 := @_root_.ISize.lt

/-- 8 位无符号整数的严格不等式，定义为相应自然数的不等式。通常通过 `<` 操作员访问。 -/
def c013 := @_root_.UInt8.lt

/-- 8 位有符号整数的严格不等式，定义为相应整数的不等式。通常通过 `<` 操作员访问。 -/
def c014 := @_root_.Int8.lt

/-- 16位无符号整数的严格不等式，定义为相应自然数的不等式。通常通过 `<` 操作员访问。 -/
def c015 := @_root_.UInt16.lt

/-- 16 位有符号整数的严格不等式，定义为相应整数的不等式。通常通过 `<` 操作员访问。 -/
def c016 := @_root_.Int16.lt

/-- 32位无符号整数的严格不等式，定义为相应自然数的不等式。通常通过 `<` 操作员访问。 -/
def c017 := @_root_.UInt32.lt

/-- 32 位有符号整数的严格不等式，定义为相应整数的不等式。通常通过 `<` 操作员访问。 -/
def c018 := @_root_.Int32.lt

/-- 64位无符号整数的严格不等式，定义为相应自然数的不等式。通常通过 `<` 操作员访问。 -/
def c019 := @_root_.UInt64.lt

/-- 64 位有符号整数的严格不等式，定义为相应整数的不等式。通常通过 `<` 操作员访问。 -/
def c020 := @_root_.Int64.lt

/--
决定两个字大小的无符号整数是否相等。通常通过 `DecidableEq USize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `USize.decEq 123 123 = .isTrue rfl`
 * `(if (6 : USize) = 7 then "yes" else "no") = "no"`
 * `show (7 : USize) = 7 by decide`
-/
def c021 := @_root_.USize.decEq

/--
确定两个字大小的有符号整数是否相等。通常通过 `DecidableEq ISize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `ISize.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : ISize) = 7 then "yes" else "no") = "no"`
 * `show (7 : ISize) = 7 by decide`
-/
def c022 := @_root_.ISize.decEq

/--
判断两个 8 位无符号整数是否相等。通常通过 `DecidableEq UInt8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `UInt8.decEq 123 123 = .isTrue rfl`
 * `(if (6 : UInt8) = 7 then "yes" else "no") = "no"`
 * `show (7 : UInt8) = 7 by decide`
-/
def c023 := @_root_.UInt8.decEq

/--
判断两个 8 位有符号整数是否相等。通常通过 `DecidableEq Int8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `Int8.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int8) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int8) = 7 by decide`
-/
def c024 := @_root_.Int8.decEq

/--
判断两个 16 位无符号整数是否相等。通常通过 `DecidableEq UInt16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `UInt16.decEq 123 123 = .isTrue rfl`
 * `(if (6 : UInt16) = 7 then "yes" else "no") = "no"`
 * `show (7 : UInt16) = 7 by decide`
-/
def c025 := @_root_.UInt16.decEq

/--
判断两个 16 位有符号整数是否相等。通常通过 `DecidableEq Int16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `Int16.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int16) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int16) = 7 by decide`
-/
def c026 := @_root_.Int16.decEq

/--
判断两个 32 位无符号整数是否相等。通常通过 `DecidableEq UInt32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `UInt32.decEq 123 123 = .isTrue rfl`
 * `(if (6 : UInt32) = 7 then "yes" else "no") = "no"`
 * `show (7 : UInt32) = 7 by decide`
-/
def c027 := @_root_.UInt32.decEq

/--
确定两个 32 位有符号整数是否相等。通常通过 `DecidableEq Int32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `Int32.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int32) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int32) = 7 by decide`
-/
def c028 := @_root_.Int32.decEq

/--
判断两个 64 位无符号整数是否相等。通常通过 `DecidableEq UInt64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `UInt64.decEq 123 123 = .isTrue rfl`
 * `(if (6 : UInt64) = 7 then "yes" else "no") = "no"`
 * `show (7 : UInt64) = 7 by decide`
-/
def c029 := @_root_.UInt64.decEq

/--
确定两个 64 位有符号整数是否相等。通常通过 `DecidableEq Int64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `Int64.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int64) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int64) = 7 by decide`
-/
def c030 := @_root_.Int64.decEq

/--
确定一个字大小的无符号整数是否小于或等于另一个字大小的无符号整数。通常通过 `DecidableLE USize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (15 : USize) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : USize) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : USize) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : USize) ≤ 7 by decide`
-/
def c031 := @_root_.USize.decLe

/--
确定一个字大小的有符号整数是否小于或等于另一个字大小的有符号整数。通常通过 `DecidableLE ISize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : ISize) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : ISize) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : ISize) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : ISize) ≤ 7 by decide`
-/
def c032 := @_root_.ISize.decLe

/--
确定一个 8 位无符号整数是否小于或等于另一个。通常通过 `DecidableLE UInt8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (15 : UInt8) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt8) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt8) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt8) ≤ 7 by decide`
-/
def c033 := @_root_.UInt8.decLe

/--
确定一个 8 位有符号整数是否小于或等于另一个。通常通过 `DecidableLE Int8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int8) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int8) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int8) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int8) ≤ 7 by decide`
-/
def c034 := @_root_.Int8.decLe

/--
确定一个 16 位无符号整数是否小于或等于另一个。通常通过 `DecidableLE UInt16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (15 : UInt16) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt16) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt16) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt16) ≤ 7 by decide`
-/
def c035 := @_root_.UInt16.decLe

/--
确定一个 16 位有符号整数是否小于或等于另一个。通常通过 `DecidableLE Int16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int16) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int16) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int16) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int16) ≤ 7 by decide`
-/
def c036 := @_root_.Int16.decLe

/--
确定一个 32 位有符号整数是否小于或等于另一个。通常通过 `DecidableLE UInt32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (15 : UInt32) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt32) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt32) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt32) ≤ 7 by decide`
-/
def c037 := @_root_.UInt32.decLe

/--
确定一个 32 位有符号整数是否小于或等于另一个。通常通过 `DecidableLE Int32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int32) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int32) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int32) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int32) ≤ 7 by decide`
-/
def c038 := @_root_.Int32.decLe

/--
确定一个 64 位无符号整数是否小于或等于另一个。通常通过 `DecidableLE UInt64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (15 : UInt64) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt64) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt64) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt64) ≤ 7 by decide`
-/
def c039 := @_root_.UInt64.decLe

/--
确定一个 8 位有符号整数是否小于或等于另一个。通常通过 `DecidableLE Int64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int64) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int64) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int64) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int64) ≤ 7 by decide`
-/
def c040 := @_root_.Int64.decLe

/--
确定一个字大小的无符号整数是否严格小于另一个字大小的无符号整数。通常通过 `DecidableLT USize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (6 : USize) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : USize) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : USize) < 7) by decide`
-/
def c041 := @_root_.USize.decLt

/--
确定一个字大小的有符号整数是否严格小于另一个字大小的有符号整数。通常通过 `DecidableLT ISize` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : ISize) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : ISize) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : ISize) < 7) by decide`
-/
def c042 := @_root_.ISize.decLt

/--
确定一个 8 位无符号整数是否严格小于另一个。通常通过 `DecidableLT UInt8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (6 : UInt8) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt8) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt8) < 7) by decide`
-/
def c043 := @_root_.UInt8.decLt

/--
确定一个 8 位有符号整数是否严格小于另一个。通常通过 `DecidableLT Int8` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int8) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int8) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int8) < 7) by decide`
-/
def c044 := @_root_.Int8.decLt

/--
确定一个 16 位无符号整数是否严格小于另一个。通常通过 `DecidableLT UInt16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (6 : UInt16) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt16) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt16) < 7) by decide`
-/
def c045 := @_root_.UInt16.decLt

/--
确定一个 16 位有符号整数是否严格小于另一个。通常通过 `DecidableLT Int16` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int16) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int16) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int16) < 7) by decide`
-/
def c046 := @_root_.Int16.decLt

/--
确定一个 8 位无符号整数是否严格小于另一个。通常通过 `DecidableLT UInt32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (6 : UInt32) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt32) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt32) < 7) by decide`
-/
def c047 := @_root_.UInt32.decLt

/--
确定一个 32 位有符号整数是否严格小于另一个。通常通过 `DecidableLT Int32` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int32) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int32) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int32) < 7) by decide`
-/
def c048 := @_root_.Int32.decLt

/--
确定一个 64 位无符号整数是否严格小于另一个。通常通过 `DecidableLT UInt64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if (6 : UInt64) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt64) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt64) < 7) by decide`
-/
def c049 := @_root_.UInt64.decLt

/--
确定一个 8 位有符号整数是否严格小于另一个。通常通过 `DecidableLT Int64` 实例访问。

该函数在运行时被有效的实现覆盖。

示例：
 * `(if ((-7) : Int64) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int64) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int64) < 7) by decide`
-/
def c050 := @_root_.Int64.decLt

/-- 将 `String` 转换为表示整个字符串的 `Substring`。 -/
def c051 := @_root_.String.toRawSubstring

/--
将 `String` 转换为表示整个字符串的 `Substring`。

这是 `String.toRawSubstring` 的一个不带 `@[inline]` 注解的版本。
-/
def c052 := @_root_.String.toRawSubstring'

/--
某些底层字符串的区域或切片。

子字符串包含一个字符串以及感兴趣区域的起始和结束字节位置。实际上提取子字符串需要复制和内存分配，而同一底层字符串可能存在许多子字符串，开销很小，并且它们比手动跟踪边界更方便。

显式使用其构造函数，可以构造一个 `Substring`，其中一个或两个位置对于字符串无效。如果开始位置和停止位置无效，许多操作将返回意外或令人困惑的结果。因此，`Substring` 将被弃用，取而代之的是 `String.Slice`，它始终表示有效的子字符串。
-/
structure c053 where
  /-- 底层字符串。 -/
  str : String
  /-- 字符串切片起始位置的字节位置。 -/
  startPos : String.Pos.Raw
  /-- 字符串切片结束位置的字节位置。 -/
  stopPos : String.Pos.Raw

/--
检查子字符串是否为空。

如果子字符串的开始位置和结束位置相同，则子字符串为空。
-/
def c054 := @_root_.Substring.Raw.isEmpty

/-- 字符串的 UTF-8 编码使用的字节数。 -/
def c055 := @_root_.Substring.Raw.bsize

/--
检查子字符串中的位置是否精确等于其结束位置。

该位置是相对于子字符串的起始位置而不是基础字符串的起始位置来理解的。
-/
def c056 := @_root_.Substring.Raw.atEnd

/-- 返回 `c` 在 `s` 中首次出现位置相对于子字符串的位置；若 `s.bsize` 之前未出现 `c`，则返回该值。 -/
def c057 := @_root_.Substring.Raw.posOf

/--
返回子字符串中给定位置之后的下一个位置。如果位置位于子字符串的末尾，则原样返回。

输入位置和返回位置都是相对于子字符串的起始位置而不是基础字符串进行解释的。
-/
def c058 := @_root_.Substring.Raw.next

/--
返回子字符串中从给定位置向前指定字符数的位置。如果到达子字符串的结束位置，则返回该子字符串。

输入位置和返回位置都是相对于子字符串的起始位置而不是基础字符串进行解释的。
-/
def c059 := @_root_.Substring.Raw.nextn

/--
返回子字符串中给定位置之前的上一个位置。如果位置位于子字符串的开头，则原样返回。

输入位置和返回位置都是相对于子字符串的起始位置而不是基础字符串进行解释的。
-/
def c060 := @_root_.Substring.Raw.prev

/--
返回子字符串中给定位置之前指定字符数的位置。如果到达子字符串的起始位置，则返回该子字符串。

输入位置和返回位置都是相对于子字符串的起始位置而不是基础字符串进行解释的。
-/
def c061 := @_root_.Substring.Raw.prevn

/-- 将函数折叠到左侧的子字符串上，累加以 `init` 开头的值。累加值按顺序与每个字符组合，使用 `f`。 -/
def c062 := @_root_.Substring.Raw.foldl

/-- 将函数折叠到右侧的子字符串上，累加以 `init` 开头的值。使用 `f` 将累积值与每个字符按相反顺序组合。 -/
def c063 := @_root_.Substring.Raw.foldr

/--
检查布尔谓词 `p` 是否为子字符串中的每个字符返回 `true`。

在 `p` 返回 `false` 的第一个字符处短路。
-/
def c064 := @_root_.Substring.Raw.all

/--
检查布尔谓词 `p` 是否为子字符串中的任何字符返回 `true`。

在 `p` 返回 `true` 的第一个字符处短路。
-/
def c065 := @_root_.Substring.Raw.any

/--
检查两个子字符串是否表示相等的字符串。通常通过 `==` 操作员访问。

两个子字符串不需要具有相同的底层字符串或相同的开始和结束位置；相反，如果它们包含相同的字符序列，则它们相等。
-/
def c066 := @_root_.Substring.Raw.beq

/--
检查两个子字符串是否具有相同的位置和内容。

两个子字符串不需要具有相同的基础字符串即可使此检查成功。
-/
def c067 := @_root_.Substring.Raw.sameAs

/--
返回两个子字符串的最长公共前缀。

返回的子字符串使用与 `s` 相同的基础字符串。
-/
def c068 := @_root_.Substring.Raw.commonPrefix

/--
返回两个子字符串的最长公共后缀。

返回的子字符串使用与 `s` 相同的基础字符串。
-/
def c069 := @_root_.Substring.Raw.commonSuffix

/--
如果 `pre` 是 `s` 的前缀，则返回剩余部分，否则返回 `none`。

子字符串 `pre` 是 `s` 的前缀，当且仅当存在 `t : Substring` 使得 `s.toString = pre.toString ++ t.toString`。此时结果是 `s` 去掉该前缀后的子字符串。
-/
def c070 := @_root_.Substring.Raw.dropPrefix?

/--
如果 `suff` 是 `s` 的后缀，则返回剩余部分，否则返回 `none`。

子字符串 `suff` 是 `s` 的后缀，当且仅当存在 `t : Substring` 使得 `s.toString = t.toString ++ suff.toString`。此时结果是 `s` 去掉该后缀后的子字符串。
-/
def c071 := @_root_.Substring.Raw.dropSuffix?

/--
返回子字符串中给定位置的字符。

该位置是相对于子字符串而不是基础字符串的，并且不会针对子字符串的结束位置执行边界检查。如果相对位置不是基础字符串中的有效位置，则返回回退值 `(default : Char)`，即 `'A'`。  不惊慌。
-/
def c072 := @_root_.Substring.Raw.get

/-- 检查子字符串是否包含指定字符。 -/
def c073 := @_root_.Substring.Raw.contains

/--
返回子字符串中的第一个字符。

如果子字符串为空，但子字符串的起始位置是基础字符串中的有效位置，则返回起始位置处的字符。如果子字符串的起始位置不是字符串中的有效位置，则返回回退值 `(default : Char)`，即 `'A'`。  不惊慌。
-/
def c074 := @_root_.Substring.Raw.front

/--
通过向前移动子字符串的起始位置，从子字符串的开头删除指定数量的字符（Unicode 代码点）。

如果到达子字符串的结束位置，则起始位置不会提前超过它。
-/
def c075 := @_root_.Substring.Raw.drop

/-- 通过移动子字符串的起始位置，删除其中布尔谓词为所有字符返回 `true` 的子字符串的最长前缀。起始位置将移动到谓词返回 `false` 的第一个字符的位置，或者如果谓词始终返回 `true`，则移动到子字符串的结束位置。 -/
def c076 := @_root_.Substring.Raw.dropWhile

/--
通过将子字符串的结束位置移向其开始位置，从子字符串的末尾删除指定数量的字符（Unicode 代码点）。

如果到达子字符串的起始位置，则结束位置不会缩回超过它。
-/
def c077 := @_root_.Substring.Raw.dropRight

/-- 通过移动子字符串的结束位置，删除其中布尔谓词为所有字符返回 `true` 的子字符串的最长后缀。结束位置将移动到谓词返回 `false` 的最后一个字符的位置之后，或者如果谓词始终返回 `true`，则移动到子字符串的开始位置。 -/
def c078 := @_root_.Substring.Raw.dropRightWhile

/--
通过将子字符串的结束位置移向开始位置，仅保留子字符串开头的指定数量的字符（Unicode 代码点）。

如果到达子字符串的起始位置，则结束位置不会缩回超过它。
-/
def c079 := @_root_.Substring.Raw.take

/-- 仅保留子字符串的最长前缀，其中布尔谓词通过将子字符串的结束位置移向其开始位置来为所有字符返回 `true`。 -/
def c080 := @_root_.Substring.Raw.takeWhile

/--
通过将子字符串的起始位置移向结束位置，仅保留子字符串末尾指定数量的字符（Unicode 代码点）。

如果到达子字符串的结束位置，则起始位置不会提前超过它。
-/
def c081 := @_root_.Substring.Raw.takeRight

/-- 仅保留子字符串的最长后缀，其中布尔谓词通过将子字符串的起始位置移向其结束位置来为所有字符返回 `true`。 -/
def c082 := @_root_.Substring.Raw.takeRightWhile

/--
以子字符串的形式返回由提供的开始位置和停止位置分隔的子字符串区域。这些位置是根据子字符串的起始位置而不是底层字符串来解释的。

如果生成的子字符串为空，则生成的子字符串是空字符串 `""` 的子字符串。否则，底层字符串是输入子字符串的起始位置和结束位置已调整的字符串。
-/
def c083 := @_root_.Substring.Raw.extract

/--
通过首先将其起始位置移动到第一个非空白字符，然后将其结束位置移动到最后一个非空白字符，从子字符串中删除前导和尾随空白。

如果子字符串仅包含空格，则生成的子字符串的起始位置将移动到其结束位置。

“空白”定义为 `Char.isWhitespace` 返回 `true` 的字符。

示例：
 * `" red green blue ".toRawSubstring.trim.toString = "red green blue"`
 * `" red green blue ".toRawSubstring.trim.startPos = ⟨1⟩`
 * `" red green blue ".toRawSubstring.trim.stopPos = ⟨15⟩`
 * `"     ".toRawSubstring.trim.startPos = ⟨5⟩`
-/
def c084 := @_root_.Substring.Raw.trim

/--
通过将子字符串的起始位置移动到第一个非空格字符，或者如果没有非空格字符，则移动到其结束位置，从而删除子字符串中的前导空格。

“空白”定义为 `Char.isWhitespace` 返回 `true` 的字符。
-/
def c085 := @_root_.Substring.Raw.trimLeft

/--
通过将子字符串的结束位置移动到最后一个非空格字符，或者如果没有非空格字符，则移动到其开始位置，从而删除子字符串中的尾随空格。

“空白”定义为 `Char.isWhitespace` 返回 `true` 的字符。
-/
def c086 := @_root_.Substring.Raw.trimRight

/--
在子字符串 `s` 中每次出现分隔符字符串 `sep` 的位置进行拆分。默认分隔符是 `" "`。

当 `sep` 为空时，结果为 `[s]`。当 `sep` 以重叠模式出现时，采用首个匹配。如果存在 `n+1` 个返回元素，则恰好存在 `n` 个非重叠的 `sep` 匹配。分隔符不会包含在返回的子字符串中，而这些子字符串全都是 `s` 的底层字符串的子字符串。
-/
def c087 := @_root_.Substring.Raw.splitOn

/-- 给定一个 `Substring`，返回另一个具有有效端点并根据 `Substring.toString` 表示相同子字符串的值。 （注意，子字符串仍然可能是反转的，即开始大于结束。） -/
def c088 := @_root_.Substring.Raw.repair

/-- {} 将子字符串指向的基础字符串区域复制到新字符串中。 -/
def c089 := @_root_.Substring.Raw.toString

/--
检查子字符串是否可以解释为自然数的十进制表示形式。

如果子字符串不为空并且其中的所有字符都是数字，则可以将其解释为十进制自然数。为了便于阅读，允许使用下划线 ({lit}`_`) 作为数字分隔符，但不能出现在开头、结尾或连续。

使用 `Substring.toNat?` 将此类子字符串转换为自然数。
-/
def c090 := @_root_.Substring.Raw.isNat

/--
检查子字符串是否可以解释为自然数的十进制表示形式，如果可以则返回该数字。

如果子字符串不为空并且其中的所有字符都是数字，则可以将其解释为十进制自然数。下划线 ({lit}`_`) 允许作为数字分隔符，但在解析过程中会被忽略。

使用`Substring.isNat`检查子串是否是这样的子串。
-/
def c091 := @_root_.Substring.Raw.toNat?

/-- 返回一个迭代器到底层字符串的子字符串的起始位置。结束位置被丢弃，因此不能单独使用迭代器来确定其当前位置是否在原始子字符串内。 -/
def c092 := @_root_.Substring.Raw.toLegacyIterator

/--
将子字符串转换为精益编译器的名称表示形式。生成的名称是分层的，并且字符串在点处分割 (`'.'`)。

`"a.b".toRawSubstring.toName` 是名称 `a.b`，而不是 `«a.b»`。对于后者，请使用 `Name.mkSimple ∘ Substring.Raw.toString`。 -- TODO: 弃用旧名称
-/
def c093 := @_root_.Substring.Raw.toName

/--
某些底层数组的区域。

子数组包含一个数组以及感兴趣区域的起始索引和结束索引。子数组可用于避免复制或分配空间，同时比手动跟踪边界更方便。感兴趣区域由大于或等于 `start` 且严格小于 `stop` 的每个索引组成。
-/
def c094 := @_root_.Subarray

/--
空子数组。

这个空子数组由一个空数组支持。
-/
def c095 := @_root_.Subarray.empty

/-- 底层数组。 -/
def c096 := @_root_.Subarray.array

/-- 感兴趣区域的起始索引（含）。 -/
def c097 := @_root_.Subarray.start

/-- 感兴趣区域的结束索引（不包括）。 -/
def c098 := @_root_.Subarray.stop

/--
起始索引不晚于结束索引。

结束索引是排他的。如果起始索引和结束索引相等，则子数组为空。
-/
def c099 := @_root_.Subarray.start_le_stop

/--
停止索引不晚于数组末尾。

结束索引是排他的。如果它等于数组的大小，则数组的最后一个元素在子数组中。
-/
def c100 := @_root_.Subarray.stop_le_array_size

/-- 删除子数组的第一个 `i` 元素。如果元素数量为 `i` 或更少，则生成的子数组为空。 -/
def c101 := @_root_.Subarray.drop

/-- 仅保留子数组的前 `i` 元素。如果元素数量为 `i` 或更少，则生成的子数组为空。 -/
def c102 := @_root_.Subarray.take

/--
如果可能的话，通过增加其起始索引来缩小子数组，否则返回原样。

示例：
* `#[1,2,3].toSubarray.popFront.toArray = #[2, 3]`
* `#[1,2,3].toSubarray.popFront.popFront.toArray = #[3]`
* `#[1,2,3].toSubarray.popFront.popFront.popFront.toArray = #[]`
* `#[1,2,3].toSubarray.popFront.popFront.popFront.popFront.toArray = #[]`
-/
def c103 := @_root_.Subarray.popFront

/-- 将子数组分为两部分，第一部分包含第一个 `i` 元素，第二部分包含其余部分。 -/
def c104 := @_root_.Subarray.split

/--
从子数组中提取一个元素。

索引是相对于子数组的开头，而不是相对于底层数组。
-/
def c105 := @_root_.Subarray.get

/--
从子数组中提取元素，或者当索引越界时返回默认值。

索引是相对于子数组的开头和结尾，而不是相对于底层数组。默认值是 `Inhabited α` 实例提供的值。
-/
def c106 := @_root_.Subarray.get!

/--
从子数组中提取元素，或者当索引越界时返回默认值 `v₀`。

索引是相对于子数组的开头和结尾，而不是相对于底层数组。
-/
def c107 := @_root_.Subarray.getD

/--
在子数组中的元素上从右向左折叠操作。

`β` 类型的累加器的构造方法是从 `init` 开始，依次将子数组的每个元素与当前累加器值相结合，从末尾移动到开头。

示例：
 * `#["red", "green", "blue"].toSubarray.foldr (·.length + ·) 0 = 12`
 * `#["red", "green", "blue"].toSubarray.popFront.foldr (·.length + ·) 0 = 9`
-/
def c108 := @_root_.Subarray.foldr

/--
在子数组中的元素上从右向左折叠一元运算。

`β` 类型的累加器是通过以下方式构造的：从 `init` 开始，依次将子数组的每个元素与当前累加器值进行一元组合，从末尾移动到开头。所讨论的单子可能允许提前终止或重复。

示例：
```lean example
#eval #["red", "green", "blue"].toSubarray.foldrM (init := "") fun x acc => do
  let l ← Option.guard (· ≠ 0) x.length
  return s!"{acc}({l}){x} "
```
```output
some "(4)blue (5)green (3)red "
```
```lean example
#eval #["red", "green", "blue"].toSubarray.foldrM (init := 0) fun x acc => do
  let l ← Option.guard (· ≠ 5) x.length
  return s!"{acc}({l}){x} "
```
```output
none
```
-/
def c109 := @_root_.Subarray.foldrM

/--
对子数组的每个元素运行一元操作。

从最低索引开始处理元素并向上移动。
-/
def c110 := @_root_.Subarray.forM

/--
以相反的顺序对子数组的每个元素运行一元操作。

从最高索引开始处理元素并向下移动。
-/
def c111 := @_root_.Subarray.forRevM

/-- `ForIn.forIn` 针对 `Subarray` 的实现，使其可用于 `for` 循环的 `do` 记法。 -/
def c112 := @_root_.Subarray.forIn

/--
使用布尔谓词以相反顺序测试子数组中的每个元素，在满足谓词的第一个元素处停止。返回满足谓词的元素，如果没有元素满足谓词，则返回 `none`。

示例：
 * `#["red", "green", "blue"].toSubarray.findRev? (·.length ≠ 4) = some "green"`
 * `#["red", "green", "blue"].toSubarray.findRev? (fun _ => true) = some "blue"`
 * `#["red", "green", "blue"].toSubarray 0 0 |>.findRev? (fun _ => true) = none`
-/
def c113 := @_root_.Subarray.findRev?

/--
以相反的顺序将一元布尔谓词应用于子数组中的每个元素，在满足谓词的第一个元素处停止。返回满足谓词的元素，如果没有元素满足它，则返回 `none`。

例子：
```lean example
#eval #["red", "green", "blue"].toSubarray.findRevM? fun x => do
  IO.println x
  return (x.length = 5)
```
```output
blue
green
```
```output
some 5
```
-/
def c114 := @_root_.Subarray.findRevM?

/--
以相反的顺序将一元函数应用于子数组中的每个元素，并在函数成功的第一个元素处停止，返回 `none` 以外的值。返回后续值，如果不成功则返回 `none`。

例子：
```lean example
#eval #["red", "green", "blue"].toSubarray.findSomeRevM? fun x => do
  IO.println x
  return Option.guard (· = 5) x.length
```
```output
blue
green
```
```output
some 5
```
-/
def c115 := @_root_.Subarray.findSomeRevM?

/--
检查子数组中的所有元素是否满足布尔谓词。

从最低索引开始并向上移动元素进行测试。一旦找到不满足谓词的元素，搜索就会终止。
-/
def c116 := @_root_.Subarray.all

/--
检查子数组中的所有元素是否满足一元布尔谓词。

从最低索引开始并向上移动元素进行测试。一旦找到不满足谓词的元素，搜索就会终止。

例子：
```lean example
#eval #["red", "green", "blue", "orange"].toSubarray.popFront.allM fun x => do
  IO.println x
  pure (x.length == 5)
```
```output
green
blue
```
```output
false
```
-/
def c117 := @_root_.Subarray.allM

/--
检查子数组中的任何元素是否满足布尔谓词。

从最低索引开始并向上移动元素进行测试。一旦找到满足谓词的元素，搜索就会终止。
-/
def c118 := @_root_.Subarray.any

/--
检查子数组中的任何元素是否满足一元布尔谓词。

从最低索引开始并向上移动元素进行测试。一旦找到满足谓词的元素，搜索就会终止。

例子：
```lean example
#eval #["red", "green", "blue", "orange"].toSubarray.popFront.anyM fun x => do
  IO.println x
  pure (x == "blue")
```
```output
green
blue
```
```output
true
```
-/
def c119 := @_root_.Subarray.anyM

/--
将函数应用于列表的每个元素，返回结果值列表。

`O(|l|)`。

示例：
* `[a, b, c].map f = [f a, f b, f c]`
* `[].map Nat.succ = []`
* `["one", "two", "three"].map (·.length) = [3, 3, 5]`
* `["one", "two", "three"].map (·.reverse) = ["eno", "owt", "eerht"]`
-/
def c120 := @_root_.List.map

/--
将函数应用于列表的每个元素，返回结果值列表。

`O(|l|)`。这是 `List.map` 的尾递归变体，在运行时代码中使用。

示例：
* `[a, b, c].mapTR f = [f a, f b, f c]`
* `[].mapTR Nat.succ = []`
* `["one", "two", "three"].mapTR (·.length) = [3, 3, 5]`
* `["one", "two", "three"].mapTR (·.reverse) = ["eno", "owt", "eerht"]`
-/
def c121 := @_root_.List.mapTR

/--
将单子操作 `f` 从左到右应用于列表中的每个元素，并返回结果列表。

这个实现是尾递归的。 `List.mapM'` 是一种非尾递归变体，可能更方便推理。 `List.forM` 是丢弃结果的变体，`List.mapA` 是与 `Applicative` 一起使用的变体。
-/
def c122 := @_root_.List.mapM

/--
从左到右对列表中的每个元素应用一元操作 `f`，并返回结果列表。

这是 `List.mapM` 的非尾递归变体，更容易推理。它不能用作主定义并被尾递归版本替换，因为只有当 `m` 是 `LawfulMonad` 时才能证明它们相等。
-/
def c123 := @_root_.List.mapM'

/--
从左到右对列表中的每个元素应用应用操作 `f`，并返回结果列表。

如果 `m` 也是 `Monad`，则使用 `mapM` 会更高效。

请参阅 `List.forA` 了解丢弃结果的变体。请参阅 `List.mapM` 了解与 `Monad` 配合使用的变体。

此函数不是尾递归的，因此它可能会因长列表上的堆栈溢出而失败。
-/
def c124 := @_root_.List.mapA

/--
将函数应用于列表中的每个元素以及找到该元素的索引，返回结果列表。除了索引之外，该函数还提供了索引有效的证明。

`List.mapIdx` 是一个变体，它不向函数提供索引有效的证据。
-/
def c125 := @_root_.List.mapFinIdx

/--
将一元函数应用于列表中的每个元素以及找到该元素的索引，返回结果列表。除了索引之外，该函数还提供了索引有效的证明。

`List.mapIdxM` 是一个变体，它不向函数提供索引有效的证据。
-/
def c126 := @_root_.List.mapFinIdxM

/--
将函数应用于列表中的每个元素以及找到该元素的索引，返回结果列表。

`List.mapFinIdx` 是一个变体，它另外为该函数提供索引有效的证明。
-/
def c127 := @_root_.List.mapIdx

/--
将一元函数应用于列表的每个元素以及找到该元素的索引，返回结果列表。

`List.mapFinIdxM` 是一个变体，它另外为该函数提供索引有效的证明。
-/
def c128 := @_root_.List.mapIdxM

/--
将函数应用于列表的每个元素，返回结果列表。该函数是单态的：要求返回相同类型的值。内部实现使用指针相等，并且如果每个函数调用的结果与其参数指针相等，则不会分配新列表。

出于验证目的，`List.mapMono = List.map`。
-/
def c129 := @_root_.List.mapMono

/-- 将一元函数应用于列表的每个元素，返回结果列表。该函数是单态的：要求返回相同类型的值。内部实现使用指针相等，并且如果每个函数调用的结果与其参数指针相等，则不会分配新列表。 -/
def c130 := @_root_.List.mapMonoM

/--
应用一个函数，将列表返回到列表的每个元素，并连接结果列表。

示例：
* `[2, 3, 2].flatMap List.range = [0, 1, 0, 1, 2, 0, 1]`
* `["red", "blue"].flatMap String.toList = ['r', 'e', 'd', 'b', 'l', 'u', 'e']`
-/
def c131 := @_root_.List.flatMap

/--
应用一个函数，将列表返回到列表的每个元素，并连接结果列表。

这是运行时使用的 `List.flatMap` 的尾递归版本。

示例：
* `[2, 3, 2].flatMapTR List.range = [0, 1, 0, 1, 2, 0, 1]`
* `["red", "blue"].flatMapTR String.toList = ['r', 'e', 'd', 'b', 'l', 'u', 'e']`
-/
def c132 := @_root_.List.flatMapTR

/-- 应用一个单子函数，该函数从左到右将列表返回到列表中的每个元素，并连接结果列表。 -/
def c133 := @_root_.List.flatMapM

/--
将两个列表组合成一个对列表，其中第一个和第二个组件是每个列表的对应元素。结果列表是输入列表中较短者的长度。

`O(min |xs| |ys|)`。

示例：
* `["Mon", "Tue", "Wed"].zip [1, 2, 3] = [("Mon", 1), ("Tue", 2), ("Wed", 3)]`
* `["Mon", "Tue", "Wed"].zip [1, 2] = [("Mon", 1), ("Tue", 2)]`
* `[x₁, x₂, x₃].zip [y₁, y₂, y₃, y₄] = [(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def c134 := @_root_.List.zip

/--
将列表的每个元素与其索引配对，可以选择从 `0` 以外的索引开始。

`O(|l|)`。

示例：
* `[a, b, c].zipIdx = [(a, 0), (b, 1), (c, 2)]`
* `[a, b, c].zipIdx 5 = [(a, 5), (b, 6), (c, 7)]`
-/
def c135 := @_root_.List.zipIdx

/--
将列表的每个元素与其索引配对，可以选择从 `0` 以外的索引开始。

`O(|l|)`。这是在运行时使用的 `List.zipIdx` 的尾递归版本。

示例：
* `[a, b, c].zipIdxTR = [(a, 0), (b, 1), (c, 2)]`
* `[a, b, c].zipIdxTR 5 = [(a, 5), (b, 6), (c, 7)]`
-/
def c136 := @_root_.List.zipIdxTR

/--
将函数应用于两个列表的相应元素，并在较短列表的末尾停止。

`O(min |xs| |ys|)`。

示例：
* `[1, 2].zipWith (· + ·) [5, 6] = [6, 8]`
* `[1, 2, 3].zipWith (· + ·) [5, 6, 10] = [6, 8, 13]`
* `[].zipWith (· + ·) [5, 6] = []`
* `[x₁, x₂, x₃].zipWith f [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
def c137 := @_root_.List.zipWith

/--
将函数应用于两个列表的相应元素，并在较短列表的末尾停止。

`O(min |xs| |ys|)`。这是在运行时使用的 `List.zipWith` 的尾递归版本。

示例：
* `[1, 2].zipWithTR (· + ·) [5, 6] = [6, 8]`
* `[1, 2, 3].zipWithTR (· + ·) [5, 6, 10] = [6, 8, 13]`
* `[].zipWithTR (· + ·) [5, 6] = []`
* `[x₁, x₂, x₃].zipWithTR f [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
def c138 := @_root_.List.zipWithTR

/--
将函数应用于两个列表的相应元素，当两个列表中都没有更多元素时停止。如果一个列表比另一个列表短，则函数将通过 `none` 查找缺失的元素。

示例：
* `[1, 6].zipWithAll min [5, 2] = [some 1, some 2]`
* `[1, 2, 3].zipWithAll Prod.mk [5, 6] = [(some 1, some 5), (some 2, some 6), (some 3, none)]`
* `[x₁, x₂].zipWithAll f [y] = [f (some x₁) (some y), f (some x₂) none]`
-/
def c139 := @_root_.List.zipWithAll

/--
将成对列表分成两个列表，其中包含各自的第一和第二组件。

`O(|l|)`。

示例：
* `[("Monday", 1), ("Tuesday", 2)].unzip = (["Monday", "Tuesday"], [1, 2])`
* `[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzip = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
* `([] : List (Nat × String)).unzip = (([], []) : List Nat × List String)`
-/
def c140 := @_root_.List.unzip

/--
将成对列表分成两个列表，其中包含各自的第一和第二组件。

`O(|l|)`。这是在运行时使用的 `List.unzip` 的尾递归版本。

示例：
* `[("Monday", 1), ("Tuesday", 2)].unzipTR = (["Monday", "Tuesday"], [1, 2])`
* `[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzipTR = ([x₁, x₂, x₃], [y₁, y₂, y₃])`
* `([] : List (Nat × String)).unzipTR = (([], []) : List Nat × List String)`
-/
def c141 := @_root_.List.unzipTR

/-- 字符是 Unicode [标量值](http://www.unicode.org/glossary/#unicode_scalar_value)。 -/
structure c142 where
  mk ::
  /-- 以 `UInt32` 表示的底层 Unicode 标量值。 -/
  val : UInt32
  /-- 该值必须是合法的标量值。 -/
  valid : val.isValidChar

/-- 将 `Nat` 转换为 `Char`。如果 `Nat` 未编码有效的 Unicode 标量值，则返回 `'\0'`。 -/
def c143 := @_root_.Char.ofNat

/-- 该字符的 Unicode 代码点为 `Nat`。 -/
def c144 := @_root_.Char.toNat

/-- 对于有效的 [Unicode 标量值](https://www.unicode.org/glossary/#unicode_scalar_value) 的自然数为 true。 -/
def c145 := @_root_.Char.isValidCharNat

/--
将 8 位无符号整数转换为字符。

该整数的值被解释为 Unicode 代码点。
-/
def c146 := @_root_.Char.ofUInt8

/--
将字符转换为包含其代码点的 `UInt8`。

如果代码点大于 255，则会被截断（模 256 减少）。
-/
def c147 := @_root_.Char.toUInt8

/--
构造一个仅包含所提供字符的单例字符串。

示例：
* `'L'.toString = "L"`
* `'"'.toString = "\""`
-/
def c148 := @_root_.Char.toString

/--
将字符引用为字符文字的表示形式，用单引号括起来并根据需要进行转义。

示例：
 * `'L'.quote = "'L'"`
 * `'"'.quote = "'\\\"'"`
-/
def c149 := @_root_.Char.quote

/--
如果字符是 ASCII 字母，则返回 `true`。

ASCII 字母如下：`ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz`。
-/
def c150 := @_root_.Char.isAlpha

/--
如果字符是 ASCII 字母或数字，则返回 `true`。

ASCII 字母如下：`ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz`。 ASCII 数字如下：`0123456789`。
-/
def c151 := @_root_.Char.isAlphanum

/--
如果字符是 ASCII 数字，则返回 `true`。

ASCII 数字如下：`0123456789`。
-/
def c152 := @_root_.Char.isDigit

/--
如果字符是小写 ASCII 字母，则返回 `true`。

小写 ASCII 字母如下：`abcdefghijklmnopqrstuvwxyz`。
-/
def c153 := @_root_.Char.isLower

/--
如果字符是大写 ASCII 字母，则返回 `true`。

大写 ASCII 字母如下：`ABCDEFGHIJKLMNOPQRSTUVWXYZ`。
-/
def c154 := @_root_.Char.isUpper

/-- 当字符为空格时返回 `true`；空格包括 `(' ', U+0020)`、制表符 `('\t', U+0009)`、回车符 `('\r', U+000D)` 或换行符 `('\n', U+000A)`。 -/
def c155 := @_root_.Char.isWhitespace

/--
将小写 ASCII 字母转换为相应的大写字母。 ASCII 字母表之外的字母将原样返回。

小写 ASCII 字母如下：`abcdefghijklmnopqrstuvwxyz`。
-/
def c156 := @_root_.Char.toUpper

/--
将大写 ASCII 字母转换为相应的小写字母。 ASCII 字母表之外的字母将原样返回。

大写 ASCII 字母如下：`ABCDEFGHIJKLMNOPQRSTUVWXYZ`。
-/
def c157 := @_root_.Char.toLower

/-- 如果一个字符的代码点小于或等于另一个字符的代码点，则该字符小于或等于另一个字符。 -/
def c158 := @_root_.Char.le

/-- 如果一个字符的代码点严格小于另一个字符的代码点，则该字符小于另一个字符。 -/
def c159 := @_root_.Char.lt

/-- 返回以 UTF-8 编码此 `Char` 所需的字节数。 -/
def c160 := @_root_.Char.utf8Size

/--
提取前 `n` 个 `xs` 元素；如果 `n` 大于 `xs.length`，则提取整个列表。

`O(min n |xs|)`。

示例：
* `[a, b, c, d, e].take 0 = []`
* `[a, b, c, d, e].take 3 = [a, b, c]`
* `[a, b, c, d, e].take 6 = [a, b, c, d, e]`
-/
def c161 := @_root_.List.take

/--
提取前 `n` 个 `xs` 元素；如果 `n` 大于 `xs.length`，则提取整个列表。

`O(min n |xs|)`。这是运行时使用的 `List.take` 尾递归版本。

示例：
* `[a, b, c, d, e].takeTR 0 = []`
* `[a, b, c, d, e].takeTR 3 = [a, b, c]`
* `[a, b, c, d, e].takeTR 6 = [a, b, c, d, e]`
-/
def c162 := @_root_.List.takeTR

/--
返回 `xs` 中 `p` 返回 true 的最长初始段。

`O(|xs|)`。

示例：
* `[7, 6, 4, 8].takeWhile (· > 5) = [7, 6]`
* `[7, 6, 6, 5].takeWhile (· > 5) = [7, 6, 6]`
* `[7, 6, 6, 8].takeWhile (· > 5) = [7, 6, 6, 8]`
-/
def c163 := @_root_.List.takeWhile

/--
返回 `xs` 中 `p` 返回 true 的最长初始段。

`O(|xs|)`。这是 `List.take` 的尾递归版本，在运行时使用。

示例：
* `[7, 6, 4, 8].takeWhileTR (· > 5) = [7, 6]`
* `[7, 6, 6, 5].takeWhileTR (· > 5) = [7, 6, 6]`
* `[7, 6, 6, 8].takeWhileTR (· > 5) = [7, 6, 6, 8]`
-/
def c164 := @_root_.List.takeWhileTR

/--
移除前 `n` 个列表 `xs` 的元素。如果 `n` 大于列表长度，则返回空列表。

`O(min n |xs|)`。

示例：
* `[0, 1, 2, 3, 4].drop 0 = [0, 1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].drop 3 = [3, 4]`
* `[0, 1, 2, 3, 4].drop 6 = []`
-/
def c165 := @_root_.List.drop

/--
删除 `p` 返回 `true` 的列表的最长前缀。

元素将从列表中删除，直到遇到 `p` 返回 `false` 的元素为止。返回该元素和列表的其余部分。

`O(|l|)`。

示例：
 * `[1, 3, 2, 4, 2, 7, 4].dropWhile (· < 4) = [4, 2, 7, 4]`
 * `[8, 3, 2, 4, 2, 7, 4].dropWhile (· < 4) = [8, 3, 2, 4, 2, 7, 4]`
 * `[8, 3, 2, 4, 2, 7, 4].dropWhile (· < 100) = []`
-/
def c166 := @_root_.List.dropWhile

/--
删除列表的最后一个元素（如果存在）。

示例：
* `[].dropLast = []`
* `["tea"].dropLast = []`
* `["tea", "coffee", "juice"].dropLast = ["tea", "coffee"]`
-/
def c167 := @_root_.List.dropLast

/--
删除列表的最后一个元素（如果存在）。

这是 `List.dropLast` 的尾递归版本，在运行时使用。

示例：
* `[].dropLastTR = []`
* `["tea"].dropLastTR = []`
* `["tea", "coffee", "juice"].dropLastTR = ["tea", "coffee"]`
-/
def c168 := @_root_.List.dropLastTR

/--
在索引处拆分列表，结果将前 `n` 个 `l` 的元素与剩余元素配对。

如果 `n` 大于 `l` 的长度，则结果对由 `l` 和空列表组成。`List.splitAt` 等价于组合使用 `List.take` 和 `List.drop`，但效率更高。

示例：
* `["red", "green", "blue"].splitAt 2 = (["red", "green"], ["blue"])`
* `["red", "green", "blue"].splitAt 3 = (["red", "green", "blue], [])`
* `["red", "green", "blue"].splitAt 4 = (["red", "green", "blue], [])`
-/
def c169 := @_root_.List.splitAt

/--
将列表拆分为最长的初始段，`p` 返回 `true`，并与列表的其余部分配对。

`O(|l|)`。

示例：
* `[6, 8, 9, 5, 2, 9].span (· > 5) = ([6, 8, 9], [5, 2, 9])`
* `[6, 8, 9, 5, 2, 9].span (· > 10) = ([], [6, 8, 9, 5, 2, 9])`
* `[6, 8, 9, 5, 2, 9].span (· > 0) = ([6, 8, 9, 5, 2, 9], [])`
-/
def c170 := @_root_.List.span

/--
将列表拆分为最长的段，其中每对相邻元素通过 `R` 相关。

`O(|l|)`。

示例：
* `[1, 1, 2, 2, 2, 3, 2].splitBy (· == ·) = [[1, 1], [2, 2, 2], [3], [2]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (· < ·) = [[1, 2, 5], [4, 5], [1, 4]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (fun _ _ => true) = [[1, 2, 5, 4, 5, 1, 4]]`
* `[1, 2, 5, 4, 5, 1, 4].splitBy (fun _ _ => false) = [[1], [2], [5], [4], [5], [1], [4]]`
-/
def c171 := @_root_.List.splitBy

/--
返回一对列表，它们一起包含 `as` 的所有元素。第一个列表包含 `p` 返回 `true` 的元素，第二个列表包含 `p` 返回 `false` 的元素。

`O(|l|)`。 `as.partition p` 等效于 `(as.filter p, as.filter (not ∘ p))`，但它的效率稍高一些，因为它只需对列表执行一次传递。

示例：
 * `[1, 2, 5, 2, 7, 7].partition (· > 2) = ([5, 7, 7], [1, 2, 2])`
 * `[1, 2, 5, 2, 7, 7].partition (fun _ => false) = ([], [1, 2, 5, 2, 7, 7])`
 * `[1, 2, 5, 2, 7, 7].partition (fun _ => true) = ([1, 2, 5, 2, 7, 7], [])`
-/
def c172 := @_root_.List.partition

/--
返回一对列表，它们一起包含 `as` 的所有元素。第一个列表包含单子谓词 `p` 返回 `true` 的元素，第二个列表包含 `p` 返回 `false` 的元素。按从左到右的顺序检查列表的元素。

这是 `List.partition` 的一元版本。

例子：
```lean example
def posOrNeg (x : Int) : Except String Bool :=
  if x > 0 then pure true
  else if x < 0 then pure false
  else throw "Zero is not positive or negative"
```
```lean example
#eval [-1, 2, 3].partitionM posOrNeg
```
```output
Except.ok ([2, 3], [-1])
```
```lean example
#eval [0, 2, 3].partitionM posOrNeg
```
```output
Except.error "Zero is not positive or negative"
```
-/
def c173 := @_root_.List.partitionM

/--
应用一个函数，该函数向列表的每个元素返回不相交并集，将 `Sum.inl` 和 `Sum.inr` 结果收集到单独的列表中。

示例：
 * `[0, 1, 2, 3].partitionMap (fun x => if x % 2 = 0 then .inl x else .inr x) = ([0, 2], [1, 3])`
 * `[0, 1, 2, 3].partitionMap (fun x => if x = 0 then .inl x else .inr x) = ([0], [1, 2, 3])`
-/
def c174 := @_root_.List.partitionMap

/--
根据列表 `xs` 的元素经函数 `key` 得到的结果进行分组，返回将每组与其键关联的哈希映射。各组保留元素在 `xs` 中的相对顺序。

示例：
```lean example
#eval [0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)
```
```output
Std.HashMap.ofList [(0, [0, 2, 4, 6]), (1, [1, 3, 5])]
```
-/
def c175 := @_root_.List.groupByKey

/--
类型 `α` 和 `β` 的不交并，通常写作 `α ⊕ β`。

`α ⊕ β` 的元素要么是由 `a : α` 经 `Sum.inl` 包装得到的值，要么是由 `b : β` 经 `Sum.inr` 包装得到的值。`α ⊕ β` 不等价于 `α` 与 `β` 的集合论并集，因为其值还包含从两种类型中选择了哪一种的信息。单元素集合与自身的并集只有一个元素，而 `Unit ⊕ Unit` 包含不同的值 `inl ()` 和 `inr ()`。
-/
inductive c176 (α : Type u) (β : Type v) where
  /-- 到和类型 `α ⊕ β` 的左注入。 -/
  | inl (val : α) : c176 α β
  /-- 到和类型 `α ⊕ β` 的右注入。 -/
  | inr (val : β) : c176 α β

/--
任意排序 `α` `β` 或 `α ⊕' β` 的不相交并集。

它与 `α ⊕ β` 的不同之处在于，它允许 `α` 和 `β` 具有任意排序 `Sort u` 和 `Sort v`，而不是将它们限制为 `Type u` 和 `Type v`。这意味着它可以用在一侧是命题的情况下，例如 `True ⊕' Nat`。然而，由此产生的宇宙级约束通常比 `Sum` 产生的约束更难解决。
-/
inductive c177 (α : Sort u) (β : Sort v) : Sort (max (max 1 u) v) where
  /-- 到和类型 `α ⊕' β` 的左注入。 -/
  | inl (val : α) : c177 α β
  /-- 到和类型 `α ⊕' β` 的右注入。 -/
  | inr (val : β) : c177 α β

/-- 检查总和是否为左注入`inl`。 -/
def c178 := @_root_.Sum.isLeft

/-- 检查总和是否是正确的注入 `inr`。 -/
def c179 := @_root_.Sum.isRight

/-- 在检查存在哪个构造函数后，对应用适当函数 `f` 或 `g` 的求和进行案例分析。 -/
def c180 := @_root_.Sum.elim

/-- 从已知为 `inl` 的总和中检索内容。 -/
def c181 := @_root_.Sum.getLeft

/-- 检查总和是否为左注入 `inl`，如果是，则检索其内容。 -/
def c182 := @_root_.Sum.getLeft?

/-- 从已知为 `inr` 的总和中检索内容。 -/
def c183 := @_root_.Sum.getRight

/-- 检查总和是否是正确的注入 `inr`，如果是，则检索其内容。 -/
def c184 := @_root_.Sum.getRight?

/--
根据每种类型的函数转换总和。

该函数将 `α ⊕ β` 映射到 `α' ⊕ β'`，将 `α` 发送到 `α'`，将 `β` 发送到 `β'`。
-/
def c185 := @_root_.Sum.map

/--
交换和类型的因子。

构造函数 `Sum.inl` 替换为 `Sum.inr`，反之亦然。
-/
def c186 := @_root_.Sum.swap

/--
如果总和中的左侧类型被占据，则总和被占据。

当左类型和右类型都存在时，这不是避免非规范实例的实例。
-/
def c187 := @_root_.Sum.inhabitedLeft

/--
如果总和中存在正确的类型，那么总和就存在。

当左类型和右类型都存在时，这不是避免非规范实例的实例。
-/
def c188 := @_root_.Sum.inhabitedRight

/--
如果总和中的左侧类型被占据，则总和被占据。

当左类型和右类型都存在时，这不是避免非规范实例的实例。
-/
def c189 := @_root_.PSum.inhabitedLeft

/--
如果总和中存在正确的类型，那么总和就存在。

当左类型和右类型都存在时，这不是避免非规范实例的实例。
-/
def c190 := @_root_.PSum.inhabitedRight

/--
第一个列表是第二个列表的前缀。

`IsPrefix l₁ l₂` 写作 `l₁ <+: l₂`，表示存在一些 `t : List α`，使得 `l₂` 具有 `l₁ ++ t` 的形式。

函数 `List.isPrefixOf` 是布尔值等价函数。


标识符中的符号约定：

 * 标识符中 `<+:` 的建议拼写为 `prefix`（而不是 `isPrefix`）。
-/
def c191 := @_root_.List.IsPrefix

/--
第一个列表是第二个列表的后缀。

`IsSuffix l₁ l₂` 写作 `l₁ <:+ l₂`，表示存在一些 `t : List α`，使得 `l₂` 具有 `t ++ l₁` 的形式。

函数 `List.isSuffixOf` 是布尔值等价函数。


标识符中的符号约定：

 * 标识符中 `<:+` 的建议拼写为 `suffix`（而不是 `isSuffix`）。
-/
def c192 := @_root_.List.IsSuffix

/--
第一个列表是第二个列表的连续子列表。通常用 `<:+:` 运算符编写。

换句话说，`l₁ <:+: l₂` 表示存在列表 `s : List α` 和 `t : List α`，使得 `l₂` 具有 `s ++ l₁ ++ t` 的形式。


标识符中的符号约定：

 * 标识符中 `<:+:` 的建议拼写为 `infix`（而不是 `isInfix`）。
-/
def c193 := @_root_.List.IsInfix

/--
第一个列表是第二个列表的不连续子列表。通常用 `<+` 运算符编写。

换句话说，`l₁ <+ l₂`表示通过重复插入新元素，可以将`l₁`转变为`l₂`。
-/
inductive c194 {α : Type u} : List α → List α → Prop where
  /-- 基本情形：`[]` 是 `[]` 的子列表。 -/
  | slnil : c194 [] []
  /-- 若 `l₁` 是 `l₂` 的子序列，则它也是 `a :: l₂` 的子序列。 -/
  | cons {l₁ l₂ : List α} (a : α) : c194 l₁ l₂ → c194 l₁ (a :: l₂)
  /-- 若 `l₁` 是 `l₂` 的子序列，则 `a :: l₁` 是 `a :: l₂` 的子序列。 -/
  | cons_cons {l₁ l₂ : List α} (a : α) : c194 l₁ l₂ → c194 (a :: l₁) (a :: l₂)

/--
如果两个列表包含相同的元素，并且每个列表出现相同的次数但不一定以相同的顺序，则它们是彼此的排列。

通过展示如何通过重复交换相邻元素将一个列表转换为另一个列表，可以证明一个列表是另一个列表的排列。

`List.isPerm` 是该关系的布尔等价值。
-/
inductive c195 {α : Type u} : List α → List α → Prop where
  /-- 空列表是空列表的一个排列：`[] ~ []`。 -/
  | nil : c195 [] []
  /-- 若一个列表是另一个列表的排列，则在二者头部添加相同元素后所得的列表也互为排列：`l₁ ~ l₂ → x::l₁ ~ x::l₂`。 -/
  | cons (x : α) {l₁ l₂ : List α} : c195 l₁ l₂ → c195 (x :: l₁) (x :: l₂)
  /-- 若两个列表除前两个元素互换外完全相同，则它们互为排列：`x::y::l ~ y::x::l`。 -/
  | swap (x y : α) (l : List α) : c195 (y :: x :: l) (x :: y :: l)
  /-- 排列具有传递性：`l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`。 -/
  | trans {l₁ l₂ l₃ : List α} : c195 l₁ l₂ → c195 l₂ l₃ → c195 l₁ l₃

/--
列表中的每个元素都通过 `R` 与列表中所有后续元素相关。

`Pairwise R l` 表示 `l` 中索引较早的所有元素与索引较晚的所有元素都与 `R` 相关。

例如，`Pairwise (· ≠ ·) l` 断言 `l` 没有重复项，`Pairwise (· < ·) l` 断言 `l` 已（严格）排序。

示例：
 * `Pairwise (· < ·) [1, 2, 3] ↔ (1 < 2 ∧ 1 < 3) ∧ 2 < 3`
 * `Pairwise (· = ·) [1, 2, 3] = False`
 * `Pairwise (· ≠ ·) [1, 2, 3] = True`
-/
inductive c196 {α : Type u} (R : α → α → Prop) : List α → Prop where
  /-- 空列表的所有元素之间自然两两满足给定关系。 -/
  | nil : c196 R []
  /--
若非空列表的头部与尾部的每个元素都满足关系 `R`，且尾部自身的元素两两满足该关系，则此列表的元素两两满足该关系。

也就是说，若满足以下条件，则 `a :: l` 为 `Pairwise R`：
 * `R` 将 `a` 与 `l` 的每个元素相关联
 * `l` 为 `Pairwise R`。
  -/
  | cons {a : α} {l : List α} : (∀ a' ∈ l, R a a') → c196 R l → c196 R (a :: l)

/--
该列表没有重复项：它最多包含每个元素一次。

它被定义为`Pairwise (· ≠ ·)`：每个元素都不等于所有其他元素。
-/
def c197 := @_root_.List.Nodup

/--
列表的字典顺序与元素的顺序有关。

`as` 按字典顺序小于 `bs`，如果
* `as` 为空且 `bs` 非空，或者
* `as` 和 `bs` 均非空，且 `as` 的头部小于 `bs` 的头部
`r`，或
* `as` 和 `bs` 都是非空的，它们的头相等，并且 `as` 的尾部小于
`bs` 的尾部。
-/
inductive c198 {α : Type u} (r : α → α → Prop) : List α → List α → Prop where
  /-- `[]` 是字典序中的最小元素。 -/
  | nil {a : α} {l : List α} : c198 r [] (a :: l)
  /-- 若第一个列表的头部小于第二个列表的头部，则第一个列表按字典序小于第二个列表。 -/
  | rel {a₁ : α} {l₁ : List α} {a₂ : α} {l₂ : List α} : r a₁ a₂ → c198 r (a₁ :: l₁) (a₂ :: l₂)
  /-- 若两个列表的头部相同，则它们的尾部决定其字典序。若第一个列表的尾部按字典序小于第二个列表的尾部，则整个第一个列表按字典序小于整个第二个列表。 -/
  | cons {a : α} {l₁ l₂ : List α} : c198 r l₁ l₂ → c198 r (a :: l₁) (a :: l₂)

/--
列出成员资格，通常通过 `∈` 操作员访问。

`a ∈ l` 表示 `a` 是列表 `l` 的元素。元素根据精益的逻辑相等进行比较。

相关函数 `List.elem` 是使用 `BEq α` 实例的布尔隶属度测试。

示例：
* `a ∈ [x, y, z] ↔ a = x ∨ a = y ∨ a = z`
-/
inductive c199 {α : Type u} (a : α) : List α → Prop where
  /-- 列表的头部是其成员：`a ∈ a :: as`。 -/
  | head (as : List α) : c199 a (a :: as)
  /-- 列表尾部的成员也是该列表的成员：`a ∈ l → a ∈ b :: l`。 -/
  | tail (b : α) {as : List α} : c199 a as → c199 a (b :: as)

/--
空类型。它没有构造子。

当作用域中有一个类型为 `Empty.elim` 所消去的 `Empty` 值时使用它。
-/
inductive c200 : Type

/--
宇宙多态的空类型，没有构造子。

`PEmpty` 可用于任意宇宙，但这种灵活性可能导致较差的错误消息，并使宇宙层级统一更具挑战。可能时应优先使用类型 `Empty` 或命题 `False`。
-/
inductive c201.{u} : Type u

/-- `Empty.elim : Empty → C` 表示可以从 `Empty` 构造任何类型的值。这可以被认为是编译器检查的断言，即代码路径无法访问。 -/
def c202 := @_root_.Empty.elim

/-- `PEmpty.elim : Empty → C` 表示可以从 `PEmpty` 构造任何类型的值。这可以被认为是编译器检查的断言，即代码路径无法访问。 -/
def c203 := @_root_.PEmpty.elim

/--
字符串是 Unicode 标量值的序列。

在运行时，字符串由使用 UTF-8 编码的字节的[动态数组](https://en.wikipedia.org/wiki/Dynamic_array) 表示。以字节为单位的大小 (`String.utf8ByteSize`) 和以字符为单位的大小 (`String.length`) 都会被缓存并占用恒定时间。当对字符串的引用是唯一的时，对字符串的许多操作都会执行就地修改。
-/
structure c204 where
  ofByteArray ::
  /-- 字符串 UTF-8 编码的字节。由于字符串在运行时采用特殊表示，此函数在运行时实际需要线性时间和空间。若要高效访问字符串的字节，请使用 `String.utf8ByteSize` 和 `String.getUTF8Byte`。 -/
  toByteArray : ByteArray
  /-- 字符串的字节构成有效的 UTF-8。 -/
  isValidUTF8 : toByteArray.IsValidUTF8

/--
创建一个字符串，其中按顺序包含列表中的字符。

示例：
* `String.ofList ['L', '∃', '∀', 'N'] = "L∃∀N"`
* `String.ofList [] = ""`
* `String.ofList ['a', 'a', 'a'] = "aaa"`
-/
def c205 := @_root_.String.ofList

/--
将字符串转换为字符列表。

由于字符串表示为包含使用 UTF-8 编码的字符串的动态字节数组，因此此操作所需的时间和空间与字符串的长度成线性关系。

示例：
 * `"abc".toList = ['a', 'b', 'c']`
 * `"".toList = []`
 * `"\n".toList = ['\n']`
-/
def c206 := @_root_.String.toList

/--
满足某个谓词的一个类型中的所有元素。

`Subtype p` 通常写作 `{ x : α // p x }` 或 `{ x // p x }`，它包含所有 `x : α` 且 `p x` 为真的元素。其构造子由值及证明该值满足谓词的证据组成。在运行时代码中，`{ x : α // p x }` 与 `α` 具有相同的表示。

存在从 `{ x : α // p x }` 到 `α` 的强制转换，因此子类型的元素可用于需要底层类型之处。

示例：
 * `{ n : Nat // n % 2 = 0 }` 是偶数的类型。
 * `{ xs : Array String // xs.size = 5 }` 是包含五个 `String` 的数组类型。
 * 给定 `xs : List α`，`List { x : α // x ∈ xs }` 是其所有元素都包含在 `xs` 中的列表类型。


标识符中记法的约定：

 * 标识符中 `{ x // p x }` 的推荐拼写是 `subtype`。
-/
structure c207 {α : Sort u} (p : α → Prop) : Sort (max 1 u) where
  mk ::
  /-- 底层类型中满足该谓词的值。 -/
  val : α
  /-- 证明 `val` 满足谓词 `p` 的证明。 -/
  property : p val

end Manual.ZhDocString.Ch19Ch20.G9
