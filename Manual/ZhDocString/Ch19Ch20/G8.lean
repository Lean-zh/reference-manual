/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G8

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w

/-!
本模块为第 19–20 章的字符串切片、位向量与范围 API 提供中文动态文档载体。
普通定义透明别名到真实声明；结构体和类型类按真实参数与字段逐项镜像。
-/

/--
某个底层字符串的区域或切片。

一个切片由一个字符串以及感兴趣区域的起始和结束字节位置组成。实际提取子字符串需要复制和内存分配，而同一个底层字符串的多个切片可以存在而几乎没有额外开销。虽然可以通过手动跟踪边界来实现，但切片 API 更加方便。

`String.Slice` 打包证明以确保起始和结束位置始终描绘出一个有效的字符串。出于这个原因，它应该优先于 `Substring.Raw` 使用。
-/
structure c001 where
  /--
  底层字符串。
  -/
  str : String
  /--
  字符串切片开始的字节位置。
  -/
  startInclusive : str.Pos
  /--
  字符串切片结束的字节位置。
  -/
  endExclusive : str.Pos
  /--
  该切片不是退化的（但它可能是空的）。
  -/
  startInclusive_le_endExclusive : startInclusive ≤ endExclusive

/--
返回包含整个字符串的切片。
-/
noncomputable def c002 := @String.toSlice

/--
从`p`（包括）到`s`结束的切片。
-/
noncomputable def c003 := @String.sliceFrom

/--
从 `s` 的开头到 `p`（不含该位置）的切片。
-/
noncomputable def c004 := @String.sliceTo

/--
A `Slice.Pos s` 是 `s` 中的一个字节偏移量，并附有证明该位置位于 UTF-8 字符边界处的证明。
-/
structure c005 (s : String.Slice) where
  /--
  `Slice.Pos` 的底层字节偏移。
  -/
  offset : String.Pos.Raw
  /--
  证明 `offset` 对字符串切片 `s` 是有效的。
  -/
  isValidForSlice : offset.IsValidForSlice s

/--
通过复制字节创建一个 `String`，字节来自 `String.Slice`。
-/
noncomputable def c006 := @String.Slice.copy

/--
检查切片是否为空。

空片有 {name}`utf8ByteSize` {lean}`0`。

示例：
* {lean}`"".toSlice.isEmpty = true`
* {lean}`" ".toSlice.isEmpty = false`
-/
noncomputable def c007 := @String.Slice.isEmpty

/--
字符串切片的 UTF-8 编码字节数。
-/
noncomputable def c008 := @String.Slice.utf8ByteSize

/--
从一个位置和一个关于它有效性的证明构造一个在 `s` 上有效的位置。
-/
noncomputable def c009 := @String.Slice.pos

/--
从一个位置构造一个有效的位置 `s`，如果该位置无效则引发运行时错误。
-/
noncomputable def c010 := @String.Slice.pos!

/--
从一个位置构建一个有效的 `s` 位置，如果该位置无效，则返回 `none`。
-/
noncomputable def c011 := @String.Slice.pos?

/--
`s` 的起始位置，作为一个 `s.Pos`。
-/
noncomputable def c012 := @String.Slice.startPos

/--
`s` 的末端之后位置，作为 `s.Pos`。
-/
noncomputable def c013 := @String.Slice.endPos

/--
切片的结束位置，作为 `Pos.Raw`。
-/
noncomputable def c014 := @String.Slice.rawEndPos

/--
给定一个切片和切片内的有效位置，通过将切片的起始位置替换为给定位置，获取同一底层字符串上的新切片。
-/
noncomputable def c015 := @String.Slice.sliceFrom

/--
给定一个切片和切片内的有效位置，通过将切片的末端替换为给定位置，在相同的底层字符串上获得一个新的切片。
-/
noncomputable def c016 := @String.Slice.sliceTo

/--
给定一个切片以及切片内的两个有效位置，获得一个由新边界形成的在相同基础字符串上的新切片。
-/
noncomputable def c017 := @String.Slice.slice

/--
给定一个切片和切片内的两个有效位置，获取由新边界形成的相同底层字符串上的新切片，如果给定的结束位置严格小于给定的起始位置，则触发运行时错误。
-/
noncomputable def c018 := @String.Slice.slice!

/--
从切片的开头移除指定数量的字符（Unicode 代码点）。

如果 `n` 大于 `s` 中的字符数，则返回一个空切片。

示例：

* `"red green blue".toSlice.drop 4 == "green blue".toSlice`

* `"red green blue".toSlice.drop 10 == "blue".toSlice`

* `"red green blue".toSlice.drop 50 == "".toSlice`
-/
noncomputable def c019 := @String.Slice.drop

/--
从切片的末尾移除指定数量的字符（Unicode 代码点）。

如果 `n` 大于 `s` 中的字符数，则返回一个空切片。

示例：

* `"red green blue".toSlice.dropEnd 5 == "red green".toSlice`

* `"red green blue".toSlice.dropEnd 11 == "red".toSlice`

* `"red green blue".toSlice.dropEnd 50 == "".toSlice`
-/
noncomputable def c020 := @String.Slice.dropEnd

/--
创建一个新切片，包含 `s` 中 `pat` 匹配的最长后缀（可能重复匹配）。

示例：

* `"red green blue".toSlice.dropEndWhile Char.isLower == "red green ".toSlice`

* `"red green blue".toSlice.dropEndWhile 'e' == "red green blu".toSlice`

* `"red green blue".toSlice.dropEndWhile (fun (_ : Char) => true) == "".toSlice`
-/
noncomputable def c021 := @String.Slice.dropEndWhile

/--
如果 `pat` 匹配 `s` 的前缀，则返回剩余部分；否则原样返回 `s`。

可使用 `String.Slice.dropPrefix?` 返回 `none`，以处理 `pat` 不匹配前缀的情况。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.dropPrefix "red " == "green blue".toSlice`

* `"red green blue".toSlice.dropPrefix "reed " == "red green blue".toSlice`

* `"red green blue".toSlice.dropPrefix 'r' == "ed green blue".toSlice`

* `"red green blue".toSlice.dropPrefix Char.isLower == "ed green blue".toSlice`
-/
noncomputable def c022 := @String.Slice.dropPrefix

/--
如果 `pat` 匹配 `s` 的前缀，则返回剩余部分；否则返回 `none`。

可使用 `String.Slice.dropPrefix` 原样返回切片，以处理 `pat` 不匹配前缀的情况。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.dropPrefix? "red " == some "green blue".toSlice`

* `"red green blue".toSlice.dropPrefix? "reed " == none`

* `"red green blue".toSlice.dropPrefix? 'r' == some "ed green blue".toSlice`

* `"red green blue".toSlice.dropPrefix? Char.isLower == some "ed green blue".toSlice`
-/
noncomputable def c023 := @String.Slice.dropPrefix?

/--
如果 `pat` 匹配 `s` 的后缀，则返回剩余部分；否则原样返回 `s`。

可使用 `String.Slice.dropSuffix?` 返回 `none`，以处理 `pat` 不匹配后缀的情况。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.dropSuffix " blue" == "red green".toSlice`

* `"red green blue".toSlice.dropSuffix "bluu " == "red green blue".toSlice`

* `"red green blue".toSlice.dropSuffix 'e' == "red green blu".toSlice`

* `"red green blue".toSlice.dropSuffix Char.isLower == "red green blu".toSlice`
-/
noncomputable def c024 := @String.Slice.dropSuffix

/--
如果 `pat` 匹配 `s` 的后缀，则返回剩余部分；否则返回 `none`。

可使用 `String.Slice.dropSuffix` 原样返回切片，以处理 `pat` 不匹配后缀的情况。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.dropSuffix? " blue" == some "red green".toSlice`

* `"red green blue".toSlice.dropSuffix? "bluu " == none`

* `"red green blue".toSlice.dropSuffix? 'e' == some "red green blu".toSlice`

* `"red green blue".toSlice.dropSuffix? Char.isLower == some "red green blu".toSlice`
-/
noncomputable def c025 := @String.Slice.dropSuffix?

/--
创建一个新切片，包含 `s` 的最长前缀，该前缀与 `pat` 匹配（可能重复匹配）。

示例：

* `"red green blue".toSlice.dropWhile Char.isLower == " green blue".toSlice`

* `"red green blue".toSlice.dropWhile 'r' == "ed green blue".toSlice`

* `"red red green blue".toSlice.dropWhile "red " == "green blue".toSlice`

* `"red green blue".toSlice.dropWhile (fun (_ : Char) => true) == "".toSlice`
-/
noncomputable def c026 := @String.Slice.dropWhile

/--
创建一个包含前 `n` 个字符（即 `s` 中的 Unicode 码点）的新切片。

如果 `n` 大于 `s` 中的字符数，则返回 `s`。

示例：

* `"red green blue".toSlice.take 3 == "red".toSlice`

* `"red green blue".toSlice.take 1 == "r".toSlice`

* `"red green blue".toSlice.take 0 == "".toSlice`

* `"red green blue".toSlice.take 100 == "red green blue".toSlice`
-/
noncomputable def c027 := @String.Slice.take

/--
创建一个包含后 `n` 个字符（即 `s` 中的 Unicode 码点）的新切片。

如果 `n` 大于 `s` 中的字符数，则返回 `s`。

示例：

* `"red green blue".toSlice.takeEnd 4 == "blue".toSlice`

* `"red green blue".toSlice.takeEnd 1 == "e".toSlice`

* `"red green blue".toSlice.takeEnd 0 == "".toSlice`

* `"red green blue".toSlice.takeEnd 100 == "red green blue".toSlice`
-/
noncomputable def c028 := @String.Slice.takeEnd

/--
创建一个新切片，包含 `s` 的后缀前缀，其中 `pat` 匹配（可能重复）。

此函数适用于所有当前支持的模式。

示例：

* `"red green blue".toSlice.takeEndWhile Char.isLower == "blue".toSlice`

* `"red green blue".toSlice.takeEndWhile 'e' == "e".toSlice`

* `"red green blue".toSlice.takeEndWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
noncomputable def c029 := @String.Slice.takeEndWhile

/--
创建一个新切片，包含 `s` 的最长前缀，该前缀与 `pat` 匹配（可能重复匹配）。

此函数适用于所有当前支持的模式。

示例：

* `"red green blue".toSlice.takeWhile Char.isLower == "red".toSlice`

* `"red green blue".toSlice.takeWhile 'r' == "r".toSlice`

* `"red red green blue".toSlice.takeWhile "red " == "red red ".toSlice`

* `"red green blue".toSlice.takeWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
noncomputable def c030 := @String.Slice.takeWhile

/--
返回 `s` 中的第一个字符。如果 `s` 为空，则返回 `(default : Char)`。

示例：

* `"abc".toSlice.front = 'a'`

* `"".toSlice.front = (default : Char)`
-/
noncomputable def c031 := @String.Slice.front

/--
返回 `s` 中的第一个字符。如果 `s` 为空，则返回 `none`。

示例：

* `"abc".toSlice.front? = some 'a'`

* `"".toSlice.front? = none`
-/
noncomputable def c032 := @String.Slice.front?

/--
返回 `s` 中的最后一个字符。如果 `s` 为空，则返回 `(default : Char)`。

示例：

* `"abc".toSlice.back = 'c'`

* `"".toSlice.back = (default : Char)`
-/
noncomputable def c033 := @String.Slice.back

/--
返回 `s` 中的最后一个字符。如果 `s` 为空，则返回 `none`。

示例：

* `"abc".toSlice.back? = some 'c'`

* `"".toSlice.back? = none`
-/
noncomputable def c034 := @String.Slice.back?

/--
访问字符串切片的 UTF-8 编码中指定的字节。

在运行时，这个函数由高效的、常数时间的代码实现。
-/
noncomputable def c035 := @String.Slice.getUTF8Byte

/--
访问字符串切片的 UTF-8 编码中指定的字节，如果位置超出范围则会触发 panic。
-/
noncomputable def c036 := @String.Slice.getUTF8Byte!

/--
获取大于或等于给定字节位置的最小有效位置。
-/
noncomputable def c037 := @String.Slice.posGE

/--
获取严格大于给定字节位置的最小有效位置。
-/
noncomputable def c038 := @String.Slice.posGT

/--
检查切片中是否有模式 `pat` 的匹配项。

此函数适用于所有当前支持的模式。

示例：

* `"coffee tea water".toSlice.contains Char.isWhitespace = true`

* `"tea".toSlice.contains (fun (c : Char) => c == 'X') = false`

* `"coffee tea water".toSlice.contains "tea" = true`
-/
noncomputable def c039 := @String.Slice.contains

/--
检查切片 \(`s`\) 是否以模式 \(`pat`\) 开头。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.startsWith "red" = true`

* `"red green blue".toSlice.startsWith "green" = false`

* `"red green blue".toSlice.startsWith "" = true`

* `"red green blue".toSlice.startsWith 'r' = true`

* `"red green blue".toSlice.startsWith Char.isLower = true`
-/
noncomputable def c040 := @String.Slice.startsWith

/--
检查切片 \(`s`\) 是否以模式 \(`pat`\) 结尾。

此函数适用于当前支持的所有模式。

示例：

* `"red green blue".toSlice.endsWith "blue" = true`

* `"red green blue".toSlice.endsWith "green" = false`

* `"red green blue".toSlice.endsWith "" = true`

* `"red green blue".toSlice.endsWith 'e' = true`

* `"red green blue".toSlice.endsWith Char.isLower = true`
-/
noncomputable def c041 := @String.Slice.endsWith

/--
检查切片是否仅由模式 `pat` 的匹配项组成。

在第一个模式不匹配时短路。

此函数适用于所有当前支持的模式。

示例：

* `"brown".toSlice.all Char.isLower = true`

* `"brown and orange".toSlice.all Char.isLower = false`

* `"aaaaaa".toSlice.all 'a' = true`

* `"aaaaaa".toSlice.all "aa" = true`

* `"aaaaaaa".toSlice.all "aa" = false`
-/
noncomputable def c042 := @String.Slice.all

/--
查找模式 `pat` 在切片 `s` 中首次匹配的位置。如果没有匹配，则返回 `none`。

此函数适用于所有当前支持的模式。

示例：

* `("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '`

* `"tea".toSlice.find? (fun (c : Char) => c == 'X') == none`

* `("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'`
-/
noncomputable def c043 := @String.Slice.find?

/--
在切片中查找模式 `pat` 的第一个匹配位置，从切片末尾开始向起始位置遍历。如果没有匹配，则返回 `none`。

此函数对当前支持的所有模式都是通用的，除了`String`/`String.Slice`。

示例：

* `("coffee tea water".toSlice.revFind? Char.isWhitespace).map (·.get!) == some ' '`

* `"tea".toSlice.revFind? (fun (c : Char) => c == 'X') == none`
-/
noncomputable def c044 := @String.Slice.revFind?

/--
在每个与模式 `pat` 匹配的子切片处拆分切片。

与模式匹配的子切片不会包含在任何结果子切片中。如果连续多个子切片匹配该模式，结果列表将包含空字符串。

此函数适用于所有当前支持的模式。

示例：

* `("coffee tea water".toSlice.split Char.isWhitespace).toStringList == ["coffee", "tea", "water"]`

* `("coffee tea water".toSlice.split ' ').toStringList == ["coffee", "tea", "water"]`

* `("coffee tea water".toSlice.split " tea ").toStringList == ["coffee", "water"]`

* `("ababababa".toSlice.split "aba").toStringList == ["coffee", "water"]`

* `("baaab".toSlice.split "aa").toStringList == ["b", "ab"]`
-/
noncomputable def c045 := @String.Slice.split

/--
在每个匹配模式 `pat` 的子切片处拆分切片。与 `split` 不同，匹配的子切片会包含在每个子切片的末尾。

此函数适用于所有当前支持的模式。

示例：

* `("coffee tea water".toSlice.splitInclusive Char.isWhitespace).toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`

* `("coffee tea water".toSlice.splitInclusive ' ').toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`

* `("coffee tea water".toSlice.splitInclusive " tea ").toList == ["coffee tea ".toSlice, "water".toSlice]`

* `("baaab".toSlice.splitInclusive "aa").toList == ["baa".toSlice, "ab".toSlice]`
-/
noncomputable def c046 := @String.Slice.splitInclusive

/--
创建一个迭代器，用于遍历 `s` 中的所有行，并去除行结束字符 `\r\n` 或 `\n`。

示例：

* `"foo\r\nbar\n\nbaz\n".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`

* `"foo\r\nbar\n\nbaz".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`

* `"foo\r\nbar\n\nbaz\r".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz\r".toSlice]`
-/
noncomputable def c047 := @String.Slice.lines

/--
从切片中移除前导和尾部空白。

“空白字符”被定义为 `Char.isWhitespace` 返回 `true` 的字符。

示例：

* `"abc".toSlice.trimAscii == "abc".toSlice`

* `"   abc".toSlice.trimAscii == "abc".toSlice`

* `"abc \t  ".toSlice.trimAscii == "abc".toSlice`

* `"  abc   ".toSlice.trimAscii == "abc".toSlice`

* `"abc\ndef\n".toSlice.trimAscii == "abc\ndef".toSlice`
-/
noncomputable def c048 := @String.Slice.trimAscii

/--
通过将切片的结束位置移动到最后一个非空白字符来移除切片末尾的空白字符，如果没有非空白字符，则移动到其起始位置。

“空白字符”被定义为 `Char.isWhitespace` 返回 `true` 的字符。

示例：

* `"abc".toSlice.trimAsciiEnd == "abc".toSlice`

* `"   abc".toSlice.trimAsciiEnd == "   abc".toSlice`

* `"abc \t  ".toSlice.trimAsciiEnd == "abc".toSlice`

* `"  abc   ".toSlice.trimAsciiEnd == "  abc".toSlice`

* `"abc\ndef\n".toSlice.trimAsciiEnd == "abc\ndef".toSlice`
-/
noncomputable def c049 := @String.Slice.trimAsciiEnd

/--
通过将切片的起始位置移动到第一个非空白字符处（如果没有非空白字符，则移动到其结束位置），来移除切片开头的空白字符。

“空白字符”被定义为 `Char.isWhitespace` 返回 `true` 的字符。

示例：

* `"abc".toSlice.trimAsciiStart == "abc".toSlice`

* `"   abc".toSlice.trimAsciiStart == "abc".toSlice`

* `"abc \t  ".toSlice.trimAsciiStart == "abc \t  ".toSlice`

* `"  abc   ".toSlice.trimAsciiStart == "abc   ".toSlice`

* `"abc\ndef\n".toSlice.trimAsciiStart == "abc\ndef\n".toSlice`
-/
noncomputable def c050 := @String.Slice.trimAsciiStart

/--
创建一个迭代器，用于遍历 `s` 中的所有字符（Unicode 代码点）。

示例：

* `"abc".toSlice.chars.toList = ['a', 'b', 'c']`

* `"ab∀c".toSlice.chars.toList = ['a', 'b', '∀', 'c']`
-/
noncomputable def c051 := @String.Slice.chars

/--
创建一个迭代器，用于遍历 `s` 中的所有字符（Unicode 码点），从切片的末尾开始向起始位置迭代。

示例：

* `"abc".toSlice.revChars.toList = ['c', 'b', 'a']`

* `"ab∀c".toSlice.revChars.toList = ['c', '∀', 'b', 'a']`
-/
noncomputable def c052 := @String.Slice.revChars

/--
创建一个迭代器，用于遍历 {name}`s` 内的所有有效位置。

示例：
* {lean}`("abc".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', 'c']`
* {lean}`("abc".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2]`
* {lean}`("ab∀c".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', '∀', 'c']`
* {lean}`("ab∀c".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2, 5]`
-/
noncomputable def c053 := @String.Slice.positions

/--
创建一个迭代器，遍历 {name}`s` 中所有有效位置，从最后一个有效位置开始，向第一个位置迭代。

例子
 * {lean}`("abc".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', 'b', 'a']`
 * {lean}`("abc".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [2, 1, 0]`
 * {lean}`("ab∀c".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', '∀', 'b', 'a']`
 * {lean}`("ab∀c".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [5, 2, 1, 0]`
-/
noncomputable def c054 := @String.Slice.revPositions

/--
创建一个遍历 {name}`s` 中所有字节的迭代器。

示例：
* {lean}`"abc".toSlice.bytes.toList = [97, 98, 99]`
* {lean}`"ab∀c".toSlice.bytes.toList = [97, 98, 226, 136, 128, 99]`
-/
noncomputable def c055 := @String.Slice.bytes

/--
创建一个迭代器，用于遍历 {name}`s` 中的所有字节，从最后一个开始，向第一个迭代。

示例：
 * {lean}`"abc".toSlice.revBytes.toList = [99, 98, 97]`
 * {lean}`"ab∀c".toSlice.revBytes.toList = [99, 128, 136, 226, 98, 97]`
-/
noncomputable def c056 := @String.Slice.revBytes

/--
从切片末端向开头遍历，在每个与模式 `pat` 匹配的子切片处拆分切片。

与模式匹配的子切片不会包含在任何结果子切片中。如果多个连续子切片匹配该模式，结果列表将包含空切片。

此函数适用于当前支持的所有模式，但 `String`/`String.Slice` 除外。

示例：

* `("coffee tea water".toSlice.revSplit Char.isWhitespace).toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`

* `("coffee tea water".toSlice.revSplit ' ').toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`
-/
noncomputable def c057 := @String.Slice.revSplit

/--
从开始对切片上的函数进行折叠，从 `init` 开始累积值。累积的值按照顺序与每个字符结合，使用 `f`。

示例：

* `"coffee tea water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2`

* `"coffee tea and water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3`

* `"coffee tea water".toSlice.foldl (·.push ·) "" = "coffee tea water"`
-/
noncomputable def c058 := @String.Slice.foldl

/--
从末尾对切片上的函数进行折叠，累积一个从 `init` 开始的值。累积值按照逆序与每个字符结合，使用 `f`。

示例：

* `"coffee tea water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2`

* `"coffee tea and water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3`

* `"coffee tea water".toSlice.foldr (fun c s => s.push c) "" = "retaw aet eeffoc"`
-/
noncomputable def c059 := @String.Slice.foldr

/--
检查切片能否解释为自然数的十进制表示。

切片非空且其中所有字符都是数字时，便可解释为十进制自然数。为便于阅读，可以使用下划线 \(`_`\) 分隔数字，但下划线不能位于开头或结尾，也不能连续出现。

使用 `toNat?` 或 `toNat!` 将此类切片转换为自然数。

示例：

* `"".toSlice.isNat = false`

* `"0".toSlice.isNat = true`

* `"5".toSlice.isNat = true`

* `"05".toSlice.isNat = true`

* `"587".toSlice.isNat = true`

* `"1_000".toSlice.isNat = true`

* `"100_000_000".toSlice.isNat = true`

* `"-587".toSlice.isNat = false`

* `" 5".toSlice.isNat = false`

* `"2+3".toSlice.isNat = false`

* `"0xff".toSlice.isNat = false`

* `"_123".toSlice.isNat = false`

* `"123_".toSlice.isNat = false`

* `"12__34".toSlice.isNat = false`
-/
noncomputable def c060 := @String.Slice.isNat

/--
将切片解释为自然数的十进制表示并返回该自然数。如果切片不包含十进制自然数，则引发运行时错误。

切片非空且其中所有字符都是数字时，便可解释为十进制自然数。可以使用下划线 \(`_`\) 分隔数字；解析时会忽略下划线。

使用 `isNat` 检查 `toNat!` 是否会返回值。更安全的替代方案是 `toNat?`：当字符串不是自然数时，它返回 `none`，而不会引发运行时错误。

示例：

* `"0".toSlice.toNat! = 0`

* `"5".toSlice.toNat! = 5`

* `"587".toSlice.toNat! = 587`

* `"1_000".toSlice.toNat! = 1000`
-/
noncomputable def c061 := @String.Slice.toNat!

/--
将切片解释为自然数的十进制表示并返回该自然数。如果切片不包含十进制自然数，则返回 `none`。

切片非空且其中所有字符都是数字时，便可解释为十进制自然数。可以使用下划线 \(`_`\) 分隔数字；解析时会忽略下划线。

使用 `isNat` 检查 `toNat?` 是否会返回 `some`。
另一种方案是 `toNat!`：当切片不是自然数时，它会引发运行时错误，而不是返回 `none`。

示例：

* `"".toSlice.toNat? = none`

* `"0".toSlice.toNat? = some 0`

* `"5".toSlice.toNat? = some 5`

* `"587".toSlice.toNat? = some 587`

* `"1_000".toSlice.toNat? = some 1000`

* `"100_000_000".toSlice.toNat? = some 100000000`

* `"-587".toSlice.toNat? = none`

* `" 5".toSlice.toNat? = none`

* `"2+3".toSlice.toNat? = none`

* `"0xff".toSlice.toNat? = none`
-/
noncomputable def c062 := @String.Slice.toNat?

/--
检查 `s1` 和 `s2` 是否表示相同的字符串，即使它们是不同基字符串的切片或同一字符串中的不同切片。

该实现是 `s1.copy == s2.copy` 的高效等价物
-/
noncomputable def c063 := @String.Slice.beq

/--
检查 `s1 == s2` 是否成立，如果忽略 ASCII 大小写。
-/
noncomputable def c064 := @String.Slice.eqIgnoreAsciiCase

/--
提供从模式到 `SearchStep` 迭代器的转换；该迭代器从 `Slice` 的开头向末尾搜索模式匹配项。

这些操作可以基于 `ForwardPattern` 实现，但某些模式可以采用更高效的实现。例如，`String` 模式搜索器若由字符串的 `ForwardPattern` 实例派生，就会尝试在字符串的每个位置匹配模式，而已有更高效的字符串匹配方法。Lean 标准库实际使用 Knuth–Morris–Pratt 算法；实现见模块 `Init.Data.String.Pattern.String`。

此类型类可用于提供这样的高效实现。如果不需要这种专门实现，可以使用 `ToForwardSearcher.defaultImplementation` 自动派生实例。
-/
class c065 {ρ : Type} (pat : ρ) (σ : outParam (String.Slice → Type)) where
  /--
  构建一个迭代器，其产生的 `SearchStep` 对应于模式 `pat` 在切片
    `s` 中的各次匹配。该迭代器返回的 `SearchStep` 所含范围必须
    彼此相邻、互不重叠，并覆盖整个 `s`。
  -/
  toSearcher : (s : String.Slice) → @Std.Iter (σ s) (String.Slice.Pattern.SearchStep s)

/--
从 `Slice` 的起始提供简单的模式匹配功能。
-/
class c066 {ρ : Type} (pat : ρ) where
  /--
  检查切片是否以该模式开始。如果是，则返回移除了前缀的切片；否则结果为 `none`。
  -/
  skipPrefix? : (s : String.Slice) → Option s.Pos
  /--
  检查切片是否以该模式开始。如果是，则返回移除了前缀的切片；否则结果为 `none`。
  -/
  skipPrefixOfNonempty? : (s : String.Slice) → s.isEmpty = false → Option s.Pos
  /--
  检查切片是否以该模式开始。
  -/
  startsWith : String.Slice → Bool

/--
提供从模式到 `SearchStep` 迭代器的转换；该迭代器从 `Slice` 的末尾向开头搜索模式匹配项。

这些操作可以基于 `BackwardPattern` 实现，但某些模式可以采用更高效的实现。例如，`String` 模式搜索器若由字符串的 `BackwardPattern` 实例派生，就会尝试在字符串的每个位置匹配模式，而已有更高效的字符串匹配方法。Lean 标准库实际使用 Knuth–Morris–Pratt 算法；实现见模块 `Init.Data.String.Pattern.String`。

此类型类可用于提供这样的高效实现。如果不需要这种专门实现，可以使用 `ToBackwardSearcher.defaultImplementation` 自动派生实例。
-/
class c067 {ρ : Type} (pat : ρ) (σ : outParam (String.Slice → Type)) where
  /--
  构建一个迭代器，其产生的 `SearchStep` 对应于模式 `pat` 在切片
    `s` 中的各次匹配。该迭代器返回的 `SearchStep` 所含范围必须
    彼此相邻、互不重叠，并覆盖整个 `s`。
  -/
  toSearcher : (s : String.Slice) → @Std.Iter (σ s) (String.Slice.Pattern.SearchStep s)

/--
提供从`Slice`末尾进行简单模式匹配的功能。
-/
class c068 {ρ : Type} (pat : ρ) where
  /--
  检查切片是否以该模式结束。如果是，则返回移除该后缀的切片；否则结果为 `none`。
  -/
  skipSuffix? : (s : String.Slice) → Option s.Pos
  /--
  检查切片是否以该模式结束。如果是，则返回移除该后缀的切片；否则结果为 `none`。
  -/
  skipSuffixOfNonempty? : (s : String.Slice) → s.isEmpty = false → Option s.Pos
  /--
  检查切片是否以该模式结尾。
  -/
  endsWith : String.Slice → Bool

/--
返回切片中某个位置的字节，该位置不是结束位置。
-/
noncomputable def c069 := @String.Slice.Pos.byte

/--
获取字符串中给定位置的字符。
-/
noncomputable def c070 := @String.Slice.Pos.get

/--
返回字符串中给定位置的字节；如果该位置是结束位置，则引发运行时错误。
-/
noncomputable def c071 := @String.Slice.Pos.get!

/--
返回字符串中给定位置的字节，如果位置是结尾位置，则返回`none`。
-/
noncomputable def c072 := @String.Slice.Pos.get?

/--
在给定一个证明该位置不是起始位置的前提下，返回给定位置之前的有效位置，这保证了这样的一个位置存在。
-/
noncomputable def c073 := @String.Slice.Pos.prev

/--
返回给定位置之前的上一个有效位置；如果给定位置是起始位置，则引发运行时错误。
-/
noncomputable def c074 := @String.Slice.Pos.prev!

/--
返回给定位置之前的上一个有效位置，如果该位置是起始位置，则返回`none`。
-/
noncomputable def c075 := @String.Slice.Pos.prev?

/--
迭代 `p.prev` `n` 次。

如果这会将 `p` 移动到 `s` 的开始之前，结果是 `s.endPos`。
-/
noncomputable def c076 := @String.Slice.Pos.prevn

/--
在给定证明该位置不是超出末尾位置的情况下，将有效位置在切片上前进到下一个有效位置，这保证了该位置的存在。
-/
noncomputable def c077 := @String.Slice.Pos.next

/--
将切片上的有效位置推进到下一个有效位置；如果给定位置是末端之后的位置，则引发运行时错误。
-/
noncomputable def c078 := @String.Slice.Pos.next!

/--
将切片上的有效位置推进到下一个有效位置，或者如果给定位置是超出末尾的位置，则返回 `none`。
-/
noncomputable def c079 := @String.Slice.Pos.next?

/--
将位置 `p` 前进 `n` 次。

如果这会将 `p` 移动到 `s` 的末尾之后，结果是 `s.endPos`。
-/
noncomputable def c080 := @String.Slice.Pos.nextn

/--
为 `t` 构造有效位置，依据是 `s` 上的有效位置以及证明 `s.copy = t.copy`。
-/
noncomputable def c081 := @String.Slice.Pos.cast

/--
给定`s.slice p₀ p₁ h`中的一个位置，获得`s`中的对应位置。
-/
noncomputable def c082 := @String.Slice.Pos.ofSlice

/--
给定切片 `s` 上的有效位置，获取底层字符串 `s.str` 上对应的有效位置。
-/
noncomputable def c083 := @String.Slice.Pos.str

/--
给定一个切片 `s` 和 `s` 上的一个位置，获取 `s.copy.` 上的对应位置
-/
noncomputable def c084 := @String.Slice.Pos.copy

/--
给定`s.sliceFrom p₀`中的一个位置，获得`s`中的对应位置。
-/
noncomputable def c085 := @String.Slice.Pos.ofSliceFrom

/--
给定`s.sliceTo p₀`中的一个位置，获得`s`中的对应位置。
-/
noncomputable def c086 := @String.Slice.Pos.ofSliceTo

/--
指定宽度的位向量。

这在运行时和内核中都表示为底层的 `Nat` 数字，继承了对 `Nat` 的所有特殊支持。
-/
structure c087 (w : Nat) where
  ofFin ::
  /--
  将位向量解释为小于 `2^w` 的数字。 O(1)，因为我们使用 `Fin` 作为位向量的内部表示。
  -/
  toFin : Fin (2^w)

/--
构造一个 `BitVec w`，其数值小于 `2^w`。
O(1)，因为位向量以 `Fin` 作为内部表示。
-/
add_decl_doc c087.ofFin

/--
宽度为 `w` 的位向量，当作为整数解释时具有最大值。
-/
noncomputable def c088 := @BitVec.intMax

/--
宽度为 `w` 的位向量，当作为整数解释时具有最小值。
-/
noncomputable def c089 := @BitVec.intMin

/--
用 `w` 个位 `b` 填充位向量。
-/
noncomputable def c090 := @BitVec.fill

/--
返回一个大小为 `n` 的位向量，其中所有位都是 `0`。
-/
noncomputable def c091 := @BitVec.zero

/--
返回一个大小为 `n` 的位向量，其中所有位都是 `1`。
-/
noncomputable def c092 := @BitVec.allOnes

/--
`twoPow w i` 是位向量 `2^i` 如果 `i < w`，否则是 `0`。换句话说，它是 2 的 `i` 次方。

从按位的角度来看，它的第`i`位是`1`，所有其他位都是`0`。
-/
noncomputable def c093 := @BitVec.twoPow

/--
将位向量转换为固定宽度的十六进制数字，具有足够的数字来表示它。

如果 `n` 是 `0`，则返回一个数字。否则，返回 `⌊(n + 3) / 4⌋` 个数字。
-/
noncomputable def c094 := @BitVec.toHex

/--
将位向量解释为以二进制补码形式存储的整数。
-/
noncomputable def c095 := @BitVec.toInt

/--
返回表示位向量的底层 `Nat`。

这是 O(1)，因为 `BitVec` 是围绕 `Nat` 的（零成本）包装器。
-/
noncomputable def c096 := @BitVec.toNat

/--
将 `Bool` 转换为长度为 `1` 的位向量。
-/
noncomputable def c097 := @BitVec.ofBool

/--
将`Bool`列表转换为大端`BitVec`。
-/
noncomputable def c098 := @BitVec.ofBoolListBE

/--
将`Bool`列表转换为小端`BitVec`。
-/
noncomputable def c099 := @BitVec.ofBoolListLE

/--
将整数转换为给定宽度 `n` 的二进制补码位向量，并按需上溢或下溢。

底层 `Nat` 为 `(2^n + (i mod 2^n)) mod 2^n`。将位向量转回 `Int` 时，使用 `BitVec.toInt` 所得值为 `i.bmod (2^n)`。
-/
noncomputable def c100 := @BitVec.ofInt

/--
值为 `i mod 2^n` 的位向量。


标识符中的记号约定：

 * 在标识符中推荐的`0#n`拼写是`zero`（而不是`ofNat_zero`）。

 * 在标识符中推荐的`1#n`拼写是`one`（而不是`ofNat_one`）。
-/
noncomputable def c101 := @BitVec.ofNat

/--
构造 `BitVec`，其值为 `i`，前提是有证明 `i < 2^w`。
-/
noncomputable def c102 := @BitVec.ofNatLT

/--
如果两个自然数 `n` 和 `m` 相等，那么宽度为 `n` 的位向量也是宽度为 `m` 的位向量。

应该优先使用 `x.cast eq` 而不是 `eq ▸ x`，因为有专用的 `simp` 引理可以更一致地简化 `BitVec.cast`。
-/
noncomputable def c103 := @BitVec.cast

/--
位向量的无符号小于或等于。

SMT-LIB 名称：`bvule`。
-/
noncomputable def c104 := @BitVec.ule

/--
针对位向量的有符号小于或等于。

SMT-LIB 名称: `bvsle`。
-/
noncomputable def c105 := @BitVec.sle

/--
位向量的无符号小于。

SMT-LIB 名称：`bvult`。
-/
noncomputable def c106 := @BitVec.ult

/--
用于位向量的有符号小于比较。

SMT-LIB 名称: `bvslt`。

示例：
* `BitVec.slt 6#4 7 = true`
* `BitVec.slt 7#4 8 = false`
-/
noncomputable def c107 := @BitVec.slt

/--
位向量具有可判定的相等性。

这应该通过实例 `DecidableEq (BitVec w)` 使用。
-/
noncomputable def c108 := @BitVec.decEq

/--
计算位向量的哈希值，使用 `mixHash` 组合 64 位字。
-/
noncomputable def c109 := @BitVec.hash

/--
空的位向量。
-/
noncomputable def c110 := @BitVec.nil

/--
在位向量的前面添加一个比特，使用大端序（参见 `append`）。

新位是最高有效位。
-/
noncomputable def c111 := @BitVec.cons

/--
将一个单独的比特附加到位向量的末尾，使用大端顺序（参见 `append`）。也就是说，新的比特是最低有效位。
-/
noncomputable def c112 := @BitVec.concat

/--
将 `x` 的所有位向左移动 `1` 位，并将最低有效位设置为 `b`。

这是`BitVec.concat`的非依赖版本，它不会改变总位宽。
-/
noncomputable def c113 := @BitVec.shiftConcat

/--
将长度为 `w` 的位向量转换为长度为 `v` 的位向量，并根据需要使用 `0` 进行填充。

具体行为取决于起始宽度 `w` 与最终宽度之间的关系
`v`:
 * 如果`v > w`，则进行零扩展；高位用零填充，直到位向量达到`v`
位。
 * 如果 `v = w`，位向量将保持不变返回。
 * 如果 `v < w`，高位将被截断。

`BitVec.setWidth`、`BitVec.zeroExtend` 和 `BitVec.truncate` 是此操作的别名。

SMT-LIB 名称: `zero_extend`。
-/
noncomputable def c114 := @BitVec.truncate

/--
将长度为 `w` 的位向量转换为长度为 `v` 的位向量，并根据需要使用 `0` 进行填充。

具体行为取决于起始宽度 `w` 与最终宽度之间的关系
`v`:
 * 如果`v > w`，则进行零扩展；高位用零填充，直到位向量达到`v`
位。
 * 如果 `v = w`，位向量将保持不变返回。
 * 如果 `v < w`，高位将被截断。

`BitVec.setWidth`、`BitVec.zeroExtend` 和 `BitVec.truncate` 是此操作的别名。

SMT-LIB 名称: `zero_extend`。
-/
noncomputable def c115 := @BitVec.setWidth

/--
通过零扩展将位向量的宽度增加到至少一样大。

这是一个常数时间操作，因为底层的 `Nat` 未被修改；由于新的宽度至少与旧的宽度一样大，不可能发生溢出。
-/
noncomputable def c116 := @BitVec.setWidth'

/--
使用“大端”约定连接两个位向量，即更高有效位的输入在左侧。通常通过 `++` 运算符访问。

SMT-LIB 名称：`concat`。

示例：
 * `0xAB#8 ++ 0xCD#8 = 0xABCD#16`。
-/
noncomputable def c117 := @BitVec.append

/--
连接 `i` 个 `x`，得到长度为 `w * i` 的新向量。
-/
noncomputable def c118 := @BitVec.replicate

/--
反转位向量中的比特位。
-/
noncomputable def c119 := @BitVec.reverse

/--
将位向量中的位向左旋转。

`x` 的所有位都被移到更高的位置，最上面的 `n` 位会回绕以填充腾出的低位。

SMT-LIB 名称：`rotate_left`，不过该运算符使用 `Nat` 位移量。

示例：
 * `(0b0011#4).rotateLeft 3 = 0b1001`
-/
noncomputable def c120 := @BitVec.rotateLeft

/--
将位向量中的位向右旋转。

`x` 的所有位都被移到较低的位置，底部的 `n` 位会环绕以填充腾出的高位。

SMT-LIB 名称：`rotate_right`，不过该运算符使用 `Nat` 位移量。

示例：
 * `rotateRight 0b01001#5 1 = 0b10100`
-/
noncomputable def c121 := @BitVec.rotateRight

/--
返回位向量中最重要的位。
-/
noncomputable def c122 := @BitVec.msb

/--
返回第 `i` 个最高有效位，或返回 `false`（若 `i ≥ w`）。
-/
noncomputable def c123 := @BitVec.getMsbD

/--
返回第`i`个最重要的位。
-/
noncomputable def c124 := @BitVec.getMsb

/--
返回第 `i` 个最高有效位，或返回 `none`（若 `i ≥ w`）。
-/
noncomputable def c125 := @BitVec.getMsb?

/--
返回第 `i` 个最低有效位，或返回 `false`（若 `i ≥ w`）。
-/
noncomputable def c126 := @BitVec.getLsbD

/--
返回第`i`个最低有效位。
-/
noncomputable def c127 := @BitVec.getLsb

/--
返回第 `i` 个最低有效位，或返回 `none`（若 `i ≥ w`）。
-/
noncomputable def c128 := @BitVec.getLsb?

/--
从位向量中提取从 `hi` 到 `lo`（包括两者）的位，如果有必要，会隐式地进行零扩展。

生成的位向量大小为 `hi - lo + 1`。

SMT-LIB 名称：`extract`。
-/
noncomputable def c129 := @BitVec.extractLsb

/--
提取第 `start` 位到第 `start + len - 1` 位，来源是大小为 `n` 的位向量，并得到大小为 `len` 的新位向量。如果 `start + len > n`，则对位向量进行零扩展。
-/
noncomputable def c130 := @BitVec.extractLsb'

/--
位向量的按位与。通常通过 `&&&` 运算符访问。

SMT-LIB 名称：`bvand`。

示例：
* `0b1010#4 &&& 0b0110#4 = 0b0010#4`
-/
noncomputable def c131 := @BitVec.and

/--
位向量的按位或。通常通过 `|||` 运算符访问。

SMT-LIB 名称：`bvor`。

示例：
* `0b1010#4 ||| 0b0110#4 = 0b1110#4`
-/
noncomputable def c132 := @BitVec.or

/--
位向量的按位取反。通常通过 `~~~` 前缀运算符访问。

SMT-LIB 名称: `bvnot`。

示例：
* `~~~(0b0101#4) == 0b1010`
-/
noncomputable def c133 := @BitVec.not

/--
位向量的按位异或。通常通过 `^^^` 操作符访问。

SMT-LIB 名称：`bvxor`。

示例：
* `0b1010#4 ^^^ 0b0110#4 = 0b1100#4`
-/
noncomputable def c134 := @BitVec.xor

/--
将长度为 `w` 的位向量转换为长度为 `v` 的位向量，并根据需要使用 `0` 进行填充。

具体行为取决于起始宽度 `w` 与最终宽度之间的关系
`v`:
 * 如果`v > w`，则进行零扩展；高位用零填充，直到位向量达到`v`
位。
 * 如果 `v = w`，位向量将保持不变返回。
 * 如果 `v < w`，高位将被截断。

`BitVec.setWidth`、`BitVec.zeroExtend` 和 `BitVec.truncate` 是此操作的别名。

SMT-LIB 名称: `zero_extend`。
-/
noncomputable def c135 := @BitVec.zeroExtend

/--
将长度为 `w` 的位向量转换为长度为 `v` 的位向量，并根据需要使用最高有效位的值进行填充。

如果`x`是一个空位向量，则符号被视为零。

SMT-LIB 名称：`sign_extend`。
-/
noncomputable def c136 := @BitVec.signExtend

/--
将位向量向右移动。这是逻辑右移——高位用零填充。

作为一种数字运算，这等同于`x / 2^s`，向下取整。

SMT-LIB 名称：`bvlshr`，只是这个运算符使用了一个 `Nat` 的移位值。
-/
noncomputable def c137 := @BitVec.ushiftRight

/--
将位向量向右移动。这是算术右移——高位用最高有效位的值填充。

作为一种数值运算，这等同于 `x.toInt >>> s`。

SMT-LIB 名称：`bvashr`，只是这个运算符使用了一个 `Nat` 的移位值。
-/
noncomputable def c138 := @BitVec.sshiftRight

/--
将位向量向右移动。这是算术右移——高位用最高有效位的值填充。

作为一种数值运算，这等同于 `a.toInt >>> s.toNat`。

SMT-LIB 名称: `bvashr`。
-/
noncomputable def c139 := @BitVec.sshiftRight'

/--
将位向量向左移动。低位填充为零。作为数值运算，这等同于 `x * 2^s` 对 `2^n` 取模。

SMT-LIB 名称：`bvshl`，只是这个运算符使用了一个 `Nat` 的移位值。
-/
noncomputable def c140 := @BitVec.shiftLeft

/--
返回 `zeroExtend (w+n) x <<< n` 而不需要计算 `x % 2^(2+n)`。
-/
noncomputable def c141 := @BitVec.shiftLeftZeroExtend

/--
将两个位向量相加。这可以解释为带符号或无符号加法，模 `2^n`。
通常通过 `+` 运算符访问。

SMT-LIB 名称：`bvadd`。
-/
noncomputable def c142 := @BitVec.add

/--
将一个位向量从另一个位向量中减去。这可以解释为有符号或无符号的减法，模 `2^n`。通常通过 `-` 运算符访问。

-/
noncomputable def c143 := @BitVec.sub

/--
将两个位向量相乘。这可以解释为有符号或无符号乘法，模 `2^n`。通常通过`*`运算符访问。

SMT-LIB 名称：`bvmul`。
-/
noncomputable def c144 := @BitVec.mul

/--
使用 Lean 约定的位向量无符号除法，其中除以零返回零。通常通过 `/` 操作符访问。
-/
noncomputable def c145 := @BitVec.udiv

/--
使用 [SMT-LIB 约定](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml) 对位向量进行无符号除法，其中除以零返回 `BitVector.allOnes n`。

SMT-LIB 名称：`bvudiv`。
-/
noncomputable def c146 := @BitVec.smtUDiv

/--
位向量的无符号取模。通常通过 `%` 操作符访问。

SMT-LIB 名称：`bvurem`。
-/
noncomputable def c147 := @BitVec.umod

/--
检查`x`和`y`的相加是否导致*无符号*溢出。

SMT-LIB 名称：`bvuaddo`。
-/
noncomputable def c148 := @BitVec.uaddOverflow

/--
检查 `x` 和 `y` 的减法是否导致*无符号*溢出。

SMT-Lib 名称：`bvusubo`。
-/
noncomputable def c149 := @BitVec.usubOverflow

/--
返回有符号位向量的绝对值。
-/
noncomputable def c150 := @BitVec.abs

/--
位向量的取反。这可以解释为模 `2^n` 的有符号或无符号取反。
通常通过 `-` 前缀运算符访问。

SMT-LIB 名称：`bvneg`。
-/
noncomputable def c151 := @BitVec.neg

/--
位向量的带符号 T 除法（采用向零截断的舍入约定）。此函数遵循 Lean 的约定：除以零返回零。

示例：
* `(7#4).sdiv 2 = 3#4`
* `(-8#4).sdiv 2 = -4#4`
* `(5#4).sdiv -2 = -2#4`
* `(-7#4).sdiv (-2) = 3#4`
-/
noncomputable def c152 := @BitVec.sdiv

/--
使用 SMT-LIB 对位向量进行有符号除法，使用 [SMT-LIB 约定](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)，其中除以零返回 `BitVector.allOnes n`。

具体来说，`x.smtSDiv 0 = if x >= 0 then -1 else 1`

SMT-LIB 名称：`bvsdiv`。
-/
noncomputable def c153 := @BitVec.smtSDiv

/--
有符号除法的余数向负无穷舍入。

SMT-LIB 名称：`bvsmod`。
-/
noncomputable def c154 := @BitVec.smod

/--
带符号除法取零舍入的余数。

SMT-LIB 名称：`bvsrem`。
-/
noncomputable def c155 := @BitVec.srem

/--
检查将 `x` 和 `y` 相加是否导致*有符号*溢出，将 `x` 和 `y` 视为二进制补码有符号位向量。

SMT-LIB 名称：`bvsaddo`。
-/
noncomputable def c156 := @BitVec.saddOverflow

/--
检查 `x` 与 `y` 相减是否会导致*有符号*溢出，将 `x` 和 `y` 视为二进制补码有符号位向量。

SMT-Lib 名称：`bvssubo`。
-/
noncomputable def c157 := @BitVec.ssubOverflow

/--
使用函数 `f` 为每一位迭代计算状态，并从初始状态 `s` 开始，从而构造位向量。每一步都把前一状态和当前位索引传给 `f`，由它生成一个位以及下一状态。这些位随后组合成最终的位向量。

它生成状态序列 `[s_0, s_1 .. s_w]` 和位向量 `v`，其中 `f i s_i =
(s_{i+1}, b_i)`，并且 `b_i` 表示第 `i` 个最低有效位，它位于 `v` 中（例如 `getLsb v i = b_i`）。

定理 `iunfoldr_replace` 可将 `BitVec.iunfoldr` 的使用替换为更便于推理的声明式规范。
-/
noncomputable def c158 := @BitVec.iunfoldr

/--
给定一个函数 `state`，它为每一个潜在的迭代次数提供正确的状态，以及一个从正确初始状态计算这些状态的函数，将 `BitVec.iunfoldr f` 应用于初始状态的结果就是与位向量宽度对应的状态，配对着由每个计算得出的比特组成的位向量。

这个定理可以用来证明使用 `BitVec.iunfoldr` 定义的函数的性质。
-/
noncomputable def c159 := @BitVec.iunfoldr_replace

/--
通过连锁进位加法器实现的按位加法。
-/
noncomputable def c160 := @BitVec.adc

/--
用于按位相加的进位函数。
-/
noncomputable def c161 := @BitVec.adcb

/--
如果第 `i` 个进位在计算 `x + y + c` 时为真，则 carry i x y c 返回 true。
-/
noncomputable def c162 := @BitVec.carry

/--
一个描述乘法为重复加法的递推关系。

这个函数对于位爆炸乘法很有用。
-/
noncomputable def c163 := @BitVec.mulRec

/--
用于位爆炸的除法递归定义，以移位-减法电路为基础。
-/
noncomputable def c164 := @BitVec.divRec

/--
除法算法的一个回合。它尝试执行减位移操作。

这应仅在 `r.msb = false` 时调用，因此不会溢出。
-/
noncomputable def c165 := @BitVec.divSubtractShift

/--
将 `x` 左移前 `n` 位的 `y` 所表示的位数。

定理 `BitVec.shiftLeft_eq_shiftLeftRec` 证明 `(x <<< y)` 与 `BitVec.shiftLeftRec x y` 等价。

结合方程 `BitVec.shiftLeftRec_zero` 和 `BitVec.shiftLeftRec_succ`，可将 `BitVec.shiftLeft` 展开为用于位级展开的电路。
-/
noncomputable def c166 := @BitVec.shiftLeftRec

/--
将 `x` 以算术（有符号）方式右移前 `n` 位的 `y` 所表示的位数。

定理 `BitVec.sshiftRight_eq_sshiftRightRec` 证明 `(x.sshiftRight y)` 与 `BitVec.sshiftRightRec x y` 等价。结合方程 `BitVec.sshiftRightRec_zero` 和 `BitVec.sshiftRightRec_succ`，可将 `BitVec.sshiftRight` 展开为用于位级展开的电路。
-/
noncomputable def c167 := @BitVec.sshiftRightRec

/--
将 `x` 以逻辑方式右移前 `n` 位的 `y` 所表示的位数。

定理 `BitVec.shiftRight_eq_ushiftRightRec` 证明 `(x >>> y)` 与 `BitVec.ushiftRightRec` 等价。

结合方程 `BitVec.ushiftRightRec_zero` 和 `BitVec.ushiftRightRec_succ`，可将 `BitVec.ushiftRight` 展开为用于位级展开的电路。
-/
noncomputable def c168 := @BitVec.ushiftRightRec

/--
`α` 中具有闭下界和开上界的区间。

`a...b` 或 `a...<b` 表示所有大于等于 `a : α` 且小于 `b : α` 的值。这是 `Rco.mk a b` 的记法。
-/
structure c169 (α : Type u) where
  /--
  范围的下限。`lower` 包含在范围内。
  -/
  lower : α
  /--
  范围的上限。`upper` 不包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c170 := @Std.Rco.iter

/--
以升序将给定的左闭右开区间的元素作为数组返回。
-/
noncomputable def c171 := @Std.Rco.toArray

/--
将给定的左闭右开范围的元素作为列表按升序返回。
-/
noncomputable def c172 := @Std.Rco.toList

/--
返回给定左闭右开区间中包含的元素数量。
-/
noncomputable def c173 := @Std.Rco.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable` 和 `LawfulUpwardEnumerableLT` 实例时返回一个有意义的值。
-/
noncomputable def c174 := @Std.Rco.isEmpty

/--
具有闭合上下界的`α`的一系列元素。

`a...=b` 是所有大于或等于 `a : α` 并且小于或等于 `b : α` 的值的范围。这是 `Rcc.mk a b` 的表示法。
-/
structure c175 (α : Type u) where
  /--
  范围的下限。`lower` 包含在范围内。
  -/
  lower : α
  /--
  范围的上限。`upper` 包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c176 := @Std.Rcc.iter

/--
以升序将给定闭区间的元素作为数组返回。
-/
noncomputable def c177 := @Std.Rcc.toArray

/--
以升序将给定闭区间的元素作为列表返回。
-/
noncomputable def c178 := @Std.Rcc.toList

/--
返回给定闭区间中包含的元素数量。
-/
noncomputable def c179 := @Std.Rcc.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable` 和 `LawfulUpwardEnumerableLE` 实例时返回一个有意义的值。
-/
noncomputable def c180 := @Std.Rcc.isEmpty

/--
`α` 中具有闭下界、向上无界的区间。

`a...*` 表示所有大于等于 `a : α` 的值。这是 `Rci.mk a` 的记法。
-/
structure c181 (α : Type u) where
  /--
  范围的下限。`lower` 包含在范围内。
  -/
  lower : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c182 := @Std.Rci.iter

/--
以升序返回给定左闭右无界范围的元素数组。
-/
noncomputable def c183 := @Std.Rci.toArray

/--
将给定的左闭右开区间的元素作为列表按升序返回。
-/
noncomputable def c184 := @Std.Rci.toList

/--
返回给定左闭右开区间中包含的元素数量。
-/
noncomputable def c185 := @Std.Rci.size

/--
检查范围是否包含任何值。
此函数存在是为了完整性，并且总是返回 false：
闭合的下界包含在范围内，因此左闭右无界的范围永远不为空。
-/
noncomputable def c186 := @Std.Rci.isEmpty

/--
`α` 中下界和上界均为开的区间。

`a<...b` 或 `a<...<b` 表示所有大于 `a : α` 且小于 `b : α` 的值。这是 `Roo.mk a b` 的记法。
-/
structure c187 (α : Type u) where
  /--
  范围的下界。`lower`不包含在范围内。
  -/
  lower : α
  /--
  范围的上限。`upper` 不包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c188 := @Std.Roo.iter

/--
以升序将给定开区间的元素作为数组返回。
-/
noncomputable def c189 := @Std.Roo.toArray

/--
以升序将给定开区间的元素作为列表返回。
-/
noncomputable def c190 := @Std.Roo.toList

/--
返回给定开区间中包含的元素数量。
-/
noncomputable def c191 := @Std.Roo.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable` 和 `LawfulUpwardEnumerableLT` 实例时返回一个有意义的值。
-/
noncomputable def c192 := @Std.Roo.isEmpty

/--
`α` 的一系列元素，具有开下界和闭上界。

`a<...=b` 是所有大于 `a : α` 且小于或等于 `b : α` 的值的范围。这是 `Roc.mk a b` 的表示法。
-/
structure c193 (α : Type u) where
  /--
  范围的下界。`lower`不包含在范围内。
  -/
  lower : α
  /--
  范围的上限。`upper` 包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c194 := @Std.Roc.iter

/--
以升序将给定的左开右闭区间的元素作为数组返回。
-/
noncomputable def c195 := @Std.Roc.toArray

/--
以升序将给定的左开右闭区间的元素作为列表返回。
-/
noncomputable def c196 := @Std.Roc.toList

/--
返回给定左开右闭区间中包含的元素数量。
-/
noncomputable def c197 := @Std.Roc.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable` 和 `LawfulUpwardEnumerableLT` 实例时返回一个有意义的值。
-/
noncomputable def c198 := @Std.Roc.isEmpty

/--
`α` 中具有开下界、向上无界的区间。

`a<...*` 表示所有大于 `a : α` 的值。这是 `Roi.mk a` 的记法。
-/
structure c199 (α : Type u) where
  /--
  范围的下界。`lower`不包含在范围内。
  -/
  lower : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c200 := @Std.Roi.iter

/--
以升序将给定的左开右无界范围的元素作为数组返回。
-/
noncomputable def c201 := @Std.Roi.toArray

/--
将给定的左开右无界区间的元素作为列表按升序返回。
-/
noncomputable def c202 := @Std.Roi.toList

/--
返回给定左开右无限区间中包含的元素数量。
-/
noncomputable def c203 := @Std.Roi.size

/--
检查范围内是否包含任何值。

此函数在给定 `LawfulUpwardEnumerable` 实例时返回一个有意义的值。
-/
noncomputable def c204 := @Std.Roi.isEmpty

/--
`α` 中具有开上界、向下无界的区间。

`*...b` 或 `*...<b` 表示所有小于 `b : α` 的值。这是 `Rio.mk b` 的记法。
-/
structure c205 (α : Type u) where
  /--
  范围的上限。`upper` 不包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c206 := @Std.Rio.iter

/--
以升序将给定闭区间的元素作为数组返回。
-/
noncomputable def c207 := @Std.Rio.toArray

/--
以升序将给定闭区间的元素作为列表返回。
-/
noncomputable def c208 := @Std.Rio.toList

/--
返回给定闭区间中包含的元素数量。
-/
noncomputable def c209 := @Std.Rio.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable`、`LawfulUpwardEnumerableLT` 和 `LawfulUpwardEnumerableLeast?` 实例时返回一个有意义的值。
-/
noncomputable def c210 := @Std.Rio.isEmpty

/--
`α` 中具有闭上界、向下无界的区间。

`*...=b` 表示所有小于等于 `b : α` 的值。这是 `Ric.mk b` 的记法。
-/
structure c211 (α : Type u) where
  /--
  范围的上限。`upper` 包含在范围内。
  -/
  upper : α

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c212 := @Std.Ric.iter

/--
以升序将给定闭区间的元素作为数组返回。
-/
noncomputable def c213 := @Std.Ric.toArray

/--
以升序将给定闭区间的元素作为列表返回。
-/
noncomputable def c214 := @Std.Ric.toList

/--
返回给定闭区间中包含的元素数量。
-/
noncomputable def c215 := @Std.Ric.size

/--
检查范围是否包含任何值。该函数存在是为了完整性，并且总是返回 false：闭合的上界包含在范围内，因此左无界右闭合的范围从不为空。
-/
noncomputable def c216 := @Std.Ric.isEmpty

/--
`α` 所有元素构成的全区间。它唯一的值是区间 `*...*`，这是 `Rii.mk` 的记法。
-/
structure c217 (α : Type u) : Type where

/--
返回给定范围的迭代器。该迭代器将按递增顺序生成范围内的元素。
-/
noncomputable def c218 := @Std.Rii.iter

/--
以升序将给定完整范围的元素作为数组返回。
-/
noncomputable def c219 := @Std.Rii.toArray

/--
以升序将给定完整范围的元素作为列表返回。
-/
noncomputable def c220 := @Std.Rii.toList

/--
返回完整范围中包含的元素数量。
-/
noncomputable def c221 := @Std.Rii.size

/--
检查范围内是否包含任何值。

该函数在给定 `LawfulUpwardEnumerable` 和 `LawfulUpwardEnumerableLeast?` 实例时返回一个有意义的值。
-/
noncomputable def c222 := @Std.Rii.isEmpty

/--
此类型类提供函数 `succ? : α → Option α`，用于计算 `α` 中元素的后继；不存在后继时返回 none。
它还提供函数 `succMany?`，用于计算第 `n` 个后继。

`succ?` 应当无环：任何元素都不是自身的传递后继。如果 `α` 有序，则每个大于 `a : α` 的元素都应是 `a` 的传递后继。这些性质以及 `succ?` 与 `succMany?` 的兼容性由类型类 `LawfulUpwardEnumerable`、`LawfulUpwardEnumerableLE` 和 `LawfulUpwardEnumerableLT` 编码。

-/
class c223 (α : Type u) where
  /--
  将 `α` 中的元素映射到其后继；若不存在后继，则返回空值。
  -/
  succ? : α → Option α
  /--
  将 `α` 中的元素映射到其第 `n` 个后继；若该后继不存在，则返回空值。
  这在语义上应表现得像重复应用 `succ?`，但可能更高效。

  `LawfulUpwardEnumerable` 确保与 `succ?` 的兼容性。

  如果在 `UpwardEnumerable` 实例中没有提供其他实现，`succMany?` 会重复应用 `succ?`。
  -/
  succMany? : Nat → α → Option α

/--
按照 `UpwardEnumerable.LE`，`a` 小于等于 `b`，当且仅当 `b` 等于 `a` 或是 `a` 的传递后继。
-/
noncomputable def c224 := @Std.PRange.UpwardEnumerable.LE

/--
按照 `UpwardEnumerable.LT`，`a` 小于 `b`，当且仅当 `b` 是 `a` 的真传递后继。“真”表示 `b` 是第 `n` 个后继，起点为 `a`，其中 `n > 0`。

给定 `LawfulUpwardEnumerable α`，`α` 中没有元素小于自身。
-/
noncomputable def c225 := @Std.PRange.UpwardEnumerable.LT

/--
这种类型类确保 `UpwardEnumerable α` 实例行为良好。
-/
class c226 (α : Type u) [Std.PRange.UpwardEnumerable α] : Prop where
  /--
  后继链中不存在环。
  -/
  ne_of_lt : ∀ a b : α, Std.PRange.UpwardEnumerable.LT a b → a ≠ b
  /--
  `0` 阶后继对于 `a` 就是 `a` 自身。
  -/
  succMany?_zero : ∀ a : α, Std.PRange.succMany? 0 a = some a
  /--
  `n + 1` 阶后继对于 `a`，等于其第 `n` 阶后继的后继，前提是这些
  后继确实存在。
  -/
  succMany?_add_one : ∀ (n : Nat) (a : α), Std.PRange.succMany? (n + 1) a = (Std.PRange.succMany? n a).bind Std.PRange.succ?

/--
类型类 `Least? α` 可选择性地提供 `α`、`least? : Option α` 的最小元素。

这种类型类的主要用例是将其与 `UpwardEnumerable` 结合使用，以获得 `α` 所有元素的（可能是无限的）升序枚举。
-/
class c227 (α : Type u) where
  /--
  返回 `α` 中最小的元素；如果 `α` 为空，则返回空值。

  仅允许空类型定义 `least? := none`。如果 `α` 有序且非空，则 `least?` 的值应为根据 `α` 上的顺序确定的最小元素。
  -/
  least? : Option α

/--
这个命题类型类确保 `UpwardEnumerable.succ?` 永远不会返回 `none`。换句话说，它确保总是会有一个后继。
-/
class c228 (α : Type u) [Std.PRange.UpwardEnumerable α] : Prop where
  /--
  `α` 的每个元素都有一个后继。
  -/
  isSome_succ? : ∀ a : α, (Std.PRange.succ? a).isSome = true

/--
这个命题类型类确保 `UpwardEnumerable.succ?` 是单射的。
-/
class c229 (α : Type u) [Std.PRange.UpwardEnumerable α] : Prop where
  /--
  `UpwardEnumerable.succ?` 在 `α` 上的实现是单射函数。
  -/
  eq_of_succ?_eq : ∀ a b : α, Std.PRange.succ? a = Std.PRange.succ? b → a = b

/--
这种类型类确保右无界的范围（即对于界 `a`、`a...*`、`a<...*` 和 `*...*`）总是有限的。这是许多函数和实例的前提条件，例如 `Rci.toList` 或 `ForIn'`。
-/
class c230 (α : Type u) [Std.PRange.UpwardEnumerable α] : Prop where
  /--
  对于每个元素 `init`，存在一个后继链，最终得到一个没有后继的元素。
  -/
  finite : ∀ init : α, ∃ n : Nat, Std.PRange.succMany? n init = none

/--
此类型类为下界无界的区间（`Ric.size`、`Rio.size` 和 `Rii.size`）提供大小函数。

返回的大小应等于 `toList` 返回的元素数量。此条件由类型类 `LawfulHasSize` 描述。
-/
class c231 (α : Type u) where
  /--
  返回从 `lo` 开始满足给定上限的元素数量。
  -/
  size : α → Nat

/--
此类型类确保右闭区间（即，对边界 `a` 和 `b` 而言，`a...=b`、`a<...=b` 与 `*...=b`）总是有限。
这是 `Rcc.toList`、`ForIn'` 等许多函数和实例的前提。
-/
class c232 (α : Type u) [Std.PRange.UpwardEnumerable α] [LE α] : Prop where
  /--
  对于每一对元素 `init` 和 `hi`，存在一个后继链，最终得到一个要么没有后继要么大于 `hi` 的元素。
  -/
  finite : ∀ init hi : α, ∃ n : Nat, (Std.PRange.succMany? n init).elim True (fun x => ¬ x ≤ hi)

/--
此类型类为具有闭下界的区间（`Rcc.size`、`Rco.size` 和 `Rci.size`）提供大小函数。

返回的大小应等于 `toList` 返回的元素数量。此条件由类型类 `LawfulHasSize` 描述。
-/
class c233 (α : Type u) where
  /--
  返回从 `lo` 开始满足给定上限的元素数量。
  -/
  size : α → α → Nat

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中的左闭右开区间指定。

结果切片的类型为 `γ`。
-/
class c234 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取为从 `range.lower`（含）到 `range.upper`（不含）的切片。
  -/
  mkSlice : α → Std.Rco β → γ

/--
这个类型类表示如何获取`α`中元素在索引类型`β`范围上的切片，这些范围是闭合的。

结果切片的类型是 `γ`。
-/
class c235 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取为从 `range.lower` 到 `range.upper`（两端均含）的切片。
  -/
  mkSlice : α → Std.Rcc β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中左闭、右端无界的区间指定。

结果切片的类型为 `γ`。
-/
class c236 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  对 `carrier` 从 `range.lower`（含）开始切取。
  -/
  mkSlice : α → Std.Rci β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中的开区间指定。

结果切片的类型为 `γ`。
-/
class c237 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取为从 `range.lower` 到 `range.upper`（两端均不含）的切片。
  -/
  mkSlice : α → Std.Roo β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中的左开右闭区间指定。

结果切片的类型为 `γ`。
-/
class c238 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取为从 `range.lower`（不含）到 `range.upper`（含）的切片。
  -/
  mkSlice : α → Std.Roc β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中左开、右端无界的区间指定。

结果切片的类型为 `γ`。
-/
class c239 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  对 `carrier` 从 `range.lower`（不含）开始切取。
  -/
  mkSlice : α → Std.Roi β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中左端无界、右开的区间指定。

结果切片的类型为 `γ`。
-/
class c240 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取到 `range.upper`（不含）为止。
  -/
  mkSlice : α → Std.Rio β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中左端无界、右闭的区间指定。

结果切片的类型为 `γ`。
-/
class c241 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  将 `carrier` 切取到 `range.upper`（含）为止。
  -/
  mkSlice : α → Std.Ric β → γ

/--
此类型类说明如何取得 `α` 中元素；这些切片由索引类型 `β` 中的全区间指定。

结果切片的类型为 `γ`。
-/
class c242 (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  /--
  切取整个 `carrier`，不设边界。
  -/
  mkSlice : α → Std.Rii β → γ

end Manual.ZhDocString.Ch19Ch20.G8
