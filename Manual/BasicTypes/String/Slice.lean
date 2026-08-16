/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G8
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "字符串切片" =>
%%%
tag := "string-api-slice"
%%%

{zhdocstring String.Slice Manual.ZhDocString.Ch19Ch20.G8.c001}

{zhdocstring String.toSlice Manual.ZhDocString.Ch19Ch20.G8.c002}

{zhdocstring String.sliceFrom Manual.ZhDocString.Ch19Ch20.G8.c003}

{zhdocstring String.sliceTo Manual.ZhDocString.Ch19Ch20.G8.c004}

{zhdocstring String.Slice.Pos Manual.ZhDocString.Ch19Ch20.G8.c005}

# 接口参考

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference"
%%%
## 复制

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Copying"
%%%
{zhdocstring String.Slice.copy Manual.ZhDocString.Ch19Ch20.G8.c006}

## 大小

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Size"
%%%
{zhdocstring String.Slice.isEmpty Manual.ZhDocString.Ch19Ch20.G8.c007}

{zhdocstring String.Slice.utf8ByteSize Manual.ZhDocString.Ch19Ch20.G8.c008}

## 边界

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Boundaries"
%%%
{zhdocstring String.Slice.pos Manual.ZhDocString.Ch19Ch20.G8.c009}

{zhdocstring String.Slice.pos! Manual.ZhDocString.Ch19Ch20.G8.c010}

{zhdocstring String.Slice.pos? Manual.ZhDocString.Ch19Ch20.G8.c011}

{zhdocstring String.Slice.startPos Manual.ZhDocString.Ch19Ch20.G8.c012}

{zhdocstring String.Slice.endPos Manual.ZhDocString.Ch19Ch20.G8.c013}

{zhdocstring String.Slice.rawEndPos Manual.ZhDocString.Ch19Ch20.G8.c014}


### 调整

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Boundaries--Adjustment"
%%%
{zhdocstring String.Slice.sliceFrom Manual.ZhDocString.Ch19Ch20.G8.c015}

{zhdocstring String.Slice.sliceTo Manual.ZhDocString.Ch19Ch20.G8.c016}

{zhdocstring String.Slice.slice Manual.ZhDocString.Ch19Ch20.G8.c017}

{zhdocstring String.Slice.slice! Manual.ZhDocString.Ch19Ch20.G8.c018}

{zhdocstring String.Slice.drop Manual.ZhDocString.Ch19Ch20.G8.c019}

{zhdocstring String.Slice.dropEnd Manual.ZhDocString.Ch19Ch20.G8.c020}

{zhdocstring String.Slice.dropEndWhile Manual.ZhDocString.Ch19Ch20.G8.c021}

{zhdocstring String.Slice.dropPrefix Manual.ZhDocString.Ch19Ch20.G8.c022}

{zhdocstring String.Slice.dropPrefix? Manual.ZhDocString.Ch19Ch20.G8.c023}

{zhdocstring String.Slice.dropSuffix Manual.ZhDocString.Ch19Ch20.G8.c024}

{zhdocstring String.Slice.dropSuffix? Manual.ZhDocString.Ch19Ch20.G8.c025}

{zhdocstring String.Slice.dropWhile Manual.ZhDocString.Ch19Ch20.G8.c026}

{zhdocstring String.Slice.take Manual.ZhDocString.Ch19Ch20.G8.c027}

{zhdocstring String.Slice.takeEnd Manual.ZhDocString.Ch19Ch20.G8.c028}

{zhdocstring String.Slice.takeEndWhile Manual.ZhDocString.Ch19Ch20.G8.c029}

{zhdocstring String.Slice.takeWhile Manual.ZhDocString.Ch19Ch20.G8.c030}

## 字符

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Characters"
%%%
{zhdocstring String.Slice.front Manual.ZhDocString.Ch19Ch20.G8.c031}

{zhdocstring String.Slice.front? Manual.ZhDocString.Ch19Ch20.G8.c032}

{zhdocstring String.Slice.back Manual.ZhDocString.Ch19Ch20.G8.c033}

{zhdocstring String.Slice.back? Manual.ZhDocString.Ch19Ch20.G8.c034}

## 字节

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Bytes"
%%%
{zhdocstring String.Slice.getUTF8Byte Manual.ZhDocString.Ch19Ch20.G8.c035}

{zhdocstring String.Slice.getUTF8Byte! Manual.ZhDocString.Ch19Ch20.G8.c036}

## 位置

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Positions"
%%%
{zhdocstring String.Slice.posGE Manual.ZhDocString.Ch19Ch20.G8.c037}

{zhdocstring String.Slice.posGT Manual.ZhDocString.Ch19Ch20.G8.c038}

## 搜索

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Searching"
%%%
{zhdocstring String.Slice.contains Manual.ZhDocString.Ch19Ch20.G8.c039}

{zhdocstring String.Slice.startsWith Manual.ZhDocString.Ch19Ch20.G8.c040}

{zhdocstring String.Slice.endsWith Manual.ZhDocString.Ch19Ch20.G8.c041}

{zhdocstring String.Slice.all Manual.ZhDocString.Ch19Ch20.G8.c042}

{zhdocstring String.Slice.find? Manual.ZhDocString.Ch19Ch20.G8.c043}

{zhdocstring String.Slice.revFind? Manual.ZhDocString.Ch19Ch20.G8.c044}

## 操作

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Manipulation"
%%%
{zhdocstring String.Slice.split Manual.ZhDocString.Ch19Ch20.G8.c045}

{zhdocstring String.Slice.splitInclusive Manual.ZhDocString.Ch19Ch20.G8.c046}

{zhdocstring String.Slice.lines Manual.ZhDocString.Ch19Ch20.G8.c047}

{zhdocstring String.Slice.trimAscii Manual.ZhDocString.Ch19Ch20.G8.c048}

{zhdocstring String.Slice.trimAsciiEnd Manual.ZhDocString.Ch19Ch20.G8.c049}

{zhdocstring String.Slice.trimAsciiStart Manual.ZhDocString.Ch19Ch20.G8.c050}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Iteration"
%%%
{zhdocstring String.Slice.chars Manual.ZhDocString.Ch19Ch20.G8.c051}

{zhdocstring String.Slice.revChars Manual.ZhDocString.Ch19Ch20.G8.c052}

{zhdocstring String.Slice.positions Manual.ZhDocString.Ch19Ch20.G8.c053}

{zhdocstring String.Slice.revPositions Manual.ZhDocString.Ch19Ch20.G8.c054}

{zhdocstring String.Slice.bytes Manual.ZhDocString.Ch19Ch20.G8.c055}

{zhdocstring String.Slice.revBytes Manual.ZhDocString.Ch19Ch20.G8.c056}

{zhdocstring String.Slice.revSplit Manual.ZhDocString.Ch19Ch20.G8.c057}

{zhdocstring String.Slice.foldl Manual.ZhDocString.Ch19Ch20.G8.c058}

{zhdocstring String.Slice.foldr Manual.ZhDocString.Ch19Ch20.G8.c059}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Conversions"
%%%
{zhdocstring String.Slice.isNat Manual.ZhDocString.Ch19Ch20.G8.c060}

{zhdocstring String.Slice.toNat! Manual.ZhDocString.Ch19Ch20.G8.c061}

{zhdocstring String.Slice.toNat? Manual.ZhDocString.Ch19Ch20.G8.c062}


## 相等性

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--API-Reference--Equality"
%%%
{zhdocstring String.Slice.beq Manual.ZhDocString.Ch19Ch20.G8.c063}

{zhdocstring String.Slice.eqIgnoreAsciiCase Manual.ZhDocString.Ch19Ch20.G8.c064}


# 模式

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--Patterns"
%%%
字符串切片支持广义的搜索模式。
许多切片操作并不只针对字符或字符串定义，而是接受任意模式。
通过为本节中的类定义实例，可以让新的类型也成为模式。
Lean 标准库提供了实例，使下列类型既可用于向前搜索，也可用于向后搜索：

:::table +header
* * 模式类型
  * 含义
* * {name}`Char`
  * 匹配给定字符
*
  * {lean}`Char → Bool`
  * 匹配任意满足该谓词的字符
* * {lean}`String`
  * 匹配给定字符串的出现位置
* * {lean}`String.Slice`
  * 匹配该切片所表示字符串的出现位置
:::

{zhdocstring String.Slice.Pattern.ToForwardSearcher Manual.ZhDocString.Ch19Ch20.G8.c065}

{zhdocstring String.Slice.Pattern.ForwardPattern Manual.ZhDocString.Ch19Ch20.G8.c066}

{zhdocstring String.Slice.Pattern.ToBackwardSearcher Manual.ZhDocString.Ch19Ch20.G8.c067}

{zhdocstring String.Slice.Pattern.BackwardPattern Manual.ZhDocString.Ch19Ch20.G8.c068 +allowMissing}

# 位置

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--Positions"
%%%
## 查找

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--Positions--Lookups"
%%%
由于切片位置保留了对其来源切片的引用，因此可以借助它们查找单个字符或字节。

{zhdocstring String.Slice.Pos.byte Manual.ZhDocString.Ch19Ch20.G8.c069}

{zhdocstring String.Slice.Pos.get Manual.ZhDocString.Ch19Ch20.G8.c070}

{zhdocstring String.Slice.Pos.get! Manual.ZhDocString.Ch19Ch20.G8.c071}

{zhdocstring String.Slice.Pos.get? Manual.ZhDocString.Ch19Ch20.G8.c072}

## 递增与递减

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--Positions--Incrementing-and-Decrementing"
%%%
{zhdocstring String.Slice.Pos.prev Manual.ZhDocString.Ch19Ch20.G8.c073}

{zhdocstring String.Slice.Pos.prev! Manual.ZhDocString.Ch19Ch20.G8.c074}

{zhdocstring String.Slice.Pos.prev? Manual.ZhDocString.Ch19Ch20.G8.c075}

{zhdocstring String.Slice.Pos.prevn Manual.ZhDocString.Ch19Ch20.G8.c076}

{zhdocstring String.Slice.Pos.next Manual.ZhDocString.Ch19Ch20.G8.c077}

{zhdocstring String.Slice.Pos.next! Manual.ZhDocString.Ch19Ch20.G8.c078}

{zhdocstring String.Slice.Pos.next? Manual.ZhDocString.Ch19Ch20.G8.c079}

{zhdocstring String.Slice.Pos.nextn Manual.ZhDocString.Ch19Ch20.G8.c080}

## 其他字符串或切片

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--String-Slices--Positions--Other-Strings-or-Slices"
%%%
{zhdocstring String.Slice.Pos.cast Manual.ZhDocString.Ch19Ch20.G8.c081}

{zhdocstring String.Slice.Pos.ofSlice Manual.ZhDocString.Ch19Ch20.G8.c082}

{zhdocstring String.Slice.Pos.str Manual.ZhDocString.Ch19Ch20.G8.c083}

{zhdocstring String.Slice.Pos.copy Manual.ZhDocString.Ch19Ch20.G8.c084}

{zhdocstring String.Slice.Pos.ofSliceFrom Manual.ZhDocString.Ch19Ch20.G8.c085}

{zhdocstring String.Slice.Pos.ofSliceTo Manual.ZhDocString.Ch19Ch20.G8.c086}
