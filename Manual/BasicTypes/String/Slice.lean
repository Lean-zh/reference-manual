/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "字符串切片" =>
%%%
tag := "string-api-slice"
%%%

{docstring String.Slice}

{docstring String.toSlice}

{docstring String.sliceFrom}

{docstring String.sliceTo}

{docstring String.Slice.Pos}

# 接口参考

## 复制

{docstring String.Slice.copy}

## 大小

{docstring String.Slice.isEmpty}

{docstring String.Slice.utf8ByteSize}

## 边界

{docstring String.Slice.pos}

{docstring String.Slice.pos!}

{docstring String.Slice.pos?}

{docstring String.Slice.startPos}

{docstring String.Slice.endPos}

{docstring String.Slice.rawEndPos}


### 调整

{docstring String.Slice.sliceFrom}

{docstring String.Slice.sliceTo}

{docstring String.Slice.slice}

{docstring String.Slice.slice!}

{docstring String.Slice.drop}

{docstring String.Slice.dropEnd}

{docstring String.Slice.dropEndWhile}

{docstring String.Slice.dropPrefix}

{docstring String.Slice.dropPrefix?}

{docstring String.Slice.dropSuffix}

{docstring String.Slice.dropSuffix?}

{docstring String.Slice.dropWhile}

{docstring String.Slice.take}

{docstring String.Slice.takeEnd}

{docstring String.Slice.takeEndWhile}

{docstring String.Slice.takeWhile}

## 字符

{docstring String.Slice.front}

{docstring String.Slice.front?}

{docstring String.Slice.back}

{docstring String.Slice.back?}

## 字节

{docstring String.Slice.getUTF8Byte}

{docstring String.Slice.getUTF8Byte!}

## 位置

{docstring String.Slice.posGE}

{docstring String.Slice.posGT}

## 搜索

{docstring String.Slice.contains}

{docstring String.Slice.startsWith}

{docstring String.Slice.endsWith}

{docstring String.Slice.all}

{docstring String.Slice.find?}

{docstring String.Slice.revFind?}

## 操作

{docstring String.Slice.split}

{docstring String.Slice.splitInclusive}

{docstring String.Slice.lines}

{docstring String.Slice.trimAscii}

{docstring String.Slice.trimAsciiEnd}

{docstring String.Slice.trimAsciiStart}

## 迭代

{docstring String.Slice.chars}

{docstring String.Slice.revChars}

{docstring String.Slice.positions}

{docstring String.Slice.revPositions}

{docstring String.Slice.bytes}

{docstring String.Slice.revBytes}

{docstring String.Slice.revSplit}

{docstring String.Slice.foldl}

{docstring String.Slice.foldr}

## 转换

{docstring String.Slice.isNat}

{docstring String.Slice.toNat!}

{docstring String.Slice.toNat?}


## 相等性

{docstring String.Slice.beq}

{docstring String.Slice.eqIgnoreAsciiCase}


# 模式

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

{docstring String.Slice.Pattern.ToForwardSearcher}

{docstring String.Slice.Pattern.ForwardPattern}

{docstring String.Slice.Pattern.ToBackwardSearcher}

{docstring String.Slice.Pattern.BackwardPattern +allowMissing}

# 位置

## 查找

由于切片位置保留了对其来源切片的引用，因此可以借助它们查找单个字符或字节。

{docstring String.Slice.Pos.byte}

{docstring String.Slice.Pos.get}

{docstring String.Slice.Pos.get!}

{docstring String.Slice.Pos.get?}

## 递增与递减

{docstring String.Slice.Pos.prev}

{docstring String.Slice.Pos.prev!}

{docstring String.Slice.Pos.prev?}

{docstring String.Slice.Pos.prevn}

{docstring String.Slice.Pos.next}

{docstring String.Slice.Pos.next!}

{docstring String.Slice.Pos.next?}

{docstring String.Slice.Pos.nextn}

## 其他字符串或切片

{docstring String.Slice.Pos.cast}

{docstring String.Slice.Pos.ofSlice}

{docstring String.Slice.Pos.str}

{docstring String.Slice.Pos.copy}

{docstring String.Slice.Pos.ofSliceFrom}

{docstring String.Slice.Pos.ofSliceTo}
