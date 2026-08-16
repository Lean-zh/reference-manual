/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.String.Logical
import Manual.BasicTypes.String.Literals
import Manual.BasicTypes.String.FFI
import Manual.BasicTypes.String.Substrings
import Manual.BasicTypes.String.Slice

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "字符串" =>
%%%
tag := "String"
%%%


字符串表示 Unicode 文本。
Lean 对字符串有特殊支持：
 * 它们具有_逻辑模型_，该模型通过包含 UTF-8 标量值的 {name}`ByteArray` 来指定其行为。
 * 在编译后的代码中，它们有一个运行时表示，该表示额外包含了一个缓存的长度，以标量值的数量来衡量。
   Lean 运行时提供了字符串操作的优化实现。
 * 存在用于编写字符串的{ref "string-syntax"}[字符串字面量语法]。

UTF-8 是一种可变宽度编码。
一个字符可以编码为一个、两个、三个或四个字节的代码单元。
字符串是 UTF-8 编码的字节数组这一事实在 API 中是可见的：
 * 没有从字符串中提取特定字符的操作，因为这可能是一个性能陷阱。在循环中应{ref "string-iterators"}[使用迭代器]而不是 {name}`Nat`。
 * 字符串由 {name}`String.Pos` 索引，其在内部记录的是_字节数_而不是_字符数_，因此需要常量时间。
   {name}`String.Pos` 包含一个证明，证明字节计数实际上指向一个 UTF-8 代码单元的起始位置。
   除了 `0` 之外，这些不应该直接构造，而应该使用 {name}`String.next` 和 {name}`String.prev` 来更新。

{include 0 Manual.BasicTypes.String.Logical}

# 运行时表示
%%%
tag := "string-runtime"
%%%

:::figure "字符串的内存布局" (tag := "stringffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean object header"),
  ("m_size", .size_t, twoLine "Byte count" "size_t"),
  ("m_capacity", .size_t, twoLine "Allocated space" "size_t"),
  ("m_length", .size_t, twoLine "Characters" "size_t"),
  ("m_data", .data none,
    some <| .styledText (base := fieldLabelStyle) <|
      "String data\n" ++ family "monospace" "char" ++ " array"),
  ("'\\0'", .data (some 30), none)
]
```
:::

字符串被表示为 UTF-8 编码的字节{tech (key := "dynamic arrays")}[动态数组]。
在对象头部之后，一个字符串包含：

: 字节数

  当前包含有效字符串数据的字节数。

: capacity（容量）

  目前为该字符串分配的字节数。

: length（长度）

  编码后字符串的长度，由于 UTF-8 的多字节字符，它可能短于字节数。

: data（数据）

  字符串中实际的字符数据，以 null 结尾。

Lean 运行时中的许多字符串函数会通过查询对象头部中的引用计数来检查它们是否对齐参数具有独占访问权。
如果是这样，并且字符串的容量足够，那么现有的字符串就可以被修改，而不是分配新的内存。
否则，必须分配一个新的字符串。


## 性能说明
%%%
tag := "string-performance"
%%%

尽管它们看起来像是普通的构造子和投影，但 {name}`String.ofByteArray` 和 {name}`String.toByteArray` 需要的*时间与字符串的长度成正比*。
这是因为字节数组和字符串没有相同的表示，因此必须将字节数组的内容复制到一个新对象中。


{include 0 Manual.BasicTypes.String.Literals}

# API 参考
%%%
tag := "string-api"
%%%


## 构造
%%%
tag := "string-api-build"
%%%


{docstring String.singleton}

{docstring String.append}

{docstring String.join}

{docstring String.intercalate}

## 转换
%%%
tag := "string-api-convert"
%%%


{docstring String.toList}

{docstring String.isNat}

{docstring String.toNat?}

{docstring String.toNat!}

{docstring String.isInt}

{docstring String.toInt?}

{docstring String.toInt!}

{docstring String.toFormat}

## 属性
%%%
tag := "string-api-props"
%%%

{docstring String.isEmpty}

{docstring String.length}

## 位置
%%%
tag := "string-api-valid-pos"
%%%

{docstring String.Pos}

### 字符串内

{docstring String.startPos}

{docstring String.endPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

{docstring String.extract}

### 查找

{docstring String.Pos.get}

{docstring String.Pos.get!}

{docstring String.Pos.get?}

{docstring String.Pos.set}

### 修改

{docstring String.Pos.modify}

{docstring String.Pos.byte}

### 调整

{docstring String.Pos.prev}

{docstring String.Pos.prev!}

{docstring String.Pos.prev?}

{docstring String.Pos.next}

{docstring String.Pos.next!}

{docstring String.Pos.next?}

### 其他字符串

{docstring String.Pos.cast}

{docstring String.Pos.ofCopy}

{docstring String.Pos.toSetOfLE}

{docstring String.Pos.toModifyOfLE}

{docstring String.Pos.toSlice}

## 原始位置
%%%
tag := "string-api-pos"
%%%

{docstring String.Pos.Raw}

### 字节位置

{docstring String.Pos.Raw.offsetOfPos}

### 有效性

{docstring String.Pos.Raw.isValid}

{docstring String.Pos.Raw.isValidForSlice}

### 边界

{docstring String.rawEndPos}

{docstring String.Pos.Raw.atEnd}

### 比较

{docstring String.Pos.Raw.min}

{docstring String.Pos.Raw.byteDistance}

{docstring String.Pos.Raw.substrEq}

### 调整

{docstring String.Pos.Raw.prev}

{docstring String.Pos.Raw.next}

{docstring String.Pos.Raw.next'}

{docstring String.Pos.Raw.nextUntil}

{docstring String.Pos.Raw.nextWhile}

{docstring String.Pos.Raw.inc}

{docstring String.Pos.Raw.increaseBy}

{docstring String.Pos.Raw.offsetBy}

{docstring String.Pos.Raw.dec}

{docstring String.Pos.Raw.decreaseBy}

{docstring String.Pos.Raw.unoffsetBy}

### 字符串查找

{docstring String.Pos.Raw.extract}

{docstring String.Pos.Raw.get}

{docstring String.Pos.Raw.get!}

{docstring String.Pos.Raw.get'}

{docstring String.Pos.Raw.get?}

### 字符串修改

{docstring String.Pos.Raw.set}

{docstring String.Pos.Raw.modify}

## 查找与修改
%%%
tag := "string-api-lookup"
%%%

选择字符串子区域（例如它的前缀或后缀）的操作会返回原字符串的一个{ref "string-api-slice"}[切片]，而不是分配一个新字符串。
使用 {name}`String.Slice.copy` 将切片转换为新字符串。

{docstring String.take}

{docstring String.takeWhile}

{docstring String.takeEnd}

{docstring String.takeEndWhile}

{docstring String.drop}

{docstring String.dropWhile}

{docstring String.dropEnd}

{docstring String.dropEndWhile}

{docstring String.dropPrefix?}

{docstring String.dropPrefix}

{docstring String.dropSuffix?}

{docstring String.dropSuffix}

{docstring String.trimAscii}

{docstring String.trimAsciiStart}

{docstring String.trimAsciiEnd}

{docstring String.removeLeadingSpaces}

{docstring String.front}

{docstring String.back}

{docstring String.find}

{docstring String.revFind?}

{docstring String.contains}

{docstring String.replace}

{docstring String.find}

## 折叠与聚合
%%%
tag := "string-api-fold"
%%%

{docstring String.map}

{docstring String.foldl}

{docstring String.foldr}

{docstring String.all}

{docstring String.any}

## 比较
%%%
tag := "string-api-compare"
%%%

{inst}`LT String` 实例是由基于 {inst}`LT Char` 实例的字符串字典序定义的。
在逻辑上，这是由对建模字符串的列表进行字典序排列来建模的，因此 `List.Lex` 定义了此顺序。
它是可判定的，并且决策过程在运行时被利用字符串运行时表示的有效代码所覆盖。

{docstring String.le}

{docstring String.firstDiffPos}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

## 操作
%%%
tag := "string-api-modify"
%%%

{docstring String.splitToList}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

## 遗留迭代器
%%%
tag := "string-iterators"
%%%

为了向后兼容，Lean 包含遗留的字符串迭代器。
从根本上说，一个 {name}`String.Legacy.Iterator` 是一个字符串和该字符串中有效位置的有序对。
迭代器提供了获取当前字符（{name String.Legacy.Iterator.curr}`curr`）、替换当前字符（{name String.Legacy.Iterator.setCurr}`setCurr`）、检查迭代器是否可以向左或向右移动（分别为 {name String.Legacy.Iterator.hasPrev}`hasPrev` 和 {name String.Legacy.Iterator.hasNext}`hasNext`），以及移动迭代器（分别为 {name String.Legacy.Iterator.prev}`prev` 和 {name String.Legacy.Iterator.next}`next`）的函数。
调用者有责任检查它们是否已经到达字符串的开头或结尾；否则，迭代器确保其位置始终指向一个字符。
然而，{name}`String.Legacy.Iterator` 不包含这些良构性条件的证明，这可能使其在经验证的代码中更难使用。

{docstring String.Legacy.Iterator}

{docstring String.Legacy.iter}

{docstring String.Legacy.mkIterator}

{docstring String.Legacy.Iterator.curr}

{docstring String.Legacy.Iterator.curr'}

{docstring String.Legacy.Iterator.hasNext}

{docstring String.Legacy.Iterator.next}

{docstring String.Legacy.Iterator.next'}

{docstring String.Legacy.Iterator.forward}

{docstring String.Legacy.Iterator.nextn}

{docstring String.Legacy.Iterator.hasPrev}

{docstring String.Legacy.Iterator.prev}

{docstring String.Legacy.Iterator.prevn}

{docstring String.Legacy.Iterator.atEnd}

{docstring String.Legacy.Iterator.toEnd}

{docstring String.Legacy.Iterator.setCurr}

{docstring String.Legacy.Iterator.find}

{docstring String.Legacy.Iterator.foldUntil}

{docstring String.Legacy.Iterator.extract}

{docstring String.Legacy.Iterator.remainingToString}

{docstring String.Legacy.Iterator.remainingBytes}

{docstring String.Legacy.Iterator.pos}

{docstring String.Legacy.Iterator.toString}

{include 2 Manual.BasicTypes.String.Slice}

{include 2 Manual.BasicTypes.String.Substrings}





## 元编程
%%%
tag := "string-api-meta"
%%%

{docstring String.toName}

{docstring String.quote}


## 编码
%%%
tag := "string-api-encoding"
%%%

{docstring String.getUTF8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.crlfToLf}


{include 0 Manual.BasicTypes.String.FFI}
