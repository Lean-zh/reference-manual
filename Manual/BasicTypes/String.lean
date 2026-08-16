/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G4

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

Lean 运行时中的许多字符串函数会通过查询对象头部中的引用计数，检查它们是否独占其参数。
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


{zhdocstring String.singleton Manual.ZhDocString.Ch19Ch20.G4.c084}

{zhdocstring String.append Manual.ZhDocString.Ch19Ch20.G4.c085}

{zhdocstring String.join Manual.ZhDocString.Ch19Ch20.G4.c086}

{zhdocstring String.intercalate Manual.ZhDocString.Ch19Ch20.G4.c087}

## 转换
%%%
tag := "string-api-convert"
%%%


{zhdocstring String.toList Manual.ZhDocString.Ch19Ch20.G4.c088}

{zhdocstring String.isNat Manual.ZhDocString.Ch19Ch20.G4.c089}

{zhdocstring String.toNat? Manual.ZhDocString.Ch19Ch20.G4.c090}

{zhdocstring String.toNat! Manual.ZhDocString.Ch19Ch20.G4.c091}

{zhdocstring String.isInt Manual.ZhDocString.Ch19Ch20.G4.c092}

{zhdocstring String.toInt? Manual.ZhDocString.Ch19Ch20.G4.c093}

{zhdocstring String.toInt! Manual.ZhDocString.Ch19Ch20.G4.c094}

{zhdocstring String.toFormat Manual.ZhDocString.Ch19Ch20.G4.c095}

## 属性
%%%
tag := "string-api-props"
%%%

{zhdocstring String.isEmpty Manual.ZhDocString.Ch19Ch20.G4.c096}

{zhdocstring String.length Manual.ZhDocString.Ch19Ch20.G4.c097}

## 位置
%%%
tag := "string-api-valid-pos"
%%%

{zhdocstring String.Pos Manual.ZhDocString.Ch19Ch20.G4.c098}

### 字符串内

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Positions--In-Strings"
%%%
{zhdocstring String.startPos Manual.ZhDocString.Ch19Ch20.G4.c099}

{zhdocstring String.endPos Manual.ZhDocString.Ch19Ch20.G4.c100}

{zhdocstring String.pos Manual.ZhDocString.Ch19Ch20.G4.c101}

{zhdocstring String.pos? Manual.ZhDocString.Ch19Ch20.G4.c102}

{zhdocstring String.pos! Manual.ZhDocString.Ch19Ch20.G4.c103}

{zhdocstring String.extract Manual.ZhDocString.Ch19Ch20.G4.c104}

### 查找

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Positions--Lookups"
%%%
{zhdocstring String.Pos.get Manual.ZhDocString.Ch19Ch20.G4.c105}

{zhdocstring String.Pos.get! Manual.ZhDocString.Ch19Ch20.G4.c106}

{zhdocstring String.Pos.get? Manual.ZhDocString.Ch19Ch20.G4.c107}

{zhdocstring String.Pos.set Manual.ZhDocString.Ch19Ch20.G4.c108}

### 修改

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Positions--Modifications"
%%%
{zhdocstring String.Pos.modify Manual.ZhDocString.Ch19Ch20.G4.c109}

{zhdocstring String.Pos.byte Manual.ZhDocString.Ch19Ch20.G4.c110}

### 调整

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Positions--Adjustment"
%%%
{zhdocstring String.Pos.prev Manual.ZhDocString.Ch19Ch20.G4.c111}

{zhdocstring String.Pos.prev! Manual.ZhDocString.Ch19Ch20.G4.c112}

{zhdocstring String.Pos.prev? Manual.ZhDocString.Ch19Ch20.G4.c113}

{zhdocstring String.Pos.next Manual.ZhDocString.Ch19Ch20.G4.c114}

{zhdocstring String.Pos.next! Manual.ZhDocString.Ch19Ch20.G4.c115}

{zhdocstring String.Pos.next? Manual.ZhDocString.Ch19Ch20.G4.c116}

### 其他字符串

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Positions--Other-Strings"
%%%
{zhdocstring String.Pos.cast Manual.ZhDocString.Ch19Ch20.G4.c117}

{zhdocstring String.Pos.ofCopy Manual.ZhDocString.Ch19Ch20.G4.c118}

{zhdocstring String.Pos.toSetOfLE Manual.ZhDocString.Ch19Ch20.G4.c119}

{zhdocstring String.Pos.toModifyOfLE Manual.ZhDocString.Ch19Ch20.G4.c120}

{zhdocstring String.Pos.toSlice Manual.ZhDocString.Ch19Ch20.G4.c121}

## 原始位置
%%%
tag := "string-api-pos"
%%%

{zhdocstring String.Pos.Raw Manual.ZhDocString.Ch19Ch20.G4.c122}

### 字节位置

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--Byte-Position"
%%%
{zhdocstring String.Pos.Raw.offsetOfPos Manual.ZhDocString.Ch19Ch20.G4.c123}

### 有效性

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--Validity"
%%%
{zhdocstring String.Pos.Raw.isValid Manual.ZhDocString.Ch19Ch20.G4.c124}

{zhdocstring String.Pos.Raw.isValidForSlice Manual.ZhDocString.Ch19Ch20.G4.c125}

### 边界

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--Boundaries"
%%%
{zhdocstring String.rawEndPos Manual.ZhDocString.Ch19Ch20.G4.c126}

{zhdocstring String.Pos.Raw.atEnd Manual.ZhDocString.Ch19Ch20.G4.c127}

### 比较

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--Comparisons"
%%%
{zhdocstring String.Pos.Raw.min Manual.ZhDocString.Ch19Ch20.G4.c128}

{zhdocstring String.Pos.Raw.byteDistance Manual.ZhDocString.Ch19Ch20.G4.c129}

{zhdocstring String.Pos.Raw.substrEq Manual.ZhDocString.Ch19Ch20.G4.c130}

### 调整

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--Adjustment"
%%%
{zhdocstring String.Pos.Raw.prev Manual.ZhDocString.Ch19Ch20.G4.c131}

{zhdocstring String.Pos.Raw.next Manual.ZhDocString.Ch19Ch20.G4.c132}

{zhdocstring String.Pos.Raw.next' Manual.ZhDocString.Ch19Ch20.G4.c133}

{zhdocstring String.Pos.Raw.nextUntil Manual.ZhDocString.Ch19Ch20.G4.c134}

{zhdocstring String.Pos.Raw.nextWhile Manual.ZhDocString.Ch19Ch20.G4.c135}

{zhdocstring String.Pos.Raw.inc Manual.ZhDocString.Ch19Ch20.G4.c136}

{zhdocstring String.Pos.Raw.increaseBy Manual.ZhDocString.Ch19Ch20.G4.c137}

{zhdocstring String.Pos.Raw.offsetBy Manual.ZhDocString.Ch19Ch20.G4.c138}

{zhdocstring String.Pos.Raw.dec Manual.ZhDocString.Ch19Ch20.G4.c139}

{zhdocstring String.Pos.Raw.decreaseBy Manual.ZhDocString.Ch19Ch20.G4.c140}

{zhdocstring String.Pos.Raw.unoffsetBy Manual.ZhDocString.Ch19Ch20.G4.c141}

### 字符串查找

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--String-Lookups"
%%%
{zhdocstring String.Pos.Raw.extract Manual.ZhDocString.Ch19Ch20.G4.c142}

{zhdocstring String.Pos.Raw.get Manual.ZhDocString.Ch19Ch20.G4.c143}

{zhdocstring String.Pos.Raw.get! Manual.ZhDocString.Ch19Ch20.G4.c144}

{zhdocstring String.Pos.Raw.get' Manual.ZhDocString.Ch19Ch20.G4.c145}

{zhdocstring String.Pos.Raw.get? Manual.ZhDocString.Ch19Ch20.G4.c146}

### 字符串修改

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Positions--String-Modifications"
%%%
{zhdocstring String.Pos.Raw.set Manual.ZhDocString.Ch19Ch20.G4.c147}

{zhdocstring String.Pos.Raw.modify Manual.ZhDocString.Ch19Ch20.G4.c148}

## 查找与修改
%%%
tag := "string-api-lookup"
%%%

选择字符串子区域（例如它的前缀或后缀）的操作会返回原字符串的一个{ref "string-api-slice"}[切片]，而不是分配一个新字符串。
使用 {name}`String.Slice.copy` 将切片转换为新字符串。

{zhdocstring String.take Manual.ZhDocString.Ch19Ch20.G4.c149}

{zhdocstring String.takeWhile Manual.ZhDocString.Ch19Ch20.G4.c150}

{zhdocstring String.takeEnd Manual.ZhDocString.Ch19Ch20.G4.c151}

{zhdocstring String.takeEndWhile Manual.ZhDocString.Ch19Ch20.G4.c152}

{zhdocstring String.drop Manual.ZhDocString.Ch19Ch20.G4.c153}

{zhdocstring String.dropWhile Manual.ZhDocString.Ch19Ch20.G4.c154}

{zhdocstring String.dropEnd Manual.ZhDocString.Ch19Ch20.G4.c155}

{zhdocstring String.dropEndWhile Manual.ZhDocString.Ch19Ch20.G4.c156}

{zhdocstring String.dropPrefix? Manual.ZhDocString.Ch19Ch20.G4.c157}

{zhdocstring String.dropPrefix Manual.ZhDocString.Ch19Ch20.G4.c158}

{zhdocstring String.dropSuffix? Manual.ZhDocString.Ch19Ch20.G4.c159}

{zhdocstring String.dropSuffix Manual.ZhDocString.Ch19Ch20.G4.c160}

{zhdocstring String.trimAscii Manual.ZhDocString.Ch19Ch20.G4.c161}

{zhdocstring String.trimAsciiStart Manual.ZhDocString.Ch19Ch20.G4.c162}

{zhdocstring String.trimAsciiEnd Manual.ZhDocString.Ch19Ch20.G4.c163}

{zhdocstring String.removeLeadingSpaces Manual.ZhDocString.Ch19Ch20.G4.c164}

{zhdocstring String.front Manual.ZhDocString.Ch19Ch20.G4.c165}

{zhdocstring String.back Manual.ZhDocString.Ch19Ch20.G4.c166}

{zhdocstring String.find Manual.ZhDocString.Ch19Ch20.G4.c167}

{zhdocstring String.revFind? Manual.ZhDocString.Ch19Ch20.G4.c168}

{zhdocstring String.contains Manual.ZhDocString.Ch19Ch20.G4.c169}

{zhdocstring String.replace Manual.ZhDocString.Ch19Ch20.G4.c170}

{zhdocstring String.find Manual.ZhDocString.Ch19Ch20.G4.c171}

## 折叠与聚合
%%%
tag := "string-api-fold"
%%%

{zhdocstring String.map Manual.ZhDocString.Ch19Ch20.G4.c172}

{zhdocstring String.foldl Manual.ZhDocString.Ch19Ch20.G4.c173}

{zhdocstring String.foldr Manual.ZhDocString.Ch19Ch20.G4.c174}

{zhdocstring String.all Manual.ZhDocString.Ch19Ch20.G4.c175}

{zhdocstring String.any Manual.ZhDocString.Ch19Ch20.G4.c176}

## 比较
%%%
tag := "string-api-compare"
%%%

{inst}`LT String` 实例是由基于 {inst}`LT Char` 实例的字符串字典序定义的。
在逻辑上，这是由对建模字符串的列表进行字典序排列来建模的，因此 `List.Lex` 定义了此顺序。
它是可判定的；在运行时，该判定过程会被利用字符串运行时表示的高效代码替代。

{zhdocstring String.le Manual.ZhDocString.Ch19Ch20.G4.c177}

{zhdocstring String.firstDiffPos Manual.ZhDocString.Ch19Ch20.G4.c178}

{zhdocstring String.isPrefixOf Manual.ZhDocString.Ch19Ch20.G4.c179}

{zhdocstring String.startsWith Manual.ZhDocString.Ch19Ch20.G4.c180}

{zhdocstring String.endsWith Manual.ZhDocString.Ch19Ch20.G4.c181}

{zhdocstring String.decEq Manual.ZhDocString.Ch19Ch20.G4.c182}

{zhdocstring String.hash Manual.ZhDocString.Ch19Ch20.G4.c183}

## 操作
%%%
tag := "string-api-modify"
%%%

{zhdocstring String.splitToList Manual.ZhDocString.Ch19Ch20.G4.c184}

{zhdocstring String.splitOn Manual.ZhDocString.Ch19Ch20.G4.c185}

{zhdocstring String.push Manual.ZhDocString.Ch19Ch20.G4.c186}

{zhdocstring String.pushn Manual.ZhDocString.Ch19Ch20.G4.c187}

{zhdocstring String.capitalize Manual.ZhDocString.Ch19Ch20.G4.c188}

{zhdocstring String.decapitalize Manual.ZhDocString.Ch19Ch20.G4.c189}

{zhdocstring String.toUpper Manual.ZhDocString.Ch19Ch20.G4.c190}

{zhdocstring String.toLower Manual.ZhDocString.Ch19Ch20.G4.c191}

## 遗留迭代器
%%%
tag := "string-iterators"
%%%

为了向后兼容，Lean 包含遗留的字符串迭代器。
从根本上说，一个 {name}`String.Legacy.Iterator` 是一个字符串和该字符串中有效位置的有序对。
迭代器提供了获取当前字符（{name String.Legacy.Iterator.curr}`curr`）、替换当前字符（{name String.Legacy.Iterator.setCurr}`setCurr`）、检查迭代器是否可以向左或向右移动（分别为 {name String.Legacy.Iterator.hasPrev}`hasPrev` 和 {name String.Legacy.Iterator.hasNext}`hasNext`），以及移动迭代器（分别为 {name String.Legacy.Iterator.prev}`prev` 和 {name String.Legacy.Iterator.next}`next`）的函数。
调用者有责任检查它们是否已经到达字符串的开头或结尾；否则，迭代器确保其位置始终指向一个字符。
然而，{name}`String.Legacy.Iterator` 不包含这些良构性条件的证明，这可能使其在经验证的代码中更难使用。

{zhdocstring String.Legacy.Iterator Manual.ZhDocString.Ch19Ch20.G4.c192}

{zhdocstring String.Legacy.iter Manual.ZhDocString.Ch19Ch20.G4.c193}

{zhdocstring String.Legacy.mkIterator Manual.ZhDocString.Ch19Ch20.G4.c194}

{zhdocstring String.Legacy.Iterator.curr Manual.ZhDocString.Ch19Ch20.G4.c195}

{zhdocstring String.Legacy.Iterator.curr' Manual.ZhDocString.Ch19Ch20.G4.c196}

{zhdocstring String.Legacy.Iterator.hasNext Manual.ZhDocString.Ch19Ch20.G4.c197}

{zhdocstring String.Legacy.Iterator.next Manual.ZhDocString.Ch19Ch20.G4.c198}

{zhdocstring String.Legacy.Iterator.next' Manual.ZhDocString.Ch19Ch20.G4.c199}

{zhdocstring String.Legacy.Iterator.forward Manual.ZhDocString.Ch19Ch20.G4.c200}

{zhdocstring String.Legacy.Iterator.nextn Manual.ZhDocString.Ch19Ch20.G4.c201}

{zhdocstring String.Legacy.Iterator.hasPrev Manual.ZhDocString.Ch19Ch20.G4.c202}

{zhdocstring String.Legacy.Iterator.prev Manual.ZhDocString.Ch19Ch20.G4.c203}

{zhdocstring String.Legacy.Iterator.prevn Manual.ZhDocString.Ch19Ch20.G4.c204}

{zhdocstring String.Legacy.Iterator.atEnd Manual.ZhDocString.Ch19Ch20.G4.c205}

{zhdocstring String.Legacy.Iterator.toEnd Manual.ZhDocString.Ch19Ch20.G4.c206}

{zhdocstring String.Legacy.Iterator.setCurr Manual.ZhDocString.Ch19Ch20.G4.c207}

{zhdocstring String.Legacy.Iterator.find Manual.ZhDocString.Ch19Ch20.G4.c208}

{zhdocstring String.Legacy.Iterator.foldUntil Manual.ZhDocString.Ch19Ch20.G4.c209}

{zhdocstring String.Legacy.Iterator.extract Manual.ZhDocString.Ch19Ch20.G4.c210}

{zhdocstring String.Legacy.Iterator.remainingToString Manual.ZhDocString.Ch19Ch20.G4.c211}

{zhdocstring String.Legacy.Iterator.remainingBytes Manual.ZhDocString.Ch19Ch20.G4.c212}

{zhdocstring String.Legacy.Iterator.pos Manual.ZhDocString.Ch19Ch20.G4.c213}

{zhdocstring String.Legacy.Iterator.toString Manual.ZhDocString.Ch19Ch20.G4.c214}

{include 2 Manual.BasicTypes.String.Slice}

{include 2 Manual.BasicTypes.String.Substrings}





## 元编程
%%%
tag := "string-api-meta"
%%%

{zhdocstring String.toName Manual.ZhDocString.Ch19Ch20.G4.c215}

{zhdocstring String.quote Manual.ZhDocString.Ch19Ch20.G4.c216}


## 编码
%%%
tag := "string-api-encoding"
%%%

{zhdocstring String.getUTF8Byte Manual.ZhDocString.Ch19Ch20.G4.c217}

{zhdocstring String.utf8ByteSize Manual.ZhDocString.Ch19Ch20.G4.c218}

{zhdocstring String.utf8EncodeChar Manual.ZhDocString.Ch19Ch20.G4.c219}

{zhdocstring String.fromUTF8 Manual.ZhDocString.Ch19Ch20.G4.c220}

{zhdocstring String.fromUTF8? Manual.ZhDocString.Ch19Ch20.G4.c221}

{zhdocstring String.fromUTF8! Manual.ZhDocString.Ch19Ch20.G4.c222}

{zhdocstring String.toUTF8 Manual.ZhDocString.Ch19Ch20.G4.c223}

{zhdocstring String.crlfToLf Manual.ZhDocString.Ch19Ch20.G4.c224}


{include 0 Manual.BasicTypes.String.FFI}
