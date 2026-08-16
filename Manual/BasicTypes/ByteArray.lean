/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G6

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true -- TODO remove after docstrings are merged

example := Char

#doc (Manual) "字节数组" =>
%%%
tag := "ByteArray"
%%%

字节数组是一种专门化的数组类型，只能包含类型为 {name}`UInt8` 的元素。
由于这一限制，它们可以采用高效得多的表示，不需要指针间接访问。
与其他数组一样，字节数组在编译后的代码中表示为 {tech (key := "dynamic arrays")}[动态数组]，Lean 运行时还会专门优化其数组操作。
修改字节数组的操作会先检查该数组的 {ref "reference-counting"}[引用计数]；如果没有其他引用指向该数组，就会原地修改它。

字节数组没有字面量语法。
可以使用 {name}`List.toByteArray` 从列表字面量构造字节数组。

{zhdocstring ByteArray Manual.ZhDocString.Ch19Ch20.G6.c109}

# 接口参考

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference"
%%%
## 构造字节数组

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Constructing-Byte-Arrays"
%%%
{zhdocstring ByteArray.empty Manual.ZhDocString.Ch19Ch20.G6.c110}

{zhdocstring ByteArray.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G6.c111}

{zhdocstring ByteArray.append Manual.ZhDocString.Ch19Ch20.G6.c112}

{zhdocstring ByteArray.fastAppend Manual.ZhDocString.Ch19Ch20.G6.c113}

{zhdocstring ByteArray.copySlice Manual.ZhDocString.Ch19Ch20.G6.c114}

## 大小

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Size"
%%%
{zhdocstring ByteArray.size Manual.ZhDocString.Ch19Ch20.G6.c115}

{zhdocstring ByteArray.usize Manual.ZhDocString.Ch19Ch20.G6.c116}

{zhdocstring ByteArray.isEmpty Manual.ZhDocString.Ch19Ch20.G6.c117}

## 查找

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Lookups"
%%%
{zhdocstring ByteArray.get Manual.ZhDocString.Ch19Ch20.G6.c118}

{zhdocstring ByteArray.uget Manual.ZhDocString.Ch19Ch20.G6.c119}

{zhdocstring ByteArray.get! Manual.ZhDocString.Ch19Ch20.G6.c120}

{zhdocstring ByteArray.extract Manual.ZhDocString.Ch19Ch20.G6.c121}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Conversions"
%%%
{zhdocstring ByteArray.toList Manual.ZhDocString.Ch19Ch20.G6.c122}

{zhdocstring ByteArray.toUInt64BE! Manual.ZhDocString.Ch19Ch20.G6.c123}

{zhdocstring ByteArray.toUInt64LE! Manual.ZhDocString.Ch19Ch20.G6.c124}

### UTF-8

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Conversions--UTF-8"
%%%
{zhdocstring ByteArray.utf8Decode? Manual.ZhDocString.Ch19Ch20.G6.c125}

{zhdocstring ByteArray.utf8DecodeChar? Manual.ZhDocString.Ch19Ch20.G6.c126}

{zhdocstring ByteArray.utf8DecodeChar Manual.ZhDocString.Ch19Ch20.G6.c127}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Modification"
%%%
{zhdocstring ByteArray.push Manual.ZhDocString.Ch19Ch20.G6.c128}

{zhdocstring ByteArray.set Manual.ZhDocString.Ch19Ch20.G6.c129}

{zhdocstring ByteArray.uset Manual.ZhDocString.Ch19Ch20.G6.c130}

{zhdocstring ByteArray.set! Manual.ZhDocString.Ch19Ch20.G6.c131}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Iteration"
%%%
{zhdocstring ByteArray.foldl Manual.ZhDocString.Ch19Ch20.G6.c132}

{zhdocstring ByteArray.foldlM Manual.ZhDocString.Ch19Ch20.G6.c133}

{zhdocstring ByteArray.forIn Manual.ZhDocString.Ch19Ch20.G6.c134}

## 迭代器

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Iterators"
%%%
{zhdocstring ByteArray.iter Manual.ZhDocString.Ch19Ch20.G6.c135}

{zhdocstring ByteArray.Iterator Manual.ZhDocString.Ch19Ch20.G6.c136}

{zhdocstring ByteArray.Iterator.pos Manual.ZhDocString.Ch19Ch20.G6.c137}

{zhdocstring ByteArray.Iterator.atEnd Manual.ZhDocString.Ch19Ch20.G6.c138}

{zhdocstring ByteArray.Iterator.hasNext Manual.ZhDocString.Ch19Ch20.G6.c139}

{zhdocstring ByteArray.Iterator.hasPrev Manual.ZhDocString.Ch19Ch20.G6.c140}

{zhdocstring ByteArray.Iterator.curr Manual.ZhDocString.Ch19Ch20.G6.c141}

{zhdocstring ByteArray.Iterator.curr' Manual.ZhDocString.Ch19Ch20.G6.c142}

{zhdocstring ByteArray.Iterator.next Manual.ZhDocString.Ch19Ch20.G6.c143}

{zhdocstring ByteArray.Iterator.next' Manual.ZhDocString.Ch19Ch20.G6.c144}

{zhdocstring ByteArray.Iterator.forward Manual.ZhDocString.Ch19Ch20.G6.c145}

{zhdocstring ByteArray.Iterator.nextn Manual.ZhDocString.Ch19Ch20.G6.c146}

{zhdocstring ByteArray.Iterator.prev Manual.ZhDocString.Ch19Ch20.G6.c147}

{zhdocstring ByteArray.Iterator.prevn Manual.ZhDocString.Ch19Ch20.G6.c148}

{zhdocstring ByteArray.Iterator.remainingBytes Manual.ZhDocString.Ch19Ch20.G6.c149}

{zhdocstring ByteArray.Iterator.toEnd Manual.ZhDocString.Ch19Ch20.G6.c150}

## 切片

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Slices"
%%%
{zhdocstring ByteArray.toByteSlice Manual.ZhDocString.Ch19Ch20.G6.c151}

{zhdocstring ByteSlice Manual.ZhDocString.Ch19Ch20.G6.c152}

{zhdocstring ByteSlice.beq Manual.ZhDocString.Ch19Ch20.G6.c153}

{zhdocstring ByteSlice.byteArray Manual.ZhDocString.Ch19Ch20.G6.c154}

{zhdocstring ByteSlice.contains Manual.ZhDocString.Ch19Ch20.G6.c155}

{zhdocstring ByteSlice.empty Manual.ZhDocString.Ch19Ch20.G6.c156}

{zhdocstring ByteSlice.foldr Manual.ZhDocString.Ch19Ch20.G6.c157}

{zhdocstring ByteSlice.foldrM Manual.ZhDocString.Ch19Ch20.G6.c158}

{zhdocstring ByteSlice.forM Manual.ZhDocString.Ch19Ch20.G6.c159}

{zhdocstring ByteSlice.get Manual.ZhDocString.Ch19Ch20.G6.c160}

{zhdocstring ByteSlice.get! Manual.ZhDocString.Ch19Ch20.G6.c161}

{zhdocstring ByteSlice.getD Manual.ZhDocString.Ch19Ch20.G6.c162}

{zhdocstring ByteSlice.ofByteArray Manual.ZhDocString.Ch19Ch20.G6.c163}

{zhdocstring ByteSlice.size Manual.ZhDocString.Ch19Ch20.G6.c164}

{zhdocstring ByteSlice.slice Manual.ZhDocString.Ch19Ch20.G6.c165}

{zhdocstring ByteSlice.start Manual.ZhDocString.Ch19Ch20.G6.c166}

{zhdocstring ByteSlice.stop Manual.ZhDocString.Ch19Ch20.G6.c167}

{zhdocstring ByteSlice.toByteArray Manual.ZhDocString.Ch19Ch20.G6.c168}


## 元素判定

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Element-Predicates"
%%%
{zhdocstring ByteArray.findIdx? Manual.ZhDocString.Ch19Ch20.G6.c169}

{zhdocstring ByteArray.findFinIdx? Manual.ZhDocString.Ch19Ch20.G6.c170}
