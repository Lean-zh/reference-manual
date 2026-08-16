/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
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

{docstring ByteArray}

# 接口参考

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference"
%%%
## 构造字节数组

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Constructing-Byte-Arrays"
%%%
{docstring ByteArray.empty}

{docstring ByteArray.emptyWithCapacity}

{docstring ByteArray.append}

{docstring ByteArray.fastAppend}

{docstring ByteArray.copySlice}

## 大小

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Size"
%%%
{docstring ByteArray.size}

{docstring ByteArray.usize}

{docstring ByteArray.isEmpty}

## 查找

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Lookups"
%%%
{docstring ByteArray.get}

{docstring ByteArray.uget}

{docstring ByteArray.get!}

{docstring ByteArray.extract}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Conversions"
%%%
{docstring ByteArray.toList}

{docstring ByteArray.toUInt64BE!}

{docstring ByteArray.toUInt64LE!}

### UTF-8

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Conversions--UTF-8"
%%%
{docstring ByteArray.utf8Decode?}

{docstring ByteArray.utf8DecodeChar?}

{docstring ByteArray.utf8DecodeChar}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Modification"
%%%
{docstring ByteArray.push}

{docstring ByteArray.set}

{docstring ByteArray.uset}

{docstring ByteArray.set!}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Iteration"
%%%
{docstring ByteArray.foldl}

{docstring ByteArray.foldlM}

{docstring ByteArray.forIn}

## 迭代器

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Iterators"
%%%
{docstring ByteArray.iter}

{docstring ByteArray.Iterator}

{docstring ByteArray.Iterator.pos}

{docstring ByteArray.Iterator.atEnd}

{docstring ByteArray.Iterator.hasNext}

{docstring ByteArray.Iterator.hasPrev}

{docstring ByteArray.Iterator.curr}

{docstring ByteArray.Iterator.curr'}

{docstring ByteArray.Iterator.next}

{docstring ByteArray.Iterator.next'}

{docstring ByteArray.Iterator.forward}

{docstring ByteArray.Iterator.nextn}

{docstring ByteArray.Iterator.prev}

{docstring ByteArray.Iterator.prevn}

{docstring ByteArray.Iterator.remainingBytes}

{docstring ByteArray.Iterator.toEnd}

## 切片

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Slices"
%%%
{docstring ByteArray.toByteSlice}

{docstring ByteSlice}

{docstring ByteSlice.beq}

{docstring ByteSlice.byteArray}

{docstring ByteSlice.contains}

{docstring ByteSlice.empty}

{docstring ByteSlice.foldr}

{docstring ByteSlice.foldrM}

{docstring ByteSlice.forM}

{docstring ByteSlice.get}

{docstring ByteSlice.get!}

{docstring ByteSlice.getD}

{docstring ByteSlice.ofByteArray}

{docstring ByteSlice.size}

{docstring ByteSlice.slice}

{docstring ByteSlice.start}

{docstring ByteSlice.stop}

{docstring ByteSlice.toByteArray}


## 元素判定

%%%
tag := "Lean-__________________--Basic-Types--Byte-Arrays--API-Reference--Element-Predicates"
%%%
{docstring ByteArray.findIdx?}

{docstring ByteArray.findFinIdx?}
