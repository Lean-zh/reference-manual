/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.ZhDocString.Ch19Ch20.G7

import Manual.Meta
import Manual.BasicTypes.UInt.Comparisons
import Manual.BasicTypes.UInt.Arith

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "定精度整数" =>
%%%
tag := "fixed-ints"
file := "Fixed-Precision-Integers"
%%%

Lean 的标准库包含通常的各种固定宽度整数类型。
从形式化和证明的角度来看，这些类型是适当大小的位向量的包装器；这些包装器确保应用正确的算术操作等实现。
在编译后的代码中，它们的表示非常高效：编译器对它们有特殊的支持，就像对其他基础类型一样。

# 逻辑模型

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--Logical-Model"
%%%
固定宽度整数可以是无符号的或有符号的。
此外，它们有五种大小：8 位、16 位、32 位和 64 位，以及当前架构的字长。
在它们的逻辑模型中，无符号整数是包装了适当宽度的 {name}`BitVec` 的结构体。
有符号整数包装了相应的无符号整数，并使用二进制补码表示。

## 无符号

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--Logical-Model--Unsigned"
%%%
{zhdocstring USize Manual.ZhDocString.Ch19Ch20.G7.c001}

{zhdocstring UInt8 Manual.ZhDocString.Ch19Ch20.G7.c002}

{zhdocstring UInt16 Manual.ZhDocString.Ch19Ch20.G7.c003}

{zhdocstring UInt32 Manual.ZhDocString.Ch19Ch20.G7.c004}

{zhdocstring UInt64 Manual.ZhDocString.Ch19Ch20.G7.c005}

## 有符号

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--Logical-Model--Signed"
%%%
{zhdocstring ISize Manual.ZhDocString.Ch19Ch20.G7.c006}

{zhdocstring Int8 Manual.ZhDocString.Ch19Ch20.G7.c007}

{zhdocstring Int16 Manual.ZhDocString.Ch19Ch20.G7.c008}

{zhdocstring Int32 Manual.ZhDocString.Ch19Ch20.G7.c009}

{zhdocstring Int64 Manual.ZhDocString.Ch19Ch20.G7.c010}

# 运行时表示
%%%
tag := "fixed-int-runtime"
%%%

在编译后的代码中，即使上下文要求采用{tech (key := "boxed")}[装箱]表示，只要某种固定宽度整数类型能装入比平台指针少一位的空间，就始终无需额外分配或间接寻址。
这始终包含 {lean}`Int8`、{lean}`UInt8`、{lean}`Int16` 和 {lean}`UInt16`。
在 64 位架构上，{lean}`Int32` 和 {lean}`UInt32` 也可以在没有指针的情况下表示。
在 32 位架构上，{lean}`Int32` 和 {lean}`UInt32` 需要一个指向堆上对象的指针。
{lean}`ISize`、{lean}`USize`、{lean}`Int64` 和 {lean}`UInt64` 在所有架构上都可能需要指针。

尽管通常情况下一些固定宽度整数类型需要装箱，但编译器能够在仅使用特定固定宽度类型而不是多态的代码路径中，（可能在特化阶段之后）在没有装箱或指针间接寻址的情况下表示它们。
这适用于使用这些类型的大多数实际情况：当已知构造子参数、函数参数、函数返回值或中间结果是固定宽度整数类型时，它们的值将使用相应的无符号固定宽度 C 类型来表示。
Lean 运行时系统包含了在{tech (key := "inductive types")}[归纳类型]的构造子中存储固定宽度整数的原语，并且基本操作是在相应的 C 类型上定义的，因此装箱往往发生在整数计算的“边缘”，而不是针对每个中间结果。
在可能出现其他类型的上下文中，例如像 {name}`Array` 这样的多态容器的内容，这些类型会被装箱，即使静态地知道一个数组只包含单一的固定宽度整数类型。{margin}[单态数组类型 {lean}`ByteArray` 避免了对 {lean}`UInt8` 数组的装箱。]
Lean 不特化归纳类型或数组的表示。
在 Lean 中检查函数的类型不足以确定固定宽度整数值将如何表示，因为装箱的值不会被急切地取消装箱——例如一个从数组中投影出 {name}`Int64` 的函数返回的是一个装箱的整数值。

# 语法

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--Syntax"
%%%
所有的固定宽度整数类型都有 {name}`OfNat` 实例，这允许在表达式和模式上下文中将数字用作字面量。
有符号类型另外还有 {lean}`Neg` 实例，允许应用求负操作。

:::example "固定宽度字面量"
对于具有 {name}`OfNat` 实例的类型，Lean 允许使用十进制和十六进制字面量。
在此示例中，字面量表示法用于定义掩码。

```lean
structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool

def Permissions.encode (p : Permissions) : UInt8 :=
  let r := if p.readable then 0x01 else 0
  let w := if p.writable then 0x02 else 0
  let x := if p.executable then 0x04 else 0
  r ||| w ||| x

def Permissions.decode (i : UInt8) : Permissions :=
  ⟨i &&& 0x01 ≠ 0, i &&& 0x02 ≠ 0, i &&& 0x04 ≠ 0⟩
```

```lean -show
-- 检查以上内容
theorem Permissions.decode_encode (p : Permissions) : p = .decode (p.encode) := by
  let ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;>
  simp +decide [decode]
```
:::

溢出其类型精度的字面量将被解释为对精度取模。
对于有符号类型，则按底层的二进制补码表示来解释。

:::example "溢出固定宽度字面量"
以下声明均为真：
```lean
example : (255 : UInt8) = 255 := by rfl
example : (256 : UInt8) = 0   := by rfl
example : (257 : UInt8) = 1   := by rfl

example : (0x7f : Int8) = 127  := by rfl
example : (0x8f : Int8) = -113 := by rfl
example : (0xff : Int8) = -1   := by rfl
```
:::

# API 参考

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference"
%%%
## 大小

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Sizes"
%%%
每个固定宽度整数都有一个_大小_，这是该类型可以表示的不同值的数量。
这不等同于 C 语言的 `sizeof` 运算符，后者是用来确定该类型占用多少字节的。

{zhdocstring USize.size Manual.ZhDocString.Ch19Ch20.G7.c011}

{zhdocstring ISize.size Manual.ZhDocString.Ch19Ch20.G7.c012}

{zhdocstring UInt8.size Manual.ZhDocString.Ch19Ch20.G7.c013}

{zhdocstring Int8.size Manual.ZhDocString.Ch19Ch20.G7.c014}

{zhdocstring UInt16.size Manual.ZhDocString.Ch19Ch20.G7.c015}

{zhdocstring Int16.size Manual.ZhDocString.Ch19Ch20.G7.c016}

{zhdocstring UInt32.size Manual.ZhDocString.Ch19Ch20.G7.c017}

{zhdocstring Int32.size Manual.ZhDocString.Ch19Ch20.G7.c018}

{zhdocstring UInt64.size Manual.ZhDocString.Ch19Ch20.G7.c019}

{zhdocstring Int64.size Manual.ZhDocString.Ch19Ch20.G7.c020}

## 范围

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Ranges"
%%%
{zhdocstring ISize.minValue Manual.ZhDocString.Ch19Ch20.G7.c021}

{zhdocstring ISize.maxValue Manual.ZhDocString.Ch19Ch20.G7.c022}

{zhdocstring Int8.minValue Manual.ZhDocString.Ch19Ch20.G7.c023}

{zhdocstring Int8.maxValue Manual.ZhDocString.Ch19Ch20.G7.c024}

{zhdocstring Int16.minValue Manual.ZhDocString.Ch19Ch20.G7.c025}

{zhdocstring Int16.maxValue Manual.ZhDocString.Ch19Ch20.G7.c026}

{zhdocstring Int32.minValue Manual.ZhDocString.Ch19Ch20.G7.c027}

{zhdocstring Int32.maxValue Manual.ZhDocString.Ch19Ch20.G7.c028}

{zhdocstring Int64.minValue Manual.ZhDocString.Ch19Ch20.G7.c029}

{zhdocstring Int64.maxValue Manual.ZhDocString.Ch19Ch20.G7.c030}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions"
%%%
### 到/从 `Int` 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From--Int"
%%%
{zhdocstring ISize.toInt Manual.ZhDocString.Ch19Ch20.G7.c031}

{zhdocstring Int8.toInt Manual.ZhDocString.Ch19Ch20.G7.c032}

{zhdocstring Int16.toInt Manual.ZhDocString.Ch19Ch20.G7.c033}

{zhdocstring Int32.toInt Manual.ZhDocString.Ch19Ch20.G7.c034}

{zhdocstring Int64.toInt Manual.ZhDocString.Ch19Ch20.G7.c035}


{zhdocstring ISize.ofInt Manual.ZhDocString.Ch19Ch20.G7.c036}

{zhdocstring Int8.ofInt Manual.ZhDocString.Ch19Ch20.G7.c037}

{zhdocstring Int16.ofInt Manual.ZhDocString.Ch19Ch20.G7.c038}

{zhdocstring Int32.ofInt Manual.ZhDocString.Ch19Ch20.G7.c039}

{zhdocstring Int64.ofInt Manual.ZhDocString.Ch19Ch20.G7.c040}


{zhdocstring ISize.ofIntClamp Manual.ZhDocString.Ch19Ch20.G7.c041}

{zhdocstring Int8.ofIntClamp Manual.ZhDocString.Ch19Ch20.G7.c042}

{zhdocstring Int16.ofIntClamp Manual.ZhDocString.Ch19Ch20.G7.c043}

{zhdocstring Int32.ofIntClamp Manual.ZhDocString.Ch19Ch20.G7.c044}

{zhdocstring Int64.ofIntClamp Manual.ZhDocString.Ch19Ch20.G7.c045}


{zhdocstring ISize.ofIntLE Manual.ZhDocString.Ch19Ch20.G7.c046}

{zhdocstring Int8.ofIntLE Manual.ZhDocString.Ch19Ch20.G7.c047}

{zhdocstring Int16.ofIntLE Manual.ZhDocString.Ch19Ch20.G7.c048}

{zhdocstring Int32.ofIntLE Manual.ZhDocString.Ch19Ch20.G7.c049}

{zhdocstring Int64.ofIntLE Manual.ZhDocString.Ch19Ch20.G7.c050}


### 到/从 `Nat` 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From--Nat"
%%%
{zhdocstring USize.ofNat Manual.ZhDocString.Ch19Ch20.G7.c051}

{zhdocstring ISize.ofNat Manual.ZhDocString.Ch19Ch20.G7.c052}

{zhdocstring UInt8.ofNat Manual.ZhDocString.Ch19Ch20.G7.c053}

{zhdocstring Int8.ofNat Manual.ZhDocString.Ch19Ch20.G7.c054}

{zhdocstring UInt16.ofNat Manual.ZhDocString.Ch19Ch20.G7.c055}

{zhdocstring Int16.ofNat Manual.ZhDocString.Ch19Ch20.G7.c056}

{zhdocstring UInt32.ofNat Manual.ZhDocString.Ch19Ch20.G7.c057}

{zhdocstring Int32.ofNat Manual.ZhDocString.Ch19Ch20.G7.c058}

{zhdocstring UInt64.ofNat Manual.ZhDocString.Ch19Ch20.G7.c059}

{zhdocstring Int64.ofNat Manual.ZhDocString.Ch19Ch20.G7.c060}

{zhdocstring USize.ofNat32 Manual.ZhDocString.Ch19Ch20.G7.c061}

{zhdocstring USize.ofNatLT Manual.ZhDocString.Ch19Ch20.G7.c062}

{zhdocstring UInt8.ofNatLT Manual.ZhDocString.Ch19Ch20.G7.c063}

{zhdocstring UInt16.ofNatLT Manual.ZhDocString.Ch19Ch20.G7.c064}

{zhdocstring UInt32.ofNatLT Manual.ZhDocString.Ch19Ch20.G7.c065}

{zhdocstring UInt64.ofNatLT Manual.ZhDocString.Ch19Ch20.G7.c066}

{zhdocstring USize.ofNatClamp Manual.ZhDocString.Ch19Ch20.G7.c067}

{zhdocstring UInt8.ofNatClamp Manual.ZhDocString.Ch19Ch20.G7.c068}

{zhdocstring UInt16.ofNatClamp Manual.ZhDocString.Ch19Ch20.G7.c069}

{zhdocstring UInt32.ofNatClamp Manual.ZhDocString.Ch19Ch20.G7.c070}

{zhdocstring UInt64.ofNatClamp Manual.ZhDocString.Ch19Ch20.G7.c071}

{zhdocstring USize.toNat Manual.ZhDocString.Ch19Ch20.G7.c072}

{zhdocstring ISize.toNatClampNeg Manual.ZhDocString.Ch19Ch20.G7.c073}

{zhdocstring UInt8.toNat Manual.ZhDocString.Ch19Ch20.G7.c074}

{zhdocstring Int8.toNatClampNeg Manual.ZhDocString.Ch19Ch20.G7.c075}

{zhdocstring UInt16.toNat Manual.ZhDocString.Ch19Ch20.G7.c076}

{zhdocstring Int16.toNatClampNeg Manual.ZhDocString.Ch19Ch20.G7.c077}

{zhdocstring UInt32.toNat Manual.ZhDocString.Ch19Ch20.G7.c078}

{zhdocstring Int32.toNatClampNeg Manual.ZhDocString.Ch19Ch20.G7.c079}

{zhdocstring UInt64.toNat Manual.ZhDocString.Ch19Ch20.G7.c080}

{zhdocstring Int64.toNatClampNeg Manual.ZhDocString.Ch19Ch20.G7.c081}


### 到其他固定宽度整数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Other-Fixed-Width-Integers"
%%%
{zhdocstring USize.toUInt8 Manual.ZhDocString.Ch19Ch20.G7.c082}

{zhdocstring USize.toUInt16 Manual.ZhDocString.Ch19Ch20.G7.c083}

{zhdocstring USize.toUInt32 Manual.ZhDocString.Ch19Ch20.G7.c084}

{zhdocstring USize.toUInt64 Manual.ZhDocString.Ch19Ch20.G7.c085}

{zhdocstring USize.toISize Manual.ZhDocString.Ch19Ch20.G7.c086}


{zhdocstring UInt8.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c087}

{zhdocstring UInt8.toUInt16 Manual.ZhDocString.Ch19Ch20.G7.c088}

{zhdocstring UInt8.toUInt32 Manual.ZhDocString.Ch19Ch20.G7.c089}

{zhdocstring UInt8.toUInt64 Manual.ZhDocString.Ch19Ch20.G7.c090}

{zhdocstring UInt8.toUSize Manual.ZhDocString.Ch19Ch20.G7.c091}


{zhdocstring UInt16.toUInt8 Manual.ZhDocString.Ch19Ch20.G7.c092}

{zhdocstring UInt16.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c093}

{zhdocstring UInt16.toUInt32 Manual.ZhDocString.Ch19Ch20.G7.c094}

{zhdocstring UInt16.toUInt64 Manual.ZhDocString.Ch19Ch20.G7.c095}

{zhdocstring UInt16.toUSize Manual.ZhDocString.Ch19Ch20.G7.c096}


{zhdocstring UInt32.toUInt8 Manual.ZhDocString.Ch19Ch20.G7.c097}

{zhdocstring UInt32.toUInt16 Manual.ZhDocString.Ch19Ch20.G7.c098}

{zhdocstring UInt32.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c099}

{zhdocstring UInt32.toUInt64 Manual.ZhDocString.Ch19Ch20.G7.c100}

{zhdocstring UInt32.toUSize Manual.ZhDocString.Ch19Ch20.G7.c101}


{zhdocstring UInt64.toUInt8 Manual.ZhDocString.Ch19Ch20.G7.c102}

{zhdocstring UInt64.toUInt16 Manual.ZhDocString.Ch19Ch20.G7.c103}

{zhdocstring UInt64.toUInt32 Manual.ZhDocString.Ch19Ch20.G7.c104}

{zhdocstring UInt64.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c105}

{zhdocstring UInt64.toUSize Manual.ZhDocString.Ch19Ch20.G7.c106}


{zhdocstring ISize.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c107}

{zhdocstring ISize.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c108}

{zhdocstring ISize.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c109}

{zhdocstring ISize.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c110}


{zhdocstring Int8.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c111}

{zhdocstring Int8.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c112}

{zhdocstring Int8.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c113}

{zhdocstring Int8.toISize Manual.ZhDocString.Ch19Ch20.G7.c114}


{zhdocstring Int16.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c115}

{zhdocstring Int16.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c116}

{zhdocstring Int16.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c117}

{zhdocstring Int16.toISize Manual.ZhDocString.Ch19Ch20.G7.c118}


{zhdocstring Int32.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c119}

{zhdocstring Int32.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c120}

{zhdocstring Int32.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c121}

{zhdocstring Int32.toISize Manual.ZhDocString.Ch19Ch20.G7.c122}


{zhdocstring Int64.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c123}

{zhdocstring Int64.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c124}

{zhdocstring Int64.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c125}

{zhdocstring Int64.toISize Manual.ZhDocString.Ch19Ch20.G7.c126}



### 到浮点数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Floating-Point-Numbers"
%%%
{zhdocstring ISize.toFloat Manual.ZhDocString.Ch19Ch20.G7.c127}

{zhdocstring ISize.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c128}

{zhdocstring Int8.toFloat Manual.ZhDocString.Ch19Ch20.G7.c129}

{zhdocstring Int8.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c130}

{zhdocstring Int16.toFloat Manual.ZhDocString.Ch19Ch20.G7.c131}

{zhdocstring Int16.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c132}

{zhdocstring Int32.toFloat Manual.ZhDocString.Ch19Ch20.G7.c133}

{zhdocstring Int32.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c134}

{zhdocstring Int64.toFloat Manual.ZhDocString.Ch19Ch20.G7.c135}

{zhdocstring Int64.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c136}

{zhdocstring USize.toFloat Manual.ZhDocString.Ch19Ch20.G7.c137}

{zhdocstring USize.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c138}

{zhdocstring UInt8.toFloat Manual.ZhDocString.Ch19Ch20.G7.c139}

{zhdocstring UInt8.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c140}

{zhdocstring UInt16.toFloat Manual.ZhDocString.Ch19Ch20.G7.c141}

{zhdocstring UInt16.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c142}

{zhdocstring UInt32.toFloat Manual.ZhDocString.Ch19Ch20.G7.c143}

{zhdocstring UInt32.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c144}

{zhdocstring UInt64.toFloat Manual.ZhDocString.Ch19Ch20.G7.c145}

{zhdocstring UInt64.toFloat32 Manual.ZhDocString.Ch19Ch20.G7.c146}

### 到/从位向量转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From-Bitvectors"
%%%
{zhdocstring ISize.toBitVec Manual.ZhDocString.Ch19Ch20.G7.c147}

{zhdocstring ISize.ofBitVec Manual.ZhDocString.Ch19Ch20.G7.c148}

{zhdocstring Int8.toBitVec Manual.ZhDocString.Ch19Ch20.G7.c149}

{zhdocstring Int8.ofBitVec Manual.ZhDocString.Ch19Ch20.G7.c150}

{zhdocstring Int16.toBitVec Manual.ZhDocString.Ch19Ch20.G7.c151}

{zhdocstring Int16.ofBitVec Manual.ZhDocString.Ch19Ch20.G7.c152}

{zhdocstring Int32.toBitVec Manual.ZhDocString.Ch19Ch20.G7.c153}

{zhdocstring Int32.ofBitVec Manual.ZhDocString.Ch19Ch20.G7.c154}

{zhdocstring Int64.toBitVec Manual.ZhDocString.Ch19Ch20.G7.c155}

{zhdocstring Int64.ofBitVec Manual.ZhDocString.Ch19Ch20.G7.c156}

### 到/从有限数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From-Finite-Numbers"
%%%
{zhdocstring USize.toFin Manual.ZhDocString.Ch19Ch20.G7.c157}

{zhdocstring UInt8.toFin Manual.ZhDocString.Ch19Ch20.G7.c158}

{zhdocstring UInt16.toFin Manual.ZhDocString.Ch19Ch20.G7.c159}

{zhdocstring UInt32.toFin Manual.ZhDocString.Ch19Ch20.G7.c160}

{zhdocstring UInt64.toFin Manual.ZhDocString.Ch19Ch20.G7.c161}

{zhdocstring USize.ofFin Manual.ZhDocString.Ch19Ch20.G7.c162}

{zhdocstring UInt8.ofFin Manual.ZhDocString.Ch19Ch20.G7.c163}

{zhdocstring UInt16.ofFin Manual.ZhDocString.Ch19Ch20.G7.c164}

{zhdocstring UInt32.ofFin Manual.ZhDocString.Ch19Ch20.G7.c165}

{zhdocstring UInt64.ofFin Manual.ZhDocString.Ch19Ch20.G7.c166}

{zhdocstring USize.repr Manual.ZhDocString.Ch19Ch20.G7.c167}

### 到字符转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Characters"
%%%
{name}`Char` 类型是对 {name}`UInt32` 的包装器，它需要一个证明，证明所包装的整数表示一个 Unicode 代码点。
该谓词是 {name}`UInt32` API 的一部分。

{zhdocstring UInt32.isValidChar Manual.ZhDocString.Ch19Ch20.G7.c168}

{include 2 Manual.BasicTypes.UInt.Comparisons}

{include 2 Manual.BasicTypes.UInt.Arith}

## 按位操作

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Bitwise-Operations"
%%%
通常，对固定宽度整数的按位操作应该使用 Lean 的重载运算符来访问，特别是它们对 {name}`ShiftLeft`、{name}`ShiftRight`、{name}`AndOp`、{name}`OrOp` 和 {name}`XorOp` 的实例。

```lean -show
-- 检查所有这些实例是否确实存在
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let classes := [`ShiftLeft, `ShiftRight, `AndOp, `OrOp, `XorOp]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
```

{zhdocstring USize.land Manual.ZhDocString.Ch19Ch20.G7.c169}

{zhdocstring ISize.land Manual.ZhDocString.Ch19Ch20.G7.c170}

{zhdocstring UInt8.land Manual.ZhDocString.Ch19Ch20.G7.c171}

{zhdocstring Int8.land Manual.ZhDocString.Ch19Ch20.G7.c172}

{zhdocstring UInt16.land Manual.ZhDocString.Ch19Ch20.G7.c173}

{zhdocstring Int16.land Manual.ZhDocString.Ch19Ch20.G7.c174}

{zhdocstring UInt32.land Manual.ZhDocString.Ch19Ch20.G7.c175}

{zhdocstring Int32.land Manual.ZhDocString.Ch19Ch20.G7.c176}

{zhdocstring UInt64.land Manual.ZhDocString.Ch19Ch20.G7.c177}

{zhdocstring Int64.land Manual.ZhDocString.Ch19Ch20.G7.c178}

{zhdocstring USize.lor Manual.ZhDocString.Ch19Ch20.G7.c179}

{zhdocstring ISize.lor Manual.ZhDocString.Ch19Ch20.G7.c180}

{zhdocstring UInt8.lor Manual.ZhDocString.Ch19Ch20.G7.c181}

{zhdocstring Int8.lor Manual.ZhDocString.Ch19Ch20.G7.c182}

{zhdocstring UInt16.lor Manual.ZhDocString.Ch19Ch20.G7.c183}

{zhdocstring Int16.lor Manual.ZhDocString.Ch19Ch20.G7.c184}

{zhdocstring UInt32.lor Manual.ZhDocString.Ch19Ch20.G7.c185}

{zhdocstring Int32.lor Manual.ZhDocString.Ch19Ch20.G7.c186}

{zhdocstring UInt64.lor Manual.ZhDocString.Ch19Ch20.G7.c187}

{zhdocstring Int64.lor Manual.ZhDocString.Ch19Ch20.G7.c188}

{zhdocstring USize.xor Manual.ZhDocString.Ch19Ch20.G7.c189}

{zhdocstring ISize.xor Manual.ZhDocString.Ch19Ch20.G7.c190}

{zhdocstring UInt8.xor Manual.ZhDocString.Ch19Ch20.G7.c191}

{zhdocstring Int8.xor Manual.ZhDocString.Ch19Ch20.G7.c192}

{zhdocstring UInt16.xor Manual.ZhDocString.Ch19Ch20.G7.c193}

{zhdocstring Int16.xor Manual.ZhDocString.Ch19Ch20.G7.c194}

{zhdocstring UInt32.xor Manual.ZhDocString.Ch19Ch20.G7.c195}

{zhdocstring Int32.xor Manual.ZhDocString.Ch19Ch20.G7.c196}

{zhdocstring UInt64.xor Manual.ZhDocString.Ch19Ch20.G7.c197}

{zhdocstring Int64.xor Manual.ZhDocString.Ch19Ch20.G7.c198}

{zhdocstring USize.complement Manual.ZhDocString.Ch19Ch20.G7.c199}

{zhdocstring ISize.complement Manual.ZhDocString.Ch19Ch20.G7.c200}

{zhdocstring UInt8.complement Manual.ZhDocString.Ch19Ch20.G7.c201}

{zhdocstring Int8.complement Manual.ZhDocString.Ch19Ch20.G7.c202}

{zhdocstring UInt16.complement Manual.ZhDocString.Ch19Ch20.G7.c203}

{zhdocstring Int16.complement Manual.ZhDocString.Ch19Ch20.G7.c204}

{zhdocstring UInt32.complement Manual.ZhDocString.Ch19Ch20.G7.c205}

{zhdocstring Int32.complement Manual.ZhDocString.Ch19Ch20.G7.c206}

{zhdocstring UInt64.complement Manual.ZhDocString.Ch19Ch20.G7.c207}

{zhdocstring Int64.complement Manual.ZhDocString.Ch19Ch20.G7.c208}

{zhdocstring USize.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c209}

{zhdocstring ISize.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c210}

{zhdocstring UInt8.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c211}

{zhdocstring Int8.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c212}

{zhdocstring UInt16.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c213}

{zhdocstring Int16.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c214}

{zhdocstring UInt32.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c215}

{zhdocstring Int32.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c216}

{zhdocstring UInt64.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c217}

{zhdocstring Int64.shiftLeft Manual.ZhDocString.Ch19Ch20.G7.c218}

{zhdocstring USize.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c219}

{zhdocstring ISize.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c220}

{zhdocstring UInt8.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c221}

{zhdocstring Int8.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c222}

{zhdocstring UInt16.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c223}

{zhdocstring Int16.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c224}

{zhdocstring UInt32.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c225}

{zhdocstring Int32.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c226}

{zhdocstring UInt64.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c227}


{zhdocstring Int64.shiftRight Manual.ZhDocString.Ch19Ch20.G7.c228}
