/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.UInt.Comparisons
import Manual.BasicTypes.UInt.Arith

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "定精度整数" =>
%%%
tag := "fixed-ints"
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
{docstring USize}

{docstring UInt8}

{docstring UInt16}

{docstring UInt32}

{docstring UInt64}

## 有符号

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--Logical-Model--Signed"
%%%
{docstring ISize}

{docstring Int8}

{docstring Int16}

{docstring Int32}

{docstring Int64}

# 运行时表示
%%%
tag := "fixed-int-runtime"
%%%

在需要{tech (key := "boxed")}[装箱]表示的上下文中，在编译后的代码里，适合在比平台指针大小少一位的空间内容纳的固定宽度整数类型总是被表示而无需额外的分配或间接寻址。
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
有符号类型，根据底层的二进制补码表示进行解释。

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

{docstring USize.size}

{docstring ISize.size}

{docstring UInt8.size}

{docstring Int8.size}

{docstring UInt16.size}

{docstring Int16.size}

{docstring UInt32.size}

{docstring Int32.size}

{docstring UInt64.size}

{docstring Int64.size}

## 范围

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Ranges"
%%%
{docstring ISize.minValue}

{docstring ISize.maxValue}

{docstring Int8.minValue}

{docstring Int8.maxValue}

{docstring Int16.minValue}

{docstring Int16.maxValue}

{docstring Int32.minValue}

{docstring Int32.maxValue}

{docstring Int64.minValue}

{docstring Int64.maxValue}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions"
%%%
### 到/从 `Int` 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From--Int"
%%%
{docstring ISize.toInt}

{docstring Int8.toInt}

{docstring Int16.toInt}

{docstring Int32.toInt}

{docstring Int64.toInt}


{docstring ISize.ofInt}

{docstring Int8.ofInt}

{docstring Int16.ofInt}

{docstring Int32.ofInt}

{docstring Int64.ofInt}


{docstring ISize.ofIntClamp}

{docstring Int8.ofIntClamp}

{docstring Int16.ofIntClamp}

{docstring Int32.ofIntClamp}

{docstring Int64.ofIntClamp}


{docstring ISize.ofIntLE}

{docstring Int8.ofIntLE}

{docstring Int16.ofIntLE}

{docstring Int32.ofIntLE}

{docstring Int64.ofIntLE}


### 到/从 `Nat` 转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From--Nat"
%%%
{docstring USize.ofNat}

{docstring ISize.ofNat}

{docstring UInt8.ofNat}

{docstring Int8.ofNat}

{docstring UInt16.ofNat}

{docstring Int16.ofNat}

{docstring UInt32.ofNat}

{docstring Int32.ofNat}

{docstring UInt64.ofNat}

{docstring Int64.ofNat}

{docstring USize.ofNat32}

{docstring USize.ofNatLT}

{docstring UInt8.ofNatLT}

{docstring UInt16.ofNatLT}

{docstring UInt32.ofNatLT}

{docstring UInt64.ofNatLT}

{docstring USize.ofNatClamp}

{docstring UInt8.ofNatClamp}

{docstring UInt16.ofNatClamp}

{docstring UInt32.ofNatClamp}

{docstring UInt64.ofNatClamp}

{docstring USize.toNat}

{docstring ISize.toNatClampNeg}

{docstring UInt8.toNat}

{docstring Int8.toNatClampNeg}

{docstring UInt16.toNat}

{docstring Int16.toNatClampNeg}

{docstring UInt32.toNat}

{docstring Int32.toNatClampNeg}

{docstring UInt64.toNat}

{docstring Int64.toNatClampNeg}


### 到其他固定宽度整数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Other-Fixed-Width-Integers"
%%%
{docstring USize.toUInt8}

{docstring USize.toUInt16}

{docstring USize.toUInt32}

{docstring USize.toUInt64}

{docstring USize.toISize}


{docstring UInt8.toInt8}

{docstring UInt8.toUInt16}

{docstring UInt8.toUInt32}

{docstring UInt8.toUInt64}

{docstring UInt8.toUSize}


{docstring UInt16.toUInt8}

{docstring UInt16.toInt16}

{docstring UInt16.toUInt32}

{docstring UInt16.toUInt64}

{docstring UInt16.toUSize}


{docstring UInt32.toUInt8}

{docstring UInt32.toUInt16}

{docstring UInt32.toInt32}

{docstring UInt32.toUInt64}

{docstring UInt32.toUSize}


{docstring UInt64.toUInt8}

{docstring UInt64.toUInt16}

{docstring UInt64.toUInt32}

{docstring UInt64.toInt64}

{docstring UInt64.toUSize}


{docstring ISize.toInt8}

{docstring ISize.toInt16}

{docstring ISize.toInt32}

{docstring ISize.toInt64}


{docstring Int8.toInt16}

{docstring Int8.toInt32}

{docstring Int8.toInt64}

{docstring Int8.toISize}


{docstring Int16.toInt8}

{docstring Int16.toInt32}

{docstring Int16.toInt64}

{docstring Int16.toISize}


{docstring Int32.toInt8}

{docstring Int32.toInt16}

{docstring Int32.toInt64}

{docstring Int32.toISize}


{docstring Int64.toInt8}

{docstring Int64.toInt16}

{docstring Int64.toInt32}

{docstring Int64.toISize}



### 到浮点数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Floating-Point-Numbers"
%%%
{docstring ISize.toFloat}

{docstring ISize.toFloat32}

{docstring Int8.toFloat}

{docstring Int8.toFloat32}

{docstring Int16.toFloat}

{docstring Int16.toFloat32}

{docstring Int32.toFloat}

{docstring Int32.toFloat32}

{docstring Int64.toFloat}

{docstring Int64.toFloat32}

{docstring USize.toFloat}

{docstring USize.toFloat32}

{docstring UInt8.toFloat}

{docstring UInt8.toFloat32}

{docstring UInt16.toFloat}

{docstring UInt16.toFloat32}

{docstring UInt32.toFloat}

{docstring UInt32.toFloat32}

{docstring UInt64.toFloat}

{docstring UInt64.toFloat32}

### 到/从位向量转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From-Bitvectors"
%%%
{docstring ISize.toBitVec}

{docstring ISize.ofBitVec}

{docstring Int8.toBitVec}

{docstring Int8.ofBitVec}

{docstring Int16.toBitVec}

{docstring Int16.ofBitVec}

{docstring Int32.toBitVec}

{docstring Int32.ofBitVec}

{docstring Int64.toBitVec}

{docstring Int64.ofBitVec}

### 到/从有限数转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-and-From-Finite-Numbers"
%%%
{docstring USize.toFin}

{docstring UInt8.toFin}

{docstring UInt16.toFin}

{docstring UInt32.toFin}

{docstring UInt64.toFin}

{docstring USize.ofFin}

{docstring UInt8.ofFin}

{docstring UInt16.ofFin}

{docstring UInt32.ofFin}

{docstring UInt64.ofFin}

{docstring USize.repr}

### 到字符转换

%%%
tag := "Lean-__________________--Basic-Types--Fixed-Precision-Integers--API-Reference--Conversions--To-Characters"
%%%
{name}`Char` 类型是对 {name}`UInt32` 的包装器，它需要一个证明，证明所包装的整数表示一个 Unicode 代码点。
该谓词是 {name}`UInt32` API 的一部分。

{docstring UInt32.isValidChar}

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

{docstring USize.land}

{docstring ISize.land}

{docstring UInt8.land}

{docstring Int8.land}

{docstring UInt16.land}

{docstring Int16.land}

{docstring UInt32.land}

{docstring Int32.land}

{docstring UInt64.land}

{docstring Int64.land}

{docstring USize.lor}

{docstring ISize.lor}

{docstring UInt8.lor}

{docstring Int8.lor}

{docstring UInt16.lor}

{docstring Int16.lor}

{docstring UInt32.lor}

{docstring Int32.lor}

{docstring UInt64.lor}

{docstring Int64.lor}

{docstring USize.xor}

{docstring ISize.xor}

{docstring UInt8.xor}

{docstring Int8.xor}

{docstring UInt16.xor}

{docstring Int16.xor}

{docstring UInt32.xor}

{docstring Int32.xor}

{docstring UInt64.xor}

{docstring Int64.xor}

{docstring USize.complement}

{docstring ISize.complement}

{docstring UInt8.complement}

{docstring Int8.complement}

{docstring UInt16.complement}

{docstring Int16.complement}

{docstring UInt32.complement}

{docstring Int32.complement}

{docstring UInt64.complement}

{docstring Int64.complement}

{docstring USize.shiftLeft}

{docstring ISize.shiftLeft}

{docstring UInt8.shiftLeft}

{docstring Int8.shiftLeft}

{docstring UInt16.shiftLeft}

{docstring Int16.shiftLeft}

{docstring UInt32.shiftLeft}

{docstring Int32.shiftLeft}

{docstring UInt64.shiftLeft}

{docstring Int64.shiftLeft}

{docstring USize.shiftRight}

{docstring ISize.shiftRight}

{docstring UInt8.shiftRight}

{docstring Int8.shiftRight}

{docstring UInt16.shiftRight}

{docstring Int16.shiftRight}

{docstring UInt32.shiftRight}

{docstring Int32.shiftRight}

{docstring UInt64.shiftRight}


{docstring Int64.shiftRight}
