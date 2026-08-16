/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G5

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "有限自然数" =>
%%%
tag := "Fin"
%%%

```lean -show
section
variable (n : Nat)
```

对于任何{tech (key := "natural number")}[自然数] {lean}`n`，{lean}`Fin n` 是一种包含所有严格小于 {lean}`n` 的自然数的类型。
换句话说，{lean}`Fin n` 恰好有 {lean}`n` 个元素。
它可用于表示列表或数组的有效索引，或者可用作规范的 {lean}`n` 元素类型。

{zhdocstring Fin Manual.ZhDocString.Ch19Ch20.G5.c109}

{lean}`Fin` 与 {name}`UInt8`、{name}`UInt16`、{name}`UInt32`、{name}`UInt64` 和 {name}`USize` 密切相关，它们也表示有限的非负整数类型。
然而，这些类型是由位向量而不是由自然数支持的，并且它们具有固定的边界。
{lean}`Fin` 相对更灵活，但在进行底层推理时不够方便。
特别是，使用位向量而不是证明某个数小于 2 的某个幂，可以避免必须小心翼翼地防止对具体边界求值的问题。

# 运行时特征

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--Run-Time-Characteristics"
%%%
因为 {lean}`Fin n` 是一种只有一个字段不是证明的结构体，所以它是一个{ref "inductive-types-trivial-wrappers"}[平凡包装器]。
这意味着它在编译代码中的表示与底层的自然数相同。

# 强制转换和字面量

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--Coercions-and-Literals"
%%%
从 {lean}`Fin n` 到 {lean}`Nat` 有一个{tech (key := "coercion")}[强制转换]，它会丢弃该数字小于边界的证明。
具体来说，这个强制转换正是投影 {name}`Fin.val`。
这带来的一个后果是，{name}`Fin.val` 的使用在证明状态中会显示为强制转换，而不是显式的投影。
:::example "从 {name}`Fin` 强制转换到 {name}`Nat`"
{lean}`Fin n` 可以用在预期 {lean}`Nat` 的地方：
```lean (name := oneFinCoe)
#eval let one : Fin 3 := ⟨1, by omega⟩; (one : Nat)
```
```leanOutput oneFinCoe
1
```

{name}`Fin.val` 的使用在证明状态中显示为强制转换：
```proofState
∀(n : Nat) (i : Fin n), i < n := by
  intro n i
/--
n : Nat
i : Fin n
⊢ ↑i < n
-/

```
:::

自然数字面量可用于 {lean}`Fin` 类型，通常通过 {name}`OfNat` 实例实现。
{name}`OfNat` 为 {lean}`Fin n` 提供的实例要求上限 {lean}`n` 不为零，但不检查字面量是否小于 {lean}`n`。
如果字面量大于该类型所能表示的范围，则使用将其除以 {lean}`n` 的余数。

:::example "{name}`Fin` 的数字字面量"

如果 {lean}`n > 0`，则自然数字面量可用于 {lean}`Fin n`：
```lean
example : Fin 5 := 3
example : Fin 20 := 19
```
当字面量大于或等于 {lean}`n` 时，则使用除以 {lean}`n` 时的余数：
```lean (name := fivethree)
#eval (5 : Fin 3)
```
```leanOutput fivethree
2
```
```lean (name := fourthree)
#eval ([0, 1, 2, 3, 4, 5, 6] : List (Fin 3))
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```

如果 Lean 无法综合 {lean}`NeZero n` 的实例，那么就没有 {lean}`OfNat (Fin n)` 实例：
```lean +error (name := fin0)
example : Fin 0 := 0
```
```leanOutput fin0
failed to synthesize instance of type class
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

```lean +error (name := finK)
example (k : Nat) : Fin k := 0
```
```leanOutput finK
failed to synthesize instance of type class
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

# API 参考

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference"
%%%
## 构造

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Construction"
%%%
{zhdocstring Fin.last Manual.ZhDocString.Ch19Ch20.G5.c110}

{zhdocstring Fin.succ Manual.ZhDocString.Ch19Ch20.G5.c111}

{zhdocstring Fin.pred Manual.ZhDocString.Ch19Ch20.G5.c112}

## 算术

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Arithmetic"
%%%
通常，对 {name}`Fin` 的算术运算应该使用 Lean 的重载算术符号来访问，特别是通过实例 {inst}`Add (Fin n)`、{inst}`Sub (Fin n)`、{inst}`Mul (Fin n)`、{inst}`Div (Fin n)` 和 {inst}`Mod (Fin n)`。
异质运算符（例如 {lean}`Fin.natAdd`）没有对应的异质实例（例如 {name}`HAdd`），以避免产生令人困惑的类型推断行为。

{zhdocstring Fin.add Manual.ZhDocString.Ch19Ch20.G5.c113}

{zhdocstring Fin.natAdd Manual.ZhDocString.Ch19Ch20.G5.c114}

{zhdocstring Fin.addNat Manual.ZhDocString.Ch19Ch20.G5.c115}

{zhdocstring Fin.mul Manual.ZhDocString.Ch19Ch20.G5.c116}

{zhdocstring Fin.sub Manual.ZhDocString.Ch19Ch20.G5.c117}

{zhdocstring Fin.subNat Manual.ZhDocString.Ch19Ch20.G5.c118}

{zhdocstring Fin.div Manual.ZhDocString.Ch19Ch20.G5.c119}

{zhdocstring Fin.mod Manual.ZhDocString.Ch19Ch20.G5.c120}

{zhdocstring Fin.modn Manual.ZhDocString.Ch19Ch20.G5.c121}

{zhdocstring Fin.log2 Manual.ZhDocString.Ch19Ch20.G5.c122}

## 按位运算

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Bitwise-Operations"
%%%
通常，对 {name}`Fin` 的按位运算应该使用 Lean 的重载按位运算符来访问，特别是通过实例 {inst}`ShiftLeft (Fin n)`、{inst}`ShiftRight (Fin n)`、{inst}`AndOp (Fin n)`、{inst}`OrOp (Fin n)`、{inst}`Xor (Fin n)`

{zhdocstring Fin.shiftLeft Manual.ZhDocString.Ch19Ch20.G5.c123}

{zhdocstring Fin.shiftRight Manual.ZhDocString.Ch19Ch20.G5.c124}

{zhdocstring Fin.land Manual.ZhDocString.Ch19Ch20.G5.c125}

{zhdocstring Fin.lor Manual.ZhDocString.Ch19Ch20.G5.c126}

{zhdocstring Fin.xor Manual.ZhDocString.Ch19Ch20.G5.c127}


## 转换

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Conversions"
%%%
{zhdocstring Fin.toNat Manual.ZhDocString.Ch19Ch20.G5.c128}

{zhdocstring Fin.ofNat Manual.ZhDocString.Ch19Ch20.G5.c129}

{zhdocstring Fin.cast Manual.ZhDocString.Ch19Ch20.G5.c130}

{zhdocstring Fin.castLT Manual.ZhDocString.Ch19Ch20.G5.c131}

{zhdocstring Fin.castLE Manual.ZhDocString.Ch19Ch20.G5.c132}

{zhdocstring Fin.castAdd Manual.ZhDocString.Ch19Ch20.G5.c133}

{zhdocstring Fin.castSucc Manual.ZhDocString.Ch19Ch20.G5.c134}

{zhdocstring Fin.rev Manual.ZhDocString.Ch19Ch20.G5.c135}

{zhdocstring Fin.elim0 Manual.ZhDocString.Ch19Ch20.G5.c136}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Iteration"
%%%
{zhdocstring Fin.foldr Manual.ZhDocString.Ch19Ch20.G5.c137}

{zhdocstring Fin.foldrM Manual.ZhDocString.Ch19Ch20.G5.c138}

{zhdocstring Fin.foldl Manual.ZhDocString.Ch19Ch20.G5.c139}

{zhdocstring Fin.foldlM Manual.ZhDocString.Ch19Ch20.G5.c140}

{zhdocstring Fin.hIterate Manual.ZhDocString.Ch19Ch20.G5.c141}

{zhdocstring Fin.hIterateFrom Manual.ZhDocString.Ch19Ch20.G5.c142}

## 推理

%%%
tag := "Lean-__________________--Basic-Types--Finite-Natural-Numbers--API-Reference--Reasoning"
%%%
{zhdocstring Fin.induction Manual.ZhDocString.Ch19Ch20.G5.c143}

{zhdocstring Fin.inductionOn Manual.ZhDocString.Ch19Ch20.G5.c144}

{zhdocstring Fin.reverseInduction Manual.ZhDocString.Ch19Ch20.G5.c145}

{zhdocstring Fin.cases Manual.ZhDocString.Ch19Ch20.G5.c146}

{zhdocstring Fin.lastCases Manual.ZhDocString.Ch19Ch20.G5.c147}

{zhdocstring Fin.addCases Manual.ZhDocString.Ch19Ch20.G5.c148}

{zhdocstring Fin.succRec Manual.ZhDocString.Ch19Ch20.G5.c149}

{zhdocstring Fin.succRecOn Manual.ZhDocString.Ch19Ch20.G5.c150}
