/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.typography.dashes false -- 下文引用图 5-2，此处不应使用短破折号

set_option maxRecDepth 768

#doc (Manual) "位向量" =>
%%%
tag := "BitVec"
%%%

位向量是固定宽度的二进制数字序列。
它们经常用于软件验证，因为它们能贴切地建模与硬件相似的高效数据结构和操作。
位向量可以从两个角度来理解：既可视为位的序列，也可视为由位序列编码的数。
当位向量表示一个数时，它既可以表示有符号数，也可以表示无符号数。
有符号数采用二进制补码形式表示。

# 逻辑模型

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--Logical-Model"
%%%
位向量表示为对具有适当界限的 {name}`Fin` 的包装。
由于 {name}`Fin` 本身是对 {name}`Nat` 的包装，位向量能够利用内核对自然数高效计算的特殊支持。

{docstring BitVec}

# 运行时表示

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--Runtime-Representation"
%%%
位向量表示为具有相应范围的 {lean}`Fin`。
由于 {name}`BitVec` 是对 {name}`Fin` 的{ref "inductive-types-trivial-wrappers"}[平凡包装]，而 {name}`Fin` 又是对 {name}`Nat` 的平凡包装，因此在编译后的代码中，位向量与 {name}`Nat` 使用相同的运行时表示。

# 语法
%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--Syntax"
%%%
:::leanSection
```lean -show
variable {w n : Nat}
```
实例 {inst}`OfNat (BitVec w) n` 对所有宽度 {lean}`w` 和自然数 {lean}`n` 都存在。
在预期类型已知的上下文中，可以使用自然数文本——包括十六进制或二进制记法——来表示位向量。
当预期类型未知时，可以使用专用语法同时指定该位向量的宽度和值。
:::

:::example "位向量的数值文本"
以下文本都等价：
```lean
example : BitVec 8 := 0xff
example : BitVec 8 := 255
example : BitVec 8 := 0b1111_1111
```
```lean -show
-- 内联测试
example : (0xff : BitVec 8) = 255 := by rfl
example : (0b1111_1111 : BitVec 8) = 255 := by rfl
```
:::

:::syntax term (title := "固定宽度位向量文本")
```grammar
$_:num#$_
```
此记法将数值文本与表示其宽度的项配对。
`#` 两侧禁止出现空格。
超出位向量宽度的文本将被截断。
:::

:::::example "固定宽度位向量文本"

位向量可以用自然数文本表示，因此 {lean}`(5 : BitVec 8)` 是一个有效的位向量。
此外，还可以直接在文本中指定宽度：

```leanTerm
5#8
```


`#` 的任何一侧都不允许有空格：

```syntaxError spc1 (category := term)
5 #8
```
```leanOutput spc1
<example>:1:2-1:3: expected end of input
```

```syntaxError spc2 (category := term)
5# 8
```
```leanOutput spc2
<example>:1:3-1:4: expected no space before
```


`#` 的左侧必须是数值文本：

```syntaxError spc3 (category := term)
(3 + 2)#8
```
```leanOutput spc3
<example>:1:7-1:8: expected end of input
```


不过，`#` 的右侧可以是一个项：
```leanTerm
5#(4 + 4)
```

如果文本过大，无法容纳在指定的位数中，则会被截断：
```lean (name := overflow)
#eval 7#2
```
```leanOutput overflow
3#2
```
:::::

:::syntax term (title := "有界位向量文本") (namespace := BitVec)

```grammar
$_:num#'$_
```

此记法仅在打开 `BitVec` 命名空间后可用。
它不要求显式给出宽度，而是要求提供一个证明，表明文本值可由相应宽度的位向量表示。
:::

::::::leanSection
:::::example "有界位向量文本"
有界位向量文本记法可确保文本不会溢出指定的位数。
此记法仅在打开 `BitVec` 命名空间后可用。

```lean
open BitVec
```

界限内的文本需要提供相应证明：
```lean
example : BitVec 8 := 1#'(by decide)
```

不在界限内的文本是不允许的：
```lean +error (name := oob)
example : BitVec 8 := 256#'(by decide)
```
```leanOutput oob
Tactic `decide` proved that the proposition
  256 < 2 ^ 8
is false
```

:::::
::::::

# 自动化
%%%
tag := "BitVec-automation"
%%%

除了 Lean 为每种类型提供的整套自动化功能和工具外，{tactic}`bv_decide` 策略还能解决许多与位向量有关的问题。
此策略调用外部自动定理证明器（`cadical`），并在 Lean 自身的逻辑中重构它所提供的证明。
所得证明仅依赖公理 {name}`Lean.ofReduceBool`；外部证明器并非可信代码库的一部分。

:::example "置位计数"

```imports -show
import Std.Tactic.BVDecide
```

函数 {lean}`popcount` 返回位向量中置位的数量。
它可以实现为一个迭代 32 次的循环：逐一测试每个位，若该位已置位，则递增计数器：

```lean
def popcount_spec (x : BitVec 32) : BitVec 32 :=
  (32 : Nat).fold (init := 0) fun i _ pop =>
    pop + ((x >>> i) &&& 1)
```

Henry S. Warren,
Jr. 所著 _Hacker's Delight, Second Edition_ 第 82 页的图 5-2 描述了 {lean}`popcount` 的另一种实现。
它使用底层位运算，以少得多的操作计算出相同的值：
```lean
def popcount (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x &&& 0x0000003F
  x
```

可以使用 {tactic}`bv_decide` 证明这两种实现等价：
```lean
theorem popcount_correct : popcount = popcount_spec := by
  funext x
  simp [popcount, popcount_spec]
  bv_decide
```
:::

# API 参考
%%%
tag := "BitVec-api"
%%%


## 界限

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Bounds"
%%%
{docstring BitVec.intMax}

{docstring BitVec.intMin}

## 构造

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Construction"
%%%
{docstring BitVec.fill}

{docstring BitVec.zero}

{docstring BitVec.allOnes}

{docstring BitVec.twoPow}

## 转换


%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Conversion"
%%%
{docstring BitVec.toHex}

{docstring BitVec.toInt}

{docstring BitVec.toNat}

{docstring BitVec.ofBool}

{docstring BitVec.ofBoolListBE}

{docstring BitVec.ofBoolListLE}

{docstring BitVec.ofInt}

{docstring BitVec.ofNat}

{docstring BitVec.ofNatLT}

{docstring BitVec.cast}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Comparisons"
%%%
{docstring BitVec.ule}

{docstring BitVec.sle}

{docstring BitVec.ult}

{docstring BitVec.slt}

{docstring BitVec.decEq}

## 哈希

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Hashing"
%%%
{docstring BitVec.hash}

## 序列操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Sequence-Operations"
%%%
这些操作将位向量视为位的序列，而非数的编码。

{docstring BitVec.nil}

{docstring BitVec.cons}

{docstring BitVec.concat}

{docstring BitVec.shiftConcat}

{docstring BitVec.truncate}

{docstring BitVec.setWidth}

{docstring BitVec.setWidth'}

{docstring BitVec.append}

{docstring BitVec.replicate}

{docstring BitVec.reverse}

{docstring BitVec.rotateLeft}

{docstring BitVec.rotateRight}

### 位提取

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Sequence-Operations--Bit-Extraction"
%%%
{docstring BitVec.msb}

{docstring BitVec.getMsbD}

{docstring BitVec.getMsb}

{docstring BitVec.getMsb?}

{docstring BitVec.getLsbD}

{docstring BitVec.getLsb}

{docstring BitVec.getLsb?}

{docstring BitVec.extractLsb}

{docstring BitVec.extractLsb'}

## 位运算符

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Bitwise-Operators"
%%%
这些运算符修改一个或多个位向量中的各个位。

{docstring BitVec.and}

{docstring BitVec.or}

{docstring BitVec.not}

{docstring BitVec.xor}

{docstring BitVec.zeroExtend}

{docstring BitVec.signExtend}

{docstring BitVec.ushiftRight}

{docstring BitVec.sshiftRight}

{docstring BitVec.sshiftRight'}

{docstring BitVec.shiftLeft}

{docstring BitVec.shiftLeftZeroExtend}


## 算术

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic"
%%%
这些运算符将位向量视为数。
有些操作按有符号方式进行，另一些则按无符号方式进行。
由于位向量被解释为二进制补码数，因此加法、减法和乘法在有符号与无符号解释下是一致的。


{docstring BitVec.add}

{docstring BitVec.sub}

{docstring BitVec.mul}


### 无符号操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic--Unsigned-Operations"
%%%
{docstring BitVec.udiv}

{docstring BitVec.smtUDiv}

{docstring BitVec.umod}

{docstring BitVec.uaddOverflow}

{docstring BitVec.usubOverflow}

### 有符号操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic--Signed-Operations"
%%%
{docstring BitVec.abs}

{docstring BitVec.neg}

{docstring BitVec.sdiv}

{docstring BitVec.smtSDiv}

{docstring BitVec.smod}

{docstring BitVec.srem}

{docstring BitVec.saddOverflow}

{docstring BitVec.ssubOverflow}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Iteration"
%%%
{docstring BitVec.iunfoldr}

{docstring BitVec.iunfoldr_replace}

## 证明自动化

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Proof-Automation"
%%%
### 位爆破

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Proof-Automation--Bit-Blasting"
%%%
标准库包含许多有助于实现位爆破的辅助实现；位爆破是 {tactic}`bv_decide` 用来将命题编码为供外部求解器处理的布尔可满足性问题的技术。

{docstring BitVec.adc}

{docstring BitVec.adcb}

{docstring BitVec.carry}

{docstring BitVec.mulRec}

{docstring BitVec.divRec}

{docstring BitVec.divSubtractShift}

{docstring BitVec.shiftLeftRec}

{docstring BitVec.sshiftRightRec}

{docstring BitVec.ushiftRightRec}
