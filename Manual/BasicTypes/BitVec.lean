/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G8

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

{zhdocstring BitVec Manual.ZhDocString.Ch19Ch20.G8.c087}

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
{zhdocstring BitVec.intMax Manual.ZhDocString.Ch19Ch20.G8.c088}

{zhdocstring BitVec.intMin Manual.ZhDocString.Ch19Ch20.G8.c089}

## 构造

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Construction"
%%%
{zhdocstring BitVec.fill Manual.ZhDocString.Ch19Ch20.G8.c090}

{zhdocstring BitVec.zero Manual.ZhDocString.Ch19Ch20.G8.c091}

{zhdocstring BitVec.allOnes Manual.ZhDocString.Ch19Ch20.G8.c092}

{zhdocstring BitVec.twoPow Manual.ZhDocString.Ch19Ch20.G8.c093}

## 转换


%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Conversion"
%%%
{zhdocstring BitVec.toHex Manual.ZhDocString.Ch19Ch20.G8.c094}

{zhdocstring BitVec.toInt Manual.ZhDocString.Ch19Ch20.G8.c095}

{zhdocstring BitVec.toNat Manual.ZhDocString.Ch19Ch20.G8.c096}

{zhdocstring BitVec.ofBool Manual.ZhDocString.Ch19Ch20.G8.c097}

{zhdocstring BitVec.ofBoolListBE Manual.ZhDocString.Ch19Ch20.G8.c098}

{zhdocstring BitVec.ofBoolListLE Manual.ZhDocString.Ch19Ch20.G8.c099}

{zhdocstring BitVec.ofInt Manual.ZhDocString.Ch19Ch20.G8.c100}

{zhdocstring BitVec.ofNat Manual.ZhDocString.Ch19Ch20.G8.c101}

{zhdocstring BitVec.ofNatLT Manual.ZhDocString.Ch19Ch20.G8.c102}

{zhdocstring BitVec.cast Manual.ZhDocString.Ch19Ch20.G8.c103}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Comparisons"
%%%
{zhdocstring BitVec.ule Manual.ZhDocString.Ch19Ch20.G8.c104}

{zhdocstring BitVec.sle Manual.ZhDocString.Ch19Ch20.G8.c105}

{zhdocstring BitVec.ult Manual.ZhDocString.Ch19Ch20.G8.c106}

{zhdocstring BitVec.slt Manual.ZhDocString.Ch19Ch20.G8.c107}

{zhdocstring BitVec.decEq Manual.ZhDocString.Ch19Ch20.G8.c108}

## 哈希

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Hashing"
%%%
{zhdocstring BitVec.hash Manual.ZhDocString.Ch19Ch20.G8.c109}

## 序列操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Sequence-Operations"
%%%
这些操作将位向量视为位的序列，而非数的编码。

{zhdocstring BitVec.nil Manual.ZhDocString.Ch19Ch20.G8.c110}

{zhdocstring BitVec.cons Manual.ZhDocString.Ch19Ch20.G8.c111}

{zhdocstring BitVec.concat Manual.ZhDocString.Ch19Ch20.G8.c112}

{zhdocstring BitVec.shiftConcat Manual.ZhDocString.Ch19Ch20.G8.c113}

{zhdocstring BitVec.truncate Manual.ZhDocString.Ch19Ch20.G8.c114}

{zhdocstring BitVec.setWidth Manual.ZhDocString.Ch19Ch20.G8.c115}

{zhdocstring BitVec.setWidth' Manual.ZhDocString.Ch19Ch20.G8.c116}

{zhdocstring BitVec.append Manual.ZhDocString.Ch19Ch20.G8.c117}

{zhdocstring BitVec.replicate Manual.ZhDocString.Ch19Ch20.G8.c118}

{zhdocstring BitVec.reverse Manual.ZhDocString.Ch19Ch20.G8.c119}

{zhdocstring BitVec.rotateLeft Manual.ZhDocString.Ch19Ch20.G8.c120}

{zhdocstring BitVec.rotateRight Manual.ZhDocString.Ch19Ch20.G8.c121}

### 位提取

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Sequence-Operations--Bit-Extraction"
%%%
{zhdocstring BitVec.msb Manual.ZhDocString.Ch19Ch20.G8.c122}

{zhdocstring BitVec.getMsbD Manual.ZhDocString.Ch19Ch20.G8.c123}

{zhdocstring BitVec.getMsb Manual.ZhDocString.Ch19Ch20.G8.c124}

{zhdocstring BitVec.getMsb? Manual.ZhDocString.Ch19Ch20.G8.c125}

{zhdocstring BitVec.getLsbD Manual.ZhDocString.Ch19Ch20.G8.c126}

{zhdocstring BitVec.getLsb Manual.ZhDocString.Ch19Ch20.G8.c127}

{zhdocstring BitVec.getLsb? Manual.ZhDocString.Ch19Ch20.G8.c128}

{zhdocstring BitVec.extractLsb Manual.ZhDocString.Ch19Ch20.G8.c129}

{zhdocstring BitVec.extractLsb' Manual.ZhDocString.Ch19Ch20.G8.c130}

## 位运算符

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Bitwise-Operators"
%%%
这些运算符修改一个或多个位向量中的各个位。

{zhdocstring BitVec.and Manual.ZhDocString.Ch19Ch20.G8.c131}

{zhdocstring BitVec.or Manual.ZhDocString.Ch19Ch20.G8.c132}

{zhdocstring BitVec.not Manual.ZhDocString.Ch19Ch20.G8.c133}

{zhdocstring BitVec.xor Manual.ZhDocString.Ch19Ch20.G8.c134}

{zhdocstring BitVec.zeroExtend Manual.ZhDocString.Ch19Ch20.G8.c135}

{zhdocstring BitVec.signExtend Manual.ZhDocString.Ch19Ch20.G8.c136}

{zhdocstring BitVec.ushiftRight Manual.ZhDocString.Ch19Ch20.G8.c137}

{zhdocstring BitVec.sshiftRight Manual.ZhDocString.Ch19Ch20.G8.c138}

{zhdocstring BitVec.sshiftRight' Manual.ZhDocString.Ch19Ch20.G8.c139}

{zhdocstring BitVec.shiftLeft Manual.ZhDocString.Ch19Ch20.G8.c140}

{zhdocstring BitVec.shiftLeftZeroExtend Manual.ZhDocString.Ch19Ch20.G8.c141}


## 算术

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic"
%%%
这些运算符将位向量视为数。
有些操作按有符号方式进行，另一些则按无符号方式进行。
由于位向量被解释为二进制补码数，因此加法、减法和乘法在有符号与无符号解释下是一致的。


{zhdocstring BitVec.add Manual.ZhDocString.Ch19Ch20.G8.c142}

{zhdocstring BitVec.sub Manual.ZhDocString.Ch19Ch20.G8.c143}

{zhdocstring BitVec.mul Manual.ZhDocString.Ch19Ch20.G8.c144}


### 无符号操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic--Unsigned-Operations"
%%%
{zhdocstring BitVec.udiv Manual.ZhDocString.Ch19Ch20.G8.c145}

{zhdocstring BitVec.smtUDiv Manual.ZhDocString.Ch19Ch20.G8.c146}

{zhdocstring BitVec.umod Manual.ZhDocString.Ch19Ch20.G8.c147}

{zhdocstring BitVec.uaddOverflow Manual.ZhDocString.Ch19Ch20.G8.c148}

{zhdocstring BitVec.usubOverflow Manual.ZhDocString.Ch19Ch20.G8.c149}

### 有符号操作

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Arithmetic--Signed-Operations"
%%%
{zhdocstring BitVec.abs Manual.ZhDocString.Ch19Ch20.G8.c150}

{zhdocstring BitVec.neg Manual.ZhDocString.Ch19Ch20.G8.c151}

{zhdocstring BitVec.sdiv Manual.ZhDocString.Ch19Ch20.G8.c152}

{zhdocstring BitVec.smtSDiv Manual.ZhDocString.Ch19Ch20.G8.c153}

{zhdocstring BitVec.smod Manual.ZhDocString.Ch19Ch20.G8.c154}

{zhdocstring BitVec.srem Manual.ZhDocString.Ch19Ch20.G8.c155}

{zhdocstring BitVec.saddOverflow Manual.ZhDocString.Ch19Ch20.G8.c156}

{zhdocstring BitVec.ssubOverflow Manual.ZhDocString.Ch19Ch20.G8.c157}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Iteration"
%%%
{zhdocstring BitVec.iunfoldr Manual.ZhDocString.Ch19Ch20.G8.c158}

{zhdocstring BitVec.iunfoldr_replace Manual.ZhDocString.Ch19Ch20.G8.c159}

## 证明自动化

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Proof-Automation"
%%%
### 位爆破

%%%
tag := "Lean-__________________--Basic-Types--Bitvectors--API-Reference--Proof-Automation--Bit-Blasting"
%%%
标准库包含许多有助于实现位爆破的辅助实现；位爆破是 {tactic}`bv_decide` 用来将命题编码为供外部求解器处理的布尔可满足性问题的技术。

{zhdocstring BitVec.adc Manual.ZhDocString.Ch19Ch20.G8.c160}

{zhdocstring BitVec.adcb Manual.ZhDocString.Ch19Ch20.G8.c161}

{zhdocstring BitVec.carry Manual.ZhDocString.Ch19Ch20.G8.c162}

{zhdocstring BitVec.mulRec Manual.ZhDocString.Ch19Ch20.G8.c163}

{zhdocstring BitVec.divRec Manual.ZhDocString.Ch19Ch20.G8.c164}

{zhdocstring BitVec.divSubtractShift Manual.ZhDocString.Ch19Ch20.G8.c165}

{zhdocstring BitVec.shiftLeftRec Manual.ZhDocString.Ch19Ch20.G8.c166}

{zhdocstring BitVec.sshiftRightRec Manual.ZhDocString.Ch19Ch20.G8.c167}

{zhdocstring BitVec.ushiftRightRec Manual.ZhDocString.Ch19Ch20.G8.c168}
