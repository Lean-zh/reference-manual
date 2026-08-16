/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G5

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "自然数" =>
%%%
tag := "Nat"
file := "Natural-Numbers"
%%%

{deftech (key := "natural numbers")}[自然数]是非负整数。
逻辑上，它们是数字 0、1、2、3 等，由构造子 {lean}`Nat.zero` 和 {lean}`Nat.succ` 生成。
除了计算机可用内存强加的物理限制外，Lean 对自然数的表示没有施加上限。

由于自然数是数学推理和编程的基础，因此它们在 Lean 的实现中得到特殊支持。
自然数的逻辑模型是一个{tech (key := "inductive type")}[归纳类型]，算术运算则使用该模型来规定。
在 Lean 的内核、解释器和编译代码中，封闭的自然数被表示为高效的任意精度整数。
足够小的数字是那些不需要通过指针间接寻址的值。
算术运算由利用高效表示的原语实现。

# 逻辑模型
%%%
tag := "nat-model"
%%%


{zhdocstring Nat Manual.ZhDocString.Ch19Ch20.G5.c001}

::::leanSection
```lean -show
variable (i : Nat)
```
:::example "归纳法证明"
自然数是一个{tech (key := "inductive type")}[归纳类型]，所以 {tactic}`induction` 策略可用于证明全称量化的陈述。
归纳法证明需要一个基本情况和一个归纳步骤。
基本情况是证明陈述对于 `0` 为真。
归纳步骤是证明陈述对某个任意数字 {lean}`i` 为真蕴含了它对 {lean}`i + 1` 为真。

该证明在其归纳步骤中使用了引理 `Nat.succ_lt_succ`。
```lean
example (n : Nat) : n < n + 1 := by
  induction n with
  | zero =>
    show 0 < 1
    decide
  | succ i ih => -- ih : i < i + 1
    show i + 1 < i + 1 + 1
    exact Nat.succ_lt_succ ih
```
:::
::::

## 皮亚诺公理
%%%
tag := "peano-axioms"
%%%

皮亚诺公理是此定义的推论。
为 {lean}`Nat` 生成的归纳原理是归纳公理所要求的：
```signature
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
```
这种归纳原理还实现了原语递归。
{lean}`Nat.succ` 的单射性以及 {lean}`Nat.succ` 和 `Nat.zero` 的不相交性是归纳原理的推论，使用通常称为“无混淆”的构造：
```lean
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True
  | 0, _ + 1 | _ + 1, 0 => False
  | n + 1, k + 1 => n = k

theorem noConfusionDiagonal (n : Nat) :
    NoConfusion n n :=
  Nat.rec True.intro (fun _ _ => rfl) n

theorem noConfusion (n k : Nat) (eq : n = k) :
    NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

theorem succ_injective : n + 1 = k + 1 → n = k :=
  noConfusion (n + 1) (k + 1)

theorem succ_not_zero : ¬n + 1 = 0 :=
  noConfusion (n + 1) 0
```

# 运行时表示
%%%
tag := "nat-runtime"
%%%

由 `Nat` 声明所暗示的表示效率会极其低下，因为它本质上是一个链表。
链表的长度就是数字。
使用这种表示，加法所花费的时间将与其中一个加数的大小成线性关系，而且数字在内存中占据的机器字数至少与其大小一样多。
因此，自然数在内核和编译器中都具有特殊的专门支持，以避免这种开销。

在内核中，有特殊的 `Nat` 字面量值使用了广受信赖、高效的任意精度整数库（通常是 [GMP](https://gmplib.org/)）。
像加法这样的基本函数被使用这种表示的原语所覆盖。
因为它们是内核的一部分，如果这些原语不符合它们作为 Lean 函数的定义，可能会破坏健全性。

在编译代码中，足够小的自然数可以在不使用指针间接寻址的情况下表示：对象指针中的最低位用于指示该值实际上不是指针，其余的位用于存储数字。
对于无指针的 {lean}`Nat`，32位架构上有 31 位可用，而 64 位架构上有 63 位可用。
换句话说，小于 $`2^{31} = 2,147,483,648` 或 $`2^{63} = 9,223,372,036,854,775,808` 的自然数不需要分配。
如果一个自然数对于这种表示来说太大，它会作为普通的 Lean 对象进行分配，该对象由对象头和任意精度整数值组成。

## 性能说明
%%%
tag := "nat-performance"
%%%


使用 Lean 内置的算术运算符，而不是重新定义它们，是至关重要的。
{lean}`Nat` 的逻辑模型本质上是链表，所以加法的时间与其中一个参数的大小成线性关系。
更糟糕的是，在这种模型中乘法需要二次方时间。
虽然从头开始定义算术可能是一个有用的学习练习，但这些重新定义的运算速度远不及内置的那么快。

# 语法
%%%
tag := "nat-syntax"
%%%


自然数字面量通过 {lean}`OfNat` 类型类实现重载，这在{ref "nat-literals"}[关于字面量语法的章节]中有所描述。


# API 参考
%%%
tag := "nat-api"
%%%


## 算术
%%%
tag := "nat-api-arithmetic"
%%%

{zhdocstring Nat.pred Manual.ZhDocString.Ch19Ch20.G5.c002}

{zhdocstring Nat.add Manual.ZhDocString.Ch19Ch20.G5.c003}

{zhdocstring Nat.sub Manual.ZhDocString.Ch19Ch20.G5.c004}

{zhdocstring Nat.mul Manual.ZhDocString.Ch19Ch20.G5.c005}

{zhdocstring Nat.div Manual.ZhDocString.Ch19Ch20.G5.c006}

{zhdocstring Nat.mod Manual.ZhDocString.Ch19Ch20.G5.c007}

{zhdocstring Nat.modCore Manual.ZhDocString.Ch19Ch20.G5.c008}

{zhdocstring Nat.pow Manual.ZhDocString.Ch19Ch20.G5.c009}

{zhdocstring Nat.log2 Manual.ZhDocString.Ch19Ch20.G5.c010}

### 按位运算
%%%
tag := "nat-api-bitwise"
%%%

{zhdocstring Nat.shiftLeft Manual.ZhDocString.Ch19Ch20.G5.c011}

{zhdocstring Nat.shiftRight Manual.ZhDocString.Ch19Ch20.G5.c012}

{zhdocstring Nat.xor Manual.ZhDocString.Ch19Ch20.G5.c013}

{zhdocstring Nat.lor Manual.ZhDocString.Ch19Ch20.G5.c014}

{zhdocstring Nat.land Manual.ZhDocString.Ch19Ch20.G5.c015}

{zhdocstring Nat.bitwise Manual.ZhDocString.Ch19Ch20.G5.c016}

{zhdocstring Nat.testBit Manual.ZhDocString.Ch19Ch20.G5.c017}

## 最小值和最大值
%%%
tag := "nat-api-minmax"
%%%


{zhdocstring Nat.min Manual.ZhDocString.Ch19Ch20.G5.c018}

{zhdocstring Nat.max Manual.ZhDocString.Ch19Ch20.G5.c019}

## 最大公约数和最小公倍数
%%%
tag := "nat-api-gcd-lcm"
%%%


{zhdocstring Nat.gcd Manual.ZhDocString.Ch19Ch20.G5.c020}

{zhdocstring Nat.lcm Manual.ZhDocString.Ch19Ch20.G5.c021}

## 2 的幂
%%%
tag := "nat-api-pow2"
%%%


{zhdocstring Nat.isPowerOfTwo Manual.ZhDocString.Ch19Ch20.G5.c022}

{zhdocstring Nat.nextPowerOfTwo Manual.ZhDocString.Ch19Ch20.G5.c023}

## 比较
%%%
tag := "nat-api-comparison"
%%%


### 布尔比较
%%%
tag := "nat-api-comparison-bool"
%%%


{zhdocstring Nat.beq Manual.ZhDocString.Ch19Ch20.G5.c024}

{zhdocstring Nat.ble Manual.ZhDocString.Ch19Ch20.G5.c025}

{zhdocstring Nat.blt Manual.ZhDocString.Ch19Ch20.G5.c026}

### 可判定相等
%%%
tag := "nat-api-deceq"
%%%

{zhdocstring Nat.decEq Manual.ZhDocString.Ch19Ch20.G5.c027}

{zhdocstring Nat.decLe Manual.ZhDocString.Ch19Ch20.G5.c028}

{zhdocstring Nat.decLt Manual.ZhDocString.Ch19Ch20.G5.c029}

### 谓词
%%%
tag := "nat-api-predicates"
%%%

{zhdocstring Nat.le Manual.ZhDocString.Ch19Ch20.G5.c030}

{zhdocstring Nat.lt Manual.ZhDocString.Ch19Ch20.G5.c031}

## 迭代
%%%
tag := "nat-api-iteration"
%%%

许多迭代运算符有两个版本：结构递归版本和尾递归版本。
结构递归版本通常在定义等价重要的上下文中更容易使用，因为当只知道自然数的某些前缀时它就可以进行计算。

{zhdocstring Nat.repeat Manual.ZhDocString.Ch19Ch20.G5.c032}

{zhdocstring Nat.repeatTR Manual.ZhDocString.Ch19Ch20.G5.c033}

{zhdocstring Nat.fold Manual.ZhDocString.Ch19Ch20.G5.c034}

{zhdocstring Nat.foldTR Manual.ZhDocString.Ch19Ch20.G5.c035}

{zhdocstring Nat.foldM Manual.ZhDocString.Ch19Ch20.G5.c036}

{zhdocstring Nat.foldRev Manual.ZhDocString.Ch19Ch20.G5.c037}

{zhdocstring Nat.foldRevM Manual.ZhDocString.Ch19Ch20.G5.c038}

{zhdocstring Nat.forM Manual.ZhDocString.Ch19Ch20.G5.c039}

{zhdocstring Nat.forRevM Manual.ZhDocString.Ch19Ch20.G5.c040}

{zhdocstring Nat.all Manual.ZhDocString.Ch19Ch20.G5.c041}

{zhdocstring Nat.allTR Manual.ZhDocString.Ch19Ch20.G5.c042}

{zhdocstring Nat.any Manual.ZhDocString.Ch19Ch20.G5.c043}

{zhdocstring Nat.anyTR Manual.ZhDocString.Ch19Ch20.G5.c044}

{zhdocstring Nat.allM Manual.ZhDocString.Ch19Ch20.G5.c045}

{zhdocstring Nat.anyM Manual.ZhDocString.Ch19Ch20.G5.c046}

## 转换
%%%
tag := "nat-api-conversion"
%%%

{zhdocstring Nat.toUInt8 Manual.ZhDocString.Ch19Ch20.G5.c047}

{zhdocstring Nat.toUInt16 Manual.ZhDocString.Ch19Ch20.G5.c048}

{zhdocstring Nat.toUInt32 Manual.ZhDocString.Ch19Ch20.G5.c049}

{zhdocstring Nat.toUInt64 Manual.ZhDocString.Ch19Ch20.G5.c050}

{zhdocstring Nat.toUSize Manual.ZhDocString.Ch19Ch20.G5.c051}

{zhdocstring Nat.toInt8 Manual.ZhDocString.Ch19Ch20.G5.c052}

{zhdocstring Nat.toInt16 Manual.ZhDocString.Ch19Ch20.G5.c053}

{zhdocstring Nat.toInt32 Manual.ZhDocString.Ch19Ch20.G5.c054}

{zhdocstring Nat.toInt64 Manual.ZhDocString.Ch19Ch20.G5.c055}

{zhdocstring Nat.toISize Manual.ZhDocString.Ch19Ch20.G5.c056}

{zhdocstring Nat.toFloat Manual.ZhDocString.Ch19Ch20.G5.c057}

{zhdocstring Nat.toFloat32 Manual.ZhDocString.Ch19Ch20.G5.c058}

{zhdocstring Nat.isValidChar Manual.ZhDocString.Ch19Ch20.G5.c059}

{zhdocstring Nat.repr Manual.ZhDocString.Ch19Ch20.G5.c060}

{zhdocstring Nat.toDigits Manual.ZhDocString.Ch19Ch20.G5.c061}

{zhdocstring Nat.digitChar Manual.ZhDocString.Ch19Ch20.G5.c062}

{zhdocstring Nat.toSubscriptString Manual.ZhDocString.Ch19Ch20.G5.c063}

{zhdocstring Nat.toSuperscriptString Manual.ZhDocString.Ch19Ch20.G5.c064}

{zhdocstring Nat.toSuperDigits Manual.ZhDocString.Ch19Ch20.G5.c065}

{zhdocstring Nat.toSubDigits Manual.ZhDocString.Ch19Ch20.G5.c066}

{zhdocstring Nat.subDigitChar Manual.ZhDocString.Ch19Ch20.G5.c067}

{zhdocstring Nat.superDigitChar Manual.ZhDocString.Ch19Ch20.G5.c068}

## 消除
%%%
tag := "nat-api-elim"
%%%


为 {lean}`Nat` 自动生成的递归原理会导致以 {lean}`Nat.zero` 和 {lean}`Nat.succ` 的形式来表达证明目标。
这并不是特别友好，因此提供了一个逻辑上等价的替代递归原理，其结果是目标以 {lean}`0` 和 `n + 1` 的形式表达。
{tech (key := "Custom eliminators")}[自定义消除器]可提供给 {tactic}`induction` 和 {tactic}`cases` 策略，方法是使用 {attr}`induction_eliminator` 和 {attr}`cases_eliminator` 属性。

{zhdocstring Nat.recAux Manual.ZhDocString.Ch19Ch20.G5.c069}

{zhdocstring Nat.casesAuxOn Manual.ZhDocString.Ch19Ch20.G5.c070}

### 替代归纳原理
%%%
tag := "nat-api-induction"
%%%

{zhdocstring Nat.strongRecOn Manual.ZhDocString.Ch19Ch20.G5.c071}

{zhdocstring Nat.caseStrongRecOn Manual.ZhDocString.Ch19Ch20.G5.c072}

{zhdocstring Nat.div.inductionOn Manual.ZhDocString.Ch19Ch20.G5.c073}

{zhdocstring Nat.div2Induction Manual.ZhDocString.Ch19Ch20.G5.c074}

{zhdocstring Nat.mod.inductionOn Manual.ZhDocString.Ch19Ch20.G5.c075}
