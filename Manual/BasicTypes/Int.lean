/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "整数" =>
%%%
tag := "Int"
%%%

整数是包含正负的完整数字。
整数是任意精度的，仅受运行 Lean 的硬件能力的限制；对于编程和计算机科学中使用的固定宽度整数，请参阅{ref "fixed-ints"}[定精度整数章节]。

Lean 的实现对整数提供了特殊支持。
整数的逻辑模型基于自然数：每个整数被建模为自然数或自然数的负后继。
整数上的操作是使用该模型指定的，该模型用于内核和解释代码中。
在这些语境中，整数代码继承了自然数特殊支持带来的性能优势。
在编译后的代码中，整数被表示为高效的任意精度整数，并且足够小的数字被存储为不需要通过指针间接引用的值。
算术操作由利用这些高效表示的原语实现。

# 逻辑模型
%%%
tag := "int-model"
%%%
整数既可以表示为一个自然数，也可以表示为一个自然数后继的否定。

{docstring Int}

整数的这种表示方式具有许多有用的属性。
它使用和理解起来相对简单。
与符号和 {lean}`Nat` 构成的有序对不同，$`0` 有一个唯一的表示形式，这简化了关于等式的推理。
整数也可以表示为一对自然数，其中一个减去另一个，但这需要一个行为良好的{ref "quotients"}[商类型]，并且由于需要证明函数尊重等价关系，使用商类型可能会非常繁琐。

# 运行时表示
%%%
tag := "int-runtime"
%%%

像{ref "nat-runtime"}[自然数]一样，足够小的整数无需指针即可表示：对象指针中的最低位用于指示该值实际上不是指针。
如果一个整数太大，无法放入剩余的位中，它将作为一个普通的 Lean 对象分配，该对象由对象头和任意精度整数组成。

# 语法
%%%
tag := "int-syntax"
%%%

```lean -show
section
variable (n : Nat)
```

{lean}`OfNat Int` 实例允许数字在表达式和模式语境中用作字面量。
{lean}`(OfNat.ofNat n : Int)` 规约为构造子应用 {lean}`Int.ofNat n`。
{inst}`Neg Int` 实例也允许使用否定。

```lean -show
open Int
```

在这些实例之上，构造子 {lean}`Int.negSucc` 还有一套特殊语法，可在打开 `Int` 命名空间时使用。
记号 {lean}`-[ n +1]` 让人联想到 $`-(n + 1)`，这也是 {lean}`Int.negSucc n` 的含义。

:::syntax term (title := "负后继")

{lean}`-[ n +1]` 是 {lean}`Int.negSucc n` 的记号。

```grammar
-[ $_ +1]
```
:::

```lean -show
end
```


# API 参考

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference"
%%%
## 属性

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference--Properties"
%%%
{docstring Int.sign}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference--Conversions"
%%%
{docstring Int.natAbs}

{docstring Int.toNat}

{docstring Int.toNat?}

{docstring Int.toISize}

{docstring Int.toInt8}

{docstring Int.toInt16}

{docstring Int.toInt32}

{docstring Int.toInt64}

{docstring Int.repr}

## 算术

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference--Arithmetic"
%%%
通常，使用 Lean 的重载算术记号来访问整数上的算术操作。
特别是，{inst}`Add Int`、{inst}`Neg Int`、{inst}`Sub Int` 和 {inst}`Mul Int` 实例允许使用普通的插缀运算符。
{ref "int-div"}[除法]稍微复杂一些，因为整数上有多种合理的除法概念。

{docstring Int.add}

{docstring Int.sub}

{docstring Int.subNatNat}

{docstring Int.neg}

{docstring Int.negOfNat}

{docstring Int.mul}

{docstring Int.pow}

{docstring Int.gcd}

{docstring Int.lcm}

### 除法
%%%
tag := "int-div"
%%%
{inst}`Div Int` 和 {inst}`Mod Int` 实例实现了欧几里得除法，在 {name}`Int.ediv` 的参考中有描述。
然而，这并不是唯一合理的除法舍入和余数约定。
有四对除法和取模函数可用，它们实现了各种约定。

:::example "除以 0"
在所有整数除法约定中，除以 {lean  (type := "Int")}`0` 都被定义为 {lean  (type := "Int")}`0`：

```lean (name := div0)
#eval Int.ediv 5 0
#eval Int.ediv 0 0
#eval Int.ediv (-5) 0
#eval Int.bdiv 5 0
#eval Int.bdiv 0 0
#eval Int.bdiv (-5) 0
#eval Int.fdiv 5 0
#eval Int.fdiv 0 0
#eval Int.fdiv (-5) 0
#eval Int.tdiv 5 0
#eval Int.tdiv 0 0
#eval Int.tdiv (-5) 0
```
都求值为 0。
```leanOutput div0
0
```
:::

{docstring Int.ediv}

{docstring Int.emod}

{docstring Int.tdiv}

{docstring Int.tmod}

{docstring Int.bdiv}

{docstring Int.bmod}

{docstring Int.fdiv}

{docstring Int.fmod}

## 按位运算符

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference--Bitwise-Operators"
%%%
{name}`Int` 上的按位运算符可以理解为对整数的二进制补码表示的无限位流进行按位操作。

{docstring Int.not}

{docstring Int.shiftRight}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Integers--API-Reference--Comparisons"
%%%
{lean}`Int` 上的相等和不等测试通常使用其相等和排序关系的可判定性，或者使用 {inst}`BEq Int` 和 {inst}`Ord Int` 实例来执行。

```lean -show
example (i j : Int) : Decidable (i ≤ j) := inferInstance
example (i j : Int) : Decidable (i < j) := inferInstance
example (i j : Int) : Decidable (i = j) := inferInstance
```

{docstring Int.le}

{docstring Int.lt}

{docstring Int.decEq}
