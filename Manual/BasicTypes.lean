/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.ZhDocString.Ch19Ch20.G7

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.Int
import Manual.BasicTypes.String
import Manual.BasicTypes.Array
import Manual.BasicTypes.ByteArray
import Manual.BasicTypes.Fin
import Manual.BasicTypes.UInt
import Manual.BasicTypes.BitVec
import Manual.BasicTypes.Float
import Manual.BasicTypes.Char
import Manual.BasicTypes.Option
import Manual.BasicTypes.Empty
import Manual.BasicTypes.Products
import Manual.BasicTypes.Sum
import Manual.BasicTypes.List
import Manual.BasicTypes.Maps
import Manual.BasicTypes.Subtype
import Manual.BasicTypes.Thunk
import Manual.BasicTypes.Range

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "基本类型" =>
%%%
tag := "basic-types"
file := "Basic-Types"
%%%


Lean 包含一些由编译器提供特殊支持的内置类型。
其中有些类型（例如 {lean}`Nat`）在内核中还有特殊支持。
其他类型本身虽然没有特殊的编译器支持，但出于性能原因，它们在很大程度上依赖于类型的内部表示。

{include 0 Manual.BasicTypes.Nat}

{include 0 Manual.BasicTypes.Int}

{include 0 Manual.BasicTypes.Fin}

{include 0 Manual.BasicTypes.UInt}

{include 0 Manual.BasicTypes.BitVec}

{include 0 Manual.BasicTypes.Float}

{include 0 Manual.BasicTypes.Char}


{include 0 Manual.BasicTypes.String}

# 单元类型

%%%
tag := "Lean-__________________--Basic-Types--The-Unit-Type"
file := "The-Unit-Type"
%%%
单元类型是恰好具有一个元素的规范类型，该元素名为 {name Unit.unit}`unit`，并由空元组 {lean}`()` 表示。
它只描述单个值，该值由上述不带参数的构造子构成。

{lean}`Unit` 类似于 C 语言及其派生语言中的 `void`：尽管 `void` 没有任何可以被命名的元素，但它表示从函数返回的控制流，而不包含额外信息。
在函数式编程中，{lean}`Unit` 是那些“什么都不返回”的事物的返回类型。
在数学上，这由一个完全不包含任何信息的单一值来表示，这与 {lean}`Empty` 这样的空类型相反，后者表示不可达的代码。

:::leanSection
```lean -show
variable {m : Type → Type} [Monad m] {α : Type}
```

当使用 {ref "monads-and-do"}[单子]编程时，{lean}`Unit` 特别有用。
对于任何类型 {lean}`α`，{lean}`m α` 表示一个具有副作用并返回类型 {lean}`α` 的值的操作。
类型 {lean}`m Unit` 表示一个具有某些副作用但不返回值的操作。

:::



单元类型有两种变体：

 * {lean}`Unit` 是一个 {lean}`Type`，存在于最小的非命题 {tech (key := "universe")}[宇宙]中。

 * {lean}`PUnit` 是 {tech (key := "universe polymorphism")}[宇宙多态]的，可以在任何非命题 {tech (key := "universe")}[宇宙]中使用。

在幕后，{lean}`Unit` 实际上被定义为 {lean}`PUnit.{1}`。
可能的情况下，应优先使用 {lean}`Unit` 而不是 {name}`PUnit`，以避免不必要的宇宙参数。
如有疑问，请使用 {lean}`Unit` 直到出现宇宙层级的错误。

{zhdocstring Unit Manual.ZhDocString.Ch19Ch20.G7.c229}

{zhdocstring Unit.unit Manual.ZhDocString.Ch19Ch20.G7.c230}

{zhdocstring PUnit Manual.ZhDocString.Ch19Ch20.G7.c231}

## 定义等价

%%%
tag := "Lean-__________________--Basic-Types--The-Unit-Type--Definitional-Equality"
%%%
{deftech (key := "Unit-like types")}_类单元类型_ 是一种只有一个构造子的归纳类型，且该构造子不接受非证明参数。
{lean}`PUnit` 就是这样一种类型。
类单元类型的所有元素都与所有其他元素 {tech (key := "definitional equality")}[定义等价]。

:::example "{lean}`Unit` 的定义等价"
具有 {lean}`Unit` 类型的每个项都与具有 {lean}`Unit` 类型的每个其他项定义等价：

```lean
example (e1 e2 : Unit) : e1 = e2 := rfl
```
:::

::::keepEnv
:::example "类单元类型的定义等价"

{lean}`CustomUnit` 和 {lean}`AlsoUnit` 都是类单元类型，具有不带参数的单一构造子。
这两种类型中的任意一对项都是定义等价的。

```lean
inductive CustomUnit where
  | customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl

structure AlsoUnit where

example (e1 e2 : AlsoUnit) : e1 = e2 := rfl
```

带有参数的类型（例如 {lean}`WithParam`）如果是具有不接受参数的单一构造子，那么它们也是类单元类型。

```lean
inductive WithParam (n : Nat) where
  | mk

example (x y : WithParam 3) : x = y := rfl
```

具有非证明参数的构造子不是类单元类型，即使参数全部是类单元类型也是如此。
```lean
inductive NotUnitLike where
  | mk (u : Unit)
```

```lean +error (name := NotUnitLike)
example (e1 e2 : NotUnitLike) : e1 = e2 := rfl
```
```leanOutput NotUnitLike
Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  e1 = e2
```

类单元类型的构造子可以接受证明作为参数。
```lean
inductive ProofUnitLike where
  | mk : 2 = 2 → ProofUnitLike

example (e1 e2 : ProofUnitLike) : e1 = e2 := rfl
```
:::
::::

{include 0 Manual.BasicTypes.Empty}


# 布尔值

%%%
tag := "Lean-__________________--Basic-Types--Booleans"
file := "Booleans"
%%%
{zhdocstring Bool Manual.ZhDocString.Ch19Ch20.G7.c232}

构造子 {lean}`Bool.true` 和 {lean}`Bool.false` 是从 {lean}`Bool` 命名空间导出的，因此它们可以被写成 {lean}`true` 和 {lean}`false`。

## 运行时表示

%%%
tag := "Lean-__________________--Basic-Types--Booleans--Run-Time-Representation"
%%%
因为 {lean}`Bool` 是一个 {tech (key := "enum inductive")}[枚举归纳]类型，所以它在编译后的代码中由单字节表示。

## 布尔值和命题

%%%
tag := "Lean-__________________--Basic-Types--Booleans--Booleans-and-Propositions"
%%%
{lean}`Bool` 和 {lean}`Prop` 都表示真理的概念。
从纯逻辑的角度来看，它们是等价的：{tech (key := "propositional extensionality")}[命题外延性]意味着从根本上只有两个命题，即 {lean}`True` 和 {lean}`False`。
然而，这里有一个重要的实用差异：{lean}`Bool` 划分程序可以计算的_值_，而 {lean}`Prop` 划分生成代码没有意义的陈述。
换句话说，{lean}`Bool` 是适用于程序的真与假的概念，而 {lean}`Prop` 是适用于数学的概念。
由于证明会从编译后的程序中被擦除，因此区分 {lean}`Bool` 和 {lean}`Prop` 可以明确 Lean 文件中的哪些部分旨在用于计算。

```lean -show
section BoolProp

axiom b : Bool

/-- info: b = true : Prop -/
#check_msgs in
#check (b : Prop)

example : (true = true) = True := by simp

#check decide
```

{lean}`Bool` 可以用在任何预期 {lean}`Prop` 的地方。
从每个 {lean}`Bool` 类型的 {lean}`b` 到命题 {lean}`b = true` 都存在一个 {tech (key := "coercion")}[强制转换]。
根据 {lean}`propext`，{lean}`true = true` 等于 {lean}`True`，而 {lean}`false = true` 等于 {lean}`False`。

并非每个命题都可以被程序用来在运行时做出决定。
否则，程序就可以对角谷猜想是真还是假进行分支！
然而，许多命题可以通过算法来检查。
这些命题被称为 {tech (key := "decidable")}_可判定_ 命题，并具有 {lean}`Decidable` 类型类的实例。
函数 {name}`Decidable.decide` 将带有证明的 {lean}`Decidable` 结果转换为 {lean}`Bool`。
此函数也是从可判定命题到 {lean}`Bool` 的强制转换，因此 {lean}`(2 = 2 : Bool)` 的计算结果为 {lean}`true`。

```lean -show
/-- info: true -/
#check_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```

## 语法

%%%
tag := "Lean-__________________--Basic-Types--Booleans--Syntax"
%%%
:::syntax term (title := "布尔中缀运算符")
中缀运算符 `&&`、`||` 和 `^^` 分别是 {lean}`Bool.and`、{lean}`Bool.or` 和 {lean}`Bool.xor` 的记号。

```grammar
$_:term && $_:term
```
```grammar
$_:term || $_:term
```
```grammar
$_:term ^^ $_:term
```
:::

:::syntax term (title := "布尔非")
前缀运算符 `!` 是 {lean}`Bool.not` 的记号。
```grammar
!$_:term
```
:::


## API 参考

%%%
tag := "Lean-__________________--Basic-Types--Booleans--API-Reference"
%%%
### 逻辑运算

%%%
tag := "Lean-__________________--Basic-Types--Booleans--API-Reference--Logical-Operations"
%%%
```lean -show
section ShortCircuit

axiom BIG_EXPENSIVE_COMPUTATION : Bool
```

函数 {name}`cond`、{name Bool.and}`and` 和 {name Bool.or}`or` 是短路的。
换句话说，{lean}`false && BIG_EXPENSIVE_COMPUTATION` 不需要执行 {lean}`BIG_EXPENSIVE_COMPUTATION` 就可返回 `false`。
这些函数使用 {attr}`macro_inline` 属性定义，这会使得编译器在生成代码时将其调用替换为它们的定义，并且这些定义使用嵌套模式匹配来实现短路行为。

```lean -show
end ShortCircuit
```


{zhdocstring cond Manual.ZhDocString.Ch19Ch20.G7.c233}

{zhdocstring Bool.dcond Manual.ZhDocString.Ch19Ch20.G7.c234}

{zhdocstring Bool.not Manual.ZhDocString.Ch19Ch20.G7.c235}

{zhdocstring Bool.and Manual.ZhDocString.Ch19Ch20.G7.c236}

{zhdocstring Bool.or Manual.ZhDocString.Ch19Ch20.G7.c237}

{zhdocstring Bool.xor Manual.ZhDocString.Ch19Ch20.G7.c238}

### 比较

%%%
tag := "Lean-__________________--Basic-Types--Booleans--API-Reference--Comparisons"
%%%
大多数关于布尔值的比较应该使用 {inst}`DecidableEq Bool`、{inst}`LT Bool` 和 {inst}`LE Bool` 实例来执行。

{zhdocstring Bool.decEq Manual.ZhDocString.Ch19Ch20.G7.c239}

### 转换

%%%
tag := "Lean-__________________--Basic-Types--Booleans--API-Reference--Conversions"
%%%
{zhdocstring Bool.toISize Manual.ZhDocString.Ch19Ch20.G7.c240}

{zhdocstring Bool.toUInt8 Manual.ZhDocString.Ch19Ch20.G7.c241}

{zhdocstring Bool.toUInt16 Manual.ZhDocString.Ch19Ch20.G7.c242}

{zhdocstring Bool.toUInt32 Manual.ZhDocString.Ch19Ch20.G7.c243}

{zhdocstring Bool.toUInt64 Manual.ZhDocString.Ch19Ch20.G7.c244}

{zhdocstring Bool.toUSize Manual.ZhDocString.Ch19Ch20.G7.c245}

{zhdocstring Bool.toInt8 Manual.ZhDocString.Ch19Ch20.G7.c246}

{zhdocstring Bool.toInt16 Manual.ZhDocString.Ch19Ch20.G7.c247}

{zhdocstring Bool.toInt32 Manual.ZhDocString.Ch19Ch20.G7.c248}

{zhdocstring Bool.toInt64 Manual.ZhDocString.Ch19Ch20.G7.c249}

{zhdocstring Bool.toNat Manual.ZhDocString.Ch19Ch20.G7.c250}

{zhdocstring Bool.toInt Manual.ZhDocString.Ch19Ch20.G7.c251}


{include 0 Manual.BasicTypes.Option}

{include 0 Manual.BasicTypes.Products}

{include 0 Manual.BasicTypes.Sum}

{include 0 Manual.BasicTypes.List}

{include 0 Manual.BasicTypes.Array}

{include 0 Manual.BasicTypes.ByteArray}

{include 0 Manual.BasicTypes.Range}

{include 0 Manual.BasicTypes.Maps}

{include 0 Manual.BasicTypes.Subtype}

{include 0 Manual.BasicTypes.Thunk}
