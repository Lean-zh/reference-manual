/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option maxHeartbeats 250000

#doc (Manual) "基础类" =>
%%%
tag := "basic-classes"
file := "Basic-Classes"
%%%

Lean 中的许多类型类用于让加法、数组索引等内置记法可以重载。

# 布尔相等性测试
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Boolean-Equality-Tests"
%%%

布尔相等运算符 `==` 通过定义 {name}`BEq` 的实例来重载。
配套的 {name}`Hashable` 类为类型指定哈希过程。
当某个类型同时具有 {name}`BEq` 和 {name}`Hashable` 实例时，计算出的哈希值应当遵循 {name}`BEq` 实例：被 {name}`BEq.beq` 判为相等的两个值应始终具有相同的哈希值。

{docstring BEq}

{docstring Hashable}

{docstring mixHash}

{docstring LawfulBEq}

{docstring ReflBEq}

{docstring EquivBEq}

{docstring LawfulHashable}

{docstring hash_eq}

# 排序关系
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Ordering"
%%%

主要有两种方式为一个类型的值规定次序：
 * {name}`Ord` 类型类提供三路比较运算符 {name}`compare`，它可以指出一个值小于、等于或大于另一个值。它返回一个 {name}`Ordering`。
 * {name}`LT` 和 {name}`LE` 类为类型提供取值于 {lean}`Prop` 的典范排序关系，且这些关系不必是可判定的。它们用于重载 `<` 和 `≤` 运算符。

{docstring Ord}

{name}`compare` 方法已被导出，因此使用它时无需显式写出 `Ord` 命名空间。

{docstring compareOn}

{docstring Ord.opposite}

{docstring Ordering}

{docstring Ordering.swap}

{docstring Ordering.then}

{docstring Ordering.isLT}

{docstring Ordering.isLE}

{docstring Ordering.isEq}

{docstring Ordering.isNe}

{docstring Ordering.isGE}

{docstring Ordering.isGT}

{docstring compareOfLessAndEq}

{docstring compareOfLessAndBEq}

{docstring compareLex}

:::syntax term (title := "排序运算符")

小于运算符在 {name}`LT` 类中重载：

```grammar
$_ < $_
```

小于等于运算符在 {name}`LE` 类中重载：

```grammar
$_ ≤ $_
```

大于和大于等于运算符分别是小于和小于等于运算符的反向形式，不能独立重载：

```grammar
$_ > $_
```

```grammar
$_ ≥ $_
```

:::

{docstring LT}

{docstring LE}

可以用以下辅助函数从 {name}`Ord` 构造 {name}`BEq`、{name}`LT` 和 {name}`LE` 实例。
这些辅助函数不会自动成为实例，因为对许多类型而言，自定义关系更为合适。

{docstring ltOfOrd}

{docstring leOfOrd}

{docstring Ord.toBEq}

{docstring Ord.toLE}

{docstring Ord.toLT}

:::example "使用 `Ord` 实例构造 `LT` 和 `LE` 实例"

Lean 可以自动派生 {name}`Ord` 实例。
在本例中，{inst}`Ord Vegetable` 实例按字典序比较蔬菜：
```lean
structure Vegetable where
  color : String
  size : Fin 5
deriving Ord
```

```lean
def broccoli : Vegetable where
  color := "green"
  size := 2

def sweetPotato : Vegetable where
  color := "orange"
  size := 3
```


使用辅助函数 {name}`ltOfOrd` 和 {name}`leOfOrd`，可以定义 {inst}`LT Vegetable` 与 {inst}`LE Vegetable` 实例。
这些实例使用 {name}`compare` 比较蔬菜，并在逻辑上断言结果符合预期。
```lean
instance : LT Vegetable := ltOfOrd
instance : LE Vegetable := leOfOrd
```

所得关系是可判定的，因为 {lean}`Ordering` 上的相等性是可判定的：

```lean (name := brLtSw)
#eval broccoli < sweetPotato
```
```leanOutput brLtSw
true
```
```lean (name := brLeSw)
#eval broccoli ≤ sweetPotato
```
```leanOutput brLeSw
true
```
```lean (name := brLtBr)
#eval broccoli < broccoli
```
```leanOutput brLtBr
false
```
```lean (name := brLeBr)
#eval broccoli ≤ broccoli
```
```leanOutput brLeBr
true
```
:::

## 实例构造
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Ordering--Instance-Construction"
%%%

{docstring Ord.lex}

{docstring Ord.lex'}

{docstring Ord.on}

# 最小值与最大值
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Minimum-and-Maximum-Values"
%%%

类 `Max` 和 `Min` 提供重载运算符，用于从两个值中选择较大者或较小者。
若 `Ord`、`LT` 和 `LE` 实例存在，它们应当与这些运算符保持一致，但并没有强制这一点的机制。

{docstring Min}

{docstring Max}

:::leanSection

```lean -show
variable {α : Type u} [LE α]
```

给定一个 {name}`LE.le` 可判定的 {inst}`LE α` 实例，可以使用辅助函数 {name}`minOfLe` 和 {name}`maxOfLe` 创建合适的 {lean}`Min α` 与 {lean}`Max α` 实例。
它们可以用作 {keywordOf Lean.Parser.Command.declaration}`instance` 声明的右侧。

{docstring minOfLe}

{docstring maxOfLe}

:::

# 可判定性
%%%
tag := "decidable-propositions"
%%%

如果一个命题可以通过算法检查，那么它就是{deftech (key := "decidable")}_可判定的_。{index}[可判定]{index (subterm := "可判定")}[命题]
排中律意味着每个命题非真即假，但它没有提供检查究竟是哪种情形成立的方法；而这种检查往往很有用。
默认情况下，作用域中只有可生成代码的算法式 {lean}`Decidable` 实例；打开 `Classical` 命名空间则会使每个命题都可判定。

{docstring Decidable}

{docstring DecidablePred}

{docstring DecidableRel}

{docstring DecidableEq}

{docstring DecidableLT}

{docstring DecidableLE}

{docstring Decidable.decide}

{docstring Decidable.byCases}

::::keepEnv
:::example "排中律与 {lean}`Decidable`"
从 {lean}`Nat` 到 {lean}`Nat` 的函数之间的相等性不可判定：
```lean +error (name := NatFunNotDecEq)
example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```
```leanOutput NatFunNotDecEq
failed to synthesize instance of type class
  Decidable (f = g)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

打开 `Classical` 会使每个命题都可判定；不过，使用这一事实的声明和示例必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，以表明不应为它们生成代码。
```lean
open Classical
noncomputable example (f g : Nat → Nat) : Decidable (f = g) :=
  inferInstance
```

:::
::::


# 有元素的类型
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Inhabited-Types"
%%%

{docstring Inhabited}

{docstring Nonempty}

# 至多单元素类型
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Subsingleton-Types"
%%%

{docstring Subsingleton}

{docstring Subsingleton.elim}

{docstring Subsingleton.helim}

# 可见表示
%%%
tag := "visible-representations"
draft := true
%%%
:::planned 135
 * `ToString`
 * 指向 `Repr` 一节的交叉引用
 * 何时使用 {name}`Repr`，何时使用 {name}`ToString`
:::


{docstring ToString +allowMissing}

# 算术与位运算符
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Arithmetic-and-Bitwise-Operators"
%%%

{docstring Zero}

{docstring NeZero}

{docstring HAdd}

{docstring Add}

{docstring HSub}

{docstring Sub}

{docstring HMul}

{docstring SMul}

{docstring Mul}

{docstring HDiv}

{docstring Div}

{docstring Dvd}

{docstring HMod}

{docstring Mod}

{docstring HPow}

{docstring Pow}

{docstring NatPow}

{docstring HomogeneousPow}

{docstring HShiftLeft}

{docstring ShiftLeft}

{docstring HShiftRight}

{docstring ShiftRight}

{docstring Neg}

{docstring HAnd}

{docstring AndOp}

{docstring HOr}

{docstring OrOp}

{docstring HXor}

{docstring XorOp}

# 追加
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Append"
%%%

{docstring HAppend}

{docstring Append}

# 数据查找
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Basic-Classes--Data-Lookups"
%%%

{docstring GetElem}

{docstring GetElem?}

{docstring LawfulGetElem}
