/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Functions
import Manual.Language.InductiveTypes

import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Quotients

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


/-
#doc (Manual) "Quotients" =>
%%%
tag := "quotients"
%%%
-/

#doc (Manual) "商类型" =>
%%%
file := "Quotients"
tag := "quotients"
%%%
/-
{deftech}_Quotient types_ allow a new type to be formed by decreasing the granularity of an existing type's {tech}[propositional equality].
In particular, given an type $`A` and an equivalence relation $`\sim`, the quotient $`A / \sim` contains the same elements as $`A`, but every pair of elements that are related by $`\sim` are considered equal.
Equality is respected universally; nothing in Lean's logic can observe any difference between two equal terms.
Thus, quotient types provide a way to build an impenetrable abstraction barrier.
In particular, all functions from a quotient type must prove that they respect the equivalence relation.
-/
{deftech key := "quotient types"}_商类型_ 允许通过降低现有类型的{tech key := "propositional equality"}[命题等价]的细粒度来构造新类型。
具体来说，给定一个类型 $`A` 和一个等价关系 $`\sim`，商 $`A / \sim` 拥有与 $`A` 相同的元素，但每对被 $`\sim` 相关联的元素在新类型中都被视为相等。
等价性在全局范围内都被满足：Lean 的逻辑中任何事物都无法察觉两个被判等的项的不同。
因此，商类型为我们构建一种不可穿透的抽象屏障提供了途径。
特别是，所有从商类型出发的函数都必须证明它们满足该等价关系。

{zhdocstring Quotient ZhDoc.Quotient}

/-
A proof that two elements of the underlying type are related by the equivalence relation is sufficient to prove that they are equal in the {name}`Quotient`.
However, {tech}[definitional equality] is unaffected by the use of {lean}`Quotient`: two elements in the quotient are definitionally equal if and only if they are definitionally equal in the underlying type.
-/

只要能够证明底层类型的两个元素通过等价关系相关联，那么它们在{name}`Quotient` 中就是相等的。
然而，{tech key := "definitional equality"}[定义等价]不会因使用 {lean}`Quotient` 而改变：两个商中的元素只有当它们本就在底层类型中定义等价时，才在商类型中定义等价。

/-
:::paragraph
Quotient types are not widely used in programming.
However, they occur regularly in mathematics:

: Integers

  The integers are traditionally defined as a pair of natural numbers $`(n, k)` that encodes the integer $`n - k`.
  In this encoding, two integers $`(n_1, k_1)` and $`(n_2, k_2)` are equal if $`n_1 + k_2 = n_2 + k_1`.

: Rational Numbers

  The number $`\frac{n}{d}` can be encoded as the pair $`(n, d)`, where $`d \neq 0`.
  Two rational numbers $`\frac{n_1}{d_1}` and $`\frac{n_2}{d_2}` are equal if $`n_1 d_2 = n_2 d_1`.

: Real Numbers

  The real numbers can be represented as a Cauchy sequence, but this encoding is not unique.
  Using a quotient type, two Cauchy sequences can be made equal when their difference converges to zero.

: Finite Sets

  Finite sets can be represented as lists of elements.
  With a quotient types, two finite sets can be made equal if they contain the same elements; this definition does not impose any requirements (such as decidable equality or an ordering relation) on the type of elements.

:::
-/

:::paragraph
商类型在编程中用得不多，但在数学中非常常见:

: 整数

  整数传统上可表示为自然数对 $`(n, k)`，它编码整数 $`n - k`。
  在这种编码下，两个整数 $$`(n_1, k_1)` 和 $`(n_2, k_2)` 当且仅当 $`n_1 + k_2 = n_2 + k_1` 时视为相等。

: 有理数

  有理数 $`\frac{n}{d}` 可编码为 `(n, d)`，其中 $`d \neq 0`。两个有理数 $`\frac{n_1}{d_1}` 和 $`\frac{n_2}{d_2}` 当且仅当 $`n_1 d_2 = n_2 d_1` 时视为相等。

: 实数

  实数可以用柯西序列来表示，但此编码不是唯一的。利用商类型，可以让它们的差收敛到零时的柯西序列判为相等。

: 有限集

  有限集可以用元素列表表示。通过商类型，如果两个列表包含的元素完全相同（不用要求元素类型有判定等价或序关系），则它们视为相等。

:::

/-
One alternative to quotient types would be to reason directly about the equivalence classes introduced by the relation.
The downside of this approach is that it does not allow _computation_: in addition to knowing _that_ there is an integer that is the sum of 5 and 8, it is useful for $`5 + 8 = 13` to not be a theorem that requires proof.
Defining functions out of sets of equivalence classes relies on non-computational classical reasoning principles, while functions from quotient types are ordinary computational functions that additionally respect an equivalence relation.
-/

与商类型对应的另一个选项就是直接对等价类进行推理。
这种方式的劣势在于其不可“计算”：知道 _确有_ 一个整数等于 $`5+8` 当然很好，对于 $`5+8=13` 来说，它不应是一个需要证明的定理。
基于等价类集合定义函数需要依赖不可计算的经典推理原则，而商类型中的函数则是普通的可计算函数，并且还尊重等价关系。

/-
# Alternatives to Quotient Types
%%%
tag := "quotient-alternatives"
%%%
-/

# 商类型的替代方案
%%%
file := "Alternatives to Quotient Types"
tag := "quotient-alternatives"
%%%

/-
While {name}`Quotient` is a convenient way to form quotients with reasonable computational properties, it is often possible to define quotients in other ways.
-/

虽然 {name}`Quotient` 提供了一种带有合理可计算性的方便商构造方式，但通常还可以通过其他办法定义商类型。

/-
In general, a type $`Q` is said to be the quotient of $`A` by an equivalence relation $`\sim` if it respects the universal property of quotients: there is a function $`q:A\to Q` with the property that $`q(a)=q(b)` if and only if $`a\sim b` for all $`a` and $`b` in $`A`.
-/
一般来说，当一个类型 $`Q` 满足商的普适性质时，它被称为 $`A` 关于等价关系 $`\sim` 的商类型：存在一个函数 $`q : A \to Q`，使得 $`\forall a, b \in A, q(a) = q(b) \iff a \sim b`。

/-
Quotients formed with {name}`Quotient` have this property up to {tech}[propositional equality]: elements of $`A` that are related by $`\sim` are equal, so they cannot be distinguished.
However, members of the same equivalence class are not necessarily {tech key:="definitional equality"}[definitionally equal] in the quotient.
-/

由 {name}`Quotient` 形成的商只在{tech key := "propositional equality"}[命题等价]意义下满足这一性质：被 $`\sim`$ 相关联的 $`A` 的元素在商类型中也是等价的，因此无法区分。
然而，同一个等价类中的成员在商类型中不一定{tech key:="definitional equality"}[定义等价]。

/-
Quotients may also be implemented by designating a single representative of each equivalence class in $`A` itself, and then defining $`Q` as pair of elements in $`A` with proofs that they are such a canonical representative.
Together with a function that maps each $`a` in $`A` to its canonical representative, $`Q` is a quotient of $`A`.
Due to {tech}[proof irrelevance], representatives in $`Q` of the same equivalence class are {tech key:="definitional equality"}[definitionally equal].
-/

还有一种实现方式是：在 $`A` 内为每个等价类选择一个唯一代表，然后将 $`Q` 定义为 $`A` 中的元素对，再加上它们确实是该标准代表的证明。配合一个把 $`A` 中每个 $`a` 都映射到其标准代表的函数，$`Q` 就成了 $`A` 的商类型。
由于 {tech key := "proof irrelevance"}[证明无关性]，$`Q` 内同一等价类代表在定义上就是{tech key:="definitional equality"}[定义相等]的。

/-
Such a manually implemented quotient $`Q` can be easier to work with than {name}`Quotient`.
In particular, because each equivalence class is represented by its single canonical representative, there's no need to prove that functions from the quotient respect the equivalence relation.
It can also have better computational properties due to the fact that the computations give normalized values (in contrast, elements of {name}`Quotient` can be represented in multiple ways).
Finally, because the manually implemented quotient is an {tech}[inductive type], it can be used in contexts where other kinds of types cannot, such as when defining a {ref "nested-inductive-types"}[nested inductive type].
However, not all quotients can be manually implemented.
-/

这种手工实现的商类型 $Q$ 往往比 {name}`Quotient` 更好用。
特别是，由于每个等价类由唯一标准代表表示，定义自商类型的函数再不需要证明其尊重等价关系。
这样也常带来更好的计算效果（商类型下同一个元素可能有多种表现形式，而手工商类型始终规范）。
最后，手工商类型是{tech key:="inductive type"}[归纳类型]，因此能在某些场景用作嵌套归纳类型等用途，而 {name}`Quotient` 却不能。
然而，并非所有商类型都能手工实现。

/-
:::example "Manually Quotiented Integers"
When implemented as pairs of {lean}`Nat`s, each equivalence class according to the desired equality for integers has a canonical representative in which at least one of the {lean}`Nat`s is zero.
This can be represented as a Lean structure:
```lean
structure Z where
  a : Nat
  b : Nat
  canonical : a = 0 ∨ b = 0
```
Due to {tech}[proof irrelevance], every value of this structure type that represents the same integer is _already_ equal.
Constructing a {lean}`Z` can be made more convenient with a wrapper that uses the fact that subtraction of natural numbers truncates at zero to automate the construction of the proof:
```lean
def Z.mk' (n k : Nat) : Z where
  a := n - k
  b := k - n
  canonical := by omega
```

This construction respects the equality demanded of integers:
```lean
theorem Z_mk'_respects_eq :
    (Z.mk' n k = Z.mk' n' k') ↔ (n + k' = n' + k) := by
  simp [Z.mk']
  omega
```

To use this type in examples, it's convenient to have {name}`Neg`, {name}`OfNat`, and {name}`ToString` instances.
These instances make it easier to read or write examples.

```lean
instance : Neg Z where
  neg n := Z.mk' n.b n.a

instance : OfNat Z n where
  ofNat := Z.mk' n 0

instance : ToString Z where
  toString n :=
    if n.a = 0 then
      if n.b = 0 then "0"
      else s!"-{n.b}"
    else toString n.a
```
```lean (name := intFive)
#eval (5 : Z)
```
```leanOutput intFive
5
```
```lean (name := intMinusFive)
#eval (-5 : Z)
```
```leanOutput intMinusFive
-5
```


Addition is addition of the underlying {lean}`Nat`s:
```lean
instance : Add Z where
  add n k := Z.mk' (n.a + k.a) (n.b + k.b)
```

```lean (name := addInt)
#eval (-5 + 22: Z)
```
```leanOutput addInt
17
```

Because each equivalence class is uniquely represented, there's no need to write a proof that these functions from {lean}`Z` respect the equivalence relation.
However, in practice, the {ref "quotient-api"}[API for quotients] should be implemented for manually-constructed quotients and proved to respect the universal property.

:::
-/

:::example "手工实现的商类型整数"
作为{lean}`Nat`对实现时，根据整数所需等式，每个等价类有至少一个{lean}`Nat`为零的标准代表。这可表示为Lean结构：
```lean
structure Z where
  a : Nat
  b : Nat
  canonical : a = 0 ∨ b = 0
```
因{tech key := "proof irrelevance"}[证明无关性]，该结构类型中表示相同整数的每个值_已经_等价。用自然数截断于零的减法自动化证明构建，包装器使{lean}`Z`构造更便利：
```lean
def Z.mk' (n k : Nat) : Z where
  a := n - k
  b := k - n
  canonical := by omega
```

此构造满足整数所需等式：
```lean
theorem Z_mk'_respects_eq :
    (Z.mk' n k = Z.mk' n' k') ↔ (n + k' = n' + k) := by
  simp [Z.mk']
  omega
```

为了在示例中使用此类型，添加{name}`Neg`、{name}`OfNat`和{name}`ToString`实例较便利。这些实例使示例读写更易。

```lean
instance : Neg Z where
  neg n := Z.mk' n.b n.a

instance : OfNat Z n where
  ofNat := Z.mk' n 0

instance : ToString Z where
  toString n :=
    if n.a = 0 then
      if n.b = 0 then "0"
      else s!"-{n.b}"
    else toString n.a
```
```lean (name := intFive)
#eval (5 : Z)
```
```leanOutput intFive
5
```
```lean (name := intMinusFive)
#eval (-5 : Z)
```
```leanOutput intMinusFive
-5
```


加法是底层{lean}`Nat`的加法：
```lean
instance : Add Z where
  add n k := Z.mk' (n.a + k.a) (n.b + k.b)
```

```lean (name := addInt)
#eval (-5 + 22: Z)
```
```leanOutput addInt
17
```

由于每个等价类都唯一表示，自该类型出发的函数无需再证明符合等价关系。不过，实际开发中，建议为手动实现的商类型补齐 {ref "quotient-api"}[商类型 API] 以及相关的普遍性质证明。
:::


/-
:::example "Built-In Integers as Quotients"

Lean's built-in integer type {lean}`Int` satisfies the universal property of quotients, and can thus be thought of as a quotient of pairs of {lean}`Nat`s.
The canonical representative of each equivalence class can be computed via comparison and subtraction:{margin}[This {lean}`toInt` function is called {name}`Int.subNatNat` in the standard library.]
```lean
def toInt (n k : Nat) : Int :=
  if n < k then - (k - n : Nat)
  else if n = k then 0
  else (n - k : Nat)
```

It satisfies the universal property.
Two pairs of {lean}`Nat`s are represent the same integer if and only if {lean}`toInt` computes the same {lean}`Int` for both pairs:
```lean
theorem toInt_sound :
    n + k' = k + n' ↔
    toInt n k = toInt n' k' := by
  simp only [toInt]
  split <;> split <;> omega
```
:::
-/

:::example "内建整数类型作为商类型"

Lean 内建的整数类型 {lean}`Int` 满足商类型的普遍性质，可以看作是 {lean}`Nat` 对的商类型。每个等价类的代表元可以通过比较和减法计算得出：{margin}[标准库中该函数叫 {name}`Int.subNatNat`。]
```lean
def toInt (n k : Nat) : Int :=
  if n < k then - (k - n : Nat)
  else if n = k then 0
  else (n - k : Nat)
```

它满足商类型的普遍性质。两个 {lean}`Nat` 对只有在 {lean}`toInt` 计算结果相等时代表同一个整数：
```lean
theorem toInt_sound :
    n + k' = k + n' ↔
    toInt n k = toInt n' k' := by
  simp only [toInt]
  split <;> split <;> omega
```
:::

/-
# Setoids
%%%
tag := "setoids"
%%%
-/

# 集合体 （Setoid）
%%%
file := "Setoids"
tag := "setoids"
%%%

/-
Quotient types are built on setoids.
A {deftech}_setoid_ is a type paired with a distinguished equivalence relation.
Unlike a quotient type, the abstraction barrier is not enforced, and proof automation designed around equality cannot be used with the setoid's equivalence relation.
Setoids are useful on their own, in addition to being a building block for quotient types.
-/

商类型基于集合体（setoid）概念。
{deftech key := "setoid"}_集合体_ 指一个类型和其上选定的等价关系的配对。
不同于商类型，集合体并不强制抽象屏障，对等价关系的自动化证明（如简化）不能直接用集合体中的等价关系。
除了作为商类型的基础结构外，集合体本身也有其用途。


{zhdocstring Setoid ZhDoc.Setoid}

{zhdocstring Setoid.refl ZhDoc.Setoid.refl}

{zhdocstring Setoid.symm ZhDoc.Setoid.symm}

{zhdocstring Setoid.trans ZhDoc.Setoid.symm}

/-
# Equivalence Relations
%%%
tag := "equivalence-relations"
%%%
-/

# 等价关系
%%%
file := "Equivalence Relations"
tag := "equivalence-relations"
%%%

/-
An {deftech}_equivalence relation_ is a relation that is reflexive, symmetric, and transitive.
-/

{deftech key := "equivalence relation"}_等价关系_ 指的是自反、对称且传递的关系。

/-
:::syntax term (title := "Equivalence Relations")
Equivalence according to some canonical equivalence relation for a type is written using `≈`, which is overloaded using the {tech}[type class] {name}`HasEquiv`.
```grammar
$_ ≈ $_
```
:::
-/

:::syntax term (title := "等价关系")
某个类型上的“标准”等价关系记为 `≈`，它是通过 {tech key := "type class"}[类型类] {name}`HasEquiv` 重载的。
```grammar
$_ ≈ $_
```
:::

{zhdocstring HasEquiv ZhDoc.HasEquiv}

```lean (show := false)
section
variable (r : α → α → Prop)
```

/-
The fact that a relation {lean}`r` is actually an equivalence relation is stated {lean}`Equivalence r`.
-/

声明某关系 {lean}`r` 实际上是等价关系用 {lean}`Equivalence r` 实现。

{zhdocstring Equivalence ZhDoc.Equivalence}

```lean (show := false)
end
```

每一个 {name}`Setoid` 实例都自动带来一个对应的 {name}`HasEquiv` 实例：

```lean (show := false)
-- Check preceding para
section
variable {α : Sort u} [Setoid α]
/-- info: instHasEquivOfSetoid -/
#guard_msgs in
#synth HasEquiv α
end

```
/-
# Quotient API
%%%
tag := "quotient-api"
%%%
-/

# 商类型 API
%%%
file := "Quotient API"
tag := "quotient-api"
%%%

/-
The quotient API relies on a pre-existing {name}`Setoid` instance.
-/

商类型 API 依赖已存在的 {name}`Setoid` 实例。

/-
## Introducing Quotients
%%%
tag := "quotient-intro"
%%%
-/

## 构造商类型
%%%
file := "Introducing Quotients"
tag := "quotient-intro"
%%%

/-
The type {lean}`Quotient` expects an instance of {lean}`Setoid` as an ordinary parameter, rather than as an {tech}[instance implicit] parameter.
This helps ensure that the quotient uses the intended equivalence relation.
The instance can be provided either by naming the instance or by using {name}`inferInstance`.
-/

{lean}`Quotient` 类型需要以普通参数形式显式传入 {lean}`Setoid` 实例（而不是作为 {tech key := "instance implicit"}[隐式实例] 参数）。
这样可以保证商类型使用的是期望的等价关系。
该实例可通过取名或用 {name}`inferInstance` 获得。

/-
A value in the quotient is a value from the setoid's underlying type, wrapped in {lean}`Quotient.mk`.
-/

商类型中的值实际上就是集合体的底层类型的元素, 用 {lean}`Quotient.mk` 包裹。

{zhdocstring Quotient.mk ZhDoc.Quotient.mk}

{zhdocstring Quotient.mk' ZhDoc.Quotient.mk'}

/-
:::example "The Integers as a Quotient Type"
The integers, defined as pairs of natural numbers where the represented integer is the difference of the two numbers, can be represented via a quotient type.
This representation is not unique: both {lean}`(4, 7)` and {lean}`(1, 4)` represent {lean type:="Int"}`-3`.

Two encoded integers should be considered equal when they are related by {name}`Z.eq`:

```lean
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1
```

This relation is an equivalence relation:
```lean
def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega
```

Thus, it can be used as a {name}`Setoid`:
```lean
instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv
```

The type {lean}`Z` of integers is then the quotient of {lean}`Z'` by the {name}`Setoid` instance:

```lean
def Z : Type := Quotient Z.instSetoid
```

The helper {lean}`Z.mk` makes it simpler to create integers without worrying about the choice of {name}`Setoid` instance:
```lean
def Z.mk (n : Z') : Z := Quotient.mk _ n
```

However, numeric literals are even more convenient.
An {name}`OfNat` instance allows numeric literals to be used for integers:
```lean
instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
:::
-/

:::example "用商类型定义整数"
整数可定义为一对自然数，并通过它们的差值来表示。该表示不是唯一的，比如 {lean}`(4, 7)` 和 {lean}`(1, 4)` 都表示 {lean type:="Int"}`-3`。


两个整数编码在何时相等由 {name}`Z.eq` 决定：

```lean
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1
```

该关系是个等价关系：
```lean
def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega
```

可以据此实现 {name}`Setoid` 实例：
```lean
instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv
```

于是类型 {lean}`Z` 是 {lean}`Z'` 在此 {name}`Setoid` 实例下的商类型：

```lean
def Z : Type := Quotient Z.instSetoid
```

可用辅助函数 {lean}`Z.mk` 省去每次显式传递实例的麻烦：
```lean
def Z.mk (n : Z') : Z := Quotient.mk _ n
```

当然，数值字面量更方便。给出 {name}`OfNat` 实例可让整数接受数字字面量：
```lean
instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
:::

/-
## Eliminating Quotients
%%%
tag := "quotient-elim"
%%%
-/

## 消解商类型
%%%
file := "Eliminating Quotients"
tag := "quotient-elim"
%%%

/-
Functions from quotients can be defined by proving that a function from the underlying type respects the quotient's equivalence relation.
This is accomplished using {lean}`Quotient.lift` or its binary counterpart {lean}`Quotient.lift₂`.
The variants {lean}`Quotient.liftOn` and {lean}`Quotient.liftOn₂` place the quotient parameter first rather than last in the parameter list.
-/

要从商类型出发定义函数，只需证明相应的底层函数保持等价关系。
可使用 {lean}`Quotient.lift` 或二元版本 {lean}`Quotient.lift₂` 实现。
变体 {lean}`Quotient.liftOn` 和 {lean}`Quotient.liftOn₂` 则是将商类型实参放在参数列表前。

{zhdocstring Quotient.lift ZhDoc.Quotient.lift}

{zhdocstring Quotient.liftOn ZhDoc.Quotient.liftOn}

{zhdocstring Quotient.lift₂ ZhDoc.Quotient.lift₂}

{zhdocstring Quotient.liftOn₂ ZhDoc.Quotient.liftOn₂}


/-
:::example "Integer Negation and Addition"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n
```

Given the encoding {lean}`Z` of integers as a quotient of pairs of natural numbers, negation can be implemented by swapping the first and second projections:
```lean
def neg' : Z' → Z
  | (x, y) => .mk (y, x)
```

This can be transformed into a function from {lean}`Z` to {lean}`Z` by proving that negation respects the equivalence relation:
```lean
instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega
```

Similarly, {lean}`Quotient.lift₂` is useful for defining binary functions from a quotient type.
Addition is defined point-wise:
```lean
def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)
```

Lifting it to the quotient requires a proof that addition respects the equivalence relation:
```lean
instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega
```
:::
-/


:::example "整数的取负与加法"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n
```
对于给定的由一对自然数编码而成的整数{lean}`Z`, 取负操作就是交换两分量：
Given the encoding {lean}`Z` of integers as a quotient of pairs of natural numbers, negation can be implemented by swapping the first and second projections:
```lean
def neg' : Z' → Z
  | (x, y) => .mk (y, x)
```

只要证明其符合等价关系，即可用 {lean}`Quotient.lift` 升级为商类型上的函数：
```lean
instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega
```

类似地，{lean}`Quotient.lift₂` 可定义二元运算，例如分量加法：
```lean
def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)
```

用等价关系证明加法保持等价后即可“提升”：
```lean
instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega
```
:::

/-
When the function's result type is a {tech}[subsingleton], {name}`Quotient.recOnSubsingleton` or {name}`Quotient.recOnSubsingleton₂` can be used to define the function.
Because all elements of a subsingleton are equal, such a function automatically respects the equivalence relation, so there is no proof obligation.
-/

若函数的返回类型是 {tech key := "subsingleton"}[子单元]，可用 {name}`Quotient.recOnSubsingleton` 或 {name}`Quotient.recOnSubsingleton₂` 直接定义。
因为目标类型的所有元素都已相等，函数自然保持等价关系。

{zhdocstring Quotient.recOnSubsingleton ZhDoc.Quotient.recOnSubsingleton}

{zhdocstring Quotient.recOnSubsingleton₂ ZhDoc.Quotient.recOnSubsingleton₂}

/-
## Proofs About Quotients
%%%
tag := "quotient-proofs"
%%%
-/

## 商类型上的证明
%%%
file := "Proofs About Quotients"
tag := "quotient-proofs"
%%%


/-
The fundamental tools for proving properties of elements of quotient types are the soundness axiom and the induction principle.
The soundness axiom states that if two elements of the underlying type are related by the quotient's equivalence relation, then they are equal in the quotient type.
The induction principle follows the structure of recursors for inductive types: in order to prove that a predicate holds all elements of a quotient type, it suffices to prove that it holds for an application of {name}`Quotient.mk` to each element of the underlying type.
Because {name}`Quotient` is not an {tech}[inductive type], tactics such as {tactic}`cases` and {tactic}`induction` require that {name}`Quotient.ind` be specified explicitly with the {keyword}`using` modifier.
-/

在商类型上证明性质，主要工具是 soundness 公理和归纳原理。
soundness 公理表明，如果两个底层类型中的元素满足等价关系，则在商类型中相等。
归纳原理类似于归纳类型的递归：若要证明某谓词对全部商类型元素成立，只需证明对每个 {name}`Quotient.mk` 形式的元素成立即可。
由于 {name}`Quotient` 不是 {tech key := "inductive type"}[归纳类型]，使用如 {tactic}`cases` 或 {tactic}`induction` 时需显式指定 {name}`Quotient.ind` 并用 {keyword}`using` 修饰。


{zhdocstring Quotient.sound ZhDoc.Quotient.sound}

{zhdocstring Quotient.ind ZhDoc.Quotient.ind}

/-
:::example "Proofs About Quotients"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n

def neg' : Z' → Z
  | (x, y) => .mk (y, x)

instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega

def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)

instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega

instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```

Given the definition of integers as a quotient type from the prior examples, {name}`Quotient.ind` and {name}`Quotient.sound` can be used to prove that negation is an additive inverse.
First, {lean}`Quotient.ind` is used to replace instances of `n` with applications of {name}`Quotient.mk`.
Having done so, the left side of the equality becomes definitionally equal to a single application of {name}`Quotient.mk`, via unfolding definitions and the computation rule for {name}`Quotient.lift`.
This makes {name}`Quotient.sound` applicable, which yields a new goal: to show that both sides are related by the equivalence relation.
This is provable using {tactic}`simp_arith`.

```lean
theorem Z.add_neg_inverse (n : Z) : n  + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp +arith [· ≈ ·, Setoid.r, eq]
```

:::
-/

:::example "商类型上的证明"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n

def neg' : Z' → Z
  | (x, y) => .mk (y, x)

instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega

def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)

instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega

instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```

给定前面例子中将整数定义为一个商类型，你可以使用 {name}`Quotient.ind` 和 {name}`Quotient.sound` 来证明取负是加法的逆元。
首先，使用 {lean}`Quotient.ind` 可以将出现的 `n` 替换为 {name}`Quotient.mk` 的应用。
完成这一转换后，等式的左边，通过具体展开定义以及 {name}`Quotient.lift` 的计算规则，可以归约为一次 {name}`Quotient.mk` 的应用，即两边是定义等价的项。
此时，就可以应用 {name}`Quotient.sound`，这将带来一个新的目标：需要证明等式两边通过等价关系相关。
这个目标可以通过 {tactic}`simp_arith` 策略来证明。


```lean
theorem Z.add_neg_inverse (n : Z) : n  + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp +arith [· ≈ ·, Setoid.r, eq]
```

:::

/-
For more specialized use cases, {name}`Quotient.rec`, {name}`Quotient.recOn`, and {name}`Quotient.hrecOn` can be used to define dependent functions from a quotient type to a type in any other universe.
Stating that a dependent function respects the quotient's equivalence relation requires a means of dealing with the fact that the dependent result type is instantiated with different values from the quotient on each side of the equality.
{name}`Quotient.rec` and {name}`Quotient.recOn` use the {name}`Quotient.sound` to equate the related elements, inserting the appropriate cast into the statement of equality, while {name}`Quotient.hrecOn` uses heterogeneous equality.
-/

对于更特设的使用场景，可以使用 {name}`Quotient.rec`，{name}`Quotient.recOn` 和 {name}`Quotient.hrecOn` 来从一个商类型到任意其他宇宙中的类型，定义依值函数。
要说明一个依值函数能够遵循商类型的等价关系，需要处理这样一种情况：依值结果类型在等式两边会用不同的商类型里的值来实例化。
{name}`Quotient.rec` 和 {name}`Quotient.recOn` 会利用 {name}`Quotient.sound` 将相关元素建立等价关系，并在等式中插入恰当的强制转换（cast）；而 {name}`Quotient.hrecOn` 则使用异质等式（heterogeneous equality）。

{zhdocstring Quotient.rec ZhDoc.Quotient.rec}

{zhdocstring Quotient.recOn ZhDoc.Quotient.recOn}

{zhdocstring Quotient.hrecOn ZhDoc.Quotient.hrecOn}

/-
If two elements of a type are equal in a quotient, then they are related by the setoid's equivalence relation.
This property is called {name}`Quotient.exact`.
-/

若某类型的两个元素在某商类型中相等，则它们在集合体等价关系下也等价。这个性质叫做 {name}`Quotient.exact`。


{zhdocstring Quotient.exact ZhDoc.Quotient.exact}


/-

# Logical Model
%%%
tag := "quotient-model"
%%%

-/

# 逻辑模型
%%%
file := "Logical Model"
tag := "quotient-model"
%%%

/-
Like functions and universes, quotient types are a built-in feature of Lean's type system.
However, the underlying primitives are based on the somewhat simpler {name}`Quot` type rather than on {name}`Quotient`, and {name}`Quotient` is defined in terms of {name}`Quot`.
The primary difference is that {name}`Quot` is based on an arbitrary relation, rather than a {name}`Setoid` instance.
The provided relation need not be an equivalence relation; the rules that govern {name}`Quot` and {name}`Eq` automatically extend the provided relation into its reflexive, transitive, symmetric closure.
When the relation is already an equivalence relation, {name}`Quotient` should be used instead of {name}`Quot` so Lean can make use of the fact that the relation is an equivalence relation.
-/

类似函数和宇宙，商类型是 Lean 类型系统的内建特性。
但底层原语是基于更简单的 {name}`Quot` 类型，而不是 {name}`Quotient`，后者是基于前者实现的。
主要区别在于 {name}`Quot` 可以接受任意关系，并不限于 {name}`Setoid` 实例。
而且提供的关系不必先是等价关系。{name}`Quot` 和 {name}`Eq` 的相关规则自动向外扩展为自反、传递和对称。
如果用的是等价关系，应优先选用 {name}`Quotient` 以便 Lean 利用更多性质。

/-
The fundamental quotient type API consists of {lean}`Quot`, {name}`Quot.mk`, {name}`Quot.lift`, {name}`Quot.ind`, and {name}`Quot.sound`.
These are used in the same way as their {name}`Quotient`-based counterparts.
-/

最基本的商类型操作有 {lean}`Quot`，{name}`Quot.mk`，{name}`Quot.lift`，{name}`Quot.ind`，{name}`Quot.sound`。
它们的用法与对应的基于 {name}`Quotient` 的 API 类似。

{zhdocstring Quot ZhDoc.Quot}

{zhdocstring Quot.mk ZhDoc.Quot.mk}

{zhdocstring Quot.lift ZhDoc.Quot.lift}

{zhdocstring Quot.ind ZhDoc.Quot.ind}

{zhdocstring Quot.sound ZhDoc.Quot.sound}

/-
## Quotient Reduction
%%%
tag := "quotient-reduction"
%%%
-/


## 商类型规约
%%%
file := "Quotient Reduction"
tag := "quotient-reduction"
%%%


```lean (show := false)
section
variable
  (α β : Sort u)
  (r : α → α → Prop)
  (f : α → β)
  (resp : ∀ x y, r x y → f x = f y)
  (x : α)
```
/-
In addition to the above constants, Lean's kernel contains a reduction rule for {name}`Quot.lift` that causes it to reduce when used with {name}`Quot.mk`, analogous to {tech}[ι-reduction] for inductive types.
Given a relation {lean}`r` over {lean}`α`, a function {lean}`f` from {lean}`α` to {lean}`β`, and a proof {lean}`resp` that {lean}`f` respects {lean}`r`, the term {lean}`Quot.lift f resp (Quot.mk r x)` is {tech key:="definitional equality"}[definitionally equal] to {lean}`f x`.
-/

除了上述常量之外，Lean 的内核还包含了关于 {name}`Quot.lift` 的规约规则，使其在与 {name}`Quot.mk` 一起使用时能够规约，这类似于归纳类型的 {tech key:="ι-reduction"}[ι-规约]。
给定在 {lean}`α` 上的一个关系 {lean}`r`，一个从 {lean}`α` 到 {lean}`β` 的函数 {lean}`f`，以及一个证明 {lean}`resp`，表明 {lean}`f` 保持了 {lean}`r`，那么项 {lean}`Quot.lift f resp (Quot.mk r x)` 与 {lean}`f x` 是 {tech key:="definitional equality"}[定义等价]的。

```lean (show := false)
end
```

```lean (show := false)
section
```

```lean
variable
  (r : α → α → Prop)
  (f : α → β)
  (ok : ∀ x y, r x y → f x = f y)
  (x : α)

example : Quot.lift f ok (Quot.mk r x) = f x := rfl
```

```lean (show := false)
end
```

/-
## Quotients and Inductive Types
%%%
tag := "quotients-nested-inductives"
%%%
-/

## 商类型与归纳类型
%%%
file := "Quotients and Inductive Types"
tag := "quotients-nested-inductives"
%%%

/-
Because {name}`Quot` is not an inductive type, types implemented as quotients may not occur around {ref "nested-inductive-types"}[nested occurrences] in inductive type declarations.
These types declarations must be rewritten to remove the nested quotient, which can often be done by defining a quotient-free version and then separately defining an equivalence relation that implements the desired equality relation.
-/

由于 {name}`Quot` 不是归纳类型，因此作为商类型实现的类型不能作为 {ref "nested-inductive-types"}[嵌套项] 出现在归纳类型定义中。此时需拆解商类型，将归纳类型定义为无商版本，再对其定义独立的等价关系。

/-
:::example "Nested Inductive Types and Quotients"

The nested inductive type of rose trees nests the recursive occurrence of {lean}`RoseTree` under {lean}`List`:
```lean
inductive RoseTree (α : Type u) where
  | leaf : α → RoseTree α
  | branch : List (RoseTree α) → RoseTree α
```

However, taking a quotient of the {name}`List` that identifies all elements in the style of {ref "squash-types"}[squash types] causes Lean to reject the declaration:
```lean (error := true) (name := nestedquot)
inductive SetTree (α : Type u) where
  | leaf : α → SetTree α
  | branch :
    Quot (fun (xs ys : List (SetTree α)) => True) →
    SetTree α
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```

:::
-/

:::example "嵌套归纳类型与商类型"

{lean}`RoseTree`的嵌套归纳类型，是将递归出现的 {lean}`RoseTree` 嵌套在 {lean}`List` 之下：
```lean
inductive RoseTree (α : Type u) where
  | leaf : α → RoseTree α
  | branch : List (RoseTree α) → RoseTree α
```

然而，对 {name}`List` 按照 {ref "squash-types"}[压缩类型] 的方式，将所有元素视为相同来取商会导致 Lean 拒绝该声明：
```lean (error := true) (name := nestedquot)
inductive SetTree (α : Type u) where
  | leaf : α → SetTree α
  | branch :
    Quot (fun (xs ys : List (SetTree α)) => True) →
    SetTree α
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```

:::

/-
##  底层商类型 API
-/

/-
{name}`Quot.liftOn` is an version of {name}`Quot.lift` that takes the quotient type's value first, by analogy to {name}`Quotient.liftOn`.
-/

{name}`Quot.liftOn` 是 {name}`Quot.lift` 的变体，将商类型值放参数首，与 {name}`Quotient.liftOn` 类似。

{zhdocstring Quot.liftOn ZhDoc.Quot.liftOn}

/-
Lean also provides convenient elimination from {name}`Quot` into any subsingleton without further proof obligations, along with dependent elimination principles that correspond to those used for {name}`Quotient`.
-/
Lean 还提供了从 {name}`Quot` 到任意 {tech key := "subsingleton"}[子单元] 的消解，无需额外证明，以及与 {name}`Quotient` 相对应的依赖消解原理。

{zhdocstring Quot.recOnSubsingleton ZhDoc.Quot.recOnSubsingleton}

{zhdocstring Quot.rec  ZhDoc.Quot.rec}

{zhdocstring Quot.recOn  ZhDoc.Quot.rec}

{zhdocstring Quot.hrecOn ZhDoc.Quot.hrecOn}


/-
# Quotients and Function Extensionality
%%%
tag := "quotient-funext"
%%%
-/

# 商类型与函数外延性
%%%
file := "Quotients and Function Extensionality"
tag := "quotient-funext"
%%%

/-
:::::keepEnv

Because Lean's definitional equality includes a computational reduction rule for {lean}`Quot.lift`, quotient types are used in the standard library to prove function extensionality, which would need to be an {ref "axioms"}[axiom] otherwise.
This is done by first defining a type of functions quotiented by extensional equality, for which extensional equality holds by definition.

```lean
variable {α : Sort u} {β : α → Sort v}

def extEq (f g : (x : α) → β x) : Prop :=
  ∀ x, f x = g x

def ExtFun (α : Sort u) (β : α → Sort v) :=
  Quot (@extEq α β)
```

Extensional functions can be applied just like ordinary functions.
Application respects extensional equality by definition: if applying to functions gives equal results, then applying them gives equal results.
```lean
def extApp
    (f : ExtFun α β)
    (x : α) :
    β x :=
  f.lift (· x) fun g g' h => by
    exact h x
```

```lean (show := false)
section
variable (f : (x : α) → β x)
```
To show that two functions that are extensionally equal are in fact equal, it suffices to show that the functions that result from extensionally applying the corresponding extensional functions are equal.
This is because
```leanTerm
extApp (Quot.mk _ f)
```
is definitionally equal to
```leanTerm
fun x => (Quot.mk extEq f).lift (· x) (fun _ _ h => h x)
```
which is definitionally equal to {lean}`fun x => f x`, which is definitionally equal (by {tech}[η-equivalence]) to {lean}`f`.
A propositional version of the computation rule for {name}`Quot.lift` would not suffice, because the reducible expression occurs in the body of a function and rewriting by an equality in a function would already require function extensionality.

```lean (show := false)
end
```

From here, it is enough to show that the extensional versions of the two functions are equal.
This is true due to {name}`Quot.sound`: the fact that they are in the quotient's equivalence relation is an assumption.
This proof is a much more explicit version of the one in the standard library:

```lean
theorem funext'
    {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) :
    f = g := by
  suffices extApp (Quot.mk _ f) = extApp (Quot.mk _ g) by
    unfold extApp at this
    dsimp at this
    exact this
  suffices Quot.mk extEq f = Quot.mk extEq g by
    apply congrArg
    exact this
  apply Quot.sound
  exact h
```

:::::
-/

:::::keepEnv

由于 Lean 的定义等价包含了 {lean}`Quot.lift` 的计算规约规则，标准库中用商类型来证明函数外延性，否则这个结果通常需要作为一个 {ref "axioms"}[公理] 引入。
具体做法是，先定义一种按外延等价关系取商的函数类型，对于这种类型，外延等价是定义成立的。


```lean
variable {α : Sort u} {β : α → Sort v}

def extEq (f g : (x : α) → β x) : Prop :=
  ∀ x, f x = g x

def ExtFun (α : Sort u) (β : α → Sort v) :=
  Quot (@extEq α β)
```

外延函数和普通函数一样可以调用。
函数应用本身就满足外延等价：只要对所有输入应用得到的结果都相等，那应用后的结果自然也相等。

```lean
def extApp
    (f : ExtFun α β)
    (x : α) :
    β x :=
  f.lift (· x) fun g g' h => by
    exact h x
```

```lean (show := false)
section
variable (f : (x : α) → β x)
```
为了证明两个函数在外延意义下相等就等价于本身相等，只需证明它们各自转换为外延函数之后，再通过外延化应用的方法得到的结果是相等的。
原因在于
```leanTerm
extApp (Quot.mk _ f)
```
在定义上等价于
```leanTerm
fun x => (Quot.mk extEq f).lift (· x) (fun _ _ h => h x)
```
定义上等价于 {lean}`fun x => f x`，而根据 {tech key := "η-equivalence"}[η-等价]，又等价于 {lean}`f`。
如果 {name}`Quot.lift` 的计算规则只是命题形式，而不是定义等价的形式，那就不满足，因为规约表达式会出现在函数体里，按等式重写一整个函数本身就需要函数外延性。

```lean (show := false)
end
```

于是，只要证明参与两端的外延版函数真的相等即可。
这正是由于 {name}`Quot.sound` 成立：即它们本就在商类型的等价关系下。
这里的证明其实比标准库里的写法更为直白：


```lean
theorem funext'
    {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) :
    f = g := by
  suffices extApp (Quot.mk _ f) = extApp (Quot.mk _ g) by
    unfold extApp at this
    dsimp at this
    exact this
  suffices Quot.mk extEq f = Quot.mk extEq g by
    apply congrArg
    exact this
  apply Quot.sound
  exact h
```

:::::

/-
# Squash Types
%%%
tag := "squash-types"
%%%
-/

# 压缩类型
%%%
file := "Squash Types"
tag := "squash-types"
%%%


```lean (show := false)
section
variable {α : Sort u}
```

/-
Squash types are a quotient by the relation that relates all elements, transforming it into a {tech}[subsingleton].
In other words, if {lean}`α` is inhabited, then {lean}`Squash α` has a single element, and if {lean}`α` is uninhabited, then {lean}`Squash α` is also uninhabited.
Unlike {lean}`Nonempty α`, which is a proposition stating that {lean}`α` is inhabited and is thus represented by a dummy value at runtime, {lean}`Squash α` is a type that is represented identically to {lean}`α`.
Because {lean}`Squash α` is in the same universe as {lean}`α`, it is not subject to the restrictions on computing data from propositions.
-/

压缩类型（Squash types）是以“所有元素互相关联”的关系取商后的类型，这样得到的就是一个 {tech key := "subsingleton"}[子单元]。
换句话说，如果 {lean}`α` 中有元素，那么 {lean}`Squash α` 就只有一个元素；如果 {lean}`α` 为空，则 {lean}`Squash α` 也为空。
和 {lean}`Nonempty α` 不同，后者只是一个“{lean}`α` 非空”这一命题，在运行时只表现为一个占位值；而 {lean}`Squash α` 是类型层面的，它在表示层和 {lean}`α` 完全一样。
并且由于 {lean}`Squash α` 和 {lean}`α` 处在同一个宇宙层级，它不受“不能从命题中计算数据”的限制。

```lean (show := false)
end
```

{zhdocstring Squash ZhDoc.Squash}

{zhdocstring Squash.mk ZhDoc.Squash.mk}

{zhdocstring Squash.lift ZhDoc.Squash.lift}

{zhdocstring Squash.ind ZhDoc.Squash.ind}
