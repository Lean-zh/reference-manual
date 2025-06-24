namespace ZhDoc

/-
Quotient types coarsen the propositional equality for a type so that terms related by some
equivalence relation are considered equal. The equivalence relation is given by an instance of
`Setoid`.

Set-theoretically, `Quotient s` can seen as the set of equivalence classes of `α` modulo the
`Setoid` instance's relation `s.r`. Functions from `Quotient s` must prove that they respect `s.r`:
to define a function `f : Quotient s → β`, it is necessary to provide `f' : α → β` and prove that
for all `x : α` and `y : α`, `s.r x y → f' x = f' y`. `Quotient.lift` implements this operation.

The key quotient operators are:
 * `Quotient.mk` places elements of the underlying type `α` into the quotient.
 * `Quotient.lift` allows the definition of functions from the quotient to some other type.
 * `Quotient.sound` asserts the equality of elements related by `r`
 * `Quotient.ind` is used to write proofs about quotients by assuming that all elements are
   constructed with `Quotient.mk`.

`Quotient` is built on top of the primitive quotient type `Quot`, which does not require a proof
that the relation is an equivalence relation. `Quotient` should be used instead of `Quot` for
relations that actually are equivalence relations.
-/

/--
商类型将某一类型的命题等价关系变粗,使得由某个等价关系关联的项被视为相等。该等价关系由`Setoid`的一个实例给出。

从集合论的角度来看,`Quotient s`可以被看作是`α`在`Setoid`实例的关系`s.r`下的等价类的集合。
来自`Quotient s`的函数必须证明它们满足`s.r`:
- 定义一个函数`f : Quotient s → β`,
- 提供`f' : α → β`
- 并证明对于所有`x : α`和`y : α`,有`s.r x y → f' x = f' y`。
`Quotient.lift`实现了这个操作。

主要的商操作符包括:
* `Quotient.mk`将底层类型`α`的元素放入商类型中。
* `Quotient.lift`允许从商类型定义到另一个类型的函数。
* `Quotient.sound`断言由`r`关联的元素相等。
* `Quotient.ind`用于在证明商类型时假设所有元素都是通过`Quotient.mk`构造的。

`Quotient`构建在原始商类型`Quot`之上,后者不需要关系是等价关系的证明。对于确实为等价关系的场景,应使用`Quotient`而非`Quot`。
-/
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r


/-
A setoid is a type with a distinguished equivalence relation, denoted `≈`.

The `Quotient` type constructor requires a `Setoid` instance.

class Setoid (α : Sort u) where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r : α → α → Prop
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv : Equivalence r
-/

/--
Setoid 是一个带有特殊等价关系(记作 ≈)的类型

 `Quotient` 类型的构造子需要一个 Setoid 实例
-/
class Setoid (α : Sort u) where
  /-- `x ≈ y` 是一个集合体(setoid)的特殊等价关系。 -/
  r : α → α → Prop
  /--  `x ≈ y` 是一个等价关系。 -/
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

/-
/-- A setoid's equivalence relation is reflexive. -/
theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

/-- A setoid's equivalence relation is symmetric. -/
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

/-- A setoid's equivalence relation is transitive. -/
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc
-/
variable {α : Sort u} [Setoid α]

namespace Setoid
/-- 集合体的等价关系是自反的。 -/
theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

/-- 集合体的等价关系是对称的。 -/
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

/-- 集合体的等价关系是有传递性的-/
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid

/-
/-- `HasEquiv α` is the typeclass which supports the notation `x ≈ y` where `x y : α`.-/
class HasEquiv (α : Sort u) where
  /-- `x ≈ y` says that `x` and `y` are equivalent. Because this is a typeclass,
  the notion of equivalence is type-dependent. -/
  Equiv : α → α → Sort v
-/

/-- `HasEquiv α`是一个类型类,它支持记号`x ≈ y`,其中`x y : α`.-/
class HasEquiv (α : Sort u) where
  /-- ``x ≈ y`表示`x`和`y`是等价的。由于这是一个类型类，等价的概念取决于类型。 -/
  Equiv : α → α → Sort v


/-
/--
An equivalence relation `r : α → α → Prop` is a relation that is

* reflexive: `r x x`,
* symmetric: `r x y` implies `r y x`, and
* transitive: `r x y` and `r y z` implies `r x z`.

Equality is an equivalence relation, and equivalence relations share many of the properties of
equality.
-/
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- An equivalence relation is reflexive: `r x x` -/
  refl  : ∀ x, r x x
  /-- An equivalence relation is symmetric: `r x y` implies `r y x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is transitive: `r x y` and `r y z` implies `r x z` -/
  trans : ∀ {x y z}, r x y → r y z → r x z
-/

/--
一个等价关系 r: α → α → Prop 是满足以下条件的关系:

* 自反性: r x x,
* 对称性: r x y 蕴含 r y x, 并且
* 传递性: r x y 且 r y z 蕴含 r x z.

相等关系是一个等价关系, 并且等价关系具有许多与相等关系类似的性质。
-/
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- 等价关系具有自反性: `r x x` -/
  refl  : ∀ x, r x x
  /-- 等价关系具有对称性: `r x y` 蕴含 `r y x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- 等价关系具有传递性: `r x y` 和 `r y z` 蕴含 `r x z` -/
  trans : ∀ {x y z}, r x y → r y z → r x z

end ZhDoc
