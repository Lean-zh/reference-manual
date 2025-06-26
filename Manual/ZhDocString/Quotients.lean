namespace ZhDoc




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


namespace Quotient


/-
/--
Places an element of a type into the quotient that equates terms according to an equivalence
relation.

The setoid instance is provided explicitly. `Quotient.mk'` uses instance synthesis instead.

Given `v : α`, `Quotient.mk s v : Quotient s` is like `v`, except all observations of `v`'s value
must respect `s.r`. `Quotient.lift` allows values in a quotient to be mapped to other types, so long
as the mapping respects `s.r`.
-/
@[inline]
protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=
  Quot.mk Setoid.r a

/--
Places an element of a type into the quotient that equates terms according to an equivalence
relation.

The equivalence relation is found by synthesizing a `Setoid` instance. `Quotient.mk` instead expects
the instance to be provided explicitly.

Given `v : α`, `Quotient.mk' v : Quotient s` is like `v`, except all observations of `v`'s value
must respect `s.r`. `Quotient.lift` allows values in a quotient to be mapped to other types, so long
as the mapping respects `s.r`.

-/
protected def mk' {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quotient.mk s a
-/

/--
把某个类型的元素放入商类型中,该商类型根据等价关系将元素进行等价。

setoid 实例需要显式提供。而 `Quotient.mk'` 使用了实例合成。

给定 `v : α`, `Quotient.mk s v : Quotient s` 类似于 `v`, 只是对 `v` 值都必须满足 `s.r`。
`Quotient.lift` 允许将商类型中的值映射到其他类型,只要这种映射遵循 `s.r`。
-/
@[inline]
protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=
  Quot.mk Setoid.r a

/--
将某个类型的元素放入通过等价关系对项进行等价分类的商类型中。

等价关系是通过合成一个`Setoid`实例来找到的。`Quotient.mk`则要求显式地提供该实例。

给定`v : α`，`Quotient.mk' v : Quotient s`就像是`v`，只不过对`v`值的必须满足`s.r`。
`Quotient.lift`允许将商集中的值映射到其他类型，只要该映射满足`s.r`即可。
-/
protected def mk' {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quotient.mk s a

/-
/--
The **quotient axiom**, which asserts the equality of elements related in the setoid.

Because `Quotient` is built on a lower-level type `Quot`, `Quotient.sound` is implemented as a
theorem. It is derived from `Quot.sound`, the soundness axiom for the lower-level quotient type
`Quot`.
-/
theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=
  Quot.sound
-/

/--
**商等价公理**，它断言在setoid中相关的元素是相等的。

由于`Quotient`是建立在更低层类型`Quot`之上的，`Quotient.sound`被实现为一个定理。它源自于`Quot.sound`，即底层商类型`Quot`的正确性公理。
-/
theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=
  Quot.sound

/-
/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`.
-/
protected theorem ind {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} : ((a : α) → motive (Quotient.mk s a)) → (q : Quotient s) → motive q :=
  Quot.ind
-/

/--
一个关于商类型的推理原则，允许关于商类型的证明假定所有的值都是通过`Quotient.mk`构造的。
-/
protected theorem ind {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} : ((a : α) → motive (Quotient.mk s a)) → (q : Quotient s) → motive q :=
  Quot.ind



/-
/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's equivalence relation.

Given `s : Setoid α` and a quotient `Quotient s`, applying a function `f : α → β` requires a proof
`h` that `f` respects the equivalence relation `s.r`. In this case, the function
`Quotient.lift f h : Quotient s → β` computes the same values as `f`.

`Quotient.liftOn` is a version of this operation that takes the quotient value as its first explicit
parameter.
-/
protected abbrev lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) : ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f
-/
/--
将一个函数从底层类型提升为商类型的函数，要求该函数满足商类型的等价关系。

给定`s : Setoid α`和一个商类型`Quotient s`，应用一个函数`f : α → β`需要一个证明`h`，表明`f`满足等价关系`s.r`。
在这种情况下，函数`Quotient.lift f h : Quotient s → β`的计算结果与`f`一致。

`Quotient.liftOn`是该操作的一个变体，它将商类型的值作为第一个显式参数。
-/
protected abbrev lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) : ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f

/-
/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's equivalence relation.

Given `s : Setoid α` and a quotient value `q : Quotient s`, applying a function `f : α → β` requires
a proof `c` that `f` respects the equivalence relation `s.r`. In this case, the term
`Quotient.liftOn q f h : β` reduces to the result of applying `f` to the underlying `α` value.

`Quotient.lift` is a version of this operation that takes the quotient value last, rather than
first.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s) (f : α → β) (c : (a b : α) → a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c
-/

/--
将一个函数从底层类型提升为作用于商类型的函数，要求该函数满足商类型的等价关系。

给定`s : Setoid α`和一个商类型值`q : Quotient s`，想要应用函数`f : α → β`，需要证明`c`，即`f`满足等价关系`s.r`。在这种情况下，`Quotient.liftOn q f h : β`这一项可以简化为将`f`应用于底层的`α`值的结果。

`Quotient.lift`是该操作的另一个版本，其参数中商类型值放在最后，而不是最前。
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s) (f : α → β) (c : (a b : α) → a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c

section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB} {φ : Sort uC}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/-
/--
Lifts a binary function from the underlying types to a binary function on quotients. The function
must respect both quotients' equivalence relations.

`Quotient.lift` is a version of this operation for unary functions. `Quotient.liftOn₂` is a version
that take the quotient parameters first.
-/
protected abbrev lift₂
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    : φ := by
  apply Quotient.lift (fun (a₁ : α) => Quotient.lift (f a₁) (fun (a b : β) => c a₁ a a₁ b (Setoid.refl a₁)) q₂) _ q₁
  intros
  induction q₂ using Quotient.ind
  apply c; assumption; apply Setoid.refl
-/
/--
将一个二元函数从底层类型提升为作用于商类型的二元函数。该函数必须同时满足两个商类型的等价关系。

`Quotient.lift` 是此操作针对一元函数的版本。`Quotient.liftOn₂` 是接受商类型参数优先的版本。
-/
protected abbrev lift₂
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    : φ := by
  sorry

/-
/--
Lifts a binary function from the underlying types to a binary function on quotients. The function
must respect both quotients' equivalence relations.

`Quotient.liftOn` is a version of this operation for unary functions. `Quotient.lift₂` is a version
that take the quotient parameters last.
-/
protected abbrev liftOn₂
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    : φ :=
  Quotient.lift₂ f c q₁ q₂
-/

/--
把一个二元函数从底层类型提升为作用于商类型上的二元函数。该函数必须兼容两个商类型的等价关系。

`Quotient.liftOn`是针对一元函数的该操作的一个版本。`Quotient.lift₂`是参数中商类型排在最后的版本。
-/
protected abbrev liftOn₂
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    : φ :=
  Quotient.lift₂ f c q₁ q₂





end



section
variable {α : Sort u}
variable {s : Setoid α}
variable {motive : Quotient s → Sort v}

/-
/--
A dependent recursion principle for `Quotient`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:

 * `Quotient.lift` is useful for defining non-dependent functions.
 * `Quotient.ind` is useful for proving theorems about quotients.
 * `Quotient.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quotient.hrecOn` uses heterogeneous equality instead of rewriting with `Quotient.sound`.

`Quotient.recOn` is a version of this recursor that takes the quotient parameter first.
-/
@[inline, elab_as_elim]
protected def rec
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    (q : Quotient s)
    : motive q :=
  Quot.rec f h q
-/

/--
针对 `Quotient` 的依值递归原理。它类似于结构体的 [对鬼子](lean-manual://section/recursors)，可以用于当结果类型不一定是命题时的情况。

虽然此递归子非常通用，但实际使用时可能较为棘手。以下几种更简单的选取，可能更容易上手：

- `Quotient.lift` 适用于定义非依值（非依赖）函数。
- `Quotient.ind` 适用于证明关于商集的定理。
- 每当目标类型是 `Subsingleton`（子单元）时，可以使用 `Quotient.recOnSubsingleton`。
- `Quotient.hrecOn` 使用异质等价（heterogeneous equality），而非通过 `Quotient.sound` 进行重写。

`Quotient.recOn` 是该递归子的一个版本，它首先接收商集参数。
-/
@[inline, elab_as_elim]
protected def rec
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    (q : Quotient s)
    : motive q :=
  Quot.rec f h q


/-
/--
A dependent recursion principle for `Quotient`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:

 * `Quotient.lift` is useful for defining non-dependent functions.
 * `Quotient.ind` is useful for proving theorems about quotients.
 * `Quotient.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quotient.hrecOn` uses heterogeneous equality instead of rewriting with `Quotient.sound`.

`Quotient.rec` is a version of this recursor that takes the quotient parameter last.
-/
@[elab_as_elim]
protected abbrev recOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    : motive q :=
  Quot.recOn q f h
-/

/--
一个用于 `Quotient` 的依值递归原理（dependent recursion principle）。它类似于结构体的[递归子](lean-manual://section/recursors)，当结果类型不一定是命题时，可以使用它。

尽管这个递归子非常通用，但实际使用上可能较为棘手。以下这些更简单的选项通常更易于使用：

 * `Quotient.lift` 适合定义非依值函数。
 * `Quotient.ind` 适合用于对商类型证明定理。
 * 每当目标类型为 {tech key := "subsingleton"}[子单元] 时，可以使用 `Quotient.recOnSubsingleton`。
 * `Quotient.hrecOn` 使用异质等价，而不是通过 `Quotient.sound` 进行重写。

`Quotient.rec` 是该递归子的一个变体，不同之处在于它将商类型参数放在最后。
-/
@[elab_as_elim]
protected abbrev recOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    : motive q :=
  Quot.recOn q f h


/-
/--
An alternative recursion or induction principle for quotients that can be used when the target type
is a subsingleton, in which all elements are equal.

In these cases, the proof that the function respects the quotient's equivalence relation is trivial,
so any function can be lifted.

`Quotient.rec` does not assume that the target type is a subsingleton.
-/
def recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quotient.mk s a))]
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.recOnSubsingleton (h := h) q f

-/

/--
一种用于商类型上的递归或归纳原理的替代方法,当目标类型是子单元(所有元素都相等)时可以使用。

在这些情况下,证明函数满足商类型的等价关系是不必要的,因此任何函数都可以提升。

`Quotient.rec`没有假设目标类型是子单元。
-/
def recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quotient.mk s a))]
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.recOnSubsingleton (h := h) q f

/-/
/--
A dependent recursion principle for `Quotient` that uses [heterogeneous
equality](lean-manual://section/HEq), analogous to a [recursor](lean-manual://section/recursors) for
a structure.

`Quotient.recOn` is a version of this recursor that uses `Eq` instead of `HEq`.
-/
@[elab_as_elim]
protected abbrev hrecOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → (p : a ≈ b) → f a ≍ f b)
    : motive q :=
  Quot.hrecOn q f c
-/

/--
`Quotient` 的一个依值递归原理（dependent recursion principle），它利用了[异质等价](lean-manual://section/HEq)（见 [HEq](lean-manual://section/HEq)），类似于结构体的[递归子](lean-manual://section/recursors)。

`Quotient.recOn` 是这个递归子的一个版本，不过它用的是 `Eq` 而不是 `HEq`。
-/
@[elab_as_elim]
protected abbrev hrecOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → (p : a ≈ b) → f a ≍ f b)
    : motive q :=
  Quot.hrecOn q f c


end



section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/-
/--
An alternative induction or recursion operator for defining binary operations on quotients that can
be used when the target type is a subsingleton.

In these cases, the proof that the function respects the quotient's equivalence relation is trivial,
so any function can be lifted.
-/
@[elab_as_elim]
protected abbrev recOnSubsingleton₂
    {motive : Quotient s₁ → Quotient s₂ → Sort uC}
    [s : (a : α) → (b : β) → Subsingleton (motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))]
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (g : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quot.recOnSubsingleton
  induction q₂ using Quot.recOnSubsingleton
  apply g
  intro a; apply s
  induction q₂ using Quot.recOnSubsingleton
  intro a; apply s
  infer_instance
-/

/--
一种用于在商类型上定义二元运算的替代归纳或递归算子,可用于当目标类型是子单元时。

在这些情况下,证明函数满足商类型的等价关系是不必要的,因此任何函数都可以被提升。
-/
@[elab_as_elim]
protected abbrev recOnSubsingleton₂
    {motive : Quotient s₁ → Quotient s₂ → Sort uC}
    [s : (a : α) → (b : β) → Subsingleton (motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))]
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (g : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quot.recOnSubsingleton
  induction q₂ using Quot.recOnSubsingleton
  apply g
  intro a; apply s
  induction q₂ using Quot.recOnSubsingleton
  intro a; apply s
  infer_instance

end

/-
/--
If two values are equal in a quotient, then they are related by its equivalence relation.
-/
theorem exact {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b := sorry
-/

/--
如果两个值在商类型中是相等的，那么它们必定满足该商类型的等价关系。
-/
theorem exact {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b := sorry

/-
opaque Quot {α : Sort u} (r : α → α → Prop) : Sort u

opaque Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r

opaque Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → Eq (f a) (f b)) → Quot r → β

opaque Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
-/


/-
/--
Low-level quotient types. Quotient types coarsen the propositional equality for a type `α`, so that
terms related by some relation `r` are considered equal in `Quot r`.

Set-theoretically, `Quot r` can seen as the set of equivalence classes of `α` modulo `r`. Functions
from `Quot r` must prove that they respect `r`: to define a function `f : Quot r → β`, it is
necessary to provide `f' : α → β` and prove that for all `x : α` and `y : α`, `r x y → f' x = f' y`.

`Quot` is a built-in primitive:
 * `Quot.mk` places elements of the underlying type `α` into the quotient.
 * `Quot.lift` allows the definition of functions from the quotient to some other type.
 * `Quot.sound` asserts the equality of elements related by `r`.
 * `Quot.ind` is used to write proofs about quotients by assuming that all elements are constructed
   with `Quot.mk`.

The relation `r` is not required to be an equivalence relation; the resulting quotient type's
equality extends `r` to an equivalence as a consequence of the rules for equality and quotients.
When `r` is an equivalence relation, it can be more convenient to use the higher-level type
`Quotient`.
-/
add_decl_doc Quot

/--
Places an element of a type into the quotient that equates terms according to the provided relation.

Given `v : α` and relation `r : α → α → Prop`, `Quot.mk r v : Quot r` is like `v`, except all
observations of `v`'s value must respect `r`.

`Quot.mk` is a built-in primitive:
 * `Quot` is the built-in quotient type.
 * `Quot.lift` allows the definition of functions from the quotient to some other type.
 * `Quot.sound` asserts the equality of elements related by `r`.
 * `Quot.ind` is used to write proofs about quotients by assuming that all elements are constructed
   with `Quot.mk`.
-/
add_decl_doc Quot.mk

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quot.mk`.

`Quot.rec` is analogous to the [recursor](lean-manual://section/recursors) for a structure, and can
be used when the resulting type is not necessarily a proposition.

`Quot.ind` is a built-in primitive:
 * `Quot` is the built-in quotient type.
 * `Quot.mk` places elements of the underlying type `α` into the quotient.
 * `Quot.lift` allows the definition of functions from the quotient to some other type.
 * `Quot.sound` asserts the equality of elements related by `r`.
-/
add_decl_doc Quot.ind

/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's relation.

Given a relation `r : α → α → Prop` and a quotient `Quot r`, applying a function `f : α → β`
requires a proof `a` that `f` respects `r`. In this case, `Quot.lift f a : Quot r → β` computes the
same values as `f`.

Lean's type theory includes a [definitional reduction](lean-manual://section/type-theory) from
`Quot.lift f h (Quot.mk r v)` to `f v`.

`Quot.lift` is a built-in primitive:
 * `Quot` is the built-in quotient type.
 * `Quot.mk` places elements of the underlying type `α` into the quotient.
 * `Quot.sound` asserts the equality of elements related by `r`
 * `Quot.ind` is used to write proofs about quotients by assuming that all elements are constructed
   with `Quot.mk`; it is analogous to the [recursor](lean-manual://section/recursors) for a
   structure.
-/
add_decl_doc Quot.lift
-/

end Quotient



/--
底层商类型。商类型将类型 `α` 的命题等价关系加以粗化，使得由某个关系 `r` 相关联的项在 `Quot r` 中被视为相等。

从集合论的角度来看，`Quot r` 可以看作是在 `r` 下将 `α` 划分同余类所形成的集合。
想要从 `Quot r` 构造函数，必须证明该函数保持关系 `r`：如果要定义 `f : Quot r → β`，
需要给出 `f' : α → β`，并证明对于所有 `x : α` 和 `y : α`，若 `r x y`，则 `f' x = f' y`。

`Quot` 是一个内建的原语类型：
 * `Quot.mk` 用于把基础类型 `α` 的元素放入商类型中。
 * `Quot.lift` 用于定义从商类型到其他类型的函数。
 * `Quot.sound` 用于断言由关系 `r` 关联的元素相等。
 * `Quot.ind` 支持基于假设所有元素都是由 `Quot.mk` 构造，进行关于商类型的证明。

关系 `r` 并不要求一定是等价关系；
由等价和商类型的规则可知，最终得到的商类型的等价性会将 `r` 延伸为等价关系。
当 `r` 本身就是等价关系时，推荐使用更高级的 `Quotient` 类型，这样会更便捷。

-/
def Quot := Prop

/--
将某一类型的元素放置在一个等价类中，该等价类根据给定的关系将项等同起来。

给定 `v : α` 和关系 `r : α → α → Prop`，`Quot.mk r v : Quot r` 相当于 `v`，只是对
`v` 值的所有观察都必须遵守关系 `r`。

`Quot.mk` 是内建的原语：
 * `Quot` 是内建的商类型。
 * `Quot.lift` 允许从商类型定义到其他类型的函数。
 * `Quot.sound` 断言所有被关系 `r` 关联的元素的相等性。
 * `Quot.ind` 用于写关于商类型的证明，该证明假设所有元素都由 `Quot.mk` 构造。
-/
def Quot.mk := Prop

/--

一个用于商类型（quotients）的推理原则，它允许在关于商类型的证明中假定所有的值都是由 `Quot.mk` 构造的。

`Quot.rec` 类似于结构体的 [递归子](lean-manual://section/recursors)，当结果类型不一定是命题时可以使用它。

`Quot.ind` 是一个内置的原语：
 * `Quot` 是内置的商类型。
 * `Quot.mk` 用于将底层类型 `α` 的元素放入商类型中。
 * `Quot.lift` 允许从商类型到其他类型的函数定义。
 * `Quot.sound` 断言了被关系 `r` 关联的元素的相等性。
-/
def Quot.ind := Prop

/--
将一个函数从基础类型提升到商类型上的函数时，要求该函数满足商的关系约束。

对于一个关系 `r : α → α → Prop` 和商类型 `Quot r`，如果想要应用函数 `f : α → β`，则还需提供一个证明 `a`，用于保证 `f` 满足关系 `r`。此时，`Quot.lift f a : Quot r → β` 得到的值与直接用 `f` 计算一致。

Lean 的类型理论中包含一个[定义性规约](lean-manual://section/type-theory)，将
`Quot.lift f h (Quot.mk r v)` 规约为 `f v`。

`Quot.lift` 是一个内建原语：
 * `Quot` 是内建的商类型。
 * `Quot.mk` 用于将基础类型 `α` 的元素放入商类型中。
 * `Quot.sound` 用于断言因 `r` 相关的两个元素相等。
 * `Quot.ind` 用于针对商类型进行证明，此时可以假设所有元素都是用 `Quot.mk` 构造的；它的作用类似于结构体的[递归子](lean-manual://section/recursors)。
-/
def Quot.lift := Prop


namespace Quot

/-
/--
The **quotient axiom**, which asserts the equality of elements related by the quotient's relation.

The relation `r` does not need to be an equivalence relation to use this axiom. When `r` is not an
equivalence relation, the quotient is with respect to the equivalence relation generated by `r`.

`Quot.sound` is part of the built-in primitive quotient type:
 * `Quot` is the built-in quotient type.
 * `Quot.mk` places elements of the underlying type `α` into the quotient.
 * `Quot.lift` allows the definition of functions from the quotient to some other type.
 * `Quot.ind` is used to write proofs about quotients by assuming that all elements are constructed
   with `Quot.mk`; it is analogous to the [recursor](lean-manual://section/recursors) for a
   structure.

[Quotient types](lean-manual://section/quotients) are described in more detail in the Lean Language
Reference.
-/
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
-/

/--
**商公理**，断言由商集合的关系所联系的元素是相等的。

关系 `r` 并不需要是等价关系才能使用此公理。当 `r` 不是等价关系时，商集是关于由 `r` 生成的等价关系而言的。

`Quot.sound` 是内置原语型商类型的一部分：
 * `Quot` 是内置的商类型。
 * `Quot.mk` 用于将底层类型 `α` 的元素放入商集中。
 * `Quot.lift` 允许定义从商类型到其他类型的函数。
 * `Quot.ind` 用于在证明与商类型有关的命题时进行归纳，方法是假设所有元素都是通过 `Quot.mk` 构造的；它类似于结构体的 [递归子](lean-manual://section/recursors)。

关于[商类型](lean-manual://section/quotients) 的更详细描述见 Lean 语言参考手册。
-/
def sound := Prop

/-
/--
Lifts a function from an underlying type to a function on a quotient, requiring that it respects the
quotient's relation.

Given a relation `r : α → α → Prop` and a quotient's value `q : Quot r`, applying a `f : α → β`
requires a proof `c` that `f` respects `r`. In this case, `Quot.liftOn q f h : β` evaluates
to the result of applying `f` to the underlying value in `α` from `q`.

`Quot.liftOn` is a version of the built-in primitive `Quot.lift` with its parameters re-ordered.

[Quotient types](lean-manual://section/quotients) are described in more detail in the Lean Language
Reference.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop}
  (q : Quot r) (f : α → β) (c : (a b : α) → r a b → f a = f b) : β :=
  lift f c q
-/

/--

将某个函数从底层类型提升为商类型上的函数，前提是该函数要满足商类型上的等价关系。

假设有一个关系 `r : α → α → Prop`，以及商类型中的一个值 `q : Quot r`，若要对其应用函数 `f : α → β`，则需要提供一个证明 `c`，说明 `f` 能够保持（即满足）关系 `r`。
在这种情况下，`Quot.liftOn q f h : β` 的计算结果是将 `f` 应用于 `q` 所对应的底层 `α` 类型的值后所得的结果。

`Quot.liftOn` 是内建原语 `Quot.lift` 的一个参数顺序重新排列后的版本。

关于[商类型](lean-manual://section/quotients)的更多细节，可以参考 Lean 语言参考文档的对应章节。
-/
def liftOn := Prop

/-
/--
An alternative induction principle for quotients that can be used when the target type is a
subsingleton, in which all elements are equal.

In these cases, the proof that the function respects the quotient's relation is trivial, so any
function can be lifted.

`Quot.rec` does not assume that the type is a subsingleton.
-/
@[elab_as_elim] protected abbrev recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quot.mk r a))]
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    : motive q := by
  induction q using Quot.rec
  apply f
  apply Subsingleton.elim
-/

/--
当目标类型是一个子单元时，可以使用这种选取的归纳原理来处理商类型。

在这种情况下，函数满足商类型关系的证明是不必要的，因此任何函数都可以被提升。

`Quot.rec` 并不假设目标类型为子单元。
-/
def recOnSubsingleton := Prop

/-
/--
A dependent recursion principle for `Quot`. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:
 * `Quot.lift` is useful for defining non-dependent functions.
 * `Quot.ind` is useful for proving theorems about quotients.
 * `Quot.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quot.hrecOn` uses [heterogeneous equality](lean-manual://section/HEq) instead of rewriting with
   `Quot.sound`.

`Quot.recOn` is a version of this recursor that takes the quotient parameter first.
-/
@[elab_as_elim] protected abbrev rec
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (q : Quot r) : motive q :=
  Eq.ndrecOn (Quot.liftIndepPr1 f h q) ((lift (Quot.indep f) (Quot.indepCoherent f h) q).2)
-/

/--
`Quot` 的依值递归原理。它类似于结构体的[递归子](lean-manual://section/recursors)，当结果类型不一定是命题时可以使用。

虽然这种递归子极为通用，但有时使用起来不太方便。以下这些更简单的选项可能更易于使用：
 * `Quot.lift` 适用于定义非依值的函数。
 * `Quot.ind` 适用于证明关于商类型的定理。
 * 只要目标类型是一个 `Subsingleton`（子单元），就可以使用 `Quot.recOnSubsingleton`。
 * `Quot.hrecOn` 使用了 {tech key := "heterogeneous equality"}[异质等价]，而不是用 `Quot.sound` 进行重写。

`Quot.recOn` 是该递归子的一种变体，它首先传入商类型参数。
-/
def rec := Prop

/-
/--
A dependent recursion principle for `Quot` that takes the quotient first. It is analogous to the
[recursor](lean-manual://section/recursors) for a structure, and can be used when the resulting type
is not necessarily a proposition.

While it is very general, this recursor can be tricky to use. The following simpler alternatives may
be easier to use:
 * `Quot.lift` is useful for defining non-dependent functions.
 * `Quot.ind` is useful for proving theorems about quotients.
 * `Quot.recOnSubsingleton` can be used whenever the target type is a `Subsingleton`.
 * `Quot.hrecOn` uses [heterogeneous equality](lean-manual://section/HEq) instead of rewriting with
   `Quot.sound`.

`Quot.rec` is a version of this recursor that takes the quotient parameter last.
-/
@[elab_as_elim] protected abbrev recOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    : motive q :=
 q.rec f h
-/
/--
一个针对 `Quot` 的依值递归原理，其特征是首先接收商类（quotient）作为参数。它类似于结构体的[递归子](lean-manual://section/recursors)，并且在结果类型不一定是命题时可以使用。

虽然这个递归子非常通用，但使用时可能会比较棘手。以下这些更简单的选取可能更加易用：
 * `Quot.lift` 适用于定义非依值的函数。
 * `Quot.ind` 适用于对商类进行定理证明。
 * 当目标类型是 `Subsingleton` 时，可以使用 `Quot.recOnSubsingleton`。
 * `Quot.hrecOn` 则采用了[异质等价](lean-manual://section/HEq)，而非基于 `Quot.sound` 做重写。

`Quot.rec` 是这个递归子的一个变体，只是把商类参数放在最后。
-/
def recOn := Prop

/-
/--
A dependent recursion principle for `Quot` that uses [heterogeneous
equality](lean-manual://section/HEq), analogous to a [recursor](lean-manual://section/recursors) for
a structure.

`Quot.recOn` is a version of this recursor that uses `Eq` instead of `HEq`.
-/
protected abbrev hrecOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → (p : r a b) → f a ≍ f b)
    : motive q :=
  Quot.recOn q f fun a b p => eq_of_heq (eqRec_heq_iff.mpr (c a b p))
-/
/--
`Quot` 的依值递归原理（recursion principle），它使用了 [异质等价](lean-manual://section/HEq)，类似于结构体的 [递归子](lean-manual://section/recursors)。

`Quot.recOn` 是一个类似的递归子，它使用 `Eq` 替代了 `HEq`。
-/
def hrecOn := Prop

end Quot



/-
/--
The quotient of `α` by the universal relation. The elements of `Squash α` are those of `α`, but all
of them are equal and cannot be distinguished.

`Squash α` is a `Subsingleton`: it is empty if `α` is empty, otherwise it has just one element. It
is the “universal `Subsingleton`” mapped from `α`.

`Nonempty α` also has these properties. It is a proposition, which means that its elements (i.e.
proofs) are erased from compiled code and represented by a dummy value. `Squash α` is a `Type u`,
and its representation in compiled code is identical to that of `α`.

Consequently, `Squash.lift` may extract an `α` value into any subsingleton type `β`, while
`Nonempty.rec` can only do the same when `β` is a proposition.
-/
def Squash (α : Sort u) := Quot (fun (_ _ : α) => True)
-/

/--
`α` 关于全体关系的商。`Squash α` 的元素就是 `α` 的元素，但它们在此被视为全都相等，无法区分。

`Squash α` 是一个子单元：若 `α` 为空，则 `Squash α` 也为空；否则只有一个元素。它可以看作是从 `α` 映射来的“通用子单元”。

`Nonempty α` 同样拥有这些性质。它是一个命题，也就是说它的元素（比如: 证明）在编译代码时会被抹去，只用一个占位值表示。
而 `Squash α` 是 `Type u`，且它在编译代码中的表现形式和 `α` 相同。

因此，`Squash.lift` 可以将一个 `α` 的值提取到任何子单元类型 `β` 中，而 `Nonempty.rec` 只能在 `β` 是命题时才能做同样的事情。
-/
def Squash := Prop

/-
/--
Places a value into its squash type, in which it cannot be distinguished from any other.
-/
def Squash.mk {α : Sort u} (x : α) : Squash α := Quot.mk _ x
-/
/--
将一个值放入其 squash 类型中，在该类型中它无法与其他任何值区分。
-/
def Squash.mk := Prop

/-
/--
A reasoning principle that allows proofs about squashed types to assume that all values are
constructed with `Squash.mk`.
-/
theorem Squash.ind {α : Sort u} {motive : Squash α → Prop} (h : ∀ (a : α), motive (Squash.mk a)) : ∀ (q : Squash α), motive q :=
  Quot.ind h
-/
/--
一种推理原则，它允许在证明关于 squash 类型时，假定所有的值都是通过 `Squash.mk` 构造出来的。
-/
def Squash.ind := Prop

/-
/--
Extracts a squashed value into any subsingleton type.

If `β` is a subsingleton, a function `α → β` cannot distinguish between elements of `α` and thus
automatically respects the universal relation that `Squash` quotients with.
-/
@[inline] def Squash.lift {α β} [Subsingleton β] (s : Squash α) (f : α → β) : β :=
  Quot.lift f (fun _ _ _ => Subsingleton.elim _ _) s
-/
/--
从压缩值中提取为任意子单元类型。

如果 `β` 是一个子单元类型，则函数 `α → β` 无法区分 `α` 的各个元素，因此自动满足 `Squash` 所等价化的普遍关系。
-/
def Squash.lift := Prop

end ZhDoc
