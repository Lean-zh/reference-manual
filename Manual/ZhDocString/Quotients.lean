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


end Quotient

end ZhDoc
