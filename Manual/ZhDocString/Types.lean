namespace ZhDoc

/-
The axiom of **propositional extensionality**. It asserts that if propositions
`a` and `b` are logically equivalent (i.e. we can prove `a` from `b` and vice versa),
then `a` and `b` are *equal*, meaning that we can replace `a` with `b` in all
contexts.

For simple expressions like `a ∧ c ∨ d → e` we can prove that because all the logical
connectives respect logical equivalence, we can replace `a` with `b` in this expression
without using `propext`. However, for higher order expressions like `P a` where
`P : Prop → Prop` is unknown, or indeed for `a = b` itself, we cannot replace `a` with `b`
without an axiom which says exactly this.

This is a relatively uncontroversial axiom, which is intuitionistically valid.
It does however block computation when using `#reduce` to reduce proofs directly
(which is not recommended), meaning that canonicity,
the property that all closed terms of type `Nat` normalize to numerals,
fails to hold when this (or any) axiom is used:
```
set_option pp.proofs true

def foo : Nat := by
  have : (True → True) ↔ True := ⟨λ _ => trivial, λ _ _ => trivial⟩
  have := propext this ▸ (2 : Nat)
  exact this

#reduce foo
-- propext { mp := fun x x => True.intro, mpr := fun x => True.intro } ▸ 2

#eval foo -- 2
```
`#eval` can evaluate it to a numeral because the compiler erases casts and
does not evaluate proofs, so `propext`, whose return type is a proposition,
can never block it.
-/

/--
**命题外延性公理**（propositional extensionality）的含义如下：它断言如果命题 `a` 和 `b` 逻辑等价（即我们能够从 `b` 推出 `a`，反之亦然），
那么 `a` 和 `b` *是相等的*，也就是说，在所有上下文中都可以用 `b` 替换掉 `a`。

对于像 `a ∧ c ∨ d → e` 这种简单表达式来说，我们可以直接证明，所有的逻辑运算符都保持逻辑等价，因此在这个表达式里，我们无需用 `propext`（命题外延）就可以把 `a` 替换为 `b`。
然而对于更高阶的表达式，如 `P a`，其中 `P : Prop → Prop` 是未知的，甚至对于 `a = b` 这种情形，都无法在没有一个明确声明此公理的前提下，把 `a` 替换为 `b`。

这是一个相对较无争议的公理，并且在直觉主义下是有效的。
然而, 当直接使用 #reduce 对证明进行化简时(这并不推荐), 这个公理会阻碍计算。
这意味着规范性(canonicity)——也就是所有类型为 Nat 的闭合项都归约成数字的性质——在使用这个(或任何)公理时将不再成立。

```lean
set_option pp.proofs true

def foo : Nat := by
  have : (True → True) ↔ True := ⟨λ _ => trivial, λ _ _ => trivial⟩
  have := propext this ▸ (2 : Nat)
  exact this

#reduce foo
-- propext { mp := fun x x => True.intro, mpr := fun x => True.intro } ▸ 2

#eval foo -- 2
```

`#eval`可以将其计算为一个数值，因为编译器会消除类型转换并且不会计算证明，`propext`的返回类型是命题, 不会阻碍`#evel`的计算。
-/
axiom propext {a b : Prop} : (a ↔ b) → a = b


/-
Lifts a proposition or type to a higher universe level.

`PLift α` wraps a proof or value of type `α`. The resulting type is in the next largest universe
after that of `α`. In particular, propositions become data.

The related type `ULift` can be used to lift a non-proposition type by any number of levels.

Examples:
 * `(False : Prop)`
 * `(PLift False : Type)`
 * `([.up (by trivial), .up (by simp), .up (by decide)] : List (PLift True))`
 * `(Nat : Type 0)`
 * `(PLift Nat : Type 1)`
structure PLift (α : Sort u) : Type u where
  /- Wraps a proof or value to increase its type's universe level by 1. -/
  up ::
  /- Extracts a wrapped proof or value from a universe-lifted proposition or type. -/
  down : α
-/

/--
将一个命题或类型提升到更高的宇宙层级。

`PLift α` 封装了一个类型为 `α` 的证明或值。结果类型属于 `α` 所在宇宙之后的下一个最大宇宙。特别地，命题会变为数据。

相关的类型 `ULift` 可用于将一个非命题类型的宇宙提升任意多个层级。

示例:
 * `(False : Prop)`
 * `(PLift False : Type)`
 * `([.up (by trivial), .up (by simp), .up (by decide)] : List (PLift True))`
 * `(Nat : Type 0)`
 * `(PLift Nat : Type 1)`
-/
structure PLift (α : Sort u) : Type u where
  /-- 将一个证明或值包装起来,以使其类型的宇宙层级增加1。 -/
  up ::
  /-- 从提升到宇宙的命题或类型中提取一个封装的证明或值。 -/
  down : α


/-
Lifts a type to a higher universe level.

`ULift α` wraps a value of type `α`. Instead of occupying the same universe as `α`, which would be
the minimal level, it takes a further level parameter and occupies their maximum. The resulting type
may occupy any universe that's at least as large as that of `α`.

The resulting universe of the lifting operator is the first parameter, and may be written explicitly
while allowing `α`'s level to be inferred.

The related type `PLift` can be used to lift a proposition or type by one level.

Examples:
 * `(Nat : Type 0)`
 * `(ULift Nat : Type 0)`
 * `(ULift Nat : Type 1)`
 * `(ULift Nat : Type 5)`
 * `(ULift.{7} (PUnit : Type 3) : Type 7)`
-- The universe variable `r` is written first so that `ULift.{r} α` can be used
-- when `s` can be inferred from the type of `α`.
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  /- Wraps a value to increase its type's universe level. -/
  /-- 包装一个值,以提升其类型的宇宙等级。 -/
  up ::
  /- Extracts a wrapped value from a universe-lifted type. -/
  /- 从一个被提升宇宙的类型中提取出被包装的值。 -/
  down : α

end ZhDoc
-/

/--
提升一个类型到更高的宇宙层级。

`ULift α` 会包装一个类型为 `α` 的值。它不再占用和 `α` 相同的宇宙层级(即最小的层级)，而是另外接受一个层级参数，并占用两者中的最大值。由此得到的类型可以存在于任何不小于 `α` 所在层级的宇宙中。

提升操作符的结果宇宙是第一个参数，可以显式写出，同时允许推断 `α` 的层级。

相关的类型 `PLift` 可以用来将命题或类型的宇宙提升一级。
-/
-- 首先写出通用变量 `r`，这样当 `α` 的类型能够推断出 `s` 时，可以使用 `ULift.{r} α`
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  /-- 包装一个值,以提升其类型的宇宙等级。 -/
  up ::
  /-- 从一个被提升宇宙的类型中提取出被包装的值。 -/
  down : α

end ZhDoc
