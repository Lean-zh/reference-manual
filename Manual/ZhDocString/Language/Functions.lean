namespace ZhDoc

/-
**Function extensionality.** If two functions return equal results for all possible arguments, then
they are equal.

It is called “extensionality” because it provides a way to prove two objects equal based on the
properties of the underlying mathematical functions, rather than based on the syntax used to denote
them. Function extensionality is a theorem that can be [proved using quotient
types](lean-manual://section/quotient-funext).
-/
/--
**函数外延性** :如果两个函数对所有可能的参数都返回相等的结果，那么它们就是相等的。

它被称为“外延性”，因为它提供了一种基于基础数学函数的性质，而不是基于用于表示它们的语法，来证明两个对象相等的方法。函数外延性是一个可以[用商类型证明](lean-manual://section/quotient-funext)的定理。
-/
theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g := by
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
  let extfunApp (f : Quot eqv) (x : α) : β x :=
    Quot.liftOn f
      (fun (f : ∀ (x : α), β x) => f x)
      (fun _ _ h => h x)
  show extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
  exact congrArg extfunApp (Quot.sound h)


/-
Function composition, usually written with the infix operator `∘`. A new function is created from
two existing functions, where one function's output is used as input to the other.

Examples:
 * `Function.comp List.reverse (List.drop 2) [3, 2, 4, 1] = [1, 4]`
 * `(List.reverse ∘ List.drop 2) [3, 2, 4, 1] = [1, 4]`
-/
/--
函数组合，通常用中缀运算符`∘`表示。通过组合两个已存在的函数创建一个新函数，其中一个函数的输出用作另一个函数的输入。

例子:
 * `Function.comp List.reverse (List.drop 2) [3, 2, 4, 1] = [1, 4]`
 * `(List.reverse ∘ List.drop 2) [3, 2, 4, 1] = [1, 4]`
-/
@[inline] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

/-
The constant function that ignores its argument.

If `a : α`, then `Function.const β a : β → α` is the “constant function with value `a`”. For all
arguments `b : β`, `Function.const β a b = a`.

Examples:
 * `Function.const Bool 10 true = 10`
 * `Function.const Bool 10 false = 10`
 * `Function.const String 10 "any string" = 10`
-/
/--
常函数会忽略其参数。

如果a : α，那么Function.const β a : β → α就是“值为a的常函数”。对所有参数b : β，Function.const β a b = a。

示例:
* Function.const Bool 10 true = 10
* Function.const Bool 10 false = 10
* Function.const String 10 "any string" = 10
-/
@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun _ => a


/-
Transforms a function from pairs into an equivalent two-parameter function.

Examples:
 * `Function.curry (fun (x, y) => x + y) 3 5 = 8`
 * `Function.curry Prod.swap 3 "five" = ("five", 3)`
-/
/--
将一个接受一对参数的函数转换为等效的双参数函数。

例如:
* Function.curry (fun (x, y) => x + y) 3 5 = 8
* Function.curry Prod.swap 3 "five" = ("five", 3)
-/
@[inline, expose]
def Function.curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)

/-
Transforms a two-parameter function into an equivalent function from pairs.

Examples:
 * `Function.uncurry List.drop (1, ["a", "b", "c"]) = ["b", "c"]`
 * `[("orange", 2), ("android", 3) ].map (Function.uncurry String.take) = ["or", "and"]`
-/
/--
将一个带有两个参数的函数转换为一个接受参数对的等价函数。

例如:
 * `Function.uncurry List.drop (1, ["a", "b", "c"]) = ["b", "c"]`
 * `[("orange", 2), ("android", 3) ].map (Function.uncurry String.take) = ["or", "and"]`
-/
@[inline, expose]
def Function.uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2

end ZhDoc
