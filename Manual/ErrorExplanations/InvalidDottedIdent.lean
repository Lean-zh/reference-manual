/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`invalidDottedIdent`" =>
%%%
shortTitle := "invalidDottedIdent"
tag := "Lean-__________________--Error-Explanations--About___--invalidDottedIdent"
%%%

{errorExplanationHeader lean.invalidDottedIdent}

此错误表示在无效或不受支持的上下文中使用了点标识符记法。
点标识符记法允许省略标识符的命名空间，前提是 Lean 能根据类型信息推断它。关于该记法的详情请参阅
{ref "identifiers-and-resolution"}[标识符]章节。

该记法只能用于 Lean 能够推断其类型的项。如果类型信息不足，就会产生此错误。推断出的类型不能是类型
宇宙（例如 {lean}`Prop` 或 {lean}`Type`），因为这些类型不支持点标识符记法。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--invalidDottedIdent--Examples"
%%%
:::errorExample "类型信息不足"
```broken
def reverseDuplicate (xs : List α) :=
  .reverse (xs ++ xs)
```
```output
Invalid dotted identifier notation: The expected type of `.reverse` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Array.reverse`
  [apply] `BitVec.reverse`
  [apply] `List.reverse`
  [apply] `Vector.reverse`
  [apply] `List.IsInfix.reverse`
  [apply] `List.IsPrefix.reverse`
  [apply] `List.IsSuffix.reverse`
  [apply] `List.Sublist.reverse`
  [apply] `Lean.Grind.AC.Seq.reverse`
  [apply] `Std.DTreeMap.Internal.Impl.reverse`
  [apply] `Std.Tactic.BVDecide.BVUnOp.reverse`
  [apply] `Std.DTreeMap.Internal.Impl.Ordered.reverse`
```
```fixed
def reverseDuplicate (xs : List α) : List α :=
  .reverse (xs ++ xs)
```

```lean -show
variable (α : Type) (xs : List α)
```

由于未指定 `reverseDuplicate` 的返回类型，无法确定 `.reverse` 的期望类型。Lean 不会使用参数
{lean}`xs ++ xs` 的类型推断省略的命名空间。添加返回类型 {lean}`List α` 后，Lean 就能推断 `.reverse`
的类型，进而推断解析该标识符所需的命名空间（{name}`List`）。

注意，这意味着改变 `reverseDuplicate` 的返回类型会改变 `.reverse` 的解析方式：如果返回类型是 `T`，
Lean 会尝试将 `.reverse` 解析为返回类型为 `T` 的函数 `T.reverse`，即使 `T.reverse` 不接受类型为
`List α` 的参数。
:::

:::errorExample "应为类型宇宙处使用点标识符"

```broken
example (n : Nat) :=
  match n > 42 with
  | .true  => n - 1
  | .false => n + 1
```
```output
Invalid dotted identifier notation: Not supported on type universe
  Prop
```
```fixed
example (n : Nat) :=
  match decide (n > 42) with
  | .true  => n - 1
  | .false => n + 1
```

```lean -show
variable (n : Nat)
```

命题 {lean}`n > 42` 的类型是 {lean}`Prop`；由于它是类型宇宙，不支持点标识符记法。如本例所示，在这种
上下文中使用该记法几乎总是错误。此例原本想让 `.true` 和 `.false` 表示布尔值，而非命题；不过，
{keywordOf Lean.Parser.Term.match}`match` 表达式不会自动对可判定命题执行这种强制转换。显式添加
{name}`decide` 会使判别式成为 {name}`Bool`，从而使点标识符解析成功。
:::
