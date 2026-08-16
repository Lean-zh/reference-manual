/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inferBinderTypeFailed`" =>
%%%
shortTitle := "inferBinderTypeFailed"
tag := "Lean-__________________--Error-Explanations--About___--inferBinderTypeFailed"
%%%

{errorExplanationHeader lean.inferBinderTypeFailed}

当声明头或局部绑定中的绑定项类型未完全指定且 Lean 无法推断时，会产生此错误。通常可以通过提供更多
信息来帮助 Lean 确定绑定项类型来解决：显式标注其类型，或在使用处提供额外类型信息。当绑定项出现在
声明头中时，此错误通常伴随
{ref "lean.inferDefTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferDefTypeFailed`].

注意，如果声明带有显式结果类型（即使该类型包含空洞），Lean 也不会使用定义体的信息来推断参数类型。
因此，原本无需结果类型注解即可推断的参数，可能必须显式指定其类型；详见下面“因结果类型注解而无法推断
绑定项类型”的示例。在 {keyword}`theorem` 声明中，定理体从不用于推断绑定项类型，因此无法从定理类型
其余部分推断类型的绑定项必须包含类型注解。

当原本用作声明名称的标识符被误写在绑定项位置时，也可能产生此错误。此时，错误标识符会被视为
类型未指定的绑定项，从而导致类型推断失败。这常见于尝试使用不支持该形式的语法，同时定义多个相同类型
的常量。具体包括：
* 在 {keyword}`example` 关键字后写标识符，试图为示例命名；
* 在 {keyword}`def`、{keyword}`opaque` 或其他声明关键字后依次列出多个标识符，试图定义具有相同类型
  （以及适用时相同值）的多个常量；
* 在结构声明同一行依次列出名称，试图定义多个相同类型的结构字段；以及
* 省略归纳构造器名称之间的竖线。

下面的示例展示了前三种情况。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--inferBinderTypeFailed--Examples"
%%%
:::errorExample "绑定项类型需要新的类型变量"
```broken
def identity x :=
  x
```
```output
Failed to infer type of binder `x`
```
```fixed
def identity (x : α) :=
  x
```
上面的代码中，`x` 的类型没有约束；如本例所示，Lean 不会自动为这类绑定项生成新的类型变量。
因此必须把类型 `α` 显式指定为 `x` 的类型。注意，如果启用了自动插入隐式参数（默认如此），则无需为 `α` 本身提供
绑定项；Lean 会自动为该参数插入隐式绑定项。
:::

:::errorExample "因结果类型注解而无法推断绑定项类型"
```broken
def plusTwo x : Nat :=
  x + 2
```
```output
Failed to infer type of binder `x`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
```fixed
def plusTwo (x : Nat) : Nat :=
  x + 2
```
尽管在定义体中可以推断 `x` 的类型为 `Nat`，但精译 `plusTwo` 的类型时无法使用这一信息，因为定义的结果类型（`Nat`）已显式指定。
仅根据头部信息无法确定 `x` 的类型，于是产生所示错误。因此必须在
其绑定项中包含 `x` 的类型。
:::

:::errorExample "尝试为 example 声明命名"
```broken
example trivial_proof : True :=
  trivial
```
```output
Failed to infer type of binder `trivial_proof`

Note: Examples do not have names. The identifier `trivial_proof` is being interpreted as a parameter `(trivial_proof : _)`.
```
```fixed
example : True :=
  trivial
```
这段代码无效，因为它试图为 `example` 声明命名。示例不能命名；在其他声明形式中应出现名称的位置写入
标识符时，该标识符反而会被精译为绑定项，而其类型无法推断。如果声明必须命名，应使用支持命名的声明形式，
例如 `def` 或 `theorem`。
:::

:::errorExample "尝试一次定义多个不透明常量"
```broken
opaque m n : Nat
```
```output
Failed to infer type of binder `n`

Note: Multiple constants cannot be declared in a single declaration. The identifier `n` is being interpreted as a parameter `(n : _)`.
```
```fixed
opaque m : Nat
opaque n : Nat
```
此示例错误地尝试用一个 `opaque` 声明定义多个常量。这类声明只能定义一个常量：不能在 `opaque` 或
`def` 后列出多个标识符，使它们都具有相同类型（或值）。该声明反而会被精译为定义一个常量（例如上面的
`m`），后续标识符（`n`）成为其参数，而这些参数的类型未指定且无法推断。要定义多个全局常量，必须
分别声明每个常量。
:::

:::errorExample "尝试在同一行定义多个结构字段"
```broken
structure Person where
  givenName familyName : String
  age : Nat
```
```output
Failed to infer type of binder `familyName`
```
```fixed "修复（分行）"
structure Person where
  givenName : String
  familyName : String
  age : Nat
```
```fixed "修复（加括号）"
structure Person where
  (givenName familyName : String)
  age : Nat
```
此示例错误地尝试在同一行连续列出多个字段（`givenName` 和 `familyName`）来定义相同类型的结构字段。
Lean 会将其解释为定义单个字段 `givenName`，其参数是类型未指定的绑定项 `familyName`。可以将每个字段
分别列在单独一行，或将指定多个字段名称的行括在括号中，以实现预期行为（结构声明的更多详情请参阅
{ref "inductive-types"}[归纳类型]章节）。
:::
