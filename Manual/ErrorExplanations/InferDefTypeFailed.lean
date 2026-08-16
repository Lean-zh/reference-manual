/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inferDefTypeFailed`" =>
%%%
shortTitle := "inferDefTypeFailed"
%%%

{errorExplanationHeader lean.inferDefTypeFailed}

当定义的类型未完全指定且 Lean 无法从可用信息推断其类型时，会产生此错误。如果定义有参数，此错误仅指
冒号后的结果类型（错误
{ref "lean.inferBinderTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferBinderTypeFailed`]
表示无法推断参数类型）。

要解决此错误，请在定义中提供额外类型信息。最直接的方式是在定义头部冒号后提供显式结果类型。
或者，如果未提供显式结果类型，可以向定义体添加更多类型信息（例如指定隐式类型参数，或为 `let`
绑定项提供显式类型），从而让 Lean 推断定义类型。请查找与此错误同时出现的类型推断或隐式参数实例合成
错误，以确定可能造成此错误的歧义。

注意，当提供显式结果类型时，即使该类型包含空洞，Lean 也不会使用定义体的信息来推断定义或其参数的类型。
因此，添加显式结果类型也可能要求为原本可推断类型的参数添加类型注解。此外，`theorem` 声明始终必须提供
显式类型：`theorem` 语法要求类型注解，精译器绝不会尝试使用定理体推断所证明的命题。

# 示例

:::errorExample "无法推断隐式参数"
```broken
def emptyNats :=
  []
```
```output
Failed to infer type of definition `emptyNats`
```
```fixed "type annotation"
def emptyNats : List Nat :=
  []
```
```fixed "implicit argument"
def emptyNats :=
  List.nil (α := Nat)
```

这里 Lean 无法推断 `List` 类型构造器的参数 `α` 的值，进而无法推断定义类型。可以有两种修复方式：
指定定义的期望类型，让 Lean 推断 `List.nil` 构造器的适当隐式参数；或者在函数体中显式写出该隐式参数，
为 Lean 推断定义类型提供足够信息。
:::

:::errorExample "因未知参数类型而无法推断定义类型"
```broken
def identity x :=
  x
```
```output
Failed to infer type of definition `identity`
```
```fixed
def identity (x : α) :=
  x
```

在此例中，`identity` 的类型由无法推断的 `x` 类型决定。因此，所示错误和
{ref "lean.inferBinderTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferBinderTypeFailed`]
都会出现（该例的更多讨论见该说明）。解决后一个错误（显式指定 `x` 的类型）即可为 Lean 推断定义类型
提供足够信息。
:::
