/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`dependsOnNoncomputable`" =>
%%%
shortTitle := "dependsOnNoncomputable"
tag := "Lean-__________________--Error-Explanations--About___--dependsOnNoncomputable"
%%%

{errorExplanationHeader lean.dependsOnNoncomputable}

此错误表示指定的定义依赖一个或多个不包含可执行代码的定义，因此必须标记为
{keyword}`noncomputable`。这类定义可以通过类型检查，但不包含可由 Lean 执行的代码。

如果你本来就打算让错误消息中命名的定义不可计算，将其标记为 {keyword}`noncomputable` 即可解决此错误。
否则，请检查它所依赖的不可计算定义：它们可能因编译失败、是 {keyword}`axiom`，或自身被标记为
{keyword}`noncomputable` 而不可计算。让定义的所有不可计算依赖变为可计算也能解决此错误。
关于不可计算定义的更多信息，请参阅 {ref "declaration-modifiers"}[修饰符]章节。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--dependsOnNoncomputable--Examples"
%%%
:::errorExample "必然不可计算的函数未正确标记"
```broken
axiom transform : Nat → Nat

def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
```output
`transform` not supported by code generator; consider marking definition as `noncomputable`
```
```fixed
axiom transform : Nat → Nat

noncomputable def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
在此例中，`transformIfZero` 依赖公理 `transform`。由于 `transform` 是公理，它不包含可执行代码；
虽然值 `transform 0` 的类型是 `Nat`，却无法计算其值。因此，`transformIfZero` 必须标记为 `noncomputable`，
因为执行它将依赖此公理。
:::

:::errorExample "不可计算依赖可以变为可计算"
```broken
noncomputable def getOrDefault [Nonempty α] : Option α → α
  | some x => x
  | none => Classical.ofNonempty

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'getOrDefault', which is 'noncomputable'
```
```fixed
def getOrDefault [Inhabited α] : Option α → α
  | some x => x
  | none => default

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
`getOrDefault` 的原始定义因使用 `Classical.choice` 而不可计算。
不过，与前一个例子不同，可以实现一个类似但可计算的 `getOrDefault` 版本（使用 `Inhabited` 类型类），
从而使 `endsOrDefault` 可计算。（{name}`Inhabited` 与 {name}`Nonempty` 的差异见
{ref "basic-classes"}[基本类]章节中关于可居住类型的文档。）
:::

:::errorExample "命名空间中的不可计算实例"
```broken
open Classical in
/--
如果 `y` 在 `f` 的像中，则返回 `y`；
否则返回 `f` 的像中的一个元素。
-/
def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'propDecidable', which is 'noncomputable'
```
```fixed
open Classical in
/--
如果 `y` 在 `f` 的像中，则返回 `y`；
否则返回 `f` 的像中的一个元素。
-/
noncomputable def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
`Classical` 命名空间包含不可计算的 `Decidable` 实例。这些实例常导致定义依赖源代码中未显式出现的
不可计算项。例如在上例中，命题的 `Decidable` 实例
`∃ x, f x = y` 使用 `Classical` 判定实例进行实例合成；因此，`fromImage` 必须标记为 `noncomputable`。
:::
