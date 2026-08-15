/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.Monads.Syntax
import Manual.Monads.Zoo
import Manual.Monads.Lift
import Manual.Monads.API
import Manual.Monads.Laws

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option maxRecDepth 1024

#doc (Manual) "函子、单子与 `do` 记法" =>

%%%
tag := "monads-and-do"
%%%

类型类 {name}`Functor`、{name}`Applicative` 和 {name}`Monad` 为函数式编程提供了基本工具。{margin}[关于如何使用这些抽象进行编程的介绍，参见 [_Lean 函数式编程_](https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad.html)。]
它们的灵感来自范畴论中的函子和单子概念，但编程中使用的版本限制更多。
Lean 标准库中的类型类所表示的是用于编程的概念，而非一般的数学定义。

{deftech (key := "Functor")}[函子]的实例允许在某种多态上下文中一致地应用操作。
例如，可以通过应用函数来变换列表中的每个元素，也可以安排将纯函数应用于现有 {lean}`IO` 动作的结果，从而创建新的 {lean}`IO` 动作。
{deftech (key := "Monad")}[单子]的实例允许编码带有数据依赖的副作用；例如，用元组模拟可变状态、用和类型模拟异常，以及用 {lean}`IO` 表示真实的副作用。
{deftech (key := "Applicative functors")}[应用函子]介于二者之间：它们与单子一样，允许把通过效应计算出的函数应用于同样通过效应计算出的实参；但不允许顺序数据依赖，即一个效应的输出成为另一个效应操作的输入。

另外几个类型类 {name}`Pure`、{name}`Bind`、{name}`SeqLeft`、{name}`SeqRight` 和 {name}`Seq` 分别抽取了 {name}`Applicative` 与 {name}`Monad` 中的单项操作，使这些操作可以重载，并用于不一定是应用函子或单子的类型。
类型类 {name}`Alternative` 描述还具有某种失败与恢复概念的应用函子。


{docstring Functor}

{docstring Pure}

{docstring Seq}

{docstring SeqLeft}

{docstring SeqRight}

{docstring Applicative}


:::::keepEnv

```lean -show
section
variable {α : Type u} {β : Type u}
```

::::example "以定长列表作为应用函子"

结构 {name}`LenList` 将列表与其长度为所需值的证明配对。
因此，它的 `zipWith` 运算无需为输入长度不同时提供后备方案。

```lean
structure LenList (length : Nat) (α : Type u) where
  list : List α
  lengthOk : list.length = length

def LenList.head (xs : LenList (n + 1) α) : α :=
  xs.list.head <| by
    intro h
    cases xs
    simp_all
    subst_eqs

def LenList.tail (xs : LenList (n + 1) α) : LenList n α :=
  match xs with
  | ⟨_ :: xs', _⟩ => ⟨xs', by simp_all⟩

def LenList.map (f : α → β) (xs : LenList n α) : LenList n β where
  list := xs.list.map f
  lengthOk := by
    cases xs
    simp [List.length_map, *]

def LenList.zipWith (f : α → β → γ)
    (xs : LenList n α) (ys : LenList n β) :
    LenList n γ where
  list := xs.list.zipWith f ys.list
  lengthOk := by
    cases xs; cases ys
    simp [List.length_zipWith, *]
```

这个行为良好的 {name}`Applicative` 实例逐元素地将函数应用于实参。
由于 {name}`Applicative` 扩展了 {name}`Functor`，无需另外定义 {name}`Functor` 实例；{name Functor.map}`map` 可以作为 {name}`Applicative` 实例的一部分来定义。

```lean
instance : Applicative (LenList n) where
  map := LenList.map
  pure x := {
    list := List.replicate n x
    lengthOk := List.length_replicate
  }
  seq {α β} fs xs := fs.zipWith (· ·) (xs ())
```

这个行为良好的 {name}`Monad` 实例取函数应用结果的对角线：

```lean
@[simp]
theorem LenList.list_length_eq (xs : LenList n α) :
    xs.list.length = n := by
  cases xs
  simp [*]

def LenList.diagonal (square : LenList n (LenList n α)) : LenList n α :=
  match n with
  | 0 => ⟨[], rfl⟩
  | n' + 1 => {
    list :=
      square.head.head :: (square.tail.map (·.tail)).diagonal.list
    lengthOk := by simp
  }
```
::::

```lean -show
end
```
:::::


{docstring Alternative}

{docstring Bind}

{docstring Monad}

{include 0 Manual.Monads.Laws}

{include 0 Manual.Monads.Lift}

{include 0 Manual.Monads.Syntax}

{include 0 Manual.Monads.API}

{include 0 Manual.Monads.Zoo}
