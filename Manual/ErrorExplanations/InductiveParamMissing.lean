/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductiveParamMissing`" =>
%%%
shortTitle := "inductiveParamMissing"
tag := "Lean-__________________--Error-Explanations--About___--inductiveParamMissing"
%%%

{errorExplanationHeader lean.inductiveParamMissing}

当归纳类型构造器在其某个构造器的类型中被部分应用、因而省略了一个或多个参数时，会产生此错误。
精译器要求在定义中引用归纳类型的所有位置（包括其构造器的类型）都指定该归纳类型的全部参数。

如果需要允许类型构造器在不指定某个类型参数的情况下被部分应用，就必须将该参数转换为索引。
关于索引和参数差异的进一步解释，请参阅{ref "inductive-types"}[归纳类型]章节。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--inductiveParamMissing--Examples"
%%%
:::errorExample "高阶谓词参数中省略参数"
```broken
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All (P : α → Prop) (t : RoseTree α) : Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```

```output
Missing parameter(s) in occurrence of inductive type: In the expression
  List.All (All P) t.children
found
  All P
but expected all parameters to be specified:
  All P t

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
```

```fixed
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All (P : α → Prop) : RoseTree α → Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```

由于 `RoseTree.All` 类型构造器必须在 `List.All` 的参数中部分应用，未指定的参数（`t`）不能是
`RoseTree.All` 谓词的参数。将它设为 `RoseTree.All` 头部冒号右侧的索引，就允许这种部分应用成功。
:::
