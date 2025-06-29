/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

/-
#doc (Manual) "Nested Inductive Types" =>
%%%
tag := "nested-inductive-types"
%%%
-/

#doc (Manual) "嵌套归纳类型" =>
%%%
file := "Nested Inductive Types"
tag := "nested-inductive-types"
%%%

/-
{deftech}_Nested inductive types_ are inductive types in which recursive occurrences of the type being defined are parameters to other inductive type constructors.
These recursive occurrences are “nested” underneath the other type constructors.
Nested inductive types that satisfy certain requirements can be translated into mutual inductive types; this translation demonstrates that they are sound.
Internally, the {tech}[kernel] performs this translation; if it succeeds, then the _original_ nested inductive type is accepted.
This avoids performance and usability issues that would arise from details of the translation surfacing.
-/

{deftech key := "nested inductive types"}_嵌套归纳类型_是指这些归纳类型在定义中出现了递归自身类型，并且这些递归出现作为其他归纳类型构造子的参数。
这些递归出现是“嵌套”在其他类型构造子之下的。
只要满足一定条件，嵌套归纳类型就可以转换为互递归归纳类型；这种转换说明它们是可靠的。
在内部，{tech key := "kernel"}[内核]会执行这种转换；如果转换成功，那么原有的嵌套归纳类型会被接受。
这样可以避免直接暴露内部转换细节而产生的性能和易用性问题。

/-
:::paragraph
Nested recursive occurrences must satisfy the following requirements:
* They must be nested _directly_ under an inductive type's type constructor.
  Terms that reduce to such nested occurrences are not accepted.
* Local variables such as the constructor's parameters may not occur in the arguments to the nested occurrence.
* The nested occurrences must occur strictly positively. They must occur strictly positively in the position in which they are nested, and the type constructor in which they are nested must itself occur in a strictly positive position.
* Constructor parameters whose types include nested occurrences may not be used in ways that rely on the specific choice of outer type constructor. The translated version will not be usable in those contexts.
* Nested occurrences may not be used as parameters to the outer type constructor that occur in the types of the outer type's indices.
:::
-/

:::paragraph
嵌套递归出现必须满足以下要求：
* 它们必须直接嵌套在某个归纳类型的类型构造子之下。对于通过规约才变成嵌套出现的情况是不被接受的。
* 像构造子的参数这样的本地变量，不允许出现在嵌套递归出现的参数中。
* 嵌套递归出现必须处于严格正向位置。
:::

/-
:::example "Nested Inductive Types"
Instead of using two constructors, the natural numbers can be defined using {name}`Option`:
```lean
inductive ONat : Type where
  | mk (pred : Option ONat)
```

Arbitrarily-branching trees, also known as _rose trees_, are nested inductive types:
```lean
inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : List (RTree α))
```
:::
-/

:::example "Nested Inductive Types"
自然数除了用两个构造子定义，也可以通过 {name}`Option` 来定义：
```lean
inductive ONat : Type where
  | mk (pred : Option ONat)
```

可以有任意分支数的树，也叫 _rose trees_，它就是一种嵌套归纳类型：
```lean
inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : List (RTree α))
```
:::

/-
:::::example "Invalid Nested Inductive Types"

This declaration of arbitrarily-branching rose trees declares an alias for {name}`List`, rather than using {name}`List` directly:
```lean (error := true) (name := viaAlias)
abbrev Children := List

inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : Children (RTree α))
```
```leanOutput viaAlias
(kernel) arg #3 of 'RTree.node' contains a non valid occurrence of the datatypes being declared
```

::::paragraph
:::leanSection
```lean (show := false)
variable {n : Nat}
```
This declaration of arbitrarily-branching rose trees tracks the depth of the tree using an index.
The constructor `DRTree.node` has an {tech}[automatic implicit parameter] {lean}`n` that represents the depths of all sub-trees.
However, local variables such as constructor parameters are not permitted as arguments to nested occurrences:
:::
```lean (error := true) (name := localVar)
inductive DRTree (α : Type u) : Nat → Type u where
  | empty : DRTree α 0
  | node (val : α) (children : List (DRTree α n)) : DRTree α (n + 1)
```
```leanOutput localVar
(kernel) invalid nested inductive datatype 'List', nested inductive datatypes parameters cannot contain local variables.
```
::::

This declaration includes a non-strictly-positive occurrence of the inductive type, nested under an {name}`Option`:
```lean (error := true) (name := nonPos)
inductive WithCheck where
  | done
  | check (f : Option WithCheck → Bool)
```
```leanOutput nonPos
(kernel) arg #1 of 'WithCheck.check' has a non positive occurrence of the datatypes being declared
```

:::paragraph
This rose tree has a branching factor that's limited by its parameter:
```lean (error := true) (name := brtree)
inductive BRTree (branches : Nat) (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    children.length < branches →
    BRTree branches α
```
Only nested inductive types that can be translated to mutual inductive types are allowed.
However, translating this type would require a translation of {name}`List.length` to the translated types, but function definitions may not occur in mutual blocks with inductive types.
The resulting error message shows that the function was not translated, but was applied to a term of the translated type:
```leanOutput brtree
(kernel) application type mismatch
  List.length children
argument has type
  @_nested.List_1 branches α
but function has type
  List (@BRTree branches α) → Nat
```
It is acceptable to use the parameter with the nested occurrence with fully polymorphic functions, such as {name}`id`:
```lean (name := nondep)
inductive RTree'' (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    id children = children →
    BRTree branches α
```
In this case, the function applies equally well to the translated version as it does to the original.
:::

:::paragraph
A _palindrome_ is a list that is the same when reversed:
```lean
inductive Palindrome (α : Type) : List α → Prop where
  | nil : Palindrome α []
  | single : Palindrome α [x]
  | cons (x : α) (p : Palindrome α xs) : Palindrome α (x :: xs ++ [x])
```
In this predicate, the list is an index whose type depends on the parameter, which is explicit for clarity.
This means it cannot be used

:::
:::::
-/

:::::example "非法的嵌套归纳类型"

这个 rose trees 的定义用了一个 {name}`List` 的别名，而不是直接使用 {name}`List`：
```lean (error := true) (name := viaAlias)
abbrev Children := List

inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : Children (RTree α))
```
```leanOutput viaAlias
(kernel) arg #3 of 'RTree.node' contains a non valid occurrence of the datatypes being declared
```

::::paragraph
:::leanSection
```lean (show := false)
variable {n : Nat}
```

这种定义方式用于通过一个索引追踪树的深度。构造子 `DRTree.node` 有一个 {tech key := "automatic implicit parameter"}[自动隐式参数] {lean}`n`，代表所有子树的深度。
然而，像构造子参数这样本地变量，不允许作为嵌套递归出现的参数：

:::
```lean (error := true) (name := localVar)
inductive DRTree (α : Type u) : Nat → Type u where
  | empty : DRTree α 0
  | node (val : α) (children : List (DRTree α n)) : DRTree α (n + 1)
```
```leanOutput localVar
(kernel) invalid nested inductive datatype 'List', nested inductive datatypes parameters cannot contain local variables.
```
::::

下面这个定义在 {name}`Option` 下嵌入了非严格正向的归纳类型出现：
```lean (error := true) (name := nonPos)
inductive WithCheck where
  | done
  | check (f : Option WithCheck → Bool)
```
```leanOutput nonPos
(kernel) arg #1 of 'WithCheck.check' has a non positive occurrence of the datatypes being declared
```

:::::

/-
The translation from nested inductive types to mutual inductive types proceeds as follows:

: Nested occurrences become inductive types

  Nested occurrences of the inductive type are translated into new inductive types in the same mutual group, which replace the original nested occurrences.
  These new inductive types have the same constructors as the outer inductive type, except the original parameters are instantiated by the translated version of the type.
  The original inductive type becomes an alias for the version in which the nested occurrences have been rewritten.
  This process is repeated if the resulting type is also a nested inductive type (e.g. a type nested under {name}`Array` becomes a type nested under {name}`List`, because {name}`Array`'s constructor takes a {name}`List`).

: Conversions to and from the nested types

  Conversions between the outer inductive type applied to the new alias and the generated auxiliary types are generated.
  These conversions are then proved to be mutual inverses.

: Constructor reconstruction

  Each constructor of the original type is defined as a function that returns the constructor of the translated type, after applying the appropriate conversions.

: Recursor reconstruction

  The recursor for the nested inductive type is constructed from the recursor for the translated type.
  In the translation, the motives for the nested occurrences are composed with the conversion functions and the {tech}[minor premises] use them as needed.
  The proofs that the conversion functions are mutually inverse are needed because the encoded constructors convert in one direction, but end up applied to the result of the conversion in the other direction.
-/

嵌套归纳类型转换为互递归归纳类型的流程如下：

: 嵌套出现变为新的归纳类型

  对嵌套出现的归纳类型会翻译为同一互递归组里的新归纳类型，替换原先的嵌套出现。
  这些新归纳类型拥有与外层归纳类型一样的构造子，只是在原参数位置用刚刚翻译后的新类型替代。
  原始归纳类型本身定义为重写后类型的别名。如果新类型依然是嵌套归纳类型（比如在 {name}`Array` 下嵌套，因其构造子要用 {name}`List`，就需要再次翻译到 {name}`List`），则重复此流程。

: 构造嵌套类型之间的转换

  在外层归纳类型和新别名，及辅助类型之间，分别自动生成互相转换的函数，这些转换将被证明为互逆关系。

: 构造子重建

  原始类型的每个构造子定义为一个函数，返回翻译后类型的相应构造子，调用时会自动应用必要的转换。

: 递归子重建

  嵌套归纳类型的递归子则是结合翻译后类型的递归子而实现的。
  在这一步，嵌套出现的目标会先套上转换函数，而{tech key := "minor premises"}[次要前提]会以它们作为参数。
  构造子之间的互逆性证明是必要的，因为封装后的构造子是单方向转换，但在组合递归结构时需要转换后的结果。

/-
::::example "Translating Nested Inductive Types"
This nested inductive type represents the natural numbers:
```lean (keep := false)
inductive ONat where
  | mk (pred : Option ONat) : ONat

#check ONat.rec
```

The first step in the internal translation is to replace the nested occurrences with auxiliary inductive types that “inline” the resulting type.
In this case, the nested occurrence is under {name}`Option`; thus, the auxiliary type has the constructors of {name}`Option`, with {name}`ONat'` substituted for the type parameter:
```lean
mutual
inductive ONat' where
  | mk (pred : OptONat) : ONat'

inductive OptONat where
  | none
  | some : ONat' → OptONat
end
```

{lean}`ONat'` is the encoding of {lean}`ONat`:
```lean
def ONat := ONat'
```

The next step is to define conversion functions that translate the original nested type to and from the auxiliary type:
```lean
def OptONat.ofOption : Option ONat → OptONat
  | Option.none => OptONat.none
  | Option.some o => OptONat.some o
def OptONat.toOption : OptONat → Option ONat
  | OptONat.none => Option.none
  | OptONat.some o => Option.some o
```

These conversion functions are mutually inverse:
```lean
def OptONat.to_of_eq_id o :
    OptONat.toOption (ofOption o) = o := by
  cases o <;> rfl
def OptONat.of_to_eq_id o :
    OptONat.ofOption (OptONat.toOption o) = o := by
  cases o <;> rfl
```

The original constructor is translated to an application of the translation's corresponding constructor, with the appropriate conversion applied for the nested occurrence:
```lean
def ONat.mk (pred : Option ONat) : ONat :=
  ONat'.mk (.ofOption pred)
```

Finally, the original type's recursor can be translated.
The translated recursor uses the translated type's recursor.
The original nested occurrences are translated using the conversions, and the proofs that the conversions are mutually inverse are used to rewrite types as needed.
```lean
noncomputable def ONat.rec
    {motive1 : ONat → Sort u}
    {motive2 : Option ONat → Sort u}
    (h1 :
      (pred : Option ONat) → motive2 pred →
      motive1 (ONat.mk pred))
    (h2 : motive2 none)
    (h3 : (o : ONat) → motive1 o → motive2 (some o)) :
    (t : ONat) → motive1 t :=
  @ONat'.rec motive1 (motive2 ∘ OptONat.toOption)
    (fun pred ih =>
      OptONat.of_to_eq_id pred ▸ h1 pred.toOption ih)
    h2
    h3
```
::::
-/


::::example "翻译嵌套归纳类型"
下面是一个用嵌套归纳类型定义的自然数类型：
```lean (keep := false)
inductive ONat where
  | mk (pred : Option ONat) : ONat

#check ONat.rec
```

内部翻译的第一步，是用辅助归纳类型“内联”嵌套出现的位置。
这里嵌套发生在 {name}`Option` 之下，所以辅助类型拥有 {name}`Option` 的构造子，但其类型参数用 {name}`ONat'` 替代：

```lean
mutual
inductive ONat' where
  | mk (pred : OptONat) : ONat'

inductive OptONat where
  | none
  | some : ONat' → OptONat
end
```

{lean}`ONat'` 就是 {lean}`ONat` 经过编码后的版本：
```lean
def ONat := ONat'
```

下一步是定义转换函数，用于在原始嵌套类型和辅助类型之间相互转换：
```lean
def OptONat.ofOption : Option ONat → OptONat
  | Option.none => OptONat.none
  | Option.some o => OptONat.some o
def OptONat.toOption : OptONat → Option ONat
  | OptONat.none => Option.none
  | OptONat.some o => Option.some o
```

这些相互转换的函数是互逆的：
```lean
def OptONat.to_of_eq_id o :
    OptONat.toOption (ofOption o) = o := by
  cases o <;> rfl
def OptONat.of_to_eq_id o :
    OptONat.ofOption (OptONat.toOption o) = o := by
  cases o <;> rfl
```

原始的构造子被翻译成对翻译后类型的构造子的调用，同时会对嵌套递归部分做适当类型转换：
```lean
def ONat.mk (pred : Option ONat) : ONat :=
  ONat'.mk (.ofOption pred)
```

最后，原类型的递归子也可以翻译。
翻译后的递归子会通过翻译后类型的递归子来实现。
原本嵌套递归位置会采用相应的转换函数，并且互逆性的证明可以在需要时重写类型：
```lean
noncomputable def ONat.rec
    {motive1 : ONat → Sort u}
    {motive2 : Option ONat → Sort u}
    (h1 :
      (pred : Option ONat) → motive2 pred →
      motive1 (ONat.mk pred))
    (h2 : motive2 none)
    (h3 : (o : ONat) → motive1 o → motive2 (some o)) :
    (t : ONat) → motive1 t :=
  @ONat'.rec motive1 (motive2 ∘ OptONat.toOption)
    (fun pred ih =>
      OptONat.of_to_eq_id pred ▸ h1 pred.toOption ih)
    h2
    h3
```
::::
