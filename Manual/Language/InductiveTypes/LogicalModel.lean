/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

/-
#doc (Manual) "Logical Model" =>
%%%
tag := "inductive-types-logical-model"
%%%
-/

#doc (Manual) "逻辑模型" =>
%%%
file := "Logical Model"
tag := "inductive-types-logical-model"
%%%


/-
# Recursors
%%%
tag := "recursors"
%%%
-/

# 递归子
%%%
file := "Recursors"
tag := "recursors"
%%%

/-
Every inductive type is equipped with a {tech}[recursor].
The recursor is completely determined by the signatures of the type constructor and the constructors.
Recursors have function types, but they are primitive and are not definable using `fun`.
-/

每一个归纳类型都拥有一个{tech key := "recursor"}[递归子]。
递归子的定义完全由类型构造子和数据构造子的类型签名所决定。
递归子的类型是函数类型，但它们是原语级别的，不能用 `fun` 来定义。

/-
## Recursor Types
%%%
tag := "recursor-types"
%%%
-/

## 递归子类型
%%%
tag := "recursor-types"
%%%

/-
:::paragraph
The recursor takes the following parameters:
: The inductive type's {tech}[parameters]

  Because parameters are consistent, they can be abstracted over the entire recursor

: The {deftech}_motive_

  The motive determines the type of an application of the recursor. The motive is a function whose arguments are the type's indices and an instance of the type with these indices instantiated. The specific universe for the type that the motive determines depends on the inductive type's universe and the specific constructors—see the section on {ref "subsingleton-elimination"}[{tech}[subsingleton] elimination] for details.

: A {deftech}_minor premise_ for each constructor

  For each constructor, the recursor expects a function that satisfies the motive for an arbitrary application of the constructor.
  Each minor premise abstracts over all of the constructor's parameters.
  If the constructor's parameter's type is the inductive type itself, then the case additionally takes a parameter whose type is the motive applied to that parameter's value—this will receive the result of recursively processing the recursive parameter.

: The {deftech}_major premise_, or target

  Finally, the recursor takes an instance of the type as an argument, along with any index values.

The result type of the recursor is the motive applied to these indices and the target.
:::
-/

:::paragraph
递归子接收以下参数：
: 归纳类型的{tech key := "parameters"}[参数]

  由于参数是一致的，所以它们可以对整个递归子抽象

: {deftech key := "motive"}_动机_(motive)

  动机决定了递归子的应用结果的类型。动机是一个函数，其参数是类型的指标及其具体实例。动机决定的类型所处的具体宇宙由归纳类型的宇宙层级和具体的数据构造子决定——详见{ref "subsingleton-elimination"}[{tech key := "subsingleton"}[子单元] 消去]部分。

: 每个构造子的{deftech key := "minor premise"}_次要前提_(minor premise)

  对于每个构造子，递归子都需要一个函数来满足动机，针对构造子的任意应用。
  每个次要前提都对该构造子的所有参数抽象。
  如果构造子的某个参数类型是归纳类型本身，那么该前提还要接收一个类型为 对应动机应用到这个参数值 上的参数——这个参数会接收到递归处理该递归参数的结果。

: {deftech key := "major premise"}_主要前提_，或称 目标

  最后，递归子接收一个该类型的实例作为参数，以及所有指标的值。

递归子的结果类型，是动机应用于这些指标值和目标的返回值。
:::

/-
:::example "The recursor for {lean}`Bool`"
{lean}`Bool`'s recursor {name}`Bool.rec` has the following parameters:

 * The motive computes a type in any universe, given a {lean}`Bool`.
 * There are cases for both constructors, in which the motive is satisfied for both {lean}`false` and {lean}`true`.
 * The target is some {lean}`Bool`.

The return type is the motive applied to the target.

```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
:::
-/

:::example "{lean}`Bool` 的递归子"
{lean}`Bool` 的递归子 {name}`Bool.rec` 有如下参数：

 * 动机给定一个 {lean}`Bool`，可计算出所属任何宇宙中的类型。
 * 两个构造子都有对应的分支，在这两种情况下，动机分别对 {lean}`false` 和 {lean}`true` 成立。
 * 目标是某个 {lean}`Bool`。

返回类型是动机应用到目标后的结果。

```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
:::

/-
::::example "The recursor for {lean}`List`"
{lean}`List`'s recursor {name}`List.rec` has the following parameters:

:::keepEnv
```lean (show := false)
axiom α.{u} : Type u
```

 * The parameter {lean}`α` comes first, because the parameter and the cases need to refer to it
 * The motive computes a type in any universe, given a {lean}`List α`. There is no connection between the universe levels `u` and `v`.
 * There are cases for both constructors:
    - The motive is satisfied for {name}`List.nil`
    - The motive should be satisfiable for any application of {name}`List.cons`, given that it is satisfiable for the tail. The extra parameter `motive tail` is because `tail`'s type is a recursive occurrence of {name}`List`.
 * The target is some {lean}`List α`.
:::

Once again, the return type is the motive applied to the target.

```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
::::
-/

::::example "{lean}`List` 的递归子"
{lean}`List` 的递归子 {name}`List.rec` 有如下参数：

:::keepEnv
```lean (show := false)
axiom α.{u} : Type u
```

 * 参数 {lean}`α` 在最前，因为参数以及分支都需要引用它
 * 动机在给定一个 {lean}`List α` 时，计算出所属任何宇宙中的类型。这里宇宙层级 `u` 和 `v` 没有联系。
 * 两个构造子的分支：
    - 动机对 {name}`List.nil` 成立
    - 对于 {name}`List.cons`，只要对尾部成立，同样也应成立。额外的参数 `motive tail` 是因为 `tail` 类型是一次递归出现的 {name}`List`。
 * 目标是某个 {lean}`List α`。
:::

同样，返回类型是动机应用于目标的结果。

```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
::::

/-
:::::keepEnv
::::example "Recursor with parameters and indices"
Given the definition of {name}`EvenOddList`:
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


The recursor {name}`EvenOddList.rec` is very similar to that for `List`.
The difference comes from the presence of the index:
 * The motive now abstracts over any arbitrary choice of index.
 * The case for {name EvenOddList.nil}`nil` applies the motive to {name EvenOddList.nil}`nil`'s index value `true`.
 * The case for {name EvenOddList.cons}`cons` abstracts over the index value used in its recursive occurrence, and instantiates the motive with its negation.
 * The target additionally abstracts over an arbitrary choice of index.

```signature
EvenOddList.rec.{u, v} {α : Type v}
  {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
  (nil : motive true EvenOddList.nil)
  (cons : {isEven : Bool} →
    (head : α) →
    (tail : EvenOddList α isEven) → motive isEven tail →
    motive (!isEven) (EvenOddList.cons head tail)) :
  {isEven : Bool} → (t : EvenOddList α isEven) → motive isEven t
```
::::
:::::
-/

:::::keepEnv
::::example "带参数和指标的递归子"
已知 {name}`EvenOddList` 的定义如下：
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


{name}`EvenOddList.rec` 的递归子和 `List` 类似。
不同之处在于多了一个索引：
 * 动机现在对任意的索引抽象。
 * {name EvenOddList.nil}`nil` 的分支将动机应用在该构造子的索引值 `true` 上。
 * {name EvenOddList.cons}`cons` 分支对其递归出现时使用的索引值抽象，并用指标取反的结果实例化动机。
 * 目标同样对任意索引抽象。

```signature
EvenOddList.rec.{u, v} {α : Type v}
  {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
  (nil : motive true EvenOddList.nil)
  (cons : {isEven : Bool} →
    (head : α) →
    (tail : EvenOddList α isEven) → motive isEven tail →
    motive (!isEven) (EvenOddList.cons head tail)) :
  {isEven : Bool} → (t : EvenOddList α isEven) → motive isEven t
```
::::
:::::

/-
When using a predicate (that is, a function that returns a {lean}`Prop`) for the motive, recursors express induction.
The cases for non-recursive constructors are the base cases, and the additional arguments supplied to constructors with recursive arguments are the induction hypotheses.
-/

当动机是一个返回 {lean}`Prop` 的谓词时，递归子就表现为归纳法。
非递归构造子的分支是归纳的基本样例，而递归构造子所额外提供的参数就是归纳假设。

/-
### Subsingleton Elimination
%%%
tag := "subsingleton-elimination"
%%%
-/

### 子单元消去
%%%
tag := "subsingleton-elimination"
%%%

/-
Proofs in Lean are computationally irrelevant.
In other words, having been provided with *some* proof of a proposition, it should be impossible for a program to check *which* proof it has received.
This is reflected in the types of recursors for inductively defined propositions or predicates.
For these types, if there's more than one potential proof of the theorem then the motive may only return another {lean}`Prop`.
If the type is structured such that there's only at most one proof anyway, then the motive may return a type in any universe.
A proposition that has at most one inhabitant is called a {deftech}_subsingleton_.
Rather than obligating users to _prove_ that there's only one possible proof, a conservative syntactic approximation is used to check whether a proposition is a subsingleton.
Propositions that fulfill both of the following requirements are considered to be subsingletons:
 * There is at most one constructor.
 * Each of the constructor's parameter types is either a {lean}`Prop`, a parameter, or an index.
-/

Lean 中的证明是计算无关的。
换句话说，在给定了*某个*命题的证明之后，程序应该无法检测到*到底是哪一个*证明被接受了。
这种思想体现在归纳定义的命题或谓词的递归子的类型中。
对于这些类型，如果定理存在多种可能的证明方式，那么 motive 只能返回另一个 {lean}`Prop`。
如果类型的结构保证了至多只存在一个证明，那么 motive 可以返回任意宇宙中的类型。
拥有至多一个元素的命题被称为 {deftech key := "subsingleton"}_子单元_。
Lean 并不会强制用户去*证明*某命题只有唯一的证明，而是采用了一种保守的语法近似方法来检测一个命题是否为子单元。
满足以下两个条件的命题会被视为子单元（subsingleton）：
 * 至多只有一个构造子。
 * 每个构造子的参数类型要么是 {lean}`Prop`，要么是参数或者索引。

/-
:::example "{lean}`True` is a subsingleton"
{lean}`True` is a subsingleton because it has one constructor, and this constructor has no parameters.
Its recursor has the following signature:
```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
:::
-/

:::example "{lean}`True` 是子单元"
{lean}`True` 是子单元，因为它仅有一个无参数的构造子。
它的递归子类型如下：
```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
:::

/-
:::example "{lean}`False` is a subsingleton"
{lean}`False` is a subsingleton because it has no constructors.
Its recursor has the following signature:
```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
Note that the motive is an explicit parameter.
This is because it is not mentioned in any further parameters' types, so it could not be solved by unification.
:::
-/

:::example "{lean}`False` 是子单元"
{lean}`False` 是子单元，因为它没有构造子。
它的递归子类型如下：
```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
注意动机是一个显式参数。
因为它在后续参数类型中没有出现，因此不能自动推断它。
:::

/-
:::example "{name}`And` is a subsingleton"
{lean}`And` is a subsingleton because it has one constructor, and both of the constructor's parameters' types are propositions.
Its recursor has the following signature:
```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
:::
-/

:::example "{name}`And` 是子单元"
{lean}`And` 是子单元，因为它仅有一个构造子，并且这个构造子的两个参数类型都是命题。
它的递归子类型如下：
```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
:::

/-
:::example "{name}`Or` is not a subsingleton"
{lean}`Or` is not a subsingleton because it has more than one constructor.
Its recursor has the following signature:
```signature
Or.rec {a b : Prop} {motive : a ∨ b → Prop}
  (inl : ∀ (h : a), motive (.inl h))
  (inr : ∀ (h : b), motive (.inr h))
  (t : a ∨ b) : motive t
```
The motive's type indicates that {name}`Or.rec` can only be used to produce proofs.
A proof of a disjunction can be used to prove something else, but there's no way for a program to inspect _which_ of the two disjuncts was true and used for the proof.
:::
-/

:::example "{name}`Or` 不是子单元"
{lean}`Or` 不是子单元，因为它有多个构造子。
它的递归子类型如下：
```signature
Or.rec {a b : Prop} {motive : a ∨ b → Prop}
  (inl : ∀ (h : a), motive (.inl h))
  (inr : ∀ (h : b), motive (.inr h))
  (t : a ∨ b) : motive t
```
动机的类型表明 {name}`Or.rec` 只能用于产生证明。
对析取命题提供的证明也能用来证明其它命题，但程序无法判别具体是哪个分支为真。
:::

/-
:::example "{name}`Eq` is a subsingleton"
{lean}`Eq` is a subsingleton because it has just one constructor, {name}`Eq.refl`.
This constructor instantiates {lean}`Eq`'s index with a parameter value, so all arguments are parameters:
```signature
Eq.refl.{u} {α : Sort u} (x : α) : Eq x x
```
Its recursor has the following signature:
```signature
Eq.rec.{u, v} {α : Sort v} {x : α}
  {motive : (y : α) → x = y → Sort u}
  (refl : motive x (.refl x))
  {y : α} (t : x = y) : motive y t
```
This means that proofs of equality can be used to rewrite the types of non-propositions.
:::
-/

:::example "{name}`Eq` 是子单元"
{lean}`Eq` 是子单元，因为它只有一个构造子 {name}`Eq.refl`。
构造子会用参数值实例化 {lean}`Eq` 的索引，因此所有参数都是参数项：
```signature
Eq.refl.{u} {α : Sort u} (x : α) : Eq x x
```
它的递归子类型如下：
```signature
Eq.rec.{u, v} {α : Sort v} {x : α}
  {motive : (y : α) → x = y → Sort u}
  (refl : motive x (.refl x))
  {y : α} (t : x = y) : motive y t
```
意味着等式证明可以用来重写非命题类型的类型。
:::

/-
## Reduction
%%%
tag := "iota-reduction"
%%%
-/

## 规约
%%%
tag := "iota-reduction"
%%%

/-
In addition to adding new constants to the logic, inductive type declarations also add new reduction rules.
These rules govern the interaction between recursors and constructors; specifically recursors that have constructors as their targets.
This form of reduction is called {deftech}_ι-reduction_ (iota reduction){index}[ι-reduction]{index (subterm:="ι (iota)")}[reduction].

When the recursor's target is a constructor with no recursive parameters, the recursor application reduces to an application of the constructor's case to the constructor's arguments.
If there are recursive parameters, then these arguments to the case are found by applying the recursor to the recursive occurrence.
-/

归纳类型声明除了为逻辑添加新常量外，还会引入新的规约规则。
这些规则负责处理递归子和数据构造子之间的互动，尤其是以构造子为目标的递归子的简化行为。
这种规约形式称为 {deftech key := "ι-reduction"}_ι-规约_（iota reduction）{index}[ι-规约]{index (subterm:="ι (iota)")}[规约]。

当递归子的目标是没有递归参数的构造子时，递归子应用会规约为将该构造子的分支作用于其参数的结果。
如果有递归参数，则这些传递给分支的参数是通过将递归子递归应用于递归出现的参数获得。

/-
# Well-Formedness Requirements
%%%
tag := "well-formed-inductives"
%%%
-/

# 良构性约束
%%%
file := "Well-Formedness Requirements"
tag := "well-formed-inductives"
%%%

/-
Inductive type declarations are subject to a number of well-formedness requirements.
These requirements ensure that Lean remains consistent as a logic when it is extended with the inductive type's new rules.
They are conservative: there exist potential inductive types that do not undermine consistency, but that these requirements nonetheless reject.
-/

归纳类型声明需要满足一系列良构性约束。
这些约束确保当逻辑扩展进入新的归纳类型规则时，Lean 的逻辑系统依然保持一致。
这些约束是保守的：一些不会破坏一致性的归纳类型会被这些约束拒绝。

/-
## Universe Levels
%%%
tag := "inductive-type-universe-levels"
%%%
-/

## 宇宙层级
%%%
tag := "inductive-type-universe-levels"
%%%

/-
Type constructors of inductive types must either inhabit a {tech}[universe] or a function type whose return type is a universe.
Each constructor must inhabit a function type that returns a saturated application of the inductive type.
If the inductive type's universe is {lean}`Prop`, then there are no further restrictions on universes, because {lean}`Prop` is {tech}[impredicative].
If the universe is not {lean}`Prop`, then the following must hold for each parameter to the constructor:
 * If the constructor's parameter is a parameter (in the sense of parameters vs indices) of the inductive type, then this parameter's type may be no larger than the type constructor's universe.
 * All other constructor parameters must be smaller than the type constructor's universe.
-/

归纳类型的类型构造子必须处于某个{tech key := "universe"}[宇宙]中，或是返回类型为宇宙的函数类型。
每个数据构造子的类型必须是返回饱和应用归纳类型的函数类型。
如果归纳类型的宇宙是 {lean}`Prop`，则对宇宙没有进一步的限制，因为 {lean}`Prop` 是{tech key := "impredicative"}[非直谓的]。
如果宇宙不是 {lean}`Prop`，那么以下要求必须成立，对每一个数据构造子的参数都适用：
 * 若构造子的参数是归纳类型的参数（即参数 vs 索引），则该参数类型不能超过类型构造子的宇宙层级。
 * 其它所有构造子参数的类型都必须严格小于类型构造子的宇宙层级。

/-
:::::keepEnv
::::example "Universes, constructors, and parameters"
{lean}`Either` is in the greater of its arguments' universes, because both are parameters to the inductive type:
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```

{lean}`CanRepr` is in a larger universe than the constructor parameter `α`, because `α` is not one of the inductive type's parameters:
```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```

Constructorless inductive types may be in universes smaller than their parameters:
```lean
inductive Spurious (α : Type 5) : Type 0 where
```
It would, however, be impossible to add a constructor to {name}`Spurious` without changing its levels.
::::
:::::
-/

:::::keepEnv
::::example "宇宙、构造子和参数"
{lean}`Either` 处于其两个参数宇宙层级的最大值，因为两个参数都是归纳类型的参数：
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```

{lean}`CanRepr` 的宇宙层级比构造子参数 `α` 要更高，因为 `α` 不是归纳类型的参数：
```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```

无构造子的归纳类型的宇宙可以比参数的宇宙更小：
```lean
inductive Spurious (α : Type 5) : Type 0 where
```
但对 {name}`Spurious` 若要添加构造子，其宇宙层级也必须做相应改变。
::::
:::::

/-
## Strict Positivity
%%%
tag := "strict-positivity"
%%%
-/

## 严格正性
%%%
tag := "strict-positivity"
%%%

/-
All occurrences of the type being defined in the types of the parameters of the constructors must be in {deftech}_strictly positive_ positions.
A position is strictly positive if it is not in a function's argument type (no matter how many function types are nested around it) and it is not an argument of any expression other than type constructors of inductive types.
This restriction rules out unsound inductive type definitions, at the cost of also ruling out some unproblematic ones.
-/

所有定义中的类型在构造子参数类型中的出现都必须处于{deftech key := "strictly positive"}_严格正性_的位置。
如果一个类型不处于函数的参数类型里（无论嵌套了多少层函数类型），也不作为任何表达式（除归纳类型的类型构造子外）的参数，那它就是严格正性的位置。
该限制用来排除不安全的归纳类型定义，虽有可能因此排除掉某些良构类型。

/-
:::::example "Non-strictly-positive inductive types"
::::keepEnv
:::keepEnv
The type `Bad` would make Lean inconsistent if it were not rejected:
```lean (name := Bad) (error := true)
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
:::

:::keepEnv
```lean (show := false)
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
This is because it would be possible to write a circular argument that proves {lean}`False` under the assumption {lean}`Bad`.
{lean}`Bad.bad` is rejected because the constructor's parameter has type {lean}`Bad → Bad`, which is a function type in which {lean}`Bad` occurs as an argument type.
:::

:::keepEnv
This declaration of a fixed point operator is rejected, because `Fix` occurs as an argument to `f`:
```lean (name := Fix) (error := true)
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
:::

`Fix.fix` is rejected because `f` is not a type constructor of an inductive type, but `Fix` itself occurs as an argument to it.
In this case, `Fix` is also sufficient to construct a type equivalent to `Bad`:
```lean (show := false)
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
::::
:::::
-/

:::::example "非严格正性的归纳类型"
::::keepEnv
:::keepEnv
类型 `Bad` 若能通过编译会导致 Lean 不一致：
```lean (name := Bad) (error := true)
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
:::

:::keepEnv
```lean (show := false)
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
之所以这样，是因为如果假定 {lean}`Bad` 成立，则可以构造出环状逻辑从而证明 {lean}`False`。
{lean}`Bad.bad` 会被拒绝，是因为构造子的参数类型是 {lean}`Bad → Bad`，也就是 {lean}`Bad` 作为函数参数出现。
:::

:::keepEnv
以下这个不动点算子类型的定义也会被拒绝，因为 `Fix` 在 `f` 的参数中出现：
```lean (name := Fix) (error := true)
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
:::

`Fix.fix` 会被拒绝，因为 `f` 并不是某个归纳类型的类型构造子，而 `Fix` 在这里作为它的参数出现。
实际上，用 `Fix` 完全可以构造出等价于 `Bad` 的类型：
```lean (show := false)
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
::::
:::::

/-
## Prop vs Type
%%%
tag := "prop-vs-type"
%%%
-/

## Prop vs Type
%%%
tag := "prop-vs-type"
%%%

/-
Lean rejects universe-polymorphic types that could not, in practice, be used polymorphically.
This could arise if certain instantiations of the universe parameters would cause the type itself to be a {lean}`Prop`.
If this type is not a {tech}[subsingleton], then is recursor can only target propositions (that is, the {tech}[motive] must return a {lean}`Prop`).
These types only really make sense as {lean}`Prop`s themselves, so the universe polymorphism is probably a mistake.
Because they are largely useless, Lean's inductive type elaborator has not been designed to support these types.
-/

Lean 会拒绝那些实际上无法多态使用的宇宙多态类型。
例如，如果对宇宙参数的部分实例化会导致类型变成 {lean}`Prop`，而该类型又不是{tech key := "subsingleton"}[子单元]，则其递归子只允许针对命题（即{tech key := "motive"}[动机]只能返回 {lean}`Prop`）。
这些类型实际上只适合充当 {lean}`Prop` 本身，所以宇宙多态很可能本就是错误。
由于这种类型几乎无实际意义，Lean 的归纳类型{tech key := "elaborator"}[繁释器]并未设计为支持它们。

/-
When such universe-polymorphic inductive types are indeed subsingletons, it can make sense to define them.
Lean's standard library defines {name}`PUnit` and {name}`PEmpty`.
To define a subsingleton that can inhabit {lean}`Prop` or a {lean}`Type`, set the option {option}`bootstrap.inductiveCheckResultingUniverse` to {lean}`false`.
-/

如果这种宇宙多态归纳类型本身是子单元，则这样的定义还是有意义的。
Lean 的标准库定义了 {name}`PUnit` 和 {name}`PEmpty`。
若要定义既可属于 {lean}`Prop` 也可属于 {lean}`Type` 的子单元类型，可将选项 {option}`bootstrap.inductiveCheckResultingUniverse` 设为 {lean}`false`。

{optionDocs bootstrap.inductiveCheckResultingUniverse}

/-
::::keepEnv
:::example "Overly-universe-polymorphic {lean}`Bool`"
Defining a version of {lean}`Bool` that can be in any universe is not allowed:
```lean (error := true) (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
invalid universe polymorphic resulting type, the resulting universe is not 'Prop', but it may be 'Prop' for some parameter values:
  Sort u
Possible solution: use levels of the form 'max 1 _' or '_ + 1' to ensure the universe is of the form 'Type _'.
```
:::
::::
-/

::::keepEnv
:::example "过度使用宇宙多态的 {lean}`Bool`"
定义一个可以处于任意宇宙的 {lean}`Bool` 是不被允许的：
```lean (error := true) (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
invalid universe polymorphic resulting type, the resulting universe is not 'Prop', but it may be 'Prop' for some parameter values:
  Sort u
Possible solution: use levels of the form 'max 1 _' or '_ + 1' to ensure the universe is of the form 'Type _'.
```
:::
::::

/-
# Constructions for Termination Checking
%%%
tag := "recursor-elaboration-helpers"
%%%
-/

# 用于终止性检查的构造
%%%
file := "Constructions for Termination Checking"
tag := "recursor-elaboration-helpers"
%%%


/-
In addition to the type constructor, constructors, and recursors that Lean's core type theory prescribes for inductive types, Lean constructs a number of useful helpers.
First, the equation compiler (which translates recursive functions with pattern matching in to applications of recursors) makes use of these additional constructs:
 * `recOn` is a version of the recursor in which the target is prior to the cases for each constructor.
 * `casesOn` is a version of the recursor in which the target is prior to the cases for each constructor, and recursive arguments do not yield induction hypotheses. It expresses case analysis rather than primitive recursion.
 * `below` computes a type that, for some motive, expresses that _all_ inhabitants of the inductive type that are subtrees of the target satisfy the motive. It transforms a motive for induction or primitive recursion into a motive for strong recursion or strong induction.
 * `brecOn` is a version of the recursor in which `below` is used to provide access to all subtrees, rather than just immediate recursive parameters. It represents strong induction.
 * `noConfusion` is a general statement from which injectivity and disjointness of constructors can be derived.
 * `noConfusionType` is the motive used for `noConfusion` that determines what the consequences of two constructors being equal would be. For separate constructors, this is {lean}`False`; if both constructors are the same, then the consequence is the equality of their respective parameters.


For {tech}[well-founded recursion], it is frequently useful to have a generic notion of size available.
This is captured in the {name}`SizeOf` class.
-/

除了 Lean 核心类型理论为归纳类型规定的类型构造子、数据构造子和递归子外，Lean 还自动生成许多实用的辅助构造。
首先，方程编译器（用于将带模式匹配的递归函数翻译为递归子应用）会用到这些额外构造：
 * `recOn` 是递归子的一个变体，其目标参数排在每个构造子的分支参数之前。
 * `casesOn` 也是一个变体，其目标参数也在分支之前，且递归参数不会产生归纳假设。它表达的是分情况分析而非原始递归。
 * `below` 生成一个类型，表达针对某动机，目标所有子树的所有归纳类型元素都满足该动机。它能把归纳/原始递归用的动机变成强递归/强归纳的动机。
 * `brecOn` 是使用 `below` 以可以访问所有子树（而不仅是直接递归参数）的递归子变体，表达强归纳。
 * `noConfusion` 是一个通用语句，可据此推出构造子的单射性和互斥性。
 * `noConfusionType` 是为 `noConfusion` 设计的动机，用以描述两个构造子相等时的推论。对不同构造子而言这是 {lean}`False`；相同构造子则为各自参数的等式。

对于{tech key := "well-founded recursion"}[良构递归]，通常还需要一个通用意义上的“大小”概念。
这正是 {name}`SizeOf` 类型类所提供的。

{docstring SizeOf}
