/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Functions
import Manual.Language.InductiveTypes
import Manual.Quotients

import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Types

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


set_option maxRecDepth 800
/-
#doc (Manual) "类型系统" =>
%%%
tag := "type-system"
%%%
-/

#doc (Manual) "类型系统" =>
%%%
file := "The Type System"
tag := "type-system"
%%%

/-
{deftech}_Terms_, also known as {deftech}_expressions_, are the fundamental units of meaning in Lean's core language.
They are produced from user-written syntax by the elaborator({tech key := "elaborator"}[繁释器]).
Lean's type system relates terms to their _types_, which are also themselves terms.
Types can be thought of as denoting sets, while terms denote individual elements of these sets.
A term is {deftech}_well-typed_ if it has a type under the rules of Lean's type theory.
Only well-typed terms have a meaning.
-/

{deftech key := "terms"}_项_，也称为{deftech key := "expressions"}_表达式_，是 Lean 核心语言中最基本的语义单元。
它们由用户编写的语法经过{tech key := "elaborator"}[繁释器]生成。
Lean 的类型系统将各项和它们的_类型(type)_关联起来，而类型本身也是项。
类型可以被看作是表示一个集合，而项表示该集合中的具体元素。
如果某个项根据 Lean 的类型论规则有一个类型，则称它是{deftech key := "well-typed"}_良型的_（well-typed）。
只有良型的项才有意义。

/-
Terms are a dependently typed λ-calculus: they include function abstraction, application, variables, and `let`-bindings.
In addition to bound variables, variables in the term language may refer to {tech}[constructors], {tech}[type constructors], {tech}[recursors], {deftech}[defined constants], or opaque constants.
Constructors, type constructors, recursors, and opaque constants are not subject to substitution, while defined constants may be replaced with their definitions.
-/

项是一种依值类型 λ-演算：它们包含函数抽象、应用、变量以及 `let`-绑定。
除了绑定变量外，项语言中的变量还可以引用{tech key := "constructor"}[构造子]、{tech key := "type constructor"}[类型构造子]、{tech key := "recursor"}[递归子]、{deftech key := "defined constant"}[已定义常量]或者不透明常量（opaque constant）。
数据构造子、类型构造子、递归子和不透明常量不会被代换，而已定义常量可以被其定义替换。

/-
A {deftech}_derivation_ demonstrates the well-typedness of a term by explicitly indicating the precise inference rules that are used.
Implicitly, well-typed terms can stand in for the derivations that demonstrate their well-typedness.
Lean's type theory is explicit enough that derivations can be reconstructed from well-typed terms, which greatly reduces the overhead that would be incurred from storing a complete derivation, while still being expressive enough to represent modern research mathematics.
This means that proof terms are sufficient evidence of the truth of a theorem and are amenable to independent verification.
-/

一个{deftech key := "derivation"}_演绎_（derivation）通过明确地指明具体应用了哪些推断规则，来展示某项的良型性。
在实际使用中，良型的项本身就代表了证明其良型性的推理过程。
Lean 的类型论可以由良型的项完全可以重建出对应的演绎过程，这大大减少了存储完整演绎所需的开销，而同时仍然能够表达现代数学中的推理。
这意味着证明项已足以作为定理成立的证据，并且可以被独立的系统验证。

/-
In addition to having types, terms are also related by {deftech}_definitional equality_.
This is the mechanically-checkable relation that syntactically equates terms modulo their computational behavior.
Definitional equality includes the following forms of {deftech}[reduction]:
-/

除了拥有类型，项之间还存在{deftech key := "definitional equality"}_定义等价_关系。
定义等价是可机械化检验的关系，用于在语法上将项根据其计算行为视作等价。
定义等价包含如下几种{deftech key := "reduction"}_规约_形式：

/-
 : {deftech}[β] (beta)

    Applying a function abstraction to an argument by substitution for the bound variable

 : {deftech}[δ] (delta)

    Replacing occurrences of {tech}[defined constants] by the definition's value

 : {deftech}[ι] (iota)

    Reduction of recursors whose targets are constructors (primitive recursion)

 : {deftech}[ζ] (zeta)

     Replacement of let-bound variables by their defined values

 : Quotient reduction

   {ref "quotient-model"}[Reduction of the quotient type's function lifting operator] when applied to an element of a quotient

Terms in which all possible reductions have been carried out are in {deftech}_normal form_.
-/

 : {deftech key := "β"}[β-规约]（beta）

    将函数抽象应用到实参时，通过对绑定变量做代换来实现

 : {deftech key := "δ"}[δ-规约]（delta）

    将{tech key := "defined constant"}[已定义常量]出现的地方用其定义值替换

 : {deftech key := "ι"}[ι-规约]（iota）

    归约以构造子为目标的递归器（即原始递归）

 : {deftech key := "ζ"}[ζ-规约]（zeta）

     用定义值替换被 `let` 绑定的变量

 : 商类型规约(Quotient reduction)

     应用于商的元素时{ref "quotient-model"}[规约商类型函数的提升算子(lifting operator)]

若项中所有可能的规约都已执行完毕，则该项处于 {deftech key := "normal form"}_规范形式_。

/-
::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```
Definitional equality includes {deftech}[η-equivalence] of functions and single-constructor inductive types.
That is, {lean}`fun x => f x` is definitionally equal to {lean}`f`, and {lean}`S.mk x.f1 x.f2` is definitionally equal to {lean}`x`, if {lean}`S` is a structure with fields {lean}`f1` and {lean}`f2`.
It also features {deftech}_proof irrelevance_: any two proofs of the same proposition are definitionally equal.
It is reflexive and symmetric, but not transitive.
::::
-/

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```
定义等价包括函数和单构造子归纳类型的 {deftech key := "η-equivalence"}[η-等价]。
也就是说，{lean}`fun x => f x` 与 {lean}`f` 是定义等价的；而若 {lean}`S` 是一个带有字段 {lean}`f1` 和 {lean}`f2` 的结构体，那么 {lean}`S.mk x.f1 x.f2` 与 {lean}`x` 定义等价。
同时还具备 {deftech key := "proof irrelevance"}_证明无关性_：同一命题的任意两个证明项是定义等价的。
定义等价关系具有自反性、对称性，但并不具有传递性。
::::

/-
Definitional equality is used by conversion: if two terms are definitionally equal, and a given term has one of them as its type, then it also has the other as its type.
Because definitional equality includes reduction, types can result from computations over data.
-/

定义等价被用于转换(conversion)：如果项`a`和项`b`是定义等价的，那么如果项`c`有`a`或`b`的类型，那么`c`也拥有另一个类型。
由于定义等价包括规约，因此类型可以通过数据计算得出。

/-
::::keepEnv
:::Manual.example "Computing types"

When passed a natural number, the function {lean}`LengthList` computes a type that corresponds to a list with precisely that many entries in it:

```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```

Because Lean's tuples nest to the right, multiple nested parentheses are not needed:
````lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
````

If the length does not match the number of entries, then the computed type will not match the term:
```lean error:=true name:=wrongNum
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
Application type mismatch: In the application
  ("number", ())
the argument
  ()
has type
  Unit : Type
but is expected to have type
  LengthList String 3 : Type
```
:::
::::
-/

::::keepEnv
:::Manual.example "计算类型"

当传入一个自然数时，{lean}`LengthList` 这个函数会得出一个类型，该类型对应于长度恰好等于这个数的列表：

```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```

由于 Lean 的元组按右结合嵌套，因此无需多层括号：
````lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
````

如果长度与元素项数不匹配，则计算出的类型与项类型不符合：
```lean error:=true name:=wrongNum
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
Application type mismatch: In the application
  ("number", ())
the argument
  ()
has type
  Unit : Type
but is expected to have type
  LengthList String 3 : Type
```
:::
::::

/-
The basic types in Lean are {tech}[universes], {tech}[function] types, the quotient former {name}`Quot`, and {tech}[type constructors] of {tech}[inductive types].
{tech}[Defined constants], applications of {tech}[recursors], function application, {tech}[axioms] or {tech}[opaque constants] may additionally give types, just as they can give rise to terms in any other type.
-/

Lean 的基本类型包括 {tech key := "universe"}[宇宙]、{tech key := "function"}[函数]类型、商类型构造器 {name}`Quot`，以及 {tech key := "inductive type"}[归纳类型]的 {tech key := "type constructor"}[类型构造子]。
{tech key := "defined constant"}[已定义常量]、{tech key := "recursor"}[递归子]的应用、函数应用、{tech key := "axiom"}[公理] 或 {tech key := "opaque constant"}[不透明常量](opaque constant) 也都可以作为类型出现，就像它们能出现在普通项的位置一样。


{include Manual.Language.Functions}

/-
# Propositions
%%%
tag := "propositions"
%%%
-/

# 命题 (Propositions)
%%%
file := "Propositions"
tag := "propositions"
%%%

/-
{deftech}[Propositions] are meaningful statements that admit proof. {index}[proposition]
Nonsensical statements are not propositions, but false statements are.
All propositions are classified by {lean}`Prop`.
-/

{deftech key := "proposition"}[命题] 是带有意义、可被证明的陈述。{index}[proposition]
没有意义的说法不是命题，但不正确/错误的说法依然是命题。
所有命题都属于 {lean}`Prop` 这一类型。

/-
Propositions have the following properties:
-/
命题具备如下属性：

/-
: Definitional proof irrelevance

  Any two proofs of the same proposition are completely interchangeable.

: Run-time irrelevance

  Propositions are erased from compiled code.

: Impredicativity

  Propositions may quantify over types from any universe whatsoever.

: Restricted Elimination

  With the exception of {tech}[subsingletons], propositions cannot be eliminated into non-proposition types.

: {deftech key:="propositional extensionality"}[Extensionality] {index subterm:="of propositions"}[extensionality]

  Any two logically equivalent propositions can be proven to be equal with the {lean}`propext` axiom.
-/

: 定义等价下的证明无关性

  对于同一命题的任意两个证明项，它们完全可以互换。

: 运行时无关性

  编译生成的代码中，命题会被擦除。

: 非限定性

  命题可以对任意宇宙中的类型进行量化。

: 消除受限

  除了 {tech key := "subsingleton"}[子单元] 外，命题不能被消除到非命题类型。

: {deftech key:="propositional extensionality"}[外延性] {index subterm:="of propositions"}[外延性]

  任意两个逻辑等价的命题，可以用公理 {lean}`propext` 证明它们相等。


{zhdocstring propext ZhDoc.propext }

/-

# Universes

Types are classified by {deftech}_universes_. {index}[universe]{margin}[Universes are also referred to as {deftech}_sorts_.]
Each universe has a {deftech (key:="universe level")}_level_, {index subterm := "of universe"}[level] which is a natural number.
The {lean}`Sort` operator constructs a universe from a given level. {index}[`Sort`]
If the level of a universe is smaller than that of another, the universe itself is said to be smaller.
With the exception of propositions (described later in this chapter), types in a given universe may only quantify over types in smaller universes.
{lean}`Sort 0` is the type of propositions, while each `Sort (u + 1)` is a type that describes data.

Every universe is an element of the next larger universe, so {lean}`Sort 5` includes {lean}`Sort 4`.
This means that the following examples are accepted:
-/

# 宇宙（Universe）
%%%
file := "Universe"
tag := "universe"
%%%

类型由 {deftech key := "universes"}_宇宙_ 分类。{index}[universe]{margin}[宇宙有时也称为 {deftech key := "sorts"}_类别(sort)_。]
每个宇宙都有一个 自然数{deftech key := "universe level"}_层级(level)_。{index subterm := "of universe"}[level]
{lean}`Sort` 操作符可根据给定层级构造出一个宇宙。{index}[`Sort`]
若一个宇宙的层级小于另一个，则该宇宙本身也小于后者。
除命题外（将在本章后面介绍），某宇宙内的类型只可以对更小宇宙内的类型进行量化。
{lean}`Sort 0` 是命题类型（Prop），而每个 `Sort (u + 1)` 可描述数据类型。

每个宇宙都是下一个更大宇宙的元素，比如 {lean}`Sort 5` 包含了 {lean}`Sort 4`。
所以如下例子有效：
```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```
/-
On the other hand, {lean}`Sort 3` is not an element of {lean}`Sort 5`:
-/
但 {lean}`Sort 3` 不属于 {lean}`Sort 5`：
```lean (error := true) (name := sort3)
example : Sort 5 := Sort 3
```

```leanOutput sort3
type mismatch
  Type 2
has type
  Type 3 : Type 4
but is expected to have type
  Type 4 : Type 5
```
/-
Similarly, because {lean}`Unit` is in {lean}`Sort 1`, it is not in {lean}`Sort 2`:
-/

同理，{lean}`Unit` 属于 {lean}`Sort 1`，不属于 {lean}`Sort 2`：
```lean
example : Sort 1 := Unit
```
```lean error := true name := unit1
example : Sort 2 := Unit
```

```leanOutput unit1
type mismatch
  Unit
has type
  Type : Type 1
but is expected to have type
  Type 1 : Type 2
```
/-
Because propositions and data are used differently and are governed by different rules, the abbreviations {lean}`Type` and {lean}`Prop` are provided to make the distinction more convenient.  {index}[`Type`] {index}[`Prop`]
`Type u` is an abbreviation for `Sort (u + 1)`, so {lean}`Type 0` is {lean}`Sort 1` and {lean}`Type 3` is {lean}`Sort 4`.
{lean}`Type 0` can also be abbreviated {lean}`Type`, so `Unit : Type` and `Type : Type 1`.
{lean}`Prop` is an abbreviation for {lean}`Sort 0`.
-/

由于命题和数据类型有不同的用法及不同规则，Lean 提供了缩写 {lean}`Type` 和 {lean}`Prop` 来区分二者。{index}[`Type`] {index}[`Prop`]
`Type u` 是 `Sort (u + 1)` 的缩写，所以 {lean}`Type 0` 就是 {lean}`Sort 1`，{lean}`Type 3` 就是 {lean}`Sort 4`。
{lean}`Type 0` 还可以简写为 {lean}`Type`，所以 `Unit : Type` 以及 `Type : Type 1` 成立。
{lean}`Prop` 是 {lean}`Sort 0` 的缩写。

/-
## Predicativity
-/

## 直谓性(Predicativity)

/-
Each universe contains dependent function types, which additionally represent universal quantification and implication.
A function type's universe is determined by the universes of its argument and return types.
The specific rules depend on whether the return type of the function is a proposition.
-/

每个宇宙都包含依值函数类型，即可以表示全称量化和蕴涵。
函数类型的宇宙由其参数类型和返回值类型的宇宙决定；
具体规则取决于返回类型是不是命题。

/-
Predicates, which are functions that return propositions (that is, where the result of the function is some type in `Prop`) may have argument types in any universe whatsoever, but the function type itself remains in `Prop`.
In other words, propositions feature {deftech}[_impredicative_] {index}[impredicative]{index subterm := "impredicative"}[quantification] quantification, because propositions can themselves be statements about all propositions (and all other types).
-/

谓词,即返回命题的函数（即结果为 `Prop` 中类型的函数）可以拥有任意宇宙的参数类型，但这类函数本身还是属于 `Prop`。
换言之，命题具有 {deftech key := "impredicative"}[_非直谓性的_](impredicative){index}[impredicative]{index subterm := "impredicative"}[quantification] 量化， 因为命题本身可以是关于所有命题（以及所有其他类型）的陈述。

/-
:::Manual.example "Impredicativity"
Proof irrelevance can be written as a proposition that quantifies over all propositions:
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

A proposition may also quantify over all types, at any given level:
```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
:::
-/

:::Manual.example "非直谓性"
证明无关性可视为对所有命题进行量化的命题：
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

命题同样可以对任意层级的类型做量化：
```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
:::

/-
For universes at {tech key:="universe level"}[level] `1` and higher (that is, the `Type u` hierarchy), quantification is {deftech}[_predicative_]. {index}[predicative]{index subterm := "predicative"}[quantification]
For these universes, the universe of a function type is the least upper bound of the argument and return types' universes.
-/

对于 1 及以上层级（即 `Type u` 层级）中的宇宙，量化是 {deftech key := "predicative"}[_直谓性_] 的。{index}[predicative]{index subterm := "predicative"}[quantification]
在这一范围内，函数类型所属宇宙为参数类型和返回类型宇宙的最小上界。

/-
:::Manual.example "Universe levels of function types"
Both of these types are in {lean}`Type 2`:
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
:::
-/

:::Manual.example "函数类型的宇宙层级"
下列类型都属于 {lean}`Type 2`：
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
:::


/-
:::Manual.example "Predicativity of {lean}`Type`"
This example is not accepted, because `α`'s level is greater than `1`. In other words, the annotated universe is smaller than the function type's universe:
```lean error := true name:=toosmall
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 1 : Type 2
```
:::
-/

:::Manual.example "{lean}`Type` 的直谓性"
下例会出错，因为 `α` 的层级大于 1。换句话说，标注的宇宙低于函数类型的宇宙：
```lean error := true name:=toosmall
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 1 : Type 2
```
:::

/-
Lean's universes are not {deftech}[cumulative];{index}[cumulativity] a type in `Type u` is not automatically also in `Type (u + 1)`.
Each type inhabits precisely one universe.
-/

Lean 的宇宙不是 {deftech key := "cumulative"}[累积性的]；{index}[cumulativity] 也就是说，`Type u` 中的类型不会自动属于 `Type (u + 1)`。
每个类型只属于唯一一个宇宙。

/-
:::Manual.example "No cumulativity"
This example is not accepted because the annotated universe is larger than the function type's universe:
```lean error := true name:=toobig
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 3 : Type 4
```
:::
-/

:::Manual.example "无累积性"
下例不可通过，因为标注的宇宙层级比实际函数类型要大：
```lean error := true name:=toobig
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 3 : Type 4
```
:::

/-
## Polymorphism
-/

## 多态性（Polymorphism）

/-
Lean supports {deftech}_universe polymorphism_, {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] which means that constants defined in the Lean environment can take {deftech}[universe parameters].
These parameters can then be instantiated with universe levels when the constant is used.
Universe parameters are written in curly braces following a dot after a constant name.
-/

Lean 支持 {deftech key := "universe polymorphism"}_宇宙多态_，{index subterm:="universe"}[polymorphism]{index}[niverse polymorphism]，即 Lean 环境中的常量可以带有 {deftech key := "universe parameter"}[宇宙参数]。
这些参数可在使用常量时以具体宇宙层级实例化。
宇宙参数通过在常量名后以点（dot）加花括号写成。

/-
:::Manual.example "Universe-polymorphic identity function"
When fully explicit, the identity function takes a universe parameter `u`. Its signature is:
```signature
id.{u} {α : Sort u} (x : α) : α
```
:::
-/

:::Manual.example "宇宙多态的身份(identity)函数"
完全显式时，身份函数带有宇宙参数 `u`。其签名为：
```signature
id.{u} {α : Sort u} (x : α) : α
```
:::

/-
Universe variables may additionally occur in {ref "level-expressions"}[universe level expressions], which provide specific universe levels in definitions.
When the polymorphic definition is instantiated with concrete levels, these universe level expressions are also evaluated to yield concrete levels.
-/

宇宙变量还可出现在 {ref "level-expressions"}[宇宙层级表达式]中，用于为定义中的层级变量提供具体值。
多态定义被替换成具体宇宙时，这些表达式也一并被计算成具体数值。

/-
::::keepEnv
:::Manual.example "Universe level expressions"

In this example, {lean}`Codec` is in a universe that is one greater than the universe of the type it contains:
```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```

Lean automatically infers most level parameters.
In the following example, it is not necessary to annotate the type as {lean}`Codec.{0}`, because {lean}`Char`'s type is {lean}`Type 0`, so `u` must be `0`:
```lean (keep := true)
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
:::
::::
-/

::::keepEnv
:::Manual.example "宇宙层级表达式"

此例中，{lean}`Codec` 所在宇宙比所含类型的宇宙高 1：
```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```

Lean 会自动推断大多数层级参数。
如下例中无需手工注明 {lean}`Codec.{0}`，因为 {lean}`Char` 属于 {lean}`Type 0`，所以 `u` 必然为 `0`：
```lean (keep := true)
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
:::
::::

/-
Universe-polymorphic definitions in fact create a _schematic definition_ that can be instantiated at a variety of levels, and different instantiations of universes create incompatible values.
-/

宇宙多态定义实际上创造了一个 _严谨的定义_，可在不同宇宙层级实例化，不同实例产生的值并不兼容。

/-
::::keepEnv
:::Manual.example "Universe polymorphism and definitional equality"

This can be seen in the following example, in which {lean}`T` is a gratuitously-universe-polymorphic function that always returns {lean}`true`.
Because it is marked {keywordOf Lean.Parser.Command.declaration}`opaque`, Lean can't check equality by unfolding the definitions.
Both instantiations of {lean}`T` have the parameters and the same type, but their differing universe instantiations make them incompatible.
```lean (error := true) (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool :=
  (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
type mismatch
  rfl.{?u.29}
has type
  Eq.{?u.29} ?m.31 ?m.31 : Prop
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0) : Prop
```
:::
::::
-/

::::keepEnv
:::Manual.example "宇宙多态 与 定义等价"

如下例中，{lean}`T` 是一个过度宇宙多态的始终返回 {lean}`true` 的函数。
由于被标记为 {keywordOf Lean.Parser.Command.declaration}`opaque`，Lean 无法通过展开定义检查等价。
尽管两次实例化有同样的参数与类型，但由于宇宙实参不同，它们互不兼容。
```lean (error := true) (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool :=
  (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
type mismatch
  rfl.{?u.29}
has type
  Eq.{?u.29} ?m.31 ?m.31 : Prop
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0) : Prop
```
:::
::::

/-
Auto-bound implicit arguments are as universe-polymorphic as possible.
Defining the identity function as follows:
-/

自动绑定的隐式参数会尽可能使用宇宙多态。
如下定义身份函数为：
```lean
def id' (x : α) := x
```
results in the signature:
```signature
id'.{u} {α : Sort u} (x : α) : α
```

/-
:::Manual.example "Universe monomorphism in auto-bound implicit parameters"
On the other hand, because {name}`Nat` is in universe {lean}`Type 0`, this function automatically ends up with a concrete universe level for `α`, because `m` is applied to both {name}`Nat` and `α`, so both must have the same type and thus be in the same universe:
```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```

```lean (show := false)
/-- info: Nat : Type -/
#check_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#check_msgs in
#check count
```
:::
-/

:::Manual.example "自动绑定的隐式参数中的相同宇宙"
另一方面，由于 {name}`Nat` 位于 {lean}`Type 0` 宇宙，下例函数自动推导出 `α` 也位于同一宇宙（因为 `m` 既应用于 {name}`Nat` 也应用于 `α`，二者需同宇宙）：
```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```

```lean (show := false)
/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#guard_msgs in
#check count
```
:::

/-
### Level Expressions
%%%
tag := "level-expressions"
%%%
-/

### 层级表达式（Level Expressions）
%%%
tag := "level-expressions"
%%%

/-
Levels that occur in a definition are not restricted to just variables and addition of constants.
More complex relationships between universes can be defined using level expressions.
-/

出现在定义中的宇宙层级不限于变量与常量加法，还可使用更复杂的层级表达式进行定义。

/-
````
Level ::= 0 | 1 | 2 | ...  -- Concrete levels
        | u, v             -- Variables
        | Level + n        -- Addition of constants
        | max Level Level  -- Least upper bound
        | imax Level Level -- Impredicative LUB
````
-/

````
Level ::= 0 | 1 | 2 | ...  -- 具体层级
        | u, v             -- 层级变量
        | Level + n        -- 常量加法
        | max Level Level  -- 最小上界
        | imax Level Level -- 非直谓性上界
````

/-
Given an assignment of level variables to concrete numbers, evaluating these expressions follows the usual rules of arithmetic.
The `imax` operation is defined as follows:
-/

给定将层级变量赋为具体数值后，计算这些表达式遵循通常的算术规则。
`imax` 的定义如下：


$$``\mathtt{imax}\ u\ v = \begin{cases}0 & \mathrm{when\ }v = 0\\\mathtt{max}\ u\ v&\mathrm{otherwise}\end{cases}``

/-
`imax` is used to implement {tech}[impredicative] quantification for {lean}`Prop`.
In particular, if `A : Sort u` and `B : Sort v`, then `(x : A) → B : Sort (imax u v)`.
If `B : Prop`, then the function type is itself a {lean}`Prop`; otherwise, the function type's level is the maximum of `u` and `v`.
-/

`imax` 用于实现 {tech key := "impredicative"}[非直谓性] 的 {lean}`Prop` 量化。
具体而言，若 `A : Sort u`, `B : Sort v`，则有 `(x : A) → B : Sort (imax u v)`。
若 `B : Prop`，则函数类型本身为 {lean}`Prop`；否则类型层级为 `u` 与 `v` 的最大值。

/-
### Universe Variable Bindings
-/

### 宇宙变量绑定

/-
Universe-polymorphic definitions bind universe variables.
These bindings may be either explicit or implicit.
Explicit universe variable binding and instantiation occurs as a suffix to the definition's name.
Universe parameters are defined or provided by suffixing the name of a constant with a period (`.`) followed by a comma-separated sequence of universe variables between curly braces.
-/

宇宙多态定义绑定宇宙变量。
这些绑定可以是显式的也可以是隐式的。
显式的宇宙变量绑定和实例化发生在定义名称的后缀处。
通过在常量名称后加上一个点(`.`)，然后在花括号中跟随以逗号分隔的宇宙变量序列，来定义或提供宇宙参数。

/-
::::keepEnv
:::Manual.example "Universe-polymorphic `map`"
The following declaration of {lean}`map` declares two universe parameters (`u` and `v`) and instantiates the polymorphic {name}`List` with each in turn:
```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
:::
::::
-/

::::keepEnv
:::Manual.example "宇宙多态的 `map`"
如下 {lean}`map` 的声明声明了两个宇宙参数（`u` 与 `v`），并实例化多态型 {name}`List` 各用一次：
```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
:::
::::

/-
Just as Lean automatically instantiates implicit parameters, it also automatically instantiates universe parameters.
When {ref "automatic-implicit-parameters"}[automatic implicit parameter insertion] is enabled (i.e. the {option}`autoImplicit` option is set to {lean}`true`, which is the default), it is not necessary to explicitly bind universe variables; they are inserted automatically.
When it is set to {lean}`false`, then they must be added explicitly or declared using the `universe` command. {TODO}[xref]
-/

就如 Lean 会自动实例化隐式参数，它也会自动实例化宇宙参数。
当开启 {ref "automatic-implicit-parameters"}[自动插入隐式参数] 功能（即 {option}`autoImplicit` 设为 {lean}`true`，默认即如此），无需显式绑定宇宙变量，会自动补全。
若设为 {lean}`false`，则需手动写明或用 `universe` 命令声明。{TODO}[xref]

/-
:::Manual.example "Automatic Implicit Parameters and Universe Polymorphism"
When `autoImplicit` is {lean}`true` (which is the default setting), this definition is accepted even though it does not bind its universe parameters:
```lean (keep := false)
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

When `autoImplicit` is {lean}`false`, the definition is rejected because `u` and `v` are not in scope:
```lean (error := true) (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level 'u'
```
```leanOutput uv
unknown universe level 'v'
```
:::
-/

:::Manual.example "自动隐式参数与宇宙多态"
当 `autoImplicit` 设为 {lean}`true`（默认设置），该代码可通过，即使没显式绑定宇宙参数：
```lean (keep := false)
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

设为 {lean}`false` 时，定义因 `u`、`v` 不在作用域而报错：
```lean (error := true) (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level 'u'
```
```leanOutput uv
unknown universe level 'v'
```
:::

/-
In addition to using `autoImplicit`, particular identifiers can be declared as universe variables in a particular {tech}[section scope] using the `universe` command.
-/

除使用 `autoImplicit` 外，也可以用 `universe` 命令在特定 {tech key := "section scope"}[作用域] 下声明特定标识符为宇宙变量。

/-
:::syntax Lean.Parser.Command.universe (title := "Universe Parameter Declarations")
```grammar
universe $x:ident $xs:ident*
```

Declares one or more universe variables for the extent of the current scope.

Just as the `variable` command causes a particular identifier to be treated as a parameter with a particular type, the `universe` command causes the subsequent identifiers to be implicitly quantified as as universe parameters in declarations that mention them, even if the option `autoImplicit` is {lean}`false`.
:::
-/

:::syntax Lean.Parser.Command.universe (title := "声明宇宙参数")
```grammar
universe $x:ident $xs:ident*
```

声明若干宇宙变量，本作用域内有效。

如同 `variable` 命令将某标识符视为带类型的参数，`universe` 命令可以让标识符在后续声明中作为宇宙参数，无需在 `autoImplicit` 为 {lean}`true` 时显式指明。
:::

/-
:::Manual.example "The `universe` command when `autoImplicit` is `false`"
```lean (keep := false)
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::
-/

:::Manual.example "`autoImplicit = false` 时的 `universe` 命令"
```lean (keep := false)
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::

/-
Because the automatic implicit parameter feature only insert parameters that are used in the declaration's {tech}[header], universe variables that occur only on the right-hand side of a definition are not inserted as arguments unless they have been declared with `universe` even when `autoImplicit` is `true`.
-/

自动隐式参数功能只会为声明 {tech key := "header"}[头部] 中用到的参数插入参数，若宇宙变量只出现在定义右侧而非头部，除非已用 `universe` 声明，否则即使 `autoImplicit` 为 {lean}`true` 也不会被自动补齐。

/-
:::Manual.example "Automatic universe parameters and the `universe` command"

This definition with an explicit universe parameter is accepted:
```lean (keep := false)
def L.{u} := List (Type u)
```
Even with automatic implicit parameters, this definition is rejected, because `u` is not mentioned in the header, which precedes the `:=`:
```lean (error := true) (name := unknownUni) (keep := false)
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level 'u'
```
With a universe declaration, `u` is accepted as a parameter even on the right-hand side:
```lean (keep := false)
universe u
def L := List (Type u)
```
The resulting definition of `L` is universe-polymorphic, with `u` inserted as a universe parameter.

Declarations in the scope of a `universe` command are not made polymorphic if the universe variables do not occur in them or in other automatically-inserted arguments.
```lean
universe u
def L := List (Type 0)
#check L
```
:::
-/

:::Manual.example "自动宇宙参数与 `universe` 命令"

下定义带显式宇宙参数可通过：
```lean (keep := false)
def L.{u} := List (Type u)
```
即使自动隐式参数开启，下定义因未在头部声明 `u` 而报错：
```lean (error := true) (name := unknownUni) (keep := false)
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level 'u'
```
用 `universe` 声明后，右侧用到的 `u` 可被接受：
```lean (keep := false)
universe u
def L := List (Type u)
```
此时得到的 `L` 定义是宇宙多态，`u` 自动插入为宇宙参数。

声明作用域内，若声明和自动参数没用到宇宙变量，定义就不是多态的：
```lean
universe u
def L := List (Type 0)
#check L
```
:::

/-
### Universe Unification
%%%
draft := true
%%%
-/

### 宇宙归一（Unification）
%%%
draft := true
%%%


/-
:::planned 99
 * Rules for unification, properties of algorithm
 * Lack of injectivity
 * Universe inference for unannotated inductive types
:::
-/

:::planned 99
 * 归一规则与算法性质
 * 非单射性
 * 归纳类型的省略注解的宇宙推断
:::

/-
### Universe Lifting
-/

### 宇宙提升（Universe Lifting）

/-
When a type's universe is smaller than the one expected in some context, {deftech}_universe lifting_ operators can bridge the gap.
These are wrappers around terms of a given type that are in larger universes than the wrapped type.
There are two lifting operators:
 * {name}`PLift` can lift any type, including {tech}[propositions], by one level. It can be used to include proofs in data structures such as lists.
 * {name}`ULift` can lift any non-proposition type by any number of levels.
-/


当某类型所在宇宙低于实际应用要求时，可以用 {deftech key := "universe lifting"}_宇宙提升_ 操作符补足。
这类操作会用包裹的方式让某类型提升至更高宇宙。
主要有两种提升操作：

 * {name}`PLift` 可将任意类型（包括 {tech key := "proposition"}[命题]）提升一级。它可用于将证明项包含进数据结构（如列表）中。
 * {name}`ULift` 可将任意非命题类型提升任意层级。

{zhdocstring PLift ZhDoc.PLift}

{zhdocstring ULift ZhDoc.ULift}

{include 0 Language.InductiveTypes}

{include 0 Manual.Quotients}
