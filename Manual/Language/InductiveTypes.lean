/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Meta.LexedText
import Manual.Language.InductiveTypes.LogicalModel
import Manual.Language.InductiveTypes.Structures
import Manual.Language.InductiveTypes.Nested
import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Language.InductiveTypes

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

/-
#doc (Manual) "Inductive Types" =>
%%%
tag := "inductive-types"
%%%
-/

#doc (Manual) "归纳类型" =>
%%%
file :=  "Inductive Types"
tag := "inductive-types"
%%%

/-
{deftech}_Inductive types_ are the primary means of introducing new types to Lean.
While {tech}[universes], {tech}[functions], and {tech}[quotient types] are built-in primitives that could not be added by users, every other type in Lean is either an inductive type or defined in terms of universes, functions, and inductive types.
Inductive types are specified by their {deftech}_type constructors_ {index}[type constructor] and their {deftech}_constructors_; {index}[constructor] their other properties are derived from these.
Each inductive type has a single type constructor, which may take both {tech}[universe parameters] and ordinary parameters.
Inductive types may have any number of constructors; these constructors introduce new values whose types are headed by the inductive type's type constructor.
-/

{deftech key := "inductive types"}_归纳类型_ 是在 Lean 中引入新类型的主要方式。
虽然 {tech key := "universes"}[宇宙]、{tech key := "functions"}[函数] 以及 {tech key := "quotient types"}[商类型] 是内置的原语类型，用户无法自行添加，但 Lean 里的其它类型要么是归纳类型，要么是基于宇宙、函数与归纳类型定义的。
归纳类型的定义依赖于它们的 {deftech key := "type constructor"}_类型构造子_ 和 {deftech key := "constructor"}_构造子_ ；{index}[constructor]它们的其它性质也由这些定义推导而来。
每个归纳类型有唯一的类型构造子，这个构造子可能带有 {tech key := "universe parameter"}[宇宙参数] 和普通参数。
归纳类型可以拥有任意数量的构造子；这些构造子用于生成新的值，其类型由归纳类型的类型构造子决定。


/-
Based on the type constructor and the constructors for an inductive type, Lean derives a {deftech}_recursor_{index}[recursor]{see "recursor"}[eliminator].
Logically, recursors represent induction principles or elimination rules; computationally, they represent primitive recursive computations.
The termination of recursive functions is justified by translating them into uses of the recursors, so Lean's kernel only needs to perform type checking of recursor applications, rather than including a separate termination analysis.
Lean additionally produces a number of helper constructions based on the recursor,{margin}[The term _recursor_ is always used, even for non-recursive types.] which are used elsewhere in the system.
-/


根据归纳类型的类型构造子和构造子，Lean 会自动生成一个 {deftech key := "recursor"}_递归子_{index}[递归子]{see "recursor"}[消去子]。
从逻辑上讲，递归子代表归纳原则或消去规则；从计算角度看，它们表示原始递归计算。
递归函数的终止性由其翻译为递归子的调用来保证，因此 Lean 的内核只需对递归子的应用做类型检查，而无需单独进行终止性分析。
除此之外，Lean 还根据递归子生成很多辅助结构{margin}[无论类型是否递归，递归子总会被用到]，这些结构被系统的其他部分使用。

/-
_Structures_ are a special case of inductive types that have exactly one constructor.
When a structure is declared, Lean generates helpers that enable additional language features to be used with the new structure.
-/

_结构体_ 是一种特殊的归纳类型，只包含一个构造子。
当一个结构体被声明时，Lean 会自动生成辅助工具，使得新结构体能支持更多语言特性。

/-
This section describes the specific details of the syntax used to specify both inductive types and structures, the new constants and definitions in the environment that result from inductive type declarations, and the run-time representation of inductive types' values in compiled code.
-/
本节描述用于定义归纳类型和结构体的具体语法细节、归纳类型声明会在环境中引入哪些新的常量和定义，以及在编译后归纳类型值的运行时表现。


/-
# Inductive Type Declarations
%%%
tag := "inductive-declarations"
%%%
-/

# 归纳类型声明
%%%
file := "Inductive Type Declarations"
tag := "inductive-declarations"
%%%

/-
:::syntax command (alias := «inductive») (title := "Inductive Type Declarations")
```grammar
$_:declModifiers
inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```

Declares a new inductive type.
The meaning of the {syntaxKind}`declModifiers` is as described in the section {ref "declaration-modifiers"}[on declaration modifiers].
:::
-/

:::syntax command (alias := «inductive») (title := "归纳类型声明")
```grammar
$_:declModifiers
inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```
声明一个新的归纳类型。
{syntaxKind}`declModifiers` 的含义可在 {ref "declaration-modifiers"}[声明修饰词部分] 查询。
:::

/-
After declaring an inductive type, its type constructor, constructors, and recursor are present in the environment.
New inductive types extend Lean's core logic—they are not encoded or represented by some other already-present data.
Inductive type declarations must satisfy {ref "well-formed-inductives"}[a number of well-formedness requirements] to ensure that the logic remains consistent.
-/


声明归纳类型后，其类型构造子、构造子和递归子会添加到环境中。
新的归纳类型扩展了 Lean 的核心逻辑——它们不是由系统中已有的数据编码或模拟出来的。
归纳类型声明还必须满足一系列 {ref "well-formed-inductives"}[良构性要求] 以确保逻辑系统的一致性。

/-
The first line of the declaration, from {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` to {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`, specifies the new {tech}[type constructor]'s name and type.
If a type signature for the type constructor is provided, then its result type must be a {tech}[universe], but the parameters do not need to be types.
If no signature is provided, then Lean will attempt to infer a universe that's just big enough to contain the resulting type.
In some situations, this process may fail to find a minimal universe or fail to find one at all, necessitating an annotation.
-/

声明的第一行，从 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` 到 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`，用于指定新的 {tech key := "type constructor"}[类型构造子] 的名字和类型。
如果为类型构造子提供了类型签名，则结果类型必须是 {tech key := "universe"}[宇宙]，但参数不一定要是类型。
如果没有提供签名，Lean 会尝试为结果类型推断出刚好合适的宇宙。
在某些场景下，推断可能无法找到最小宇宙甚至无法推断成功，此时需要手动注释。

/-
The constructor specifications follow {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`.
Constructors are not mandatory, as constructorless inductive types such as {lean}`False` and {lean}`Empty` are perfectly sensible.
Each constructor specification begins with a vertical bar (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`), declaration modifiers, and a name.
The name is a {tech}[raw identifier].
A declaration signature follows the name.
The signature may specify any parameters, modulo the well-formedness requirements for inductive type declarations, but the return type in the signature must be a saturated application of the type constructor of the inductive type being specified.
If no signature is provided, then the constructor's type is inferred by inserting sufficient implicit parameters to construct a well-formed return type.
-/

构造子定义在 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`后边。
构造子并非必需，比如像 {lean}`False` 和 {lean}`Empty` 这样没有构造子的归纳类型是完全合理的。
每个构造子定义以竖线 (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`)、声明修饰词和名字。
名字是 {tech key := "raw identifier"}[原始标识符]。
名字后接声明签名。
签名可以包含任意参数，但需满足归纳类型声明的良构性要求，返回类型必须是归纳类型的类型构造子的饱和应用。
如果未指定签名，则 Lean 会插入足够的隐式参数来推断出良构的返回类型。

/-
The new inductive type's name is defined in the {tech}[current namespace].
Each constructor's name is in the inductive type's namespace.{index subterm:="of inductive type"}[namespace]
-/
新归纳类型的名字定义在{tech key := "current namespace"}[当前命名空间]中。
每个构造子的名字位于该归纳类型的命名空间下。{index subterm:="of inductive type"}[namespace]

/-
## Parameters and Indices
%%%
tag := "inductive-datatypes-parameters-and-indices"
%%%
-/

## 参数与索引
%%%
tag := "inductive-datatypes-parameters-and-indices"
%%%

/-
Type constructors may take two kinds of arguments: {deftech}_parameters_ {index subterm:="of inductive type"}[parameter] and {deftech key:="index"}_indices_.{index subterm:="of inductive type"}[index]
Parameters must be used consistently in the entire definition; all occurrences of the type constructor in each constructor in the declaration must take precisely the same argument.
Indices may vary among the occurrences of the type constructor.
All parameters must precede all indices in the type constructor's signature.
-/

类型构造子可以接收两类参数：{deftech key:= "parameters"}_参数_ {index subterm:="of inductive type"}[parameter] 和 {deftech key:="index"}_索引_ {index subterm:="of inductive type"}[index]。
定义中，参数必须在整个归纳类型定义中保持一致；所有构造子中出现的类型构造子，参数必须一模一样。
索引则可以在不同构造子的类型构造子的具体应用中变化。
所有参数在类型构造子的签名中必须排在索引的前面。

/-
Parameters that occur prior to the colon (`':'`) in the type constructor's signature are considered parameters to the entire inductive type declaration.
They are always parameters that must be uniform throughout the type's definition.
Generally speaking, parameters that occur after the colon are indices that may vary throughout the definition of the type.
However, if the option {option}`inductive.autoPromoteIndices` is {lean}`true`, then syntactic indices that could have been parameters are made into parameters.
An index could have been a parameter if all of its type dependencies are themselves parameters and it is used uniformly as an uninstantiated variable in all occurrences of the inductive type's type constructor in all constructors.
-/

在类型构造子的签名中冒号（`':'`）之前的内容作为整个归纳类型声明的参数，
这些参数在类型定义过程中始终如一。
通常，冒号之后为索引，可以在归纳类型定义中变化。
但如果 {option}`inductive.autoPromoteIndices` 选项为 {lean}`true`，则本来可以作为参数的语法层面的索引会被自动提升为参数。
当一个索引的所有类型依赖全都是参数类型，且它在所有构造子的类型构造子调用中始终未实例化、未变化，那么它就可以被当作参数。

{zhOptionDocs inductive.autoPromoteIndices ZhDoc.Option.inductive.autoPromoteIndices}

/-
Indices can be seen as defining a _family_ of types.
Each choice of indices selects a type from the family, which has its own set of available constructors.
Type constructors with indices are said to specify {deftech}_indexed families_ {index subterm:="of types"}[indexed family] of types.
-/

索引实际上定义了一个_类型族_。
每次索引取值确定，就从族中选出一个类型，该类型有它各自的构造子。
含索引的类型构造子即定义了一个 {deftech key:="indexed family"}_索引族_ {index subterm:="of types"}[带索引类型族]。

/-
## Example Inductive Types
%%%
tag := "example-inductive-types"
%%%
-/

## 归纳类型样例
%%%
tag := "example-inductive-types"
%%%
/-
:::example "A constructorless type"
{lean}`Vacant` is an empty inductive type, equivalent to Lean's {lean}`Empty` type:
```lean
inductive Vacant : Type where
```

Empty inductive types are not useless; they can be used to indicate unreachable code.
:::
-/

:::example "一个没有构造子的类型"
{lean}`Vacant` 是一个空的归纳类型，等价于 Lean 的 {lean}`Empty` 类型：
```lean
inductive Vacant : Type where
```

空归纳类型并非毫无用处；它们可以用于标记不可达代码。
:::

/-
:::example "A constructorless proposition"
{lean}`No` is a false {tech}[proposition], equivalent to Lean's {lean}`False`:
```lean
inductive No : Prop where
```

```lean (show := false) (keep := false)
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
:::
-/

:::example "一个没有构造子的命题"
{lean}`No` 是一个假命题，等价于 Lean 的 {lean}`False`:
```lean
inductive No : Prop where
```

```lean (show := false) (keep := false)
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
:::

/-
:::example "A unit type" (keep := true)
{lean}`Solo` is equivalent to Lean's {lean}`Unit` type:
```lean
inductive Solo where
  | solo
```
It is an example of an inductive type in which the signatures have been omitted for both the type constructor and the constructor.
Lean assigns {lean}`Solo` to {lean}`Type`:
```lean (name := OneTy)
#check Solo
```
```leanOutput OneTy
Solo : Type
```
The constructor is named {lean}`Solo.solo`, because constructor names are the type constructor's namespace.
Because {lean}`Solo` expects no arguments, the signature inferred for {lean}`Solo.solo` is:
```lean (name := oneTy)
#check Solo.solo
```
```leanOutput oneTy
Solo.solo : Solo
```
:::
-/

:::example "单位类型" (keep := true)
{lean}`Solo` 和 Lean 的 {lean}`Unit` 类型等价：
```lean
inductive Solo where
  | solo
```
这是一个类型构造子和构造子的签名都被省略的例子。Lean 会将 {lean}`Solo` 推断为 {lean}`Type`：
```lean (name := OneTy)
#check Solo
```
```leanOutput OneTy
Solo : Type
```
构造子的名字是 {lean}`Solo.solo`，因为构造子的名字在类型构造子的命名空间下。
由于 {lean}`Solo` 无需参数，Lean 自动推断 {lean}`Solo.solo` 的类型为：
```lean (name := oneTy)
#check Solo.solo
```
```leanOutput oneTy
Solo.solo : Solo
```
:::


/-
:::example "A true proposition"
{lean}`Yes` is equivalent to Lean's {lean}`True` proposition:

```lean
inductive Yes : Prop where
  | intro
```
Unlike {lean}`One`, the new inductive type {lean}`Yes` is specified to be in the {lean}`Prop` universe.
```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
The signature inferred for {lean}`Yes.intro` is:
```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```

```lean (show := false) (keep := false)
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
:::
-/

:::example "真命题"
{lean}`Yes` 等价于 Lean 的 {lean}`True` 命题：

```lean
inductive Yes : Prop where
  | intro
```
不同于 {lean}`One`，新的归纳类型 {lean}`Yes` 被指定为 {lean}`Prop` 宇宙。
```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
推断得到的 {lean}`Yes.intro` 的签名如下：
```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```

```lean (show := false) (keep := false)
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
:::

/-
::::example "A type with parameter and index" (keep := true)

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

An {lean}`EvenOddList α b` is a list where {lean}`α` is the type of the data stored in the list and {lean}`b` is {lean}`true` when there are an even number of entries:
:::

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```

This example is well typed because there are two entries in the list:
```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```

This example is not well typed because there are three entries in the list:
```lean (error := true) (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true : Type
but is expected to have type
  EvenOddList String true : Type
```

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

In this declaration, {lean}`α` is a {tech}[parameter], because it is used consistently in all occurrences of {name}`EvenOddList`.
{lean}`b` is an {tech}[index], because different {lean}`Bool` values are used for it at different occurrences.
:::


```lean (show:=false) (keep:=false)
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
::::
-/

::::example "一个带参数和索引的类型" (keep := true)

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

{lean}`EvenOddList α b` 表示一种列表，其中 {lean}`α` 是元素类型，{lean}`b` 为 {lean}`true` 表示含偶数个元素：
:::

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```

以下例子类型合法，因为列表有两个元素：
```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```

下面这个例子类型不合法，因为实际有三个元素：
```lean (error := true) (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true : Type
but is expected to have type
  EvenOddList String true : Type
```

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```
在本声明中，{lean}`α` 是 {tech key := "parameter"}[参数]，
因为它在 {name}`EvenOddList` 的每次出现都保持一致；{lean}`b` 是 {tech key := "index"}[索引]，因为它在不同出现中可取不同值。
:::


```lean (show:=false) (keep:=false)
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
::::

/-
:::::keepEnv
::::example "Parameters before and after the colon"

In this example, both parameters are specified before the colon in {name}`Either`'s signature.

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β
```

In this version, there are two types named `α` that might not be identical:
```lean (name := Either') (error := true)
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : β → Either' α β
```
```leanOutput Either'
Mismatched inductive type parameter in
  Either' α β
The provided argument
  α
is not definitionally equal to the expected parameter
  α✝

Note: The value of parameter 'α✝' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

Placing the parameters after the colon results in parameters that can be instantiated by the constructors:
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v + 1) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : β → Either'' α β
```
A larger universe is required for this type because {ref "inductive-type-universe-levels"}[constructor parameters must be in universes that are smaller than the inductive type's universe].
{name}`Either''.right`'s type parameter is discovered via Lean's ordinary rules for {tech}[automatic implicit parameters].
::::
:::::
-/

:::::keepEnv
::::example "参数在冒号前和冒号后"

在本例中，所有参数都在 {name}`Either` 签名的冒号前：

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β
```

在下面这个版本中，有两个名为 `α` 的类型，可能不完全相同：
```lean (name := Either') (error := true)
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : β → Either' α β
```
```leanOutput Either'
Mismatched inductive type parameter in
  Either' α β
The provided argument
  α
is not definitionally equal to the expected parameter
  α✝

Note: The value of parameter 'α✝' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

把参数放在冒号后，则对应的构造子参数可以由构造子自行实例化：
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v + 1) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : β → Either'' α β
```
此时需要更大的宇宙层级，因为 {ref "inductive-type-universe-levels"}[构造子的参数必须处于比归纳类型本身更低的宇宙]。
{name}`Either''.right` 的类型参数会按 Lean 的 {tech key := "automatic implicit parameters"}[自动隐式参数] 规则推断。
::::
:::::

/-
## Anonymous Constructor Syntax
%%%
tag := "anonymous-constructor-syntax"
%%%
-/

## 匿名构造子语法
%%%
file := "Anonymous Constructor Syntax"
tag := "anonymous-constructor-syntax"
%%%

/-
If an inductive type has just one constructor, then this constructor is eligible for {deftech}_anonymous constructor syntax_.
Instead of writing the constructor's name applied to its arguments, the explicit arguments can be enclosed in angle brackets (`'⟨'` and `'⟩'`, Unicode `MATHEMATICAL LEFT ANGLE BRACKET	(U+0x27e8)` and `MATHEMATICAL RIGHT ANGLE BRACKET	(U+0x27e9)`) and separated with commas.
This works in both pattern and expression contexts.
Providing arguments by name or converting all implicit parameters to explicit parameters with `@` requires using the ordinary constructor syntax.
-/

如果归纳类型只有一个构造子，则这个构造子可以使用 {deftech key:="anonymous constructor syntax"}_匿名构造子语法_。
即，不必写出构造子的名字并将其应用到参数上，而直接把所有显式参数用尖括号（`'⟨'` 和 `'⟩'`, Unicode `MATHEMATICAL LEFT ANGLE BRACKET (U+0x27e8)` 和 `MATHEMATICAL RIGHT ANGLE BRACKET (U+0x27e9)`）括起来，并用逗号分隔即可。
这种语法可以用于模式匹配和表达式。
若想按照参数名字提供参数，或将所有隐式参数变为显式，则需使用普通构造子语法。

/-
:::syntax term (title := "Anonymous Constructors")
Constructors can be invoked anonymously by enclosing their explicit arguments in angle brackets, separated by commas.
```grammar
⟨ $_,* ⟩
```
:::
-/

:::syntax term (title := "匿名构造子")
可通过用尖括号括起所有显式参数并用逗号分隔，匿名地调用构造子。
```grammar
⟨ $_,* ⟩
```
:::

/-
::::example "Anonymous constructors"

:::keepEnv
```lean (show:=false)
axiom α : Type
```
The type {lean}`AtLeastOne α` is similar to `List α`, except there's always at least one element present:
:::

```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```

Anonymous constructor syntax can be used to construct them:
```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
and to match against them:
```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```

Equivalently, traditional constructor syntax could have been used:
```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
::::
-/

::::example "匿名构造子"

:::keepEnv
```lean (show:=false)
axiom α : Type
```
类型 {lean}`AtLeastOne α` 和 `List α` 相似，区别在于它始终至少有一个元素：
:::

```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```

可采用匿名构造子语法进行构造：
```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
也可用该语法进行模式匹配：
```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```

同样，传统构造子语法也可以：
```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
::::

/-
## Deriving Instances
%%%
tag := "inductive-declarations-deriving-instances"
%%%
-/


## 派生实例
%%%
tag := "inductive-declarations-deriving-instances"
%%%

/-
The optional {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` clause of an inductive type declaration can be used to derive instances of type classes.
Please refer to {ref "deriving-instances"}[the section on instance deriving] for more information.
-/

归纳类型声明末尾可选的 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` 子句，可用于自动派生类型类实例。
详情请见 {ref "deriving-instances"}[关于实例自动派生的章节]。

{include 0 Manual.Language.InductiveTypes.Structures}

{include 0 Manual.Language.InductiveTypes.LogicalModel}

/-
# Run-Time Representation
%%%
tag := "run-time-inductives"
%%%
-/

# 运行时表示
%%%
file := "Run-Time Representation"
tag := "run-time-inductives"
%%%

/-
An inductive type's run-time representation depends both on how many constructors it has, how many arguments each constructor takes, and whether these arguments are {tech}[relevant].
-/

归纳类型的运行时表示取决于构造子的数量、每个构造子参数的数量，以及参数是否 {tech key := "relevant"}[相关]。

/-
## Exceptions
%%%
tag := "inductive-types-runtime-special-support"
%%%
-/

## 特例
%%%
tag := "inductive-types-runtime-special-support"
%%%

并非所有归纳类型都采用这里描述的表示——部分归纳类型由 Lean 编译器特别支持：

/-
:::keepEnv
````lean (show := false)
axiom α : Prop
````

 * The representation of the fixed-width integer types {lean}`UInt8`, …, {lean}`UInt64`, {lean}`Int8`, …, {lean}`Int64`, and {lean}`USize` depends on the whether the code is compiled for a 32- or 64-bit architecture.
   Fixed-width integer types that are strictly smaller than the architecture's pointer type are stored unboxed by setting the lowest bit of a pointer to `1`.
   Integer types that are at least as large as the architecture's pointer type may be boxed or unboxed, depending on whether a concrete value fits in one fewer bits than the pointer type.
   If so, it is encoded by setting the lowest bit of the value to `1` (checked by {c}`lean_is_scalar`).
   Otherwise, the value is represented is a pointer to a fixed-size Lean object on the heap.
   In the C FFI, these values are marshalled into the appropriate C types {c}`uint8_t`, …, {c}`uint64_t`, and {c}`size_t`, respectively.{margin}[Fixed-width signed integer types are also represented as unsigned C integers in the FFI.]

 * {lean}`Char` is represented by `uint32_t`. Because {lean}`Char` values never require more than 21 bits, they are always unboxed.

 * {lean}`Float` is represented by a pointer to a Lean object that contains a `double`.

 * An {deftech}_enum inductive_ type of at least 2 and at most $`2^{32}` constructors, each of which has no parameters, is represented by the first type of {c}`uint8_t`, {c}`uint16_t`, {c}`uint32_t` that is sufficient to assign a unique value to each constructor. For example, the type {lean}`Bool` is represented by {c}`uint8_t`, with values {c}`0` for {lean}`false` and {c}`1` for {lean}`true`. {TODO}[Find out whether this should say "no relevant parameters"]

 * {lean}`Decidable α` is represented the same way as `Bool` {TODO}[Aren't Decidable and Bool just special cases of the rules for trivial constructors and irrelevance?]

 * {lean}`Nat` and {lean}`Int` are represented by {c}`lean_object *`.
   A run-time {lean}`Nat` or {lean}`Int` value is either a pointer to an opaque arbitrary-precision integer object or, if the lowest bit of the “pointer” is `1` (checked by {c}`lean_is_scalar`), an encoded unboxed natural number or integer ({c}`lean_box`/{c}`lean_unbox`). {TODO}[Move these to FFI section or Nat chapter]

:::
-/

:::keepEnv
````lean (show := false)
axiom α : Prop
````

 * 固定宽度整数类型 {lean}`UInt8`、{lean}`UInt64`、{lean}`Int8`、{lean}`Int64` 与 {lean}`USize` 的表示，取决于是为 32 位还是 64 位架构编译。
   比指针类型宽度小的固定宽度整数，采用设置指针最低位为 1 的无箱（unbox）方式存储。
   长度等于指针宽度的类型，视具体内容可采用无箱或有箱方式：如果实际数值可以用指针位数减一的位表示，则用最低位为 1 区分为 unbox；否则，将其作为指针指向堆上的固定大小 Lean 对象。
   在 C FFI 中，这些值会被转为相应的 C 类型 {c}`uint8_t`、{c}`uint64_t`、{c}`size_t`。{margin}[固定宽度有符号整数类型在 FFI 中也表示为无符号整数。]

 * {lean}`Char` 用 `uint32_t` 表示。由于 {lean}`Char` 取值不超过 21 位，所以总是无箱。

 * {lean}`Float` 由指向包含 `double` 的 Lean 对象的指针表示。

 * {deftech key:="enum inductive"}_枚举归纳类型_，即至少 2 个、且不超过 $`2^{32}` 个构造子，且构造子无参数的类型，用 {c}`uint8_t`、{c}`uint16_t`、{c}`uint32_t` 中能一一编号的最小类型表示。例如，{lean}`Bool` 用 {c}`uint8_t` 表示，{lean}`false` 为 {c}`0`，{lean}`true` 为 {c}`1`。{TODO}[需确认此处“无相关参数”描述是否准确]

 * {lean}`Decidable α` 的表示与 `Bool` 相同。{TODO}[其实 Decidable 和 Bool 只是“无参数/无相关性”规则的特例？]

 * {lean}`Nat` 和 {lean}`Int` 由 {c}`lean_object *` 表示。运行时的 {lean}`Nat` 或 {lean}`Int`，要么是指向任意精度整数对象的指针，要么（如“指针”的最低位为 1，经 {c}`lean_is_scalar` 检查）为 unbox 编码的无箱自然数或整数（相应转换用 {c}`lean_box`/{c}`lean_unbox`）。{TODO}[应移动到 FFI 章节或 Nat 章节]
:::

/-
## Relevance
%%%
tag := "inductive-types-runtime-relevance"
%%%
-/

## 相关性
%%%
tag := "inductive-types-runtime-relevance"
%%%

/-
Types and proofs have no run-time representation.
That is, if an inductive type is a `Prop`, then its values are erased prior to compilation.
Similarly, all theorem statements and types are erased.
Types with run-time representations are called {deftech}_relevant_, while types without run-time representations are called {deftech}_irrelevant_.
-/

类型和证明在运行时没有表示形式。
也就是说，若归纳类型处于 `Prop`，则其值会在编译前被抹除。
同理，所有定理的陈述和类型都会被抹除。
具有运行时表示的类型称为 {deftech key:= "relevant"}_相关类型_，反之则为 {deftech key:="irrelevant"}_无关类型_。

/-
:::example "Types are irrelevant"
Even though {name}`List.cons` has the following signature, which indicates three parameters:
```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
its run-time representation has only two, because the type argument is run-time irrelevant.
:::
-/

:::example "类型是无关的"
虽然 {name}`List.cons` 的签名表面有三个参数：
```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
但运行时实际上只有两个参数，因为类型参数是无关的，不参与运行时表示。
:::

/-
:::example "Proofs are irrelevant"
Even though {name}`Fin.mk` has the following signature, which indicates three parameters:
```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
its run-time representation has only two, because the proof is erased.
:::
-/

:::example "证明是无关的"
虽然 {name}`Fin.mk` 的签名表面有三个参数：
```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
但运行时只有两个参数，因为证明会被抹除。
:::

/-
In most cases, irrelevant values simply disappear from compiled code.
However, in cases where some representation is required (such as when they are arguments to polymorphic constructors), they are represented by a trivial value.
-/

大多数情况下，无关的值在编译后直接消失。但在少数情况下（如它们是多态构造子的参数时），需要某种“形态”时，会以简单的值表示。

/-
## Trivial Wrappers
%%%
tag := "inductive-types-trivial-wrappers"
%%%
-/

## 平凡包装类型
%%%
tag := "inductive-types-trivial-wrappers"
%%%

/-
If an inductive type has exactly one constructor, and that constructor has exactly one run-time relevant parameter, then the inductive type is represented identically to its parameter.
-/

如果归纳类型只有一个构造子，且该构造子只有一个运行时相关参数，则该归纳类型的运行时表示与其参数类型完全一致。

/-
:::example "Zero-Overhead Subtypes"
The structure {name}`Subtype` bundles an element of some type with a proof that it satisfies a predicate.
Its constructor takes four arguments, but three of them are irrelevant:
```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
Thus, subtypes impose no runtime overhead in compiled code, and are represented identically to the type of the {name Subtype.val}`val` field.
:::
-/

:::example "零负载子类型"
结构体 {name}`Subtype` 用于将某个类型的元素和满足某谓词的证明打包。
其构造子需要四个参数，但其中三个参数是无关的：

```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
因此，子类型在编译后不带来运行时额外开销，其表示和 {name Subtype.val}`val` 字段的类型完全一致。
:::

/-
:::example "Signed Integers"
The signed integer types {lean}`Int8`, ..., {lean}`Int64`, {lean}`ISize` are structures with a single field that wraps the corresponding unsigned integer type.
They are represented by the unsigned C types {c}`uint8_t`, ..., {c}`uint64_t`, {c}`size_t`, respectively, because they have a trivial structure.
:::
-/

:::example "带符号整数"
有符号整数类型 {lean}`Int8`、...、{lean}`Int64`、{lean}`ISize` 是只带唯一字段、该字段包装了对应无符号整数类型的结构体。
因此它们的表示就是无符号 C 类型 {c}`uint8_t`、...、{c}`uint64_t`、{c}`size_t`，因为结构体本身是平凡包装，不带额外信息。
:::

/-
## Other Inductive Types
%%%
tag := "inductive-types-standard-representation"
%%%
-/

## 其它归纳类型
%%%
tag := "inductive-types-standard-representation"
%%%

/-
If an inductive type doesn't fall into one of the categories above, then its representation is determined by its constructors.
Constructors without relevant parameters are represented by their index into the list of constructors, as unboxed unsigned machine integers (scalars).
Constructors with relevant parameters are represented as an object with a header, the constructor's index, an array of pointers to other objects, and then arrays of scalar fields sorted by their types.
The header tracks the object's reference count and other necessary bookkeeping.
-/

如果归纳类型不属于上述类别，则其运行时表示由其构造子结构决定。
没有相关参数的构造子，仅以在构造子列表中的索引（无箱无符号机器整数）表示。
有相关参数的构造子表示为一个对象，该对象有头部信息、构造子索引、指向其它对象的指针数组、以及按照类型分组排序的标量字段数组。
头部用来追踪引用计数以及其它记账信息。

/-
Recursive functions are compiled as they are in most programming languages, rather than by using the inductive type's recursor.
Elaborating recursive functions to recursors serves to provide reliable termination evidence, not executable code.
-/

递归函数的编译生成过程与大多数编程语言一致，并不是利用归纳类型的递归子来实现。
将递归函数翻译为递归子只是为了给出可靠的终止证据，而非用于实际执行代码。

### FFI
%%%
tag := "inductive-types-ffi"
%%%

/-
From the perspective of C, these other inductive types are represented by {c}`lean_object *`.
Each constructor is stored as a {c}`lean_ctor_object`, and {c}`lean_is_ctor` will return true.
A {c}`lean_ctor_object` stores the constructor index in its header, and the fields are stored in the {c}`m_objs` portion of the object.
Lean assumes that {c}`sizeof(size_t) == sizeof(void*)`—while this is not guaranteed by C, the Lean run-time system contains an assertion that fails if this is not the case.
-/

从 C 语言视角看，其他归纳类型统一用 {c}`lean_object *` 表示。
每个构造子的存储为一个 {c}`lean_ctor_object`，且 {c}`lean_is_ctor` 的返回值为“真”。
{c}`lean_ctor_object` 在头部存储构造子索引，各字段存放在对象中的 {c}`m_objs` 区段。Lean 假定 {c}`sizeof(size_t) == sizeof(void*)`——虽然 C 标准不保证，但 Lean 运行时包含断言，如果这一条件不满足会直接报错。

/-
The memory order of the fields is derived from the types and order of the fields in the declaration. They are ordered as follows:

* Non-scalar fields stored as {c}`lean_object *`
* Fields of type {lean}`USize`
* Other scalar fields, in decreasing order by size
-/

内存中各字段的布局由声明中的类型及声明顺序决定，排序原则如下：

* 非标量字段按 {c}`lean_object *` 存储
* 类型为 {lean}`USize` 的字段
* 其它标量字段，按大小从大到小排序

/-
Within each group the fields are ordered in declaration order. **Warning**: Trivial wrapper types still count toward a field being treated as non-scalar for this purpose.

* To access fields of the first kind, use {c}`lean_ctor_get(val, i)` to get the `i`th non-scalar field.
* To access {lean}`USize` fields, use {c}`lean_ctor_get_usize(val, n+i)` to get the {c}`i`th `USize` field and {c}`n` is the total number of fields of the first kind.
* To access other scalar fields, use {c}`lean_ctor_get_uintN(val, off)` or {c}`lean_ctor_get_usize(val, off)` as appropriate. Here `off` is the byte offset of the field in the structure, starting at {c}`n*sizeof(void*)` where `n` is the number of fields of the first two kinds.
-/

每组内部，字段顺序与声明顺序一致。**注意**：即使是“平凡包装类型”，只要包装体类型不是标量，也算作非标量字段。

* 需要访问第一类字段时，用 {c}`lean_ctor_get(val, i)` 获取第 i 个非标量字段；
* 访问 {lean}`USize` 字段时，用 {c}`lean_ctor_get_usize(val, n+i)`，其中 n 是前面所有非标量字段的数目；第 i 个 USize 字段索引为 n+i；
* 访问其它标量字段，用 {c}`lean_ctor_get_uintN(val, off)` 或 {c}`lean_ctor_get_usize(val, off)`，其中 off 是该字段在结构体中的字节偏移，从 {c}`n*sizeof(void*)`（n 为前两类字段总数）处算起。

/-
::::keepEnv

For example, a structure such as
```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
  -- wrappers don't count as scalars:
  ptr_2 : { x : UInt64 // x > 0 }
  sc64_2 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_3 : UInt64
  usize_2 : USize
  -- trivial wrapper around `UInt32`
  ptr_3 : Char
  sc32_1 : UInt32
  sc16_2 : UInt16
```
would get re-sorted into the following memory order:

* {name}`S.ptr_1` - {c}`lean_ctor_get(val, 0)`
* {name}`S.ptr_2` - {c}`lean_ctor_get(val, 1)`
* {name}`S.ptr_3` - {c}`lean_ctor_get(val, 2)`
* {name}`S.usize_1` - {c}`lean_ctor_get_usize(val, 3)`
* {name}`S.usize_2` - {c}`lean_ctor_get_usize(val, 4)`
* {name}`S.sc64_1` - {c}`lean_ctor_get_uint64(val, sizeof(void*)*5)`
* {name}`S.sc64_2` - {c}`lean_ctor_get_float(val, sizeof(void*)*5 + 8)`
* {name}`S.sc64_3` - {c}`lean_ctor_get_uint64(val, sizeof(void*)*5 + 16)`
* {name}`S.sc32_1` - {c}`lean_ctor_get_uint32(val, sizeof(void*)*5 + 24)`
* {name}`S.sc16_1` - {c}`lean_ctor_get_uint16(val, sizeof(void*)*5 + 28)`
* {name}`S.sc16_2` - {c}`lean_ctor_get_uint16(val, sizeof(void*)*5 + 30)`
* {name}`S.sc8_1` - {c}`lean_ctor_get_uint8(val, sizeof(void*)*5 + 32)`
* {name}`S.sc8_2` - {c}`lean_ctor_get_uint8(val, sizeof(void*)*5 + 33)`

::::
-/

::::keepEnv

For example, a structure such as
```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
  -- wrappers don't count as scalars:
  ptr_2 : { x : UInt64 // x > 0 }
  sc64_2 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_3 : UInt64
  usize_2 : USize
  -- trivial wrapper around `UInt32`
  ptr_3 : Char
  sc32_1 : UInt32
  sc16_2 : UInt16
```
排序后，内存布局如下：

* {name}`S.ptr_1` - {c}`lean_ctor_get(val, 0)`
* {name}`S.ptr_2` - {c}`lean_ctor_get(val, 1)`
* {name}`S.ptr_3` - {c}`lean_ctor_get(val, 2)`
* {name}`S.usize_1` - {c}`lean_ctor_get_usize(val, 3)`
* {name}`S.usize_2` - {c}`lean_ctor_get_usize(val, 4)`
* {name}`S.sc64_1` - {c}`lean_ctor_get_uint64(val, sizeof(void*)*5)`
* {name}`S.sc64_2` - {c}`lean_ctor_get_float(val, sizeof(void*)*5 + 8)`
* {name}`S.sc64_3` - {c}`lean_ctor_get_uint64(val, sizeof(void*)*5 + 16)`
* {name}`S.sc32_1` - {c}`lean_ctor_get_uint32(val, sizeof(void*)*5 + 24)`
* {name}`S.sc16_1` - {c}`lean_ctor_get_uint16(val, sizeof(void*)*5 + 28)`
* {name}`S.sc16_2` - {c}`lean_ctor_get_uint16(val, sizeof(void*)*5 + 30)`
* {name}`S.sc8_1` - {c}`lean_ctor_get_uint8(val, sizeof(void*)*5 + 32)`
* {name}`S.sc8_2` - {c}`lean_ctor_get_uint8(val, sizeof(void*)*5 + 33)`

::::

/-
::: TODO
Figure out how to test/validate/CI these statements
:::
-/

::: TODO
需要想办法对这些实现描述做测试/验证/CI
:::

/-
# Mutual Inductive Types
%%%
tag := "mutual-inductive-types"
%%%
-/

# 互递归归纳类型
%%%
file := "Mutual Inductive Types"
tag := "mutual-inductive-types"
%%%

/-
Inductive types may be mutually recursive.
Mutually recursive definitions of inductive types are specified by defining the types in a `mutual ... end` block.
-/

归纳类型之间可以互相递归。
互递归的归纳类型需在 `mutual ... end` 代码块中统一声明。

/-
:::example "Mutually Defined Inductive Types"
The type {name}`EvenOddList` in a prior example used a Boolean index to select whether the list in question should have an even or odd number of elements.
This distinction can also be expressed by the choice of one of two mutually inductive types {name}`EvenList` and {name}`OddList`:

```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean (error := true) (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
invalid dotted identifier notation, unknown identifier `OddList.nil` from expected type
  OddList String
```
:::
-/

:::example "互递归归纳类型"

在前面的例子中，类型 {name}`EvenOddList` 用 Boolean 索引来区分列表是偶数还是奇数长度。
这个区分也可以用两个互递归类型 {name}`EvenList` 和 {name}`OddList` 表达：

```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean (error := true) (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
invalid dotted identifier notation, unknown identifier `OddList.nil` from expected type
  OddList String
```
:::

/-
## Requirements
%%%
tag := "mutual-inductive-types-requirements"
%%%
-/

## 要求
%%%
tag := "mutual-inductive-types-requirements"
%%%

/-
The inductive types declared in a `mutual` block are considered as a group; they must collectively satisfy generalized versions of the well-formedness criteria for non-mutually-recursive inductive types.
This is true even if they could be defined without the `mutual` block, because they are not in fact mutually recursive.
-/

`mutual` 块中的归纳类型视为一个整体；它们必须一起满足对非互递归归纳类型良构性条件的泛化要求。
即便这些类型单独也可以用非互递归方式定义，只要它们放在 mutual 块内，也要集体满足这些要求。

/-
### Mutual Dependencies
%%%
tag := "mutual-inductive-types-dependencies"
%%%
-/

### 互相关系
%%%
tag := "mutual-inductive-types-dependencies"
%%%

/-
Each type constructor's signature must be able to be elaborated without reference to the other inductive types in the `mutual` group.
In other words, the inductive types in the `mutual` group may not take each other as arguments.
The constructors of each inductive type may mention the other type constructors in the group in their parameter types, with restrictions that are a generalization of those for recursive occurrences in non-mutual inductive types.
-/

每个类型构造子的签名必须可以脱离同组其它类型独立完成繁释。
换句话说，mutual 组内的归纳类型不得作为其它归纳类型的参数。
而各个类型的构造子可以在参数类型中引用本组的其它类型构造子，但需遵守与普通递归情形类似的（严格）限制。

/-
:::example "Mutual inductive type constructors may not mention each other"
These inductive types are not accepted by Lean:
```lean (error:=true) (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh (r : α → FreshList α → Prop) : α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

The type constructors may not refer to the other type constructors in the `mutual` group, so `FreshList` is not in scope in the type constructor of `Fresh`:
```leanOutput mutualNoMention
unknown identifier 'FreshList'
```
:::
-/

:::example "类型构造子之间不能互相引用"
下述归纳类型 Lean 不接受：
```lean (error:=true) (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh (r : α → FreshList α → Prop) : α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

类型构造子不能出现在同组另一个归纳类型的签名中，所以 `FreshList` 在 `Fresh` 的类型构造子中不可见：
```leanOutput mutualNoMention
unknown identifier 'FreshList'
```
:::

/-
### Parameters Must Match
%%%
tag := "mutual-inductive-types-same-parameters"
%%%
-/

### 参数必须匹配
%%%
tag := "mutual-inductive-types-same-parameters"
%%%

/-
All inductive types in the `mutual` group must have the same {tech}[parameters].
Their indices may differ.
-/

同一个 mutual 组中的所有归纳类型，{tech key := "parameter"}[参数] 必须类型完全一致。
索引可以不同。


/-
::::keepEnv
::: example "Differing numbers of parameters"
Even though `Both` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters:
```lean (name := bothOptional) (error := true)
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
invalid inductive type, number of parameters mismatch in mutually inductive datatypes
```
:::
::::
-/

::::keepEnv
::: example "参数类型不一致"
即便 `Many` 和 `OneOf` 之间不存在互递归，只要在同一个 mutual 块声明，也必须参数类型完全一样。两者参数数目一致，但 `Many` 的参数可能不在 `Optional` 的宇宙层级：

```lean (name := bothOptional) (error := true)
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
invalid inductive type, number of parameters mismatch in mutually inductive datatypes
```
:::
::::

/-
::::keepEnv
::: example "Differing parameter types"
Even though `Many` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters.
They both have exactly one parameter, but `Many`'s parameter is not necessarily in the same universe as `Optional`'s:
```lean (name := manyOptional) (error := true)
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
invalid mutually inductive types, parameter 'α' has type
  Type u : Type (u + 1)
but is expected to have type
  Type : Type 1
```
:::
::::
-/

::::keepEnv
::: example "参数类型不一致"
即便 `Many` 和 `OneOf` 之间不存在互递归，只要在同一个 mutual 块声明，也必须参数类型完全一样。
两者参数数目一致，但 `Many` 的参数可能不在 `Optional` 的宇宙层级：
```lean (name := manyOptional) (error := true)
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
invalid mutually inductive types, parameter 'α' has type
  Type u : Type (u + 1)
but is expected to have type
  Type : Type 1
```
:::
::::

/-
### Universe Levels
%%%
tag := "mutual-inductive-types-same-universe"
%%%
-/
### 宇宙层级
%%%
tag := "mutual-inductive-types-same-universe"
%%%

/-
The universe levels of each inductive type in a mutual group must obey the same requirements as non-mutually-recursive inductive types.
Additionally, all the inductive types in a mutual group must be in the same universe, which implies that their constructors are similarly limited with respect to their parameters' universes.
-/

互递归组中每个归纳类型的宇宙层级，同样需满足非互递归归纳类型的宇宙要求。
另外，所有 mutual 组的类型必须位于同一宇宙，这意味着它们的构造子的参数也要受宇宙层级统一的限制。

/-
::::example "Universe mismatch"
:::keepEnv
These mutually-inductive types are a somewhat complicated way to represent run-length encoding of a list:
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```

Specifying {name}`PrefixRunOf` as a {lean}`Prop` would be sensible, but it cannot be done because the types would be in different universes:
:::

:::keepEnv
```lean (error :=true) (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
invalid mutually inductive types, resulting universe mismatch, given
  Prop
expected type
  Type
```
:::

:::keepEnv
This particular property can be expressed by separately defining the well-formedness condition and using a subtype:
```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
:::
::::
-/

::::example "宇宙层级不一致"
:::keepEnv
这些互递归类型可以表示列表的行程编码（run-length encoding）：
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```

若将 {name}`PrefixRunOf` 声明为 {lean}`Prop` 会更有意义，但类型因此不在同一宇宙，导致无法通过类型检查：
:::

:::keepEnv
```lean (error :=true) (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
invalid mutually inductive types, resulting universe mismatch, given
  Prop
expected type
  Type
```
:::

:::keepEnv
这里也可以将性质单独定义，再通过子类型表达：
```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
:::
::::

/-
### Positivity
%%%
tag := "mutual-inductive-types-positivity"
%%%
-/

### 正性条件(Positivity)
%%%
tag := "mutual-inductive-types-positivity"
%%%

/-
Each inductive type that is defined in the `mutual` group may occur only strictly positively in the types of the parameters of the constructors of all the types in the group.
In other words, in the type of each parameter to each constructor in all the types of the group, none of the type constructors in the group occur to the left of any arrows, and none of them occur in argument positions unless they are an argument to an inductive type's type constructor.
-/

互递归组中各归纳类型只能“严格正”地出现在所有构造子参数的类型表达式中。
即，对于所有类型的所有构造子的每个参数类型，互递归组内的类型构造子不能出现在任何函数箭头左边，也不能出现在参数位置，除非它正好是某个归纳类型类型构造子的参数。

/-
::: example "Mutual strict positivity"
In the following mutual group, `Tm` occurs in a negative position in the argument to `Binding.scope`:
```lean (error := true) (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
Because `Tm` is part of the same mutual group, it must occur only strictly positively in the arguments to the constructors of `Binding`.
It occurs, however, negatively:
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
:::
-/

::: example "互递归条件下的严格正性"
如下 mutual 组中，`Tm` 在 `Binding.scope` 的参数类型里出现了负位置：
```lean (error := true) (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
由于 `Tm` 属于同一个互递归组，故只能严格正性出现。实际却出现在负位置：
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
:::

::: example "嵌套位置"
{name}`LocatedStx` 和 {name}`Stx` 这组互递归类型，递归出现均不在箭头左侧，且作为归纳类型类型构造子的参数，有严格正性：
```lean
mutual
  inductive LocatedStx where
    | mk (line col : Nat) (val : Stx)
  inductive Stx where
    | atom (str : String)
    | node (kind : String) (args : List LocatedStx)
end
```
:::

/-
## Recursors
%%%
tag := "mutual-inductive-types-recursors"
%%%
-/

## 递归子
%%%
tag := "mutual-inductive-types-recursors"
%%%

/-
Mutual inductive types are provided with primitive recursors, just like non-mutually-defined inductive types.
These recursors take into account that they must process the other types in the group, and thus will have a motive for each inductive type.
Because all inductive types in the `mutual` group are required to have identical parameters, the recursors still take the parameters first, abstracting them over the motives and the rest of the recursor.
Additionally, because the recursor must process the group's other types, it will require cases for each constructor of each of the types in the group.
The actual dependency structure between the types is not taken into account; even if an additional motive or constructor case is not really required due to there being fewer mutual dependencies than there could be, the generated recursor still requires them.
-/

互递归归纳类型和非互递归归纳类型一样，都提供了原语递归子。
这些递归子会考虑到需要处理组内的其他类型，因此每个归纳类型都会有一个目标参数。
由于在 `mutual` 组中的所有归纳类型都被要求有相同的参数，递归子依然会首先接收这些参数，并将它们抽象到目标参数和递归子的其余部分上。
此外，因为递归子必须处理组内的其他类型，所以它还需要为组内每个类型的每个构造子提供分支。
实际上，类型之间具体的依赖关系在这里没有被考虑；即使由于互递归依赖关系较少，某些目标参数或构造子分支实际上并非必须，生成的递归子依旧会要求这些内容。

/-
::::keepEnv
::: example "Even and odd"
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```

```signature
Even.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : {n : Nat} → (a : Odd n) → motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) →
  ∀ {a : Nat} (t : Even a), motive_1 a t
```

```signature
Odd.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : ∀ {n : Nat} (a : Odd n), motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) → ∀ {a : Nat} (t : Odd a), motive_2 a t
```

:::
::::
-/

::::keepEnv
::: example "偶数与奇数"
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```

```signature
Even.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : {n : Nat} → (a : Odd n) → motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) →
  ∀ {a : Nat} (t : Even a), motive_1 a t
```

```signature
Odd.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : ∀ {n : Nat} (a : Odd n), motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) → ∀ {a : Nat} (t : Odd a), motive_2 a t
```

:::
::::

/-
::::keepEnv
:::example "Spuriously mutual types"
The types {name}`Two` and {name}`Three` are defined in a mutual block, even though they do not refer to each other:
```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
```
{name}`Two`'s recursor, {name}`Two.rec`, nonetheless requires a motive and a case for {name}`Three`:
```signature
Two.rec.{u} {α : Type}
  {motive_1 : Two α → Sort u}
  {motive_2 : Three α → Sort u}
  (mk : (a a_1 : α) → motive_1 (Two.mk a a_1)) :
  ((a a_1 a_2 : α) → motive_2 (Three.mk a a_1 a_2)) → (t : Two α) → motive_1 t
```

:::
::::
-/

::::keepEnv
:::example "表面互递归类型"
类型 {name}`Two` 和 {name}`Three` 其实互不引用，却作为一个 mutual 组共同声明：
```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
```
{name}`Two` 的递归子 {name}`Two.rec` 依然需要 motive 以及 {name}`Three` 的分支：
```signature
Two.rec.{u} {α : Type}
  {motive_1 : Two α → Sort u}
  {motive_2 : Three α → Sort u}
  (mk : (a a_1 : α) → motive_1 (Two.mk a a_1)) :
  ((a a_1 a_2 : α) → motive_2 (Three.mk a a_1 a_2)) → (t : Two α) → motive_1 t
```

:::
::::

/-
## Run-Time Representation
%%%
tag := "mutual-inductive-types-run-time"
%%%
-/

## 运行时表示
%%%
tag := "mutual-inductive-types-run-time"
%%%

/-
Mutual inductive types are represented identically to {ref "run-time-inductives"}[non-mutual inductive types] in compiled code and in the runtime.
The restrictions on mutual inductive types exist to ensure Lean's consistency as a logic, and do not impact compiled code.
-/

互递归归纳类型在编译后及运行期的表示，与 {ref "run-time-inductives"}[非互递归归纳类型] 完全一致。
对于互递归归纳类型的限制，是为了保证 Lean 作为一种逻辑的可靠性，不影响实际代码的编译与运行。


{include 2 Manual.Language.InductiveTypes.Nested}
