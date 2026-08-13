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


#doc (Manual) "归纳类型" =>
%%%
file :=  "Inductive Types"
tag := "inductive-types"
%%%


{deftech (key := "inductive types")}_归纳类型_ 是在 Lean 中引入新类型的主要方式。
虽然 {tech (key := "universes")}[宇宙]、{tech (key := "functions")}[函数] 以及 {tech (key := "quotient types")}[商类型] 是内置的原语类型，用户无法自行添加，但 Lean 里的其它类型要么是归纳类型，要么是基于宇宙、函数与归纳类型定义的。
归纳类型的定义依赖于它们的 {deftech (key := "type constructor")}_类型构造子_ 和 {deftech (key := "constructor")}_构造子_ ；{index}[constructor]它们的其它性质也由这些定义推导而来。
每个归纳类型有唯一的类型构造子，这个构造子可能带有 {tech (key := "universe parameter")}[宇宙参数] 和普通参数。
归纳类型可以拥有任意数量的构造子；这些构造子用于生成新的值，其类型由归纳类型的类型构造子决定。




根据归纳类型的类型构造子和构造子，Lean 会自动生成一个 {deftech (key := "recursor")}_递归子_{index}[递归子]{see "recursor"}[消去子]。
从逻辑上讲，递归子代表归纳原则或消去规则；从计算角度看，它们表示原始递归计算。
递归函数的终止性由其翻译为递归子的调用来保证，因此 Lean 的内核只需对递归子的应用做类型检查，而无需单独进行终止性分析。
除此之外，Lean 还根据递归子生成很多辅助结构{margin}[无论类型是否递归，递归子总会被用到]，这些结构被系统的其他部分使用。


_结构体_ 是一种特殊的归纳类型，只包含一个构造子。
当一个结构体被声明时，Lean 会自动生成辅助工具，使得新结构体能支持更多语言特性。

本节描述用于定义归纳类型和结构体的具体语法细节、归纳类型声明会在环境中引入哪些新的常量和定义，以及在编译后归纳类型值的运行时表现。



# 归纳类型声明
%%%
file := "Inductive Type Declarations"
tag := "inductive-declarations"
%%%


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



声明归纳类型后，其类型构造子、构造子和递归子会添加到环境中。
新的归纳类型扩展了 Lean 的核心逻辑——它们不是由系统中已有的数据编码或模拟出来的。
归纳类型声明还必须满足一系列 {ref "well-formed-inductives"}[良构性要求] 以确保逻辑系统的一致性。


The new inductive type's name is defined in the {tech}[current namespace].
Each constructor's name is in the inductive type's namespace.{index (subterm := "of inductive type")}[namespace]



构造子定义在 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`后边。
构造子并非必需，比如像 {lean}`False` 和 {lean}`Empty` 这样没有构造子的归纳类型是完全合理的。
每个构造子定义以竖线 (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`)、声明修饰词和名字。
名字是 {tech (key := "raw identifier")}[原始标识符]。
名字后接声明签名。
签名可以包含任意参数，但需满足归纳类型声明的良构性要求，返回类型必须是归纳类型的类型构造子的饱和应用。
如果未指定签名，则 Lean 会插入足够的隐式参数来推断出良构的返回类型。

新归纳类型的名字定义在{tech (key := "current namespace")}[当前命名空间]中。
每个构造子的名字位于该归纳类型的命名空间下。{index (subterm := "of inductive type")}[namespace]


## 参数与索引
%%%
tag := "inductive-datatypes-parameters-and-indices"
%%%


类型构造子可以接收两类参数：{deftech (key := "parameters")}_参数_ {index (subterm := "of inductive type")}[parameter] 和 {deftech (key := "index")}_索引_ {index (subterm := "of inductive type")}[index]。
定义中，参数必须在整个归纳类型定义中保持一致；所有构造子中出现的类型构造子，参数必须一模一样。
索引则可以在不同构造子的类型构造子的具体应用中变化。
所有参数在类型构造子的签名中必须排在索引的前面。


在类型构造子的签名中冒号（`':'`）之前的内容作为整个归纳类型声明的参数，
这些参数在类型定义过程中始终如一。
通常，冒号之后为索引，可以在归纳类型定义中变化。
但如果 {option}`inductive.autoPromoteIndices` 选项为 {lean}`true`，则本来可以作为参数的语法层面的索引会被自动提升为参数。
当一个索引的所有类型依赖全都是参数类型，且它在所有构造子的类型构造子调用中始终未实例化、未变化，那么它就可以被当作参数。


索引实际上定义了一个_类型族_。
每次索引取值确定，就从族中选出一个类型，该类型有它各自的构造子。
含索引的类型构造子即定义了一个 {deftech (key := "indexed family")}_索引族_ {index (subterm := "of types")}[带索引类型族]。


## 归纳类型样例
%%%
tag := "example-inductive-types"
%%%

:::example "一个没有构造子的类型"
{lean}`Vacant` 是一个空的归纳类型，等价于 Lean 的 {lean}`Empty` 类型：
```lean
inductive Vacant : Type where
```

空归纳类型并非毫无用处；它们可以用于标记不可达代码。
:::


:::example "一个没有构造子的命题"
{lean}`No` 是一个假命题，等价于 Lean 的 {lean}`False`:
```lean
inductive No : Prop where
```

```lean -show -keep
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
:::


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
The constructor is named {lean}`Solo.solo`, because constructor names are in the type constructor's namespace.
Because {lean}`Solo` expects no arguments, the signature inferred for {lean}`Solo.solo` is:

```lean (name := oneTy)
#check Solo.solo
```
```leanOutput oneTy
Solo.solo : Solo
```
:::



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

```lean -show -keep
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
:::


::::example "一个带参数和索引的类型" (keep := true)

:::keepEnv
```lean -show
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

This example is not well typed because there are three entries in the list:
```lean +error (name := evenOddOops)

example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
Type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true
but is expected to have type
  EvenOddList String true
```

:::keepEnv
```lean -show
universe u
axiom α : Type u
axiom b : Bool
```
在本声明中，{lean}`α` 是 {tech (key := "parameter")}[参数]，
因为它在 {name}`EvenOddList` 的每次出现都保持一致；{lean}`b` 是 {tech (key := "index")}[索引]，因为它在不同出现中可取不同值。
:::


```lean -show -keep
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


:::::keepEnv
::::example "参数在冒号前和冒号后"

在本例中，所有参数都在 {name}`Either` 签名的冒号前：

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β
```

In this version, there are two types named `α` that might not be identical:
```lean (name := Either') +error

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

Note: The value of parameter `α✝` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

把参数放在冒号后，则对应的构造子参数可以由构造子自行实例化：
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v + 1) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : β → Either'' α β
```
此时需要更大的宇宙层级，因为 {ref "inductive-type-universe-levels"}[构造子的参数必须处于比归纳类型本身更低的宇宙]。
{name}`Either''.right` 的类型参数会按 Lean 的 {tech (key := "automatic implicit parameters")}[自动隐式参数] 规则推断。
::::
:::::


## 匿名构造子语法
%%%
file := "Anonymous Constructor Syntax"
tag := "anonymous-constructor-syntax"
%%%


如果归纳类型只有一个构造子，则这个构造子可以使用 {deftech (key := "anonymous constructor syntax")}_匿名构造子语法_。
即，不必写出构造子的名字并将其应用到参数上，而直接把所有显式参数用尖括号（`'⟨'` 和 `'⟩'`, Unicode `MATHEMATICAL LEFT ANGLE BRACKET (U+0x27e8)` 和 `MATHEMATICAL RIGHT ANGLE BRACKET (U+0x27e9)`）括起来，并用逗号分隔即可。
这种语法可以用于模式匹配和表达式。
若想按照参数名字提供参数，或将所有隐式参数变为显式，则需使用普通构造子语法。


:::syntax term (title := "匿名构造子")
可通过用尖括号括起所有显式参数并用逗号分隔，匿名地调用构造子。
```grammar
⟨ $_,* ⟩
```
:::


::::example "匿名构造子"

:::keepEnv
```lean -show
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



## 派生实例
%%%
tag := "inductive-declarations-deriving-instances"
%%%


归纳类型声明末尾可选的 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` 子句，可用于自动派生类型类实例。
详情请见 {ref "deriving-instances"}[关于实例自动派生的章节]。

{include 0 Manual.Language.InductiveTypes.Structures}

{include 0 Manual.Language.InductiveTypes.LogicalModel}


# 运行时表示
%%%
file := "Run-Time Representation"
tag := "run-time-inductives"
%%%


归纳类型的运行时表示取决于构造子的数量、每个构造子参数的数量，以及参数是否 {tech (key := "relevant")}[相关]。


## 特例
%%%
tag := "inductive-types-runtime-special-support"
%%%

并非所有归纳类型都采用这里描述的表示——部分归纳类型由 Lean 编译器特别支持：


:::keepEnv
```lean -show
axiom α : Prop
```

 * The representation of the fixed-width integer types {lean}`UInt8`, …, {lean}`UInt64`, {lean}`Int8`, …, {lean}`Int64`, and {lean}`USize` depends on whether the code is compiled for a 32- or 64-bit architecture.
  Their representation is described {ref "fixed-int-runtime"}[in a dedicated section].


 * {lean}`Char` 用 `uint32_t` 表示。由于 {lean}`Char` 取值不超过 21 位，所以总是无箱。

 * {lean}`Float` is represented by a pointer to a Lean object that contains a “double”.

 * An {deftech}_enum inductive_ type of at least 2 and at most $`2^{32}` constructors, each of which has no parameters, is represented by the first type of {C}`uint8_t`, {C}`uint16_t`, {C}`uint32_t` that is sufficient to assign a unique value to each constructor. For example, the type {lean}`Bool` is represented by {C}`uint8_t`, with values {C}`0` for {lean}`false` and {C}`1` for {lean}`true`. {TODO}[Find out whether this should say “no relevant parameters”]

 * {lean}`Decidable α` is represented the same way as `Bool` {TODO}[Aren't Decidable and Bool just special cases of the rules for trivial constructors and irrelevance?]

 * {lean}`Nat` and {lean}`Int` are represented by {C}`lean_object *`.
  Their representations are described in more detail in {ref "nat-runtime"}[the section on natural numbers] and {ref "int-runtime"}[the section on integers].
:::


## 相关性
%%%
tag := "inductive-types-runtime-relevance"
%%%


类型和证明在运行时没有表示形式。
也就是说，若归纳类型处于 `Prop`，则其值会在编译前被抹除。
同理，所有定理的陈述和类型都会被抹除。
具有运行时表示的类型称为 {deftech (key := "relevant")}_相关类型_，反之则为 {deftech (key := "irrelevant")}_无关类型_。


:::example "类型是无关的"
虽然 {name}`List.cons` 的签名表面有三个参数：
```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
但运行时实际上只有两个参数，因为类型参数是无关的，不参与运行时表示。
:::


:::example "证明是无关的"
虽然 {name}`Fin.mk` 的签名表面有三个参数：
```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
但运行时只有两个参数，因为证明会被抹除。
:::


大多数情况下，无关的值在编译后直接消失。但在少数情况下（如它们是多态构造子的参数时），需要某种“形态”时，会以简单的值表示。


## 平凡包装类型
%%%
tag := "inductive-types-trivial-wrappers"
%%%

:::paragraph
An inductive type is a {deftech}[trivial wrapper] if it has has exactly one constructor and that constructor has exactly one run-time relevant parameter.
Trivial wrappers are represented identically to their constructor's parameter in the following circumstances:

 * The inductive type is private.

 * The type is public, and the {tech}[public scope] of the module in which it is defined contains enough information to determine that it is a trivial wrapper.

 * The type is defined in a source file that is not a {tech}[module].

:::


如果归纳类型只有一个构造子，且该构造子只有一个运行时相关参数，则该归纳类型的运行时表示与其参数类型完全一致。


:::example "零负载子类型"
结构体 {name}`Subtype` 用于将某个类型的元素和满足某谓词的证明打包。
其构造子需要四个参数，但其中三个参数是无关的：

```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
因此，子类型在编译后不带来运行时额外开销，其表示和 {name Subtype.val}`val` 字段的类型完全一致。
:::

:::example "Signed Integers"
The signed integer types {lean}`Int8`, ..., {lean}`Int64`, {lean}`ISize` are structures with a single field that wraps the corresponding unsigned integer type.
They are represented by the unsigned C types {C}`uint8_t`, ..., {C}`uint64_t`, {C}`size_t`, respectively, because they have a trivial structure.

:::


## 其它归纳类型
%%%
tag := "inductive-types-standard-representation"
%%%


如果归纳类型不属于上述类别，则其运行时表示由其构造子结构决定。
没有相关参数的构造子，仅以在构造子列表中的索引（无箱无符号机器整数）表示。
有相关参数的构造子表示为一个对象，该对象有头部信息、构造子索引、指向其它对象的指针数组、以及按照类型分组排序的标量字段数组。
头部用来追踪引用计数以及其它记账信息。


递归函数的编译生成过程与大多数编程语言一致，并不是利用归纳类型的递归子来实现。
将递归函数翻译为递归子只是为了给出可靠的终止证据，而非用于实际执行代码。

### FFI
%%%
tag := "inductive-types-ffi"
%%%

From the perspective of C, these other inductive types are represented by {C}`lean_object *`.
Each constructor is stored as a {C}`lean_ctor_object`, and {C}`lean_is_ctor` will return true.


There are no guarantees about the exact layout of fields in a constructor object; the compiler is free to select any layout.
Thus, constructor objects should only be created or unpacked by functions defined in Lean code.
These functions can be made available to C via the {attr}`export` attribute.
Because the resulting C and Lean code call symbols defined in each other, they should be linked together.
Each C should be compiled to an object file using a custom target in Lake and added to the Lean library configuration's {tomlField Lake.LeanLibConfig}`moreLinkObjs` field.

# 互递归归纳类型
%%%
file := "Mutual Inductive Types"
tag := "mutual-inductive-types"
%%%


归纳类型之间可以互相递归。
互递归的归纳类型需在 `mutual ... end` 代码块中统一声明。


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
```lean +error (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
Unknown constant `OddList.nil`

Note: Inferred this name from the expected resulting type of `.nil`:
  OddList String
```
:::


## 要求
%%%
tag := "mutual-inductive-types-requirements"
%%%


`mutual` 块中的归纳类型视为一个整体；它们必须一起满足对非互递归归纳类型良构性条件的泛化要求。
即便这些类型单独也可以用非互递归方式定义，只要它们放在 mutual 块内，也要集体满足这些要求。


### 互相关系
%%%
tag := "mutual-inductive-types-dependencies"
%%%


:::example "Mutual inductive type constructors may not mention each other"
These inductive types are not accepted by Lean:
```lean +error (name := mutualNoMention)

mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh
      (r : α → FreshList α → Prop) :
      α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

类型构造子不能出现在同组另一个归纳类型的签名中，所以 `FreshList` 在 `Fresh` 的类型构造子中不可见：
```leanOutput mutualNoMention
Unknown identifier `FreshList`
```
:::


### 参数必须匹配
%%%
tag := "mutual-inductive-types-same-parameters"
%%%


同一个 mutual 组中的所有归纳类型，{tech (key := "parameter")}[参数] 必须类型完全一致。
索引可以不同。



::::keepEnv
::: example "Differing numbers of parameters"
Even though `Both` and `Optional` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters:
```lean (name := bothOptional) +error

mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
Invalid mutually inductive types: `Optional` has 1 parameter(s), but the preceding type `Both` has 2

Note: All inductive types declared in the same `mutual` block must have the same parameters
```
:::
::::


::::keepEnv
::: example "Differing parameter types"
Even though `Many` and `Optional` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters.
They both have exactly one parameter, but `Many`'s parameter is not necessarily in the same universe as `Optional`'s:
```lean (name := manyOptional) +error

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
Invalid mutually inductive types: Parameter `α` has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
```
:::
::::

### 宇宙层级
%%%
tag := "mutual-inductive-types-same-universe"
%%%


互递归组中每个归纳类型的宇宙层级，同样需满足非互递归归纳类型的宇宙要求。
另外，所有 mutual 组的类型必须位于同一宇宙，这意味着它们的构造子的参数也要受宇宙层级统一的限制。


::::example "宇宙层级不一致"
:::keepEnv
这些互递归类型可以表示列表的行程编码（run-length encoding）：
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
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
```lean +error (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run
    (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys →
    RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
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


### 正性条件(Positivity)
%%%
tag := "mutual-inductive-types-positivity"
%%%


::: example "Mutual strict positivity"
In the following mutual group, `Tm` occurs in a negative position in the argument to `Binding.scope`:
```lean +error (name := mutualHoas)

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


## 递归子
%%%
tag := "mutual-inductive-types-recursors"
%%%


互递归归纳类型和非互递归归纳类型一样，都提供了原语递归子。
这些递归子会考虑到需要处理组内的其他类型，因此每个归纳类型都会有一个目标参数。
由于在 `mutual` 组中的所有归纳类型都被要求有相同的参数，递归子依然会首先接收这些参数，并将它们抽象到目标参数和递归子的其余部分上。
此外，因为递归子必须处理组内的其他类型，所以它还需要为组内每个类型的每个构造子提供分支。
实际上，类型之间具体的依赖关系在这里没有被考虑；即使由于互递归依赖关系较少，某些目标参数或构造子分支实际上并非必须，生成的递归子依旧会要求这些内容。


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


## 运行时表示
%%%
tag := "mutual-inductive-types-run-time"
%%%


互递归归纳类型在编译后及运行期的表示，与 {ref "run-time-inductives"}[非互递归归纳类型] 完全一致。
对于互递归归纳类型的限制，是为了保证 Lean 作为一种逻辑的可靠性，不影响实际代码的编译与运行。


{include 2 Manual.Language.InductiveTypes.Nested}

## Lattice-Theoretic Inductive and Coinductive Predicates

The syntax of inductive type declarations can be used to specify both inductive and coinductive predicates.
These are not a built-in feature of Lean's type system, but are instead elaborated to a suitable encoding.
They are described in {ref "coinductive-predicates"}[a dedicated section].
