/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Papers
import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Language.InductiveTypes.LogicalModel


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800


#doc (Manual) "逻辑模型" =>
%%%
file := "Logical Model"
tag := "inductive-types-logical-model"
%%%



# 递归子
%%%
file := "Recursors"
tag := "recursors"
%%%


每一个归纳类型都拥有一个{tech (key := "recursor")}[递归子]。
递归子的定义完全由类型构造子和数据构造子的类型签名所决定。
递归子的类型是函数类型，但它们是原语级别的，不能用 `fun` 来定义。


## 递归子类型
%%%
tag := "recursor-types"
%%%


:::paragraph
递归子接收以下参数：
: 归纳类型的{tech (key := "parameters")}[参数]

  由于参数在整个定义中保持一致，因此递归子可以统一对这些参数进行抽象。


: {deftech (key := "motive")}_动机_(motive)

  动机决定了递归子的应用结果的类型。动机是一个函数，其参数是类型的指标及其具体实例。动机决定的类型所处的具体宇宙由归纳类型的宇宙层级和具体的数据构造子决定——详见{ref "subsingleton-elimination"}[{tech (key := "subsingleton")}[子单元] 消去]部分。

: 每个构造子的{deftech (key := "minor premise")}_次要前提_(minor premise)

  对每个构造子，递归子都要求一个函数，证明动机对该构造子的任意应用成立。
  每个次要前提都会对该构造子的所有参数进行抽象。
  如果构造子的某个参数类型就是该归纳类型本身，那么次要前提还会接收一个额外参数，其类型是动机应用于该参数值的结果；它将接收递归处理这一递归参数所得的结果。


: {deftech (key := "major premise")}_主要前提_，或称 目标

  最后，递归子接收一个该类型的实例作为参数，以及所有指标的值。

递归子的结果类型是将动机应用于这些指标和主要前提所得的类型。

:::


:::example "{lean}`Bool` 的递归子"
{lean}`Bool` 的递归子 {name}`Bool.rec` 有如下参数：

 * 动机给定一个 {lean}`Bool` 后，在任意宇宙中计算出一个类型。
 * 两个构造子各有一个次要前提，分别说明动机对 {lean}`false` 和 {lean}`true` 成立。
 * 主要前提是某个 {lean}`Bool`。

返回类型是动机应用于主要前提所得的类型。


```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
:::


::::example "{lean}`List` 的递归子"
{lean}`List` 的递归子 {name}`List.rec` 有如下参数：

:::keepEnv
```lean -show
axiom α.{u} : Type u
```

 * 参数 {lean}`α` 位于最前，因为动机、次要前提和主要前提都需要引用它。
 * 动机给定一个 {lean}`List α` 后，在任意宇宙中计算出一个类型；宇宙层级 `u` 与 `v` 彼此无关。
 * 两个构造子各有一个次要前提：
    - 动机对 {name}`List.nil` 成立；
    - 对 {name}`List.cons` 的任意应用，只要动机对尾部成立，就应对整个列表成立。额外参数 `motive tail` 来自 `tail` 的类型中对 {name}`List` 的递归出现。
 * 主要前提是某个 {lean}`List α`。
:::

同样，返回类型是动机应用于主要前提所得的类型。


```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
::::


:::::keepEnv
::::example "带参数和指标的递归子"
已知 {name}`EvenOddList` 的定义如下：
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


递归子 {name}`EvenOddList.rec` 与 {name}`List.rec` 十分相似，差别来自指标：
 * 动机会对任意选择的指标进行抽象。
 * {name EvenOddList.nil}`nil` 的次要前提把动机应用于该构造子的指标值 `true`。
 * {name EvenOddList.cons}`cons` 的次要前提对递归出现中使用的指标值进行抽象，并用其否定值实例化动机。
 * 主要前提也会对任意选择的指标进行抽象。


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

当动机是一个返回 {lean}`Prop` 的谓词时，递归子就表现为归纳法。
非递归构造子的分支是归纳的基本样例，而递归构造子所额外提供的参数就是归纳假设。


### 子单元消去
%%%
tag := "subsingleton-elimination"
%%%


Lean 中的证明是计算无关的。
换句话说，在给定了*某个*命题的证明之后，程序应该无法检测到*到底是哪一个*证明被接受了。
这种思想体现在归纳定义的命题或谓词的递归子的类型中。
对于这些类型，如果定理存在多种可能的证明方式，那么 motive 只能返回另一个 {lean}`Prop`。
如果类型的结构保证了至多只存在一个证明，那么 motive 可以返回任意宇宙中的类型。
拥有至多一个元素的命题被称为 {deftech (key := "subsingleton")}_子单元_。
Lean 并不会强制用户去*证明*某命题只有唯一的证明，而是采用了一种保守的语法近似方法来检测一个命题是否为子单元。
满足以下两个条件的命题会被视为子单元（subsingleton）：
 * 至多只有一个构造子。
 * 每个构造子的参数类型要么是 {lean}`Prop`，要么是参数或者索引。


:::example "{lean}`True` 是子单元"
{lean}`True` 是子单元，因为它仅有一个无参数的构造子。
它的递归子类型如下：
```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
:::


:::example "{lean}`False` 是子单元"
{lean}`False` 是子单元，因为它没有构造子。
它的递归子类型如下：
```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
注意动机是一个显式参数。
因为它在后续参数类型中没有出现，因此不能自动推断它。
:::


:::example "{name}`And` 是子单元"
{lean}`And` 是子单元，因为它仅有一个构造子，并且这个构造子的两个参数类型都是命题。
它的递归子类型如下：
```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
:::


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


## 规约
%%%
tag := "iota-reduction"
%%%


归纳类型声明除了为逻辑添加新常量外，还会引入新的规约规则。
这些规则负责处理递归子与构造子之间的互动，尤其是以构造子为主要前提的递归子应用。
这种规约形式称为 {deftech (key := "ι-reduction")}_ι-规约_（iota reduction）{index}[ι-规约]{index (subterm:="ι (iota)")}[规约]。

当递归子的主要前提是没有递归参数的构造子时，递归子应用会规约为将该构造子的次要前提应用于构造子的参数。
如果存在递归参数，则传给次要前提的对应参数由递归子应用于递归出现而得到。


# 良构性约束
%%%
file := "Well-Formedness Requirements"
tag := "well-formed-inductives"
%%%


归纳类型声明需要满足一系列良构性约束。
这些约束确保当逻辑扩展进入新的归纳类型规则时，Lean 的逻辑系统依然保持一致。
这些约束是保守的：一些不会破坏一致性的归纳类型会被这些约束拒绝。


## 宇宙层级
%%%
tag := "inductive-type-universe-levels"
%%%


归纳类型的类型构造子必须处于某个{tech (key := "universe")}[宇宙]中，或是返回类型为宇宙的函数类型。
每个数据构造子的类型必须是返回饱和应用归纳类型的函数类型。
如果归纳类型的宇宙是 {lean}`Prop`，则对宇宙没有进一步的限制，因为 {lean}`Prop` 是{tech (key := "impredicative")}[非直谓的]。
如果宇宙不是 {lean}`Prop`，那么以下要求必须成立，对每一个数据构造子的参数都适用：
 * 若构造子的参数是归纳类型的参数（即参数 vs 索引），则该参数类型不能超过类型构造子的宇宙层级。
 * 其它所有构造子参数的类型都必须严格小于类型构造子的宇宙层级。


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


## 严格正性
%%%
tag := "strict-positivity"
%%%


所有定义中的类型在构造子参数类型中的出现都必须处于{deftech (key := "strictly positive")}_严格正性_的位置。
如果一个类型不处于函数的参数类型里（无论嵌套了多少层函数类型），也不作为任何表达式（除归纳类型的类型构造子外）的参数，那它就是严格正性的位置。
该限制用来排除不安全的归纳类型定义，虽有可能因此排除掉某些良构类型。


:::::example "非严格正性的归纳类型"
::::keepEnv
:::keepEnv
如果不拒绝类型 `Bad`，它会导致 Lean 不一致：
```lean (name := Bad) +error

inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
:::

:::keepEnv
```lean -show
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
之所以这样，是因为如果假定 {lean}`Bad` 成立，则可以构造出环状逻辑从而证明 {lean}`False`。
{lean}`Bad.bad` 会被拒绝，是因为构造子的参数类型是 {lean}`Bad → Bad`，也就是 {lean}`Bad` 作为函数参数出现。
:::

:::keepEnv
下面这个不动点算子的声明会被拒绝，因为 `Fix` 作为参数出现在 `f` 中：
```lean (name := Fix) +error

inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
:::

`Fix.fix` 会被拒绝，因为 `f` 不是归纳类型的类型构造子，而 `Fix` 本身却作为它的参数出现。
在这种情况下，`Fix` 也足以构造一个等价于 `Bad` 的类型：
```lean -show

axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
::::
:::::


## Prop vs Type
%%%
tag := "prop-vs-type"
%%%


Lean 会拒绝那些实际上无法多态使用的宇宙多态类型。
例如，如果对宇宙参数的部分实例化会导致类型变成 {lean}`Prop`，而该类型又不是{tech (key := "subsingleton")}[子单元]，则其递归子只允许针对命题（即{tech (key := "motive")}[动机]只能返回 {lean}`Prop`）。
这些类型实际上只适合充当 {lean}`Prop` 本身，所以宇宙多态很可能本就是错误。
由于这种类型几乎无实际意义，Lean 的归纳类型{tech (key := "elaborator")}[精译器]并未设计为支持它们。


如果这种宇宙多态归纳类型本身是子单元，则这样的定义还是有意义的。
Lean 的标准库定义了 {name}`PUnit` 和 {name}`PEmpty`。
若要定义既可属于 {lean}`Prop` 也可属于 {lean}`Type` 的子单元类型，可将选项 {option}`bootstrap.inductiveCheckResultingUniverse` 设为 {lean}`false`。

{zhOptionDocs bootstrap.inductiveCheckResultingUniverse ZhDoc.Option.bootstrap.inductiveCheckResultingUniverse}


::::keepEnv
:::example "过度使用宇宙多态的 {lean}`Bool`"
不允许定义可处于任意宇宙中的 {lean}`Bool` 版本：
```lean +error (name := PBool)

inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
```
:::
::::


# 用于终止性检查的构造
%%%
file := "Constructions for Termination Checking"
tag := "recursor-elaboration-helpers"
%%%


These constructions follow the description in {citet constructionsOnConstructors}[].

除了 Lean 核心类型理论为归纳类型规定的类型构造子、数据构造子和递归子外，Lean 还自动生成许多实用的辅助构造。
首先，方程编译器（用于将带模式匹配的递归函数翻译为递归子应用）会用到这些额外构造：
 * `recOn` 是递归子的一个变体，其目标参数排在每个构造子的分支参数之前。
 * `casesOn` 也是一个变体，其目标参数也在分支之前，且递归参数不会产生归纳假设。它表达的是分情况分析而非原始递归。
 * `below` 生成一个类型，表达针对某动机，目标所有子树的所有归纳类型元素都满足该动机。它能把归纳/原始递归用的动机变成强递归/强归纳的动机。
 * `brecOn` 是使用 `below` 以可以访问所有子树（而不仅是直接递归参数）的递归子变体，表达强归纳。
 * `noConfusion` 是一个通用语句，可据此推出构造子的单射性和互斥性。
 * `noConfusionType` 是为 `noConfusion` 设计的动机，用以描述两个构造子相等时的推论。对不同构造子而言这是 {lean}`False`；相同构造子则为各自参数的等式。

对于{tech (key := "well-founded recursion")}[良构递归]，通常还需要一个通用意义上的“大小”概念。
这正是 {name}`SizeOf` 类型类所提供的。

{zhdocstring SizeOf ZhDoc.SizeOf}
