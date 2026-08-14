/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import Manual.Classes.InstanceDecls
import Manual.Classes.InstanceSynth
import Manual.Classes.DerivingHandlers
import Manual.Classes.BasicClasses

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxRecDepth 100000
#doc (Manual) "类型类" =>
%%%
file := "Type-Classes"
tag := "type-classes"
%%%

如果一个操作可以用于多种类型，它就是_多态的_。
在 Lean 中，多态有三种变体：

 1. {tech (key := "universe polymorphism")}[宇宙多态]，其中定义中的类可以用各种方式实例化，
 2. 接受类型作为（可能是隐式）参数的函数，允许单段代码可用于任何类型，以及
 3. 用类型类实现的 {deftech (key := "ad-hoc polymorphism")}[特设多态]，其中被重载的操作对于不同类型可能有不同的实现。

因为 Lean 不允许对类型进行情况分析，所以多态函数实现了对任何类型参数选择都统一的操作；例如，{name}`List.map` 不会仅仅因为输入列表包含的是 {name}`String` 还是 {name}`Nat` 就突然采取不同的计算方式。
当无法以“统一”的方式实现某个操作时，特设多态操作就非常有用；最典型的用例是重载算术运算符，使它们能用于 {name}`Nat`、{name}`Int`、{name}`Float`，以及其他任何具有合理加法概念的类型。
特设多态也可能涉及多种类型；在一个集合的给定索引处查找值时，就涉及了集合类型、索引类型以及要提取的成员元素的类型。
{deftech (key := "type class")}[类型类]{margin}[类型类最早在 {citehere wadlerBlott89}[] 中描述。] 描述了一组重载操作（称为 {deftech (key := "method")}[方法]）以及它们所涉及的类型。

类型类非常灵活。
重载可能涉及多种类型；例如在数据结构中通过索引取值的操作，可以针对特定的数据结构、索引类型、元素类型甚至断言键存在于结构中的谓词进行重载。
得益于 Lean 富有表现力的类型系统，重载操作不仅限于类型；类型类可以通过普通值、类型族甚至谓词或命题进行参数化。
所有这些可能情况在实践中都有应用：

: 自然数字面量

  {name}`OfNat` 类型类用于解释自然数字面量。
  其实例不仅可能取决于被实例化的类型，还可能取决于数字面量本身。

: 计算效应

  像 {name}`Monad` 这样的类型类（其参数是一个从某个类型到另一个类型的函数）被用于为 {ref "monads-and-do"}[具有副作用的程序提供特殊语法]。
  这里被重载操作的“类型”实际上是一个类型级函数，例如 {name}`Option`、{name}`IO` 或 {name}`Except`。

: 谓词与命题

  {name}`Decidable` 类型类允许 Lean 自动找到一个命题的判定过程。
  这是 {keywordOf termIfThenElse}`if`-表达式的基础，使其可以基于任何可判定命题进行分支。

虽然普通的多态定义仅仅期望使用任意参数进行实例化，但被类型类重载的运算符要被 {deftech (key := "instance")}[实例]实例化，这些实例为某组特定参数定义了重载后的操作。
这些 {deftech (key := "instance-implicit")}[实例隐式]参数在方括号中指定。
在调用位置，Lean 要么从候选列表中 {deftech (key := "synthesis")}[合成]{index}[实例合成] {index (subterm := "of type class instances")}[合成]一个合适的实例，要么报告错误。
由于实例本身也可能有实例参数，这个搜索过程可能是递归的，并产生一个将各种实例的代码组合在一起的最终复合实例值。
因此，类型类实例合成也是一种类型制导的程序构建手段。

以下是类型类的一些典型用例：
 * 类型类可以表示重载运算符，比如可用于多种数值类型的算术运算符，或者可用于多种数据结构的成员判定谓词。对于给定类型，操作符通常有一个唯一的规范选择——毕竟对于 {lean}`Nat` 的加法没有其他合理的替代定义——但这并非一个必然属性，库如果需要也可以提供替代实例。
 * 类型类可以表示代数结构，提供该结构所需的额外结构及其公理。例如，表示阿贝尔群的类型类可能包含二元运算符、一元逆元运算符、单位元的方法，以及证明二元运算符具有结合律和交换律、单位元确实是单位元，以及逆元运算符在运算符两边都产生单位元的证明。在这里，可能没有规范的结构选择，库可能会提供许多实例化给定公理集合的方法；例如整数上就有两个同样规范的幺半群结构。
 * 类型类可以表示两种类型之间的关系，允许它们在库中以某种新颖的方式一起使用。
   {lean}`Coe` 类表示自动插入的从一种类型到另一种类型的强制转换，{lean}`MonadLift` 表示在期望另一种效应的上下文中运行带有某一种效应操作的方法。
 * 类型类可以表示类型制导的代码生成框架，其中多态类型的实例各自贡献最终程序的一部分。
    {name}`Repr` 类为一个类型定义了规范的美观打印器，而多态类型最终会有多态的 {name}`Repr` 实例。
    当美观打印最终在已知具体类型的表达式（如 {lean}`List (Nat × (String ⊕ Int))`）上被调用时，产生的漂亮打印器将包含由 {name}`List`、{name}`Prod`、{name}`Nat`、{name}`Sum`、{name}`String` 和 {name}`Int` 的 {name}`Repr` 实例组装而成的代码。

# 类声明
%%%
file := "Class-Declarations"
tag := "class"
%%%

类型类使用 {keywordOf Lean.Parser.Command.declaration}`class` 关键字进行声明。

:::syntax command (title := "类型类声明")
```grammar
$_:declModifiers
class $d:declId $_:bracketedBinder* $[: $_]?
  $[extends $[$[$_ : ]?$_],*]?
  where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$x:ident],*]?
```

声明一个新类型类。
:::

:::keepEnv
```lean -show
-- 只是确保 `deriving` 子句是合法的
class A (n : Nat) where
  k : Nat
  eq : n = k
deriving DecidableEq
```
:::


{keywordOf Lean.Parser.Command.declaration}`class` 声明创建了一个新的单构造器归纳类型，就好像使用了 {keywordOf Lean.Parser.Command.declaration}`structure` 命令一样。
实际上，{keywordOf Lean.Parser.Command.declaration}`class` 和 {keywordOf Lean.Parser.Command.declaration}`structure` 命令的结果几乎相同，并且诸如默认值之类的特性在两者中以相同的方式使用。
请参考{ref "structures"}[结构的文档]以获取有关默认值、继承及结构的其他特性的更多信息。
结构体声明和类声明之间的区别是：

: 方法而不是字段

  它不会创建以结构体类型的值作为显式参数的字段投影，而是创建{tech (key := "method")}[方法]。每个方法将对应的实例作为实例隐式参数。

: 实例隐式父类

  继承了其他类的类的构造器将其父类的实例作为实例隐式参数，而不是显式参数。
  当定义该类的实例时，实例合成被用于查找继承字段的值。
  不是类的父类仍然是底层构造器的显式参数。

: 借由实例合成得到的父投影

  结构体字段投影利用{ref "structure-inheritance"}[继承信息]从子结构体值中投影出父结构体字段。
  类取而代之使用实例合成：给定一个子类实例，合成机制将构造父类；因此，方法不会像投影被添加到子结构体那样被添加到子类中。

: 注册为类

  得到的归纳类型被注册为类型类，可以为其定义实例，并且可以用作实例隐式参数的类型。

: 考虑输出参数与半输出参数

  {name}`outParam` 和 {name}`semiOutParam` {tech (key := "gadget")}[小工具]在结构体定义中没有意义，但它们在类定义中用于控制实例搜索。

虽然在类定义中允许 {keywordOf Lean.Parser.Command.declaration}`deriving` 子句，以保持类和结构体精译过程的平行，但它们并不常用，且应被视为高级特性。

:::example "非类的实例不存在"

Lean 拒绝使用非类类型的实例隐式参数：
```lean +error (name := notClass)
def f [n : Nat] : n = n := rfl
```

```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
```

:::

::::example "类与结构体构造器对比"
一个非常小的代数层次结构既可以表示为结构体（如下面的 {name}`S.Magma`、{name}`S.Semigroup` 和 {name}`S.Monoid`），也可以表示为结构体与类的混合（{name}`C1.Monoid`），或仅使用类（{name}`C2.Magma`、{name}`C2.Semigroup` 和 {name}`C2.Monoid`）：
```lean
namespace S
structure Magma (α : Type u) where
  op : α → α → α

structure Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

structure Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end S

namespace C1
class Monoid (α : Type u) extends S.Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C1

namespace C2
class Magma (α : Type u) where
  op : α → α → α

class Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

class Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C2
```


{name}`S.Monoid.mk` 和 {name}`C1.Monoid.mk` 有着完全相同的签名，因为 {name}`C1.Monoid` 类的父结构体本身并不是类：
```signature
S.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  S.Monoid α
```
```signature
C1.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  C1.Monoid α
```

类似地，因为 `S.Magma` 和 `C2.Magma` 都没有从其他结构体或类继承，所以它们的构造器是相同的：
```signature
S.Magma.mk.{u} {α : Type u} (op : α → α → α) : S.Magma α
```
```signature
C2.Magma.mk.{u} {α : Type u} (op : α → α → α) : C2.Magma α
```

然而，{name}`S.Semigroup.mk` 会将它的父级作为普通参数接受，而 {name}`C2.Semigroup.mk` 会将其父级作为实例隐式参数接受：
```signature
S.Semigroup.mk.{u} {α : Type u}
  (toMagma : S.Magma α)
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  S.Semigroup α
```
```signature
C2.Semigroup.mk.{u} {α : Type u} [toMagma : C2.Magma α]
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  C2.Semigroup α
```

最后，{name}`C2.Monoid.mk` 接受其半群父类作为实例隐式参数。
对 `op` 的引用变为了对方法 {name}`C2.Magma.op` 的引用，这依赖于实例合成通过其父级投影从 {name}`C2.Semigroup` 实例隐式参数中恢复实现：
```signature
C2.Monoid.mk.{u} {α : Type u}
  [toSemigroup : C2.Semigroup α]
  (ident : α)
  (ident_left : ∀ (x : α), C2.Magma.op ident x = x)
  (ident_right : ∀ (x : α), C2.Magma.op x ident = x) :
  C2.Monoid α
```
::::

类型类的参数可以用 {deftech (key := "gadget")}[小工具]标记，小工具是恒等函数的特殊版本，会导致精译器对值的处理方式有所不同。
小工具从不改变项的_含义_，但可能会让精译时的搜索过程对其采取不同的处理。
小工具 {name}`outParam` 和 {name}`semiOutParam` 会影响{ref "instance-synth"}[实例合成]，因此它们在对应小节记录。

某个类型是不是类对定义相等没有任何影响。
参数相同的两个同类实例不一定相同，甚至在实际上可以有很大差别。

::::example "实例并不唯一"

二叉堆插入的这个实现是有缺陷的：
```lean
structure Heap (α : Type u) where
  contents : Array α
deriving Repr

def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if Ord.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j { xs with contents := xs.contents.swap i j }
    else xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```

问题在于用一个 {name}`Ord` 实例构造的堆可能在之后用到了另一个实例上，导致破坏堆的不变式。

修正该问题的一个方法是让堆类型依赖于选定的 `Ord` 实例：
```lean
structure Heap' (α : Type u) [Ord α] where
  contents : Array α

def Heap'.bubbleUp [inst : Ord α]
    (i : Nat) (xs : @Heap' α inst) :
    @Heap' α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap'.bubbleUp j {xs with contents := xs.contents.swap i j}
    else xs

def Heap'.insert [Ord α] (x : α) (xs : Heap' α) : Heap' α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```

在改进后的定义中，{name}`Heap'.bubbleUp` 不必要地显式化；这里实例不需要被显式命名，因为即使不显式声明 Lean 也会选择所示的实例，但这确实向读者凸显了正确性不变式。
::::

## 作为类的和类型
%%%
tag := "class inductive"
%%%

大多数类型类遵循一组重载方法的范式，调用者可以从中自由选择。
这自然可以用积类型来建模，其中被重载的方法即为其投影。
然而，有些类是和类型：它们要求合成实例的接收者首先检查提供了_哪个_可用的实例构造器。
为了将此类纳入考虑范围，类声明可以包含一个任意的{tech (key := "inductive type")}[归纳类型]，而不仅是结构体声明的扩展形式。

:::syntax Lean.Parser.Command.declaration (title := "类归纳类型声明")
```grammar
$_:declModifiers
class inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```
:::

类归纳类型就像其他归纳类型一样，唯一的区别是它们可能参与实例合成。
类归纳类型的一个典型例子是 {name}`Decidable`：在有自由变量的上下文中合成一个实例就等价于合成一个判定过程，但如果没有自由变量，那么就可以仅通过实例合成来确立命题的真值（就像 {tactic (show:="decide")}`Lean.Parser.Tactic.decide` 策略所做的那样）。

## 类缩写
%%%
tag := "class-abbrev"
%%%

在某些情况下，代码库中可能到处会出现许多相关的类型类。
与其重复写出所有名称，不如定义一个继承了所有相关类的类，而该类本身不提供任何新方法。
但是，这个新类有一个缺点：必须显式地声明它的实例。

{keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` 命令允许创建 {deftech (key := "class abbreviation")}[类缩写]，其中一个名称就是许多其他类参数的简写。
在幕后，类缩写是用一个继承了其他类的类来表示的。
其构造器还被额外声明为实例，这样新类就可以仅通过实例合成来构造了。

::::keepEnv

:::example "类缩写"
{name}`plusTimes1` 和 {name}`plusTimes2` 都要求其参数的类型具有 {name}`Add` 和 {name}`Mul` 实例：

```lean
class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z
```

由于 {name}`AddMul` 是一个 {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev`，因此无需任何额外声明就能以 {lean}`Nat` 使用 {name}`plusTimes1`：

```lean (name := plusTimes1)
#eval plusTimes1 2 5 7
```
```leanOutput plusTimes1
37
```

然而，{name}`plusTimes2` 会失败，因为不存在 {lean}`AddMul' Nat` 的实例——目前还未声明任何实例：
```lean (name := plusTimes2a) +error
#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2a
failed to synthesize instance of type class
  AddMul' ?m.8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
声明一个非常通用的实例就能解决 {lean}`Nat` 和其他每种类型的问题：
```lean (name := plusTimes2b)
instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2b
37
```
:::
::::

{include 0 Manual.Classes.InstanceDecls}

{include 0 Manual.Classes.InstanceSynth}

# 派生实例
%%%
tag := "deriving-instances"
%%%

Lean 可以为许多类自动生成实例，这一过程被称为 {deftech (key := "deriving")}[派生]实例。
既可以在定义类型时调用实例派生，也可以作为独立命令调用它。

:::syntax Lean.Parser.Command.optDeriving -open (title := "实例派生（可选）")
作为创建新归纳类型的命令的一部分，{keywordOf Lean.Parser.Command.declaration}`deriving` 子句指定了以逗号分隔的类名列表，用于为其生成实例：
```grammar
$[deriving $[$_],*]?
```
:::

:::syntax Lean.Parser.Command.deriving (title := "独立的派生实例")
独立的 {keywordOf Lean.Parser.Command.deriving}`deriving` 命令指定了几个类名和目标名。
每个指定的类都会为每个指定的目标进行派生。
```grammar
deriving instance $[$_],* for $_,*
```
:::

::::keepEnv
:::example "派生多个类"
在为多个类型指定派生多个类后，如下面的代码所示：
```lean
structure A where
structure B where

deriving instance BEq, Repr for A, B
```
所有类型的这些实例都存在了，因此全部四个 {keywordOf Lean.Parser.Command.synth}`#synth` 命令都成功了：
```lean
#synth BEq A
#synth BEq B
#synth Repr A
#synth Repr B
```
:::
::::

{include 2 Manual.Classes.DerivingHandlers}

{include 0 Manual.Classes.BasicClasses}
