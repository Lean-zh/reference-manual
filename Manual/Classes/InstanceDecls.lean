/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option warn.classDefReducibility false

#doc (Manual) "实例声明" =>
%%%
file := "Instance-Declarations"
tag := "instance-declarations"
%%%

实例声明的语法与定义几乎完全相同。
唯一的语法区别在于关键字 {keywordOf Lean.Parser.Command.declaration}`def` 被替换为 {keywordOf Lean.Parser.Command.declaration}`instance`，且名称是可选的：

:::syntax Lean.Parser.Command.instance (title := "实例声明")

大多数实例使用 {keywordOf Lean.Parser.Command.declaration}`where` 语法来定义各个方法：

```grammar
instance $[(priority := $p:prio)]? $name? $_ where
  $_*
```

然而，类型类本身是归纳类型，因此可以使用任何具有合适类型的表达式来构造实例：

```grammar
instance $[(priority := $p:prio)]? $_? $_ :=
  $_
```

实例也可以通过分情况进行定义；然而，除了 {name}`Decidable` 实例外，这个特性很少被使用：

```grammar
instance $[(priority := $p:prio)]? $_? $_
  $[| $_ => $_]*
```

:::

使用显式项定义的实例通常包含以下两种：要么是包装着方法实现的匿名构造器（{keywordOf Lean.Parser.Term.anonymousCtor}`⟨...⟩`），要么是在定义相等的类型上调用 {name}`inferInstanceAs`。

实例的精译过程几乎与普通定义的精译相同，除了以下记录的一些注意事项。
如果没有提供名称，系统将自动创建一个。
可以直接引用这个生成的名称，但用于生成名称的算法过去曾经改变过，将来也可能还会改变。
对于将要被直接引用的实例，最好对其进行显式命名。
精译之后，新实例会被注册为实例搜索的一个候选者。
将 {attr}`instance` 属性添加到一个名称上，可以用来将任何其他已定义的名称标记为候选。

::::keepEnv
:::example "实例名称的生成"

执行这些声明后：
```lean
structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y
```

名称 {lean}`instBEqNatWrapper` 指代该新实例。
:::
::::

::::keepEnv
:::example "实例定义的变体"

给定这个结构体类型：
```lean
structure NatWrapper where
  val : Nat
```
以下所有定义 {name}`BEq` 实例的方式都是等价的：
```lean
instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```

除了向环境中引入了不同的名称外，以下这些也是等价的：
```lean
@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
:::
::::

# 递归实例
%%%
tag := "recursive-instances"
%%%

在结构体定义中使用 {keywordOf Lean.Parser.Command.declaration}`where` 语法定义的函数不是递归的。
由于实例声明是结构体定义的一种变体，默认情况下，类型类的方法也不是递归的。
然而，递归归纳类型的实例是很常见的。
为了绕过这个限制，有一个标准的惯用法：在实例之外独立定义一个递归函数，然后在实例定义中引用它。
按照惯例，这些递归函数与相应的方法同名，但定义在目标类型的命名空间中。

:::example "实例不是递归的"
给定如下的 {lean}`NatTree` 定义：
```lean
inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)
```
如下的 {name}`BEq` 实例会失败：
```lean +error (name := beqNatTreeFail)
instance : BEq NatTree where
  beq
    | .leaf, .leaf =>
      true
    | .branch l1 v1 r1, .branch l2 v2 r2 =>
      l1 == l2 && v1 == v2 && r1 == r2
    | _, _ =>
      false
```
在左右的递归调用处都会出现如下报错：
```leanOutput beqNatTreeFail
failed to synthesize instance of type class
  BEq NatTree

Hint: Adding the command `deriving instance BEq for NatTree` may allow Lean to derive the missing instance.
```
给定一个合适的递归函数，例如 {lean}`NatTree.beq`：
```lean
def NatTree.beq : NatTree → NatTree → Bool
  | .leaf, .leaf =>
    true
  | .branch l1 v1 r1, .branch l2 v2 r2 =>
    NatTree.beq l1 l2 && v1 == v2 && NatTree.beq r1 r2
  | _, _ =>
    false
```
就可以分第二步创建这个实例：
```lean
instance : BEq NatTree where
  beq := NatTree.beq
```
或者，等价地，使用匿名构造器语法：
```lean
instance : BEq NatTree := ⟨NatTree.beq⟩
```
:::

此外，实例在其自身的定义期间是不可以用于实例合成的。
它们仅在定义完成之后，才会被标记为可供实例合成。
对于嵌套归纳类型（其中类型的递归出现是作为其他一些归纳类型的参数），甚至可能需要一个可用的实例才能写出递归函数。
绕过这个限制的标准惯用法是：在递归定义的函数中创建一个局部实例（包含对正在定义的函数的引用），从而利用实例合成可使用局部上下文中每一个具有正确类型的绑定这一事实。


::: example "嵌套类型的实例"
在这个 {lean}`NatRoseTree` 的定义中，正被定义的类型被嵌套在另一个归纳类型构造器（{name}`Array`）之下：
```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
检查玫瑰树的相等性需要检查数组的相等性。
然而，实例在其自身定义期间通常不能用于实例合成，因此以下定义会失败，尽管 {lean}`NatRoseTree.beq` 是一个递归函数并且在其自身定义的作用域内。
```lean +error (name := natRoseTreeBEqFail) -keep
def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    val1 == val2 &&
    children1 == children2
```
```leanOutput natRoseTreeBEqFail
failed to synthesize instance of type class
  BEq (Array NatRoseTree)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

要解决这个问题，可以通过 `let` 绑定一个局部的 {lean}`BEq NatRoseTree` 实例：

```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
子节点上使用了数组相等性，可以在实例合成期间找到由 `let` 绑定的实例。
:::

# `class inductive` 的实例
%%%
tag := "class-inductive-instances"
%%%

许多实例具有函数类型：任何会递归调用实例搜索的实例本身都是一个函数，具有隐式参数的实例同样如此。
虽然大多数实例只是根据它们自己的实例参数投影出方法实现，但类归纳类型的实例通常会对它们的一个或多个参数进行模式匹配，允许实例去选择适当的构造器。
这是使用普通的 Lean 函数语法完成的。
正如其他实例一样，讨论的这个函数在其自身定义期间是不可用于实例合成的。
::::keepEnv
:::example "和类的实例"
```lean -show
axiom α : Type
```
因为 {lean}`DecidableEq α` 是 {lean}`(a b : α) → Decidable (Eq a b)` 的缩写，其参数可以直接使用，如此例所示：

```lean
inductive ThreeChoices where
  | yes | no | maybe

instance : DecidableEq ThreeChoices
  | .yes,   .yes   =>
    .isTrue rfl
  | .no,    .no    =>
    .isTrue rfl
  | .maybe, .maybe =>
    .isTrue rfl
  | .yes,   .maybe | .yes,   .no
  | .maybe, .yes   | .maybe, .no
  | .no,    .yes   | .no,    .maybe =>
    .isFalse nofun

```

:::
::::

::::keepEnv
:::example "和类的递归实例"
{lean}`StringList` 类型表示字符串的单态列表：
```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
在下述定义 {name}`DecidableEq` 实例的尝试中，精译内部的 {keywordOf termIfThenElse}`if` 时调用的实例合成失败了，因为该实例在其自身的定义期间不能用于实例合成：
```lean +error (name := stringListNoRec) -keep
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```leanOutput stringListNoRec
failed to synthesize instance of type class
  Decidable (t1 = t2)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
然而，因为它只是一个普通的 Lean 函数，所以它可以递归地引用自身显式提供的名称：
```lean
instance instDecidableEqStringList : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    let _ : Decidable (t1 = t2) :=
      instDecidableEqStringList t1 t2
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
:::
::::


# 实例优先级
%%%
tag := "instance-priorities"
%%%

可以为实例分配 {deftech (key := "priorities")}[优先级]。
在实例合成期间，更高优先级的实例会被优先考虑；有关实例合成的详情，请参阅 {ref "instance-synth"}[实例合成小节]。

:::syntax prio -open (title := "实例优先级")
优先级可以是数字：
```grammar
$n:num
```

如果没有指定优先级，则使用对应于 {evalPrio}`default` 的默认优先级：
```grammar
default
```

当数字值太细粒度时，有三种命名优先级可用，分别对应于 {evalPrio}`low`、{evalPrio}`mid` 和 {evalPrio}`high`。
{keywordOf prioMid}`mid` 优先级低于 {keywordOf prioDefault}`default`。
```grammar
low
```
```grammar
mid
```
```grammar
high
```

最后，优先级还可以做加减法，因此 `default + 2` 也是个有效的优先级，对应于 {evalPrio}`default + 2`：
```grammar
($_)
```
```grammar
$_ + $_
```
```grammar
$_ - $_
```

:::

# 默认实例
%%%
tag := "default-instances"
%%%

{attr}`default_instance` 属性指定了 {ref "default-instance-synth"}[在没有足够的信息来选择实例时，应将其作为后备方案使用]。
如果没有指定优先级，则使用默认优先级 `default`。

:::syntax attr (title := "{keyword}`default_instance` 属性")
```grammar
default_instance $p?
```
:::

:::::keepEnv
::::example "默认实例"
当缺少其他类型信息时，自然数字面量将通过 {lean}`OfNat Nat` 的默认实例来选择被解释为 {lean}`Nat` 类型。
它在 Lean 标准库中被声明，其优先级为 100。
给定偶数的如下表示方式，其中偶数由其一半来表示：
```lean
structure Even where
  half : Nat
```

以下实例允许将数字字面量用于较小的 {lean}`Even` 值（对类型类实例搜索深度的限制阻碍了它们被用于任意大的字面量）：
```lean (name := insts)
instance ofNatEven0 : OfNat Even 0 where
  ofNat := ⟨0⟩

instance ofNatEvenPlusTwo [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(OfNat.ofNat n : Even).half + 1⟩

#eval (0 : Even)
#eval (34 : Even)
#eval (254 : Even)
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 127 }
```

将它们指定为优先级大于等于 100 的默认实例，会导致在没有类型提示时它们被使用而不是 {lean}`Nat`：
```lean
attribute [default_instance 100] ofNatEven0
attribute [default_instance 100] ofNatEvenPlusTwo
```
```lean (name := withDefaults)
#eval 0
#eval 34
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 17 }
```

非偶数数字仍使用 {lean}`OfNat Nat` 实例：
```lean (name := stillNat)
#eval 5
```
```leanOutput stillNat
5
```
::::
:::::

# `instance` 属性
%%%
tag := "instance-attribute"
%%%

{attr}`instance` 属性将一个名称声明为指定优先级的实例。
与其他属性一样，{attr}`instance` 可以全局应用，或者局部应用，或者仅当打开了当前命名空间时应用。
{keywordOf Lean.Parser.Command.declaration}`instance` 声明就是一种会自动应用 {attr}`instance` 属性的定义形式。

:::syntax attr (title := "`instance` 属性")

将其应用的定义声明为一个实例。
如果没有提供优先级，则使用默认优先级 `default`。

```grammar
instance $p?
```


:::
