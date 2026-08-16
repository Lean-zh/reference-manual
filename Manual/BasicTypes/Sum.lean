/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "和类型" =>
%%%
tag := "sum-types"
file := "Sum-Types"
%%%


{deftech (key := "Sum types")}_和类型_表示两种类型之间的选择：和类型的一个元素是这两种类型之一的元素，并配有指示其来源类型的标记。
和类型也称为不相交并集、可辨识联合或标记联合。
和类型的构造子也称为{deftech (key := "injections")}_单射_；在数学上，它们可以被视为从每个被加数到和类型的单射函数。

::::leanSection
```lean -show
universe u v
```

:::paragraph
和类型有两种变体：

 * {lean}`Sum` 是{tech (key := "universe polymorphism")}[多态]的，覆盖所有 {lean}`Type` {tech (key := "universes")}[宇宙]，并且永远不是{tech (key := "proposition")}[命题]。

 * {lean}`PSum` 允许被加数为命题或类型。与 {name}`Or` 不同，两个命题的 {name}`PSum` 仍然是一个类型，并且非命题代码可以检查用于构造给定值的是哪个单射。

手动编写的 Lean 代码几乎总是只使用 {lean}`Sum`，而 {lean}`PSum` 则作为证明自动化实现的一部分使用。
这是因为它施加了宇宙层级合一无法解决的棘手约束。
特别地，该类型位于宇宙 {lean}`Sort (max 1 u v)` 中，这可能会给宇宙层级合一带来问题，因为等式 `max 1 u v = ?u + 1` 在层级算术中无解。
`PSum` 通常仅用于构造任意类型之和的自动化中。
:::
::::

{zhdocstring Sum Manual.ZhDocString.Ch19Ch20.G9.c176}

{zhdocstring PSum Manual.ZhDocString.Ch19Ch20.G9.c177}



# 语法
%%%
tag := "sum-syntax"
%%%

名称 {name}`Sum` 和 {name}`PSum` 很少被显式写出。
大多数代码使用相应的插缀运算符。

```lean -show
section
variable {α : Type u} {β : Type v}
```

:::syntax term (title := "和类型")
```grammar
$_ ⊕ $_
```

{lean}`α ⊕ β` 是 {lean}`Sum α β` 的记号。

:::

```lean -show
end
```

```lean -show
section
variable {α : Sort u} {β : Sort v}
```

:::syntax term (title := "潜在命题和类型")
```grammar
$_ ⊕' $_
```

{lean}`α ⊕' β` 是 {lean}`PSum α β` 的记号。

:::

```lean -show
end
```

# API 参考
%%%
tag := "sum-api"
%%%

和类型主要与{tech (key := "pattern matching")}[模式匹配]一起使用，而不是来自 API 的显式函数调用。
因此，它们的主要 API 是构造子 {name Sum.inl}`inl` 和 {name Sum.inr}`inr`。

## 分情况讨论

%%%
tag := "Lean-__________________--Basic-Types--Sum-Types--API-Reference--Case-Distinction"
%%%
{zhdocstring Sum.isLeft Manual.ZhDocString.Ch19Ch20.G9.c178}

{zhdocstring Sum.isRight Manual.ZhDocString.Ch19Ch20.G9.c179}

## 提取值

%%%
tag := "Lean-__________________--Basic-Types--Sum-Types--API-Reference--Extracting-Values"
%%%
{zhdocstring Sum.elim Manual.ZhDocString.Ch19Ch20.G9.c180}

{zhdocstring Sum.getLeft Manual.ZhDocString.Ch19Ch20.G9.c181}

{zhdocstring Sum.getLeft? Manual.ZhDocString.Ch19Ch20.G9.c182}

{zhdocstring Sum.getRight Manual.ZhDocString.Ch19Ch20.G9.c183}

{zhdocstring Sum.getRight? Manual.ZhDocString.Ch19Ch20.G9.c184}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Sum-Types--API-Reference--Transformations"
%%%
{zhdocstring Sum.map Manual.ZhDocString.Ch19Ch20.G9.c185}

{zhdocstring Sum.swap Manual.ZhDocString.Ch19Ch20.G9.c186}

## 居留性

%%%
tag := "Lean-__________________--Basic-Types--Sum-Types--API-Reference--Inhabited"
%%%
{name}`Inhabited` 对 {name}`Sum` 和 {name}`PSum` 的定义没有被注册为实例。
这是因为有两种不同的方法来构造默认值（通过 {name Sum.inl}`inl` 或 {name Sum.inr}`inr`），而实例合成可能会导致任一选择。
结果可能是两种写法完全相同的项却精译出不同的结果，并且它们不是{tech (key := "definitional equality")}[定义等价]的。

这两种类型都有 {name}`Nonempty` 实例，由于{tech (key := "proof irrelevance")}[证明无关性]，选择 {name Sum.inl}`inl` 还是 {name Sum.inr}`inr` 并不重要。
这足以启用 {keyword}`partial` 函数。
对于需要 {name}`Inhabited` 实例的情况，例如使用 {keyword}`panic!` 的程序，可以通过 {keywordOf Lean.Parser.Term.have}`have` 或 {keywordOf Lean.Parser.Term.let}`let` 将其添加到局部上下文中来显式使用该实例。

:::example "具有居留性的和类型"

在 Lean 的逻辑中，{keywordOf Lean.Parser.Term.panic}`panic!` 等同于在其类型的 {name}`Inhabited` 实例中指定的默认值。
这意味着该类型必须具有这样的实例——{name}`Nonempty` 实例结合选择公理会使程序变得不可计算。

积类型具有合适的实例：
```lean
example : Nat × String := panic! "Can't find it"
```

和类型默认情况下没有：
```lean +error (name := panic)
example : Nat ⊕ String := panic! "Can't find it"
```
```leanOutput panic
failed to synthesize instance of type class
  Inhabited (Nat ⊕ String)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

可以使用 {keywordOf Lean.Parser.Term.have}`have` 使所需的实例对实例合成可用：
```lean
example : Nat ⊕ String :=
  have : Inhabited (Nat ⊕ String) := Sum.inhabitedLeft
  panic! "Can't find it"
```
:::

{zhdocstring Sum.inhabitedLeft Manual.ZhDocString.Ch19Ch20.G9.c187}

{zhdocstring Sum.inhabitedRight Manual.ZhDocString.Ch19Ch20.G9.c188}

{zhdocstring PSum.inhabitedLeft Manual.ZhDocString.Ch19Ch20.G9.c189}

{zhdocstring PSum.inhabitedRight Manual.ZhDocString.Ch19Ch20.G9.c190}
