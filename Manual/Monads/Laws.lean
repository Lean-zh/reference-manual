/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Monads.Core

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "定律" =>
%%%
tag := "monad-laws"
file := "Laws"
%%%

::::keepEnv

```lean -show
section Laws
universe u u' v
axiom f : Type u → Type v
axiom m : Type u → Type v
variable [Functor f]
variable [Applicative f]
variable [Monad m]
axiom α : Type u'
axiom β : Type u'
axiom γ : Type u'
axiom x : f α
```


```lean -show
section F
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {h : β → γ} {x : f α}
```

仅有类型适当的 {name Functor.map}`map`、{name Pure.pure}`pure`、{name Seq.seq}`seq` 和 {name Bind.bind}`bind` 运算，还不足以真正构成函子、应用函子或单子。
这些运算还必须满足某些公理，它们通常称为该类型类的{deftech (key := "laws")}_定律_。

对于函子，{name Functor.map}`map` 操作必须保持恒等函数和函数复合。换言之，给定一个声称为 {name}`Functor` 的 {lean}`f`，对所有 {lean}`x`​` : `​{lean}`f α`：
 * {lean}`id <$> x = x`；并且
 * 对所有函数 {lean}`g` 和 {lean}`h`，有 {lean}`(h ∘ g) <$> x = h <$> g <$> x`。

违反这些假设的实例可能产生非常出人意料的行为！
此外，因为 {lean}`Functor` 包含 {name Functor.mapConst}`mapConst`，以便实例提供更高效的实现，所以合法函子的 {name Functor.mapConst}`mapConst` 应当等价于其默认实现。

Lean 标准库不要求每个 {name}`Functor` 实例都提供这些性质的证明。
尽管如此，如果某个实例违反了它们，就应将其视为缺陷。
需要这些性质的证明时，可以使用类型为 {lean}`LawfulFunctor f` 的实例隐式参数。
类型类 {name}`LawfulFunctor` 包含所需的证明。

{zhdocstring LawfulFunctor Manual.ZhDocString.Monads.Core.LawfulFunctor}

```lean -show
end F
```


除了要证明可能经过优化的 {name}`SeqLeft.seqLeft` 和 {name}`SeqRight.seqRight` 操作等价于其默认实现之外，应用函子 {lean}`f` 还必须满足四条定律。

:::TODO
讨论传统应用函子定律与此处表述之间的关系
:::

{zhdocstring LawfulApplicative Manual.ZhDocString.Monads.Core.LawfulApplicative}

{deftech (key := "monad laws")}[单子定律]规定：{name}`pure` 后接 {name}`bind` 应等价于函数应用（即 {name}`pure` 没有任何效应）；{name}`bind` 后接用 {name}`pure` 包裹的函数应用，应等价于 {name Functor.map}`map`；并且 {name}`bind` 满足结合律。


{zhdocstring LawfulMonad Manual.ZhDocString.Monads.Core.LawfulMonad}


{zhdocstring LawfulMonad.mk' Manual.ZhDocString.Monads.Core.LawfulMonad.mk'}

::::
