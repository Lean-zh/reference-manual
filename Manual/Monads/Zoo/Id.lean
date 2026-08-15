/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Monads.State

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "恒等" =>
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Identity"
%%%

恒等单子 {name}`Id` 完全没有任何作用。
{name}`Id` 以及对应的 {name}`pure` 实现都是恒等函数，而 {name}`bind` 是反向函数应用。
恒等单子主要有两种用途：
 1. 它可以作为 {keywordOf Lean.Parser.Term.do}`do` 块的类型，用局部作用实现纯函数。
 2. 它可以放在单子变换器栈的最底层。

```lean -show
-- 验证上述说法
example : Id = id := rfl
example : Id.run (α := α) = id := rfl
example : (pure (f := Id)) = (id : α → α) := rfl
example : (bind (m := Id)) = (fun (x : α) (f : α → Id β) => f x) := rfl
```

{zhdocstring Id ZhDoc.Monads.State.Id}

{zhdocstring Id.run ZhDoc.Monads.State.Id.run}

:::example "恒等单子中的局部作用"
这段代码通过在恒等单子中模拟局部可变性，实现了一个倒数过程。
```lean (name := idDo)
#eval Id.run do
  let mut xs := []
  for x in [0:10] do
    xs := x :: xs
  pure xs
```
```leanOutput idDo
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
```
:::
