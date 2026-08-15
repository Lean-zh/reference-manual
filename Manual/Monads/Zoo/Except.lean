/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Monads.Except

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "异常" =>
%%%
tag := "exception-monads"
%%%

异常单子描述会提前终止（失败）的计算。
失败的计算向调用方提供一个_异常_值，用于说明失败的_原因_。
换言之，计算要么返回值，要么返回异常。
归纳类型 {name}`Except` 刻画了这一模式，而它本身也是单子。

# 异常
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Exceptions--Exceptions"
%%%

{zhdocstring Except Manual.ZhDocString.Monads.Except.Except}

{zhdocstring Except.pure Manual.ZhDocString.Monads.Except.Except.pure}

{zhdocstring Except.bind Manual.ZhDocString.Monads.Except.Except.bind}

{zhdocstring Except.map Manual.ZhDocString.Monads.Except.Except.map}

{zhdocstring Except.mapError Manual.ZhDocString.Monads.Except.Except.mapError}

{zhdocstring Except.tryCatch Manual.ZhDocString.Monads.Except.Except.tryCatch}

{zhdocstring Except.orElseLazy Manual.ZhDocString.Monads.Except.Except.orElseLazy}

{zhdocstring Except.isOk Manual.ZhDocString.Monads.Except.Except.isOk}

{zhdocstring Except.toOption Manual.ZhDocString.Monads.Except.Except.toOption}

{zhdocstring Except.toBool Manual.ZhDocString.Monads.Except.Except.toBool}


# 类型类
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Exceptions--Type-Class"
%%%

{zhdocstring MonadExcept Manual.ZhDocString.Monads.Except.MonadExcept}

{zhdocstring MonadExcept.ofExcept Manual.ZhDocString.Monads.Except.MonadExcept.ofExcept}

{zhdocstring MonadExcept.orElse Manual.ZhDocString.Monads.Except.MonadExcept.orElse}

{zhdocstring MonadExcept.orelse' Manual.ZhDocString.Monads.Except.MonadExcept.orelse'}

{zhdocstring MonadExceptOf Manual.ZhDocString.Monads.Except.MonadExceptOf}

{zhdocstring throwThe Manual.ZhDocString.Monads.Except.throwThe}

{zhdocstring tryCatchThe Manual.ZhDocString.Monads.Except.tryCatchThe}

# “最终”计算
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Exceptions--___Finally___-Computations"
%%%

{zhdocstring MonadFinally Manual.ZhDocString.Monads.Except.MonadFinally}

# 变换器
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Exceptions--Transformer"
%%%

{zhdocstring ExceptT Manual.ZhDocString.Monads.Except.exceptT}

{zhdocstring ExceptT.lift Manual.ZhDocString.Monads.Except.ExceptT.lift}

{zhdocstring ExceptT.run Manual.ZhDocString.Monads.Except.ExceptT.run}

{zhdocstring ExceptT.pure Manual.ZhDocString.Monads.Except.ExceptT.pure}

{zhdocstring ExceptT.bind Manual.ZhDocString.Monads.Except.ExceptT.bind}

{zhdocstring ExceptT.bindCont Manual.ZhDocString.Monads.Except.ExceptT.bindCont}

{zhdocstring ExceptT.tryCatch Manual.ZhDocString.Monads.Except.ExceptT.tryCatch}

{zhdocstring ExceptT.mk Manual.ZhDocString.Monads.Except.ExceptT.mk}

{zhdocstring ExceptT.map Manual.ZhDocString.Monads.Except.ExceptT.map}

{zhdocstring ExceptT.adapt Manual.ZhDocString.Monads.Except.ExceptT.adapt}


# 延续传递风格的异常单子
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Exceptions--Exception-Monads-in-Continuation-Passing-Style"
%%%

```lean -show
universe u
variable (α : Type u)
variable (ε : Type u)
variable {m : Type u → Type v}
```

延续传递风格的异常单子把可能失败的计算表示为函数：它接受成功延续和失败延续，二者返回相同类型，而函数也返回该类型。
它们必须适用于_任意_返回类型。
这种类型的一个例子是 {lean}`(β : Type u) → (α → β) → (ε → β) → β`。
{lean}`ExceptCpsT` 是可应用于任意单子的变换器，因此 {lean}`ExceptCpsT ε m α` 实际定义为 {lean}`(β : Type u) → (α → m β) → (ε → m β) → m β`。
延续传递风格的异常单子与基于 {name}`Except` 的异常单子具有不同的性能特征；对某些应用而言，值得对它们进行基准测试。

```lean -show
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#check_msgs in
#reduce (types := true) ExceptCpsT ε m α
```

{zhdocstring ExceptCpsT Manual.ZhDocString.Monads.Except.exceptCpsT}

{zhdocstring ExceptCpsT.runCatch Manual.ZhDocString.Monads.Except.ExceptCpsT.runCatch}

{zhdocstring ExceptCpsT.runK Manual.ZhDocString.Monads.Except.ExceptCpsT.runK}

{zhdocstring ExceptCpsT.run Manual.ZhDocString.Monads.Except.ExceptCpsT.run}

{zhdocstring ExceptCpsT.lift Manual.ZhDocString.Monads.Except.ExceptCpsT.lift}
