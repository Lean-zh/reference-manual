/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

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

{docstring Except}

{docstring Except.pure}

{docstring Except.bind}

{docstring Except.map}

{docstring Except.mapError}

{docstring Except.tryCatch}

{docstring Except.orElseLazy}

{docstring Except.isOk}

{docstring Except.toOption}

{docstring Except.toBool}


# 类型类

{docstring MonadExcept}

{docstring MonadExcept.ofExcept}

{docstring MonadExcept.orElse}

{docstring MonadExcept.orelse'}

{docstring MonadExceptOf}

{docstring throwThe}

{docstring tryCatchThe}

# “最终”计算

{docstring MonadFinally}

# 变换器

{docstring ExceptT}

{docstring ExceptT.lift}

{docstring ExceptT.run}

{docstring ExceptT.pure}

{docstring ExceptT.bind}

{docstring ExceptT.bindCont}

{docstring ExceptT.tryCatch}

{docstring ExceptT.mk}

{docstring ExceptT.map}

{docstring ExceptT.adapt}


# 延续传递风格的异常单子

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
延续传递风格的异常单子与基于 {name}`Except` 的状态单子具有不同的性能特征；对某些应用而言，值得对它们进行基准测试。

```lean -show
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#check_msgs in
#reduce (types := true) ExceptCpsT ε m α
```

{docstring ExceptCpsT}

{docstring ExceptCpsT.runCatch}

{docstring ExceptCpsT.runK}

{docstring ExceptCpsT.run}

{docstring ExceptCpsT.lift}
