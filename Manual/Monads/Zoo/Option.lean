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

#doc (Manual) "可选值" =>
%%%
tag := "option-monad"
%%%

通常，{lean}`Option` 被视为数据，类似于可空类型。
它也可以被视为单子，从而成为一种执行计算的方式。
{lean}`Option` 单子及其变换器 {lean}`OptionT` 可以理解为描述可能提前终止并丢弃结果的计算。
调用方可以使用 {name}`OrElse.orElse` 检查是否提前终止，并按需调用后备计算；也可以把它当作 {lean}`MonadExcept Unit` 处理。

{docstring OptionT}

{docstring OptionT.run}

{docstring OptionT.lift}

{docstring OptionT.mk}

{docstring OptionT.pure}

{docstring OptionT.bind}

{docstring OptionT.fail}

{docstring OptionT.orElse}

{docstring OptionT.tryCatch}
