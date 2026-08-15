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

#doc (Manual) "读取器" =>
%%%
tag := "reader-monad"
%%%

{zhdocstring MonadReader ZhDoc.Monads.State.MonadReader}

{zhdocstring MonadReaderOf ZhDoc.Monads.State.MonadReaderOf}

{zhdocstring readThe ZhDoc.Monads.State.readThe}

{zhdocstring MonadWithReader ZhDoc.Monads.State.MonadWithReader}

{zhdocstring MonadWithReaderOf ZhDoc.Monads.State.MonadWithReaderOf}

{zhdocstring withTheReader ZhDoc.Monads.State.withTheReader}

{zhdocstring ReaderT ZhDoc.Monads.State.ReaderT}

{zhdocstring ReaderM ZhDoc.Monads.State.ReaderM}

{zhdocstring ReaderT.run ZhDoc.Monads.State.ReaderT.run}

{zhdocstring ReaderT.read ZhDoc.Monads.State.ReaderT.read}

{zhdocstring ReaderT.adapt ZhDoc.Monads.State.ReaderT.adapt}

{zhdocstring ReaderT.pure ZhDoc.Monads.State.ReaderT.pure}

{zhdocstring ReaderT.bind ZhDoc.Monads.State.ReaderT.bind}

{zhdocstring ReaderT.orElse ZhDoc.Monads.State.ReaderT.orElse}

{zhdocstring ReaderT.failure ZhDoc.Monads.State.ReaderT.failure}
