/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "化简" =>
%%%
tag := "simp-tactics"
file := "Simplification"
%%%

专门介绍{ref "the-simplifier"}[化简器的章节]对其有更详细的说明。

:::tactic "simp"
:::

:::tactic "simp!"
:::

:::tactic "simp?"
:::

:::tactic "simp?!"
:::

:::tactic "simp_arith"
:::

:::tactic "simp_arith!"
:::

:::tactic "dsimp"
:::

:::tactic "dsimp!"
:::

:::tactic "dsimp?"
:::

:::tactic "dsimp?!"
:::


:::tactic "simp_all"
:::

:::tactic "simp_all!"
:::

:::tactic "simp_all?"
:::

:::tactic "simp_all?!"
:::


:::tactic "simp_all_arith"
:::


:::tactic "simp_all_arith!"
:::


:::tactic "simpa"
:::


:::tactic "simpa!"
:::

:::tactic "simpa?"
:::

:::tactic "simpa?!"
:::

:::tactic "simp_wf"
:::
