/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "算术" =>
%%%
tag := "fixed-int-arithmetic"
%%%

通常，定宽整数上的算术运算应通过 Lean 的重载算术记号来使用，尤其是它们的 {name}`Add`、{name}`Sub`、{name}`Mul`、{name}`Div` 与 {name}`Mod` 实例，以及有符号类型的 {name}`Neg` 实例。

```lean -show
-- 检查这些实例确实都存在
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let signed := [`ISize, `Int8, `Int16, `Int32, `Int64]
  let unsigned := [`USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let types := signed ++ unsigned
  let classes : List Name := [`Add, `Sub, `Mul, `Div, `Mod]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
  for t in signed do
    elabCommand <| ← `(example : Neg $(mkIdent t) := inferInstance)
```

{docstring ISize.neg}

{docstring Int8.neg}

{docstring Int16.neg}

{docstring Int32.neg}

{docstring Int64.neg}

{docstring USize.neg}

{docstring UInt8.neg}

{docstring UInt16.neg}

{docstring UInt32.neg}

{docstring UInt64.neg}

{docstring USize.add}

{docstring ISize.add}

{docstring UInt8.add}

{docstring Int8.add}

{docstring UInt16.add}

{docstring Int16.add}

{docstring UInt32.add}

{docstring Int32.add}

{docstring UInt64.add}

{docstring Int64.add}

{docstring USize.sub}

{docstring ISize.sub}

{docstring UInt8.sub}

{docstring Int8.sub}

{docstring UInt16.sub}

{docstring Int16.sub}

{docstring UInt32.sub}

{docstring Int32.sub}

{docstring UInt64.sub}

{docstring Int64.sub}

{docstring USize.mul}

{docstring ISize.mul}

{docstring UInt8.mul}

{docstring Int8.mul}

{docstring UInt16.mul}

{docstring Int16.mul}

{docstring UInt32.mul}

{docstring Int32.mul}

{docstring UInt64.mul}

{docstring Int64.mul}

{docstring USize.div}

{docstring ISize.div}

{docstring UInt8.div}

{docstring Int8.div}

{docstring UInt16.div}

{docstring Int16.div}

{docstring UInt32.div}

{docstring Int32.div}

{docstring UInt64.div}

{docstring Int64.div}

{docstring USize.mod}

{docstring ISize.mod}

{docstring UInt8.mod}

{docstring Int8.mod}

{docstring UInt16.mod}

{docstring Int16.mod}

{docstring UInt32.mod}

{docstring Int32.mod}

{docstring UInt64.mod}

{docstring Int64.mod}

{docstring USize.log2}

{docstring UInt8.log2}

{docstring UInt16.log2}

{docstring UInt32.log2}

{docstring UInt64.log2}

{docstring ISize.abs}

{docstring Int8.abs}

{docstring Int16.abs}

{docstring Int32.abs}

{docstring Int64.abs}
