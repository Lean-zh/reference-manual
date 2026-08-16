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

set_option verso.docstring.allowMissing true

#doc (Manual) "比较" =>
%%%
tag := "fixed-int-comparisons"
%%%


本节中的运算符很少通过名称调用。
通常，定宽整数上的比较操作应该使用相应关系的可判定性，这些关系由相等类型 {name}`Eq` 以及在 {name}`LE` 和 {name}`LT` 实例中实现的关系组成。

```lean -show
-- 检查所有这些实例是否确实存在
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example : LE $(mkIdent t) := inferInstance)
    elabCommand <| ← `(example : LT $(mkIdent t) := inferInstance)
```

```lean -show
-- 检查所有这些实例是否确实存在
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x < y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x ≤ y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x = y) := inferInstance)
```


{docstring USize.le}

{docstring ISize.le}

{docstring UInt8.le}

{docstring Int8.le}

{docstring UInt16.le}

{docstring Int16.le}

{docstring UInt32.le}

{docstring Int32.le}

{docstring UInt64.le}

{docstring Int64.le}

{docstring USize.lt}

{docstring ISize.lt}

{docstring UInt8.lt}

{docstring Int8.lt}

{docstring UInt16.lt}

{docstring Int16.lt}

{docstring UInt32.lt}

{docstring Int32.lt}

{docstring UInt64.lt}

{docstring Int64.lt}

{docstring USize.decEq}

{docstring ISize.decEq}

{docstring UInt8.decEq}

{docstring Int8.decEq}

{docstring UInt16.decEq}

{docstring Int16.decEq}

{docstring UInt32.decEq}

{docstring Int32.decEq}

{docstring UInt64.decEq}

{docstring Int64.decEq}

{docstring USize.decLe}

{docstring ISize.decLe}

{docstring UInt8.decLe}

{docstring Int8.decLe}

{docstring UInt16.decLe}

{docstring Int16.decLe}

{docstring UInt32.decLe}

{docstring Int32.decLe}

{docstring UInt64.decLe}

{docstring Int64.decLe}

{docstring USize.decLt}

{docstring ISize.decLt}

{docstring UInt8.decLt}

{docstring Int8.decLt}

{docstring UInt16.decLt}

{docstring Int16.decLt}

{docstring UInt32.decLt}

{docstring Int32.decLt}

{docstring UInt64.decLt}

{docstring Int64.decLt}
