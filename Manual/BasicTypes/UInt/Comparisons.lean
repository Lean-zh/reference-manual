/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9

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


{zhdocstring USize.le Manual.ZhDocString.Ch19Ch20.G9.c001}

{zhdocstring ISize.le Manual.ZhDocString.Ch19Ch20.G9.c002}

{zhdocstring UInt8.le Manual.ZhDocString.Ch19Ch20.G9.c003}

{zhdocstring Int8.le Manual.ZhDocString.Ch19Ch20.G9.c004}

{zhdocstring UInt16.le Manual.ZhDocString.Ch19Ch20.G9.c005}

{zhdocstring Int16.le Manual.ZhDocString.Ch19Ch20.G9.c006}

{zhdocstring UInt32.le Manual.ZhDocString.Ch19Ch20.G9.c007}

{zhdocstring Int32.le Manual.ZhDocString.Ch19Ch20.G9.c008}

{zhdocstring UInt64.le Manual.ZhDocString.Ch19Ch20.G9.c009}

{zhdocstring Int64.le Manual.ZhDocString.Ch19Ch20.G9.c010}

{zhdocstring USize.lt Manual.ZhDocString.Ch19Ch20.G9.c011}

{zhdocstring ISize.lt Manual.ZhDocString.Ch19Ch20.G9.c012}

{zhdocstring UInt8.lt Manual.ZhDocString.Ch19Ch20.G9.c013}

{zhdocstring Int8.lt Manual.ZhDocString.Ch19Ch20.G9.c014}

{zhdocstring UInt16.lt Manual.ZhDocString.Ch19Ch20.G9.c015}

{zhdocstring Int16.lt Manual.ZhDocString.Ch19Ch20.G9.c016}

{zhdocstring UInt32.lt Manual.ZhDocString.Ch19Ch20.G9.c017}

{zhdocstring Int32.lt Manual.ZhDocString.Ch19Ch20.G9.c018}

{zhdocstring UInt64.lt Manual.ZhDocString.Ch19Ch20.G9.c019}

{zhdocstring Int64.lt Manual.ZhDocString.Ch19Ch20.G9.c020}

{zhdocstring USize.decEq Manual.ZhDocString.Ch19Ch20.G9.c021}

{zhdocstring ISize.decEq Manual.ZhDocString.Ch19Ch20.G9.c022}

{zhdocstring UInt8.decEq Manual.ZhDocString.Ch19Ch20.G9.c023}

{zhdocstring Int8.decEq Manual.ZhDocString.Ch19Ch20.G9.c024}

{zhdocstring UInt16.decEq Manual.ZhDocString.Ch19Ch20.G9.c025}

{zhdocstring Int16.decEq Manual.ZhDocString.Ch19Ch20.G9.c026}

{zhdocstring UInt32.decEq Manual.ZhDocString.Ch19Ch20.G9.c027}

{zhdocstring Int32.decEq Manual.ZhDocString.Ch19Ch20.G9.c028}

{zhdocstring UInt64.decEq Manual.ZhDocString.Ch19Ch20.G9.c029}

{zhdocstring Int64.decEq Manual.ZhDocString.Ch19Ch20.G9.c030}

{zhdocstring USize.decLe Manual.ZhDocString.Ch19Ch20.G9.c031}

{zhdocstring ISize.decLe Manual.ZhDocString.Ch19Ch20.G9.c032}

{zhdocstring UInt8.decLe Manual.ZhDocString.Ch19Ch20.G9.c033}

{zhdocstring Int8.decLe Manual.ZhDocString.Ch19Ch20.G9.c034}

{zhdocstring UInt16.decLe Manual.ZhDocString.Ch19Ch20.G9.c035}

{zhdocstring Int16.decLe Manual.ZhDocString.Ch19Ch20.G9.c036}

{zhdocstring UInt32.decLe Manual.ZhDocString.Ch19Ch20.G9.c037}

{zhdocstring Int32.decLe Manual.ZhDocString.Ch19Ch20.G9.c038}

{zhdocstring UInt64.decLe Manual.ZhDocString.Ch19Ch20.G9.c039}

{zhdocstring Int64.decLe Manual.ZhDocString.Ch19Ch20.G9.c040}

{zhdocstring USize.decLt Manual.ZhDocString.Ch19Ch20.G9.c041}

{zhdocstring ISize.decLt Manual.ZhDocString.Ch19Ch20.G9.c042}

{zhdocstring UInt8.decLt Manual.ZhDocString.Ch19Ch20.G9.c043}

{zhdocstring Int8.decLt Manual.ZhDocString.Ch19Ch20.G9.c044}

{zhdocstring UInt16.decLt Manual.ZhDocString.Ch19Ch20.G9.c045}

{zhdocstring Int16.decLt Manual.ZhDocString.Ch19Ch20.G9.c046}

{zhdocstring UInt32.decLt Manual.ZhDocString.Ch19Ch20.G9.c047}

{zhdocstring Int32.decLt Manual.ZhDocString.Ch19Ch20.G9.c048}

{zhdocstring UInt64.decLt Manual.ZhDocString.Ch19Ch20.G9.c049}

{zhdocstring Int64.decLt Manual.ZhDocString.Ch19Ch20.G9.c050}
