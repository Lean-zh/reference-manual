/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G6

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

{zhdocstring ISize.neg Manual.ZhDocString.Ch19Ch20.G6.c171}

{zhdocstring Int8.neg Manual.ZhDocString.Ch19Ch20.G6.c172}

{zhdocstring Int16.neg Manual.ZhDocString.Ch19Ch20.G6.c173}

{zhdocstring Int32.neg Manual.ZhDocString.Ch19Ch20.G6.c174}

{zhdocstring Int64.neg Manual.ZhDocString.Ch19Ch20.G6.c175}

{zhdocstring USize.neg Manual.ZhDocString.Ch19Ch20.G6.c176}

{zhdocstring UInt8.neg Manual.ZhDocString.Ch19Ch20.G6.c177}

{zhdocstring UInt16.neg Manual.ZhDocString.Ch19Ch20.G6.c178}

{zhdocstring UInt32.neg Manual.ZhDocString.Ch19Ch20.G6.c179}

{zhdocstring UInt64.neg Manual.ZhDocString.Ch19Ch20.G6.c180}

{zhdocstring USize.add Manual.ZhDocString.Ch19Ch20.G6.c181}

{zhdocstring ISize.add Manual.ZhDocString.Ch19Ch20.G6.c182}

{zhdocstring UInt8.add Manual.ZhDocString.Ch19Ch20.G6.c183}

{zhdocstring Int8.add Manual.ZhDocString.Ch19Ch20.G6.c184}

{zhdocstring UInt16.add Manual.ZhDocString.Ch19Ch20.G6.c185}

{zhdocstring Int16.add Manual.ZhDocString.Ch19Ch20.G6.c186}

{zhdocstring UInt32.add Manual.ZhDocString.Ch19Ch20.G6.c187}

{zhdocstring Int32.add Manual.ZhDocString.Ch19Ch20.G6.c188}

{zhdocstring UInt64.add Manual.ZhDocString.Ch19Ch20.G6.c189}

{zhdocstring Int64.add Manual.ZhDocString.Ch19Ch20.G6.c190}

{zhdocstring USize.sub Manual.ZhDocString.Ch19Ch20.G6.c191}

{zhdocstring ISize.sub Manual.ZhDocString.Ch19Ch20.G6.c192}

{zhdocstring UInt8.sub Manual.ZhDocString.Ch19Ch20.G6.c193}

{zhdocstring Int8.sub Manual.ZhDocString.Ch19Ch20.G6.c194}

{zhdocstring UInt16.sub Manual.ZhDocString.Ch19Ch20.G6.c195}

{zhdocstring Int16.sub Manual.ZhDocString.Ch19Ch20.G6.c196}

{zhdocstring UInt32.sub Manual.ZhDocString.Ch19Ch20.G6.c197}

{zhdocstring Int32.sub Manual.ZhDocString.Ch19Ch20.G6.c198}

{zhdocstring UInt64.sub Manual.ZhDocString.Ch19Ch20.G6.c199}

{zhdocstring Int64.sub Manual.ZhDocString.Ch19Ch20.G6.c200}

{zhdocstring USize.mul Manual.ZhDocString.Ch19Ch20.G6.c201}

{zhdocstring ISize.mul Manual.ZhDocString.Ch19Ch20.G6.c202}

{zhdocstring UInt8.mul Manual.ZhDocString.Ch19Ch20.G6.c203}

{zhdocstring Int8.mul Manual.ZhDocString.Ch19Ch20.G6.c204}

{zhdocstring UInt16.mul Manual.ZhDocString.Ch19Ch20.G6.c205}

{zhdocstring Int16.mul Manual.ZhDocString.Ch19Ch20.G6.c206}

{zhdocstring UInt32.mul Manual.ZhDocString.Ch19Ch20.G6.c207}

{zhdocstring Int32.mul Manual.ZhDocString.Ch19Ch20.G6.c208}

{zhdocstring UInt64.mul Manual.ZhDocString.Ch19Ch20.G6.c209}

{zhdocstring Int64.mul Manual.ZhDocString.Ch19Ch20.G6.c210}

{zhdocstring USize.div Manual.ZhDocString.Ch19Ch20.G6.c211}

{zhdocstring ISize.div Manual.ZhDocString.Ch19Ch20.G6.c212}

{zhdocstring UInt8.div Manual.ZhDocString.Ch19Ch20.G6.c213}

{zhdocstring Int8.div Manual.ZhDocString.Ch19Ch20.G6.c214}

{zhdocstring UInt16.div Manual.ZhDocString.Ch19Ch20.G6.c215}

{zhdocstring Int16.div Manual.ZhDocString.Ch19Ch20.G6.c216}

{zhdocstring UInt32.div Manual.ZhDocString.Ch19Ch20.G6.c217}

{zhdocstring Int32.div Manual.ZhDocString.Ch19Ch20.G6.c218}

{zhdocstring UInt64.div Manual.ZhDocString.Ch19Ch20.G6.c219}

{zhdocstring Int64.div Manual.ZhDocString.Ch19Ch20.G6.c220}

{zhdocstring USize.mod Manual.ZhDocString.Ch19Ch20.G6.c221}

{zhdocstring ISize.mod Manual.ZhDocString.Ch19Ch20.G6.c222}

{zhdocstring UInt8.mod Manual.ZhDocString.Ch19Ch20.G6.c223}

{zhdocstring Int8.mod Manual.ZhDocString.Ch19Ch20.G6.c224}

{zhdocstring UInt16.mod Manual.ZhDocString.Ch19Ch20.G6.c225}

{zhdocstring Int16.mod Manual.ZhDocString.Ch19Ch20.G6.c226}

{zhdocstring UInt32.mod Manual.ZhDocString.Ch19Ch20.G6.c227}

{zhdocstring Int32.mod Manual.ZhDocString.Ch19Ch20.G6.c228}

{zhdocstring UInt64.mod Manual.ZhDocString.Ch19Ch20.G6.c229}

{zhdocstring Int64.mod Manual.ZhDocString.Ch19Ch20.G6.c230}

{zhdocstring USize.log2 Manual.ZhDocString.Ch19Ch20.G6.c231}

{zhdocstring UInt8.log2 Manual.ZhDocString.Ch19Ch20.G6.c232}

{zhdocstring UInt16.log2 Manual.ZhDocString.Ch19Ch20.G6.c233}

{zhdocstring UInt32.log2 Manual.ZhDocString.Ch19Ch20.G6.c234}

{zhdocstring UInt64.log2 Manual.ZhDocString.Ch19Ch20.G6.c235}

{zhdocstring ISize.abs Manual.ZhDocString.Ch19Ch20.G6.c236}

{zhdocstring Int8.abs Manual.ZhDocString.Ch19Ch20.G6.c237}

{zhdocstring Int16.abs Manual.ZhDocString.Ch19Ch20.G6.c238}

{zhdocstring Int32.abs Manual.ZhDocString.Ch19Ch20.G6.c239}

{zhdocstring Int64.abs Manual.ZhDocString.Ch19Ch20.G6.c240}
