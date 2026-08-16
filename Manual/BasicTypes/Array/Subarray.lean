/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "子数组" =>
%%%
tag := "subarray"
%%%

:::leanSection
```lean -show
variable {α : Type u}
```

类型 {lean}`Subarray α` 是 {lean}`Std.Slice α` 的缩写。
这意味着，除了本节中的运算符外，还可以使用{tech (key := "generalized field notation")}[泛化字段记号]来调用 {namespace}`Std.Slice` 命名空间中的函数，例如 {name}`Std.Slice.foldl`。
:::

{zhdocstring Subarray Manual.ZhDocString.Ch19Ch20.G9.c094}

{zhdocstring Subarray.empty Manual.ZhDocString.Ch19Ch20.G9.c095}

# 数组数据

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Array-Data"
%%%
{zhdocstring Subarray.array Manual.ZhDocString.Ch19Ch20.G9.c096}

{zhdocstring Subarray.start Manual.ZhDocString.Ch19Ch20.G9.c097}

{zhdocstring Subarray.stop Manual.ZhDocString.Ch19Ch20.G9.c098}

{zhdocstring Subarray.start_le_stop Manual.ZhDocString.Ch19Ch20.G9.c099}

{zhdocstring Subarray.stop_le_array_size Manual.ZhDocString.Ch19Ch20.G9.c100}

# 调整大小

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Resizing"
%%%
{zhdocstring Subarray.drop Manual.ZhDocString.Ch19Ch20.G9.c101}

{zhdocstring Subarray.take Manual.ZhDocString.Ch19Ch20.G9.c102}

{zhdocstring Subarray.popFront Manual.ZhDocString.Ch19Ch20.G9.c103}

{zhdocstring Subarray.split Manual.ZhDocString.Ch19Ch20.G9.c104}

# 查找

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Lookups"
%%%
{zhdocstring Subarray.get Manual.ZhDocString.Ch19Ch20.G9.c105}

{zhdocstring Subarray.get! Manual.ZhDocString.Ch19Ch20.G9.c106}

{zhdocstring Subarray.getD Manual.ZhDocString.Ch19Ch20.G9.c107}

# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Iteration"
%%%
{zhdocstring Subarray.foldr Manual.ZhDocString.Ch19Ch20.G9.c108}

{zhdocstring Subarray.foldrM Manual.ZhDocString.Ch19Ch20.G9.c109}

{zhdocstring Subarray.forM Manual.ZhDocString.Ch19Ch20.G9.c110}

{zhdocstring Subarray.forRevM Manual.ZhDocString.Ch19Ch20.G9.c111}

{zhdocstring Subarray.forIn Manual.ZhDocString.Ch19Ch20.G9.c112}

# 元素谓词

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Element-Predicates"
%%%
{zhdocstring Subarray.findRev? Manual.ZhDocString.Ch19Ch20.G9.c113}

{zhdocstring Subarray.findRevM? Manual.ZhDocString.Ch19Ch20.G9.c114}

{zhdocstring Subarray.findSomeRevM? Manual.ZhDocString.Ch19Ch20.G9.c115}

{zhdocstring Subarray.all Manual.ZhDocString.Ch19Ch20.G9.c116}

{zhdocstring Subarray.allM Manual.ZhDocString.Ch19Ch20.G9.c117}

{zhdocstring Subarray.any Manual.ZhDocString.Ch19Ch20.G9.c118}

{zhdocstring Subarray.anyM Manual.ZhDocString.Ch19Ch20.G9.c119}
