/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

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

{docstring Subarray}

{docstring Subarray.empty}

# 数组数据

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Array-Data"
%%%
{docstring Subarray.array}

{docstring Subarray.start}

{docstring Subarray.stop}

{docstring Subarray.start_le_stop}

{docstring Subarray.stop_le_array_size}

# 调整大小

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Resizing"
%%%
{docstring Subarray.drop}

{docstring Subarray.take}

{docstring Subarray.popFront}

{docstring Subarray.split}

# 查找

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Lookups"
%%%
{docstring Subarray.get}

{docstring Subarray.get!}

{docstring Subarray.getD}

# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Iteration"
%%%
{docstring Subarray.foldr}

{docstring Subarray.foldrM}

{docstring Subarray.forM}

{docstring Subarray.forRevM}

{docstring Subarray.forIn}

# 元素谓词

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Subarrays--Element-Predicates"
%%%
{docstring Subarray.findRev?}

{docstring Subarray.findRevM?}

{docstring Subarray.findSomeRevM?}

{docstring Subarray.all}

{docstring Subarray.allM}

{docstring Subarray.any}

{docstring Subarray.anyM}
