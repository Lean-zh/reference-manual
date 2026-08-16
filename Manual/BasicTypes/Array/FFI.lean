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


#doc (Manual) "FFI" =>
%%%
tag := "array-ffi"
%%%

:::ffi "lean_string_object" (kind := type)
```
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    lean_object * m_data[];
} lean_array_object;
```
数组在 C 中的表示。更多细节请参阅{ref "array-runtime"}[运行时 {name}`Array` 的说明]。
:::

:::ffi "lean_is_array"
```
bool lean_is_array(lean_object * o)
```

返回 `true` 表示 `o` 是数组；否则返回 `false`。
:::

:::ffi "lean_to_array"
```
lean_array_object * lean_to_array(lean_object * o)
```
执行运行时检查，确认 `o` 确实是数组。如果 `o` 不是数组，断言将失败。
:::

::::draft
:::planned 158
 * 完善 {lean}`Array` 的 C API
:::
::::
