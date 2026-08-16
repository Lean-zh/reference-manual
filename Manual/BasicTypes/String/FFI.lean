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


#doc (Manual) "外部函数接口（FFI）" =>
%%%
tag := "string-ffi"
%%%


:::ffi "lean_string_object" (kind := type)
```
typedef struct {
    lean_object m_header;
    /* 字节长度，包含 '\0' 终止符 */
    size_t      m_size;
    size_t      m_capacity;
    /* UTF8 长度 */
    size_t      m_length;
    char        m_data[0];
} lean_string_object;
```
这是字符串在 C 中的表示。更多细节参见 {ref "string-runtime"}[运行时 {name}`String` 的说明]。
:::

:::ffi "lean_is_string"
```
bool lean_is_string(lean_object * o)
```

返回值为 `true` 当且仅当 `o` 是字符串；否则返回 `false`。
:::

:::ffi "lean_to_string"
```
lean_string_object * lean_to_string(lean_object * o)
```
在运行时检查 `o` 是否确为字符串。若 `o` 不是字符串，则断言失败。
:::

::::draft
:::planned 158
 * 完成 {lean}`String` 的完整 C API
:::
::::
