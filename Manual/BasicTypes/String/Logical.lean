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


#doc (Manual) "逻辑模型" =>

{docstring String}

:::paragraph
Lean 中字符串的逻辑模型是一个包含两个字段的结构体：

 * {name}`String.toByteArray` 是一个 {name}`ByteArray`，包含了该字符串的 UTF-8 编码。

 * {name}`String.isValidUTF8` 是一个证明，证明这些字节实际上是字符串的有效 UTF-8 编码。

此模型允许使用针对字节数组的操作在低级别上指定并证明关于字符串操作的属性，同时仍能建立在字节数组理论之上。
同时，它足够接近真实的运行时表示，从而避免了逻辑模型与运行时表示中有意义的操作之间的阻抗失配。
:::

# 向后兼容性

在 Lean 的早期版本中，字符串的逻辑模型是包含字符列表的结构体。
该模型仍然有用。
它仍然可以使用 {name}`String.ofList`（将字符列表转换为 {name}`String`）以及 {name}`String.toList`（将 {name}`String` 转换为字符列表）来访问。

{docstring String.ofList}

{docstring String.toList}

{docstring String}

:::paragraph
Lean 中字符串的逻辑模型是一个包含两个字段的结构体：

 * {name}`String.toByteArray` 是一个 {name}`ByteArray`，包含了该字符串的 UTF-8 编码。

 * {name}`String.isValidUTF8` 是一个证明，证明这些字节实际上是字符串的有效 UTF-8 编码。

此模型允许使用针对字节数组的操作在低级别上指定并证明关于字符串操作的属性，同时仍能建立在字节数组理论之上。
同时，它足够接近真实的运行时表示，从而避免了逻辑模型与运行时表示中有意义的操作之间的阻抗失配。
:::

# 向后兼容性

%%%
tag := "Lean-__________________--Basic-Types--Strings--Logical-Model--Backwards-Compatibility"
%%%
在 Lean 的早期版本中，字符串的逻辑模型是包含字符列表的结构体。
该模型仍然有用。
它仍然可以使用 {name}`String.ofList`（将字符列表转换为 {name}`String`）以及 {name}`String.toList`（将 {name}`String` 转换为字符列表）来访问。

{docstring String.ofList}

{docstring String.toList}
