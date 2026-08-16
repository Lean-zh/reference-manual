/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "精益4.29.1 (2026-04-14)" =>
%%%
tag := "release-v4.29.1"
file := "v4.29.1"
%%%

此版本有 1 项更改。
除了 0 个功能添加之外，
以及下面列出的 1 个修复，
有 0 处重构更改，
0 项文档改进，
0 性能改进，
对测试套件进行 0 项改进，
和 0 个其他更改。

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___1-_LPAR_2026-04-14_RPAR_--Compiler"
%%%

```markdown

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  fixes a heap buffer overflow in `lean_io_prim_handle_read` that was triggered through an
  integer overflow in the size computation of an allocation. In addition it places several checked
  arithmetic operations on all relevant allocation paths to have potential future overflows be turned
  into crashes instead. The offending code now throws an out of memory error instead.

```
