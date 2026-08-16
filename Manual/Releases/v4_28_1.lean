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

#doc (Manual) "Lean4.28.1 (2026-04-14)" =>
%%%
tag := "release-v4.28.1"
file := "v4.28.1"
%%%

此版本有 2 处更改。
除了 0 个功能添加之外，
以及下面列出的 1 个修复，
有 0 处重构更改，
0 项文档改进，
0 性能改进，
对测试套件进行 0 项改进，
以及其他 1 项变更。

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___1-_LPAR_2026-04-14_RPAR_--Compiler"
%%%

```markdown

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  修复了 `lean_io_prim_handle_read` 中由分配大小计算发生整数溢出而触发的堆缓冲区溢出。
  此外，所有相关的分配路径现在都使用若干经过检查的算术运算，
  从而让未来可能出现的溢出转化为崩溃，而不是继续执行。
  相关代码现在会改为抛出内存不足错误。

```
