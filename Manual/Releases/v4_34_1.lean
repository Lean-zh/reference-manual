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

#doc (Manual) "Lean 4.34.1 (2026-09-24)" =>
%%%
tag := "release-v4.34.1"
file := "v4.34.1"
%%%

此补丁版本包含多项运行时修复，
建议所有 v4.34.0 或更早版本的用户升级。

此版本合入了 3 项更改。
除下面列出的 0 项新增功能
和 3 项修复外，
还有 0 项重构，
0 项文档改进，
0 项性能改进，
0 项测试套件改进，
以及 0 项其他更改。

# 编译器
%%%
file := "Compiler"
tag := "Manual-Releases-v4_34_1-Compiler"
%%%

```markdown

- [#15289](https://github.com/leanprover/lean4/pull/15289)
  当共享子项的引用数超过 `INT_MAX` 时，让最大共享机制（包括内核对所检查每个定理的共享）触发 panic，而非最终在仍有引用时释放子项。在超过 100GB 的输入上，无法排除以此触发官方内核未定义行为、并进一步构造 False 证明的可能。不基于 Lean 运行时或不使用此特定函数的 nanoda、con-leche 等内核不受影响。

- [#15288](https://github.com/leanprover/lean4/pull/15288)
  修复大量入引用的对象在线程间共享时可能出现的未定义行为。官方内核的默认配置（comparator 及 `lake check/compare` 所用配置）不使用多线程，但 con-leche 等基于 Lean 的检查器可能受影响。

- [#15241](https://github.com/leanprover/lean4/pull/15241)
  防止删除级联释放因引用计数上溢或下溢而被冻结的对象。与 #14838 一样，在至少有 18GB 可用内存的机器上，此问题可能触发官方内核的释放后使用，并进一步构造 False 的证明。不依赖 Lean 运行时的 nanoda、con-ron 等内核不受影响。

```
