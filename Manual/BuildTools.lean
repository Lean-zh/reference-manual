/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta
import Manual.BuildTools.Lake
import Manual.BuildTools.Elan

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "构建工具与发行" =>
%%%
tag := "build-tools-and-distribution"
shortContextTitle := "构建工具"
file := "Build-Tools-and-Distribution"
%%%

:::paragraph
Lean {deftech (key := "toolchain")}[工具链]是一组命令行工具，用于检查证明并编译由多个 Lean 文件组成的程序。
工具链由 `elan` 管理；它会按需安装工具链。
Lean 工具链采用自包含设计，大多数命令行用户除了 `lake` 和 `elan` 之外，无需显式调用其中的其他工具。
其中包含以下工具：

: `lean`

  Lean 编译器，用于精译和编译 Lean 源文件。

: `lake`

  Lean 构建工具，在跟踪依赖关系的同时增量调用 `lean` 和其他工具。

: `leanc`

  Lean 随附的 C 编译器，它是 [Clang](https://clang.llvm.org/) 的一个版本。

: `leanmake`

  `make` 构建工具的一种实现，用于编译 C 依赖项。

: `leanchecker`

  一种通过 Lean 内核重放 {tech (key := ".olean files")}[`.olean` 文件]中精译结果的工具，为所有项均已得到正确检查提供额外保证。
:::

除这些构建工具外，工具链还包含构建 Lean 代码所需的文件。
其中包括源代码、{tech (key := ".olean files")}[`.olean` 文件]、已编译的库、C 头文件以及已编译的 Lean 运行时系统。
其中还包括 Lean 随附策略所使用的外部证明自动化工具，例如 {tactic}`bv_decide` 使用的 `cadical`。


{include 0 Manual.BuildTools.Lake}

{include 0 Manual.BuildTools.Elan}

# Reservoir 包仓库
%%%
tag := "reservoir"
draft := true
%%%


::: planned 76
 * 概念
 * 包与工具链版本
 * 标签与构建
:::
