/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

open Verso.Genre Manual

#doc (Manual) "支持的平台" =>
%%%
tag := "platforms"
file := "platforms"
number := false
htmlSplit := .never
%%%



# 第一层级

:::paragraph
第一层级平台是 Lean 由 CI 基础设施构建并测试的平台。
这些平台的 Lean 二进制发行版可通过 {ref "elan"}[`elan`] 获取。
第一层级平台包括：

* 使用 glibc 2.26+ 的 `x86-64` Linux
* 使用 glibc 2.27+ 的 `aarch64` Linux
* `aarch64`（Apple 芯片）macOS 10.15+
* `x86-64` Windows 11（任意版本）、Windows 10（版本 1903 或更高）、Windows Server 2022、Windows Server 2025
:::

# 第二层级

第二层级平台是 Lean 为其交叉编译但未由 CI 测试的平台。
这些平台也提供二进制发行版。

由于缺少自动化测试，发行版可能在不显眼的情况下损坏。
欢迎报告问题并提交修复。

:::paragraph
第二层级平台包括：
* `x86-64` macOS 10.15+
* Emscripten WebAssembly
:::
