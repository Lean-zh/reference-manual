/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Module


import Manual.Meta
import Manual.ZhDocString.BuildTools.Lake
import Manual.BuildTools.Lake.API
import Manual.BuildTools.Lake.Builds
import Manual.BuildTools.Lake.Cache
import Manual.BuildTools.Lake.CLI
import Manual.BuildTools.Lake.Config
import Manual.BuildTools.Lake.Drivers
import Manual.BuildTools.Lake.PackageOverrides
import Manual.BuildTools.Lake.Scripts

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Lake" =>
%%%
tag := "lake"
file := "Lake"
%%%

Lake 是标准的 Lean 构建工具。
它负责：
 * 配置{tech (key := "builds")}[构建]并构建 Lean 代码
 * 获取并构建外部{tech (key := "dependencies")}[依赖]
 * 与 Lean 包服务器 [Reservoir](https://reservoir.lean-lang.org/){TODO}[此处需添加章节交叉引用] 集成
 * 运行测试、代码检查器及其他{tech (key := "development workflows")}[开发工作流]

Lake 是可扩展的。
它提供了一组丰富的接口，可用于为非 Lean 编写的软件工件定义增量构建任务，以自动化管理任务并与外部工作流集成。
对于不需要这些特性的构建配置，Lake 提供了一种声明式配置语言，可以写成 TOML 或 Lean 文件。

本节介绍 Lake 的{ref "lake-builds"}[构建]、{ref "lake-cache"}[缓存]、{ref "lake-workflows"}[工作流]、{ref "lake-cli"}[命令行界面]、{ref "lake-config"}[配置文件]以及{ref "lake-api"}[内部接口]。
它们共享一套概念和术语。


# 概念与术语
%%%
tag := "lake-vocab"
%%%

{deftech (key := "package")}_包_ 是 Lean 代码分发的基本单位。
一个包可以包含多个库或可执行程序。
一个包由一个目录组成，其中包含一个 {tech (key := "package configuration")}[包配置] 文件以及源代码。
包可以 {deftech (key := "require")}_请求_ 其他包，在这种情况下，这些包的代码（更确切地说，它们的 {tech (key := "targets")}[目标]）将变为可用状态。
所请求的包称为{deftech (key := "dependencies")}_依赖_。
一个包的 {deftech (key := "direct dependencies")}_直接依赖_ 是它所请求的包，而 {deftech (key := "transitive dependencies")}_传递依赖_ 则是包的直接依赖及其直接依赖的传递依赖。
包可以从 Lean 包仓库 [Reservoir](https://reservoir.lean-lang.org/){TODO}[此处需添加章节交叉引用] 获取，或者从手动指定的位置获取。
{deftech (key := "Git dependencies")}_Git 依赖_ 通过 Git 仓库 URL 及修订版本（分支、标签或哈希）指定，并在构建之前必须克隆到本地，而本地的 {deftech (key := "path dependencies")}_路径依赖_ 则通过相对于包目录的路径指定。

:::paragraph
{deftech (key := "workspace")}_工作区_ 是磁盘上的一个目录，包含一个 {tech (key := "package")}[包] 的源代码工作副本，以及所有未指定为本地路径的 {tech (key := "transitive dependencies")}[传递依赖] 的源代码。
为其创建工作区的包即为 {deftech (key := "root package")}_根包_。
工作区还包含为该包构建的任何 {tech (key := "artifacts")}[工件]，从而支持 {tech (key := "incremental builds")}[增量构建]。
一个目录要被视为工作区，并不需要预先存在依赖和工件；如果它们缺失，诸如 {lake}`update` 和 {lake}`build` 这样的命令会生成它们。
Lake 通常在工作区中使用。{margin}[创建工作区的 {lake}`init` 和 {lake}`new` 是例外。]
工作区通常具有以下布局：

 * `lean-toolchain`：{tech (key := "toolchain file")}[工具链文件]。
 * `lakefile.toml` 或 `lakefile.lean`：根包的 {tech (key := "package configuration")}[包配置] 文件。
 * `lake-manifest.json`：根包的 {tech (key := "manifest")}[清单]。
 * `.lake/`：Lake 管理的中间状态，例如已构建的 {tech (key := "artifacts")}[工件] 和依赖源代码。
   * `.lake/lakefile.olean`：根包的配置（已缓存）。
   * `.lake/packages/`：工作区的 {deftech (key := "package directory")}_包目录_，其中包含根包的所有非本地传递依赖的副本，并在它们各自的 `.lake` 目录中包含已构建的工件。
   * `.lake/build/`：{deftech (key := "build directory")}_构建目录_，其中包含根包的已构建工件：
     * `.lake/build/bin`：包的 {deftech (key := "binary directory")}_二进制目录_，其中包含已构建的可执行文件。
     * `.lake/build/lib`：包的 _库目录_，其中包含已构建的库和 {tech (key := ".olean files")}[`.olean` 文件]。
     * `.lake/build/ir`：包的中间结果目录，其中包含生成的中间工件，主要是 C 代码。
:::

:::figure "工作区布局" (tag :="workspace-layout")
```diagram
open Illuminate in
  let txt (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, anchor := TextAnchor.start }
  let bold (s : String) (size : Float := 11) : Diagram SVG :=
    .text s { fontSize := size, bold := true, anchor := TextAnchor.start }
  let mono (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, fontFamily := "monospace", anchor := TextAnchor.start }
  let items (ss : List String) (size : Float := 10) : Diagram SVG :=
    Diagram.vsep 3 (ss.map fun s => txt s size) (align := .left)
  let borderedBox (title : String) (content : Diagram SVG)
      (titleSize : Float := 11) (pad : Float := 8) : Diagram SVG :=
    Diagram.vsep 4 [bold title titleSize, content] (align := .left)
      |>.pad pad |>.frame (padding := 2) (cornerRadius := 4)

  let toolchain := mono "lean-toolchain"
  let rootPkg := borderedBox "根包" <|
    items [
      "包配置文件 (lakefile.lean)",
      "库",
      "可执行文件",
      "清单 (lake-manifest.json)"
    ]
  let depItems := items ["包配置文件", "库", "可执行文件", "工件"] 8
  let dep1 := borderedBox "依赖 1" depItems 9 6
  let dep2 := borderedBox "依赖 2" depItems 9 6
  let dots : Diagram SVG := .text "⋯" { fontSize := 14 }
  let packages := borderedBox "包" <|
    Diagram.vsep 8 [Diagram.hsep 12 [dep1, dep2], dots] (align := .left)
  let artifacts := borderedBox "工件" <|
    items ["已构建的库", "已构建的可执行文件"]
  let lakeDir := borderedBox "Lake 目录 (.lake)" <|
    Diagram.vsep 10 [packages, artifacts] (align := .left)
  borderedBox "工作区" <|
    Diagram.vsep 10 [toolchain, rootPkg, lakeDir] (align := .left)


```
:::

:::paragraph
{deftech (key := "package configuration")}_包配置_ 文件指定了一个包的依赖、设置和目标。
包可以指定适用于其包含的所有目标的配置选项。
它们可以用两种格式编写：
 * {ref "lake-config-toml"}[TOML 格式]（`lakefile.toml`）用于完全声明式的包配置。
 * {ref "lake-config-lean"}[Lean 格式]（`lakefile.lean`）另外支持使用 Lean 代码来以声明式选项不支持的方式配置包。
:::

{deftech (key := "manifest")}_清单_ 追踪包中使用的其他包的特定版本。
清单和 {tech (key := "package configuration")}[包配置] 文件共同为一个包指定了唯一的一组传递依赖。
在构建之前，Lake 会将每个依赖的本地副本与清单中指定的版本同步。
如果没有可用的清单，Lake 会获取每个依赖的最新匹配版本并创建一个清单。
如果清单中列出的包名与包所使用的名称不匹配，则会报错；在构建之前必须使用 {lake}`update` 更新清单。
清单应被视为包代码的一部分，通常应检入版本控制系统。

:::paragraph
{deftech (key := "target")}_目标_ 表示用户可以请求的输出。
持久的构建输出，例如目标代码、可执行二进制文件或 {tech (key := ".olean file")}[`.olean` 文件]，被称为 {deftech (key := "artifact")}_工件_。
在生成工件的过程中，Lake 可能需要生成进一步的工件；例如，将 Lean 程序编译为可执行文件要求它及其依赖被编译为目标文件，而这些文件本身是从 C 源文件生成的，C 源文件则是通过对 Lean 源文件进行精译并生成 {tech (key := ".olean files")}[`.olean` 文件] 得出的。
该链条中的每个环节都是一个目标，Lake 会安排它们依次构建。
处于链条起点的是 {deftech (key := "initial targets")}_初始目标_：
 * {tech (key := "Packages")}_包_ 是作为一个单元分发的 Lean 代码单元。
 * {deftech (key := "Libraries")}_库_ 是 Lean {tech (key := "module")}[模块] 的集合，在一个或多个 {deftech (key := "module roots")}_模块根_ 下按层次结构组织。
 * {deftech (key := "Executables")}_可执行文件_ 由一个定义了 `main` 的_单个_模块组成。
 * {deftech (key := "External libraries")}_外部库_ 是非 Lean 的*静态*库，它们将链接到包及依赖它的包的二进制文件，包括它们的共享库和可执行文件。
 * {deftech (key := "Custom targets")}_自定义目标_ 包含运行构建的任意代码，使用 Lake 的内部接口编写。

除了它们的 Lean 代码外，包、库和可执行文件还包含影响后续构建步骤的配置设置。
包可以指定一组 {deftech (key := "default targets")}_默认目标_。
默认目标是包中要在指定了包但未指定特定目标的上下文中构建的初始目标。
:::

:::paragraph
{deftech (key := "log")}_日志_ 包含在构建期间生成的信息。
保存日志是为了在 {tech (key := "incremental builds")}[增量构建] 期间进行重放。
日志中的消息按严重程度分为四个级别：

 1. _追踪消息_包含通常特定于运行构建的机器的内部构建详细信息，包括传递给命令外壳的 Lean 及其他工具的具体调用。
 2. _信息性消息_包含通常不表示代码有问题的常规信息输出，例如 {keywordOf Lean.Parser.Command.eval}`#eval` 命令的结果。
 3. _警告_指出潜在问题，例如未使用的变量绑定。
 4. _错误_解释为什么解析和精译无法完成。

默认情况下，追踪消息被隐藏，其他的被显示。
阈值可以通过 {lakeOpt}`--log-level` 选项、{lakeOpt}`--verbose` 标志或 {lakeOpt}`--quiet` 标志进行调整。
:::

{include 2 Manual.BuildTools.Lake.PackageOverrides}

{include 0 Manual.BuildTools.Lake.Builds}

{include 0 Manual.BuildTools.Lake.Cache}

# 开发工作流
%%%
tag := "lake-workflows"
%%%

开发形式化数学或软件的过程不仅包含编写和构建代码。
测试、{tech (key := "lint driver")}[代码检查]及其他定期执行的固定过程统称为{deftech (key := "development workflows")}_开发工作流_。
Lake 通过 {lake}`test` 和 {lake}`lint` 命令直接支持测试和代码检查，这些命令使用包中配置的{ref "test-lint-drivers"}[测试和代码检查驱动程序]。
Lean 还提供内置代码检查器。
{ref "linters"}[代码检查器与代码质量]一章介绍了这些检查器，以及 {lake}`lint` 为它们提供的{ref "linting-workflows"}[代码检查工作流]。
对于其他工作流，Lake 提供{ref "lake-scripts"}[脚本]，即可以使用{ref "lake-api"}[Lake API]执行任意任务的程序。
脚本使用{ref "lake-config-lean"}[Lean 配置格式]定义，并通过命令行的 {lake}`script run` 运行。

{include 2 Manual.BuildTools.Lake.Drivers}

{include 2 Manual.BuildTools.Lake.Scripts}

{include 0 Manual.BuildTools.Lake.CLI}

{include 0 Manual.BuildTools.Lake.Config}

{include 0 Manual.BuildTools.Lake.API}
