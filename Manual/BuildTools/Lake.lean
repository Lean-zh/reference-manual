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
import Manual.BuildTools.Lake.CLI
import Manual.BuildTools.Lake.Config

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Lake" =>
%%%
tag := "lake"
%%%

Lake 是标准的 Lean 构建工具。
它负责：
 * 配置构建并构建 Lean 代码
 * 获取并构建外部依赖
 * 与 Reservoir（Lean 包服务器）集成
 * 运行测试、代码检查器及其它开发工作流

Lake 是可扩展的。
它提供了一组丰富的 API，可用于为非 Lean 编写的软件工件定义增量构建任务，以自动化管理任务并与外部工作流集成。
对于不需要这些特性的构建配置，Lake 提供了一种声明式配置语言，可以写成 TOML 或 Lean 文件。

本节介绍了 Lake 的 {ref "lake-cli"}[命令行界面]、{ref "lake-config"}[配置文件] 以及 {ref "lake-api"}[内部 API]。
这三者共享了一套概念和术语。


# 概念与术语
%%%
tag := "lake-vocab"
%%%

{deftech (key := "package")}_包_ 是 Lean 代码分发的基本单位。
一个包可以包含多个库或可执行程序。
一个包由一个目录组成，其中包含一个 {tech (key := "package configuration")}[包配置] 文件以及源代码。
包可以 {deftech (key := "require")}_请求_ 其他包，在这种情况下，这些包的代码（更确切地说，它们的 {tech (key := "targets")}[目标]）将变为可用状态。
一个包的 {deftech (key := "direct dependencies")}_直接依赖_ 是它所请求的包，而 {deftech (key := "transitive dependencies")}_传递依赖_ 则是包的直接依赖及其直接依赖的传递依赖。
包可以从 Lean 包仓库 [Reservoir](https://reservoir.lean-lang.org/){TODO}[添加章节交叉引用] 获取，或者从手动指定的位置获取。
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
  let rootPkg := borderedBox "Root package" <|
    items [
      "Package configuration file (lakefile.lean)",
      "Libraries",
      "Executables",
      "Manifest (lake-manifest.json)"
    ]
  let depItems := items ["Package configuration file", "Libraries", "Executables", "Artifacts"] 8
  let dep1 := borderedBox "Dependency 1" depItems 9 6
  let dep2 := borderedBox "Dependency 2" depItems 9 6
  let dots : Diagram SVG := .text "⋯" { fontSize := 14 }
  let packages := borderedBox "Packages" <|
    Diagram.vsep 8 [Diagram.hsep 12 [dep1, dep2], dots] (align := .left)
  let artifacts := borderedBox "Artifacts" <|
    items ["Built libraries", "Built executables"]
  let lakeDir := borderedBox "Lake Directory (.lake)" <|
    Diagram.vsep 10 [packages, artifacts] (align := .left)
  borderedBox "Workspace" <|
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
在生成工件的过程中，Lake 可能需要生成进一步的工件；例如，将 Lean 程序编译为可执行文件要求它及其依赖被编译为目标文件，而这些文件本身是从 C 源文件生成的，C 源文件则是通过对 Lean 源文件进行推导并生成 {tech (key := ".olean files")}[`.olean` 文件] 得出的。
该链条中的每个环节都是一个目标，Lake 会安排它们依次构建。
处于链条起点的是 {deftech (key := "initial targets")}_初始目标_：
 * {tech (key := "Packages")}_包_ 是作为一个单元分发的 Lean 代码单元。
 * {deftech (key := "Libraries")}_库_ 是 Lean {tech (key := "module")}[模块] 的集合，在一个或多个 {deftech (key := "module roots")}_模块根_ 下按层次结构组织。
 * {deftech (key := "Executables")}_可执行文件_ 由一个定义了 `main` 的_单个_模块组成。
 * {deftech (key := "External libraries")}_外部库_ 是非 Lean 的*静态*库，它们将链接到包及其依赖的二进制文件，包括它们的共享库和可执行文件。
 * {deftech (key := "Custom targets")}_自定义目标_ 包含运行构建的任意代码，使用 Lake 的内部 API 编写。

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
 4. _错误_解释为什么解析和推导无法完成。

默认情况下，追踪消息被隐藏，其他的被显示。
阈值可以通过 {lakeOpt}`--log-level` 选项、{lakeOpt}`--verbose` 标志或 {lakeOpt}`--quiet` 标志进行调整。
:::

## 包覆盖
%%%
tag := "package-overrides"
%%%

{tech (key := "package configuration")}[包配置] 和 {tech (key := "manifest")}[清单] 共同描述了 Lake 获取依赖的精确方式。
通常，这涉及通过网络从远程 Git 仓库获取本地副本。
如果无法访问远程仓库，Lake 会终止并报错。
因为依赖来源是可预测的，所以跨系统的构建是可重现的；在所有机器上都从相同来源以相同方式检索包。

尽管如此，仍存在无法采用与原始开发者相同的方式获取包依赖的情况。
例如，有些公司要求所有依赖在使用前都须经过审计，而且并不是每个人在工作时都能一直连接互联网。
在这些情况下，就有必要通过其他方式获取包。

Lake 的 {deftech (key := "package overrides")}_包覆盖_ 允许将包依赖从一个源重定向到另一个源，而无需修改任何 {tech (key := "package configurations")}[包配置] 或 {tech (key := "manifests")}[清单]。
它们不允许在 {tech (key := "workspace")}[工作区] 中添加或移除包。
工作区中所有的传递依赖都遵守重定向。
包覆盖文件是一个 JSON 文件，包含包条目的备用列表。
这些条目将优先于包的 {tech (key := "manifest")}[清单] 中的条目。
可以通过 {lakeOpt}`--packages` 选项，或者将其放置在 Lake 工作区内的固定路径 `.lake/package-overrides.json`，来将此文件提供给 Lake。

包覆盖文件中的包条目语法与 {tech (key := "manifest")}[清单] 的语法一致。
因此，可以把清单中的条目复制到包覆盖文件中（反之亦然）。
确定包条目所需语法的一种方法是：向 {tech (key := "package configuration")}[包配置] 中添加匹配所需配置的临时依赖，运行 {lake}`update` 以生成包含该依赖的清单，然后将清单中的条目复制到包覆盖文件中。

:::example "本地化远程依赖" (file := "Making Remote Dependencies Local")

考虑这样一个用例：在受限环境（例如出于安全原因）中开发程序，且没有网络连接。
团队希望编译一个用 Lean 编写的依赖于 [`@leanprover/Cli`](https://reservoir.lean-lang.org/@leanprover/Cli) 库来提供简单命令行界面的小工具。
该工具的 {tech (key := "manifest")}[清单] 因此如下所示：

```lakeManifest
{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [{
    "url": "https://github.com/leanprover/lean4-cli",
    "type": "git",
    "subDir": null,
    "scope": "leanprover",
    "rev": "0000000000000000000000000000000000000000",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inputRev": null,
    "inherited": false,
    "configFile": "lakefile.toml"
  }],
  "name": "myTool",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

该清单将指示 Lake 在构建此工具时从指定的 GitHub URL 下载 `Cli` 包。
但是，由于受限环境没有网络连接，如果不使用本地副本，构建将会失败。
这可以通过以下 {tech (key := "package overrides")}[包覆盖] 文件完成：

```lakePackageOverrides
{
  "version": "1.2.0",
  "packages": [{
    "type": "path",
    "dir": "/etc/lean-packages/Cli",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inherited": false,
    "configFile": "lakefile.toml"
  }]
}
```

有了这个文件，Lake 将把 `Cli` 依赖解析为位于路径 `/etc/lean-packages/Cli` 的本地包。

:::

## 构建

:::paragraph
生成所需的 {tech (key := "artifact")}[工件]，比如 {tech (key := ".olean file")}[`.olean` 文件] 或可执行二进制文件，被称为 {deftech (key := "build")}_构建_。
构建由 {lake}`build` 命令或需要工件存在的其他命令（例如 {lake}`exe`）触发。
构建包括以下步骤：

: {deftech (key := "configure package")}[配置包]

  如果 {tech (key := "package configuration")}[包配置] 文件比缓存的配置文件 `lakefile.olean` 更新，那么包配置就会被重新推导。
  当缓存文件缺失或者提供了 {lakeOpt}`--reconfigure` 或 {lakeOpt}`-R` 标志时，也会发生这种情况。
  使用 {lakeOpt}`-K` 对选项的更改不会触发配置文件的重新推导；在这些情况下，必须使用 {lakeOpt}`-R`。

: 计算依赖

  确定产生所需输出所需的工件集，以及产生它们的 {tech (key := "targets")}[目标] 和 {tech (key := "facets")}[分面]。
  该过程是递归的，结果是一个依赖_图_。
  图中的依赖与为包声明的依赖不同：包依赖于其他包，而构建目标依赖于其他构建目标，它们可能位于同一个包中，也可能位于不同的包中。
  给定目标的一个分面可能依赖于同一目标的其他分面。
  Lake 会自动分析 Lean 模块的导入以发现它们的依赖，并且可使用 {tomlField Lake.LeanLibConfig}`extraDepTargets` 字段向目标添加额外的依赖。

: 重放追踪

  Lake 不会从头开始重建依赖图中的所有内容，而是使用保存的 {deftech (key := "trace files")}_追踪文件_ 来确定哪些工件需要构建。
  在构建期间，Lake 会记录用于生成每个工件的源文件或其他工件，保存每个输入的哈希；这些 {deftech (key := "traces")}_追踪_ 保存在 {tech (key := "build directory")}[构建目录] 中。{margin}[更具体地说，每个工件的追踪文件包含其输入哈希值的 Merkle 树哈希混合。]
  如果所有输入均未修改，则不再重新构建相应的工件。
  追踪文件还额外记录了每个构建任务的 {tech (key := "log")}[日志]；这些输出会被重放，就好像工件被重新构建一样。
  在可能的情况下重用先前的构建产物被称为 {deftech (key := "incremental build")}_增量构建_。

: 构建工件

  当依赖图中所有未修改的依赖都从它们的追踪文件中重放后，Lake 会继续构建每个工件。
  这涉及在输入文件上运行适当的构建工具，并按对应分面的指定，保存工件及其追踪文件。
:::

Lake 使用两种不同的哈希算法。
文本文件在规范化换行符之后再进行哈希处理，以便仅因平台特定的换行约定不同而不同的文件也能生成相同的哈希值。
其他文件在哈希时则不作任何规范化。

与追踪文件一样，Lean 会缓存输入哈希。
每当构建一个工件时，其哈希值都会保存在一个独立的文件中，这样可以直接读取该文件，而无需从头计算哈希值。
这是一种性能优化。
可以通过 {lakeOpt}`--rehash` 命令行选项禁用此功能，导致所有哈希值都由其输入重新计算。

:::paragraph
在构建期间，会向底层构建工具提供以下目录：
 * {deftech (key := "source directory")}_源码目录_ 包含可供导入的 Lean 源代码。
 * {deftech (key := "library directories")}_库目录_ 包含 {tech (key := ".olean files")}[`.olean` 文件] 以及可用于链接的共享库和静态库；它通常由 {tech (key := "root package")}[根包] 的库目录（在 `.lake/build/lib` 下）、工作区中其他包的库目录、当前 Lean 工具链的库目录以及系统库目录组成。
 * {deftech (key := "Lake home")}_Lake 主目录_ 是安装 Lake 的目录，包含二进制文件、源代码和库。
   Lake 目录中的库在推导 Lake 配置文件时不可或缺，这样配置文件就能访问 Lean 的全部功能。
:::

## 分面
%%%
tag := "lake-facets"
%%%

{deftech (key := "facet")}_分面_ 描述了一个目标从另一个目标的生产过程。
从概念上讲，任何目标都可以拥有分面。
然而，可执行文件、外部库和自定义目标只提供单一的隐式分面。
包、库和模块拥有多个分面，调用 {lake}`build` 选定相应目标时，可以通过名称请求它们。

当没有显式请求分面，但指定了初始目标时，{lake}`build` 将产生初始目标的 {deftech (key := "default facet")}_默认分面_。
每种类型的初始目标都有相应的默认分面（例如从可执行文件目标生成可执行二进制文件或构建一个包的 {tech (key := "default targets")}[默认目标]）；可以在 {tech (key := "package configuration")}[包配置] 中或通过 Lake 的 {ref "lake-cli"}[命令行界面] 显式请求其他分面。
可以使用 Lake 的内部 API 来编写自定义分面。


```lakeHelp "build"
Build targets

USAGE:
  lake build [<targets>...] [-o <mappings>]

A target is specified with a string of the form:

  [@[<package>]/][<target>|[+]<module>][:<facet>]

You can also use the source path of a module as a target. For example,

  lake build Foo/Bar.lean:o

will build the Lean module (within the workspace) whose source file is
`Foo/Bar.lean` and compile the generated C file into a native object file.

The `@` and `+` markers can be used to disambiguate packages and modules
from file paths or other kinds of targets (e.g., executables or libraries).

LIBRARY FACETS:         build the library's ...
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  olean                 OLean (binary blob of Lean data for importers)
  ilean                 ILean (binary blob of metadata for the Lean LSP server)
  c                     compiled C file
  bc                    compiled LLVM bitcode file
  c.o                   compiled object file (of its C file)
  bc.o                  compiled object file (of its LLVM bitcode file)
  o                     compiled object file (of its configured backend)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet(s) of target `a`
  @a                    default target(s) of package `a`
  +A                    default facet(s) of module `A`
  @/a                   default facet(s) of target `a` of the root package
  @a/b                  default facet(s) of target `b` of package `a`
  @a/+A:c               C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default target(s) of the root
package. Package dependencies are not updated during a build.

With the Lake cache enabled, the `-o` option will cause Lake to track the
input-to-outputs mappings of targets in the root package touched during the
build and write them to the specified file at the end of the build. These
mappings can then be used to upload build artifacts to a remote cache with
`lake cache put`.
```


::::paragraph

包可用的分面有：

```lean -show
-- 始终使之与下方描述保持同步。这确保了列表是完整的。
/--
info: #[`package.barrel, `package.cache, `package.deps, `package.extraDep, `package.optBarrel, `package.optCache,
  `package.optRelease, `package.release, `package.transDeps]
-/
#guard_msgs in
#eval Lake.initPackageFacetConfigs.toList.map (·.1) |>.toArray |>.qsort (·.toString < ·.toString)
```
: `extraDep`

  包在 {tomlField Lake.PackageConfig}`extraDepTargets` 字段中指定的额外依赖目标的默认分面。

: `deps`

  包的 {tech (key := "direct dependencies")}[直接依赖]。

: `transDeps`

  包经过拓扑排序的 {tech (key := "transitive dependencies")}[传递依赖]。


: `optCache`

  包可选的缓存构建归档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取归档，*不会*导致整个构建失败。

: `cache`

  包的缓存构建归档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取归档，将导致整个构建失败。

: `optBarrel`

  包可选的缓存构建归档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取归档，*不会*导致整个构建失败。

: `barrel`

  包的缓存构建归档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取归档，将导致整个构建失败。

: `optRelease`

  来自 GitHub 发布版本的包可选构建归档。
  如果无法获取发布版本，*不会*导致整个构建失败。

: `release`

  来自 GitHub 发布版本的包构建归档。
  如果无法获取归档，将导致整个构建失败。


::::

```lean -show
-- 始终使之与下方描述保持同步。这确保了列表是完整的。
/--
info: [`lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.static.export, `lean_lib.shared, `lean_lib.modules, `lean_lib.static,
  `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```

:::paragraph

库可用的分面有：

: `leanArts`

  Lean 编译器为库或可执行文件生成的工件（{tech (key := ".olean files")}`*.olean`、`*.ilean` 和 `*.c` 文件）。

: `static`

  由 C 编译器从 `leanArts` 生成的静态库（即 `*.a` 文件）。

: `static.export`

  由 C 编译器从 `leanArts` 生成的具有导出符号的静态库（即 `*.a` 文件）。

: `shared`

  由 C 编译器从 `leanArts` 生成的共享库（取决于平台，即 `*.so`、`*.dll` 或 `*.dylib` 文件）。

: `extraDep`

  Lean 库及其所属包的 {tomlField Lake.LeanLibConfig}`extraDepTargets`。

:::

:::paragraph

可执行文件只有一个由可执行二进制文件组成的 `exe` 分面。

:::

```lean -show
-- 始终使之与下方描述保持同步。这确保了列表是完整的。
/--
info: module.bc
module.bc.o
module.c
module.c.o
module.c.o.export
module.c.o.noexport
module.depHash
module.depTrace
module.deps
module.dynlib
module.exportInfo
module.header
module.ilean
module.importAllArts
module.importArts
module.importInfo
module.imports
module.input
module.ir
module.ir.sig
module.lean
module.leanArts
module.linkInfoExport
module.linkInfoNoExport
module.ltar
module.o
module.o.export
module.o.noexport
module.olean
module.olean.private
module.olean.server
module.precompileImports
module.presetup
module.setup
module.transImports
-/
#guard_msgs in
#eval Lake.initModuleFacetConfigs.toList.toArray.map (·.1) |>.qsort (·.toString < ·.toString) |>.forM (IO.println)
```

:::paragraph
模块可用的分面有：

: `lean`

  模块的 Lean 源文件。

: `leanArts`（默认）

  模块的 Lean 工件（`*.olean`、`*.ilean`、`*.c` 文件）。

: `deps`

  模块的依赖（例如导入或共享库）。

: `depHash`

  模块的构建依赖（例如，导入、源码、插件）的哈希。

: `depTrace`

  包含模块的构建依赖（例如，导入、源码、插件）的 Lake 构建追踪数据结构（即复合哈希与修改时间）。

: `olean`

  模块的 {tech (key := ".olean file")}[`.olean` 文件]。{TODO}[一旦模块系统完全落地，添加 `olean.private` 和 `olean.server` 的文档。]

: `ilean`

  模块的 `.ilean` 文件，即 Lean 语言服务器使用的元数据。

: `header`

  模块源文件中解析出的模块头部。

: `input`

  模块处理过的 Lean 源文件。结合了对文件的追踪与头部的解析。

: `imports`

  Lean 模块的直接导入，但不包含传递导入的全集。{TODO}[一旦模块系统完全落地，在此处添加 `module.importAllArts` 和 `module.importArts` 的文档。]

: `precompileImports`

  Lean 模块的传递导入，编译为目标代码。

: `transImports`

  作为 {tech (key := ".olean files")}[`.olean` 文件] 的 Lean 模块传递导入。

: `allImports`

  Lean 模块的直接导入和传递导入。

: `setup`

  模块的所有依赖：使用 `--load-dynlib` 加载的传递本地导入和共享库。
  返回要加载的共享库列表及其搜索路径。

: `ir`

  为使用 {ref "module-structure"}[模块系统] 的模块生成的 `.ir` 文件。


: `ir.sig`

  为使用 {ref "module-structure"}[模块系统] 的模块生成的 `.ir.sig` 文件。

: `c`

  由 Lean 编译器生成的 C 文件。

: `bc`

  由 Lean 编译器生成的 LLVM 位码文件。

: `c.o`

  由 C 文件生成的编译目标文件。在 Windows 上它等同于 `.c.o.noexport`，而在其他平台上它等同于 `.c.o.export`。

: `c.o.export`

  由 C 文件生成的编译目标文件，其中导出了 Lean 符号。

: `c.o.noexport`

  由 C 文件生成的编译目标文件，其中未导出 Lean 符号。

: `bc.o`

  由 LLVM 位码文件生成的编译目标文件。

: `o`

  为配置的后端生成的编译目标文件。

: `dynlib`

  共享库（例如，用于 Lean 选项 `--load-dynlib`）{TODO}[记录 Lean 命令行选项的文档，并从此处提供交叉引用]。

: `ltar`

  包含模块构建工件的压缩包（通过 `leantar` 生成）。{TODO}[请同时在手册中记录 `leantar` 的文档。]

: `linkInfoExport`

  要链接一个模块及其依赖所需的链接器参数、静态对象和动态库的结构化表示。这些对象会导出 Lean 符号。

: `linkInfoNoExport`

  要链接一个模块及其依赖所需的链接器参数、静态对象和动态库的结构化表示。这些对象不导出 Lean 符号。

:::


## 脚本
%%%
tag := "lake-scripts"
%%%

Lake {tech (key := "package configuration")}[包配置] 文件可包含 {deftech (key := "Lake scripts")}_Lake 脚本_，这些脚本是可从命令行执行的内嵌程序。
脚本旨在用于特定于项目、且 Lake 的其他特性尚未能很好地处理的任务。
普通的执行程序在 {name}`IO` {tech (key := "monad")}[单子] 中运行，而脚本在 {name Lake.ScriptM}`ScriptM` 中运行，后者在 {name}`IO` 的基础上扩展了有关工作区的信息。
因为它们是 Lean 定义，Lake 脚本只能在 Lean 配置格式中定义。

:::::TODO

一旦能够导入足够多的 Lake 以进行推导，恢复以下内容：

````
```lean -show
section
open Lake DSL
```

:::example "列出依赖" (file := "Listing Dependencies")

此 Lake 脚本按字母顺序列出根包的所有传递依赖及其 Git URL。
类似的脚本可以用于检查已声明的许可证、发现哪些依赖已配置测试驱动程序，或者随时间计算传递依赖集的各项指标。

```lean
script "list-deps" := do
  let mut results := #[]
  for p in (← getWorkspace).packages do
    if p.name ≠ (← getWorkspace).root.name then
      results := results.push (p.name.toString, p.remoteUrl)
  results := results.qsort (·.1 < ·.1)
  IO.println "Dependencies:"
  for (name, url) in results do
    IO.println s!"{name}:\t{url}"
  return 0
```
:::

```lean -show
end
```
````

:::::

## 测试和代码检查驱动程序
%%%
tag := "test-lint-drivers"
%%%

{deftech (key := "test driver")}_测试驱动程序_ 负责运行一个包的测试。
它可以是可执行目标、{tech (key := "Lake script")}[Lake 脚本] 或库。
Lake 本身并不是测试框架：{lake}`test` 命令只是定位已配置的目标，构建它，并且（针对可执行文件和脚本）运行它。
库的驱动程序纯粹通过推导来执行，因此它们不会作为单独的步骤运行。
断言、测试发现以及报告都由目标本身决定，这既可以是第三方测试库，也可以是手写的检查。

对于可执行文件和脚本，Lake 将非零退出代码视为测试失败。
对于库，任何推导错误均算作测试失败，包括 {keyword}`#guard` 风格命令的失败。

{deftech (key := "lint driver")}_代码检查驱动程序_ 也是类似的，只是它由 {lake}`lint` 运行，负责检查包在风格及其他方面是否存在不是_错误_但预示存在潜在问题的状况。
代码检查驱动程序只能是可执行文件或脚本，而不能是库。

### 配置测试驱动程序
%%%
tag := "lake-test-driver-config"
%%%

在 `lakefile.toml` 中，将 {tomlField Lake.PackageConfig}`testDriver` 设置为相同配置中定义的可执行文件目标、库目标或脚本的名称：

:::::example "测试驱动（`lakefile.toml`）" (file := "Test Driver (lakefile.toml)")

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
testDriver = "my-package-tests"

[[lean_exe]]
name = "my-package-tests"
root = "Tests"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

在 `lakefile.lean` 中，可以在 {keyword}`package` 声明中设置 {name Lake.Package.testDriver}`testDriver` 字段（如上所述），也可以使用 {attr}`test_driver` 属性对脚本、可执行文件或库声明进行标记。
属性标记的形式往往更方便，因为它将标记放在了目标旁边。

:::::example "测试驱动（`lakefile.lean`）" (file := "Test Driver (lakefile.lean)")

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  testDriver := "my-package-tests"

lean_exe «my-package-tests» where
  root := `Tests
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

每个包中只有一个声明可以被标记为 {attr}`test_driver`。
如果在同一 Lake 配置文件中同时使用 {attr}`test_driver` 属性和非空的 {name Lake.Package.testDriver}`testDriver` 字段，则会引发错误。

测试驱动程序也可以是传递地 {tech (key:="require")}[请求] 的包依赖项中的目标。
要使用其他包中的目标，请使用 `<pkg>/<name>` 作为 `testDriver` 的值，其中 `<pkg>` 是该目标所在的包的名称。

### 运行测试
%%%
tag := "lake-test-running"
%%%

{lake}`test` 命令仅运行 {tech (key := "root package")}[根包] 已配置的驱动程序。
不会运行依赖项的测试驱动程序。

:::paragraph
如果测试驱动程序是可执行文件或脚本，Lake 会先传递 {tomlField Lake.PackageConfig}`testDriverArgs` 中的参数，然后传递命令行上 `--` 之后的所有内容。
例如，

```
lake test -- --filter Foo --verbose
```

将在任何已配置好的 {tomlField Lake.PackageConfig}`testDriverArgs` 后，把 `--filter Foo --verbose` 传递给驱动程序。
Lake 在运行可执行文件驱动程序前会先对其进行构建。
:::

如果测试驱动程序是库，则不接受参数。
如果 {tomlField Lake.PackageConfig}`testDriverArgs` 不为空，或在 `--` 之后有任何参数，Lake 将报告错误。
要运行测试，只需使用 {tech (key:="Lean elaborator")}[Lean 推导器] 对该库进行推导即可。

如果为根包配置了测试驱动程序，{lake}`check-test` 将以退出代码 0（即成功）终止。
它不检查所命名的目标是否实际存在。

### 代码检查驱动程序
%%%
tag := "lake-lint-drivers"
%%%

代码检查驱动程序的配置和运行方式类似于 {ref "lake-test-driver-config"}[测试驱动程序]。
Lake 配置文件指定一个目标作为代码检查驱动程序，然后由 {lake}`lint` 运行它。
此目标必须是可执行文件或脚本；与测试驱动程序不同，代码检查驱动程序不能是库。

在 TOML 格式的 Lake 配置文件中，包级别的 {tomlField Lake.PackageConfig}`lintDriver` 字段指定了代码检查驱动程序目标的名称。

:::::example "代码检查驱动（`lakefile.toml`）" (file := "Lint Driver (lakefile.toml)")
这个最小化的 `lakefile.toml` 配置了一个代码检查驱动程序：

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
lintDriver = "my-package-lint"

[[lean_exe]]
name = "my-package-lint"
root = "Lint"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::


在 `lakefile.lean` 中，可以在 {keyword}`package` 声明中设置 {name Lake.Package.lintDriver}`lintDriver` 字段，也可以使用 {attr}`lint_driver` 属性标记脚本或可执行文件声明。
属性的形式往往更方便，因为它将标记放在了目标旁边。

:::::example "代码检查驱动（`lakefile.lean`）" (file := "Lint Driver (lakefile.lean)")

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  lintDriver := "my-package-lint"

lean_exe «my-package-lint» where
  root := `Lint
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::

每个包中只有一个声明可以被标记为 {attr}`lint_driver`。
如果在同一 Lake 配置文件中同时使用 {attr}`lint_driver` 属性和非空的 {name Lake.Package.lintDriver}`lintDriver` 字段，则会引发错误。

:::lakeSession -show
```lean +lakefile
import Lake
open Lake DSL
package p

@[lint_driver]
lean_exe Foo where

@[lint_driver]
lean_exe Bar where
```
```lakeCmd "lake build" +error
error: p: only one script or executable can be tagged @[lint_driver]
```
:::

依赖包中的代码检查驱动程序可以使用与测试驱动程序相同的 `<pkg>/<name>` 语法进行引用。

{lake}`lint` 运行已配置的驱动程序，首先传递 {tomlField Lake.PackageConfig}`lintDriverArgs`，然后传递命令行上 `--` 之后的任何内容：

```
lake lint -- --warnings-as-errors
```

Lake 还有单独的 {deftech (key := "builtin linter")}_内置检查器_，它直接在 Lean 模块上运行，独立于任何已配置的驱动程序。
内置代码检查可以通过 `--builtin-lint` 及相关标志（见 {lake}`lint`）启用，或通过在包配置中将 {tomlField Lake.PackageConfig}`builtinLint` 设置为 `true` 来启用。
当内置代码检查启用时，`--` 之前的位置参数 `MODULE` 用于选择要检查的模块，而且它们*不会*被传递给已配置的驱动程序。
因此 `lake lint Mathlib` 会触发对 `Mathlib` 的内置代码检查，而 `lake lint -- Mathlib` 则会将 `Mathlib` 传递给驱动程序。
这两种机制相互独立且可同时运行：当它们同时适用时，Lake 将先运行内置检查器，然后再运行驱动程序。

如果为根包配置了代码检查驱动程序，或者其配置中的 {tomlField Lake.PackageConfig}`builtinLint` 被设置为 `true`，{lake}`check-lint` 将以退出代码 0（即成功）退出。


## GitHub 发布版本构建
%%%
tag := "lake-github"
%%%

Lake 支持将构建工件（即归档后的构建目录）上传到包的 GitHub 发布版本中，或从其中下载。
这使得最终用户能够从云端获取预构建的工件，而无需自己从源码重建整个包。
可以使用 {envVar}`LAKE_NO_CACHE` 环境变量来禁用此功能。

### 下载

要下载工件，应配置包选项 `releaseRepo` 和 `buildArchive`，使其指向托管发布版本的 GitHub 仓库以及其中正确的工件名称（如果默认设置不充分）。
然后，设置 `preferReleaseBuild := true`，指示 Lake 将其作为额外的包依赖项获取并解包。

作为标准构建过程的一部分，Lake 仅当需要发布版本构建的包属于依赖时才会获取它（因为根包通常会被修改，所以它往往与此方案不兼容）。
但是，如果希望为根包获取发布版本构建（例如，在克隆发布版本的源代码之后、编辑之前），可以通过 `lake build :release` 手动执行。

Lake 在内部使用 `curl` 下载发布版本，并使用 `tar` 将其解包，因此最终用户必须安装这两种工具才能使用此功能。
如果 Lake 因任何原因未能获取发布版本，它将继续从源代码构建。
该机制在技术上不仅限于 GitHub：任何使用相同 URL 方案的 Git 托管平台同样适用。

### 上传

要将构建的包作为工件上传到 GitHub 发布版本，Lake 提供了 {lake}`upload` 命令作为便捷的简写。
此命令使用 `tar` 将包的构建目录打包为归档，并使用 `gh release upload` 将其附加到指定标签下预先存在的 GitHub 发布版本中。
因此，为了使用该命令，包的上传者（但不是下载者）需要安装 GitHub 命令行界面 `gh` 并将其包含在 `PATH` 中。

## 工件缓存
%%%
tag := "lake-cache"
%%%

*这是一项仍在开发中的实验性功能。*

Lake 支持 {deftech (key := "local cache")}_本地工件缓存_，该缓存会存储单个构建产物，并追踪生成它们的所有输入集。
每个 {tech (key := "toolchain")}[工具链] 都有其自己的缓存，因为工具链版本之间的中间构建产物是不兼容的。
不过，一个工具链的缓存在使用它的所有本地 {tech (key := "workspaces")}[工作区] 之间是共享的，因此常见的依赖不需要重新构建。
如果两个具有相同工具链的独立工作区依赖于相同的包，则它们可以共享彼此的构建产物。

因为这是一项实验性功能，所以本地缓存默认处于禁用状态。
只有当 {envVar}`LAKE_ARTIFACT_CACHE` 环境变量被设置为 `true`，或者当 {TODO}[ref] `enableArtifactCache` 字段在 {ref "lake-config"}[配置文件] 中被设置为 `true` 时才会被启用。


### 远程工件缓存
%%%
tag := "lake-cache-remote"
%%%

构建产物可以从远程缓存服务器检索，并放入本地缓存中。
这使得完全避免本地构建成为可能。
{lake}`cache get` 命令用于将工件下载到本地缓存中。

与 {ref "lake-github"}[GitHub 发布版本构建] 相比，远程工件缓存的粒度要细得多。
它追踪源代码文件级别、{tech (key := ".olean files")}[`.olean` 文件] 以及目标代码级别的构建产物，而不是整个包级别的。

### 映射

当传递 `-o` 选项时，{lake}`build` 会追踪用于生成每个构建产物的输入。
它们被存储为 JSON 行格式的 {deftech (key := "mappings file")}_映射文件_，文件中每一行都必须是一个有效的 JSON 对象。
一个映射文件追踪单次构建，包括工作区 {tech (key := "root package")}[根包] 的所有中间和最终构建产物，但不包含其依赖。
这包括那些已经处于最新状态且不需要重新生成的构建产物。
{lake}`cache put` 命令从本地缓存把映射文件中的构建产物上传到远程缓存。

### 配置

:::paragraph
使用以下环境变量配置远程工件缓存：
 * {envVar}`LAKE_CACHE_KEY`
 * {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`
 * {envVar}`LAKE_CACHE_REVISION_ENDPOINT`
:::

{include 0 Manual.BuildTools.Lake.CLI}

{include 0 Manual.BuildTools.Lake.Config}

# 脚本 API 参考
%%%
tag := "lake-api"
%%%

除了普通的 {lean}`IO` 效应，Lake 脚本还能访问 Lake 环境（它提供了有关当前工具链的信息，例如 Lean 编译器的位置）以及当前的工作区。
这一访问权限是在 {name Lake.ScriptM}`ScriptM` 中提供的。

{docstring Lake.ScriptM}

## 访问环境

提供对当前 Lake 环境信息（例如 Lean、Lake 以及其它工具的位置）访问权限的单子具备 {name Lake.MonadLakeEnv}`MonadLakeEnv` 实例。
Lake API 中的所有单子皆是如此，包括 {name Lake.ScriptM}`ScriptM`。

{docstring Lake.MonadLakeEnv}

{docstring Lake.getLakeEnv}

{docstring Lake.getNoCache}

{docstring Lake.getTryCache}

{docstring Lake.getPkgUrlMap}

{docstring Lake.getElanToolchain}

### 搜索路径辅助函数

{docstring Lake.getEnvLeanPath}

{docstring Lake.getEnvLeanSrcPath}

{docstring Lake.getEnvSharedLibPath}

### Elan 安装辅助函数

{docstring Lake.getElanInstall?}

{docstring Lake.getElanHome?}

{docstring Lake.getElan?}

### Lean 安装辅助函数

{docstring Lake.getLeanInstall}

{docstring Lake.getLeanSysroot}

{docstring Lake.getLeanSrcDir}

{docstring Lake.getLeanLibDir}

{docstring Lake.getLeanIncludeDir}

{docstring Lake.getLeanSystemLibDir}

{docstring Lake.getLean}

{docstring Lake.getLeanc}

{docstring Lake.getLeanSharedLib}

{docstring Lake.getLeanAr}

{docstring Lake.getLeanCc}

{docstring Lake.getLeanCc?}

### Lake 安装辅助函数

{docstring Lake.getLakeInstall}

{docstring Lake.getLakeHome}

{docstring Lake.getLakeSrcDir}

{docstring Lake.getLakeLibDir}

{docstring Lake.getLake}

## 访问工作区

提供对当前 Lake 工作区信息访问权限的单子具备 {name Lake.MonadWorkspace}`MonadWorkspace` 实例。
特别是，有针对 {name Lake.ScriptM}`ScriptM` 和 {name Lake.LakeM}`LakeM` 的实例。

```lean -show
section
open Lake
#synth MonadWorkspace ScriptM

end
```

{docstring Lake.MonadWorkspace}

{docstring Lake.getRootPackage}

{docstring Lake.findPackageByName?}

{docstring Lake.findPackageByKey?}

{docstring Lake.findModule?}

{docstring Lake.findLeanExe?}

{docstring Lake.findLeanLib?}

{docstring Lake.findExternLib?}

{docstring Lake.getLeanPath}

{docstring Lake.getLeanSrcPath}

{docstring Lake.getSharedLibPath}

{docstring Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath }

{docstring Lake.getAugmentedSharedLibPath}

{docstring Lake.getAugmentedEnv}
