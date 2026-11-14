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

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

#doc (Manual) "构建" =>
%%%
file := "Builds"
tag := "lake-builds"
%%%

:::paragraph
生成所需的 {tech (key := "artifact")}[工件]，比如 {tech (key := ".olean file")}[`.olean` 文件] 或可执行二进制文件，被称为 {deftech (key := "build")}_构建_。
构建由 {lake}`build` 命令或需要工件存在的其他命令（例如 {lake}`exe`）触发。
构建包括以下步骤：

: {deftech (key := "configure package")}[配置包]

  如果 {tech (key := "package configuration")}[包配置] 文件比缓存的配置文件 `lakefile.olean` 更新，那么包配置就会被重新精译。
  当缓存文件缺失或者提供了 {lakeOpt}`--reconfigure` 或 {lakeOpt}`-R` 标志时，也会发生这种情况。
  使用 {lakeOpt}`-K` 对选项的更改不会触发配置文件的重新精译；在这些情况下，必须使用 {lakeOpt}`-R`。

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
   Lake 目录中的库在精译 Lake 配置文件时不可或缺，这样配置文件就能访问 Lean 的全部功能。
:::

# 分面
%%%
file := "Facets"
tag := "lake-facets"
%%%

{deftech (key := "facet")}_分面_ 描述了一个目标从另一个目标的生产过程。
从概念上讲，任何目标都可以拥有分面。
然而，可执行文件、外部库和自定义目标只提供单一的隐式分面。
包、库和模块拥有多个分面，调用 {lake}`build` 选定相应目标时，可以通过名称请求它们。

当没有显式请求分面，但指定了初始目标时，{lake}`build` 将产生初始目标的 {deftech (key := "default facet")}_默认分面_。
每种类型的初始目标都有相应的默认分面（例如从可执行文件目标生成可执行二进制文件或构建一个包的 {tech (key := "default targets")}[默认目标]）；可以在 {tech (key := "package configuration")}[包配置] 中或通过 Lake 的 {ref "lake-cli"}[命令行界面] 显式请求其他分面。
可以使用 Lake 的内部接口来编写自定义分面。


```lakeHelp "build"
Build targets

USAGE:
  lake build [<targets>...] [-o <mappings>] [--package <name>]

A target is specified with a string of the form:

  [@[<package>]/][<target>|[+]<module>][:<facet>]

You can also use the source path of a module as a target. For example,

  lake build Foo/Bar.lean:o

will build the Lean module (within the workspace) whose source file is
`Foo/Bar.lean` and compile the generated C file into a native object file.

The `@` and `+` markers can be used to disambiguate packages and modules
from file paths or other kinds of targets (e.g., executables or libraries).

LIBRARY FACETS:         build the library's ...
  elabArts              elaboration artifacts (*.olean, *.ilean files)
  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  elabArts              elaboration artifacts (*.olean, *.ilean files)
  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)
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

With the Lake cache enabled, Lake can track the targets the build covers
(both those up-to-date and those newly built) and write the input-to-outputs
mappings of each to a file specified by the `-o` option. By default, with `-o`,
Lake will track the targets of the root package, use `--package` to select a
different one. These mappings can then be used to upload the build artifacts
to a remote cache with `lake cache put`. This will only include the artifacts
from the covered targets. Other targets in the package will not be tracked.
```


::::paragraph

包可用的分面有：

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: #[`package.barrel, `package.cache, `package.defaultModules, `package.deps, `package.extraDep, `package.optBarrel,
  `package.optCache, `package.optRelease, `package.release, `package.transDeps]
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

: `defaultModules`

  包的{tech (key := "default targets")}[默认目标]所包含的 Lean 模块：每个默认库的所有模块，以及每个默认可执行文件的根模块和它在工作区中传递导入的模块。
  其他默认目标（例如{ref "lake-config-custom-target"}[自定义目标]）不在其中。


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
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: [`lean_lib.elabArts, `lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.irArts, `lean_lib.static.export,
  `lean_lib.shared, `lean_lib.modules, `lean_lib.static, `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```

:::paragraph

库可用的分面有：

: `elabArts`

  库的精译工件（{tech (key := ".olean files")}`*.olean` 和 `*.ilean` 文件）。

: `irArts` (default)

  库的精译工件和代码生成工件（`*.ir`、`*.ir.sig` 和 `*.c` 文件）。

: `leanArts`

  Lean 编译器为该库生成的工件（`irArts` 的别名）。

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
-- Always keep this in sync with the description below. It ensures that the list is complete.
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
module.elabArts
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
module.irArts
module.lean
module.leanArts
module.linkInfoExport
module.linkInfoNoExport
module.ltar
module.metaExportInfo
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

: `elabArts`

  模块的精译工件（`*.olean` 和 `*.ilean` 文件）。

: `irArts` (default)

  模块的精译工件和代码生成工件（`*.ir`、`*.ir.sig` 和 `*.c` 文件）。

: `leanArts`

  Lean 编译器为该模块生成的工件（`irArts` 的别名）。

: `deps`

  模块的依赖（例如导入或共享库）。

: `depHash`

  模块的构建依赖（例如，导入、源码、插件）的哈希。

: `depTrace`

  包含模块的构建依赖（例如，导入、源码、插件）的 Lake 构建追踪数据结构（即复合哈希与修改时间）。

: `olean`

  模块的 {tech (key := ".olean file")}[`.olean` 文件]。{TODO}[模块系统完全落地后，此处需添加 `olean.private` 和 `olean.server` 的文档。]

: `ilean`

  模块的 `.ilean` 文件，即 Lean 语言服务器使用的元数据。

: `header`

  模块源文件中解析出的模块头部。

: `input`

  模块处理过的 Lean 源文件。结合了对文件的追踪与头部的解析。

: `imports`

  Lean 模块的直接导入，但不包含传递导入的全集。{TODO}[模块系统完全落地后，此处需添加 `module.importAllArts` 和 `module.importArts` 的文档。]

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

  共享库（例如，用于 Lean 选项 `--load-dynlib`）{TODO}[此处需记录 Lean 命令行选项的文档，并提供交叉引用]。

: `ltar`

  包含模块构建工件的压缩包（通过 `leantar` 生成）。{TODO}[此处还需在手册中补充 `leantar` 的文档。]

: `linkInfoExport`

  要链接一个模块及其依赖所需的链接器参数、静态对象和动态库的结构化表示。这些对象会导出 Lean 符号。

: `linkInfoNoExport`

  要链接一个模块及其依赖所需的链接器参数、静态对象和动态库的结构化表示。这些对象不导出 Lean 符号。

:::
