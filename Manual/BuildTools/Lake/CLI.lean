/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "命令行界面" =>
%%%
tag := "lake-cli"
%%%


```lakeHelp
USAGE:
  lake [OPTIONS] <COMMAND>

COMMANDS:
  new <name> <temp>     create a Lean package in a new directory
  init <name> <temp>    create a Lean package in the current directory
  build <targets>...    build targets
  query <targets>...    build targets and output results
  exe <exe> <args>...   build an exe and run it in Lake's environment
  check-build           check if any default build targets are configured
  test                  test the package using the configured test driver
  check-test            check if there is a properly configured test driver
  lint                  lint the package
  check-lint            check if there is a properly configured lint driver
  clean                 remove build outputs
  shake                 minimize imports in source files
  env <cmd> <args>...   execute a command in Lake's environment
  lean <file>           elaborate a Lean file in Lake's context
  update                update dependencies and save them to the manifest
  pack                  pack build artifacts into an archive for distribution
  unpack                unpack build artifacts from an distributed archive
  upload <tag>          upload build artifacts to a GitHub release
  cache                 manage the Lake cache
  script                manage and run workspace scripts
  scripts               shorthand for `lake script list`
  run <script>          shorthand for `lake script run`
  translate-config      change language of the package configuration
  serve                 start the Lean language server

BASIC OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration
  -K key[=value]        set the configuration file option named key
  --old                 only rebuild modified modules (ignore transitive deps)
  --rehash, -H          hash all files for traces (do not trust `.hash` files)
  --update              update dependencies on load (e.g., before a build)
  --packages=file       JSON file of package entries that override the manifest
  --reconfigure, -R     elaborate configuration files instead of using OLeans
  --keep-toolchain      do not update toolchain on workspace update
  --allow-empty         accept bare builds with no default targets configured
  --no-build            exit immediately if a build target is not up-to-date
  --no-cache            build packages locally; do not download build caches
  --try-cache           attempt to download build caches for supported packages
  --json, -J            output JSON-formatted results (in `lake query`)
  --text                output results as plain text (in `lake query`)

OUTPUT OPTIONS:
  --quiet, -q           hide informational logs and the progress indicator
  --verbose, -v         show trace logs (command invocations) and built targets
  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output
  --log-level=lv        minimum log level to output on success
                        (levels: trace, info, warning, error)
  --fail-level=lv       minimum log level to fail a build (default: error)
  --iofail              fail build if any I/O or other info is logged
                        (same as --fail-level=info)
  --wfail               fail build if warnings are logged
                        (same as --fail-level=warning)


See `lake help <command>` for more information on a specific command.
```

Lake 的命令行界面结构分为一系列子命令。
所有的子命令都共享由特定的环境变量和全局命令行选项进行配置的能力。
每个子命令都应被理解为一个独立的实用工具，拥有自己必需的实参语法和文档。

:::paragraph
一些 Lake 命令委托给了未包含在 Lean 发行版中的其他命令行实用工具。
这些实用工具必须在 `PATH` 上可用才能使用相应的功能：

 * 访问 Git 依赖项需要 `git`。
 * 创建或提取云构建归档文件需要 `tar`，获取它们需要 `curl`。
 * 将构建工件上传到 GitHub 发布版需要 `gh`。

Lean 发行版包含了 C 编译器工具链。
:::

# 环境变量
%%%
tag := "lake-environment"
%%%

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```


当调用 Lean 编译器或其他工具时，Lake 会设置或修改许多环境变量。{index}[环境变量]
这些值是与系统相关的。
在没有任何实参的情况下调用 {lake}`env` 会显示环境变量及其值。
否则，所提供的命令将在 Lake 的环境中被调用。

::::paragraph
设置以下变量，覆盖之前的值：
:::table (align := left) -header
*
  * {envVar +def}`LAKE`
  * 检测到的 Lake 可执行文件
*
  * {envVar}`LAKE_HOME`
  * 检测到的 {tech (key := "Lake home")}[Lake 主目录]
*
  * {envVar}`LEAN_SYSROOT`
  * 检测到的 Lean {tech (key := "toolchain")}[工具链]目录
*
 * {envVar}`LEAN_AR`
 * 检测到的 Lean `ar` 二进制文件
*
  * {envVar}`LEAN_CC`
  * 检测到的 C 编译器（如果不使用绑定的编译器）
:::
::::

::::paragraph
以下变量被增加了附加信息：
:::table (align := left) -header
*
  * {envVar}`LEAN_PATH`
  * 添加了 Lake 的和 {tech (key := "workspace")}[工作区]的 Lean {tech (key := "library directories")}[库目录]。
*
  * {envVar}`LEAN_SRC_PATH`
  * 添加了 Lake 的和 {tech (key := "workspace")}[工作区]的 {tech (key := "source directories")}[源目录]。
*
  * {envVar}`PATH`
  * 添加了 Lean 的、Lake 的和 {tech (key := "workspace")}[工作区]的 {tech (key := "binary directories")}[二进制目录]。
    在 Windows 上，也添加了 Lean 的和 {tech (key := "workspace")}[工作区]的 {tech (key := "library directories")}[库目录]。
*
  * {envVar}`DYLD_LIBRARY_PATH`
  * 在 macOS 上，添加了 Lean 的和 {tech (key := "workspace")}[工作区]的 {tech (key := "library directories")}[库目录]。
*
  * {envVar}`LD_LIBRARY_PATH`
  * 在除 Windows 和 macOS 之外的平台上，添加了 Lean 的和 {tech (key := "workspace")}[工作区]的 {tech (key := "library directories")}[库目录]。
:::
::::

::::paragraph
可以使用以下环境变量配置 Lake 本身：
:::table (align := left) -header
*
  * {envVar +def}`ELAN_HOME`
  * {ref "elan"}[Elan] 安装的位置，用于{ref "automatic-toolchain-updates"}[自动更新工具链]。

*
  * {envVar +def}`ELAN`
  * `elan` 二进制文件的位置，用于{ref "automatic-toolchain-updates"}[自动更新工具链]。
    如果未设置，`elan` 必须在 {envVar}`PATH` 上存在。

*
  * {envVar +def}`LAKE_HOME`
  * Lake 安装的位置。
    只有当 Lake 无法从当前运行的 `lake` 可执行文件的位置确定其安装路径时，才会查询此环境变量。
*
  * {envVar +def}`LEAN_SYSROOT`
  * Lean 安装的位置，用于查找 Lean 编译器、标准库和其他绑定工具。
    Lake 首先检查其二进制文件是否与 Lean 安装位于同一位置，如果是则使用该安装。
    如果不是，或者 {envVar +def}`LAKE_OVERRIDE_LEAN` 为 true，那么 Lake 会查询 {envVar}`LEAN_SYSROOT`。
    如果未设置此变量，Lake 会查询 {envVar +def}`LEAN` 环境变量以查找 Lean 编译器，并尝试查找相对于编译器的 Lean 安装。
    如果设置了 {envVar}`LEAN` 但为空，Lake 将认为 Lean 已被禁用。
    如果未设置 {envVar}`LEAN_SYSROOT` 和 {envVar}`LEAN`，则使用 {envVar}`PATH` 上的第一个 `lean` 来查找安装。
*
  * {envVar +def}`LEAN_CC` 和 {envVar +def}`LEAN_AR`
  * 如果设置了 {envVar}`LEAN_CC` 和/或 {envVar}`LEAN_AR`，其值将在构建库时用作 C 编译器或 `ar` 命令。
    如果没有设置，Lake 将回退到 Lean 安装中的绑定工具。
    如果找不到绑定工具，将使用 {envVar +def}`CC` 或 {envVar +def}`AR` 的值，接着是 {envVar}`PATH` 上的 `cc` 或 `ar`。
*
  * {envVar +def}`LAKE_NO_CACHE`
  * 如果为 true，Lake 不使用来自 [Reservoir](https://reservoir.lean-lang.org/) 或 {ref "lake-github"}[GitHub] 的缓存构建。
    可以使用 {lakeOpt}`--try-cache` 命令行选项覆盖此环境变量。

*
  * {envVar +def}`LAKE_ARTIFACT_CACHE`
  * 如果为 true，Lake 将使用工件缓存。
    这是一个实验性功能。

*
  * {envVar +def}`LAKE_CACHE_KEY`
  * 为{ref "lake-cache-remote"}[远程工件缓存]定义认证密钥。

*
  * {envVar +def}`LAKE_CACHE_ARTIFACT_ENDPOINT`
  * 用于工件上传的{ref "lake-cache-remote"}[远程工件缓存]的基准 URL。
    如果设置了此变量，则还必须设置 {envVar}`LAKE_CACHE_REVISION_ENDPOINT`。
    如果两者都未设置，Lake 将使用 Reservoir。

*
  * {envVar +def}`LAKE_CACHE_REVISION_ENDPOINT`
  * 用于为每个工件上传 {tech (key := "mappings file")}[输入/输出映射]的{ref "lake-cache-remote"}[远程工件缓存]的基准 URL。
    如果设置了此变量，则还必须设置 {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`。
    如果两者都未设置，Lake 将使用 Reservoir。

:::
::::

Lake 将值为 `y`、`yes`、`t`、`true`、`on` 或 `1`（不区分大小写）的环境变量视为 true。
它将值为 `n`、`no`、`f`、`false`、`off` 或 `0`（不区分大小写）的变量视为 false。
如果变量未设置，或者其值既不为 true 也不为 false，则使用默认值。

```lean -show
-- 测试上述断言
/--
info: def Lake.envToBool? : String → Option Bool :=
fun o =>
  if ["y", "yes", "t", "true", "on", "1"].contains o.toLower = true then some true
  else if ["n", "no", "f", "false", "off", "0"].contains o.toLower = true then some false else none
-/
#guard_msgs in
#print Lake.envToBool?
```

# 选项

Lake 的命令行界面提供了许多全局选项以及执行重要任务的子命令。
单字符标志不能组合；`-HR` 不等于 `-H -R`。

: {lakeOptDef flag}`--version`

  Lake 输出其版本并退出，不执行任何其他操作。

: {lakeOptDef flag}`--help` 或 {lakeOptDef flag}`-h`

  Lake 输出其版本以及使用信息并退出，不执行任何其他操作。
  子命令可以与 {lakeOpt}`--help` 一起使用，在这种情况下将输出该子命令的使用信息。

: {lakeOptDef option}`--dir DIR` 或 {lakeOptDef option}`-d=DIR`

  将提供的目录而不是当前工作目录用作包的位置。
  这并不总是等同于先更改到该目录，因为会使用当前目录的{tech (key := "toolchain file")}[工具链文件]指示的 `lake` 版本，而不是 `DIR` 的版本。

: {lakeOptDef option}`--file FILE` 或 {lakeOptDef option}`-f=FILE`

  使用指定的{tech (key := "package configuration")}[包配置]文件而不是默认文件。

: {lakeOptDef flag}`--old`

  仅重新构建修改的模块，忽略传递依赖项。
  导入修改模块的模块将不会被重新构建。
  为了实现这一点，将使用文件修改时间而不是哈希来确定模块是否已更改。

: {lakeOptDef flag}`--rehash` 或 {lakeOptDef flag}`-H`

  忽略缓存的文件哈希，重新计算它们。
  Lake 使用依赖项的哈希来确定是否重新构建工件。
  每当构建模块时，这些哈希都会缓存在磁盘上。
  为了在构建过程中节省时间，除非指定了 {lakeOpt}`--rehash`，否则会使用这些缓存的哈希，而不是重新计算每个哈希。

: {lakeOptDef flag}`--allow-empty`

  接受在未配置{tech (key := "default targets")}[默认目标]时产生无输出的构建。

: {lakeOptDef flag}`--update`

  在加载{tech (key := "package configuration")}[包配置]之后、但在执行其他任务（例如构建）之前更新依赖项。
  这等同于在选定命令之前运行 `lake update`，但由于不需要加载配置两次，它可能会更快。

: {lakeOptDef option}`--packages=FILE`

  使用指定的{tech (key := "package overrides")}[包覆盖]文件。
  可以多次指定此选项以添加更多覆盖（后指定的覆盖优先）。
  包覆盖的完整集合还将包括来自 `.lake/package-overrides.json` 的覆盖（如果有）。
  但是，通过此选项提供的覆盖具有更高的优先级。

:  {lakeOptDef flag}`--reconfigure` 或 {lakeOptDef flag}`-R`

  通常，{tech (key := "package configuration")}[包配置]文件在首次配置包时由{tech (key := "elaborator") -normalize}[精译器处理]，并将结果缓存到供将来调用使用的 {tech (key := ".olean file")}[`.olean` 文件]中，直到包配置发生更改。
  提供此标志将导致配置文件被重新精译。

: {lakeOptDef flag}`--keep-toolchain`

  默认情况下，Lake 会尝试更新本地{tech (key := "workspace")}[工作区]的{tech (key := "toolchain file")}[工具链文件]。
  提供此标志会禁用{ref "automatic-toolchain-updates"}[自动更新工具链]。

: {lakeOptDef flag}`--no-build`

  如果构建目标不是最新的，Lake 会立即退出，并返回非零的退出代码。

: {lakeOptDef flag}`--no-cache`

  不使用可用的云构建缓存，而是在本地构建所有包。
  构建缓存不被下载。

: {lakeOptDef flag}`--try-cache`

  尝试下载支持的包的构建缓存

# 控制输出

这些选项允许控制在构建时生成的{tech (key := "log")}[日志]。
除了显示或隐藏消息之外，还可以使构建在发出警告甚至信息时失败；这可用于强制实施不允许在构建期间输出的风格指南。

: {lakeOptDef flag}`--quiet`, {lakeOptDef flag}`-q`

  隐藏信息日志和进度指示器。

: {lakeOptDef flag}`--verbose`, {lakeOptDef flag}`-v`

  显示跟踪日志（通常是命令调用）和构建的{tech (key := "targets")}[目标]。

:  {lakeOptDef flag}`--ansi`, {lakeOptDef flag}`--no-ansi`

  启用或禁用使用为 Lake 的输出添加颜色和动画的 [ANSI 转义码](https://en.wikipedia.org/wiki/ANSI_escape_code)。

:  {lakeOptDef option}`--log-level=LV`

  设置在构建成功时要显示的{tech (key := "logs")}[日志]的最低级别。
  `LV` 可以是 `trace`、`info`、`warning` 或 `error`，不区分大小写。
  当构建失败时，会显示所有级别。
  默认日志级别为 `info`。

:  {lakeOptDef option}`--fail-level=LV`

  设置导致构建被视为失败的{tech (key := "log")}[日志]消息级别阈值。
  如果在日志中发出的消息级别大于或等于该阈值，构建将失败。
  `LV` 可以是 `trace`、`info`、`warning` 或 `error`，不区分大小写；默认为 `error`。


: {lakeOptDef flag}`--iofail`

  如果记录了任何 I/O 或其他信息，则导致构建失败。
  这等同于 {lakeOpt}`--fail-level=info`。

: {lakeOptDef flag}`--wfail`

  如果记录了任何警告，则导致构建失败。
  这等同于 {lakeOpt}`--fail-level=warning`。

# 自动更新工具链
%%%
tag := "automatic-toolchain-updates"
%%%

{lake}`update` 命令检查依赖项的更改，获取其源代码并相应地更新{tech (key := "manifest")}[清单]。
默认情况下，当依赖项的新版本指定了更新的工具链时，{lake}`update` 还会尝试更新{tech (key := "root package")}[根包]的{tech (key := "toolchain file")}[工具链文件]。
可以使用 {lakeOpt}`--keep-toolchain` 标志禁用此行为。

:::paragraph
如果多个依赖项指定了较新的工具链，Lake 将选择最新的兼容工具链（如果存在）。
为了确定最新的兼容工具链，Lake 将包的 `lean-toolchain` 文件中列出的工具链解析为四类：

 * 发布版，按版本号进行比较（例如，`v4.4.0` < `v4.8.0` 和 `v4.6.0-rc1` < `v4.6.0`）
 * 每日构建版，按日期进行比较（例如，`nightly-2024-01-10` < `nightly-2024-10-01`）
 * 针对 Lean 编译器的拉取请求构建，不可比较
 * 其他版本，同样不可比较

来自多个类别的工具链版本是不可比较的。
如果没有唯一的最新的工具链，Lake 将打印警告并继续更新，而不更改工具链。
:::

如果 Lake 确实找到了新的工具链，那么它会相应地更新{tech (key := "workspace")}[工作区]的 `lean-toolchain` 文件，并使用新工具链的 Lake 重新启动 {lake}`update`。
如果检测到 {ref "elan"}[Elan]，它将通过 `elan run` 启动新的 Lake 进程，并使用最初运行 Lake 时的相同参数。
如果缺少 Elan，它将提示用户手动重新启动 Lake，并退出特殊的错误代码（即 `4`）。
可以使用 {envVar}`ELAN` 环境变量配置 Lake 使用的 Elan 可执行文件。


# 创建包

```lakeHelp "new"
Create a Lean package in a new directory

USAGE:
  lake [+<lean-version>] new <name> [<template>][.<language>]

If you are using Lake through Elan (which is standard), you can create a
package with a specific Lean version via the `+` option.

The initial configuration and starter files are based on the template:

  std                   library and executable; default
  exe                   executable only
  lib                   library only
  math-lax              library only with a Mathlib dependency
  math                  library with Mathlib standards for linting and workflows

Templates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML
version of the configuration file, respectively. The default is TOML.
```

:::lake new "name [template][\".\"language]"

运行 {lake}`new` 将在新目录中创建一个初始的 Lean 包。
此命令等同于创建一个名为 {lakeMeta}`name` 的目录，然后运行 {lake}`init`。

:::

:::lake init "name [template][\".\"language]"

运行 {lake}`init` 将在当前目录中创建一个初始的 Lean 包。
包的内容基于模板，其{tech (key := "package")}[包]的名称、{tech (key := "targets")}[目标]及其{tech (key := "module roots")}[模块根]来自当前目录的名称。

{lakeMeta}`template` 可以是：

: `std`（默认）

  创建一个包含库和可执行文件的包。

: `exe`

  创建一个仅包含可执行文件的包。

: `lib`

  创建一个仅包含库的包。

: `math`

  创建一个包含依赖于 [Mathlib](https://github.com/leanprover-community/mathlib4) 库的包。

{lakeMeta}`language` 选择用于{tech (key := "package configuration")}[包配置]文件的文件格式，可以是 `lean`（默认）或 `toml`。
:::

:::TODO
`lake init` 或 `lake new` 的示例
:::

# 构建与运行

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

::::lake build "[targets...] [\"-o\" mappings]"

构建指定的目标的指定分面。

每个 {lakeMeta}`targets` 都是通过以下形式的字符串指定的：

{lakeArgs}`[["@"]package["/"]][target|["+"]module][":"facet]`

可选的 {keyword}`@` 和 {keyword}`+` 标记可用于将包和模块与文件路径以及通过按名称作为 {lakeMeta}`target` 指定的可执行文件和库区分开来。
如果未提供，{lakeMeta}`package` 默认为{tech (key := "workspace")}[工作区]的{tech (key := "root package")}[根包]。
如果工作区中的多个包中存在相同的目标名称，则选择在包依赖关系图的拓扑排序中找到的目标名称的第一次出现。
模块目标也可以由它们的文件名指定，在冒号之后带有可选的分面。

可用的{tech (key := "facets")}[分面]取决于要构建的是包、库、可执行文件还是模块。
它们在{ref "lake-facets"}[关于分面的部分]中列出。

当使用{ref "lake-cache"}[本地工件缓存]时，{lakeOptDef option}`-o` 选项将保存一个跟踪构建每一步的输入和输出的{tech (key := "mappings file")}[映射文件]。
此文件可与 {lake}`cache get` 和 {lake}`cache put` 一起使用以与远程缓存进行交互。
映射文件采用 JSON Lines 格式，每行一个有效的 JSON 对象，通常文件扩展名为 `.jsonl`。
::::

::::example "目标和分面规范" (file := "Target and Facet Specifications")

:::table
*
  - `a`
  - 目标 `a` 的{tech (key := "default facet")}[默认分面]
*
  - `@a`
  - {tech (key := "package")}[包] `a` 的{tech (key := "default targets")}[默认目标]
*
  - `+A`
  -  模块 `A` 的 Lean 工件（因为模块的默认分面是 `leanArts`）
*
  - `@a/b`
  - 包 `a` 的目标 `b` 的默认分面
*
  - `@a/+A:c`
  - 从包 `a` 的模块 `A` 编译的 C 文件
*
  - `:foo`
  - {tech (key := "root package")}[根包]的分面 `foo`
*
  - `A/B/C.lean:o`
  - 文件 `A/B/C.lean` 中模块的编译目标代码
:::
::::

```lakeHelp "check-build"
Check if any default build targets are configured

USAGE:
  lake check-build

Exits with code 0 if the workspace's root package has any
default targets configured. Errors (with code 1) otherwise.

Does NOT verify that the configured default targets are valid.
It merely verifies that some are specified.

```

:::lake «check-build»
如果{tech (key := "workspace")}[工作区]的{tech (key := "root package")}[根包]配置了任何{tech (key := "default targets")}[默认目标]，则以状态码 0 退出。
否则报错（退出代码 1）。

{lake}`check-build` *不*验证配置的默认目标是否有效。
它仅仅验证至少指定了一个。
:::

```lakeHelp "exe"
Build an executable target and run it in Lake's environment

USAGE:
  lake exe <exe-target> [<args>...]

ALIAS: lake exec

Looks for the executable target in the workspace (see `lake help build` to
learn how to specify targets), builds it if it is out of date, and then runs
it with the given `args` in Lake's environment (see `lake help env` for how
the environment is set up).
```

```lakeHelp "query"
Build targets and output results

USAGE:
  lake query [<targets>...]

Builds a set of targets, reporting progress on standard error and outputting
the results on standard out. Target results are output in the same order they
are listed and end with a newline. If `--json` is set, results are formatted as
JSON. Otherwise, they are printed as raw strings. Targets which do not have
output configured will be printed as an empty string or `null`.

See `lake help build` for information on and examples of targets.
```

:::lake query "[targets...]"
构建一组目标，在标准错误上报告进度，并在标准输出上输出结果。
目标结果按照它们列出的顺序输出，并以换行符结束。
如果设置了 `--json`，结果将格式化为 JSON。
否则，它们将被打印为原始字符串。

未配置输出的目标将被打印为空字符串或 `null`。
对于可执行目标，输出是已构建可执行文件的路径。

使用与 {lake}`build` 相同的语法指定目标。
:::

:::lake exe "«exe-target» [args...]" (alias := exec)

在工作区中查找可执行目标 {lakeMeta}`exe-target`，如果过期则构建它，然后在 Lake 的环境中使用给定的 {lakeMeta}`args` 运行它。

有关目标规范的语法，请参见 {lake}`build`，有关如何设置环境的描述，请参见 {lake}`env`。

:::

```lakeHelp "clean"
Remove build outputs

USAGE:
  lake clean [<package>...]

If no package is specified, deletes the build directories of every package in
the workspace. Otherwise, just deletes those of the specified packages.
```

:::lake clean "[packages...]"

如果没有指定包，则删除工作区中每个包的{tech (key := "build directories")}[构建目录]。
否则，它只删除指定的 {lakeMeta}`packages` 的构建目录。

:::

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```

::::lake env "[cmd [args...]]"

当提供了 {lakeMeta}`cmd` 时，它将在带有实参 {lakeMeta}`args` 的{ref "lake-environment"}[Lake 环境]中执行。

如果没有提供 {lakeMeta}`cmd`，Lake 将打印其运行工具的环境。
这个环境是特定于系统的。
::::

```lakeHelp "lean"
Elaborate a Lean file in the context of the Lake workspace

USAGE:
  lake lean <file> [-- <args>...]

Build the imports of the given file and then runs `lean` on it using
the workspace's root package's additional Lean arguments and the given args
(in that order). The `lean` process is executed in Lake's environment like
`lake env lean` (see `lake help env` for how the environment is set up).
```

:::lake lean "file [\"--\" args...]"

构建给定的 {lakeMeta}`file` 的导入，然后在此文件上使用{tech (key := "workspace")}[工作区]的{tech (key := "root package")}[根包]的其他 Lean 实参和给定的 {lakeMeta}`args`（按此顺序）运行 `lean`。
`lean` 进程在{ref "lake-environment"}[Lake 的环境]中执行。
:::

# 模块导入

```lakeHelp shake
Minimize imports in Lean source files

USAGE:
  lake shake [OPTIONS] [<MODULE>...]

Checks the current project for unused imports by analyzing generated `.olean`
files to deduce required imports and ensuring that every import contributes
some constant or other elaboration dependency.

ARGUMENTS:
  <MODULE>              A module path like `Mathlib`. All files transitively
                        reachable from the provided module(s) will be checked.
                        If not specified, uses the package's default targets.

OPTIONS:
  --force               Skip the `lake build --no-build` sanity check
  --keep-implied        Preserve imports implied by other imports
  --keep-prefix         Prefer parent module imports over specific submodules
  --keep-public         Preserve all `public` imports for API stability
  --add-public          Add new imports as `public` if they were in the
                        original public closure
  --explain             Show which constants require each import
  --fix                 Apply suggested fixes directly to source files
  --gh-style            Output in GitHub problem matcher format

ANNOTATIONS:
  Source files can contain special comments to control shake behavior:

  * `module -- shake: keep-downstream`
    Preserves this module in all downstream modules

  * `module -- shake: keep-all`
    Preserves all existing imports in this module

  * `import X -- shake: keep`
    Preserves this specific import
```

::::lake shake "[options...] [module ...]"

通过分析生成的 {tech (key := ".olean files")}[`.olean` 文件]推断所需的导入，检查当前项目中未使用的导入，确保每个导入都有助于某些常量或其他精译依赖项。

如果指定了 {lakeMeta}`module`，则将检查它及其可传递访问的所有文件。否则，将检查包的{tech (key := "default targets")}[默认目标]。

:::paragraph
源文件可以包含特殊的注释来控制 {lake}`shake` 的行为：

: `module -- shake: keep-downstream`

  在所有下游模块中保留此模块。

: `module -- shake: keep-all`

  保留此模块中的所有现有导入。

: `import X -- shake: keep`

  保留此特定的导入。
:::

:::paragraph
{lakeMeta}`options` 可以是：

: `--force`

  跳过 `lake build --no-build` 健全性检查

: `--keep-implied`

  保留由其他导入隐含的导入

: `--keep-prefix`

  倾向于父模块导入而不是特定的子模块

: `--keep-public`

  保留所有的 `public` 导入以保持 API 稳定性

: `--add-public`

  如果新导入原本在公开闭包中，则将其添加为 `public`

: `--explain`

  显示哪些常量需要每次导入

: `--fix`

  直接将建议的修复应用到源文件

: `--gh-style`

  以 GitHub 问题匹配器格式输出
:::

::::

# 开发工具

Lake 包含了对指定标准开发工具和工作流的支持。
在命令行上，可以使用适当的 `lake` 子命令调用这些工具。

## 测试和代码检查

```lakeHelp test
Test the workspace's root package using its configured test driver

USAGE:
  lake test [-- <args>...]

A test driver can be configured by either setting the 'testDriver'
package configuration option or by tagging a script, executable, or library
`@[test_driver]`. A definition in a dependency can be used as a test driver
by using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script test driver will be run with the  package configuration's
`testDriverArgs` plus the CLI `args`. An executable test driver will be
built and then run like a script. A library test driver will just be built.

```

:::lake test " [\"--\" args...]"
使用其配置的{tech (key := "test driver")}[测试驱动程序]测试工作区的根包。

作为可执行文件的测试驱动程序将被构建，然后使用包配置的 `testDriverArgs` 加上 CLI 的 {lakeMeta}`args` 运行。
作为{tech (key := "Lake script")}[Lake 脚本]的测试驱动程序使用与可执行文件测试驱动程序相同的实参运行。
库测试驱动程序只会进行构建；预期实现测试的方式是，失败会通过精译期错误导致构建失败。
:::

```lakeHelp lint
Lint the workspace's root package

USAGE:
  lake lint [OPTIONS] [<MODULE>...] [-- <args>...]

By default, runs the package's configured lint driver. If `builtinLint` is
set to `true` in the package configuration, builtin lints also run.

Builtin linting (`--builtin-lint`, `--builtin-only`, `--linters`,
`--lint-only`, or `builtinLint = true` in the package configuration) drives a
build of the targeted modules with the requested linter options enabled.
The lint driver path on its own does not trigger a build.

Which environment linters run on a declaration is determined by the linter
options in effect when that declaration was built (e.g. via `set_option` in
the source, or via `--linters`/`--lint-only` below). Both override those
options for the lint build; `--lint-only` additionally restricts the reported
output to exactly the linters its spec enables.

Positional `MODULE` arguments narrow only the builtin lints; if omitted,
the workspace's default target roots are used. The lint driver is invoked
with `lintDriverArgs` from the package config plus any arguments after
`--`; the `MODULE` list is not passed to it.

OPTIONS:
  --builtin-lint        run builtin environment and text linters
  --builtin-only        run only builtin linters, skip the lint driver
  --linters <spec>      override linter options for the lint build; <spec> is a
                        comma-separated list of linter option names, each
                        optionally prefixed with `-` to disable it. A name
                        beginning with `.` is shorthand for the `linter.`
                        prefix, so `.foo` means `linter.foo`. E.g.
                        `--linters=.foo,-linter.bar`. Repeatable; later
                        entries override earlier ones for the same linter
  --lint-only <spec>    like `--linters`, but report ONLY the linters the spec
                        positively enables, suppressing every other linter
                        (including default-on linters that are not named).
                        Expands `linter.all` and linter sets. Uses the same
                        `<spec>` syntax as `--linters`; switching between
                        `--linters` and `--lint-only` replaces the prior spec
  --record-exceptions   record each linter warning as a
                        `set_option <linter> false in` exception by editing the
                        offending source files in place, silencing the warning
                        for that declaration. Implies `--builtin-lint`.
  --code-quality        records each linter warning as a code quality check result
                        and runs the registered code quality checks.
                        Setting this flag will skip lint driver.

A lint driver can be configured by either setting the `lintDriver` package
configuration option or by tagging a script or executable `@[lint_driver]`.
A definition in a dependency can be used as a lint driver by using the
`<pkg>/<name>` syntax for the 'lintDriver' configuration option.

A script lint driver will be run with the package configuration's
`lintDriverArgs` plus the CLI `args`. An executable lint driver will be
built and then run like a script.

```

```comment
我们有意地在 --code-quality 得到进一步开发之前将其省略
```

:::lake lint "[options...] [module...] [\"--\" args...]"

默认情况下，使用工作区配置的代码检查驱动程序对其根包执行代码检查。
如果在包配置中将 {tomlField Lake.PackageConfig}`builtinLint` 设置为 {name}`true`，也会运行内置代码检查。

位置实参 {lakeMeta}`module` 仅用于缩减内置代码检查 的范围；如果省略，则使用工作区的默认目标根。
调用 代码检查驱动程序时会使用包配置中的 `lintDriverArgs` 以及位于 `--` 之后的任何实参；{lakeMeta}`module` 列表不会传递给它。

内置代码检查会在启用了要求的 代码检查器选项的情况下构建目标模块。
它可以通过 {lakeOpt}`--builtin-lint`、{lakeOpt}`--builtin-only`、{lakeOpt}`--linters`、{lakeOpt}`--lint-only`，或者在包配置中将 `builtinLint` 设置为 {name}`true` 来触发。
相比之下，运行 代码检查驱动程序本身并不会自动触发除了 代码检查驱动程序自身以外的任何构建。

要在某个声明上运行的一组环境代码检查器 由构建该声明时生效的 代码检查器选项决定，不论是通过源文件中的 `set_option` 还是命令行设置的。
{lakeOpt}`--linters` 和 {lakeOpt}`--lint-only` 都在执行 代码检查构建时覆盖了这些选项。

{lakeMeta}`options` 可以是：

: {lakeOptDef flag}`--builtin-lint`

  运行内置的环境和文本代码检查器。

: {lakeOptDef flag}`--builtin-only`

  仅运行内置代码检查器，跳过 代码检查驱动程序。

: {lakeOptDef option}`--linters` {lakeMeta}`<spec>`

  覆盖 代码检查构建的 代码检查器选项。
  {lakeMeta}`<spec>` 是一个逗号分隔的 代码检查器选项名称列表，每个选项前可以选择带有 `-` 以禁用它。
  以 `.` 开头的名称是 `linter.` 前缀的简写，因此 `.foo` 表示 `linter.foo`，正如 `--linters=.foo,-linter.bar` 那样。
  此选项可以重复；对于给定的代码检查器，后面的条目会覆盖前面的。

: {lakeOptDef option}`--lint-only` {lakeMeta}`<spec>`

  类似于 {lakeOpt}`--linters`，但仅报告 {lakeMeta}`<spec>` 明确启用的代码检查器，抑制所有其他代码检查器，包括未命名但默认启用的代码检查器。
  `linter.all` 和代码检查器集合将被展开。
  在 {lakeOpt}`--linters` 和 {lakeOpt}`--lint-only` 之间切换会替换先前的规范。

: {lakeOptDef flag}`--record-exceptions`

  将每个代码检查器 警告作为 `set_option <linter> false in` 异常记录，通过在原位编辑产生问题的源文件，静默该声明的警告。
  这隐含了 {lakeOpt}`--builtin-lint`。

可以通过设置包配置选项 {tomlField Lake.PackageConfig}`lintDriver` 或使用 {attrs}`@[lint_driver]` 属性标记脚本或可执行文件来配置 代码检查驱动程序。
通过将 `<pkg>/<name>` 语法用于 {tomlField Lake.PackageConfig}`lintDriver` 配置选项，可以将依赖项中的定义用作 代码检查驱动程序。

脚本 代码检查驱动程序将结合包配置的 {tomlField Lake.PackageConfig}`lintDriverArgs` 和 CLI {lakeMeta}`args` 运行。
可执行文件 代码检查驱动程序将被构建，然后如同脚本一样运行。
:::

```lakeHelp "check-test"
Check if there is a properly configured test driver

USAGE:
  lake check-test

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured test driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-test»

检查是否有正确配置的测试驱动程序

如果工作区的根包具有正确配置的代码检查驱动程序，则以退出码 0 退出。
否则报错（代码 1）。

不验证配置的测试驱动程序是否真正在包或其依赖项中存在。
它仅仅验证是否指定了一个。

这对于区分失败的测试和配置不正确的包很有用。
:::

```lakeHelp "check-lint"
Check if there is a properly configured lint driver

USAGE:
  lake check-lint

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured lint driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-lint»
检查是否有正确配置的代码检查驱动程序

如果工作区的根包具有正确配置的代码检查驱动程序，则以退出码 0 退出。
否则报错（退出代码 1）。

不验证配置的代码检查驱动程序是否真正在包或其依赖项中存在。
它仅仅验证是否指定了一个。

这对于区分失败的代码检查和配置不正确的包很有用。
:::


## 脚本

```lakeHelp script
Manage Lake scripts

USAGE:
  lake script <COMMAND>

COMMANDS:
  list                  list available scripts
  run <script>          run a script
  doc <script>          print the docstring of a given script

See `lake script help <command>` for more information on a specific command.
```

```lakeHelp scripts
List available scripts

USAGE:
  lake script list

ALIAS: lake scripts

This command prints the list of all available scripts in the workspace.
```

:::lake script list (alias := scripts)
列出工作区中可用的{ref "lake-scripts"}[脚本]。
:::

```lakeHelp run
Run a script

USAGE:
  lake script run [[<package>/]<script>] [<args>...]

ALIAS: lake run

This command runs the `script` of the workspace (or the specific `package`),
passing `args` to it.

A bare `lake run` command will run the default script(s) of the root package
(with no arguments).
```

:::lake script run "[[package\"/\"]script [args...]]" (alias := run)
此命令运行工作区（或特定 {lakeMeta}`package`）的 {lakeMeta}`script`，
并将 {lakeMeta}`args` 传递给它。

单独的 {lake}`run` 命令将运行根包的默认脚本（没有参数）。
:::

:::lake script doc "script"
打印 {lakeMeta}`script` 的文档注释。
:::



## 语言服务器

```lakeHelp serve
Start the Lean language server

USAGE:
  lake serve [-- <args>...]

Run the language server of the Lean installation (i.e., via `lean --server`)
with the package configuration's `moreServerArgs` field and `args`.

```

:::lake serve "[\"--\" args...]"
在工作区的根项目中使用{tech (key := "package configuration")}[包配置]的 `moreServerArgs` 字段和 {lakeMeta}`args` 运行 Lean 语言服务器。

此命令通常由编辑器或其他工具调用，而不是手动调用。
:::

# 依赖管理

```lakeHelp update
Update dependencies and save them to the manifest

USAGE:
  lake update [<package>...]

ALIAS: lake upgrade

Updates the Lake package manifest (i.e., `lake-manifest.json`),
downloading and upgrading packages as needed. For each new (transitive) git
dependency, the appropriate commit is cloned into a subdirectory of
`packagesDir`. No copy is made of local dependencies.

If a set of packages are specified, said dependencies are upgraded to
the latest version compatible with the package's configuration (or removed if
removed from the configuration). If there are dependencies on multiple versions
of the same package, the version materialized is undefined.

A bare `lake update` will upgrade all dependencies.
```

:::lake update "[packages...]"
更新 Lake 包{tech (key := "manifest")}[清单]（即，`lake-manifest.json`），按需下载和升级包。
对于每个新的（传递的）{tech (key := "Git dependency")}[Git 依赖]，相应的提交将被克隆到工作区的{tech (key := "package directory")}[包目录]的一个子目录中。
不对本地依赖项进行复制。

如果指定了一组包 {lakeMeta}`packages`，那么这些依赖项将被升级到与包配置兼容的最新版本（或者如果从配置中移除，则被删除）。
如果存在对同一包的多个版本的依赖，则会选择任意一个版本。

单独的 {lake}`update` 将升级所有依赖项。
:::

# 打包和分发

```lakeHelp "upload"
Upload build artifacts to a GitHub release

USAGE:
  lake upload <tag>

Packs the root package's `buildDir` into a `tar.gz` archive using `tar` and
then uploads the asset to the pre-existing GitHub release `tag` using `gh`.
```

:::lake upload "tag"
使用 `tar` 将根包的 `buildDir` 打包为 `tar.gz` 归档文件，然后将该资产上传到已存在的 [GitHub](https://github.com) 发布版 {lakeMeta}`tag`；上传使用 [`gh`](https://cli.github.com/) 完成。
尚未支持其他主机。
:::

## 缓存的云端构建

*这些命令仍然是实验性的。*
它们可能会在 Lake 的未来版本中根据用户反馈发生变化。
使用 Reservoir 云构建归档文件的包应启用 {tomlField Lake.PackageConfig}`platformIndependent` 设置。

```lakeHelp "pack"
Pack build artifacts into an archive for distribution

USAGE:
  lake pack [<file.tgz>]

Packs the root package's `buildDir` into a gzip tar archive using `tar`.
If a path for the archive is not specified, creates an archive in the package's
Lake directory (`.lake`) named according to its `buildArchive` setting.

Does NOT build any artifacts. It just packs the existing ones.
```

:::lake pack "[archive.tar.gz]"
使用 `tar` 将根包的{tech (key := "build directory")}[构建目录]打包为 gzip tar 归档文件。
如果未指定归档文件的路径，将在包的 Lake 目录（`.lake`）中并根据其 `buildArchive` 设置命名该归档文件。
此命令不构建任何工件：它仅将现有的工件进行归档。
用户在运行此命令之前应确保存在所需的工件。
:::

```lakeHelp "unpack"
Unpack build artifacts from a distributed archive

USAGE:
  lake unpack [<file.tgz>]

Unpack build artifacts from the gzip tar archive `file.tgz` into the root
package's `buildDir`. If a path for the archive is not specified, uses the
the package's `buildArchive` in its Lake directory (`.lake`).
```

:::lake unpack "[archive.tar.gz]"
将 gzip tar 归档文件 {lakeMeta}`archive.tgz` 的内容解包到根包的{tech (key := "build directory")}[构建目录]中。
如果未指定 {lakeMeta}`archive.tgz`，将使用包的 `buildArchive` 设置来决定文件名，并预期该文件在包的 Lake 目录（`.lake`）中。
:::


# 本地缓存

{lake}`cache get`、{lake}`cache put` 和 {lake}`cache add` 用于与远程缓存服务器交互。
这些命令是*实验性的*，并且仅在启用了{ref "lake-cache"}[本地缓存]时有用。

可以配置这些命令使用{deftech (key := "cache scope")}[缓存作用域]，它是特定于服务器的一个包的一组构建输出的标识符。
在 Reservoir 上，作用域当前与 GitHub 仓库相同，但将来可能包含工具链和平台信息。
其他远程缓存可以使用它们想要的任何作用域方案。
使用 {lakeOptDef option}`--scope=` 选项来指定缓存作用域。
缓存作用域不同于用于从 Reservoir 请求包的作用域。

```lakeCacheHelp
Manage the Lake cache

USAGE:
  lake cache <COMMAND>

COMMANDS:
  get [<mappings>]      download build outputs into the local Lake cache
  put <mappings>        upload build outputs to a remote cache
  add <mappings>        add input-to-output mappings to the Lake cache
  clean                 removes ALL from the local Lake cache
  services              print configured remote cache services

STAGING COMMANDS:
  stage <map> <dir>     copy build outputs from the cache to a directory
  unstage <dir>         cache build outputs from a staging directory
  put-staged <dir>      upload build outputs from a staging directory

See `lake cache help <command>` for more information on a specific command.
```

```lakeCacheHelp get
Download build outputs from a remote service into the Lake cache

USAGE:
  lake cache get [<mappings>]

OPTIONS:
  --max-revs=<n>                  backtrack up to n revisions (default: 100)
  --rev=<commit-hash>             lookup artifacts only for set revision
  --package=<name>                fetch outputs for set package
  --service=<name>                fetch outputs from set cache service
  --repo=<github-repo>            GitHub repository of the package or its fork
  --platform=<target-triple>      with Reservoir or --repo, set the platform
  --toolchain=<name>              with Reservoir or --repo, set the toolchain
  --scope=<remote-scope>          verbatim scope for a custom endpoint
  --mappings-only                 only download mappings, delay artifacts
  --force-download                redownload existing files

Downloads build outputs for packages in the workspace from a remote cache
service. The cache service used can be specified via the `--service` option.
Otherwise, Lake will use the configured default or, if none, Reservoir. See
`lake cache services` for more information on how to configure services.

By default, Lake will use Reservoir to download outputs for each
dependency in the workspace (in order). Non-Reservoir dependencies will be
skipped. If instead an input-to-outputs mappings file, `--scope`, or `--repo`
is provided, Lake will default to downloading build outputs for the root
package. In either case, if `--package` is specified, Lake will switch to
only downloading outputs for it.

To determine what to download, Lake searches for input-to-output mappings for
a given build of a package via the cache service. This mapping is identified
by a Git revision and prefixed with a scope derived from the package's name,
GitHub repository, Lean toolchain, and current platform. The exact configuration
can be customized using options.

For Reservoir, setting `--repo` will cause Lake to lookup outputs for the
package by a repository name, rather than the package's. This can be used to
download outputs for a fork of the Reservoir package (if such artifacts are
available). The `--platform` and `--toolchain` options can be used to download
artifacts for a different platform/toolchain configuration than Lake detects.
For a custom endpoint, the full prefix Lake uses can be set via `--scope`.

If `--rev` is not set, Lake uses the package's current revision to lookup
artifacts. If no mappings are found, Lake will backtrack the Git history up to
`--max-revs`, looking for a revision with mappings. If `--max-revs` is 0, Lake
will search the repository's entire history (or as far as Git will allow).

By default, Lake will download both the input-to-output mappings and the
output artifacts for a package. By using `--mappings-only`, Lake will only
download the mappings and delay downloading artifacts until they are needed.

If a download for an artifact fails or the download process for a whole
package fails, Lake will report this and continue on to the next. Once done,
if any download failed, Lake will exit with a nonzero status code.
```

:::lake cache get "[mappings] [\"--max-revs=\" cn] [\"--rev=\" «commit-hash»] [\"--package=\" «name»] [\"--service=\" «name»] [\"--repo=\" «github-repo»] [\"--platform=\" «target-triple»] [\"--toolchain=\"«name»] [\"--scope=\" «remote-scope»] [\"--mappings-only\"] [\"--force-download\"]"
从远程缓存服务向本地 Lake {tech (key:="local cache")}[工件缓存]下载工作区中包的构建输出。
可以通过 {lakeOpt}`--service` 选项指定使用的缓存服务。
否则，Lake 将使用系统默认服务；如果未配置任何服务，则使用 Reservoir。
参阅 {lake}`cache services` 了解如何配置服务的更多信息。

默认情况下，Lake 将使用 Reservoir 按顺序下载根依赖项树中每个包的输出。
非 Reservoir 依赖将被跳过。
如果提供了输入到输出 {lakeMeta}`mappings` 文件、{lakeMeta}`remote-scope` 或是 {lakeMeta}`github-repo`，Lake 默认将下载根包的构建输出。
无论是哪种情况，{lakeOptDef option}`--package` 都会将下载限制在命名的包的输出上。

对于 Reservoir，设置 {lakeOpt}`--repo` 将使 Lake 按仓库名称而不是包名称查找包的输出。
这可以用来下载 Reservoir 包的一个分支的输出（如果此类工件可用的话）。
{lakeOpt}`--platform` 和 {lakeOpt}`--toolchain` 选项可用于为 Lake 所检测到的平台/工具链之外的配置下载工件。
对于自定义端点，Lake 使用的完整前缀可以通过 {lakeOpt}`--scope` 设置。

如果未设置 `--rev`，Lake 使用包当前的版本来查找工件。
Lake 将为具有可用映射的最新提交下载工件。
它最多将回溯 {lakeOptDef option}`--max-revs` 个版本，默认为 100。
如果设为 0，Lake 将搜索仓库的整个历史记录，或者追溯到 Git 所允许的范围。

默认情况下，Lake 将同时下载包的输入到输出映射和输出工件。
使用 {lakeOptDef option}`--mappings-only` 将使 Lake 仅下载映射，并延迟下载工件，直到它们被需要时为止。
使用 {lakeOptDef option}`--force-download` 将重新下载现有文件。

在下载期间，当某工件的下载失败或整个包的下载过程失败时，Lake 将继续执行。
但是，在这种情况下，它将报告该情况，并以非零状态码退出。
:::


```lakeCacheHelp put
Upload build outputs from the Lake cache to a remote service

USAGE:
  lake cache put <mappings>

OPTIONS:
  --service=<name>                upload to set cache service
  --scope=<remote-scope>          upload under set scope verbatim
  --repo=<github-repo>            scope w/ repository + toolchain & platform
  --toolchain=<name>              with --repo, sets the toolchain
  --platform=<target-triple>      with --repo, sets the platform

Uploads the input-to-output mappings contained in the specified file along
with the corresponding output artifacts to a remote cache. The cache service
used can be specified via the `--service` option. If not specified, Lake will
use the system default, or error if none is configured. See the help page of
`lake cache services` for more information on how to configure services.

Files are uploaded using the AWS Signature Version 4 authentication protocol
via `curl`. Thus, the service should generally be an S3-compatible bucket.
The authentication key is set via the `LAKE_CACHE_KEY` environment variable.

Since Lake does not currently use cryptographically secure hashes for
artifacts and outputs, uploads to the cache are prefixed with a scope to
avoid clashes. This is controlled by `--scope` or `--repo`. With `--repo`,
Lake will produce a scope by augmenting the repository with toolchain and
platform information as it deems necessary. With `--scope`, Lake will use
the specified scope verbatim.

Artifacts are uploaded to the artifact endpoint with a file name derived
from their Lake content hash (and prefixed by the repository or scope).
The mappings file is uploaded to the revision endpoint with a file name
derived from the package's current Git revision (and prefixed by the
full scope). As such, the command will warn if the work tree currently
has changes.
```

::::lake cache put "mappings [\"--service=\" «name»] [\"--scope=\" «remote-scope»] [\"--repo=\" «github-repo»] [\"--toolchain=\" «name»] [\"--platform=\" «target-triple»]"
将指定文件中包含的输入到输出映射连同相应的输出工件一起上传到远程缓存。
使用的缓存服务可以通过 {lakeOpt}`--service` 选项指定。
如果未指定，Lake 将使用系统默认服务；如果未配置，则会报错。
请参阅 {lake}`cache services` 了解有关如何配置服务的更多信息。

文件是通过 `curl` 使用 AWS Signature Version 4 认证协议上传的。
因此，该服务通常应是一个兼容 S3 的存储桶。
认证密钥通过 {envVar}`LAKE_CACHE_KEY` 环境变量设置。

由于 Lake 目前不对工件和输出使用加密安全的哈希，因此缓存的上传以作用域作为前缀以避免冲突。
作用域由以下选项控制：

:::table -header
*
  * {lakeOpt}`--scope`{lit}`=`{lakeMeta}`<remote-scope>`
  * 原样使用提供的作用域 {lakeMeta}`<remote-scope>`
*
  * {lakeOptDef option}`--repo`{lit}`=`{lakeMeta}`<github-repo>`
  * 使用仓库、工具链和平台作为作用域
*
  * {lakeOptDef option}`--toolchain`{lit}`=`{lakeMeta}`<name>`
  * 与 {lakeOpt}`--repo` 一起使用，设置工具链
*
  * {lakeOptDef option}`--platform`{lit}`=`{lakeMeta}`<target-triple>`
  * 与 {lakeOpt}`--repo` 一起使用，设置平台
:::

对于 {lakeOpt}`--repo`，Lake 会通过在认为必要时为仓库添加工具链和平台信息来生成作用域。
对于 {lakeOpt}`--scope`，Lake 会原样使用指定的作用域。

工件会以由其 Lake 内容哈希派生的文件名（带有仓库或作用域前缀）上传到工件端点。
映射文件会以由该包当前 Git 版本派生的文件名（带有完整作用域前缀）上传到修订版本端点。
因此，如果工作树目前有更改，命令将会发出警告。
::::

```lakeCacheHelp add
Add input-to-output mappings to the Lake cache

USAGE:
  lake cache add <mappings>

OPTIONS:
  --package=<name>                add mappings to set package
  --service=<name>                cache service to fetch from on demand
  --scope=<remote-scope>          the prefix of artifacts within the service
  --repo=<github-repo>            for Reservoir, a GitHub repository scope
  --no-overwrite                  do not overwrite existing mappings

Reads a list of input-to-output mappings from the provided file and adds
them to the local Lake cache. Mappings already in the cache are overwritten
unless `--no-overwrite` is specified. Mappings are added for the root package
unless `--package` is specified.

If `--service` is provided, the output artifacts can then be fetched lazily
from that service during a Lake build. The service must either be `reservoir`
or be configured through the Lake system configuration (see the help page of
`lake cache services` for details).

Since Lake does not currently use cryptographically secure hashes for
artifacts and outputs, artifacts in a cache service are prefixed with a scope
to avoid clashes. For Reservoir, this scope can either be a package (set via
`--scope`) or a repository (set via `--repo`). For S3 services, both options
are synonymous.
```

::::lake cache add "mappings [\"--package=\" «name»] [\"--service=\" «name»] [\"--scope=\" «remote-scope»] [\"--repo=\" «github-repo»] [\"--no-overwrite\"]"
从提供的文件中读取一系列输入到输出映射，并将它们添加到本地 Lake 缓存中。
除非指定了 {lakeOptDef flag}`--no-overwrite`，否则缓存中已经存在的映射将被覆盖。
除非指定了 {lakeOpt}`--package`，否则映射将被添加到根包中。

如果提供了 {lakeOpt}`--service`，那么输出工件可以在 Lake 构建期间从该服务延迟获取。
服务必须是 `reservoir`，或者是通过 Lake 系统配置进行配置的（请参阅 {lake}`cache services` 了解详情）。

由于 Lake 目前不对工件和输出使用密码安全哈希，因此缓存服务中的工件会添加作用域前缀，以避免冲突。
对于 Reservoir，该作用域可以是包（通过 {lakeOpt}`--scope` 设置）或仓库（通过 {lakeOpt}`--repo` 设置）。
对于 S3 服务，这两个选项是同义词。
::::

```lakeCacheHelp clean
Removes ALL files from the local Lake cache

USAGE:
  lake cache clean

Deletes the configured Lake cache directory. If a workspace configuration
exists, this will delete the cache directory it uses. Otherwise, it will
delete the default Lake cache directory for the system.
```

:::lake cache clean
删除配置的 Lake {tech (key:="local cache")}[工件缓存]目录。
如果工作区配置存在，这将删除其所使用的缓存目录。
否则，它将删除系统的默认 Lake 缓存目录。
:::

```lakeCacheHelp services
Print configured remote cache services

USAGE:
  lake cache services

Prints the name of each configured remote cache services (one per line).
Additional services can be added by modifying the system Lake configuration.
The exact location of the this configuration file is system dependent and can
be set by `LAKE_CONFIG`, but it is usually located at `~/.lake/config.toml`.

The configuration of the system cache could look something like the following:

  cache.defaultService = "my-s3"
  cache.defaultUploadService = "my-s3"

  [[cache.service]]
  name = "my-s3"
  kind = "s3"
  artifactEndpoint = "https://my-s3.com/a0"
  revisionEndpoint = "https://my-s3.com/r0"

If no `cache.defaultService` is configured, Lake will use Reservoir by default.
```

::::lake cache services
打印每个已配置的远程缓存服务的名称（每行一个）。
可以通过修改系统 Lake 配置文件添加其他服务，该文件通常位于 `~/.lake/config.toml`，但也可以通过 {envVar}`LAKE_CONFIG` 环境变量进行设置。

:::paragraph
系统缓存配置类似如下：
```toml -link
cache.defaultService = "my-s3"
cache.defaultUploadService = "my-s3"

[[cache.service]]
name = "my-s3"
kind = "s3"
artifactEndpoint = "https://my-s3.com/a0"
revisionEndpoint = "https://my-s3.com/r0"
```
如果没有配置 `cache.defaultService`，Lake 默认将使用 Reservoir。
:::
::::

```lakeCacheHelp stage
Copy build outputs from the cache to a staging directory

USAGE:
  lake cache stage <mappings> <staging-directory> [--force-overwrite]

Creates the staging directory and copies the mappings file to it. Then,
it copies all artifacts described within the mappings file from the cache to
the staging directory. Artifacts in the staging directory are not overwritten
unless `--force-overwrite` is specified. Errors if any of the artifacts
described cannot be found in the cache.
```

::::lake cache stage "mappings «staging-directory» [\"--force-overwrite\"]"
创建 {lakeMeta}`staging-directory` 并将 {lakeMeta}`mappings` 文件复制到其中。
在这之后，它会将映射文件中描述的所有工件从缓存复制到暂存目录。
除非指定了 {lakeOptDef flag}`--force-overwrite`，否则已经存在于登台目录中的工件不会被覆盖。
如果无法在缓存中找到描述的任何工件，则报错。
::::

```lakeCacheHelp unstage
Cache build outputs from a staging directory

USAGE:
  lake cache unstage <staging-directory> [--force-overwrite]

Copies the mappings and artifacts stored in staging directory (e.g., via
`lake cache stage`) back into the cache.

Reads the mappings file located at `outputs.jsonl` within the staging
directory and writes the mappings to the Lake cache. Then, it copies the
described artifacts from the staging directory into the cache. Mappings and
artifacts already in the cache are not overwritten unless `--force-overwrite`
is specified.
```

::::lake cache unstage "«staging-directory» [\"--force-overwrite\"]"

将存储在 {lakeMeta}`staging-directory` 中的映射和工件（例如，通过 {lake}`cache stage` 生成的）复制回缓存中。

它读取登台目录内的 `outputs.jsonl` 处的映射文件，并将该映射写入 Lake 缓存中。然后，它将描述的工件从登台目录复制到缓存中。
除非指定了 {lakeOpt}`--force-overwrite`，否则缓存中已经存在的映射和工件不会被覆盖。
::::


```lakeCacheHelp "put-staged"
Upload build outputs from a staging directory to a remote service

USAGE:
  lake cache put-staged <staging-directory>

OPTIONS:
  --rev=<commit-hash>             upload for set revision
  --service=<name>                upload to set cache service
  --scope=<remote-scope>          upload under set scope verbatim
  --repo=<github-repo>            scope w/ repository + toolchain & platform
  --toolchain=<name>              with --repo, set the toolchain
  --platform=<target-triple>      with --repo, set the platform

Works like `lake cache put` but uploads outputs from the staging directory
instead of the Lake cache.

Does not configure the workspace and thus does not execute arbitrary user
code. However, because of this, the package's platform and toolchain settings
will not be automatically detected for `--repo` and must be specified manually
via `--platform` and `--toolchain` (if needed).

Lake will still, by default, detect the target revision from the workspace
directory's current Git revision. To upload outputs for a different revision,
specify it with `--rev`.
```

::::lake cache «put-staged» "«staging-directory» [\"--rev=\" «commit-hash»] [\"--service=\" «name»] [\"--scope=\" «remote-scope»] [\"--repo=\" «github-repo»] [\"--toolchain=\" «name»] [\"--platform=\" «target-triple»]"
将存储在 {lakeMeta}`staging-directory` 中的映射和工件（例如，通过 {lake}`cache stage` 生成的）上传到远程服务。
这与 {lake}`cache put` 工作原理类似，区别在于输出取自暂存目录，而不是来自 Lake {tech (key:="local cache")}[工件缓存]。

此命令不配置工作区，因此它不执行任意用户代码。
因此，包的平台和工具链设置对于 {lakeOpt}`--repo` 是无法自动检测到的，如果需要，必须通过 {lakeOpt}`--platform` 和 {lakeOpt}`--toolchain` 指定。

默认情况下，Lake 将从工作区目录的当前 Git 版本中检测目标版本。
通过使用 {lakeOptDef option}`--rev` 指定不同的版本，可以上传不同版本的输出。
::::


# 配置文件


```lakeHelp "translate-config"
Translate a Lake configuration file into a different language

USAGE:
  lake translate-config <lang> [<out-file>]

Translates the loaded package's configuration into another of
Lake's supported configuration languages (i.e., either `lean` or `toml`).
The produced file is written to `out-file` or, if not provided, the path of
the configuration file with the new language's extension. If the output file
already exists, Lake will error.

Translation is lossy. It does not preserve comments or formatting and
non-declarative configuration will be discarded.
```

:::lake «translate-config» "lang [«out-file»]"
将已加载的包的配置翻译为 Lake 的另一种受支持的配置语言（即 `lean` 或 `toml`）。
生成的文件将写入 `out-file`，如果未提供，则写入带有新语言扩展名的配置文件路径中。
如果输出文件已存在，Lake 会报错。

翻译是有损的。
它不会保留注释或格式，非声明性配置将被丢弃。
:::
