/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Config.Monad
import Lake.DSL

import Manual.Meta
import Manual.BuildTools.Lake.CLI
import Manual.ZhDocString.BuildTools.Config


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lake.DSL

#doc (Manual) "配置文件格式" =>
%%%
tag := "lake-config"
%%%

:::paragraph
Lake 为{tech (key := "package configuration")}[包配置]文件提供两种格式：

: TOML

  TOML 配置格式完全是声明式的。
  不包含自定义目标、分面或脚本的项目可以使用 TOML 格式。
  由于许多语言都有 TOML 解析器，使用这种格式便于和不是用 Lean 编写的工具集成。

: Lean

  Lean 配置格式更灵活，允许自定义目标、分面和脚本。
  它提供一种嵌入式领域特定语言，用于描述 TOML 格式所提供配置选项的声明式子集。
  此外，Lake API 还可用于表达声明式选项无法表达的构建配置。

{lake}`translate-config` 命令可用于在两种格式之间自动转换。
:::

Lake 以类似方式处理这两种格式，并以内部结构类型的形式从配置文件提取{tech (key := "package configuration")}[包配置]。
{tech (key := "configure package")}[配置包]时，所得数据结构会写入{tech (key := "build directory")}[构建目录]中的 `lakefile.olean`。


# 声明式 TOML 格式
%%%
tag := "lake-config-toml"
%%%


TOML{margin}[[_Tom's Obvious Minimal Language_](https://toml.io/en/) 是一种标准化的配置文件格式。] 配置文件描述 Lake {tech (key := "package configuration")}[包配置]文件中最常用的声明式子集。
TOML 文件表示将键映射到值的_表_。
值可以是字符串、数字、值数组或嵌套的表。
由于 TOML 的文件结构非常灵活，本参考手册记录预期的值，而不是生成这些值的具体语法。

{configFile}`lakefile.toml` 的内容应表示描述 Lean 包的 TOML 表。
该配置既包含描述整个包的标量字段，也包含以下由更多表组成的数组字段：
 * `require`
 * `lean_lib`
 * `lean_exe`

目前，不属于此处所述配置表的字段会被忽略。
为降低拼写错误的风险，这种行为将来可能会改变。
不应使用 Lake 未使用的字段名来存储供其他工具处理的元数据。


## 包配置
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Declarative-TOML-Format--Package-Configuration"
%%%

`lakefile.toml` 的顶层内容指定适用于包本身的选项，包括名称和版本等元数据、{tech (key := "workspace")}[工作区]中文件的位置，以及用于所有{tech (key := "targets")}[目标]的编译器标志等。
唯一的必填字段是 `name`，它声明包的名称。

:::::tomlTableDocs root "包配置" Lake.PackageConfig (skip := backend) (skip := releaseRepo?) (skip := buildArchive?) (skip := manifestFile) (skip := moreServerArgs) (skip := dynlibs) (skip := plugins)

::::tomlFieldCategory "元数据" name version versionTags description keywords homepage license licenseFiles readmeFile reservoir
这些选项描述包。
[Reservoir](https://reservoir.lean-lang.org/) 使用它们来索引和显示包。
如果省略某个字段，Reservoir 可能使用包的 GitHub 仓库信息补全细节。

:::tomlField Lake.PackageConfig name "包名称" "包名称" String
包的名称。
:::
::::

:::tomlFieldCategory "布局" packagesDir srcDir buildDir leanLibDr nativeLibDir binDir irDir
这些选项控制包及其构建目录的顶层目录布局。
包中库、可执行文件和目标指定的其他路径均相对于这些目录。
:::

:::tomlFieldCategory "构建与运行" defaultTargets leanLibDir platformIndependent precompileModules moreServerOptions moreGlobalServerArgs buildType leanOptions moreLeanArgs weakLeanArgs moreLeancArgs weakLeancArgs moreLinkArgs weakLinkArgs extraDepTargets

这些选项配置如何在包中构建和运行代码。
包中的库、可执行文件和其他{tech (key := "targets")}[目标]可以进一步扩充此配置的某些部分。

:::

:::tomlFieldCategory "测试与代码检查" testDriver testDriverArgs lintDriver lintDriverArgs builtinLint

命令行命令 {lake}`test` 和 {lake}`lint` 使用由{tech (key := "workspace")}[工作区]的{tech (key := "root package")}[根包]配置的定义来执行测试和代码检查。
为执行测试和代码检查而运行的代码称为测试驱动或代码检查驱动。
在 Lean 配置文件中，可以通过将 `@[test_driver]` 或 `@[lint_driver]` 属性应用于{tech (key := "Lake script")}[Lake 脚本]、可执行文件目标或库目标来指定它们。
在 Lean 和 TOML 配置文件中，也可以通过设置这些选项来配置它们。
可以使用字符串 `"PKG/TGT"` 将依赖项 `PKG` 中的目标或脚本 `TGT` 指定为测试或代码检查驱动。

:::

:::tomlFieldCategory "云端发行版" releaseRepo buildArchive preferReleaseBuild

这些选项为包定义云端发行版，详见{ref "lake-github"}[GitHub 发行版构建]一节。

:::

:::tomlField Lake.PackageConfig defaultTargets "默认目标名称（数组）" "默认目标名称（数组）" String (sort := 2)

{zhincludeDocstring Lake.Package.defaultTargets ZhDoc.BuildTools.Config.Package.defaultTargets}

:::

:::::

:::::example "最小 TOML 包配置" (file := "Minimal TOML Package Configuration")
Lean {tech (key := "package")}[包]的最小 TOML 配置只设置包名，其他所有字段均使用默认值。
此包不含{tech (key := "targets")}[目标]，因此没有需要构建的代码。

::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
```
```expected
{wsIdx := 0,
  baseName := `«example-package»,
  keyName := `«example-package»,
  origName := `«example-package»,
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
  targetDecls := #[],
  targetDeclMap := {},
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

:::::example "库的 TOML 包配置" (file := "Library TOML Package Configuration")
Lean {tech (key := "package")}[包]的最小 TOML 配置设置包名并定义一个库目标。
此库名为 `Sorting`，其模块应位于 `Sorting.*` 层次结构下。
::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
defaultTargets = ["Sorting"]

[[lean_lib]]
name = "Sorting"
```
```expected
{wsIdx := 0,
  baseName := `«example-package»,
  keyName := `«example-package»,
  origName := `«example-package»,
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
          {pkg := `«example-package»,
            name := `Sorting,
            kind := `lean_lib,
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
                roots := #[`Sorting],
                globs := #[Lake.Glob.one `Sorting],
                libName := "",
                libPrefixOnWindows := false,
                needs := #[],
                extraDepTargets := #[],
                precompileModules := false,
                defaultFacets := #[`lean_lib.leanArts],
                nativeFacets := #<fun>,
                allowImportAll := false},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`Sorting ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«example-package»,
                  name := `Sorting,
                  kind := `lean_lib,
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
                      roots := #[`Sorting],
                      globs := #[Lake.Glob.one `Sorting],
                      libName := "",
                      libPrefixOnWindows := false,
                      needs := #[],
                      extraDepTargets := #[],
                      precompileModules := false,
                      defaultFacets := #[`lean_lib.leanArts],
                      nativeFacets := #<fun>,
                      allowImportAll := false},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[`Sorting],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

## 依赖项
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Declarative-TOML-Format--Dependencies"
%%%

依赖项在包配置的 {toml}`[[require]]` 字段数组中指定，其中同时指定每个包的名称和来源。
来源有三类：
 * [Reservoir](https://reservoir.lean-lang.org/) 或其他包注册表
 * Git 仓库，可以是本地路径或 URL
 * 本地路径

::::tomlTableDocs "require" "引入包" Lake.Dependency (skip := src?) (skip := opts) (skip := subdir) (skip := version)

{tomlField Lake.Dependency}`path` 和 {tomlField Lake.Dependency}`git` 字段为依赖项指定显式来源。
如果两者均未提供，则从 [Reservoir](https://reservoir.lean-lang.org/) 获取依赖项；如果配置了其他注册表，则从该注册表获取。
从 Reservoir 获取包时，必须提供 {tomlField Lake.Dependency}`scope` 字段。

:::tomlField Lake.Dependency path "路径" "路径" System.FilePath
本地文件系统中的依赖项，以其路径指定。
:::

:::tomlField Lake.Dependency git "Git 规格" "Git 规格" Lake.DependencySrc
Git 仓库中的依赖项，可以用 URL 字符串指定，也可以用包含以下键的表指定：
 * `url`：仓库 URL
 * `subDir`：Git 仓库中包含包源代码的子目录
:::

:::tomlField Lake.Dependency rev "Git 修订版本" "Git 修订版本" String
对于 Git 或 Reservoir 依赖项，此字段指定 Git 修订版本，可以是分支名、标签名或特定哈希。
在 Reservoir 上，`version` 字段优先于此字段。
:::

:::tomlField Lake.Dependency source "包来源" "包来源" Lake.DependencySrc
依赖项来源，以独立表指定，在既没有 `git` 键也没有 `path` 键时使用。
键 `type` 应为字符串 `"git"` 或字符串 `"path"`。
如果类型是 `"path"`，则还必须有一个 `"path"` 键，其字符串值给出包在磁盘上的位置。
如果类型是 `"git"`，则应提供以下键：
 * `url`：仓库 URL
 * `rev`：Git 修订版本，可以是分支名、标签名或特定哈希（可选）
 * `subDir`：Git 仓库中包含包源代码的子目录
:::

:::tomlField Lake.Dependency version "字符串形式的版本" "字符串形式的版本" String

{zhincludeDocstring Lake.Dependency.version ZhDoc.BuildTools.Config.Dependency.version}

:::

::::

:::::example "从 Reservoir 引入包" (file := "Requiring Packages from Reservoir")
可以使用以下 TOML 配置从 Reservoir 引入包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
version = "≥2.12.0"
scope = "exampleDev"
```
```expected
#[{name := `example,
    scope := "exampleDev",
    version :=
      Lake.InputVer.ver
        { toString := "≥2.12.0",
          clauses := #[#[{ ver := { toSemVerCore := { major := 2, minor := 12, patch := 0 }, specialDescr := "" },
                           op := Lake.ComparatorOp.ge,
                           includeSuffixes := false }]] },
    src? := none,
    opts := {}}]
```
::::
:::::

:::::example "从 Git 引入包" (file := "Requiring Packages from Git")
可以使用以下 TOML 配置从 Git 仓库引入包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "main"
version = "≥2.12.0"
```
```expected
#[{name := `example,
    scope := "",
    version :=
      Lake.InputVer.ver
        { toString := "≥2.12.0",
          clauses := #[#[{ ver := { toSemVerCore := { major := 2, minor := 12, patch := 0 }, specialDescr := "" },
                           op := Lake.ComparatorOp.ge,
                           includeSuffixes := false }]] },
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "main") none),
    opts := {}}]
```
::::

具体而言，该包会从 `main` 分支检出，且包的{tech (key := "package configuration")}[配置]中指定的版本号应不低于 `2.12.0`。
:::::

:::::example "从 Git 标签引入包" (file := "Requiring Packages from a Git tag")
可以使用以下 TOML 配置从 Git 仓库的 `v2.12` 标签引入包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "v2.12"
```
```expected
#[{name := `example,
    scope := "",
    version := Lake.InputVer.git "v2.12",
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "v2.12") none),
    opts := {}}]
```
::::
不会使用包的{tech (key := "package configuration")}[配置]中指定的版本号。
:::::

:::::example "从 Git 标签引入 Reservoir 包" (file := "Requiring Reservoir Packages from a Git tag")
可以使用以下 TOML 配置，从 Reservoir 找到包 `example`，并从其 Git 仓库的 `v2.12` 标签引入：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
rev = "v2.12"
scope = "exampleDev"
```
```expected
#[{name := `example, scope := "exampleDev", version := Lake.InputVer.git "v2.12", src? := none, opts := {}}]
```
::::
不会使用包的{tech (key := "package configuration")}[配置]中指定的版本号。
:::::

:::::example "从路径引入包" (file := "Requiring Packages from Paths")
可以使用以下 TOML 配置从本地路径 `../example` 引入包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
path = "../example"
```
```expected
#[{name := `example,
    scope := "",
    version := Lake.InputVer.none,
    src? := some (Lake.DependencySrc.path (FilePath.mk "../example")),
    opts := {}}]
```
::::
在单个仓库中开发多个包，或测试依赖项的某项变更是否修复下游包中的错误时，本地路径依赖项很有用。
:::::

:::::example "以表表示来源" (file := "Sources as Tables")
包来源信息可以写在显式表中。
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
source = {type = "git", url = "https://example.com/example.git"}
```
```expected
#[{name := `example,
    scope := "",
    version := Lake.InputVer.none,
    src? := some (Lake.DependencySrc.git "https://example.com/example.git" none none),
    opts := {}}]
```
::::
:::::

## 库目标
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Declarative-TOML-Format--Library-Targets"
%%%

库目标应写在 `lean_lib` 表数组中。

::::tomlTableDocs "lean_lib" "库目标" Lake.LeanLibConfig (skip := backend) (skip := globs) (skip := nativeFacets)
:::tomlField Lake.LeanLibConfig name "库名称" "库名称" String
库的名称，通常与其唯一模块根同名。
:::

::::

:::::example "最小库目标" (file := "Minimal Library Target")
此库声明只提供名称：
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
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
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "",
      libPrefixOnWindows := false,
      needs := #[],
      extraDepTargets := #[],
      precompileModules := false,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>,
      allowImportAll := false}}]
```
::::
该库的源代码位于包的默认源目录中，处于以 `TacticTools` 为根的模块层次结构下。
:::::

:::::example "已配置的库目标" (file := "Configured Library Target")
此库声明提供更多选项：
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
srcDir = "src"
precompileModules = true
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
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
      srcDir := FilePath.mk "src",
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "",
      libPrefixOnWindows := false,
      needs := #[],
      extraDepTargets := #[],
      precompileModules := true,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>,
      allowImportAll := false}}]
```
::::
该库的源代码位于 `src` 目录中，处于以 `TacticTools` 为根的模块层次结构下。
如果在精译时访问其模块，它们会编译为原生代码并链接进来，而不是在解释器中运行。
:::::

## 可执行文件目标
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Declarative-TOML-Format--Executable-Targets"
%%%

:::: tomlTableDocs "lean_exe" "可执行文件目标" Lake.LeanExeConfig (skip := backend) (skip := globs) (skip := nativeFacets)
:::tomlField Lake.LeanExeConfig name "可执行文件名称" "可执行文件名称" String
可执行文件的名称。
:::

::::

:::::example "最小可执行文件目标" (file := "Minimal Executable Target")
此可执行文件声明只提供名称：
::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthytool"
```
```expected
#[{ name := trustworthytool,
    val := {toLeanConfig :=
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
      root := `trustworthytool,
      exeName := "trustworthytool",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```

可执行文件的 {lean}`main` 函数应位于包默认源文件路径下名为 `trustworthytool.lean` 的模块中。
生成的可执行文件名为 `trustworthytool`。
:::::

:::::example "已配置的可执行文件目标" (file := "Configured Executable Target")
名称 `trustworthy-tool` 因包含连字符（`-`）而不是有效的 Lean 名称。
要将此名称用于可执行文件目标，必须提供显式模块根。
尽管 `trustworthy-tool` 完全可以作为可执行文件名，该目标还指定编译和链接的结果应命名为 `tt`。

::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthy-tool"
root = "TrustworthyTool"
exeName = "tt"
```
```expected
#[{ name := «trustworthy-tool»,
    val := {toLeanConfig :=
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
      root := `TrustworthyTool,
      exeName := "tt",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```

可执行文件的 {lean}`main` 函数应位于包默认源文件路径下名为 `TrustworthyTool.lean` 的模块中。
:::::

# Lean 格式
%%%
tag := "lake-config-lean"
%%%


Lake {tech (key := "package configuration")}[包配置]文件的 Lean 格式为 TOML 格式支持的声明式功能提供了一种领域特定语言。
此外，还可以编写 Lean 代码来实现任何无法以声明方式表达的必要构建逻辑。
Lean 配置文件名为 {configFile}`lakefile.lean`。

由于 Lean 格式是 Lean 源文件，因此可以使用 Lean 语言服务器的全部功能进行编辑。
此外，Lean 的元编程框架允许使用精译时副作用，实现依赖当前平台的配置步骤等功能。
不过，Lean 配置格式是 Lean 文件，这意味着使用并非以 Lean 编写的工具处理此类文件并不可行。

```lean -show
section
open Lake DSL
open Lean (NameMap)
```

## 声明式字段
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Declarative-Fields"
%%%

Lean 配置格式的声明式子集使用声明字段序列来指定配置选项。

:::syntax Lake.DSL.declField (title := "声明式字段") -open

{zhincludeDocstring Lake.DSL.declField ZhDoc.BuildTools.Config.DSL.declField}

```grammar
$_ := $_
```
:::

## 包
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Packages"
%%%
::::syntax command (title := "包配置")
```grammar
$[$_:docComment]?
$[@[ $_,* ]]?
package $name:identOrStr
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $name where
  $item*
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```

每个 Lake 配置文件只能有一个 {keywordOf Lake.DSL.packageCommand}`package` 声明。
已定义的包配置可通过 `_package` 引用。

::::

::::syntax command (title := "更新后钩子")
```grammar
post_update $[$name]? $v
```

{zhincludeDocstring Lake.DSL.postUpdateDecl ZhDoc.BuildTools.Config.DSL.postUpdateDecl}

::::


## 依赖项
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Dependencies"
%%%

依赖项使用 {keywordOf Lake.DSL.requireDecl}`require` 声明指定。

:::syntax command (title := "引入包")
```grammar
$doc:docComment
require $name:depName $[@ $[git]? $_:term]? $[$_:fromClause]? $[with $_:term]?
```

`@` 子句指定包版本，用于从 [Reservoir](https://reservoir.lean-lang.org/) 引入包。
版本可以是指定包的 {name Lake.PackageConfig.version}`version` 字段中所声明版本的字符串，也可以是具体的 Git 修订版本。
Git 修订版本可以是分支名、标签名或提交哈希。

可选的 {syntaxKind}`fromClause` 指定 Reservoir 以外的包来源，可以是 Git 仓库或本地路径。

{keywordOf Lake.DSL.requireDecl}`with` 子句指定用于配置依赖项的 Lake 选项 {lean}`NameMap String`。
这等价于在命令行构建依赖项时向 {lake}`build` 传递 {lakeOpt}`-K` 选项。
:::

:::syntax fromClause -open (title := "包来源")

{zhincludeDocstring Lake.DSL.fromClause ZhDoc.BuildTools.Config.DSL.fromClause}

```grammar
from $t:term
```

```grammar
from git $t $[@ $t]? $[/ $t]?
```

:::


## 目标
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets"
%%%



通常通过应用 `default_target` 属性将{tech (key := "Targets")}[目标]加入默认目标集合，而不是显式列出它们。
:::TODO
修复上面的 `default_target`——它在 CI 上不工作，但在本地配合 `attr` 角色可以工作。
:::

:::syntax attr (title := "指定默认目标") (label := "属性") (namespace := Lake.DSL)

```grammar
default_target
```
将目标标记为默认目标，在未指定其他目标时构建。
:::

### 库
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets--Libraries"
%%%


:::syntax command (title := "库目标")

要定义所有可配置字段均使用默认值的库，请使用 {keywordOf Lake.DSL.leanLibCommand}`lean_lib`，不再添加字段。

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr
```

可以通过提供新值来修改默认配置。

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr where
  $field*
```


```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{keywordOf Lake.DSL.leanLibCommand}`lean_lib` 的字段就是 {name Lake.LeanLibConfig}`LeanLibConfig` 结构的字段。

{zhdocstring Lake.LeanLibConfig ZhDoc.BuildTools.Config.LeanLibConfig}

### 可执行文件
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets--Executables"
%%%

:::syntax command (title := "可执行文件目标")

要定义所有可配置字段均使用默认值的可执行文件，请使用 {keywordOf Lake.DSL.leanExeCommand}`lean_exe`，不再添加字段。

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr
```

可以通过提供新值来修改默认配置。

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr where
  $field*
```

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{keywordOf Lake.DSL.leanExeCommand}`lean_exe` 的字段就是 {name Lake.LeanExeConfig}`LeanExeConfig` 结构的字段。

{zhdocstring Lake.LeanExeConfig ZhDoc.BuildTools.Config.LeanExeConfig}

### 外部库
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets--External-Libraries"
%%%

由于外部库可以用任意语言编写并需要任意构建步骤，它们被定义为在 {name Lake.FetchM}`FetchM` 单子中编写、生成 {name Lake.Job}`Job` 的程序。
外部库目标应生成一个执行构建并返回所得静态库位置的构建作业。
要使外部库在启用 {name Lake.PackageConfig.precompileModules}`precompileModules` 时正确链接，{keyword}`extern_lib` 目标生成的静态库必须遵循平台的库命名约定（即在 Windows 上命名为 foo.a，在类 Unix 系统上命名为 libfoo.a）。
实用函数 {name}`Lake.nameToStaticLib` 将库名称转换为适合当前平台的文件名。

:::syntax command (title := "外部库目标")

```grammar
$[$_:docComment]?
$[$_:attributes]?
extern_lib $_:identOrStr $_? := $_:term
$[where $_*]?
```

{zhincludeDocstring Lake.DSL.externLibCommand ZhDoc.BuildTools.Config.DSL.externLibCommand}

:::

### 自定义目标
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets--Custom-Targets"
%%%

可以使用 Lake API，以自定义目标定义任意增量构建的产物。

:::syntax command (title := "自定义目标")

```grammar
$[$_:docComment]?
$[$_:attributes]?
target $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{zhincludeDocstring Lake.DSL.externLibCommand ZhDoc.BuildTools.Config.DSL.externLibCommand}

:::

### 自定义分面
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Targets--Custom-Facets"
%%%

自定义分面允许从模块、库或包增量构建额外产物。


:::syntax command (title := "自定义包分面")

包分面允许从整个包生成一个或一组产物。
Lake API 可查询包中的库；因此，包分面的一个常见用途是构建每个库的指定分面。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{zhincludeDocstring Lake.DSL.packageFacetDecl ZhDoc.BuildTools.Config.DSL.packageFacetDecl}

:::

:::syntax command (title := "自定义库分面")

库分面允许从库生成一个或一组产物。
Lake API 可查询库中的模块；因此，库分面的一个常见用途是构建每个模块的指定分面。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
library_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{zhincludeDocstring Lake.DSL.libraryFacetDecl ZhDoc.BuildTools.Config.DSL.libraryFacetDecl}

:::

:::syntax command (title := "自定义模块分面")

模块分面允许从模块生成一个或一组产物，通常通过调用命令行工具来完成。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
module_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{zhincludeDocstring Lake.DSL.moduleFacetDecl ZhDoc.BuildTools.Config.DSL.moduleFacetDecl}

:::

## 配置值类型
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Configuration-Value-Types"
%%%

{zhdocstring Lake.BuildType ZhDoc.BuildTools.Config.BuildType}

在 Lake 的 DSL 中，{deftech (key := "globs")}[通配模式]是匹配模块名称集合的模式。
名称可以强制转换为匹配该名称的通配模式，另有两个后缀运算符用于构造更多通配模式。

```lean -show
section
example : Lake.Glob := `n

/-- info: instCoeNameGlob -/
#check_msgs in
#synth Coe Lean.Name Lake.Glob

open Lake DSL

/-- info: Lake.Glob.andSubmodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.*

/-- info: Lake.Glob.submodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.+

end
```
:::freeSyntax term (title := "通配模式语法")

通配模式 `N.*` 匹配 `N`，或以 `N` 为前缀的任意子模块。

```grammar
$_:name".*"
```

通配模式 `N.+` 匹配严格以 `N` 为前缀的任意子模块，但不匹配 `N` 本身。

```grammar
$_:name".+"
```

名称与 `.*` 或 `.+` 之间不允许有空白。

:::

{zhdocstring Lake.Glob ZhDoc.BuildTools.Config.Glob}



{zhdocstring Lake.LeanOption ZhDoc.BuildTools.Config.LeanOption}

{zhdocstring Lake.Backend ZhDoc.BuildTools.Config.Backend}

## 脚本
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Scripts"
%%%

Lake 脚本用于自动化需要访问包配置、但不参与从代码增量构建产物的任务。
脚本在 {name Lake.ScriptM}`ScriptM` 单子中运行；它是在 {name}`IO` 上叠加一个提供包配置访问能力的{tech (key := "reader monad")}[读取器单子]{tech (key := "monad transformer")}[变换器]。
具体而言，脚本应具有类型 {lean}`List String → ScriptM UInt32`。
脚本主要通过 {inst}`MonadWorkspace ScriptM` 实例访问工作区信息。


```lean -show
example : ScriptFn = (List String → ScriptM UInt32) := rfl
```

:::syntax command (title := "脚本声明")
```grammar
$[$_:docComment]?
$[@[$_,*]]?
script $_:identOrStr $_? :=
  $_:term
$[where
  $_*]?
```

{zhincludeDocstring Lake.DSL.scriptDecl ZhDoc.BuildTools.Config.DSL.scriptDecl}

:::

{zhdocstring Lake.ScriptM ZhDoc.BuildTools.Config.ScriptM}


:::syntax attr (label := "属性") (title := "默认脚本")
```grammar
default_script
```

将{tech (key := "Lake script")}[Lake 脚本]标记为{tech (key := "package")}[包]的默认脚本。

:::



## 实用工具
%%%
tag := "The-Lean-Language-Reference--Build-Tools-and-Distribution--Lake--Configuration-File-Format--Lean-Format--Utilities"
%%%

:::syntax term (title := "当前目录")
```grammar
__dir__
```

{zhincludeDocstring Lake.DSL.dirConst ZhDoc.BuildTools.Config.DSL.dirConst}

:::

:::syntax term (title := "配置选项")
```grammar
get_config? $t
```

{zhincludeDocstring Lake.DSL.getConfig ZhDoc.BuildTools.Config.DSL.getConfig}

:::

:::syntax command (title := "编译时条件")

```grammar
meta if $_ then
  $_
$[else $_]?
```

{zhincludeDocstring Lake.DSL.metaIf ZhDoc.BuildTools.Config.DSL.metaIf}

:::

:::syntax cmdDo (title := "命令序列")

```grammar
  $_:command
```

```grammar
do
  $_:command
  $[$_:command]*
```

{zhincludeDocstring Lake.DSL.cmdDo ZhDoc.BuildTools.Config.DSL.cmdDo}

:::

:::syntax term (title := "编译时副作用")
```grammar
run_io $t
```

{zhincludeDocstring Lake.DSL.runIO ZhDoc.BuildTools.Config.DSL.runIO}

:::
