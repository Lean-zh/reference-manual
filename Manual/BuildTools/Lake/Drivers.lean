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

#doc (Manual) "测试和代码检查驱动程序" =>
%%%
file := "Test-and-Lint-Drivers"
tag := "test-lint-drivers"
%%%

{deftech (key := "test driver")}_测试驱动程序_ 负责运行一个包的测试。
它可以是可执行目标、{tech (key := "Lake script")}[Lake 脚本] 或库。
Lake 本身并不是测试框架：{lake}`test` 命令只是定位已配置的目标，构建它，并且（针对可执行文件和脚本）运行它。
库的驱动程序纯粹通过精译来执行，因此它们不会作为单独的步骤运行。
断言、测试发现以及报告都由目标本身决定，这既可以是第三方测试库，也可以是手写的检查。

对于可执行文件和脚本，Lake 将非零退出代码视为测试失败。
对于库，任何精译错误均算作测试失败，包括 {keyword}`#guard` 风格命令的失败。

{deftech (key := "lint driver")}_代码检查驱动程序_ 也是类似的，只是它由 {lake}`lint` 运行，负责检查包在风格及其他方面是否存在不是_错误_但预示存在潜在问题的状况。
代码检查驱动程序只能是可执行文件或脚本，而不能是库。

# 配置测试驱动程序
%%%
file := "Configuring-a-Test-Driver"
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
          precompileImports := false,
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
      checks := #[],
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
                    precompileImports := false,
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
                          precompileImports := false,
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
          precompileImports := false,
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
      checks := #[],
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
                    precompileImports := false,
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
                          precompileImports := false,
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

# 运行测试
%%%
file := "Running-Tests"
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
要运行测试，只需使用 {tech (key:="Lean elaborator")}[Lean 精译器] 对该库进行精译即可。

如果为根包配置了测试驱动程序，{lake}`check-test` 将以退出代码 0（即成功）终止。
它不检查所命名的目标是否实际存在。

# 代码检查驱动程序
%%%
file := "Lint-Drivers"
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
          precompileImports := false,
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
      checks := #[],
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
                    precompileImports := false,
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
                          precompileImports := false,
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
属性标记的形式往往更方便，因为它将标记放在了目标旁边。

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
          precompileImports := false,
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
      checks := #[],
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
                    precompileImports := false,
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
                          precompileImports := false,
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

Lake 还提供单独的{deftech (key := "builtin linter")}_内置检查器_，直接在 Lean 模块上运行 Lean {ref "kinds-of-linters"}[自身的检查器]，不依赖任何已配置的驱动程序。
内置代码检查可以通过 `--builtin-lint` 及相关标志（见 {lake}`lint`）启用，或通过在包配置中将 {tomlField Lake.PackageConfig}`builtinLint` 设置为 `true` 来启用。
{ref "running-lake-lint"}[运行 `lake lint`] 一节介绍了如何选择要运行的检查器。
当内置代码检查启用时，`--` 之前的位置参数 `MODULE` 用于选择要检查的模块，而且它们*不会*被传递给已配置的驱动程序。
因此 `lake lint Mathlib` 会触发对 `Mathlib` 的内置代码检查，而 `lake lint -- Mathlib` 则会将 `Mathlib` 传递给驱动程序。
这两种机制相互独立且可同时运行：当它们同时适用时，Lake 将先运行内置检查器，然后再运行驱动程序。

如果为根包配置了代码检查驱动程序，或者其配置中的 {tomlField Lake.PackageConfig}`builtinLint` 被设置为 `true`，{lake}`check-lint` 将以退出代码 0（即成功）退出。
