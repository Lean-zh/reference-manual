/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Mac Malone
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

#doc (Manual) "包覆盖" =>
%%%
file := "Package-Overrides"
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
  "version": "1.3.0",
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
  "version": "1.3.0",
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
