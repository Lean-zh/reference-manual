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

#doc (Manual) "构建缓存" =>
%%%
file := "Caching-Builds"
tag := "lake-cache"
%%%

Builds of large packages can consume significant time.
Compounding this, switching between local development branches can cause Lake to rebuild the same code many times.
To address these problems, Lake provides a number of ways to {deftech (key := "build cache")}_cache_ builds for later reuse.
Lake's {ref "lake-cache-local"}[local artifact cache] enables reuse of builds when switching between branches and across multiple local copies of the same package.
The {ref "lake-cache-remote"}[remote artifact cache] expands this to sharing artifact caches across machines. However, it requires the package developers to own cloud storage.
As an alternative for developers without cloud storage but already using GitHub, {ref "lake-github"}[release builds] provide a low-setup way to ship complete builds to users.

# 工件缓存
%%%
file := "Artifact-Caches"
tag := "lake-cache-local"
%%%

*这是一项仍在开发中的实验性功能。*

Lake supports a {deftech (key := "local cache")}_local artifact cache_ that stores individual build products, tracking the complete set of inputs that contributed to their final value.
每个 {tech (key := "toolchain")}[工具链] 都有其自己的缓存，因为工具链版本之间的中间构建产物是不兼容的。
不过，一个工具链的缓存在使用它的所有本地 {tech (key := "workspaces")}[工作区] 之间是共享的，因此常见的依赖不需要重新构建。
如果两个具有相同工具链的独立工作区依赖于相同的包，则它们可以共享彼此的构建产物。

因为这是一项实验性功能，所以本地缓存默认处于禁用状态。
It is only enabled when the {envVar}`LAKE_ARTIFACT_CACHE` environment variable is set to `true` or when the {tomlField Lake.PackageConfig}`enableArtifactCache` field is set to `true` in the {ref "lake-config"}[configuration file].


# 远程工件缓存
%%%
file := "Remote-Artifact-Caches"
tag := "lake-cache-remote"
%%%

构建产物可以从远程缓存服务器检索，并放入本地缓存中。
这使得完全避免本地构建成为可能。
{lake}`cache get` 命令用于将工件下载到本地缓存中。

与 {ref "lake-github"}[GitHub 发布版本构建] 相比，远程工件缓存的粒度要细得多。
它追踪源代码文件级别、{tech (key := ".olean files")}[`.olean` 文件] 以及目标代码级别的构建产物，而不是整个包级别的。

## 映射
%%%
file := "Mappings"
%%%

当传递 `-o` 选项时，{lake}`build` 会追踪用于生成每个构建产物的输入。
它们被存储为 JSON 行格式的 {deftech (key := "mappings file")}_映射文件_，文件中每一行都必须是一个有效的 JSON 对象。
A mappings file tracks a single package within a build, and includes all intermediate and final build products from the package that are part of the build.

By default, {lake}`build` saves the workspace's {tech}[root package]'s mappings.
The {lakeOpt}`--package` option selects a different package in the workspace, such as a dependency, saving its mappings instead.
The tracked build products include those that were already up to date and not regenerated, but not the package's targets that the build did not cover.
The {lake}`cache put` command uploads the build products in the mappings file from the local cache to the remote cache.

## 配置
%%%
file := "Configuration"
%%%

:::paragraph
使用以下环境变量配置远程工件缓存：
 * {envVar}`LAKE_CACHE_KEY`
 * {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`
 * {envVar}`LAKE_CACHE_REVISION_ENDPOINT`
:::

# GitHub 发布版本构建
%%%
file := "GitHub-Release-Builds"
tag := "lake-github"
%%%

Lake supports uploading and downloading the complete set of build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages.
这使得最终用户能够从云端获取预构建的工件，而无需自己从源码重建整个包。
可以使用 {envVar}`LAKE_NO_CACHE` 环境变量来禁用此功能。

## 下载
%%%
file := "Downloading"
%%%

要下载工件，应配置包选项 `releaseRepo` 和 `buildArchive`，使其指向托管发布版本的 GitHub 仓库以及其中正确的工件名称（如果默认设置不充分）。
然后，设置 `preferReleaseBuild := true`，指示 Lake 将其作为额外的包依赖项获取并解包。

作为标准构建过程的一部分，Lake 仅当需要发布版本构建的包属于依赖时才会获取它（因为根包通常会被修改，所以它往往与此方案不兼容）。
但是，如果希望为根包获取发布版本构建（例如，在克隆发布版本的源代码之后、编辑之前），可以通过 `lake build :release` 手动执行。

Lake 在内部使用 `curl` 下载发布版本，并使用 `tar` 将其解包，因此最终用户必须安装这两种工具才能使用此功能。
如果 Lake 因任何原因未能获取发布版本，它将继续从源代码构建。
该机制在技术上不仅限于 GitHub：任何使用相同 URL 方案的 Git 托管平台同样适用。

## 上传
%%%
file := "Uploading"
%%%

要将构建的包作为工件上传到 GitHub 发布版本，Lake 提供了 {lake}`upload` 命令作为便捷的简写。
此命令使用 `tar` 将包的构建目录打包为归档，并使用 `gh release upload` 将其附加到指定标签下预先存在的 GitHub 发布版本中。
因此，为了使用该命令，包的上传者（但不是下载者）需要安装 GitHub 命令行界面 `gh` 并将其包含在 `PATH` 中。
