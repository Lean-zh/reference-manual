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

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "脚本接口参考" =>
%%%
file := "Script-API-Reference"
tag := "lake-api"
%%%

除了普通的 {lean}`IO` 效应，Lake 脚本还能访问 Lake 环境（它提供了有关当前工具链的信息，例如 Lean 编译器的位置）以及当前的工作区。
这一访问权限是在 {name Lake.ScriptM}`ScriptM` 中提供的。

{zhdocstring Lake.ScriptM ZhDoc.BuildTools.Lake.ScriptM}

# 访问环境
%%%
file := "Accessing-the-Environment"
%%%

提供对当前 Lake 环境信息（例如 Lean、Lake 以及其它工具的位置）访问权限的单子具备 {name Lake.MonadLakeEnv}`MonadLakeEnv` 实例。
Lake 接口中的所有单子皆是如此，包括 {name Lake.ScriptM}`ScriptM`。

{zhdocstring Lake.MonadLakeEnv ZhDoc.BuildTools.Lake.MonadLakeEnv}

{zhdocstring Lake.getLakeEnv ZhDoc.BuildTools.Lake.getLakeEnv}

{zhdocstring Lake.getNoCache ZhDoc.BuildTools.Lake.getNoCache}

{zhdocstring Lake.getTryCache ZhDoc.BuildTools.Lake.getTryCache}

{zhdocstring Lake.getPkgUrlMap ZhDoc.BuildTools.Lake.getPkgUrlMap}

{zhdocstring Lake.getElanToolchain ZhDoc.BuildTools.Lake.getElanToolchain}

## 搜索路径辅助函数
%%%
file := "Search-Path-Helpers"
%%%

{zhdocstring Lake.getEnvLeanPath ZhDoc.BuildTools.Lake.getEnvLeanPath}

{zhdocstring Lake.getEnvLeanSrcPath ZhDoc.BuildTools.Lake.getEnvLeanSrcPath}

{zhdocstring Lake.getEnvSharedLibPath ZhDoc.BuildTools.Lake.getEnvSharedLibPath}

## Elan 安装辅助函数
%%%
file := "Elan-Install-Helpers"
%%%

{zhdocstring Lake.getElanInstall? ZhDoc.BuildTools.Lake.getElanInstall?}

{zhdocstring Lake.getElanHome? ZhDoc.BuildTools.Lake.getElanHome?}

{zhdocstring Lake.getElan? ZhDoc.BuildTools.Lake.getElan?}

## Lean 安装辅助函数
%%%
file := "Lean-Install-Helpers"
%%%

{zhdocstring Lake.getLeanInstall ZhDoc.BuildTools.Lake.getLeanInstall}

{zhdocstring Lake.getLeanSysroot ZhDoc.BuildTools.Lake.getLeanSysroot}

{zhdocstring Lake.getLeanSrcDir ZhDoc.BuildTools.Lake.getLeanSrcDir}

{zhdocstring Lake.getLeanLibDir ZhDoc.BuildTools.Lake.getLeanLibDir}

{zhdocstring Lake.getLeanIncludeDir ZhDoc.BuildTools.Lake.getLeanIncludeDir}

{zhdocstring Lake.getLeanSystemLibDir ZhDoc.BuildTools.Lake.getLeanSystemLibDir}

{zhdocstring Lake.getLean ZhDoc.BuildTools.Lake.getLean}

{zhdocstring Lake.getLeanc ZhDoc.BuildTools.Lake.getLeanc}

{zhdocstring Lake.getLeanSharedLib ZhDoc.BuildTools.Lake.getLeanSharedLib}

{zhdocstring Lake.getLeanAr ZhDoc.BuildTools.Lake.getLeanAr}

{zhdocstring Lake.getLeanCc ZhDoc.BuildTools.Lake.getLeanCc}

{zhdocstring Lake.getLeanCc? ZhDoc.BuildTools.Lake.getLeanCc?}

## Lake 安装辅助函数
%%%
file := "Lake-Install-Helpers"
%%%

{zhdocstring Lake.getLakeInstall ZhDoc.BuildTools.Lake.getLakeInstall}

{zhdocstring Lake.getLakeHome ZhDoc.BuildTools.Lake.getLakeHome}

{zhdocstring Lake.getLakeSrcDir ZhDoc.BuildTools.Lake.getLakeSrcDir}

{zhdocstring Lake.getLakeLibDir ZhDoc.BuildTools.Lake.getLakeLibDir}

{zhdocstring Lake.getLake ZhDoc.BuildTools.Lake.getLake}

# 访问工作区
%%%
file := "Accessing-the-Workspace"
%%%

提供对当前 Lake 工作区信息访问权限的单子具备 {name Lake.MonadWorkspace}`MonadWorkspace` 实例。
特别是，有针对 {name Lake.ScriptM}`ScriptM` 和 {name Lake.LakeM}`LakeM` 的实例。

```lean -show
section
open Lake
#synth MonadWorkspace ScriptM

end
```

{zhdocstring Lake.MonadWorkspace ZhDoc.BuildTools.Lake.MonadWorkspace}

{zhdocstring Lake.getRootPackage ZhDoc.BuildTools.Lake.getRootPackage}

{zhdocstring Lake.findPackageByName? ZhDoc.BuildTools.Lake.findPackageByName?}

{zhdocstring Lake.findPackageByKey? ZhDoc.BuildTools.Lake.findPackageByKey?}

{zhdocstring Lake.findModule? ZhDoc.BuildTools.Lake.findModule?}

{zhdocstring Lake.findLeanExe? ZhDoc.BuildTools.Lake.findLeanExe?}

{zhdocstring Lake.findLeanLib? ZhDoc.BuildTools.Lake.findLeanLib?}

{zhdocstring Lake.findExternLib? ZhDoc.BuildTools.Lake.findExternLib?}

{zhdocstring Lake.getLeanPath ZhDoc.BuildTools.Lake.getLeanPath}

{zhdocstring Lake.getLeanSrcPath ZhDoc.BuildTools.Lake.getLeanSrcPath}

{zhdocstring Lake.getSharedLibPath ZhDoc.BuildTools.Lake.getSharedLibPath}

{zhdocstring Lake.getAugmentedLeanPath ZhDoc.BuildTools.Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath }

{zhdocstring Lake.getAugmentedSharedLibPath ZhDoc.BuildTools.Lake.getAugmentedSharedLibPath}

{zhdocstring Lake.getAugmentedEnv ZhDoc.BuildTools.Lake.getAugmentedEnv}
