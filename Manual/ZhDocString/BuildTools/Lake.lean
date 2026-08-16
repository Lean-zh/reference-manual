/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lake
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.BuildTools.Lake

/--
`Script` 所用的单子类型。

它是一个 `IO` 单子，并配备了有关 Lake 配置的信息。
-/
abbrev ScriptM := _root_.Lake.ScriptM

/-- 配备了（只读的）已探测 Lake 环境的单子。 -/
abbrev MonadLakeEnv (m : Type → Type u) := _root_.Lake.MonadLakeEnv m

/--
获取当前 Lake 环境。
-/
def getLakeEnv := @_root_.Lake.getLakeEnv

/-- 返回 Lake 配置中的 `LAKE_NO_CACHE`/`--no-cache`。 -/
def getNoCache := @_root_.Lake.getNoCache

/-- 返回 Lake 配置中的 `LAKE_NO_CACHE`/`--no-cache` 是否**未**设置。 -/
def getTryCache := @_root_.Lake.getTryCache

/-- 返回 Lake 环境的 `LAKE_PACKAGE_URL_MAP`。若不存在则为空。 -/
def getPkgUrlMap := @_root_.Lake.getPkgUrlMap

/-- 返回 Lake 环境的 Elan 工具链名称。若不存在则为空。 -/
def getElanToolchain := @_root_.Lake.getElanToolchain

/-- 返回 Lake 环境中探测到的 `LEAN_PATH` 值。 -/
def getEnvLeanPath := @_root_.Lake.getEnvLeanPath

/-- 返回 Lake 环境中探测到的 `LEAN_SRC_PATH` 值。 -/
def getEnvLeanSrcPath := @_root_.Lake.getEnvLeanSrcPath

/-- 返回 Lake 环境中探测到的 `sharedLibPathEnvVar` 值。 -/
def getEnvSharedLibPath := @_root_.Lake.getEnvSharedLibPath

/-- 返回探测到的 Elan 安装（若存在）。 -/
def getElanInstall? := @_root_.Lake.getElanInstall?

/-- 返回探测到的 Elan 安装的根目录（即 `ELAN_HOME`）。 -/
def getElanHome? := @_root_.Lake.getElanHome?

/-- 返回探测到的 Elan 安装中 `elan` 二进制文件的路径。 -/
def getElan? := @_root_.Lake.getElan?

/-- 返回探测到的 Lean 安装。 -/
def getLeanInstall := @_root_.Lake.getLeanInstall

/-- 返回探测到的 Lean 安装的根目录。 -/
def getLeanSysroot := @_root_.Lake.getLeanSysroot

/-- 返回探测到的 Lean 安装的 Lean 源码目录。 -/
def getLeanSrcDir := @_root_.Lake.getLeanSrcDir

/-- 返回探测到的 Lean 安装的 Lean 库目录。 -/
def getLeanLibDir := @_root_.Lake.getLeanLibDir

/-- 返回探测到的 Lean 安装的 C 头文件目录。 -/
def getLeanIncludeDir := @_root_.Lake.getLeanIncludeDir

/-- 返回探测到的 Lean 安装的系统库目录。 -/
def getLeanSystemLibDir := @_root_.Lake.getLeanSystemLibDir

/-- 返回探测到的 Lean 安装中 `lean` 二进制文件的路径。 -/
def getLean := @_root_.Lake.getLean

/-- 返回探测到的 Lean 安装中 `leanc` 二进制文件的路径。 -/
def getLeanc := @_root_.Lake.getLeanc

/--
返回探测到的 Lean 安装中主核心共享库
（即 `libleanshared`）的路径。
-/
def getLeanSharedLib := @_root_.Lake.getLeanSharedLib

/-- 返回探测到的 Lean 安装中 `ar` 二进制文件的路径。 -/
def getLeanAr := @_root_.Lake.getLeanAr

/-- 返回探测到的 Lean 安装中 C 编译器的路径。 -/
def getLeanCc := @_root_.Lake.getLeanCc

/-- 返回探测到的 Lean 安装中可选的 `LEAN_CC` 编译器覆盖值。 -/
def getLeanCc? := @_root_.Lake.getLeanCc?

/-- 返回探测到的 Lake 安装。 -/
def getLakeInstall := @_root_.Lake.getLakeInstall

/-- 返回探测到的 Lake 安装的根目录（例如 `LAKE_HOME`）。 -/
def getLakeHome := @_root_.Lake.getLakeHome

/-- 返回探测到的 Lake 安装的源码目录。 -/
def getLakeSrcDir := @_root_.Lake.getLakeSrcDir

/-- 返回探测到的 Lake 安装的 Lean 库目录。 -/
def getLakeLibDir := @_root_.Lake.getLakeLibDir

/-- 返回探测到的 Lake 安装中 `lake` 二进制文件的路径。 -/
def getLake := @_root_.Lake.getLake

/-- 配备了（只读的）Lake `Workspace` 的单子。 -/
class MonadWorkspace (m : Type → Type u) where
  /-- 获取当前 Lake 工作区。 -/
  getWorkspace : m _root_.Lake.Workspace

/-- 返回上下文工作区的根包。 -/
def getRootPackage := @_root_.Lake.getRootPackage

/--
返回工作区中首个（若存在）被赋予 `name` 的包。

这可用于查找与用户提供的名称对应的包。如果已经有该包的唯一标识符，请改用
`findPackageByKey?`。
-/
def findPackageByName? := @_root_.Lake.findPackageByName?

/-- 返回工作区中由 `keyName` 标识的唯一包（若存在）。 -/
def findPackageByKey? := @_root_.Lake.findPackageByKey?

/-- 在工作区中定位具有给定名称、可构建、可导入且位于本地的模块。 -/
def findModule? := @_root_.Lake.findModule?

/-- 尝试在工作区中查找具有给定名称的 Lean 可执行文件。 -/
def findLeanExe? := @_root_.Lake.findLeanExe?

/-- 尝试在工作区中查找具有给定名称的 Lean 库。 -/
def findLeanLib? := @_root_.Lake.findLeanLib?

/-- 尝试在工作区中查找具有给定名称的外部库。 -/
def findExternLib? := @_root_.Lake.findExternLib?

/-- 返回上下文工作区添加到 `LEAN_PATH` 的路径。 -/
def getLeanPath := @_root_.Lake.getLeanPath

/-- 返回上下文工作区添加到 `LEAN_SRC_PATH` 的路径。 -/
def getLeanSrcPath := @_root_.Lake.getLeanSrcPath

/-- 返回上下文工作区添加到共享库路径的路径。 -/
def getSharedLibPath := @_root_.Lake.getSharedLibPath

/-- 返回上下文工作区设置的扩充后 `LEAN_PATH`。 -/
def getAugmentedLeanPath := @_root_.Lake.getAugmentedLeanPath

/-- 返回上下文工作区设置的扩充后 `LEAN_SRC_PATH`。 -/
def getAugmentedLeanSrcPath := @_root_.Lake.getAugmentedLeanSrcPath

/-- 返回上下文工作区设置的扩充后共享库路径。 -/
def getAugmentedSharedLibPath := @_root_.Lake.getAugmentedSharedLibPath

/-- 返回上下文工作区设置的扩充后环境变量。 -/
def getAugmentedEnv := @_root_.Lake.getAugmentedEnv

end ZhDoc.BuildTools.Lake
