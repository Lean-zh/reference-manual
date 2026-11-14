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

#doc (Manual) "脚本" =>
%%%
file := "Scripts"
tag := "lake-scripts"
%%%

Lake {tech (key := "package configuration")}[包配置] 文件可包含 {deftech (key := "Lake scripts")}_Lake 脚本_，这些脚本是可从命令行执行的内嵌程序。
脚本旨在用于特定于项目、且 Lake 的其他特性尚未能很好地处理的任务。
普通的执行程序在 {name}`IO` {tech (key := "monad")}[单子] 中运行，而脚本在 {name Lake.ScriptM}`ScriptM` 中运行，后者在 {name}`IO` 的基础上扩展了有关工作区的信息。
因为它们是 Lean 定义，Lake 脚本只能在 Lean 配置格式中定义。

:::::TODO

能够导入足够多的 Lake 以完成精译后，请恢复以下内容：

````
```lean -show
section
open Lake DSL
```

:::example "Listing Dependencies"

This Lake script lists all the transitive dependencies of the root package, along with their Git URLs, in alphabetical order.
Similar scripts could be used to check declared licenses, discover which dependencies have test drivers configured, or compute metrics about the transitive dependency set over time.

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
