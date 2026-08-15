/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "API 参考" =>

除了这里介绍的通用函数之外，按照惯例，每种集合类型的命名空间中还会定义一些函数，作为其 API 的一部分：
 * `mapM` 映射一个单子函数。
 * `forM` 映射一个单子函数并丢弃结果。
 * `filterM` 使用单子谓词进行筛选，返回满足该谓词的值。


::::example "单子式集合操作"
{name}`Array.filterM` 可用于编写依赖副作用的筛选器。

:::ioExample
```ioLean
def values := #[1, 2, 3, 5, 8]
def main : IO Unit := do
  let filtered ← values.filterM fun v => do
    repeat
      IO.println s!"Keep {v}? [y/n]"
      let answer := (← (← IO.getStdin).getLine).trimAscii.copy
      if answer == "y" then return true
      if answer == "n" then return false
    return false
  IO.println "These values were kept:"
  for v in filtered do
    IO.println s!" * {v}"
```
```stdin
y
n
oops
y
n
y
```
```stdout
Keep 1? [y/n]
Keep 2? [y/n]
Keep 3? [y/n]
Keep 3? [y/n]
Keep 5? [y/n]
Keep 8? [y/n]
These values were kept:
 * 1
 * 3
 * 8
```
:::
::::

# 丢弃结果

当使用某个仅为副作用而返回值的动作时，函数 {name}`discard` 尤其有用。

{docstring discard}

# 控制流

{docstring guard}

{docstring optional}

# 提升布尔操作

{docstring andM}

{docstring orM}

{docstring notM}

# 克莱斯利复合

{deftech (key := "Kleisli composition")}_克莱斯利复合_是单子函数的复合，类似于普通函数所用的 {name}`Function.comp`。

{docstring Bind.kleisliRight}

{docstring Bind.kleisliLeft}

# 重排实参的操作

有时，对函数的第二个实参进行部分应用会更方便。
以下函数反转实参顺序，使这一做法更容易。

{docstring Functor.mapRev}

{docstring Bind.bindLeft}
