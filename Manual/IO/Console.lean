/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command
import Manual.ZhDocString.IO

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "控制台输出" =>
%%%
tag := "Lean-__________________--IO--Console-Output"
file := "Console-Output"
%%%

Lean 提供了向{tech (key := "standard output")}[标准输出]和{tech (key := "standard error")}[标准错误]写入内容的便捷函数。
这些函数都使用 {lean}`ToString` 实例；名称以 `-ln` 结尾的变体会在输出后添加换行符。
这些便捷函数只暴露了{ref "stdio"}[标准 I/O 流]所提供的一部分功能。
特别是，要从标准输入读取一行，应组合使用 {lean}`IO.getStdin` 与 {lean}`IO.FS.Stream.getLine`。

{zhdocstring IO.print Manual.ZhDocString.IO.c056}

{zhdocstring IO.println Manual.ZhDocString.IO.c057}

{zhdocstring IO.eprint Manual.ZhDocString.IO.c058}

{zhdocstring IO.eprintln Manual.ZhDocString.IO.c059}

::::example "打印" (file := "Printing")
该程序演示了全部四个控制台 I/O 便捷函数。

:::ioExample
```ioLean
def main : IO Unit := do
  IO.print "This is the "
  IO.print "Lean"
  IO.println " language reference."
  IO.println "Thank you for reading it!"
  IO.eprint "Please report any "
  IO.eprint "errors"
  IO.eprintln " so they can be corrected."
```

它向标准输出写入以下内容：

```stdout
This is the Lean language reference.
Thank you for reading it!
```

并向标准错误写入以下内容：

```stderr
Please report any errors so they can be corrected.
```
:::
::::
