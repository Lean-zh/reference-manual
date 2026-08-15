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

#doc (Manual) "优先级" =>
%%%
tag := "precedence"
%%%

中缀运算符、记法以及 Lean 的其他语法扩展都会使用显式的 {tech (key := "precedence")}[优先级] 标注。
虽然 Lean 中的优先级在技术上可以是任意自然数，但按照约定，它们的范围从 {evalPrec}`min` 到 {evalPrec}`max`，分别记作 `min` 和 `max`。{TODO}[修复 keywordOf 运算符并在这里使用它]
函数应用具有最高的优先级。

:::syntax prec -open (title := "解析器优先级")
大多数运算符优先级都由显式数字构成。
具名优先级层级表示该范围靠近最小值或最大值的两端，通常用于更复杂的语法扩展。
```grammar
$n:num
```

优先级也可以表示为其他优先级的和或差；这通常用于指定相对于某个具名优先级的优先级。
```grammar
$p + $p
```
```grammar
$p - $p
```
```grammar
($p)
```

最大优先级用于解析出现在函数位置上的项。
运算符通常不应使用这一层级，因为这会干扰用户对于“函数应用比任何其他运算符绑定得更紧”的预期；但在更复杂的语法扩展中，它可以用来表明其他构造如何与函数应用交互。
```grammar
max
```

参数优先级比最大优先级低一。
这一层级适合定义应当被当作函数参数处理的语法，例如 {keywordOf Lean.Parser.Term.fun}`fun` 或 {keywordOf Lean.Parser.Term.do}`do`。
```grammar
arg
```

引导优先级低于参数优先级，应用于不应作为函数参数出现的自定义语法，例如 {keywordOf Lean.Parser.Term.let}`let`。
```grammar
lead
```

最小优先级可用于确保某个运算符比所有其他运算符绑定得都更松。
```grammar
min
```
:::
