/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "语法" =>
%%%
tag := "string-syntax"
%%%

Lean 有三类字符串字面量：普通字符串字面量、插值字符串字面量和原始字符串字面量。

# 字符串字面量
%%%
tag := "string-literals"
%%%

字符串字面量以双引号字符 `"` 开始并结束。{index (subterm := "string")}[literal]
在这两个字符之间，可以包含任意其他字符，包括换行；这些字符都会按字面纳入字符串（但要注意，不论文件编码和平台如何，Lean 源文件中的所有换行都会被解释为 `'\n'`）。
无法直接写入字符串字面量的特殊字符可以用反斜杠转义，因此 `"\"Quotes\""` 是一个以双引号开头并以双引号结尾的字符串字面量。
可接受的转义序列形式如下：

: `\r`, `\n`, `\t`, `\\`, `\"`, `\'`

  这些转义序列具有通常的含义，分别对应 `CR`、`LF`、制表符、反斜杠、双引号和单引号。

: `\xNN`

  当 `NN` 是由两个十六进制数字组成的序列时，该转义表示 Unicode 码点由这两个十六进制数字给出的字符。

: `\uNNNN`

  当 `NN` 是由四个十六进制数字组成的序列时，该转义表示 Unicode 码点由这四个十六进制数字给出的字符。


字符串字面量可以包含 {deftech (key := "gaps")}_间隙_。
间隙由一个被转义的换行表示，也就是转义用的反斜杠与换行之间不能有其他字符。
在这种情况下，字面量所表示的字符串会省去该换行以及下一行开头的全部空白。
字符串间隙后面不能跟只含空白字符的行。

这里，`str1` 与 `str2` 是同一个字符串：
```lean
def str1 := "String with \
             a gap"
def str2 := "String with a gap"

example : str1 = str2 := rfl
```

如果间隙后紧跟的那一行为空，则该字符串会被拒绝：

```syntaxError foo
def str3 := "String with \

             a gap"
```
解析器错误为：
```leanOutput foo
<example>:2:0-3:0: unexpected additional newline in string gap
```

# 插值字符串
%%%
tag := "string-interpolation"
%%%

在字符串字面量前加上 `s!`，会使其被处理为 {deftech (key := "interpolated string")}_插值字符串_：字符串中由 `{` 与 `}` 包围的部分会被解析并解释为 Lean 表达式。
插值字符串会被解释为：将插值前的字符串、该表达式（外围额外加上一层 {name ToString.toString}`toString` 调用）以及插值后的字符串依次拼接。

例如：
```lean
example :
    s!"1 + 1 = {1 + 1}\n" =
    "1 + 1 = " ++ toString (1 + 1) ++ "\n" :=
  rfl
```

在字面量前加上 `m!`，会使插值结果成为 {name Lean.MessageData}`MessageData` 的一个实例；这是编译器内部用于向用户显示消息的数据结构。

# 原始字符串字面量
%%%
tag := "raw-string-literals"
%%%

在 {deftech (key := "raw string literals")}[原始字符串字面量] 中，{index (subterm := "raw string")}[literal] 没有转义序列，也没有间隙，每个字符都严格按其自身含义解释。
原始字符串字面量以 `r` 开头，后跟零个或多个井号字符（`#`）以及一个双引号 `"`。
当遇到一个后面紧跟着_相同数量_井号字符的双引号时，该字符串字面量结束。
例如，它们可用于避免某些字符需要双重转义：
```lean (name := evalStr)
example : r"\t" = "\\t" := rfl
#eval r"Write backslash in a string using '\\\\'"
```
该 `#eval` 的结果为：
```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```

加入井号后，字符串中就可以包含无需转义的引号：

```lean
example :
    r#"This is "literally" quoted"# =
    "This is \"literally\" quoted" :=
  rfl
```

只要添加足够多的井号，任何原始字面量都可以被按字面写出：

```lean
example :
    r##"This is r#"literally"# quoted"## =
    "This is r#\"literally\"# quoted" :=
  rfl
```
