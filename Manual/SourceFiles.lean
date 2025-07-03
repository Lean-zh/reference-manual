/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-
#doc (Manual) "Source Files and Modules" =>
%%%
tag := "files"
htmlSplit := .never
%%%
-/

#doc (Manual) "源文件与模块" =>
%%%
file := "Source Files and Modules"
tag := "files"
htmlSplit := .never
%%%

/-
The smallest unit of compilation in Lean is a single {deftech}[module].
Modules correspond to source files, and are imported into other modules based on their filenames.
In other words, the names and folder structures of files are significant in Lean code.
-/

在 Lean 中，编译的最小单位是单个 {deftech key := "module"}[模块]。
模块对应于源代码文件，并且可以按文件名被其他模块导入。
换句话说，文件的名称和文件夹结构在 Lean 代码中具有重要意义。

/-
Every Lean file defines a module.
A module's name is derived from a combination of its filename and the way in which Lean was invoked: Lean has a _root directory_ in which it expects to find code, and the module's name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` would contain a module named `Literature.Novel.SciFi`.
-/

每个 Lean 文件都定义一个模块。
模块名称由其文件名以及 Lean 启动时的方式共同决定：Lean 有一个_根目录_，它期望在该根目录下找到代码，模块的名称则是从根目录到文件名各级目录的名称，用点（.）隔开，并去掉 `.lean` 后缀。
举例来说，如果 Lean 以 `Projects/MyLib/src` 作为根目录启动，那么文件 `Projects/MyLib/src/Literature/Novel/SciFi.lean` 中包含的模块名称就是 `Literature.Novel.SciFi`。

::: TODO
Describe case sensitivity/preservation for filenames here
:::

/-
# Encoding and Representation
%%%
tag := "module-encoding"
%%%
-/

# 编码与表示
%%%
tag := "module-encoding"
%%%

/-
Lean modules are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
-/

Lean 模块是采用 UTF-8 编码的 Unicode 文本文件。{TODO}[确认 BOM 与 Lean 的支持情况]
文件的每一行可以以换行字符（`\n`，Unicode `'LINE FEED (LF)' (U+000A)`）结尾，也可以以回车加换行序列（`\r\n`，即 Unicode `'CARRIAGE RETURN (CR)' (U+000D)` 加 `'LINE FEED (LF)' (U+000A)`）结尾。
不过，在解析或比较文件时，Lean 会对行尾进行归一化，因此所有文件在比较时都视为全部是 `\n` 行尾。

::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

/-
# Concrete Syntax
%%%
tag := "module-syntax"
%%%
-/

# 具体语法
%%%
tag := "module-syntax"
%%%

/-
Lean's concrete syntax is {ref "language-extension"}[extensible].
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or {tech}[inductive types].
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.
-/

Lean 的具体语法是 {ref "language-extension"}[可扩展的]。
在 Lean 这样的语言中，无法一次性完整地描述所有语法，因为库中还可以定义新的语法、常量，或者 {tech key := "inductive type"}[归纳类型]。
本节不会详尽描述整个语言，而是介绍整体框架；各个语言结构的具体语法则在其各自章节中详细说明。

/-
## Whitespace
%%%
tag := "whitespace"
%%%
-/

## 空白符
%%%
tag := "whitespace"
%%%

/-
Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.
-/

Lean 中的词法单元（token）之间可以用任意数量的 {deftech key := "whitespace"}[_空白符_] 字符序列分隔。
空白符可以是空格 (`" "`, Unicode `'SPACE (SP)' (U+0020)`)、合法的换行序列，或注释。{TODO}[交叉引用补充]
制表符和单独的回车（CR，未跟随换行）不是合法的空白符序列。

/-
## Comments
%%%
tag := "comments"
%%%
-/

## 注释
%%%
tag := "comments"
%%%

-- 以下原文不要使用/--/ 注释，否则会报错
-- Comments are stretches of the file that, despite not being whitespace, are treated as such.
-- Lean has two syntaxes for comments:

-- : Line comments

--   A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]

-- : Block comments

--   A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment]
--   The block comment continues until a terminating `-/` is found.
--   Block comments may be nested; a `-/` only terminates the comment if prior nested block comment openers `/-` have been terminated by a matching `-/`.


注释是文件中虽然不是空白符，但被视为空白的部分。
Lean 提供两种注释语法：

: 行注释

  当 `--` 不作为其他词法单元一部分出现时，表示行注释。该标记后的所有内容直到行尾都会被视为空白字符。{index (subterm := "line")}[comment]

: 块注释

  当 `/-` 不作为其他词法单元一部分，且后面不是 `-` 字符时，表示块注释的开始。{index (subterm := "block")}[comment]
  块注释会一直持续到出现 `-/` 终止为止。
  块注释允许嵌套；仅在所有内部嵌套的 `/-` 都被匹配的 `-/` 终止后，最外层才算结束。

-- 以下原文不要使用/--/ 注释，否则会报错
-- `/--` and `/-!` begin {deftech}_documentation_ {TODO}[xref] rather than comments, which are also terminated with `-/` and may contain nested block comments.
-- Even though documentation resembles comments, they are their own syntactic category; their valid placement is determined by Lean's grammar.


`/--` 与 `/-!` 用于开始 {deftech key := "documentation"}_文档注释_ {TODO}[交叉引用]，它们同样以 `-/` 结束，并允许嵌套块注释。
尽管文档注释看起来与普通注释类似，但在语法上它们属于不同类别；它们能出现的位置由 Lean 的语法决定。

/-
## Keywords and Identifiers
%%%
tag := "keywords-and-identifiers"
%%%
-/

## 关键字与标识符
%%%
tag := "keywords-and-identifiers"
%%%

/-
An {tech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]
-/

一个 {tech key := "identifier"}[标识符] 由一个或多个标识符成分（component）组成，各部分用 `'.'` 分隔。{index}[identifier]

/-
{deftech}[Identifier components] consist of a letter or letter-like character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letter-like characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, as well as the members of the Unicode letter-like symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations.
Identifier continuation characters consist of letters, letter-like characters, underscores (`'_'`), exclamation marks (`!`), question marks (`?`), subscripts, and single quotes (`'`).
As an exception, underscore alone is not a valid identifier.
-/

{deftech key := "identifier component"}[标识符成分] 由一个字母或类字母字符或下划线（`'_'`）开头，后面可以跟零个或多个标识符后续字符。
字母包括英文大小写字母，而类字母字符还包含范围较广的非英语字母脚本，比如 Lean 中广泛采用的希腊字母、以及 Unicode 的字母符号区块（如 `ℕ`、`ℤ` 等粗体字符和缩写）。
标识符的后续字符包括字母、类字母字符、下划线（`'_'`）、感叹号（`!`）、问号（`?`）、下标和单引号（`'`）。
作为例外，单独下划线不是合法的标识符。

````lean (show := false)
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#check_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#check_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "αποδεικνύοντας"


/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"øvelse\"" -/
#check_msgs in
#eval validIdentifier "øvelse"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"Übersetzung\""
-/
#check_msgs in
#eval validIdentifier "Übersetzung"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

````
/-
Identifiers components may also be surrounded by double {deftech}[guillemets] (`'«'` and `'»'`).
Such identifier components may contain any character at all aside from `'»'`, even `'«'`, `'.'`, and newlines.
The guillemets are not part of the resulting identifier component, so `«x»` and `x` denote the same identifier.
`«Nat.add»`, on the other hand, is an identifier with a single component, while `Nat.add` has two.
-/

标识符成分也可以用一对双 {deftech key := "guillemets"}[尖引号]（`'«'` 和 `'»'`）括起来。
这样括起来的成分可以包含除 `'»'` 之外的任意字符，包括 `'«'`、`.` 和换行符。
尖引号本身不计入标识符最终内容，所以 `«x»` 和 `x` 是同一个标识符。
而 `«Nat.add»` 是一个包含一个成分的标识符，而 `Nat.add` 则包含两个成分。



```lean (show := false)
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x0Band another»"
```
/-
Some potential identifier components may be reserved keywords.
The specific set of reserved keywords depends on the set of active syntax extensions, which may depend on the set of imported modules and the currently-opened {TODO}[xref/deftech for namespace] namespaces; it is impossible to enumerate for Lean as a whole.
These keywords must also be quoted with guillemets to be used as identifier components in most syntactic contexts.
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive types, are {deftech}_raw identifier_ contexts.{index (subterm:="raw")}[identifier]
-/

可能的标识符成分中有一些属于保留关键字。
具体的保留关键字集合取决于当前激活的语法扩展集合，后者又依赖于已导入的模块以及当前打开的 {TODO}[交叉引用/定义：namespace] 命名空间；因此无法为整个 Lean 语言列举一个完整集合。
在大多数语法环境中，若要用关键字作为标识符成分，必须用尖引号括起来。
在某些环境下（如归纳类型的构造子名称）关键字无需尖引号也能作为标识符使用，这些环境称为 {deftech key := "raw identifier"}_原始标识符_ 环境。{index (subterm:="raw")}[identifier]

/-
Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both module names and names in a namespace.
-/

包含一个或多个 `'.'` 字符的标识符（因此包含多个标识符成分）被称为 {deftech key := "hierarchical identifier"}[分层标识符]。
分层标识符同时用于表示模块名称和命名空间中的名称。

/-
# Structure
%%%
tag := "module-structure"
%%%
-/

# 结构
%%%
tag := "module-structure"
%%%

/-
:::syntax Lean.Parser.Module.module (open := false) (title := "Modules")
```grammar
$hdr:header $cmd:command*
```

A module consists of a {deftech}_module header_ followed by a sequence of {deftech}_commands_.

:::
-/

:::syntax Lean.Parser.Module.module (open := false) (title := "Modules")
```grammar
$hdr:header $cmd:command*
```

一个模块由一个 {deftech key := "module header"}_模块头_，后面跟随一系列 {deftech key := "commands"}_命令_ 组成。

:::

/-
## Module Headers
%%%
tag := "module-headers"
%%%
-/

## 模块头
%%%
tag := "module-headers"
%%%

/-
Module headers list the modules that should be elaborated prior to the current module.
Their declarations are visible in the current module.
-/

模块头列出在当前模块之前需要繁释的模块。
它们的声明在当前模块中可见。

/-
:::syntax Lean.Parser.Module.header (open := false) (title := "Module Headers")
The module header consists of a sequence of {deftech}[`import` statements]:
```grammar
$i:import*
```

The optional {keyword}`prelude` keyword should only be used in Lean's source code:
```grammar
prelude
$i:import*
```
:::
-/

:::syntax Lean.Parser.Module.header (open := false) (title := "Module Headers")
模块头由一系列 {deftech key := "import"}[`import` 语句] 组成：
```grammar
$i:import*
```

可选的 {keyword}`prelude` 关键字只应在 Lean 源码中出现：
```grammar
prelude
$i:import*
```
:::

/-
If present, the {keyword}`prelude` keyword indicates that the module is part of the implementation of the Lean {deftech}_prelude_, which is the code that is available without explicitly importing any modules—it should not be used outside of Lean's implementation.
-/

如果存在 {keyword}`prelude` 关键字，则表示该模块属于 Lean {deftech key := "prelude"}_前导库_ 的实现部分，也就是无需显式导入任何模块即可用到的代码——不应在 Lean 实现之外使用。

/-
:::syntax Lean.Parser.Module.prelude (open := false) (title := "Prelude Modules")
```grammar
prelude
```

:::
-/

:::syntax Lean.Parser.Module.prelude (open := false) (title := "前导库模块")
```grammar
prelude
```

:::

/-
:::syntax Lean.Parser.Module.import (title := "Imports")
```grammar
import $mod:ident
```

Imports the module.
Importing a module makes its contents available in the current module, as well as those from modules transitively imported by its imports.

Modules do not necessarily correspond to namespaces.
Modules may add names to any namespace, and importing a module has no effect on the set of currently open namespaces.

The imported module name is translated to a filename by replacing dots (`'.'`) in its name with directory separators and appending `.lean` or `.olean`.
Lean searches its include path for the corresponding intermediate build product or importable module file.
:::
-/

:::syntax Lean.Parser.Module.import (title := "导入")
```grammar
import $mod:ident
```

导入指定模块。
导入模块会让其内容及其递归导入的所有模块的内容在当前模块中可见。

模块与命名空间不一定一一对应。
模块可以向任意命名空间添加名称，而导入模块不会影响当前打开的命名空间集合。

被导入模块的名称会通过将名称中的点（.）替换为路径分隔符，并加上 `.lean` 或 `.olean` 后缀，转成文件名。
Lean 在其包含路径中搜索对应的中间构建产物或可导入的模块文件。
:::

/-
## Commands
%%%
tag := "commands"
%%%
-/


/-
{tech}[Commands] are top-level statements in Lean.
Some examples are inductive type declarations, theorems, function definitions, namespace modifiers like `open` or `variable`, and interactive queries such as `#check`.
The syntax of commands is user-extensible, and commands may even {ref "language-extension"}[add new syntax that is used to parse subsequent commands].
Specific Lean commands are documented in the corresponding chapters of this manual, rather than being listed here.
-/

{tech key := "command"}[命令] 是 Lean 的顶级语句。
例如归纳类型声明、定理、函数定义、像 `open` 或 `variable` 这样的命名空间修饰符，以及 `#check` 这样的交互查询，都是命令的例子。
命令的语法是用户可扩展的，而且命令本身还可以 {ref "language-extension"}[扩展用于解析后续命令的语法]。
各类 Lean 命令的详细说明见手册相应章节，下文不再一一枚举。

::: TODO
Make the index include links to all commands, then xref from here
:::

/-
# Elaborated Modules
%%%
tag := "module-contents"
%%%
-/

# 繁释后的模块
%%%
tag := "module-contents"
%%%

/-
When Lean elaborates a module, the result is an {TODO}[def and xref] environment.
The environment includes the constants, {tech}[inductive types], {tech}[theorems], {tech key:="type class"}[type classes], {tech}[instances], and everything else declared in the module, along with side tables that track data as diverse as {tech}[simp sets], namespace aliases, and {tech}[documentation comments].
-/

Lean 在繁释一个模块时，最终会得到一个 {TODO}[def 和交叉引用] 环境。
该环境包括本模块声明的常量、{tech key := "inductive type"}[归纳类型]、{tech key := "theorem"}[定理]、{tech key := "type class"}[类型类]、{tech key := "instance"}[实例] 及其它所有声明，还有用于记录各种数据（如 {tech key := "simp set"}[simp 集]、命名空间别名、{tech key := "documentation comment"}[文档注释]）的辅助表。

/-
As the module is processed by Lean, commands add content to the environment.
A module's environment can be serialized to a {deftech (key:="olean")}[`.olean` file], which contains both the environment and a compacted heap region with the run-time objects needed by the environment.
This means that an imported module can be loaded without re-executing all of its commands.
-/

Lean 处理模块时，命令会不断向环境中添加内容。
模块的环境可以被序列化为一个 {deftech key := "olean"}[`.olean` 文件]，其中即包含环境，也包含环境所需的运行时对象压缩堆区。
这意味着被导入的模块无需重新执行所有命令即可被加载。

/-
# Packages, Libraries, and Targets
%%%
tag := "code-distribution"
%%%
-/

# 包、库与目标
%%%
tag := "code-distribution"
%%%

/-
Lean modules are organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.
-/

Lean 模块被组织为 {deftech key := "package"}_包_，包是代码分发的单位。
一个 {tech key := "package"}[包] 可以包含多个库或可执行文件。

/-
Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
Code that is intended to be compiled and run as independent programs is organized into {deftech (key:="executable")}[executables].
Packages, libraries, and executables are described in detail in the section on {ref "lake"}[Lake, the standard Lean build tool].
-/

包中面向其他 Lean 包复用的代码会被组织为 {deftech key := "library"}[库]。
面向编译并作为独立程序运行的代码被组织为 {deftech key := "executable"}[可执行文件]。
包、库、可执行文件将在 {ref "lake"}[Lake，Lean 标准构建工具] 一节中详细介绍。
