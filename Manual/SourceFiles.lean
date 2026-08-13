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
-/

#doc (Manual) "源文件与模块" =>
%%%
file := "Source Files and Modules"
tag := "files"
htmlSplit := .never
%%%


在 Lean 中，编译的最小单位是单个 {tech (key := "source file")}[源文件]。
源文件可以按文件名导入其它源文件。
换句话说，文件的名称和文件夹结构在 Lean 代码中具有重要意义。


每个源文件都有一个 {deftech (key := "import name")}_导入名_。它由文件名和 Lean 的启动方式共同决定：Lean 会在一组_根目录_中查找代码；源文件的导入名由从根目录到该文件的各级目录名和文件名组成，以点（`.`）分隔，并去掉 `.lean` 后缀。
例如，如果 Lean 以 `Projects/MyLib/src` 作为根目录，那么文件 `Projects/MyLib/src/Literature/Novel/SciFi.lean` 可用 `Literature.Novel.SciFi` 导入。

::: TODO
Describe case sensitivity/preservation for filenames here
:::


# 编码与表示
%%%
tag := "module-encoding"
%%%


Lean {deftech (key := "source file")}[源文件]是采用 UTF-8 编码的 Unicode 文本文件。{TODO}[确认 BOM 与 Lean 的支持情况]
文件的每一行可以以换行字符（`\n`，Unicode `'LINE FEED (LF)' (U+000A)`）结尾，也可以以回车加换行序列（`\r\n`，即 Unicode `'CARRIAGE RETURN (CR)' (U+000D)` 加 `'LINE FEED (LF)' (U+000A)`）结尾。
不过，在解析或比较文件时，Lean 会对行尾进行归一化，因此所有文件在比较时都视为全部是 `\n` 行尾。

::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::


# 具体语法
%%%
tag := "module-syntax"
%%%


Lean 的具体语法是 {ref "language-extension"}[可扩展的]。
在 Lean 这样的语言中，无法一次性完整地描述所有语法，因为库中还可以定义新的语法、常量，或者 {tech (key := "inductive type")}[归纳类型]。
本节不会详尽描述整个语言，而是介绍整体框架；各个语言结构的具体语法则在其各自章节中详细说明。


## 空白符
%%%
tag := "whitespace"
%%%


Lean 中的词法单元（token）之间可以用任意数量的 {deftech (key := "whitespace")}[_空白符_] 字符序列分隔。
空白符可以是空格 (`" "`, Unicode `'SPACE (SP)' (U+0020)`)、合法的换行序列，或注释。{TODO}[交叉引用补充]
制表符和单独的回车（CR，未跟随换行）不是合法的空白符序列。


## 注释
%%%
tag := "comments"
%%%







注释是文件中虽然不是空白符，但被视为空白的部分。
Lean 提供两种注释语法：

: 行注释

  当 `--` 不作为其他词法单元一部分出现时，表示行注释。该标记后的所有内容直到行尾都会被视为空白字符。{index (subterm := "line")}[comment]

: 块注释

  当 `/-` 不作为其他词法单元一部分，且后面不是 `-` 字符时，表示块注释的开始。{index (subterm := "block")}[comment]
  块注释会一直持续到出现 `-/` 终止为止。
  块注释允许嵌套；仅在所有内部嵌套的 `/-` 都被匹配的 `-/` 终止后，最外层才算结束。



`/--` 与 `/-!` 用于开始 {deftech (key := "documentation")}_文档注释_ {TODO}[交叉引用]，它们同样以 `-/` 结束，并允许嵌套块注释。
尽管文档注释看起来与普通注释类似，但在语法上它们属于不同类别；它们能出现的位置由 Lean 的语法决定。


## 关键字与标识符
%%%
tag := "keywords-and-identifiers"
%%%


一个 {tech (key := "identifier")}[标识符] 由一个或多个标识符成分（component）组成，各部分用 `'.'` 分隔。{index}[identifier]


{deftech (key := "identifier component")}[标识符成分] 由一个字母或类字母字符或下划线（`'_'`）开头，后面可以跟零个或多个标识符后续字符。
字母包括英文大小写字母，而类字母字符还包含范围较广的非英语字母脚本，比如 Lean 中广泛采用的希腊字母、以及 Unicode 的字母符号区块（如 `ℕ`、`ℤ` 等粗体字符和缩写）。
标识符的后续字符包括字母、类字母字符、下划线（`'_'`）、感叹号（`!`）、问号（`?`）、下标和单引号（`'`）。
作为例外，单独下划线不是合法的标识符。

```lean -show
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

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Success! Final stack:\n  `øvelse\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "øvelse"

/-- info: "Success! Final stack:\n  `Übersetzung\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "Übersetzung"

/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"汉语\"" -/
#check_msgs in
#eval validIdentifier "汉语"


```


标识符成分也可以用一对双 {deftech (key := "guillemets")}[尖引号]（`'«'` 和 `'»'`）括起来。
这样括起来的成分可以包含除 `'»'` 之外的任意字符，包括 `'«'`、`.` 和换行符。
尖引号本身不计入标识符最终内容，所以 `«x»` 和 `x` 是同一个标识符。
而 `«Nat.add»` 是一个包含一个成分的标识符，而 `Nat.add` 则包含两个成分。



```lean -show
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

可能的标识符成分中有一些属于保留关键字。
具体的保留关键字集合取决于当前激活的语法扩展集合，后者又依赖于已导入的模块以及当前打开的 {TODO}[交叉引用/定义：namespace] 命名空间；因此无法为整个 Lean 语言列举一个完整集合。
在大多数语法环境中，若要用关键字作为标识符成分，必须用尖引号括起来。
在某些环境下（如归纳类型的构造子名称）关键字无需尖引号也能作为标识符使用，这些环境称为 {deftech (key := "raw identifier")}_原始标识符_ 环境。{index (subterm:="raw")}[identifier]


包含一个或多个 `'.'` 字符的标识符（因此包含多个标识符成分）被称为 {deftech (key := "hierarchical identifier")}[分层标识符]。
分层标识符同时用于表示导入名和命名空间中的名称。


# 结构
%%%
tag := "module-structure"
%%%


:::syntax Lean.Parser.Module.module -open (title := "源文件")
```grammar
$hdr:header $cmd:command*
```

源文件由一个 {deftech (key := "file header")}_文件头_，后面跟随一系列 {deftech (key := "commands")}_命令_ 组成。

:::

如果源文件的文件头以 {keywordOf Lean.Parser.Module.header}`module` 开头，那么该源文件称为一个 {tech (key := "module")}[模块]。
模块可以更精细地控制向使用方公开哪些信息。


## 文件头
%%%
tag := "module-headers"
%%%


文件头列出在当前源文件之前需要精译的源文件。
这些源文件中的声明在当前源文件中可见。


:::syntax Lean.Parser.Module.header -open (title := "文件头")
文件头由一个可选的 {keywordOf Lean.Parser.Module.header}`module` 关键字和一系列 {deftech (key := "import")}[`import` 语句]组成：
```grammar
$[module]?
$i:import*
```

可选的 {keyword}`prelude` 关键字只应在 Lean 源码中出现：
```grammar
$[module]?
prelude
$i:import*
```
:::


如果存在 {keyword}`prelude` 关键字，则表示该文件属于 Lean {deftech (key := "prelude")}_前导库_ 的实现部分，也就是无需任何显式导入即可使用的代码——不应在 Lean 实现之外使用。


:::syntax Lean.Parser.Module.prelude -open (title := "前导库模块")
```grammar
prelude
```

:::

::::syntax Lean.Parser.Module.import (title := "Imports")
All {tech}[source files] may use plain imports:
```grammar
import $mod:ident
```

In source files that are not modules, this imports the specified Lean file.
Importing a file makes its contents available in the current source file, as well as those from source files transitively imported by its imports.

Source file names do not necessarily correspond to namespaces.
Source files may add names to any namespace, and importing a source file has no effect on the set of currently open namespaces.

The {tech}[import name] is translated to a filename by replacing dots (`'.'`) in its name with directory separators and appending `.lean` or `.olean`.
Lean searches its include path for the corresponding intermediate build product or importable module file.

{tech}[Modules] may use the following import syntax:
```grammar
$[public]? $[meta]? import $[all]? $mod:ident
```

:::paragraph
All imports to a module must themselves be modules.
Without modifiers, the imported module's public scope is added to the current module's private scope. The imported module is not made available to modules that import the current module.
The modifiers have the following meanings:

: {keyword}`public`

  The imported module's public scope is added to the current module's public scope and made available to the current module's importers.

: {keyword}`meta`

  The contents of the imported module are made available at the {tech}[meta phase] in the current module.

: {keyword}`all`

  The imported module's private scope is added to the current module's {tech}[private scope].
:::
::::

源文件与命名空间不一定一一对应。
源文件可以向任意命名空间添加名称，而导入源文件不会影响当前打开的命名空间集合。

导入名会通过将名称中的点（`.`）替换为路径分隔符，并加上 `.lean` 或 `.olean` 后缀，转成文件名。
Lean 在其包含路径中搜索对应的中间构建产物或可导入的模块文件。


## 命令
%%%
tag := "commands"
%%%


{tech (key := "command")}[命令] 是 Lean 的顶级语句。
例如归纳类型声明、定理、函数定义、像 `open` 或 `variable` 这样的命名空间修饰符，以及 `#check` 这样的交互查询，都是命令的例子。
命令的语法是用户可扩展的，而且命令本身还可以 {ref "language-extension"}[扩展用于解析后续命令的语法]。
各类 Lean 命令的详细说明见手册相应章节，下文不再一一枚举。

::: TODO
Make the index include links to all commands, then xref from here
:::

# Modules and Visibility
%%%
tag := "module-scopes"
%%%

:::paragraph
A {deftech}[module] is a source file that has opted in to a distinction between public and private information.
Lean ensures that private information can change without affecting clients that import only its public information.
This discipline brings a number of benefits:

: Much-improved average build times

  Changes to files that affect only non-exported information (e.g. proofs, comments, and docstrings) will not trigger rebuilds outside of these files.
  Even when dependent files have to be rebuilt, those files that cannot be affected (as determined by their {keywordOf Lean.Parser.Module.import}`import` annotations) can be skipped.

: Control over API evolution

  Library authors can trust that changes to non-exported information will not affect downstream users of their library.
  If only a function's signature is exposed, then downstream users cannot rely on definitional equalities that involve its unfolding; this means that the library's author is free to adopt a more efficient algorithm without unintentionally breaking client code.

: Avoiding accidental unfolding

  Limiting the scope in which definitions can be unfolded allows for avoiding both reductions that should be replaced by application of more specific theorems as well as unproductive reductions that were not in fact necessary.
  This improves the speed of proof elaboration.

: Smaller executables

  Separating compile-time and run-time code allows for more aggressive dead code elimination, guaranteeing that metaprograms such as tactics do not make it into the final binary.

: Reduced memory usage

  Excluding private information such as proofs from importing can improve Lean's memory use both while building and editing a project.
  Porting mathlib4 to the module system has shown savings close to 50% from this even before imports are further minimized.{TODO}[link and format of mathlib name consistent with rest of manual]
:::

:::paragraph
Modules contain two separate scopes: the {deftech}_public scope_ consists of information that is visible in modules that import a module, while the {deftech}_private scope_ consists of information that is generally visible only within the module.
Some examples of information that can be private or public include:

: Names

  Constants (such as definitions, inductive types, or constructors) may be private or public.
  A public constant's type may only refer to public names.

: Definitions

  A public definition may be {deftech}[exposed] or not.
  If a public definition is not exposed, then it cannot be unfolded in contexts that only have access to the public scope.
  Instead, clients must rely on the theorems about the definition that are provided in the public scope.
:::

Each declaration has default visibility rules.
Generally speaking, all names are private by default, unless defined in a {tech}[public section].
Even public names usually place the bodies of definitions in the private scope, and even proofs in exposed definitions are kept private.
The specific visibility rules for each declaration command are documented together with the declaration itself.

::::example "Private and Public Definitions"
:::leanModules +error
The module {module}`Greet.Create` defines a function {name}`greeting`.
Because there are no visibility modifiers, this function defaults to the {tech}[private scope]:
```leanModule (moduleName := Greet.Create)
module
def greeting (name : String) : String :=
  s!"Hello, {name}"
```
The definition of {name}`greeting` is not visible in the module {module}`Greet`, even though it imports {module}`Greet.Create`:
```leanModule (moduleName := Greet) (name := noRef)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
```leanOutput noRef
Unknown identifier `greeting`
```
:::

:::leanModules
If {name}`greeting` is made public, then {name}`greetTwice` can refer to it:
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
:::
::::

::::example "Exposed and Unexposed Definitions"
:::leanModules +error
The module {module}`Greet.Create` defines a public function {name}`greeting`.
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
Although the definition of {name}`greeting` is visible in the module {module}`Greet`, it cannot be unfolded in a proof because the definition's body is in the {tech}[private scope] of {module}`Greet`:
```leanModule (moduleName := Greet) (name := nonExp)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting]
```
```leanOutput nonExp
Invalid simp theorem `greeting`: Expected a definition with an exposed body
```
:::

:::leanModules
Adding the {attrs}`@[expose]` attribute exposes the definition so that downstream modules can unfold {name}`greeting`:
```leanModule (moduleName := Greet.Create)
module
@[expose]
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
Now, the proof can proceed:
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting, toString]
  grind [String.append_assoc]
```
:::
::::

:::::example "Proofs are Private"
::::leanModules
:::paragraph
In this module, the function {name}`incr` is public, but its implementation is not exposed:
```leanModule (moduleName := Main)
module

public def incr : Nat → Nat
  | 0 => 1
  | n + 1 => incr n + 1

public theorem incr_eq_plus1 : incr = (· + 1) := by
  funext n
  induction n <;> simp [incr, *]
```
:::

Nonetheless, the proof of the theorem {name}`incr_eq_plus1` can unfold its definition.
This is because proofs of theorems are in the private scope.
This is the case both for public and private theorems.
::::
:::::

The option {option}`backward.privateInPublic` can be used while transitioning from ordinary source files to modules.
When it is set to {lean}`true`, private definitions are exported, though their names are not accessible in importing modules.
However, references to them in the public part of their defining module are allowed.
Such references result in a warning unless the option {option}`backward.privateInPublic.warn` is set to {lean}`false`.
These warnings can be used to locate and eventually eliminate these references, allowing {option}`backward.privateInPublic` to be disabled.
Similarly, {option}`backward.proofsInPublic` causes proofs created with {keywordOf Lean.Parser.Term.by}`by` to be public, rather than private; this can enable {keywordOf Lean.Parser.Term.by}`by` to fill in metavariables in its expected type.
Most use cases for {option}`backward.proofsInPublic` also require that {option}`backward.privateInPublic` is enabled.

{optionDocs backward.privateInPublic}

{optionDocs backward.privateInPublic.warn}

{optionDocs backward.proofsInPublic}

::::example "Exporting Private Definitions"
:::leanModules
In the module {module}`L.Defs`, the public definition of {name}`f` refers to the private definition {name}`drop2` in its signature.
Because {option}`backward.privateInPublic` is {lean}`true`, this is allowed, resulting in a warning:
```leanModule (moduleName := L.Defs) (name := warnPub)
module

set_option backward.privateInPublic true

def drop2 (xs : List α) : List α := xs.drop 2

public def f (xs : List α) (transform : List α → List α:= drop2) : List α :=
  transform xs
```
```leanOutput warnPub
Private declaration `drop2` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled.

Disable `backward.privateInPublic.warn` to silence this warning.
```
When the module is imported, references to {name}`f` use {name}`drop2` as a default argument value; however, its name is inaccessible in the module {module}`L`:
```leanModule (moduleName :=  L) (name := withPrivateInTerm)
module
import L.Defs

def xs := [1, 2, 3]

set_option pp.explicit true in
#check f xs
```
```leanOutput withPrivateInTerm
@f Nat xs (@drop2✝ Nat) : List Nat
```
:::
::::

::::example "Proofs in Public"
:::leanModules
In the plain source file {module}`NotMod`, the definition of {name}`two` uses the content of the proof to fill out the numeric value in the definition by solving a {tech}`metavariable`:
```leanModule (moduleName := NotMod)
structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::
:::leanModules +error
Converting this file to a module results in an error, because the body of the definition is exposed in the public part but the proof is private and thus cannot change the public type:
```leanModule (moduleName := Mod) (name := proofMeta)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
```leanOutput proofMeta
tactic execution is stuck, goal contains metavariables
  ?m.3 + ?m.3 = ?m.5
```
:::
:::leanModules
Setting the option {option}`backward.proofsInPublic` causes the proof to be in the public part of the module so it can solve the metavariable:
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

set_option backward.proofsInPublic true in
abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::

:::leanModules
However, it is typically better style to reformulate the definition so that the proof has a complete goal:
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two : Half 4 := Half.mk 2 <| by
  rfl
```
:::
::::


The private scope of a module may be imported into another module using the {keywordOf Lean.Parser.Module.import}`all` modifier.
By default, this is only allowed if the imported module and the current module are from the same Lake {tech}[package], as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
The Lake package or library option {ref "Lake.PackageConfig allowImportAll" (domain := Manual.lakeTomlField)}`allowImportAll` can be set to allow other packages to access to the current package's private scopes via {keywordOf Lean.Parser.Module.import}`import all`.
The imported private scope includes private imports of the imported module, including nested {keywordOf Lean.Parser.Module.import}`import all`s.
As a consequence, the set of private scopes accessible to the current module is the transitive closure of {keywordOf Lean.Parser.Module.import}`import all` declarations.

The module system's {keywordOf Lean.Parser.Module.import}`import all` is more powerful than {keywordOf Lean.Parser.Module.import}`import` without the module system.
It makes imported private definitions accessible directly by name, as if they were defined in the current module.
A secondary use case for {keywordOf Lean.Parser.Module.import}`import all` is to access code in multiple modules within a library that should nonetheless not be provided to downstream consumers, as well as to allow tests to access information that is not part of the public API.

::::example "Importing Private Information"
:::leanModules (moduleRoot := Tree) +error
This library separates a module of definitions from a module of lemmas.
This is a common pattern in Lean code.
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
However, because {name}`Tree.count` is not exposed, the proof in the lemma file cannot unfold it:
```leanModule (moduleName := Tree.Lemmas) (name := lemmasNoAll)
module
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
```leanOutput lemmasNoAll
Invalid simp theorem `count`: Expected a definition with an exposed body
```
:::

:::leanModules (moduleRoot := Tree)
Importing the private scope from {module}`Tree.Basic` into the lemma module allows the definition to be unfolded in the proof.
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
```leanModule (moduleName := Tree.Lemmas)
module
import all Tree.Basic
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
:::
::::


## The Meta Phase
%%%
tag := "meta-phase"
%%%

Definitions in Lean result in both a representation in the type theory that is designed for formal reasoning and a compiled representation that is designed for execution.
This compiled representation is used to generate machine code, but it can also be executed directly using an interpreter.
The code that runs during {tech (key := "Lean elaborator")}[elaboration], such as {ref "tactics"}[tactics] or {ref "macros"}[macros], is the compiled form of definitions.
If this compiled representation changes, then any code created by it may no longer be up to date, and it must be re-run.
Because the compiler performs non-trivial optimizations, changes to any definition in the transitive dependency chain of a function could in principle invalidate its compiled representation.
This means that metaprograms exported by modules induce a much stronger coupling than ordinary definitions.
Furthermore, metaprograms run _during_ the construction of ordinary terms; thus, they must be fully defined and compiled before use.
After all, a function definition without a body cannot be run.
The time at which metaprograms are run is referred to as the {deftech}_metaprogramming phase_, frequently just called the {deftech}_meta phase_.

Just as they distinguish between public and private information, modules additionally distinguish code that is available in the meta phase from ordinary code.
Any declaration used as an entry point to compile-time execution has to be tagged with the {keywordOf Lean.Parser.Module.import}`meta` modifier, which indicates that the declaration is available for use as a metaprogram.
This is automatically done in built-in metaprogramming syntax such as {keywordOf Lean.Parser.Command.syntax}`syntax`, {keywordOf Lean.Parser.Command.macro}`macro`, and {keywordOf Lean.Parser.Command.elab}`elab` but may need to be done explicitly when manually applying metaprogramming attributes such as {keyword}`app_delab` or when defining helper declarations.
A {keywordOf Parser.Command.declModifiers}`meta` definition may only access (and thus invoke) other {keywordOf Parser.Command.declModifiers}`meta` definitions in execution-relevant positions; a non-{keywordOf Parser.Command.declModifiers}`meta` definition likewise may only access other non-{keywordOf Parser.Command.declModifiers}`meta` definitions.

::::example "Meta Definitions"
:::leanModules +error
In this module, the helper function {name}`revArrays` reverses the order of the elements in each array literal in a term.
This is called by the macro {keyword}`rev!`.
```leanModule (moduleName := Main) (name := nonMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e
```
The error message indicates that {name}`revArrays` cannot be used from the macro because it is not defined in the module's {tech}[metaprogramming phase]:
```leanOutput nonMeta
Invalid `meta` definition `_aux___macroRules_termRev!__1`, `revArrays` not marked `meta`
```
:::
:::leanModules
Marking {name}`revArrays` with the {keywordOf Lean.Parser.Command.declModifiers}`meta` modifier allows the macro definition to call it:
```leanModule (moduleName := Main) (name := withMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e

#eval rev! #[1, 2, 3]
```
```leanOutput withMeta
#[3, 2, 1]
```
:::
::::

Libraries that were not originally part of the meta phase can be brought into it by importing a module with {keywordOf Parser.Module.import}`meta import`.
When a module is imported at the meta phase, all of its definitions are made available at that phase, whether or not they were marked {keywordOf Parser.Command.declModifiers}`meta`.
There is no meta-meta phase.
In addition to making the imported module's public contents available at the meta phase, {keywordOf Parser.Module.import}`meta import` indicates that the current module should be rebuilt if the compiled representation of the imported module changes, ensuring that modified metaprograms are re-run.
If a definition should be usable in both phases, then it must be defined in a separate module and imported at both phases.

::::example "Cross-Phase Code Reuse"
:::leanModules +error
In this module, the function {name}`toPalindrome` is defined in the meta phase, which allows it to be used in a macro but not in an ordinary definition:
```leanModule (moduleName := Phases) (name := bothPhases)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
```leanOutput bothPhases
Invalid definition `colors`, may not access declaration `toPalindrome` marked as `meta`
```
:::
:::leanModules
Moving {name}`toPalindrome` to its own module, {module}`Phases.Pal`, allows this module to be imported at both phases:
```leanModule (moduleName := Phases.Pal)
module

public def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse
```
```leanModule (moduleName := Phases) (name := bothPhases)
module

meta import Phases.Pal
import Phases.Pal

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

local macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
If the macro {keyword}`pal!` were public (that is, if it was not declared with the {keyword}`local` modifier) then the {keywordOf Lean.Parser.Module.import}`meta import` of {module}`Phases.Pal` would need to be declared {keywordOf Lean.Parser.Module.import}`public` as well.
:::
::::

In addition, the import must be public if the imported definition may be executed at compile time outside the current module, i.e. if it is reachable from some public {keywordOf Parser.Command.declModifiers}`meta` definition in the current module.
Use {keywordOf Parser.Module.import}`public meta import`.
If the declaration is already declared {keywordOf Parser.Command.declModifiers}`meta`, then {keywordOf Parser.Module.import}`public import` is sufficient.

Unlike definitions, most metaprograms are public by default.
Thus, most {keywordOf Lean.Parser.Module.import}`meta import` are also {keywordOf Parser.Module.import}`public` in practice.
The exception is when a definition is imported solely for use in local metaprograms, such as those declared with {keywordOf Parser.Command.syntax}`local syntax`, {keywordOf Parser.Command.macro}`local macro`, or {keywordOf Parser.Command.elab}`local elab`.

As a guideline, it is usually preferable to keep the amount of {keywordOf Lean.Parser.Command.declModifiers}`meta` annotations as small as possible.
This avoids locking otherwise-reusable declarations into the {tech}[meta phase] and it helps the build system avoid more rebuilds.
Thus, when a metaprogram depends on other code that does not itself need to be marked {keywordOf Lean.Parser.Command.declModifiers}`meta`, this other code should be placed in a separate module and not marked {keywordOf Lean.Parser.Command.declModifiers}`meta`.
Only the final module that actually registers a metaprogram needs the helpers to be in the meta phase.
This module should use {keywordOf Lean.Parser.Module.import}`public meta import` to import those helpers and then define its metaprograms using built-in syntax like {keywordOf Parser.Command.elab}`elab`, using {keywordOf Lean.Parser.Command.declaration}`meta def`, or using {keywordOf Lean.Parser.Command.section}`meta section`.




# 精译后的源文件
%%%
tag := "module-contents"
%%%


Lean 在精译一个源文件时，最终会得到一个 {tech (key := "environment")}[环境]。
该环境包括本文件声明的常量、{tech (key := "inductive type")}[归纳类型]、{tech (key := "theorems")}[定理]、{tech (key := "type class")}[类型类]、{tech (key := "instance")}[实例]及其它所有声明，还有用于记录各种数据（如 {tech (key := "simp set")}[simp 集]、命名空间别名、{tech (key := "documentation comment")}[文档注释]）的辅助表。
如果文件包含模块，环境还会记录哪些信息是公开或私有的，以及定义在哪个阶段可用。


Lean 处理源文件时，命令会不断向环境中添加内容。
精译完成后，环境会被序列化为一个 {deftech (key := "olean")}[`.olean` 文件]，其中既包含环境，也包含环境所需运行时对象的压缩堆区。
这意味着被导入的源文件无需重新执行所有命令即可加载。
精译模块所得的环境会被序列化为三个 {tech (key := "olean")}[`.olean` 文件]，分别保存环境中的私有信息、公开信息和服务器信息。
服务器信息包括 API 文档和定义的源码位置等数据；它们只在使用 Lean 语言服务器时需要，无需随公开信息一起加载。

# Module System Errors and Patterns

:::paragraph
The following list contains common errors one might encounter when using the module system and especially porting existing files to the module system:

: Unknown constant errors

  Check whether a private definition is being accessed in the {tech}[public scope].
  If so, the problem can be solved by making the current declaration private as well, or by placing the reference into the private scope using the {keywordOf Lean.Parser.Term.structInstFieldDef}`private` modifier on a field or {keywordOf Lean.Parser.Term.by}`by` for a proof.

: Definitional equality errors, especially after porting

  Failures of expected definitional equalities are usually due to a missing {attr}`expose` attribute on a definition or alternatively, if imported, an {keywordOf Lean.Parser.Module.import}`import all`.
  Prefer the former if anyone outside your library might feasibly require the same access.
  The error message should list non-exposed definitions that could not be unfolded.
  This may also appear as a kernel error when a tactic directly emits proof terms that reference specific declarations without going through the elaborator, such as for proof by reflection.
  In this case, there is no readily available trace for debugging; consider using {attrs}`@[expose]`‍` `{keywordOf Parser.Command.section}`section`s generously on the closure of relevant modules.

:::

## Recipe for Porting Existing Files

:::paragraph
To gain the benefits of the module system, source files must be made into modules.
Start by enabling the module system throughout all files with minimal breaking changes:
1. Prefix all files with {keywordOf Lean.Parser.Module.header}`module`.
2. Make all existing imports {keywordOf Lean.Parser.Command.declModifiers}`public` unless they will be used only in proofs.
 * Add {keywordOf Lean.Parser.Module.import}`import all` when errors that mention references to private data occur.
 * Add {keywordOf Lean.Parser.Module.import}`public meta import` when errors that mention “must be {keywordOf Lean.Parser.Module.import}`meta`” occur.
   The {keywordOf Lean.Parser.Module.import}`public` may be omitted when defining local-only metaprograms.
3. Prefix the remainder of the file with `@[expose] public section` or, for programming-focused files, with {keywordOf Lean.Parser.Command.section}`public section`.
   The latter should be used for programs that will be run but not reasoned about.
:::

After an initial build under the module system succeeds, the dependencies between modules can be iteratively minimized.
In particular, removing uses of {keywordOf Lean.Parser.Command.declModifiers}`public` and {attrs}`@[expose]` will help avoid unnecessary rebuilds.


# 包、库与目标
%%%
tag := "code-distribution"
%%%


Lean 模块被组织为 {tech (key := "package")}[包]，包是代码分发的单位。
一个 {tech (key := "package")}[包] 可以包含多个库或可执行文件。


包中面向其他 Lean 包复用的代码会被组织为 {deftech (key := "library")}[库]。
面向编译并作为独立程序运行的代码被组织为 {deftech (key := "executable")}[可执行文件]。
包、库、可执行文件将在 {ref "lake"}[Lake，Lean 标准构建工具] 一节中详细介绍。
