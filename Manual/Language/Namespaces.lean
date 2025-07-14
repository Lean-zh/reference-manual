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
#doc (Manual) "Namespaces" =>
%%%
tag := "namespaces"
%%%
-/

#doc (Manual) "命名空间" =>
%%%
file := "Namespaces"
tag := "namespaces"
%%%

/-
Names that contain periods (that aren't inside {tech}[guillemets]) are hierarchical names; the periods separate the _components_ of a name.
All but the final component of a name are the namespace, while the final component is the name itself.
-/

名称中如果包含句点（不在 {tech key:="guillemets"}[书名号] 之内），则代表这是一个分层名称；句点将名称分成若干_组成部分_。
除了最后一个组成部分外，其他所有部分都构成了命名空间，而最后一个部分才是名称本身。

/-
Namespaces serve to group related definitions, theorems, types, and other declarations.
When a namespace corresponds to a type's name, {tech}[generalized field notation] can be used to access its contents.
In addition to organizing names, namespaces also group {ref "language-extension"}[syntax extensions], {ref "attributes"}[attributes], and {ref "type-classes"}[instances].
-/

命名空间用于对相关的定义、定理、类型以及其他声明进行分组。
当命名空间与某个类型名称对应时，可以使用 {tech key:="generalized field notation"}[广义域标记法] 来访问其内容。
除了整理命名，命名空间还对 {ref "language-extension"}[语法扩展]、{ref "attributes"}[属性] 以及 {ref "type-classes"}[类型类实例] 进行分组。

/-
Namespaces are orthogonal to {tech}[modules]: a module is a unit of code that is elaborated, compiled, and loaded together, but there is no necessary connection between a module's name and the names that it provides.
A module may contain names in any namespace, and the nesting structure of hierarchical modules is unrelated to that of hierarchical namespaces.
-/

命名空间与 {tech key:="modules"}[模块] 是正交的：模块是一起进行繁释、编译和加载的代码单元，但模块名和它所提供的名称之间并无必要的关联。
模块可以包含任意命名空间下的名字，并且分层模块的嵌套结构与分层命名空间之间没有联系。

/-
There is a root namespace, ordinarily denoted by simply omitting a namespace.
It can be explicitly indicated by beginning a name with `_root_`.
This can be necessary in contexts where a name would otherwise be interpreted relative to an ambient namespace (e.g. from a {tech}[section scope]) or local scope.
-/

Lean 中存在一个根命名空间，一般情况下就是省略命名空间时使用的空间。
可以通过以 `_root_` 开头的名称显式指明根命名空间。
在某些情况下（如在某个 {tech key:="section scope"}[作用域] 或局部作用域中），否则名字会被当作相对当前环境来解释，这时就可能需要显式指定 `_root_`。

/-
:::example "Explicit Root Namespace"
Names in the current namespace take precedence over names in the root namespace.
In this example, {name Forest.color}`color` in the definition of {name}`Forest.statement` refers to {name}`Forest.color`:
```lean
def color := "yellow"
namespace Forest
def color := "green"
def statement := s!"Lemons are {color}"
end Forest
```
```lean (name := green)
#eval Forest.statement
```
```leanOutput green
"Lemons are green"
```

Within the `Forest` namespace, references to {name _root_.color}`color` in the root namespace must be qualified with `_root_`:
```lean
namespace Forest
def nextStatement :=
  s!"Ripe lemons are {_root_.color}, not {color}"
end Forest
```
```lean (name := ygreen)
#eval Forest.nextStatement
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
:::
-/

:::example "显式根命名空间"
当前命名空间中的名字优先于根命名空间中的名字。
下面这个例子中，{name Forest.color}`color` 在 {name}`Forest.statement` 的定义中指的是
```lean
def color := "yellow"
namespace Forest
def color := "green"
def statement := s!"Lemons are {color}"
end Forest
```
```lean (name := green)
#eval Forest.statement
```
```leanOutput green
"Lemons are green"
```

在 `Forest` 命名空间内，如果要引用根命名空间下的 {name _root_.color}`color`，则需要加上 `_root_` 前缀进行限定：
```lean
namespace Forest
def nextStatement :=
  s!"Ripe lemons are {_root_.color}, not {color}"
end Forest
```
```lean (name := ygreen)
#eval Forest.nextStatement
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
:::

/-
# Namespaces and Section Scopes
-/

# 命名空间与作用域

/-
Every {tech}[section scope] has a {deftech}_current namespace_, which is determined by the {keywordOf Lean.Parser.Command.namespace}`namespace` command.{margin}[The {keywordOf Lean.Parser.Command.namespace}`namespace` command is described in the {ref "scope-commands"}[section on commands that introduce section scopes].]
Names that are declared within the section scope are added to the current namespace.
If the declared name has more than one component, then its namespace is nested within the current namespace; the body of the declaration's current namespace is the nested namespace.
Section scopes also include a set of {deftech}_opened namespaces_, which are namespaces whose contents are in scope without additional qualification.
{tech key:="resolve"}[Resolving] an identifier to a particular name takes the current namespace and opened namespaces into account.
However, {deftech}[protected] declarations (that is, those with the {keyword}`protected` {ref "declaration-modifiers"}[modifier]) are not brought into scope when their namespace is opened.
The rules for resolving identifiers into names that take the current namespace and opened namespaces into account are described in the {ref "identifiers-and-resolution"}[section on identifiers as terms].
-/

每个 {tech key:="section scope"}[作用域] 都有一个 {deftech key:="current namespace"}_当前命名空间_，其取值由 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令决定。{margin}[关于 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令的详细介绍见 {ref "scope-commands"}[作用域命令] 一节。]
在作用域中声明的名字会被加入当前命名空间。
如果声明的名称由多部分组成，那么其命名空间会嵌套在当前命名空间下；声明体中的当前命名空间是该嵌套命名空间。
作用域还包含一组 {deftech key:="opened namespaces"}_已打开命名空间_，这些命名空间中的内容在当前作用域内无需额外限定就可直接访问。
{tech key:="resolve"}[解析] 一个标识符时，会考虑当前命名空间和已打开命名空间。
但是，被标记为 {deftech key:="protected"}[受保护] 的声明（即带有 {keyword}`protected` {ref "declaration-modifiers"}[修饰符] 的声明）在打开命名空间时并不会被带入作用域。
关于根据当前命名空间和打开的命名空间解析标识符的规则，详见 {ref "identifiers-and-resolution"}[标识符作为项的一节]。

/-
:::example "Current Namespace"
Defining an inductive type results in the type's constructors being placed in its namespace, in this case as {name}`HotDrink.coffee`, {name}`HotDrink.tea`, and {name}`HotDrink.cocoa`.
```lean
inductive HotDrink where
  | coffee
  | tea
  | cocoa
```
Outside the namespace, these names must be qualified unless the namespace is opened:
```lean (name := okTea)
#check HotDrink.tea
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```lean (name := notOkTea) (error := true)
#check tea
```
```leanOutput notOkTea
unknown identifier 'tea'
```
```lean (name := okTea2)
section
open HotDrink
#check tea
end
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```

If a function is defined directly inside the `HotDrink` namespace, then the body of the function is elaborated with the current namespace set to `HotDrink`.
The constructors are in scope:
```lean
def HotDrink.ofString? : String → Option HotDrink
  | "coffee" => some coffee
  | "tea" => some tea
  | "cocoa" => some cocoa
  | _ => none
```
Defining another inductive type creates a new namespace:
```lean
inductive ColdDrink where
  | water
  | juice
```

From within the `HotDrink` namespace, {name}`HotDrink.toString` can be defined without an explicit prefix.
Defining a function in the `ColdDrink` namespace requires an explicit `_root_` qualifier to avoid defining `HotDrink.ColdDrink.toString`:
```lean
namespace HotDrink

def toString : HotDrink → String
  | coffee => "coffee"
  | tea => "tea"
  | cocoa => "cocoa"

def _root_.ColdDrink.toString : ColdDrink → String
  | .water => "water"
  | .juice => "juice"

end HotDrink
```

:::
-/

:::example "当前命名空间"
定义一个归纳类型，会使其构造子被置于该类型的命名空间下，例如 {name}`HotDrink.coffee`、{name}`HotDrink.tea` 和 {name}`HotDrink.cocoa`：
```lean
inductive HotDrink where
  | coffee
  | tea
  | cocoa
```
在命名空间外，除非打开该命名空间，否则需要加前缀才能使用这些名字：
```lean (name := okTea)
#check HotDrink.tea
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```lean (name := notOkTea) (error := true)
#check tea
```
```leanOutput notOkTea
unknown identifier 'tea'
```
```lean (name := okTea2)
section
open HotDrink
#check tea
end
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```

如果直接在 `HotDrink` 命名空间中定义函数，该函数体会在当前命名空间为 `HotDrink` 的情况下进行繁释。
这时构造子都在作用域内：
```lean
def HotDrink.ofString? : String → Option HotDrink
  | "coffee" => some coffee
  | "tea" => some tea
  | "cocoa" => some cocoa
  | _ => none
```
定义另一个归纳类型会新建一个命名空间：
```lean
inductive ColdDrink where
  | water
  | juice
```

在 `HotDrink` 命名空间中，可以直接定义 {name}`HotDrink.toString`，无需显式前缀。
而要在 `ColdDrink` 命名空间中定义一个函数，则需要加上 `_root_` 限定，否则会变成定义 `HotDrink.ColdDrink.toString`：
```lean
namespace HotDrink

def toString : HotDrink → String
  | coffee => "coffee"
  | tea => "tea"
  | cocoa => "cocoa"

def _root_.ColdDrink.toString : ColdDrink → String
  | .water => "water"
  | .juice => "juice"

end HotDrink
```

:::

/-
The {keywordOf Lean.Parser.Command.open}`open` command opens a namespace, making its contents available in the current section scope.
There are many variations on opening namespaces, providing flexibility in managing the local scope.
-/

{keywordOf Lean.Parser.Command.open}`open` 命令用于打开一个命名空间，使其内容可以在当前作用域内使用。
打开命名空间有多种变化方式，便于灵活管理本地作用域。

/-
:::syntax command (title := "Opening Namespaces")
The {keywordOf Lean.Parser.Command.open}`open` command is used to open a namespace:
```grammar
open $_:openDecl
```
:::
-/

:::syntax command (title := "打开命名空间")
{keywordOf Lean.Parser.Command.open}`open` 命令用于打开一个命名空间：
```grammar
open $_:openDecl
```
:::

/-
:::syntax Lean.Parser.Command.openDecl (title := "Opening Entire Namespaces") (label := "open declaration")
A sequence of one or more identifiers results in each namespace in the sequence being opened:
```grammar
$_:ident $_:ident*
```
Each namespace in the sequence is considered relative to all currently-open namespaces, yielding a set of namespaces.
Every namespace in this set is opened before the next namespace in the sequence is processed.
:::
-/

:::syntax Lean.Parser.Command.openDecl (title := "打开整个命名空间") (label := "open declaration")
用一个或多个标识符组成序列，会顺序将这些命名空间打开：
```grammar
$_:ident $_:ident*
```
每个命名空间都相对于所有已打开的命名空间解析，得到一组命名空间。
在处理下一个命名空间之前，会先顺序打开这一组命名空间的所有成员。
:::

/-
:::example "Opening Nested Namespaces"
Namespaces to be opened are considered relative to the currently-open namespaces.
If the same component occurs in different namespace paths, a single {keywordOf Lean.Parser.Command.open}`open` command can be used to open all of them by iteratively bringing each into scope.
This example defines names in a variety of namespaces:
```lean
namespace A -- _root_.A
def a1 := 0
namespace B -- _root_.A.B
def a2 := 0
namespace C -- _root_.A.B.C
def a3 := 0
end C
end B
end A
namespace B -- _root_.B
def a4 := 0
namespace C -- _root_.B.C
def a5 := 0
end C
end B
namespace C -- _root_.C
def a6 := 0
end C
```
The names are:
 * {name}`A.a1`
 * {name}`A.B.a2`
 * {name}`A.B.C.a3`
 * {name}`B.a4`
 * {name}`B.C.a5`
 * {name}`C.a6`

All six names can be brought into scope with a single iterated {keywordOf Lean.Parser.Command.open}`open` command:
```lean
section
open A B C
example := [a1, a2, a3, a4, a5, a6]
end
```

If the initial namespace in the command is `A.B` instead, then neither `_root_.A`, `_root_.B`, nor `_root_.B.C` is opened:
```lean (error := true) (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
unknown identifier 'a1'
```
```leanOutput dotted
unknown identifier 'a4'
```
```leanOutput dotted
unknown identifier 'a5'
```
Opening `A.B` makes `A.B.C` visible as `C` along with `_root_.C`, so the subsequent `C` opens both.
:::
-/

:::example "打开嵌套命名空间"
被打开的命名空间会相对于当前已打开的命名空间进行处理。
如果某个组成部分在不同的命名空间路径中同时出现，则一次 {keywordOf Lean.Parser.Command.open}`open` 命令可以通过迭代方式将所有相关命名空间引入作用域。
下面这个例子定义了多个命名空间下的名称：
```lean
namespace A -- _root_.A
def a1 := 0
namespace B -- _root_.A.B
def a2 := 0
namespace C -- _root_.A.B.C
def a3 := 0
end C
end B
end A
namespace B -- _root_.B
def a4 := 0
namespace C -- _root_.B.C
def a5 := 0
end C
end B
namespace C -- _root_.C
def a6 := 0
end C
```
这些名字分别是：
 * {name}`A.a1`
 * {name}`A.B.a2`
 * {name}`A.B.C.a3`
 * {name}`B.a4`
 * {name}`B.C.a5`
 * {name}`C.a6`

通过一次嵌套的 {keywordOf Lean.Parser.Command.open}`open` 命令，可以将六个名字全部引入作用域：
```lean
section
open A B C
example := [a1, a2, a3, a4, a5, a6]
end
```

如果命令中的初始命名空间使用了 `A.B`，则不会打开 `_root_.A`、`_root_.B` 或 `_root_.B.C`：

```lean (error := true) (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
unknown identifier 'a1'
```
```leanOutput dotted
unknown identifier 'a4'
```
```leanOutput dotted
unknown identifier 'a5'
```
打开 `A.B` 后，`A.B.C` 可以作为 `C` 来访问，而 `_root_.C` 也同样如此，因此后续 open 的 `C` 实际会打开这两个名字。
:::

/-
:::syntax Lean.Parser.Command.openDecl (title := "Hiding Names") (label := "open declaration")
A {keyword}`hiding` declaration specifies a set of names that should _not_ be brought into scope.
In contrast to opening an entire namespace, the provided identifier must uniquely designate a namespace to be opened.
```grammar
$_:ident hiding $x:ident $x:ident*
```
:::
-/

:::syntax Lean.Parser.Command.openDecl (title := "隐藏名字") (label := "open declaration")
{keyword}`hiding` 声明用来指定在打开命名空间时哪些名字_不能_被带入作用域。
与打开整个命名空间不同的是，这时提供的标识符必须唯一地指明待打开命名空间。
```grammar
$_:ident hiding $x:ident $x:ident*
```
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B hiding x
```

/-
:::syntax Lean.Parser.Command.openDecl (title := "Renaming") (label := "open declaration")
A {keyword}`renaming` declaration allows some names from the opened namespace to be renamed; they are accessible under the new name in the current section scope.
The provided identifier must uniquely designate a namespace to be opened.
```grammar
$_:ident renaming $[$x:ident → $x:ident],*
```

An ASCII arrow (`->`) may be used instead of the Unicode arrow (`→`).
:::
-/

:::syntax Lean.Parser.Command.openDecl (title := "重命名") (label := "open declaration")
{keyword}`renaming` 声明允许将打开的命名空间中的部分名字重命名；在当前作用域中可用新名字访问它们。
此处提供的标识符必须唯一地指定要打开的命名空间。
```grammar
$_:ident renaming $[$x:ident → $x:ident],*
```

ASCII 箭头（`->`）也可以替代 Unicode 箭头（`→`）。
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B renaming x → y
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B renaming x -> y
```

/-
:::syntax Lean.Parser.Command.openDecl (title := "Restricted Opening") (label := "open declaration")
Parentheses indicate that _only_ the  names listed in the parentheses should be brought into scope.
```grammar
$_:ident ($x:ident $x*)
```
The indicated namespace is added to each currently-opened namespace, and each name is considered in each resulting namespace.
All of the listed names must be unambiguous; that is, they must exist in exactly one of the considered namespaces.
:::
-/

:::syntax Lean.Parser.Command.openDecl (title := "限制引入名称") (label := "open declaration")
用圆括号括住一组名字表示只将括号内列出的名字带入作用域。
```grammar
$_:ident ($x:ident $x*)
```
指定的命名空间会加到当前所有已打开命名空间中，每个名字会在所有这些命名空间中查找。
列出的每个名字都必须是明确且唯一的，也就是说每个名字只能在所有考虑到的命名空间中存在于唯一一处。
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def y := ""
end B
end A
namespace B
end B
open A
-- test claim in preceding box
-- TODO the reality is a bit more subtle - the name should be accessible by only one path. This should be clarified.
/-- error: ambiguous identifier 'y', possible interpretations: [B.y, B.y] -/
#check_msgs in
open B (y)
```
/-
:::syntax Lean.Parser.Command.openDecl (title := "Scoped Declarations Only") (label := "open declaration")
The {keyword}`scoped` keyword indicates that all scoped attributes, instances, and syntax from the provided namespaces should be opened, while not making any of the names available.
```grammar
scoped $x:ident $x*
```
:::
-/

:::syntax Lean.Parser.Command.openDecl (title := "仅打开受限定声明") (label := "open declaration")
{keyword}`scoped` 关键字用于只打开指定命名空间中的所有受限定属性、类型类实例和语法扩展，但不会将实际名字带入作用域。
```grammar
scoped $x:ident $x*
```
:::

/-
::::example "Opening Scoped Declarations"
In this example, a scoped {tech}[notation] and a definition are created in the namespace `NS`:
```lean
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS
```

Outside of the namespace, the notation is not available:

```syntaxError closed
def x := {!{ "pear" }!}
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```

An {keyword}`open scoped` command makes the notation available:
:::keepEnv
```lean
open scoped NS
def x := {!{ "pear" }!}
```

However, the name {name}`NS.three` is not in scope:
```lean (error := true) (name := nothree)
def y := three
```
```leanOutput nothree
unknown identifier 'three'
```
:::
::::
-/

::::example "打开受限定声明"
下面例子中，在命名空间 `NS` 下定义了一个受限定的 {tech key:="notation"}[符号扩展] 以及一个定义：
```lean
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS
```

在命名空间外，这个符号扩展无法直接使用：

```syntaxError closed
def x := {!{ "pear" }!}
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```

用 {keyword}`open scoped` 命令后，符号扩展才能使用：
:::keepEnv
```lean
open scoped NS
def x := {!{ "pear" }!}
```

但是，名字 {name}`NS.three` 仍然无法直接访问：
```lean (error := true) (name := nothree)
def y := three
```
```leanOutput nothree
unknown identifier 'three'
```
:::
::::

/-
# Exporting Names
-/

# 导出名称

/-
{deftech}_Exporting_ a name makes it available in the current namespace.
Unlike a definition, this alias is completely transparent: uses are resolved directly to the original name.
Exporting a name to the root namespace makes it available without qualification; the Lean standard library does this for names such as the constructors of {name}`Option` and key type class methods such as {name}`get`.
-/

{deftech key:="exporting"}_导出_一个名字，就是将其引入到当前命名空间内。
与定义不同，导出的名字是完全透明的：在使用时会直接解析到原始名字。
将名字导出到根命名空间，则可以直接不加限定地访问它；Lean 标准库会这样做，例如 {name}`Option` 的构造子，或像 {name}`get` 这样的关键类型类方法。

/-
:::syntax command (title := "Exporting Names")
The {keyword}`export` command adds names from other namespaces to the current namespace, as if they had been declared in it.
When the current namespace is opened, these exported names are also brought into scope.

```grammar
export $_ ($_*)
```

Internally, exported names are registered as aliases of their targets.
From the perspective of the kernel, only the original name exists; the elaborator resolves aliases as part of {tech key:="resolve"}[resolving] identifiers to names.
:::
-/

:::syntax command (title := "导出名称")
{keyword}`export` 命令可以将其他命名空间中的名字添加到当前命名空间，就好像它们原本就是在这里声明的一样。
当当前命名空间被打开时，这些导出的名字也会被带入作用域。

```grammar
export $_ ($_*)
```

内部实现上，导出的名字会注册成其目标的别名。
在 {tech key:="kernel"}[内核] 看来，只有原始名字存在；{tech key:="elaborator"}[繁释器] 在 {tech key:="resolve"}[解析] 标识符到名字的过程中负责处理别名。
:::

/-
:::example "Exported Names"
The declaration of the {tech}[inductive type] {name}`Veg.Leafy` establishes the constructors {name}`Veg.Leafy.spinach` and {name}`Veg.Leafy.cabbage`:
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
```
The first {keyword}`export` command makes {name}`Veg.Leafy.spinach` accessible as {name}`Veg.spinach` because the {tech}[current namespace] is `Veg`.
The second makes {name}`Veg.Leafy.cabbage` accessible as {name}`cabbage`, because the current namespace is the root namespace.
:::
-/

:::example "导出名称"
声明 {tech key:="inductive type"}[归纳类型] {name}`Veg.Leafy` 的同时，也声明了构造子 {name}`Veg.Leafy.spinach` 和 {name}`Veg.Leafy.cabbage`：
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
```
第一次 {keyword}`export` 命令将 {name}`Veg.Leafy.spinach` 作为 {name}`Veg.spinach` 引入作用域，因为此时 {tech key:="current namespace"}[当前命名空间] 是 `Veg`。
第二次导出将 {name}`Veg.Leafy.cabbage` 引入根命名空间，可以直接使用 {name}`cabbage`。
:::
