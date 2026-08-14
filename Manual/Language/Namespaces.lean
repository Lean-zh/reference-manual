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
-/

#doc (Manual) "命名空间" =>
%%%
file := "Namespaces"
tag := "namespaces"
%%%


名称中如果包含句点（不在 {tech (key := "guillemets")}[尖引号] 之内），则代表这是一个分层名称；句点将名称分成若干_组成部分_。
除了最后一个组成部分外，其他所有部分都构成了命名空间，而最后一个部分才是名称本身。


命名空间用于对相关的定义、定理、类型以及其他声明进行分组。
当命名空间与某个类型名称对应时，可以使用 {tech (key := "generalized field notation")}[广义域标记法] 来访问其内容。
除了整理命名，命名空间还对 {ref "language-extension"}[语法扩展]、{ref "attributes"}[属性] 以及 {ref "type-classes"}[类型类实例] 进行分组。


命名空间与 {tech (key := "modules")}[模块] 是正交的：模块是一起进行精译、编译和加载的代码单元，但模块名和它所提供的名称之间并无必要的关联。
模块可以包含任意命名空间下的名字，并且分层模块的嵌套结构与分层命名空间之间没有联系。


Lean 中存在一个根命名空间，一般情况下就是省略命名空间时使用的空间。
可以通过以 `_root_` 开头的名称显式指明根命名空间。
在某些情况下（如在某个 {tech (key := "section scope")}[作用域] 或局部作用域中），否则名字会被当作相对当前环境来解释，这时就可能需要显式指定 `_root_`。


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


# 命名空间与作用域
%%%
tag := "namespaces-and-scopes"
%%%


每个 {tech (key := "section scope")}[作用域] 都有一个 {tech (key := "current namespace")}[当前命名空间]，其取值由 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令决定。{margin}[关于 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令的详细介绍见 {ref "scope-commands"}[作用域命令] 一节。]
在作用域中声明的名字会被加入当前命名空间。
如果声明的名称由多部分组成，那么其命名空间会嵌套在当前命名空间下；声明体中的当前命名空间是该嵌套命名空间。
作用域还包含一组 {deftech (key := "opened namespaces")}_已打开命名空间_，这些命名空间中的内容在当前作用域内无需额外限定就可直接访问。
{tech (key := "resolve")}[解析] 一个标识符时，会考虑当前命名空间和已打开命名空间。
但是，被标记为 {deftech (key := "protected")}[受保护] 的声明（即带有 {keyword}`protected` {ref "declaration-modifiers"}[修饰符] 的声明）在打开命名空间时并不会被带入作用域。
关于根据当前命名空间和打开的命名空间解析标识符的规则，详见 {ref "identifiers-and-resolution"}[标识符作为项的一节]。


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
```lean (name := notOkTea) +error
#check tea
```
```leanOutput notOkTea
Unknown identifier `tea`
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

如果直接在 `HotDrink` 命名空间中定义函数，该函数体会在当前命名空间为 `HotDrink` 的情况下进行精译。
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


{keywordOf Lean.Parser.Command.open}`open` 命令用于打开一个命名空间，使其内容可以在当前作用域内使用。
打开命名空间有多种变化方式，便于灵活管理本地作用域。


:::syntax command (title := "打开命名空间")
{keywordOf Lean.Parser.Command.open}`open` 命令用于打开一个命名空间：
```grammar
open $_:openDecl
```
:::


:::syntax Lean.Parser.Command.openDecl (title := "打开整个命名空间") (label := "open declaration")
用一个或多个标识符组成序列，会顺序将这些命名空间打开：
```grammar
$_:ident $_:ident*
```
每个命名空间都相对于所有已打开的命名空间解析，得到一组命名空间。
在处理下一个命名空间之前，会先顺序打开这一组命名空间的所有成员。
:::


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

```lean +error (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
Unknown identifier `a1`
```
```leanOutput dotted
Unknown identifier `a4`
```
```leanOutput dotted
Unknown identifier `a5`
```
打开 `A.B` 后，`A.B.C` 可以作为 `C` 来访问，而 `_root_.C` 也同样如此，因此后续 open 的 `C` 实际会打开这两个名字。
:::


:::syntax Lean.Parser.Command.openDecl (title := "隐藏名字") (label := "open declaration")
{keyword}`hiding` 声明用来指定在打开命名空间时哪些名字_不能_被带入作用域。
与打开整个命名空间不同的是，这时提供的标识符必须唯一地指明待打开命名空间。
```grammar
$_:ident hiding $x:ident $x:ident*
```
:::

```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B hiding x
```


:::syntax Lean.Parser.Command.openDecl (title := "重命名") (label := "open declaration")
{keyword}`renaming` 声明允许将打开的命名空间中的部分名字重命名；在当前作用域中可用新名字访问它们。
此处提供的标识符必须唯一地指定要打开的命名空间。
```grammar
$_:ident renaming $[$x:ident → $x:ident],*
```

ASCII 箭头（`->`）也可以替代 Unicode 箭头（`→`）。
:::

```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x → y
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x -> y
```


:::syntax Lean.Parser.Command.openDecl (title := "限制引入名称") (label := "open declaration")
用圆括号括住一组名字表示只将括号内列出的名字带入作用域。
```grammar
$_:ident ($x:ident $x*)
```
指定的命名空间会加到当前所有已打开命名空间中，每个名字会在所有这些命名空间中查找。
列出的每个名字都必须是明确且唯一的，也就是说每个名字只能在所有考虑到的命名空间中存在于唯一一处。
:::

```lean -show -keep
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
/-- error: ambiguous identifier `y`, possible interpretations: [B.y, B.y] -/
#check_msgs in
open B (y)
```

:::syntax Lean.Parser.Command.openDecl (title := "仅打开受限定声明") (label := "open declaration")
{keyword}`scoped` 关键字用于只打开指定命名空间中的所有受限定属性、类型类实例和语法扩展，但不会将实际名字带入作用域。
```grammar
scoped $x:ident $x*
```
:::


::::example "打开受限定声明"
下面例子中，在命名空间 `NS` 下定义了一个受限定的 {tech (key := "notation")}[符号扩展] 以及一个定义：
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
```lean +error (name := nothree)
def y := three
```
```leanOutput nothree
Unknown identifier `three`
```
:::
::::


# 导出名称
%%%
tag := "exported-names"
%%%


{deftech (key := "exporting")}_导出_一个名字，就是将其引入到当前命名空间内。
与定义不同，导出的名字是完全透明的：在使用时会直接解析到原始名字。
将名字导出到根命名空间，则可以直接不加限定地访问它；Lean 标准库会这样做，例如 {name}`Option` 的构造子，或像 {name}`get` 这样的关键类型类方法。


:::syntax command (title := "导出名称")
{keyword}`export` 命令可以将其他命名空间中的名字添加到当前命名空间，就好像它们原本就是在这里声明的一样。
当当前命名空间被打开时，这些导出的名字也会被带入作用域。

```grammar
export $_ ($_*)
```

内部实现上，导出的名字会注册成其目标的别名。
在 {tech (key := "kernel")}[内核] 看来，只有原始名字存在；{tech (key := "elaborator")}[精译器] 在 {tech (key := "resolve")}[解析] 标识符到名字的过程中负责处理别名。
:::


:::example "导出名称"
声明 {tech (key := "inductive type")}[归纳类型] {name}`Veg.Leafy` 的同时，也声明了构造子 {name}`Veg.Leafy.spinach` 和 {name}`Veg.Leafy.cabbage`：
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
```
第一次 {keyword}`export` 命令将 {name}`Veg.Leafy.spinach` 作为 {name}`Veg.spinach` 引入作用域，因为此时 {tech (key := "current namespace")}[当前命名空间] 是 `Veg`。
第二次导出将 {name}`Veg.Leafy.cabbage` 引入根命名空间，可以直接使用 {name}`cabbage`。
:::
