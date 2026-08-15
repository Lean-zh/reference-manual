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


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "属性" =>
%%%
tag := "attributes"
file := "Attributes"
htmlSplit := .never
%%%

{deftech (key := "Attributes")}_属性_是施加在声明上的一组可扩展编译期注解。
它们既可以作为{ref "declaration-modifiers"}[声明修饰符]添加，也可以用 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令添加。

属性可以在编译期表中将信息与声明关联起来（包括{tech (key := "custom simp sets")}[自定义 simp 集]、{tech (key := "macros")}[宏]和{tech (key := "instances")}[实例]），可以对定义施加额外要求（例如，当定义的类型不是类型类时拒绝它），也可以生成额外代码。
与项、命令和策略的{tech (key := "macros")}[宏]及自定义{tech (key := "elaborators")}[精译器]一样，属性的{tech (key := "syntax category")}[语法类别] `attr` 也被设计为可扩展的；有一张表将每个扩展映射到解释它的编译期程序。

属性以{deftech (key := "attribute instances")}_属性实例_的形式应用；属性实例将一个作用域指示符与一个属性配成一对。
它们既可以出现在作为声明修饰符的属性中，也可以出现在独立的 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令中。

:::syntax Lean.Parser.Term.attrInstance (title := "属性实例")
```grammar
$_:attrKind $_:attr
```

`attrKind` 是可选的{ref "scoped-attributes"}[属性作用域]关键字 {keyword}`local` 或 {keyword}`scoped`。
它们控制属性效果的可见范围。
属性本身可以是可扩展{tech (key := "syntax category")}[语法类别] `attr` 中的任何内容。
:::

属性系统非常强大：属性可以将任意信息与声明关联起来，并生成任意数量的辅助声明。
这会带来一些设计上的取舍：存储这些信息会占用空间，检索它们则会耗费时间。
因此，有些属性只能应用于定义该声明的模块中的声明。
这样，在大型项目中查询会快得多，因为无需检查所有模块的数据。
每个属性自行决定如何存储其元数据，以及对特定用例而言，灵活性与性能之间怎样取舍才合适。

# 作为修饰符的属性
%%%
tag := "The-Lean-Language-Reference--Attributes--Attributes-as-Modifiers"
%%%

属性可以作为{ref "declaration-modifiers"}[声明修饰符]添加到声明上。
它们放在文档注释与可见性修饰符之间。

:::syntax Lean.Parser.Term.attributes -open (title := "属性")
```grammar
@[$_:attrInstance,*]
```
:::

# {keyword}`attribute` 命令
%%%
tag := "The-Lean-Language-Reference--Attributes--The--attribute--Command"
%%%

{keywordOf Lean.Parser.Command.attribute}`attribute` 命令可用于修改声明的属性。
一些用法示例包括：
 * 通过添加 {attr}`instance`，在局部作用域中将已有声明注册为{tech (key := "instance")}[实例]；
 * 使用 {attr}`simp` 或 {attr}`ext`，将已有定理标记为 simp 引理或外延性引理；以及
 * 暂时从默认{tech (key := "simp set")}[simp 集]中移除一个 simp 引理。

:::syntax command (title := "修改属性")
{keywordOf Lean.Parser.Command.attribute}`attribute` 命令为已有声明添加属性或从中移除属性。
标识符是要修改属性的名称。
```grammar
attribute [$_,*] $_
```
:::

除了用于向已有声明添加属性的属性实例之外，有些属性还可以被移除；这称为{deftech (key := "erasing")}_擦除_属性。
在属性名称前加上 `-` 即可擦除该属性。
不过，并非所有属性都支持擦除。

:::syntax Lean.Parser.Command.eraseAttr (title := "擦除属性")
在属性名称前加上 `-` 即可擦除该属性。

```grammar
-$_:ident
```
:::


# 有作用域的属性
%%%
tag := "scoped-attributes"
%%%

许多属性可以应用于特定作用域。
这决定了属性的效果是仅在当前小节作用域中可见、在打开当前命名空间的作用域内可见，还是处处可见。
这些作用域指示也用于控制{ref "syntax-rules"}[语法扩展]和{ref "instance-attribute"}[类型类实例]。
每个属性都负责精确定义这些术语对其特定效果意味着什么。

:::syntax attrKind -open (title := "属性作用域") (alias := Lean.Parser.Term.attrKind)
具有全局作用域的声明（默认情形）会在建立它们的{tech (key := "module")}[模块]被传递导入时生效。
不写其他作用域修饰符即表示全局作用域。
```grammar
```

具有局部作用域的声明只在建立它们的{tech (key := "section scope")}[小节作用域]范围内生效。
```grammar
local
```

具有命名空间作用域的声明会在建立它们的{tech (key := "current namespace")}[命名空间]被打开时生效。
```grammar
scoped
```
:::
