/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Namespaces
import Manual.Coercions


import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

-- #doc (Manual) "Namespaces and Sections" =>
-- %%%
-- tag := "namespaces-sections"
-- htmlSplit := .never
-- %%%

#doc (Manual) "命名空间与区段" =>
%%%
file := "Namespaces and Sections"
tag := "namespaces-sections"
htmlSplit := .never
%%%

/-
Names are organized into hierarchical {deftech}_namespaces_, which are collections of names.
Namespaces are the primary means of organizing APIs in Lean: they provide an ontology of operations, grouping related items.
Additionally, while this is not done by giving them names in the namespace, the effects of features such as {ref "language-extension"}[syntax extensions], {tech}[instances], and {tech}[attributes] can be attached to a namespace.
-/

名字会被组织到分层的 {deftech key := "namespace"}_命名空间_ 里，命名空间为名字的集合。
在 Lean 中，命名空间是组织 API 的主要方式：它为操作提供本体论，并将相关项聚合起来。
此外，虽然不是通过将名字直接放入命名空间的方式，但一些特性（比如 {ref "language-extension"}[语法扩展]、{tech key := "instance"}[实例] 以及 {tech key := "attribute"}[属性]）的效果可以被“附着”到某个命名空间。

/-
Sorting operations into namespaces organizes libraries conceptually, from a global perspective.
Any given Lean file will, however, typically not use all names equally.
{tech}[Sections] provide a means of ordering a local view of the globally-available collection of names, as well as a way to precisely control the scope of compiler options along with language extensions, instances, and attributes.
They also allow parameters shared by many declarations to be declared centrally and propagated as needed using the {keywordOf Lean.Parser.Command.variable}`variable` command.
-/

通过将操作整理到命名空间，使得库的结构在概念上得到全局的梳理。然而，在实际的 Lean 文件中，通常并不会同等地使用所有名字。
{tech key := "section"}[区段] 提供了在局部视图下组织全局名字集的方法，也能精准控制编译器选项、语言扩展、实例和属性等的作用域。
区段也允许将多个声明共享的参数集中声明，并可借助 {keywordOf Lean.Parser.Command.variable}`variable` 命令按需传播。

{include 1 Manual.Language.Namespaces}

/-
# Section Scopes
%%%
tag := "scopes"
%%%
-/


# 区段作用域（Section Scopes）
%%%
file := "Section Scopes"
tag := "scopes"
%%%

/-
Many commands have an effect for the current {deftech}[_section scope_] (sometimes just called "scope" when clear).
Every Lean module has a section scope.
Nested scopes are created via the {keywordOf Lean.Parser.Command.namespace}`namespace` and {keywordOf Lean.Parser.Command.section}`section` commands, as well as the {keywordOf Lean.Parser.Command.in}`in` command combinator.
-/

许多命令会对当前 {deftech key := "section scope"}_区段作用域_产生影响（有时在明确语境下简称为“作用域”）。
每个 Lean 模块都自带一个区段作用域。
通过 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令、{keywordOf Lean.Parser.Command.section}`section` 命令，以及 {keywordOf Lean.Parser.Command.in}`in` 命令组合子，可以创建嵌套的作用域。

/-
The following data are tracked in section scopes:

: The Current Namespace

  The {deftech}_current namespace_ is the namespace into which new declarations will be defined.
  Additionally, {tech (key:="resolve")}[name resolution] includes all prefixes of the current namespace in the scope for global names.

: Opened Namespaces

  When a namespace is {deftech}_opened_, its names become available without an explicit prefix in the current scope.
  Additionally, scoped attributes and {ref "syntax-rules"}[scoped syntax extensions] in namespaces that have been opened are active in the current section scope.

: Options

  Compiler options are reverted to their original values at the end of the scope in which they were modified.

: Section Variables

  {tech}[Section variables] are names (or {tech}[instance implicit] parameters) that are automatically added as parameters to definitions.
  They are also added as universally-quantified assumptions to theorems when they occur in the theorem's statement.
-/

区段作用域中追踪如下数据：

: 当前命名空间（The Current Namespace）

  {deftech key := "current namespace"}_当前命名空间_ 指新声明将被定义到的命名空间。
  此外，{tech key := "resolve"}[名字解析] 包括所有当前命名空间前缀，以作为全局名字可用的作用域一部分。

: 已“开放”的命名空间（Opened Namespaces）

  当一个命名空间被 {deftech key := "opened"}_开放_ 时，其名字无需显式前缀即可在当前作用域可用。
  此外，被开放命名空间下的限定属性及 {ref "syntax-rules"}[作用域内语法扩展] 在当前区段作用域内也会生效。

: 选项（Options）

  编译器选项在其被更改的作用域结束时，会复原为原来的值。

: 区段变量（Section Variables）

  {tech key := "section variable"}[区段变量]，即自动加到定义里的名字（或 {tech key := "instance implicit"}[实例隐式] 参数）。
  当区段变量出现在定理陈述中时，也会自动加为定理的全称假设。

/-
## Controlling Section Scopes
%%%
tag := "scope-commands"
%%%
-/

## 控制区段作用域
%%%
tag := "scope-commands"
%%%

/-
The {keywordOf Lean.Parser.Command.section}`section` command creates a new {deftech}[section] scope, but does not modify the current namespace, opened namespaces, or section variables.
Changes made to the section scope are reverted when the section ends.
Sections may optionally be named; the {keywordOf Lean.Parser.Command.end}`end` command that closes a named section must use the same name.
If section names have multiple components (that is, if they contain `.`-separated names), then multiple nested sections are introduced.
Section names have no other effect, and are a readability aid.
-/

{keywordOf Lean.Parser.Command.section}`section` 命令会新建一个 {deftech key := "section"}[区段] 作用域，但并不会修改当前命名空间、已开放命名空间或区段变量。
所有对区段作用域做出的更改，在区段结束时将被还原。
区段可以选择命名；关闭区段的 {keywordOf Lean.Parser.Command.end}`end` 命令需使用相同的名字。
如果区段名含有多个部分（即有 `.`分隔），则会引入多层嵌套区段。
区段名字不会产生其它效果，仅是为了可读性和方便重构。

/-
:::syntax command (title := "Sections")
The {keywordOf Lean.Parser.Command.section}`section` command creates a section scope that lasts either until an `end` command or the end of the file.
```grammar
section $[$id:ident]?
```
:::
-/

:::syntax command (title := "区段")
{keywordOf Lean.Parser.Command.section}`section` 命令创建一个区段作用域，该作用域会持续到 `end` 命令或者文件结尾为止。
```grammar
section $[$id:ident]?
```
:::

/-
:::example "Named Section"

The name {name Greetings.english}`english` is defined in the `Greetings` namespace.

```lean
def Greetings.english := "Hello"
```

Outside its namespace, it cannot be evaluated.

```lean (error := true) (name := english1)
#eval english
```
```leanOutput english1
unknown identifier 'english'
```

Opening a section allows modifications to the global scope to be contained.
This section is named `Greetings`.
```lean
section Greetings
```

Even though the section name matches the definition's namespace, the name is not in scope because section names are purely for readability and ease of refactoring.

```lean (error := true)  (name := english2)
#eval english
```
```leanOutput english2
unknown identifier 'english'
```

Opening the namespace `Greetings` brings {name}`Greetings.english` as {name Greetings.english}`english`:


```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

The section's name must be used to close it.

```lean (error := true) (name := english4) (keep := false)
end
```
```leanOutput english4
invalid 'end', name is missing (expected Greetings)
```

```lean
end Greetings
```

When the section is closed, the effects of the {keywordOf Lean.Parser.Command.open}`open` command are reverted.
```lean (error := true)  (name := english5)
#eval english
```
```leanOutput english5
unknown identifier 'english'
```
:::
-/


:::example "命名区段"

名字 {name Greetings.english}`english` 是在 `Greetings` 命名空间下定义的。

```lean
def Greetings.english := "Hello"
```

在其命名空间外无法直接访问。

```lean (error := true) (name := english1)
#eval english
```
```leanOutput english1
unknown identifier 'english'
```

打开一个区段可以让对全局作用域的修改被限制在其中。
下例区段名为 `Greetings`。
```lean
section Greetings
```

即使区段名和定义中的命名空间一致，由于区段名字仅作为可读和重构辅助，这个名字仍未在作用域内：

```lean (error := true)  (name := english2)
#eval english
```
```leanOutput english2
unknown identifier 'english'
```

打开 `Greetings` 命名空间后，{name}`Greetings.english` 就能以 {name Greetings.english}`english` 名称出现于当前作用域：


```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

关闭区段时，区段的名字必须被使用：

```lean (error := true) (name := english4) (keep := false)
end
```
```leanOutput english4
invalid 'end', name is missing (expected Greetings)
```

```lean
end Greetings
```

当区段被关闭时，通过 {keywordOf Lean.Parser.Command.open}`open` 命令带来的影响会恢复：

```lean (error := true)  (name := english5)
#eval english
```
```leanOutput english5
unknown identifier 'english'
```
:::

/-
The {keywordOf Lean.Parser.Command.namespace}`namespace` command creates a new section scope.
Within this section scope, the current namespace is the name provided in the command, interpreted relative to the current namespace in the surrounding section scope.
Like sections, changes made to the section scope are reverted when the namespace's scope ends.
-/

{keywordOf Lean.Parser.Command.namespace}`namespace` 命令也会新建一个区段作用域。
在这个区段作用域下，当前命名空间会变为所提供的名字（相对周围的当前命名空间）。
如同区段一样，对区段作用域的更改会在命名空间关闭时还原。

/-
To close a namespace, the {keywordOf Lean.Parser.Command.end}`end` command requires a suffix of the current namespace, which is removed.
All section scopes introduced by the {keywordOf Lean.Parser.Command.namespace}`namespace` command that introduced part of that suffix are closed.
-/

要关闭命名空间，{keywordOf Lean.Parser.Command.end}`end` 命令需提供当前命名空间的某个后缀，关闭后该后缀就会被移除。
所有由 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令引入、并属于该后缀的区段作用域也会一起关闭。

/-
:::syntax command (title := "Namespace Declarations")
The `namespace` command modifies the current namespace by appending the provided identifier.

creates a section scope that lasts either until an {keywordOf Lean.Parser.Command.end}`end` command or the end of the file.
```grammar
namespace $id:ident
```
:::
-/

:::syntax command (title := "命名空间声明")
`namespace` 命令通过追加指定标识符来修改当前命名空间。

会创建一个区段作用域，该作用域会持续到 {keywordOf Lean.Parser.Command.end}`end` 命令或者文件结尾为止。
```grammar
namespace $id:ident
```
:::

/-
:::syntax command (title := "Section and Namespace Terminators")
Without an identifier, {keywordOf Lean.Parser.Command.end}`end` closes the most recently opened section, which must be anonymous.
```grammar
end
```

With an identifier, it closes the most recently opened section section or namespace.
If it is a section, the identifier be a suffix of the concatenated names of the sections opened since the most recent {keywordOf Lean.Parser.Command.namespace}`namespace` command.
If it is a namespace, then the identifier must be a suffix of the current namespace's extensions since the most recent {keywordOf Lean.Parser.Command.section}`section` that is still open; afterwards, the current namespace will have had this suffix removed.
```grammar
end $id:ident
```
:::
-/

:::syntax command (title := "区段与命名空间终止")
不带标识符时，{keywordOf Lean.Parser.Command.end}`end` 会关闭最近打开的匿名区段。
```grammar
end
```

W带标识符时，会关闭最近打开的区段或者命名空间。
若是区段，则标识符必须是自上次 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令以来所打开区段名拼接的后缀。
若是命名空间，则标识符必须是自上次未闭合的 {keywordOf Lean.Parser.Command.section}`section` 以来当前命名空间扩展的后缀；之后当前命名空间会移除此后缀。
```grammar
end $id:ident
```
:::

/-
The {keywordOf Lean.Parser.Command.mutual}`end` that closes a {keywordOf Lean.Parser.Command.mutual}`mutual` block is part of the syntax of {keywordOf Lean.Parser.Command.mutual}`mutual`, rather than the {keywordOf Lean.Parser.Command.end}`end` command.
-/

{keywordOf Lean.Parser.Command.mutual}`end` 用于关闭 {keywordOf Lean.Parser.Command.mutual}`mutual` 块，它是 {keywordOf Lean.Parser.Command.mutual}`mutual` 语法本身的一部分，而不是 {keywordOf Lean.Parser.Command.end}`end` 命令。

/-
:::example "Nesting Namespaces and Sections"
Namespaces and sections may be nested.
A single {keywordOf Lean.Parser.Command.end}`end` command may close one or more namespaces or one or more sections, but not a mix of the two.

After setting the current namespace to `A.B.C` with two separate commands, `B.C` may be removed with a single {keywordOf Lean.Parser.Command.end}`end`:
```lean
namespace A.B
namespace C
end B.C
```
At this point, the current namespace is `A`.

Next, an anonymous section and the namespace `D.E` are opened:
```lean
section
namespace D.E
```
At this point, the current namespace is `A.D.E`.
An {keywordOf Lean.Parser.Command.end}`end` command cannot close all three due to the intervening section:
```lean (error := true) (name := endADE) (keep := false)
end A.D.E
```
```leanOutput endADE
invalid 'end', name mismatch (expected «».D.E)
```
Instead, namespaces and sections must be ended separately.
```lean
end D.E
end
end A
```
:::
-/

:::example "嵌套命名空间与区段"
命名空间与区段可以嵌套使用。
一次 {keywordOf Lean.Parser.Command.end}`end` 命令可以关闭一个或多个命名空间，或者一个或多个区段，但不能混合关闭两者。

通过两个单独命令将当前命名空间设为 `A.B.C` 后，可以用一次 {keywordOf Lean.Parser.Command.end}`end` 指定 `B.C` 后缀批量关闭：

```lean
namespace A.B
namespace C
end B.C
```
此时，当前命名空间变为 `A`。

接下来，打开一个匿名区段和命名空间 `D.E`：
```lean
section
namespace D.E
```
此时，当前命名空间变为 `A.D.E`。
此时如果试图用 {keywordOf Lean.Parser.Command.end}`end` 一次性关闭全部三者，会因为中间有区段导致失败：
```lean (error := true) (name := endADE) (keep := false)
end A.D.E
```
```leanOutput endADE
invalid 'end', name mismatch (expected «».D.E)
```
因此需要分别终止命名空间和区段：
```lean
end D.E
end
end A
```
:::

/-
Rather than opening a section for a single command, the {keywordOf Lean.Parser.Command.in}`in` combinator can be used to create single-command section scope.
The {keywordOf Lean.Parser.Command.in}`in` combinator is right-associative, allowing multiple scope modifications to be stacked.
-/

如果只需对单个命令临时开放作用域，可以使用 {keywordOf Lean.Parser.Command.in}`in` 命令组合子来创建单条命令的区段作用域。
{keywordOf Lean.Parser.Command.in}`in` 具备右结合性，可以组合多层作用域调整。

/-
:::syntax command (title := "Local Section Scopes")
The `in` command combinator introduces a section scope for a single command.
```grammar
$c:command in
$c:command
```
:::
-/

:::syntax command (title := "局部区段作用域")
`in` 命令组合子为单个命令引入区段作用域。
```grammar
$c:command in
$c:command
```
:::

/-
:::example "Using {keywordOf Lean.Parser.Command.in}`in` for Local Scopes"
The contents of a namespace can be made available for a single command using {keywordOf Lean.Parser.Command.in}`in`.
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

After the single command, the effects of {keywordOf Lean.Parser.Command.open}`open` are reverted.

```lean (error := true) (name := noCake)
#eval cupcake
```
```leanOutput noCake
unknown identifier 'cupcake'
```
:::
-/

:::example "利用 {keywordOf Lean.Parser.Command.in}`in` 创建局部作用域"
可以使用 {keywordOf Lean.Parser.Command.in}`in` 让命名空间内容只在单个命令中可见：
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

该命令之后，{keywordOf Lean.Parser.Command.open}`open` 的影响即恢复：

```lean (error := true) (name := noCake)
#eval cupcake
```
```leanOutput noCake
unknown identifier 'cupcake'
```
:::

/-
## Section Variables
%%%
tag := "section-variables"
%%%
-/

## 区段变量（Section Variables）
%%%
tag := "section-variables"
%%%

/-
{deftech}_Section variables_ are parameters that are automatically added to declarations that mention them.
This occurs whether or not the option {option}`autoImplicit` is {lean}`true`.
Section variables may be implicit, strict implicit, or explicit; instance implicit section variables are treated specially.
-/

{deftech key := "section variable"}_区段变量_ 指自动作为参数加到所有提及它们的声明里的参数。
不论 {option}`autoImplicit` 选项是否为 {lean}`true`，都适用。
区段变量可以是隐式、严格隐式或者显式参数，实例隐式参数则有特别处理。

/-
When the name of a section variable is encountered in a non-theorem declaration, it is added as a parameter.
Any instance implicit section variables that mention the variable are also added.
If any of the variables that were added depend on other variables, then those variables are added as well; this process is iterated until no more dependencies remain.
All section variables are added in the order in which they are declared, before all other parameters.
Section variables are added only when they occur in the _statement_ of a theorem.
Otherwise, modifying the proof of a theorem could change its statement if the proof term made use of a section variable.
-/

如果在非定理声明中遇到了区段变量，其就会被自动加为参数。
其中若有 “实例隐式” 区段变量引用了该变量，它们也会被自动加上。
如果新增的变量又依赖其它变量，那么那些变量也会被递归添加；这一过程会持续直到不再有新依赖为止。
所有区段变量按照声明顺序，在其它参数之前加入。
只有当区段变量在定理的陈述中出现时，才会被自动添加到定理。
否则，如果在证明项中更改依赖区段变量，可能会导致定理陈述发生变化。

/-
Variables are declared using the {keywordOf Lean.Parser.Command.variable}`variable` command.
-/

区段变量可以通过 {keywordOf Lean.Parser.Command.variable}`variable` 命令声明。

/-
:::syntax command (title := "Variable Declarations")
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::
-/

:::syntax command (title := "变量声明")
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::

/-
The bracketed binders allowed after `variable` match the {ref "bracketed-parameter-syntax"}[syntax used in definition headers].
-/

`variable` 后允许的带括号参数（bracketed binders）语法与 {ref "bracketed-parameter-syntax"}[定义头的语法]一致。

/-
:::example "Section Variables"
In this section, automatic implicit parameters are disabled, but a number of section variables are defined.

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```

Because automatic implicit parameters are disabled, the following definition fails:
```lean (error := true) (name := secvars) (keep := false)
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
unknown identifier 'β'
```

On the other hand, not even {lean}`xs` needs to be written directly in the definition:

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```

:::
-/

:::example "区段变量"
在下例区段中，自动隐式参数被禁用，并定义了一组区段变量。

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```

由于自动隐式参数已禁用，下面这个定义会失败：
```lean (error := true) (name := secvars) (keep := false)
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
unknown identifier 'β'
```

另一方面，即便在定义时不写 {lean}`xs`，也能使用它：

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```

:::

/-
To add a section variable to a theorem even if it is not explicitly mentioned in the statement, mark the variable with the {keywordOf Lean.Parser.Command.include}`include` command.
All variables marked for inclusion are added to all theorems.
The {keywordOf Lean.Parser.Command.omit}`omit` command removes the inclusion mark from a variable; it's typically a good idea to use it with {keywordOf Lean.Parser.Command.in}`in`.
-/

如果希望即使区段变量没有在定理声明里显式提及时也自动加到定理上，可以用 {keywordOf Lean.Parser.Command.include}`include` 命令标记该变量。
所有被标记的变量都会被无条件添加到所有定理中。
{keywordOf Lean.Parser.Command.omit}`omit` 命令可用于去除变量的 include 标记；通常建议配合 {keywordOf Lean.Parser.Command.in}`in` 使用。

/-
```lean (show := false)
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```

:::::example "Included and Omitted Section Variables"

This section's variables include a predicate as well as everything needed to prove that it holds universally, along with a useless extra assumption.

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

However, only {lean}`p` is added to this theorem's assumptions, so it cannot be proved.
```lean (error := true) (keep := false)
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

The {keywordOf Lean.Parser.Command.include}`include` command causes the additional assumptions to be added unconditionally:
```lean (keep := false) (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
Because the spurious assumption {lean}`pFifteen` was inserted, Lean issues a warning:
```leanOutput lint
automatically included section variable(s) unused in theorem 'p_all':
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...
note: this linter can be disabled with `set_option linter.unusedSectionVars false`
```

This can be avoided by using {keywordOf Lean.Parser.Command.omit}`omit`to remove {lean}`pFifteen`:
```lean (keep := false)
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean (show := false)
end
```
-/

```lean (show := false)
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```

:::::example "Included and Omitted Section Variables"

本区段的变量包含了一个谓词以及用于证明其适用于所有自然数的条件，还加了一个多余的假设。

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

但下例定理默认只加了 {lean}`p` 这个变量，导致无法证明：
```lean (error := true) (keep := false)
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

{keywordOf Lean.Parser.Command.include}`include` 命令会无条件插入额外假设：
```lean (keep := false) (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
由于插入了无意义的 {lean}`pFifteen`，Lean 会发出警告：
```leanOutput lint
automatically included section variable(s) unused in theorem 'p_all':
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...
note: this linter can be disabled with `set_option linter.unusedSectionVars false`
```

为避免这个问题，可用 {keywordOf Lean.Parser.Command.omit}`omit` 去掉 {lean}`pFifteen` 的 include 标记：
```lean (keep := false)
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean (show := false)
end
```
