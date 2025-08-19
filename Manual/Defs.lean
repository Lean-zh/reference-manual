/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.RecursiveDefs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

-- #doc (Manual) "Definitions" =>
-- %%%
-- tag := "definitions"
-- %%%

#doc (Manual) "定义" =>
%%%
file := "Definitions"
tag := "definitions"
%%%


/-
The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a {tech}[signature].
With the exception of {keywordOf Lean.Parser.Command.example}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].
-/

Lean 中以下命令属于“定义式（definition-like）”：{TODO}[以命令名形式渲染（类似策略索引）]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

这些命令都会促使 Lean 的 {tech key := "elaborator"}[繁释器] 基于其 {tech key := "signature"}[签名] 对一个项进行繁释。
除 {keywordOf Lean.Parser.Command.example}`example`（其结果会被丢弃）之外，繁释得到的 Lean 核心语言表达式都会保存到环境中以供后续使用。
{keywordOf Lean.Parser.Command.declaration}`instance` 命令见 {ref "instance-declarations"}[实例声明] 一节。


/-
# Modifiers
%%%
tag := "declaration-modifiers"
%%%
-/

# 修饰符（Modifiers）
%%%
file := "Modifiers"
tag := "declaration-modifiers"
%%%

/-
Declarations accept a consistent set of {deftech}_modifiers_, all of which are optional.
Modifiers change some aspect of the declaration's interpretation; for example, they can add documentation or change its scope.
The order of modifiers is fixed, but not every kind of declaration accepts every kind of modifier.
-/

声明支持一组一致的 {deftech key := "modifiers"}_修饰符_，它们均为可选。
修饰符会改变声明在解释上的某些方面；例如可以添加文档，或改变其作用域。
修饰符的顺序是固定的，但并非所有种类的声明都接受所有种类的修饰符。

/-
:::syntax declModifiers (open := false) (alias:=Lean.Parser.Command.declModifiers) (title := "Declaration Modifiers")
Modifiers consist of the following, in order, all of which are optional:
 1. a documentation comment,
 2. a list of {tech}[attributes],
 3. namespace control, specifying whether the resulting name is {tech}[private] or {tech}[protected],
 4. the {keyword}`noncomputable` keyword, which exempts a definition from compilation,
 5. the {keyword}`unsafe` keyword, and
 6. a recursion modifier {keyword}`partial` or {keyword}`nonrec`, which disable termination proofs or disallow recursion entirely.
```grammar
$[$_:docComment]?
$[$_:attributes]?
$[$_]?
$[noncomputable]?
$[unsafe]?
$[$_]?
```
:::
-/

:::syntax declModifiers (open := false) (alias:=Lean.Parser.Command.declModifiers) (title := "声明修饰符")
修饰符按如下顺序出现，且均为可选：
 1. 文档注释；
 2. {tech key := "attributes"}[属性] 列表；
 3. 命名空间控制，指定结果名字是否为 {tech key := "private"}[私有] 或 {tech key := "protected"}[受保护]；
 4. {keyword}`noncomputable` 关键字，将定义排除在编译之外；
 5. {keyword}`unsafe` 关键字；
 6. 递归修饰符 {keyword}`partial` 或 {keyword}`nonrec`，分别禁用终止性证明或完全禁止递归。
```grammar
$[$_:docComment]?
$[$_:attributes]?
$[$_]?
$[noncomputable]?
$[unsafe]?
$[$_]?
```
:::

/-
{deftech}_Documentation comments_ are used to provide in-source API documentation for the declaration that they modify.
Documentation comments are not, in fact comments: it is a syntax error to put a documentation comment in a position where it is not processed as documentation.
They also occur in positions where some kind of text is required, but string escaping would be onerous, such as the desired messages on the {keywordOf Lean.guardMsgsCmd}`#guard_msgs` command.
-/

{deftech key := "documentation comment"}_文档注释_ 用于为其修饰的声明提供源码中的 API 文档。
需要注意，文档注释并不是真正意义上的“注释”：如果把文档注释放在不会被当作文档处理的位置，会产生语法错误。
在某些需要文本但转义会很繁琐的场景，文档注释也很有用，例如 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令中的期望消息。


-- :::syntax docComment (open:=false) (title := "Documentation Comments")

-- Documentation comments are like ordinary block comments, but they begin with the sequence `/--` rather than `/-`; just like ordinary comments, they are terminated with `-/`.

-- ```grammar
-- /--
-- ...
-- -/
-- ```
-- :::


:::syntax docComment (open:=false) (title := "文档注释")
文档注释与普通块注释相似，但它以 `/--` 开始（而非常规块注释的 `/-`）；与普通注释一样，以 `-/` 结束。
```grammar
/--
...
-/
```
:::

/-
Attributes are an extensible collection of modifiers that associate additional information with declarations.
They are described in a {ref "attributes"}[dedicated section].
-/

属性是可扩展的一类修饰符，用于将附加信息关联到声明上。
它们在 {ref "attributes"}[属性专章] 中有详细说明。

/-
If a declaration is marked {deftech key:="private"}[{keyword}`private`], then it is not accessible outside the module in which it is defined.
If it is {keyword}`protected`, then opening its namespace does not bring it into scope.
-/

若声明被标记为 {deftech key := "private"}[{keyword}`private`]，则无法在其定义所在模块之外访问。
若声明为 {keyword}`protected`，则打开其命名空间时不会将该名字带入作用域。

/-
Functions marked {keyword}`noncomputable` are not compiled and cannot be executed.
Functions must be noncomputable if they use noncomputable reasoning principles such as the axiom of choice or excluded middle to produce data that is relevant to the answer that they return, or if they use features of Lean that are exempted from code generation for efficiency reasons, such as {tech}[recursors].
Noncomputable functions are very useful for specification and reasoning, even if they cannot be compiled and executed.
-/

被标记为 {keyword}`noncomputable` 的函数不会被编译，因而也不能执行。
当函数使用了非可计算的推理原则（例如选择公理或排中律）来产生与其返回结果相关的数据，或使用了因效率原因而不参与代码生成的 Lean 特性（如 {tech key := "recursor"}[递归子]）时，该函数必须是 noncomputable。
即使无法编译和执行，noncomputable 函数在规范化与推理中依然十分有用。

/-
The {keyword}`unsafe` marker exempts a definition from kernel checking and enables it to access features that may undermine Lean's guarantees.
It should be used with great care, and only with a thorough understanding of Lean's internals.
-/

{keyword}`unsafe` 标记会使定义跳过内核检查，并允许其访问可能破坏 Lean 保证的功能。
使用该标记务必小心，仅在深入理解 Lean 内部机制时使用。


/-
# Headers and Signatures
%%%
tag := "signature-syntax"
%%%
-/

# 头部与签名（Headers and Signatures）
%%%
file := "Headers and Signatures"
tag := "signature-syntax"
%%%

/-
The {deftech}[_header_] of a definition or declaration consists of the constant being declared or defined, if relevant, together with its signature.
The {deftech}_signature_ of a constant specifies how it can be used.
The information present in the signature is more than just the type, including information such as {tech key:="universe parameter"}[universe level parameters] and the default values of its optional parameters.
In Lean, signatures are written in a consistent format in different kinds of declarations.
-/

定义或声明的 {deftech key := "header"}_头部_（若有）由待声明/定义的常量以及其签名组成。
常量的 {deftech key := "signature"}_签名_ 指定了它可以如何被使用。
签名中包含的不仅仅是类型本身的信息，还包括例如 {tech key := "universe parameter"}[宇宙层级参数]、可选参数的默认值等。
在 Lean 中，不同类型的声明均使用一致的格式来书写签名。

/-
## Declaration Names
-/

## 声明名称（Declaration Names）

/-
Most headers begin with a {deftech}_declaration name_, which is followed by the signature proper: its parameters and the resulting type.
A declaration name is a name that may optionally include universe parameters.
-/

大多数头部以一个 {deftech key := "declaration name"}_声明名称_ 开始，随后是其真正的签名：参数列表以及结果类型。
一个声明名称可以可选地包含宇宙层级参数。

/-
:::syntax declId (open := false) (title := "Declaration Names")
Declaration names without universe parameters consist of an identifier:
```grammar
$_:ident
```

Declaration names with universe parameters consist of an identifier followed by a period and one or more universe parameter names in braces:
```grammar
$_.{$_, $_,*}
```
These universe parameter names are binding occurrences.
:::
-/

:::syntax declId (open := false) (title := "声明名称")
不带宇宙参数的声明名称仅由一个标识符组成：
```grammar
$_:ident
```

带宇宙参数的声明名称由一个标识符，后接一个点与一组花括号中的一个或多个宇宙参数名构成：
```grammar
$_.{$_, $_,*}
```
这些宇宙参数名是绑定出现（binding occurrences）。
:::

/-
Examples do not include declaration names, and names are optional for instance declarations.
-/

示例（example）不包含声明名称；而实例声明（instance）的名字是可选的。

/-
## Parameters and Types
%%%
tag := "parameter-syntax"
%%%
-/

## 参数与类型（Parameters and Types）
%%%
tag := "parameter-syntax"
%%%

/-
After the name, if present, is the header's signature.
The signature specifies the declaration's parameters and type.
-/

在（可选的）名字之后，是声明头部的签名部分。
签名用于指定声明的参数以及其类型。

/-
:::syntax declSig (open := false) (title := "Declaration Signatures")
A signature consists of zero or more parameters, followed by a colon and a type.

```grammar
$_* : $_
```
:::
-/

:::syntax declSig (open := false) (title := "声明签名")
一个签名由零个或多个参数构成，后跟一个冒号与一个类型：
```grammar
$_* : $_
```
:::

/-
:::syntax optDeclSig (open := false) (title := "Optional Signatures")
Signatures are often optional.
In these cases, parameters may be supplied even if the type is omitted.
```grammar
$_* $[: $_]?
```
:::
-/

:::syntax optDeclSig (open := false) (title := "可选签名")
许多情况下签名本身是可选的。
这时即便省略类型，也可以仅提供参数：
```grammar
$_* $[: $_]?
```
:::


/-
Parameters may have three forms:
 * An identifier, which names a parameter but does not provide a type.
   These parameters' types must be inferred during elaboration.
 * An underscore (`_`), which indicates a parameter that is not accessible by name in the local scope.
   These parameters' types must also inferred during elaboration.
 * A bracketed binder, which may specify every aspect of one or more parameters, including their names, their types, default values, and whether they are explicit, implicit, strictly implicit, or instance-implicit.
-/

参数可以有三种形式：
 * 标识符：为参数命名，但不提供类型。这类参数的类型必须在繁释阶段推断出来。
 * 下划线（`_`）：表示该参数在局部作用域中不能通过名字访问。这类参数的类型同样需要在繁释阶段推断。
 * 带括号参数（bracketed binder）：可以为一个或多个参数指定所有方面的信息，包括名称、类型、默认值，以及其是显式、隐式、严格隐式或实例隐式。

/-
## Bracketed Parameter Bindings
%%%
tag := "bracketed-parameter-syntax"
%%%
-/

## 带括号参数绑定（Bracketed Parameter Bindings）
%%%
tag := "bracketed-parameter-syntax"
%%%


/-
Parameters other than identifiers or underscores are collectively referred to as {deftech}_bracketed binders_ because every syntactic form for specifying them has some kind of brackets, braces, or parentheses.
All bracketed binders specify the type of a parameter, and most include parameter names.
The name is optional for instance implicit parameters.
Using an underscore (`_`) instead of a parameter name indicates an anonymous parameter.
-/

除标识符与下划线外的其它参数形式统称为 {deftech key := "bracketed binders"}_带括号参数_，因为它们的语法形式都使用了某种括号（圆括号、花括号或方括号）。
所有带括号参数都会显式给出参数类型，并且多数情况下也会包含参数名。
对于“实例隐式”参数，名字是可选的。
用下划线（`_`）替代参数名表示匿名参数。


/-
:::syntax bracketedBinder (open := false) (title := "Explicit Parameters")
Parenthesized parameters indicate explicit parameters.
If more than one identifier or underscore is provided, then all of them become parameters with the same type.
```grammar
($x $x* : $t)
```
:::
-/

:::syntax bracketedBinder (open := false) (title := "显式参数")
使用圆括号括起的参数表示显式参数。
如果提供了多个标识符或下划线，则它们都会成为具有相同类型的多个参数：
```grammar
($x $x* : $t)
```
:::

/-
:::syntax bracketedBinder (title := "Optional and Automatic Parameters")
Parenthesized parameters with a `:=` assign default values to parameters.
Parameters with default values are called {deftech}_optional parameters_.
At a call site, if the parameter is not provided, then the provided term is used to fill it in.
Prior parameters in the signature are in scope for the default value, and their values at the call site are substituted into the default value term.

If a {ref "tactics"}[tactic script] is provided, then the tactics are executed at the call site to synthesize a parameter value; parameters that are filled in via tactics are called {deftech}_automatic parameters_.
```grammar
($x $x* : $t := $e)
```
:::
-/

:::syntax bracketedBinder (title := "可选与自动参数")
带有 `:=` 的圆括号参数用于为参数指定默认值。
带默认值的参数称为 {deftech key := "optional parameter"}_可选参数_。
在调用位置，如果未提供该参数，则会使用给定的默认项进行填充。
签名中之前的参数在默认值表达式内可见，且其在调用点的实参会被替换进默认值表达式。

如果提供了一个 {ref "tactics"}[策略脚本]，则会在调用点执行该脚本以合成一个参数值；通过策略填充的参数称为 {deftech key := "automatic parameter"}_自动参数_。
```grammar
($x $x* : $t := $e)
```
:::

/-
:::syntax bracketedBinder (title := "Implicit Parameters")
Parameters in curly braces indicate {tech}[implicit] parameters.
Unless provided by name at a call site, these parameters are expected to be synthesized via unification at call sites.
Implicit parameters are synthesized at all call sites.
```grammar
{$x $x* : $t}
```
:::
-/

:::syntax bracketedBinder (title := "隐式参数")
使用花括号的参数表示 {tech key := "implicit"}[隐式] 参数。
除非在调用点以名字显式提供，否则它们预期将通过统一过程在调用点被自动合成。
隐式参数会在所有调用点尝试合成：
```grammar
{$x $x* : $t}
```
:::

/-
:::syntax bracketedBinder (title := "Strict Implicit Parameters")
Parameters in double curly braces indicate {tech}[strict implicit] parameters.
`⦃ … ⦄` and `{{ … }}` are equivalent.
Like implicit parameters, these parameters are expected to be synthesized via unification at call sites when they are not provided by name.
Strict implicit parameters are only synthesized at call sites when subsequent parameters in the signature are also provided.

```grammar
⦃$x $x* : $t⦄
```
```grammar
{{$x $x* : $t}}
```

:::
-/

:::syntax bracketedBinder (title := "严格隐式参数")
使用双层花括号的参数表示 {tech key := "strict implicit"}[严格隐式] 参数。
`⦃ … ⦄` 与 `{{ … }}` 等价。
和隐式参数类似，若未以名字提供，它们预期通过统一在调用点被合成。
严格隐式参数仅当签名中其后的后续参数也被提供时才会尝试在调用点合成。

```grammar
⦃$x $x* : $t⦄
```
```grammar
{{$x $x* : $t}}
```

:::

/-
:::syntax bracketedBinder (title := "Instance Implicit Parameters")
Parameters in square brackets indicate {tech}[instance implicit] parameters, which are synthesized at call sites using {tech key:="synthesis"}[instance synthesis].
```grammar
[$[$x :]? $t]
```
:::
-/

:::syntax bracketedBinder (title := "实例隐式参数")
使用方括号的参数表示 {tech key := "instance implicit"}[实例隐式] 参数，它们会在调用点通过 {tech key := "synthesis"}[实例合成] 被推导：
```grammar
[$[$x :]? $t]
```
:::

/-
The parameters are always in scope in the signature's type, which occurs after the colon.
They are also in scope in the declaration's body, while names bound in the type itself are only in scope in the type.
Thus, parameter names are used twice:
 * As names in the declaration's function type, bound as part of a {tech key:="dependent"}[dependent function type].
 * As names in the declaration's body.
   In function definitions, they are bound by a {keywordOf Lean.Parser.Term.fun}`fun`.
-/

这些参数在签名的类型（位于冒号之后）中总是处于作用域内。
它们同样在声明的主体中可见；而由类型内部绑定的名字仅在类型内部可见。
因此，参数名通常会被使用两次：
 * 作为声明函数类型中的名字，作为 {tech key := "dependent"}[依值函数类型] 的一部分被绑定；
 * 作为声明主体中的名字。在函数定义里，它们由 {keywordOf Lean.Parser.Term.fun}`fun` 进行绑定。

-- :::example "Parameter Scope"
-- The signature of {lean}`add` contains one parameter, `n`.
-- Additionally, the signature's type is {lean}`(k : Nat) → Nat`, which is a function type that includes `k`.
-- The parameter `n` is in scope in the function's body, but `k` is not.
--
-- {lean}`add` 的签名包含一个参数 `n`。
-- 此外，签名的类型为 {lean}`(k : Nat) → Nat`，这是一个包含 `k` 的函数类型。
-- 参数 `n` 在函数体内处于作用域中，而 `k` 不在。
--
-- ```lean
-- def add (n : Nat) : (k : Nat) → Nat
--   | 0 => n
--   | k' + 1 => 1 + add n k'
-- ```
--
-- Like {lean}`add`, the signature of {lean}`mustBeEqual` contains one parameter, `n`.
-- It is in scope both in the type, where it occurs in a proposition, and in the body, where it occurs as part of the message.
-- 与 {lean}`add` 类似，{lean}`mustBeEqual` 的签名也包含一个参数 `n`。
-- 它既在类型中可见（该类型中的命题涉及到它），也在定义体中可见（作为消息的一部分出现）。
-- ```lean
-- def mustBeEqual (n : Nat) : (k : Nat) → n = k → String :=
--   fun _ =>
--     fun
--     | rfl => s!"Equal - both are {n}!"
--
-- ```
-- :::

:::example "参数作用域（Parameter Scope）"
{lean}`add` 的签名包含一个参数 `n`。
此外，签名的类型为 {lean}`(k : Nat) → Nat`，这是一个包含 `k` 的函数类型。
参数 `n` 在函数体内处于作用域中，而 `k` 不在。

```lean
def add (n : Nat) : (k : Nat) → Nat
  | 0 => n
  | k' + 1 => 1 + add n k'
```

与 {lean}`add` 类似，{lean}`mustBeEqual` 的签名也包含一个参数 `n`。
它既在类型中可见（该类型中的命题涉及到它），也在定义体中可见（作为消息的一部分出现）。

```lean
def mustBeEqual (n : Nat) : (k : Nat) → n = k → String :=
  fun _ =>
    fun
    | rfl => s!"Equal - both are {n}!"
```
:::

/-
The section on {ref "function-application"}[function application] describes the interpretation of {tech key:="optional parameter"}[optional], {tech key:="automatic parameter"}[automatic], {tech}[implicit], and {tech}[instance implicit] parameters in detail.
-/

关于函数应用的章节 {ref "function-application"}[函数应用] 详细说明了 {tech key := "optional parameter"}[可选]、{tech key := "automatic parameter"}[自动]、{tech key := "implicit"}[隐式] 与 {tech key := "instance implicit"}[实例隐式] 等参数的解释规则。

/-
## Automatic Implicit Parameters
%%%
tag := "automatic-implicit-parameters"
%%%
-/

## 自动隐式参数（Automatic Implicit Parameters）
%%%
tag := "automatic-implicit-parameters"
%%%


/-
By default, otherwise-unbound names that occur in signatures are converted into implicit parameters when possible
These parameters are called {deftech}_automatic implicit parameters_.
This is possible when they are not in the function position of an application and when there is sufficient information available in the signature to infer their type and any ordering constraints on them.
This process is iterated: if the inferred type for the freshly-inserted implicit parameter has dependencies that are not uniquely determined, then these dependencies are replaced with further implicit parameters.
-/

默认情况下，出现在签名中的未绑定名字在可行时会被转换为隐式参数。
这些参数称为 {deftech key := "automatic implicit parameters"}_自动隐式参数_。
当这些名字不处于函数应用的函数位置，且签名中有足够信息可以推断其类型以及关于它们的顺序约束时，这种转换是可行的。
该过程会迭代进行：如果为新插入的隐式参数所推断的类型包含尚未唯一确定的依赖项，则这些依赖会被进一步的隐式参数所替换。

/-
Implicit parameters that don't correspond to names written in signatures are assigned names akin to those of {tech}[inaccessible] hypotheses in proofs, which cannot be referred to.
They show up in signatures with a trailing dagger (`'✝'`).
This prevents an arbitrary choice of name by Lean from becoming part of the API by being usable as a {tech}[named argument].
-/

不对应于签名中书写之名字的隐式参数会被分配类似于证明中 {tech key := "inaccessible"}[不可触达] 假设的名字，这些名字无法被引用。
它们会以带有尾随短剑符号（`✝`）的形式出现在签名里。
这样可以避免 Lean 任意选择的名字经由 {tech key := "named argument"}[具名参数] 成为 API 的一部分。

/-
::::leanSection
```lean show:=false
variable {α : Type u} {β : Type v}
```
:::example "Automatic Implicit Parameters"

In this definition of {lean}`map`, {lean}`α` and {lean}`β` are not explicitly bound.
Rather than this being an error, they are converted into implicit parameters.
Because they must be types, but nothing constrains their universes, the universe parameters `u` and `v` are also inserted.
```lean
def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

The full signature of {lean}`map` is:
```signature
map.{u, v} {α : Type u} {β : Type v}
  (f : α → β) (xs : List α) :
  List β
```
:::
::::
-/

::::leanSection
```lean show:=false
variable {α : Type u} {β : Type v}
```
:::example "自动隐式参数（Automatic Implicit Parameters）"

在下面对 {lean}`map` 的定义中，{lean}`α` 与 {lean}`β` 并未显式绑定。
这不会报错，而是会被转换为隐式参数。
由于它们必须是类型，且其宇宙层级未受任何约束，因此还会自动插入宇宙层级参数 `u` 与 `v`：
```lean
def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

{lean}`map` 的完整签名为：
```signature
map.{u, v} {α : Type u} {β : Type v}
  (f : α → β) (xs : List α) :
  List β
```
:::
::::

-- ::::example "No Automatic Implicit Parameters"
--
-- :::leanSection
-- ```lean show:=false
-- universe u v
-- variable {α : Type u} {β : Type v}
-- ```
--
-- In this definition, {lean}`α` and {lean}`β` are not explicitly bound.
-- Because {option}`autoImplicit` is disabled, this is an error:
-- :::
--
-- :::keepEnv
-- ```lean (error := true) (name := noAuto)
-- set_option autoImplicit false
--
-- def map (f : α → β) : (xs : List α) → List β
--   | [] => []
--   | x :: xs => f x :: map f xs
-- ```
--
-- ```leanOutput noAuto
-- unknown identifier 'α'
-- ```
-- ```leanOutput noAuto
-- unknown identifier 'β'
-- ```
-- :::
--
--
-- The full signature allows the definition to be accepted:
-- ```lean (keep := false)
-- set_option autoImplicit false
--
-- def map.{u, v} {α : Type u} {β : Type v}
--     (f : α → β) :
--     (xs : List α) → List β
--   | [] => []
--   | x :: xs => f x :: map f xs
-- ```
--
-- Universe parameters are inserted automatically for parameters without explicit type annotations.
-- The type parameters' universes can be inferred, and the appropriate universe parameters inserted, even when {option}`autoImplicit` is disabled:
-- ```lean (keep := false)
-- set_option autoImplicit false
--
-- def map {α β} (f : α → β) :
--     (xs : List α) → List β
--   | [] => []
--   | x :: xs => f x :: map f xs
-- ```
--
-- ::::

::::example "无自动隐式参数（No Automatic Implicit Parameters）"

:::leanSection
```lean show:=false
universe u v
variable {α : Type u} {β : Type v}
```

在这个定义中，{lean}`α` 与 {lean}`β` 没有被显式绑定。
由于禁用了 {option}`autoImplicit`，这会导致错误：
:::

:::keepEnv
```lean (error := true) (name := noAuto)
set_option autoImplicit false

def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

```leanOutput noAuto
unknown identifier 'α'
```
```leanOutput noAuto
unknown identifier 'β'
```
:::

给出完整签名即可通过：
```lean (keep := false)
set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

对于未显式标注类型的参数，其宇宙参数会被自动插入。
即便禁用了 {option}`autoImplicit`，类型参数所处的宇宙也可被推断，并插入相应的宇宙参数：
```lean (keep := false)
set_option autoImplicit false

def map {α β} (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

::::



-- :::::example "Iterated Automatic Implicit Parameters"
--
-- :::leanSection
-- ````lean (show := false)
-- variable (i : Fin n)
-- ````
-- Given a number bounded by {lean}`n`, represented by the type `Fin n`, an {lean}`AtLeast i` is a natural number paired with a proof that it is at least as large as as `i`.
-- 给定一个由 {lean}`n` 作为上界所界定的数（由类型 `Fin n` 表示），{lean}`AtLeast i` 表示一个自然数以及它不少于 `i` 的证明。
-- :::
-- ```lean
-- structure AtLeast (i : Fin n) where
--   val : Nat
--   val_gt_i : val ≥ i.val
-- ```
--
-- These numbers can be added:
-- ```lean
-- def AtLeast.add (x y : AtLeast i) : AtLeast i :=
--   AtLeast.mk (x.val + y.val) <| by
--     cases x
--     cases y
--     dsimp only
--     omega
-- ```
--
-- ::::paragraph
-- :::leanSection
-- ````lean (show := false)
-- variable (i : Fin n)
-- ````
-- The signature of {lean}`AtLeast.add` requires multiple rounds of automatic implicit parameter insertion.
-- First, {lean}`i` is inserted; but its type depends on the upper bound {lean}`n` of {lean}`Fin n`.
-- In the second round, {lean}`n` is inserted, using a machine-chosen name.
-- Because {lean}`n`'s type is {lean}`Nat`, which has no dependencies, the process terminates.
-- The final signature can be seen with {keywordOf Lean.Parser.Command.check}`#check`:
-- :::
-- ```lean (name := checkAdd)
-- #check AtLeast.add
-- ```
-- ```leanOutput checkAdd
-- AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
-- ```
-- ::::
--
-- :::::

:::::example "多轮自动隐式参数（Iterated Automatic Implicit Parameters）"

:::leanSection
````lean (show := false)
variable (i : Fin n)
````
给定一个以上界 {lean}`n`（类型 `Fin n`）约束的数，一个 {lean}`AtLeast i` 表示一个自然数以及它不少于 `i` 的证明。
:::
```lean
structure AtLeast (i : Fin n) where
  val : Nat
  val_gt_i : val ≥ i.val
```

这些数可以相加：
```lean
def AtLeast.add (x y : AtLeast i) : AtLeast i :=
  AtLeast.mk (x.val + y.val) <| by
    cases x
    cases y
    dsimp only
    omega
```

::::paragraph
:::leanSection
````lean (show := false)
variable (i : Fin n)
````
{lean}`AtLeast.add` 的签名需要多轮自动隐式参数插入。
首先插入 {lean}`i`；但它的类型依赖于 {lean}`Fin n` 的上界 {lean}`n`。
第二轮插入 {lean}`n`（名字由系统选择）。
由于 {lean}`n` 的类型为 {lean}`Nat`，没有进一步依赖，过程终止。
可以用 {keywordOf Lean.Parser.Command.check}`#check` 查看最终签名：
:::
```lean (name := checkAdd)
#check AtLeast.add
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
::::

:::::

/-
Automatic implicit parameter insertion takes place after the insertion of parameters due to {tech}[section variables].
Parameters that correspond to section variables have the same name as the corresponding variable, even when they do not correspond to a name written directly in the signature, and disabling automatic implicit parameters has no effect the parameters that correspond to section variables.
However, when automatic implicit parameters are enabled, section variable declarations that contain otherwise-unbound variables receive additional section variables that follow the same rules as those for implicit parameters.
-/

由于 {tech}[section variables] 引入的参数会先被插入，自动隐式参数的插入发生在其之后。
与节变量对应的参数即便并未直接对应于签名中书写的某个名字，仍会与其对应的节变量同名；而禁用自动隐式参数对这些对应于节变量的参数不起作用。
不过，当启用自动隐式参数时，包含其他未绑定变量的节变量声明还会获得遵循与隐式参数相同规则的附加节变量。

/-
Automatic implicit parameters insertion is controlled by two options.
By default, automatic implicit parameter insertion is _relaxed_, which means that any unbound identifier may be a candidate for automatic insertion.
Setting the option {option}`relaxedAutoImplicit` to {lean}`false` disables relaxed mode and causes only identifiers that consist of a single character followed by zero or more digits to be considered for automatic insertion.
-/

自动隐式参数的插入由两个选项控制。
默认情况下，该插入处于“宽松（relaxed）”模式，这意味着任何未绑定的标识符都可能成为自动插入的候选。
将 {option}`relaxedAutoImplicit` 设为 {lean}`false` 会禁用宽松模式，此时仅由“单个字母后跟零个或多个数字”构成的标识符才会被考虑用于自动插入。

{optionDocs relaxedAutoImplicit}

{optionDocs autoImplicit}


-- ::::example "Relaxed vs Non-Relaxed Automatic Implicit Parameters"
--
-- Misspelled identifiers or missing imports can end up as unwanted implicit parameters, as in this example:
-- 拼写错误的标识符或缺失的导入，可能会变成意外的隐式参数，如下例所示：
-- ```lean
-- inductive Answer where
--   | yes
--   | maybe
--   | no
-- ```
-- :::keepEnv
-- ```lean  (name := asnwer) (error := true)
-- def select (choices : α × α × α) : Asnwer →  α
--   | .yes => choices.1
--   | .maybe => choices.2.1
--   | .no => choices.2.2
-- ```
-- The resulting error message states that the argument's type is not a constant, so dot notation cannot be used in the pattern:
-- 报错信息指出参数的类型不是常量，因此不能在模式中使用点记法：
-- ```leanOutput asnwer
-- invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
--   Asnwer
-- ```
-- This is because the signature is:
-- 原因是其签名为：
-- ```signature
-- select.{u_1, u_2}
--   {α : Type u_1}
--   {Asnwer : Sort u_2}
--   (choices : α × α × α) :
--   Asnwer → α
-- ```
-- :::
--
-- Disabling relaxed automatic implicit parameters makes the error more clear, while still allowing the type to be inserted automatically:
-- 禁用“宽松”的自动隐式参数后，错误更清晰，同时仍允许自动插入类型：
-- :::keepEnv
-- ```lean  (name := asnwer2) (error := true)
-- set_option relaxedAutoImplicit false
--
-- def select (choices : α × α × α) : Asnwer →  α
--   | .yes => choices.1
--   | .maybe => choices.2.1
--   | .no => choices.2.2
-- ```
-- ```leanOutput asnwer2
-- unknown identifier 'Asnwer'
-- ```
-- :::
--
-- Correcting the error allows the definition to be accepted.
-- 修正该错误后，定义即可通过：
-- :::keepEnv
-- ```lean
-- set_option relaxedAutoImplicit false
--
-- def select (choices : α × α × α) : Answer →  α
--   | .yes => choices.1
--   | .maybe => choices.2.1
--   | .no => choices.2.2
-- ```
-- :::
--
-- Turning off automatic implicit parameters entirely leads to the definition being rejected:
-- 完全关闭自动隐式参数会导致该定义被拒绝：
-- :::keepEnv
-- ```lean (error := true) (name := noauto)
-- set_option autoImplicit false
--
-- def select (choices : α × α × α) : Answer →  α
--   | .yes => choices.1
--   | .maybe => choices.2.1
--   | .no => choices.2.2
-- ```
-- ````leanOutput noauto
-- unknown identifier 'α'
-- ````
-- :::
-- ::::

::::example "宽松 vs 非宽松的自动隐式参数（Relaxed vs Non-Relaxed Automatic Implicit Parameters）"

拼写错误的标识符或缺失的导入，可能会变成意外的隐式参数，如下例所示：
```lean
inductive Answer where
  | yes
  | maybe
  | no
```
:::keepEnv
```lean  (name := asnwer) (error := true)
def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
报错信息指出参数的类型不是常量，因此不能在模式中使用点记法：
```leanOutput asnwer
invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  Asnwer
```
原因是其签名为：
```signature
select.{u_1, u_2}
  {α : Type u_1}
  {Asnwer : Sort u_2}
  (choices : α × α × α) :
  Asnwer → α
```
:::

禁用“宽松”的自动隐式参数后，错误更清晰，同时仍允许自动插入类型：
:::keepEnv
```lean  (name := asnwer2) (error := true)
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer2
unknown identifier 'Asnwer'
```
:::

修正该错误后，定义即可通过：
:::keepEnv
```lean
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
:::

完全关闭自动隐式参数会导致该定义被拒绝：
:::keepEnv
```lean (error := true) (name := noauto)
set_option autoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
````leanOutput noauto
unknown identifier 'α'
````
:::
::::

/-
# Definitions
-/

# 定义（Definitions）

/-
Definitions add a new constant to the global environment as a name that stands for a term.
As part of the kernel's definitional equality, this new constant may be replaced via {tech key:="δ"}[δ-reduction] with the term that it stands for.
In the elaborator, this replacement is governed by the constant's {tech}[reducibility].
The new constant may be {tech key:="universe polymorphism"}[universe polymorphic], in which case occurrences may instantiate it with different universe level parameters.
-/

“定义”会向全局环境添加一个常量，使其名称代表某个项。
作为内核定义等价的一部分，该常量可通过 {tech key := "δ"}[δ-归约] 被替换为其所代表的项。
在繁释器中，此替换受该常量的 {tech key := "reducibility"}[可约性] 控制。
新常量可以是 {tech key := "universe polymorphism"}[宇宙多态] 的，此时它的不同出现可以用不同的宇宙层级参数来实例化。

/-
Function definitions may be recursive.
To preserve the consistency of Lean's type theory as a logic, recursive functions must either be opaque to the kernel (e.g. by {ref "partial-functions"}[declaring them {keyword}`partial`]) or proven to terminate with one of the strategies described in {ref "recursive-definitions"}[the section on recursive definitions].
-/

函数定义可以是递归的。
为保证 Lean 作为逻辑的类型论的一致性，递归函数要么对内核保持不透明（例如 {ref "partial-functions"}[将其声明为 {keyword}`partial`]），要么需要使用 {ref "recursive-definitions"}[递归定义章节] 中描述的某种策略证明其终止。

/-
The headers and bodies of definitions are elaborated together.
If the header is incompletely specified (e.g. a parameter's type or the codomain is missing), then the body may provide sufficient information for the elaborator to reconstruct the missing parts.
However, {tech}[instance implicit] parameters must be specified in the header or as {tech}[section variables].
-/

定义的头部与主体会一并进行繁释。
若头部信息不完整（例如缺失某个参数的类型或缺失余类型），则定义体可能为繁释器提供足够信息以重建缺失部分。
不过，{tech key := "instance implicit"}[实例隐式] 参数必须在头部显式给出，或作为 {tech}[section variables] 指定。

/-
:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.definition (title := "Definitions")
Definitions that use `:=` associate the term on the right-hand side with the constant's name.
The term is wrapped in a {keywordOf Lean.Parser.Term.fun}`fun` for each parameter, and the type is found by binding the parameters in a function type.
Definitions with {keyword}`def` are {tech}[semireducible].

```grammar
$_:declModifiers
def $_ $_ := $_
```

Definitions may use pattern matching.
These definitions are desugared to uses of {keywordOf Lean.Parser.Term.match}`match`.

```grammar
$_:declModifiers
def $_ $_
  $[| $_ => $_]*
```

Values of structure types, or functions that return them, may be defined by providing values for their fields, following {keyword}`where`:

```grammar
$_:declModifiers
def $_ $_ where
  $_*
```
:::
-/

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.definition (title := "定义")
使用 `:=` 的定义会将右侧的项与该常量的名字相关联。
对于每个参数，定义体外层会包裹一个 {keywordOf Lean.Parser.Term.fun}`fun`，而类型则通过将参数绑定在函数类型中获得。
使用 {keyword}`def` 的定义是 {tech key := "semireducible"}[半可约（semireducible）] 的。

```grammar
$_:declModifiers
def $_ $_ := $_
```

定义可以使用模式匹配。
此类定义会被糖化还原为 {keywordOf Lean.Parser.Term.match}`match` 的用法。

```grammar
$_:declModifiers
def $_ $_
  $[| $_ => $_]*
```

对于结构体类型的值，或返回结构体的函数，可以在 {keyword}`where` 之后为其字段提供取值来进行定义：

```grammar
$_:declModifiers
def $_ $_ where
  $_*
```
:::

/-
:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.abbrev (title := "Abbreviations")
Abbreviations are identical to definitions with {keyword}`def`, except they are {tech}[reducible].

```grammar
$_:declModifiers
abbrev $_ $_ := $_
```

```grammar
$_:declModifiers
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
abbrev $_ $_ where
  $_*
```
:::
-/

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.abbrev (title := "缩写（Abbreviations）")
“缩写”与使用 {keyword}`def` 的定义完全一致，区别仅在于它们是 {tech key := "reducible"}[可约（reducible）] 的。

```grammar
$_:declModifiers
abbrev $_ $_ := $_
```

```grammar
$_:declModifiers
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
abbrev $_ $_ where
  $_*
```
:::


/-
{deftech}_Opaque constants_ are defined constants that are not subject to {tech key:="δ"}[δ-reduction] in the kernel.
They are useful for specifying the existence of some function.
Unlike {tech}[axioms], opaque declarations can only be used for types that are inhabited, so they do not risk introducing inconsistency.
Also unlike axioms, the inhabitant of the type is used in compiled code.
The {attr}`implemented_by` attribute can be used to instruct the compiler to emit a call to some other function as the compilation of an opaque constant.
-/

{deftech key := "Opaque constants"}_不透明常量_ 是在内核中不受 {tech key := "δ"}[δ-归约] 约束的已定义常量。
它们对于仅陈述某个函数的存在性很有用。
与 {tech key := "axioms"}[公理] 不同，不透明声明只能用于“可居”（inhabited）的类型，因此不会带来不一致风险。
亦不同于公理的是，该类型的居留元会在已编译代码中被实际使用。
还可以使用 {attr}`implemented_by` 属性指示编译器在编译该不透明常量时发出对其他函数的调用。

/-
:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.opaque (title := "Opaque Constants")
Opaque definitions with right-hand sides are elaborated like other definitions.
This demonstrates that the type is inhabited; the inhabitant plays no further role.
```grammar
$_:declModifiers
opaque $_ $_ := $_
```

Opaque constants may also be specified without right-hand sides.
The elaborator fills in the right-hand side by synthesizing an instance of {name}`Inhabited`, or {name}`Nonempty` if that fails.
```grammar
$_:declModifiers
opaque $_ $_
```
:::
-/

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.opaque (title := "不透明常量（Opaque Constants）")
带右侧定义式的不透明常量会像其他定义一样被繁释。
这表明该类型是“可居”的；该居留元本身不再扮演后续角色。
```grammar
$_:declModifiers
opaque $_ $_ := $_
```

也可以不给出右侧定义式。
此时繁释器会通过合成一个 {name}`Inhabited` 实例来填充右侧；若失败，则尝试 {name}`Nonempty`：
```grammar
$_:declModifiers
opaque $_ $_
```
:::

/-
# Theorems
-/

# 定理（Theorems）

/-
:::paragraph
Because {tech}[propositions] are types whose inhabitants count as proofs, {deftech}[theorems] and definitions are technically very similar.
However, because their use cases are quite different, they differ in many details:

* The theorem statement must be a proposition.
  The types of definitions may inhabit any {tech}[universe].
* A theorem's header (that is, the theorem statement) is completely elaborated before the body is elaborated.
  Section variables only become parameters to the theorem if they (or their dependents) are mentioned in the header.
  This prevents changes to a proof from unintentionally changing the the theorem statement.
* Theorems are {tech}[irreducible] by default.
  Because all proofs of the same proposition are {tech key:="definitional equality"}[definitionally equal], there few reasons to unfold a theorem.
:::
-/

:::paragraph
由于 {tech key := "propositions"}[命题] 是其居留元可作为证明的类型，{deftech key := "theorems"}[定理] 与“定义”在技术上非常相似。
然而，由于它们的使用场景不同，许多细节上有所差异：

- 定理陈述必须是一个命题；
  而定义的类型可以属于任意 {tech key := "universe"}[宇宙]。
- 定理的头部（即定理陈述）会在定理主体之前被完全繁释。
  只有当节变量（或依赖于它们的变量）出现在头部时，它们才会成为定理的参数。
  这可以避免更改证明时无意间改变定理陈述本身。
- 定理默认是 {tech key := "irreducible"}[不可约（irreducible）] 的。
  由于对同一命题的所有证明在 {tech key := "definitional equality"}[定义相等] 下是相等的，几乎没有理由去展开一个定理。
:::

/-
Theorems may be recursive, subject to the same conditions as {ref "recursive-definitions"}[recursive function definitions].
However, it is more common to use tactics such as {tactic}`induction` or {tactic}`fun_induction` instead.
-/

定理也可以是递归的，但需满足与 {ref "recursive-definitions"}[递归函数定义] 相同的条件。
不过，更常见的做法是使用 {tactic}`induction` 或 {tactic}`fun_induction` 等策略来完成证明。

/-
:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.theorem (title := "Theorems")
The syntax of theorems is like that of definitions, except the codomain (that is, the theorem statement) in the signature is mandatory.
```grammar
$_:declModifiers
theorem $_ $_ := $_
```

```grammar
$_:declModifiers
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
theorem $_ $_ where
  $_*
```
:::
-/

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.theorem (title := "定理（Theorems）")
定理的语法与定义类似，但签名中的余类型（即定理陈述）是强制的。
```grammar
$_:declModifiers
theorem $_ $_ := $_
```

```grammar
$_:declModifiers
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
theorem $_ $_ where
  $_*
```
:::



/-
# Example Declarations
-/

# 示例声明（Example Declarations）

/-
An {deftech}[example] is an anonymous definition that is elaborated and then discarded.
Examples are useful for incremental testing during development and to make it easier to understand a file.
-/

{deftech key := "example"}[示例] 是一种匿名定义：会被繁释，但随后丢弃。
示例有助于在开发过程中进行增量测试，也有助于读者更容易理解一个文件。

/-
:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.example (title := "Examples")
```grammar
$_:declModifiers
example $_:optDeclSig := $_
```

```grammar
$_:declModifiers
example $_:optDeclSig
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
example $_:optDeclSig where
  $_*
```
:::
-/

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.example (title := "示例（Examples）")
```grammar
$_:declModifiers
example $_:optDeclSig := $_
```

```grammar
$_:declModifiers
example $_:optDeclSig
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
example $_:optDeclSig where
  $_*
```
:::



{include 0 Manual.RecursiveDefs}
