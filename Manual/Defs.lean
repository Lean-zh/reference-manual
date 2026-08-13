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



Lean 中以下命令属于“定义式（definition-like）”：{TODO}[以命令名形式渲染（类似策略索引）]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

All of these commands cause Lean to {tech (key := "elaborator") -normalize}[elaborate] a term based on a {tech}[signature].
With the exception of {keywordOf Lean.Parser.Command.example}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].




# 修饰符（Modifiers）
%%%
file := "Modifiers"
tag := "declaration-modifiers"
%%%

Declarations accept a consistent set of {deftech}_modifiers_, all of which are optional.
Modifiers change some aspect of the declaration's interpretation; for example, they can add documentation or change its scope.
The order of modifiers is fixed, but not every kind of declaration accepts every kind of modifier.

:::syntax declModifiers -open (alias:=Lean.Parser.Command.declModifiers) (title := "Declaration Modifiers")
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


:::syntax docComment -open (title := "Documentation Comments")


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


If a declaration is marked {deftech (key := "private")}[{keyword}`private`], then it is not accessible outside the module in which it is defined.
If it is {keyword}`protected`, then opening its namespace does not bring it into scope.


{keyword}`unsafe` 标记会使定义跳过内核检查，并允许其访问可能破坏 Lean 保证的功能。
使用该标记务必小心，仅在深入理解 Lean 内部机制时使用。



# 头部与签名（Headers and Signatures）
%%%
file := "Headers and Signatures"
tag := "signature-syntax"
%%%

The {deftech}[_header_] of a definition or declaration consists of the constant being declared or defined, if relevant, together with its signature.
The {deftech}_signature_ of a constant specifies how it can be used.
The information present in the signature is more than just the type, including information such as {tech (key := "universe parameter")}[universe level parameters] and the default values of its optional parameters.
In Lean, signatures are written in a consistent format in different kinds of declarations.


定义或声明的 {deftech key := "header"}_头部_（若有）由待声明/定义的常量以及其签名组成。
常量的 {deftech key := "signature"}_签名_ 指定了它可以如何被使用。
签名中包含的不仅仅是类型本身的信息，还包括例如 {tech key := "universe parameter"}[宇宙层级参数]、可选参数的默认值等。
在 Lean 中，不同类型的声明均使用一致的格式来书写签名。


:::syntax declId -open (title := "Declaration Names")
Declaration names without universe parameters consist of an identifier:

```grammar
$_:ident
```

带宇宙参数的声明名称由一个标识符，后接一个点与一组花括号中的一个或多个宇宙参数名构成：
```grammar
$_.{$_, $_,*}
```
这些宇宙参数名是绑定出现（binding occurrences）。
:::


示例（example）不包含声明名称；而实例声明（instance）的名字是可选的。


## 参数与类型（Parameters and Types）
%%%
tag := "parameter-syntax"
%%%


:::syntax declSig -open (title := "Declaration Signatures")
A signature consists of zero or more parameters, followed by a colon and a type.


:::syntax declSig (open := false) (title := "声明签名")
一个签名由零个或多个参数构成，后跟一个冒号与一个类型：
```grammar
$_* : $_
```
:::

:::syntax optDeclSig -open (title := "Optional Signatures")
Signatures are often optional.
In these cases, parameters may be supplied even if the type is omitted.

```grammar
$_* $[: $_]?
```
:::


Parameters may have three forms:
 * An identifier, which names a parameter but does not provide a type.
   These parameters' types must be inferred during elaboration.
 * An underscore (`_`), which indicates a parameter that is not accessible by name in the local scope.
   These parameters' types must also be inferred during elaboration.
 * A bracketed binder, which may specify every aspect of one or more parameters, including their names, their types, default values, and whether they are explicit, implicit, strictly implicit, or instance-implicit.


参数可以有三种形式：
 * 标识符：为参数命名，但不提供类型。这类参数的类型必须在繁释阶段推断出来。
 * 下划线（`_`）：表示该参数在局部作用域中不能通过名字访问。这类参数的类型同样需要在繁释阶段推断。
 * 带括号参数（bracketed binder）：可以为一个或多个参数指定所有方面的信息，包括名称、类型、默认值，以及其是显式、隐式、严格隐式或实例隐式。


## 带括号参数绑定（Bracketed Parameter Bindings）
%%%
tag := "bracketed-parameter-syntax"
%%%



除标识符与下划线外的其它参数形式统称为 {deftech key := "bracketed binders"}_带括号参数_，因为它们的语法形式都使用了某种括号（圆括号、花括号或方括号）。
所有带括号参数都会显式给出参数类型，并且多数情况下也会包含参数名。
对于“实例隐式”参数，名字是可选的。
用下划线（`_`）替代参数名表示匿名参数。


:::syntax bracketedBinder -open (title := "Explicit Parameters")
Parenthesized parameters indicate explicit parameters.
If more than one identifier or underscore is provided, then all of them become parameters with the same type.

```grammar
($x $x* : $t)
```
:::


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


:::syntax bracketedBinder (title := "隐式参数")
使用花括号的参数表示 {tech key := "implicit"}[隐式] 参数。
除非在调用点以名字显式提供，否则它们预期将通过统一过程在调用点被自动合成。
隐式参数会在所有调用点尝试合成：
```grammar
{$x $x* : $t}
```
:::


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

:::syntax bracketedBinder (title := "Instance Implicit Parameters")
Parameters in square brackets indicate {tech}[instance implicit] parameters, which are synthesized at call sites using {tech (key := "synthesis")}[instance synthesis].

```grammar
[$[$x :]? $t]
```
:::

The parameters are always in scope in the signature's type, which occurs after the colon.
They are also in scope in the declaration's body, while names bound in the type itself are only in scope in the type.
Thus, parameter names are used twice:
 * As names in the declaration's function type, bound as part of a {tech (key := "dependent")}[dependent function type].
 * As names in the declaration's body.
   In function definitions, they are bound by a {keywordOf Lean.Parser.Term.fun}`fun`.


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

The section on {ref "function-application"}[function application] describes the interpretation of {tech (key := "optional parameter")}[optional], {tech (key := "automatic parameter")}[automatic], {tech}[implicit], and {tech}[instance implicit] parameters in detail.


关于函数应用的章节 {ref "function-application"}[函数应用] 详细说明了 {tech key := "optional parameter"}[可选]、{tech key := "automatic parameter"}[自动]、{tech key := "implicit"}[隐式] 与 {tech key := "instance implicit"}[实例隐式] 等参数的解释规则。


## 自动隐式参数（Automatic Implicit Parameters）
%%%
tag := "automatic-implicit-parameters"
%%%



默认情况下，出现在签名中的未绑定名字在可行时会被转换为隐式参数。
这些参数称为 {deftech key := "automatic implicit parameters"}_自动隐式参数_。
当这些名字不处于函数应用的函数位置，且签名中有足够信息可以推断其类型以及关于它们的顺序约束时，这种转换是可行的。
该过程会迭代进行：如果为新插入的隐式参数所推断的类型包含尚未唯一确定的依赖项，则这些依赖会被进一步的隐式参数所替换。


不对应于签名中书写之名字的隐式参数会被分配类似于证明中 {tech key := "inaccessible"}[不可触达] 假设的名字，这些名字无法被引用。
它们会以带有尾随短剑符号（`✝`）的形式出现在签名里。
这样可以避免 Lean 任意选择的名字经由 {tech key := "named argument"}[具名参数] 成为 API 的一部分。


::::leanSection
```lean -show
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
```lean -show
universe u v
variable {α : Type u} {β : Type v}
```

在这个定义中，{lean}`α` 与 {lean}`β` 没有被显式绑定。
由于禁用了 {option}`autoImplicit`，这会导致错误：
:::

:::keepEnv
```lean +error (name := noAuto)
set_option autoImplicit false

def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

```leanOutput noAuto
Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
```leanOutput noAuto
Unknown identifier `β`

Note: It is not possible to treat `β` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
:::


The full signature allows the definition to be accepted:
```lean -keep

set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

Universe parameters are inserted automatically for parameters without explicit type annotations.
The type parameters' universes can be inferred, and the appropriate universe parameters inserted, even when {option}`autoImplicit` is disabled:
```lean -keep

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
```lean -show
variable (i : Fin n)
```
Given a number bounded by {lean}`n`, represented by the type `Fin n`, an {lean}`AtLeast i` is a natural number paired with a proof that it is at least as large as `i`.

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
```lean -show
variable (i : Fin n)
```
The signature of {lean}`AtLeast.add` requires multiple rounds of automatic implicit parameter insertion.
First, {lean}`i` is inserted; but its type depends on the upper bound {lean}`n` of {lean}`Fin n`.
In the second round, {lean}`n` is inserted, using a machine-chosen name.
Because {lean}`n`'s type is {lean}`Nat`, which has no dependencies, the process terminates.
The final signature can be seen with {keywordOf Lean.Parser.Command.check}`#check`:

:::
```lean (name := checkAdd)
#check AtLeast.add
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
::::

:::::


由于 {tech}[section variables] 引入的参数会先被插入，自动隐式参数的插入发生在其之后。
与节变量对应的参数即便并未直接对应于签名中书写的某个名字，仍会与其对应的节变量同名；而禁用自动隐式参数对这些对应于节变量的参数不起作用。
不过，当启用自动隐式参数时，包含其他未绑定变量的节变量声明还会获得遵循与隐式参数相同规则的附加节变量。


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
```lean  (name := asnwer) +error
def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
报错信息指出参数的类型不是常量，因此不能在模式中使用点记法：
```leanOutput asnwer
Invalid dotted identifier notation: The expected type of `.yes`
  Asnwer
is not of the form `C ...` or `... → C ...` where C is a constant
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
```lean  (name := asnwer2) +error
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer2
Unknown identifier `Asnwer`

Note: It is not possible to treat `Asnwer` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.
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
```lean +error (name := noauto)
set_option autoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput noauto
Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
:::
::::


Definitions add a new constant to the global environment as a name that stands for a term.
As part of the kernel's definitional equality, this new constant may be replaced via {tech (key := "δ")}[δ-reduction] with the term that it stands for.
In the elaborator, this replacement is governed by the constant's {tech}[reducibility].
The new constant may be {tech (key := "universe polymorphism")}[universe polymorphic], in which case occurrences may instantiate it with different universe level parameters.


“定义”会向全局环境添加一个常量，使其名称代表某个项。
作为内核定义等价的一部分，该常量可通过 {tech key := "δ"}[δ-归约] 被替换为其所代表的项。
在繁释器中，此替换受该常量的 {tech key := "reducibility"}[可约性] 控制。
新常量可以是 {tech key := "universe polymorphism"}[宇宙多态] 的，此时它的不同出现可以用不同的宇宙层级参数来实例化。


:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.definition) (title := "Definitions")
Definitions that use `:=` associate the term on the right-hand side with the constant's name.
The term is wrapped in a {keywordOf Lean.Parser.Term.fun}`fun` for each parameter, and the type is found by binding the parameters in a function type.
Definitions with {keyword}`def` are {tech}[semireducible].


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

In {tech}[modules], the bodies of definitions defined with {keyword}`def` are not exposed by default.
:::

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.abbrev) (title := "Abbreviations")
{deftech}[Abbreviations] are identical to definitions with {keyword}`def`, except they are {tech}[reducible].


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

In {tech}[modules], the bodies of definitions defined with {keyword}`abbrev` are exposed by default.
:::


{deftech}_Opaque constants_ are defined constants that are not subject to {tech (key := "δ")}[δ-reduction] in the kernel.
They are useful for specifying the existence of some function.
Unlike {tech}[axioms], opaque declarations can only be used for types that are inhabited, so they do not risk introducing inconsistency.
Also unlike axioms, the inhabitant of the type is used in compiled code.
The {attr}`implemented_by` attribute can be used to instruct the compiler to emit a call to some other function as the compilation of an opaque constant.

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.opaque) (title := "Opaque Constants")
Opaque definitions with right-hand sides are elaborated like other definitions.
This demonstrates that the type is inhabited; the inhabitant plays no further role.

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


# 定理（Theorems）


:::paragraph
Because {tech}[propositions] are types whose inhabitants count as proofs, {deftech}[theorems] and definitions are technically very similar.
However, because their use cases are quite different, they differ in many details:

* The theorem statement must be a proposition.
  The types of definitions may inhabit any {tech}[universe].
* A theorem's header (that is, the theorem statement) is completely elaborated before the body is elaborated.
  Section variables only become parameters to the theorem if they (or their dependents) are mentioned in the header.
  This prevents changes to a proof from unintentionally changing the theorem statement.
* Theorems are {tech}[irreducible] by default.
  Because all proofs of the same proposition are {tech (key := "definitional equality")}[definitionally equal], there are few reasons to unfold a theorem.

:::


:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.theorem) (title := "Theorems")
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

In {tech}[modules], proofs of theorems are not exposed by default.
:::




# 示例声明（Example Declarations）


{deftech key := "example"}[示例] 是一种匿名定义：会被繁释，但随后丢弃。
示例有助于在开发过程中进行增量测试，也有助于读者更容易理解一个文件。


:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.example) (title := "Examples")

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
