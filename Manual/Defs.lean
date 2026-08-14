/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Defs

import Manual.RecursiveDefs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500


#doc (Manual) "定义" =>
%%%
file := "Definitions"
tag := "definitions"
%%%



Lean 中以下命令属于“定义式”：{TODO}[以命令名形式渲染（类似策略索引）]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

这些命令都会促使 Lean 的 {tech (key := "elaborator") -normalize}[精译器]基于其 {tech (key := "signature")}[签名]对一个项进行精译。
除 {keywordOf Lean.Parser.Command.example}`example`（其结果会被丢弃）之外，精译得到的 Lean 核心语言表达式都会保存到环境中以供后续使用。
{keywordOf Lean.Parser.Command.declaration}`instance` 命令见 {ref "instance-declarations"}[实例声明]一节。




# 修饰符
%%%
file := "Modifiers"
tag := "declaration-modifiers"
%%%

声明支持一组一致的 {deftech (key := "modifiers")}_修饰符_，它们均为可选。
修饰符会改变声明在解释上的某些方面；例如可以添加文档，或改变其作用域。
修饰符的顺序是固定的，但并非所有种类的声明都接受所有种类的修饰符。

:::syntax declModifiers -open (alias:=Lean.Parser.Command.declModifiers) (title := "声明修饰符")
修饰符按如下顺序出现，且均为可选：
 1. 文档注释；
 2. {tech (key := "attributes")}[属性]列表；
 3. 命名空间控制，指定结果名字是否为 {tech (key := "private")}[私有]或 {tech (key := "protected")}[受保护]；
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


{deftech (key := "documentation comment")}_文档注释_用于为它所修饰的声明提供源码内 API 文档。
文档注释实际上并不是普通注释：把它放在不会被当作文档处理的位置会造成语法错误。
它也用于需要文本、但字符串转义会很繁琐的位置，例如 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令中的预期消息。

:::syntax docComment -open (title := "文档注释")
文档注释与普通块注释相似，但它以 `/--` 开始（而非常规块注释的 `/-`）；与普通注释一样，以 `-/` 结束。
```grammar
/--
...
-/
```
:::


属性是可扩展的一类修饰符，用于将附加信息关联到声明上。
它们在 {ref "attributes"}[属性专章]中有详细说明。

若声明被标记为 {deftech (key := "private")}[{keyword}`private`]，则无法在其定义所在模块之外访问。
若声明为 {keyword}`protected`，则打开其命名空间时不会将该名字带入作用域。

被标记为 {keyword}`noncomputable` 的函数不会被编译，因而也不能执行。
当函数使用了非可计算的推理原则（例如选择公理或排中律）来产生与其返回结果相关的数据，或使用了因效率原因而不参与代码生成的 Lean 特性（如 {tech (key := "recursor")}[递归器]）时，该函数必须是 noncomputable。
即使无法编译和执行，noncomputable 函数在规范化与推理中依然十分有用。

{keyword}`unsafe` 标记会使定义跳过内核检查，并允许其访问可能破坏 Lean 保证的功能。
使用该标记务必小心，仅在深入理解 Lean 内部机制时使用。



# 头部与签名
%%%
file := "Headers-and-Signatures"
tag := "signature-syntax"
%%%

定义或声明的 {deftech (key := "header")}_头部_（若有）由待声明/定义的常量以及其签名组成。
常量的 {deftech (key := "signature")}_签名_ 指定了它可以如何被使用。
签名中包含的不仅仅是类型本身的信息，还包括例如 {tech (key := "universe parameter")}[宇宙层级参数]、可选参数的默认值等。
在 Lean 中，不同类型的声明均使用一致的格式来书写签名。


## 声明名称
%%%
tag := "declaration-names"
%%%

大多数头部以一个 {deftech (key := "declaration name")}_声明名称_ 开始，随后是其真正的签名：参数列表以及结果类型。
一个声明名称可以可选地包含宇宙层级参数。

:::syntax declId -open (title := "声明名称")
不带宇宙参数的声明名称仅由一个标识符组成：
```grammar
$_:ident
```

带宇宙参数的声明名称由一个标识符，后接一个点与一组花括号中的一个或多个宇宙参数名构成：
```grammar
$_.{$_, $_,*}
```
这些宇宙参数名是绑定出现。
:::


示例不包含声明名称；而实例声明的名字是可选的。


## 参数与类型
%%%
tag := "parameter-syntax"
%%%


:::syntax declSig -open (title := "声明签名")
一个签名由零个或多个参数构成，后跟一个冒号与一个类型：
```grammar
$_* : $_
```
:::

:::syntax optDeclSig -open (title := "可选签名")
许多情况下签名本身是可选的。
这时即便省略类型，也可以仅提供参数：
```grammar
$_* $[: $_]?
```
:::


参数可以有三种形式：
 * 标识符：为参数命名，但不提供类型。这类参数的类型必须在精译阶段推断出来。
 * 下划线（`_`）：表示该参数在局部作用域中不能通过名字访问。这类参数的类型同样需要在精译阶段推断。
 * 带括号参数：可以为一个或多个参数指定所有方面的信息，包括名称、类型、默认值，以及其是显式、隐式、严格隐式或实例隐式。


## 带括号参数绑定
%%%
tag := "bracketed-parameter-syntax"
%%%



除标识符与下划线外的其它参数形式统称为 {deftech (key := "bracketed binders")}_带括号参数_，因为它们的语法形式都使用了某种括号（圆括号、花括号或方括号）。
所有带括号参数都会显式给出参数类型，并且多数情况下也会包含参数名。
对于“实例隐式”参数，名字是可选的。
用下划线（`_`）替代参数名表示匿名参数。


:::syntax bracketedBinder -open (title := "显式参数")
使用圆括号括起的参数表示显式参数。
如果提供了多个标识符或下划线，则它们都会成为具有相同类型的多个参数：
```grammar
($x $x* : $t)
```
:::


:::syntax bracketedBinder (title := "可选与自动参数")
带有 `:=` 的圆括号参数用于为参数指定默认值。
带默认值的参数称为 {deftech (key := "optional parameter")}_可选参数_。
在调用位置，如果未提供该参数，则会使用给定的默认项进行填充。
签名中之前的参数在默认值表达式内可见，且其在调用点的实参会被替换进默认值表达式。

如果提供了一个 {ref "tactics"}[策略脚本]，则会在调用点执行该脚本以合成一个参数值；通过策略填充的参数称为 {deftech (key := "automatic parameter")}_自动参数_。
```grammar
($x $x* : $t := $e)
```
:::


:::syntax bracketedBinder (title := "隐式参数")
使用花括号的参数表示 {tech (key := "implicit")}[隐式] 参数。
除非在调用点以名字显式提供，否则它们预期将通过统一过程在调用点被自动合成。
隐式参数会在所有调用点尝试合成：
```grammar
{$x $x* : $t}
```
:::


:::syntax bracketedBinder (title := "严格隐式参数")
使用双层花括号的参数表示 {tech (key := "strict implicit")}[严格隐式] 参数。
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

:::syntax bracketedBinder (title := "实例隐式参数")
使用方括号的参数表示 {tech (key := "instance implicit")}[实例隐式]参数，它们会在调用点通过 {tech (key := "synthesis")}[实例合成]被推导：
```grammar
[$[$x :]? $t]
```
:::

这些参数在签名的类型（位于冒号之后）中总是处于作用域内。
它们同样在声明的主体中可见；而由类型内部绑定的名字仅在类型内部可见。
因此，参数名通常会被使用两次：
 * 作为声明函数类型中的名字，作为 {tech (key := "dependent")}[依值函数类型] 的一部分被绑定；
 * 作为声明主体中的名字。在函数定义里，它们由 {keywordOf Lean.Parser.Term.fun}`fun` 进行绑定。


:::example "参数作用域"
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

关于函数应用的章节 {ref "function-application"}[函数应用] 详细说明了 {tech (key := "optional parameter")}[可选]、{tech (key := "automatic parameter")}[自动]、{tech (key := "implicit")}[隐式] 与 {tech (key := "instance implicit")}[实例隐式] 等参数的解释规则。


关于函数应用的章节 {ref "function-application"}[函数应用] 详细说明了 {tech (key := "optional parameter")}[可选]、{tech (key := "automatic parameter")}[自动]、{tech (key := "implicit")}[隐式] 与 {tech (key := "instance implicit")}[实例隐式] 等参数的解释规则。


## 自动隐式参数
%%%
tag := "automatic-implicit-parameters"
%%%



默认情况下，出现在签名中的未绑定名字在可行时会被转换为隐式参数。
这些参数称为 {deftech (key := "automatic implicit parameters")}_自动隐式参数_。
当这些名字不处于函数应用的函数位置，且签名中有足够信息可以推断其类型以及关于它们的顺序约束时，这种转换是可行的。
该过程会迭代进行：如果为新插入的隐式参数所推断的类型包含尚未唯一确定的依赖项，则这些依赖会被进一步的隐式参数所替换。


不对应于签名中书写之名字的隐式参数会被分配类似于证明中 {tech (key := "inaccessible")}[不可触达] 假设的名字，这些名字无法被引用。
它们会以带有尾随短剑符号（`✝`）的形式出现在签名里。
这样可以避免 Lean 任意选择的名字经由 {tech (key := "named argument")}[具名参数] 成为 API 的一部分。


::::leanSection
```lean -show
variable {α : Type u} {β : Type v}
```
:::example "自动隐式参数"

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


::::example "无自动隐式参数"

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


给出完整签名即可通过：
```lean -keep

set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

对于未显式标注类型的参数，其宇宙参数会被自动插入。
即便禁用了 {option}`autoImplicit`，类型参数所处的宇宙也可被推断，并插入相应的宇宙参数：
```lean -keep

set_option autoImplicit false

def map {α β} (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

::::




:::::example "多轮自动隐式参数"

:::leanSection
```lean -show
variable (i : Fin n)
```
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
```lean -show
variable (i : Fin n)
```
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


由于 {tech (key := "section variables")}[区段变量]引入的参数会先被插入，自动隐式参数的插入发生在其之后。
与节变量对应的参数即便并未直接对应于签名中书写的某个名字，仍会与其对应的节变量同名；而禁用自动隐式参数对这些对应于节变量的参数不起作用。
不过，当启用自动隐式参数时，包含其他未绑定变量的节变量声明还会获得遵循与隐式参数相同规则的附加节变量。


自动隐式参数的插入由两个选项控制。
默认情况下，该插入处于“宽松”模式，这意味着任何未绑定的标识符都可能成为自动插入的候选。
将 {option}`relaxedAutoImplicit` 设为 {lean}`false` 会禁用宽松模式，此时仅由“单个字母后跟零个或多个数字”构成的标识符才会被考虑用于自动插入。

{zhOptionDocs relaxedAutoImplicit ZhDoc.Defs.Option.relaxedAutoImplicit}

{zhOptionDocs autoImplicit ZhDoc.Defs.Option.autoImplicit}



::::example "宽松与非宽松的自动隐式参数"

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


# 定义
%%%
file := "Definitions"
tag := "definitions-command"
%%%

“定义”会向全局环境添加一个常量，使其名称代表某个项。
作为内核定义等价的一部分，该常量可通过 {tech (key := "δ")}[δ-归约] 被替换为其所代表的项。
在精译器中，此替换受该常量的 {tech (key := "reducibility")}[可约性] 控制。
新常量可以是 {tech (key := "universe polymorphism")}[宇宙多态] 的，此时它的不同出现可以用不同的宇宙层级参数来实例化。

函数定义可以是递归的。
为保证 Lean 作为逻辑的类型论的一致性，递归函数要么对内核保持不透明（例如 {ref "partial-functions"}[将其声明为 {keyword}`partial`]），要么需要使用 {ref "recursive-definitions"}[递归定义章节] 中描述的某种策略证明其终止。

定义的头部与主体会一并进行精译。
若头部信息不完整（例如缺失某个参数的类型或缺失余类型），则定义体可能为精译器提供足够信息以重建缺失部分。
不过，{tech (key := "instance implicit")}[实例隐式]参数必须在头部显式给出，或作为 {tech (key := "section variable")}[区段变量]指定。


:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.definition) (title := "定义")
使用 `:=` 的定义会将右侧的项与该常量的名字相关联。
对于每个参数，定义体外层会包裹一个 {keywordOf Lean.Parser.Term.fun}`fun`，而类型则通过将参数绑定在函数类型中获得。
使用 {keyword}`def` 的定义是 {tech (key := "semireducible")}[半可约]的。


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

在 {tech (key := "module")}[模块]中，使用 {keyword}`def` 定义的主体默认不会对外公开。
:::

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.abbrev) (title := "缩写")
{deftech (key := "abbreviation")}[缩写]与使用 {keyword}`def` 的定义完全一致，区别仅在于它们是 {tech (key := "reducible")}[可约]的。


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

在 {tech (key := "module")}[模块]中，使用 {keyword}`abbrev` 定义的主体默认会对外公开。
:::


{deftech (key := "opaque constant")}_不透明常量_是在内核中不受 {tech (key := "δ")}[δ-归约]约束的已定义常量。
它们对于仅陈述某个函数的存在性很有用。
与 {tech (key := "axiom")}[公理]不同，不透明声明只能用于可被占据的类型，因此不会带来不一致风险。
亦不同于公理的是，该类型的占据元会在已编译代码中被实际使用。
还可以使用 {attr}`implemented_by` 属性指示编译器在编译该不透明常量时发出对其他函数的调用。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.opaque) (title := "不透明常量")
带右侧定义式的不透明常量会像其他定义一样被精译。
这表明该类型可被占据；该占据元本身不再扮演后续角色。

```grammar
$_:declModifiers
opaque $_ $_ := $_
```

也可以不给出右侧定义式。
此时精译器会通过合成一个 {name}`Inhabited` 实例来填充右侧；若失败，则尝试 {name}`Nonempty`：
```grammar
$_:declModifiers
opaque $_ $_
```
:::


# 定理
%%%
file := "Theorems"
tag := "theorems"
%%%


:::paragraph
由于 {tech (key := "proposition")}[命题]是其占据元可作为证明的类型，{deftech (key := "theorem")}[定理]与“定义”在技术上非常相似。
然而，由于它们的使用场景不同，许多细节上有所差异：

* 定理陈述必须是一个命题；
  而定义的类型可以属于任意 {tech (key := "universe")}[宇宙]。
* 定理的头部（即定理陈述）会在定理主体之前被完全精译。
  只有当区段变量（或依赖于它们的变量）出现在头部时，它们才会成为定理的参数。
  这可以避免更改证明时无意间改变定理陈述本身。
* 定理默认是 {tech (key := "irreducible")}[不可约]的。
  由于对同一命题的所有证明在 {tech (key := "definitional equality")}[定义相等]下是相等的，几乎没有理由去展开一个定理。
:::

定理也可以是递归的，但需满足与 {ref "recursive-definitions"}[递归函数定义]相同的条件。
不过，更常见的做法是使用 {tactic}`induction` 或 {tactic}`fun_induction` 等策略来完成证明。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.theorem) (title := "定理")
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

在 {tech (key := "module")}[模块]中，定理的证明默认不会对外公开。
:::




# 示例声明
%%%
file := "Example-Declarations"
tag := "example-declarations"
%%%


{deftech (key := "example")}[示例] 是一种匿名定义：会被精译，但随后丢弃。
示例有助于在开发过程中进行增量测试，也有助于读者更容易理解一个文件。


:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.example) (title := "示例")

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
