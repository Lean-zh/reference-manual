/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

set_option guard_msgs.diff true

#doc (Manual) "项" =>
%%%
tag := "terms"
file := some "Terms"
%%%


{deftech (key := "Terms")}_项_是在 Lean 中书写数学和程序的主要手段。
{deftech (key := "Lean elaborator")}[精译器]将它们翻译为 Lean 的最小核心语言，随后由内核检查并编译执行。
项的语法可以{ref "syntax-ext"}[任意扩展]；本章介绍 Lean 原生提供的项语法。

# 标识符
%%%
tag := "identifiers-and-resolution"
file := some "Identifiers"
%%%

:::syntax term (title := "标识符")
```
$x:ident
```
:::

标识符项是对名称的引用。{margin}[标识符的具体词法语法见 {ref "keywords-and-identifiers"}[Lean 具体语法一节]。]
标识符也会出现在绑定名称的上下文中，例如 {keywordOf Lean.Parser.Term.let}`let` 和 {keywordOf Lean.Parser.Term.fun}`fun`；不过，这些绑定位置本身并不是完整的项。
标识符到名称的映射并不简单：在{tech (key := "module")}[模块]中的任意位置，都可能打开了若干{tech (key := "namespaces")}[命名空间]，还可能存在{tech (key := "section variables")}[节变量]和局部绑定。
此外，标识符可以包含多个由点分隔的原子标识符；点既用于分隔命名空间与其内容，也用于分隔变量与采用{tech (key := "field notation")}[字段表示法]的字段或函数。
这会产生歧义，因为标识符 `A.B.C.D.e.f` 可能指下列任一含义：

 * 命名空间 `A.B.C.D.e` 中的名称 `f`（例如，在 `e` 的 {keywordOf Lean.Parser.Command.declaration}`where` 块中定义的函数）
 * 若 `A.B.C.D.e` 的类型为 `T`，则是将 `T.f` 应用于 `A.B.C.D.e`
 * 从名为 `A.B.C.D.e` 的结构中投影字段 `f`
 * 从结构值 `A` 依次投影字段 `B.C.D.e`，再用字段表示法应用 `f`
 * 若命名空间 `Q` 已打开，则可能指上述任一带 `Q` 前缀的含义，例如命名空间 `Q.A.B.C.D.e` 中的名称 `f`

此列表并不穷尽所有可能。
给定一个标识符，精译器必须找出它指向哪个或哪些名称，并判断末尾的组成部分中是否有字段，或通过字段表示法应用的函数。
这称为对名称进行{deftech (key := "resolve")}_解析_。

全局环境中的某些声明会在首次被引用时惰性创建。
若解析标识符的过程既创建了这样的声明，又得到对它的引用，就称为{deftech (key := "realizing")}_实现_该名称。
名称解析与名称实现遵循相同规则，因此本节虽只提及名称解析，但内容同时适用于二者。

名称解析受以下因素影响：
 * 附加到标识符上的{tech (key := "pre-resolved identifier")}[预解析名称]
 * 附加到标识符上的{tech (key := "macro scopes")}[宏作用域]
 * 作用域内的局部绑定，包括精译 {keywordOf Lean.Parser.Term.letrec}`let rec` 时创建的辅助定义
 * 当前模块传递导入的模块中用 {keywordOf Lean.Parser.Command.export}`export` 创建的别名
 * 当前{tech (key := "section scope")}[节作用域]，尤其是{tech (key := "current namespace")}[当前命名空间]、已打开的命名空间和节变量


标识符的任意前缀都可能解析为一组名称。
未参与解析过程的后缀随后会被视为字段投影或字段表示法。
较长前缀的解析优先于较短前缀；换言之，标识符中应尽可能少地把组成部分视为字段表示法。
标识符前缀可以指下列任一项，越靠前者优先级越高：
 1. 名称（包括宏作用域）与标识符前缀相同的局部绑定变量；较近的局部绑定优先于外层局部绑定
 2. 名称与标识符前缀相同的局部辅助定义
 3. 名称与标识符前缀相同的{tech (key := "section variable")}[节变量]
 3. 与“{tech (key := "current namespace")}[当前命名空间]的某个前缀加上标识符前缀”相同的全局名称，或在当前命名空间的某个前缀中存在别名的全局名称；当前命名空间的较长前缀优先于较短前缀
 4. 通过 {keywordOf Lean.Parser.Command.open}`open` 命令引入作用域、且与标识符前缀相同的全局名称


若标识符解析为多个名称，精译器会尝试使用其中每一个。
若恰好只有一个成功，就将其作为该标识符的含义。
若成功者不止一个，或全部失败，都会报错。

::::keepEnv
:::example "局部名称优先"
局部绑定优先于全局绑定：
```lean (name := localOverGlobal)
def x := "global"

#eval
  let x := "local"
  x
```
```leanOutput localOverGlobal
"local"
```
名称最内层的局部绑定优先于其他绑定：
```lean (name := innermostLocal)
#eval
  let x := "outer"
  let x := "inner"
  x
```
```leanOutput innermostLocal
"inner"
```
:::
::::

::::keepEnv
:::example "当前命名空间的较长前缀优先"
命名空间 `A`、`B` 和 `C` 相互嵌套。
`A` 和 `C` 都包含 `x` 的定义。
```lean (name := NS)
namespace A
def x := "A.x"
namespace B
namespace C
def x := "A.B.C.x"
```

当前命名空间为 `A.B.C` 时，{lean}`x` 解析为 {lean}`A.B.C.x`。
```lean (name := NSC)
#eval x
```
```leanOutput NSC
"A.B.C.x"
```
当前命名空间为 `A.B` 时，{lean}`x` 解析为 {lean}`A.x`。
```lean (name := NSB)
end C
#eval x
```
```leanOutput NSB
"A.x"
```
:::
::::

::::keepEnv
:::example "较长的标识符前缀优先"
当标识符可能指从不同名称进行的投影时，名称最长者优先：
```lean
structure A where
  y : String
deriving Repr

structure B where
  y : A
deriving Repr

def y : B := ⟨⟨"shorter"⟩⟩
def y.y : A := ⟨"longer"⟩
```
给定上述声明，{lean}`y.y.y` 原则上既可指 {name}`y` 的 {name B.y}`y` 字段的 {name A.y}`y` 字段，也可指 {name}`y.y` 的 {name A.y}`y` 字段。
它指 {name}`y.y` 的 {name A.y}`y` 字段，因为名称 {name}`y.y` 是 `y.y.y` 比名称 {name}`y` 更长的前缀：
```lean (name := yyy)
#eval y.y.y
```
```leanOutput yyy
"longer"
```
:::
::::

::::keepEnv
:::example "当前命名空间的内容优先于已打开的命名空间"
当标识符既可能指当前命名空间某个前缀中定义的名称，也可能指已打开命名空间中的名称时，前者优先。
```lean
namespace A
def x := "A.x"
end A

namespace B
def x := "B.x"
namespace C
open A
#eval x
```
尽管打开 `A` 的时间晚于 {name}`B.x` 的声明，标识符 `x` 仍解析为 {name}`B.x` 而非 {name}`A.x`，因为 `B` 是当前命名空间 `B.C` 的前缀。
```lean (name := nestedVsOpen)
#eval x
```
```leanOutput nestedVsOpen
"B.x"
```
:::
::::


:::example "有歧义的标识符"
在此例中，`x` 既可能指 {name}`A.x`，也可能指 {name}`B.x`，且二者都不优先。
由于二者类型相同，因此会报错。
```lean (name := ambi) +error
def A.x := "A.x"
def B.x := "B.x"
open A
open B
#eval x
```
```leanOutput ambi (whitespace := lax)
Ambiguous term
  x
Possible interpretations:
  B.x : String

  A.x : String
```
:::


:::example "通过类型消歧"
当原本有歧义的名称类型不同时，会利用类型消除歧义：
```lean (name := ambiNo)
def C.x := "C.x"
def D.x := 3
open C
open D
#eval (x : String)
```
```leanOutput ambiNo
"C.x"
```
:::



## 前导 `.`
%%%
tag := "The-Lean-Language-Reference--Terms--Identifiers--Leading--___"
%%%

当标识符以点（`.`）开头时，会使用精译器对表达式的预期类型来解析它，而不是使用当前命名空间和已打开命名空间的集合。
{tech (key := "Generalized field notation")}[广义字段表示法]与此相关：这种{deftech (key := "leading dot notation")}_前导点表示法_使用标识符的预期类型将其解析为名称，而字段表示法使用紧邻点之前的项的推断类型。

带前导 `.` 的标识符会在{deftech (key := "expected type's namespace")}_预期类型的命名空间_中查找。
若项的预期类型是应用于零个或多个实参的常量，则其命名空间就是该常量的名称。
若该类型不是常量的应用（例如函数、元变量或宇宙），则它没有命名空间。

若在预期类型的命名空间中找不到该名称，但展开这个常量能得到另一常量，则转而查找后者的命名空间。
重复此过程，直到遇到并非常量应用的内容，或常量无法继续展开为止。

::::keepEnv
:::example "前导 `.`"
{name List.replicate}`.replicate` 的预期类型是 `List Unit`。
该类型的命名空间是 `List`，因此 {name List.replicate}`.replicate` 解析为 {name List.replicate}`List.replicate`。
```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::

:::example "前导 `.` 与展开定义"
{name List.replicate}`.replicate` 的预期类型是 `MyList Unit`。
该类型的命名空间是 `MyList`，但不存在定义 `MyList.replicate`。
展开 {lean}`MyList Unit` 得到 {lean}`List Unit`，因此 {name List.replicate}`.replicate` 解析为 {name List.replicate}`List.replicate`。
```lean (name := dotRep)
def MyList α := List α
#eval show MyList Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::
::::

# 函数类型
%%%
tag := "function-types"
file := some "Function-Types"
%%%

Lean 的函数类型所描述的不只是函数的定义域和值域。
它们还为应用处的精译提供指令：某些参数应通过合一或{ref "instance-synth"}[类型类合成]自动确定，某些参数是带默认值的可选参数，还有一些参数应使用自定义策略脚本合成。
此外，其语法还支持简写{tech (key := "currying")}[柯里化]函数。

:::syntax term (title := "函数类型")
依赖函数类型包含显式名称：
```grammar
($x:ident : $t) → $t2
```

非依赖函数类型则不包含：
```grammar
$t1:term → $t2
```
:::

:::syntax term (title := "柯里化函数类型")
依赖函数类型可在同一对圆括号中包含多个类型相同的参数：
```grammar
($x:ident* : $t) → $t
```
这等价于在嵌套函数类型中为每个参数名称重复类型标注。
:::

:::syntax term (title := "隐式、可选与自动参数")
函数类型可以描述接受隐式参数、实例隐式参数、可选参数和自动参数的函数。
除实例隐式参数外，其他参数都要求一个或多个名称。
```grammar
($x:ident* : $t := $e) → $t
```
```grammar
($x:ident* : $t := by $tacs) → $t
```
```grammar
{$x:ident* : $t} → $t
```
```grammar
[$t] → $t
```
```grammar
[$x:ident : $t] → $t
```
```grammar
⦃$x:ident* : $t⦄ → $t
```

:::

:::example "多个同类型参数"
{name}`Nat.add` 的类型可以用以下方式书写：

 * {lean}`Nat → Nat → Nat`

 * {lean}`(a : Nat) → (b : Nat) → Nat`

 * {lean}`(a b : Nat) → Nat`

后两种类型允许用{tech (key := "named arguments")}[具名实参]调用函数；除此之外，三者等价。
:::

# 函数

%%%
tag := "function-terms"
file := some "Functions"
%%%


可以通过由 {keywordOf Lean.Parser.Term.fun}`fun` 关键字引入的抽象来创建函数类型的项。{margin}[在不同社群中，函数抽象也称为 _λ 抽象_，源于 Alonzo Church 为其采用的记法；也称为_匿名函数_，因为不必在全局环境中用名称定义它们。]
核心类型论中的抽象只允许绑定单个变量，而 Lean 的高层语法中的函数项则相当灵活。

:::syntax term (title := "函数抽象")
最基本的函数抽象引入一个变量来代表函数参数：

```grammar
fun $x:ident => $t
```

精译时，Lean 必须能够确定函数的定义域。
类型指派是提供这一信息的一种方式：

```grammar
fun $x:ident : term => $t
```
:::

用 {keywordOf Lean.Parser.Command.declaration (parser := Lean.Parser.Command.definition)}`def` 等关键字定义的函数定义会脱糖为 {keywordOf Lean.Parser.Term.fun}`fun`。
另一方面，归纳类型声明会引入具有函数类型的新值（构造器和类型构造器），它们本身无法只用 {keywordOf Lean.Parser.Term.fun}`fun` 实现。

:::syntax term (title := "柯里化函数")


{keywordOf Lean.Parser.Term.fun}`fun` 后可接受多个参数名称：
```grammar
fun $x:ident $x:ident* => $t
```

```grammar
fun $x:ident $x:ident* : $t:term => $t
```

多个参数使用不同类型标注时需要圆括号：

```grammar
free{"fun " "(" (ident)* ": " term")" " =>" term}
```

这些写法等价于书写嵌套的 {keywordOf Lean.Parser.Term.fun}`fun` 项。
:::

本节所述的所有语法中，{keywordOf Lean.Parser.Term.fun}`=>` 都可以替换为 {keywordOf Lean.Parser.Term.fun}`↦`。

函数抽象还可以在参数规格中使用模式匹配语法，从而不必引入一个随即就要解构的局部变量。
此语法见{ref "pattern-fun"}[模式匹配一节]。

## 隐式参数
%%%
tag := "implicit-functions"
%%%


Lean 支持函数的隐式参数。
这意味着 Lean 自身可以为函数提供实参，而不要求用户提供全部所需实参。
隐式参数分为三类：

  : 普通隐式参数

    普通{deftech (key := "implicit")}[隐式]参数是应由 Lean 通过合一确定其值的函数参数。
    换言之，每个调用处都应恰好存在一个候选实参值，使整个函数调用良类型。
    每次函数出现时，Lean 精译器都会尝试为所有隐式实参寻找值。
    普通隐式参数写在花括号（`{` 和 `}`）中。

  : 严格隐式参数

    {deftech (key := "Strict implicit")}_严格隐式_参数与普通隐式参数相同，区别在于只有调用处提供了后续显式实参时，Lean 才会尝试寻找实参值。
    严格隐式参数写在双花括号（`⦃` 和 `⦄`，或 `{{` 和 `}}`）中。

  : 实例隐式参数

    {tech (key := "instance implicit")}_实例隐式_参数的实参通过{ref "instance-synth"}[类型类合成]查找。
    实例隐式参数写在方括号（`[` 和 `]`）中。
    与其他种类的隐式参数不同，不带 `:` 书写的实例隐式参数指定的是参数类型，而不是提供名称。
    此外，只允许一个名称。
    大多数实例隐式参数会省略参数名称，因为作为函数参数合成的实例即使没有显式命名，也已经可以在函数体中使用。

::::keepEnv
:::example "普通隐式参数与严格隐式参数"
函数 {lean}`f` 与 {lean}`g` 的区别在于，`α` 在 {lean}`f` 中是严格隐式的：
```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

应用于具体实参时，这两个函数的精译结果相同：
```lean
example : f 2 = g 2 := rfl
```

然而，未提供显式实参时，使用 {lean}`f` 不要求求解隐式的 `α`：
```lean
example := f
```
但使用 `g` 的确要求求解它；若可用信息不足，精译就会失败：
```lean +error (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument `α`
  @g ?m.3
context:
⊢ Type
```
:::
::::


:::syntax term (title := "带不同绑定器的函数")
{keywordOf Lean.Parser.Term.fun}`fun` 最一般的语法接受一系列绑定器：
```grammar
fun $p:funBinder $p:funBinder* => $t
```
:::


:::syntax Lean.Parser.Term.funBinder (title := "函数绑定器")
函数绑定器可以是标识符：
```grammar
$x:ident
```
带圆括号的标识符序列：
```grammar
($x:ident $y:ident*)
```
带类型指派的标识符序列：
```grammar
($x:ident $y:ident* : $t)
```
带或不带类型指派的隐式参数：
```grammar
{$x:ident $x:ident*}
```
```grammar
{$x:ident $x:ident* : $t}
```
匿名或具名的实例隐式参数：
```grammar
[$t:term]
```
```grammar
[$x:ident : $t]
```
或者带或不带类型指派的严格隐式参数：
```grammar
⦃$x:ident $x:ident*⦄
```
```grammar
⦃$x:ident* : $t⦄
```

与往常一样，可以用 `_` 代替标识符来创建匿名参数；`⦃` 和 `⦄` 也可分别写成 `{{` 和 `}}`。
:::



Lean 的核心语言不区分隐式参数、实例参数和显式参数：各种函数及函数类型在定义上相等。
这些区别只能在精译过程中观察到。

```lean -show
-- 上一段论述的佐证
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```


若函数的预期类型包含隐式参数，而其绑定器不包含，则所得函数最终的参数可能比代码中的绑定器所指明的更多。
这是因为隐式参数会自动添加。

:::example "来自类型的隐式参数"
恒等函数可以只用一个显式参数书写。
只要其类型已知，隐式类型参数就会自动添加。
```lean (name := funImplAdd)
#check (fun x => x : {α : Type} → α → α)
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```

以下写法全都等价：
```lean (name := funImplThere)
#check (fun {α} x => x : {α : Type} → α → α)
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn)
#check (fun {α} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn2)
#check (fun {α : Type} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```

:::

# 函数应用
%%%
tag := "function-application"
file := some "Function-Application"
%%%

通常，函数应用以并置方式书写：实参放在函数之后，二者之间至少有一个空格。
在 Lean 的类型论中，所有函数都恰好接受一个实参并产生一个值。
每个函数应用都将一个函数与一个实参组合起来。
多个实参通过柯里化表示。

高层项语言将函数及其一个或多个实参视为一个整体，除普通位置实参外，还支持隐式实参、可选实参和具名实参等附加功能。
精译器会将这些转换为核心类型论中更简单的模型。

:::freeSyntax term (title := "函数应用")
函数应用由一个项后接一个或多个实参组成；也可以后接零个或多个实参，并以{deftech (key := "ellipsis")}[省略号]结尾。
```grammar
$e:term $e:argument+
***************
$e:term $e:argument* ".."
```
:::

{TODO}[在遍历阶段用语法种类作标注，以供传入超链接使用]
:::freeSyntax Lean.Parser.Term.argument (title := "实参")
函数实参可以是项，也可以是{deftech (key := "named arguments")}[具名实参]。
```grammar
$e:term
***********
"("$x:ident ":=" $e:term")"
```
:::

函数的核心语言类型决定实参在最终表达式中的位置。
函数类型包含其预期参数的名称。
在 Lean 的核心语言中，非依赖函数类型编码为参数名称不出现在类型体中的依赖函数类型。
此外，这些名称由内部选取，无法写作具名实参的名称；这对于防止意外捕获十分重要。

函数预期的每个参数都有名称。
递归遍历函数的实参类型时，按以下方式从实参序列中选择实参：
 * 若参数名称与某个具名实参提供的名称匹配，则选择该实参。
 * 若参数是{tech (key := "implicit")}[隐式]参数，则创建并选择一个具有该参数类型的新元变量。
 * 若参数是{tech (key := "instance implicit")}[实例隐式]参数，则创建并插入一个具有该参数类型的新实例元变量。实例元变量会被安排稍后合成。
 * 若参数是{tech (key := "strict implicit")}[严格隐式]参数，且仍有尚未选择的具名或位置实参，则创建并选择一个具有该参数类型的新元变量。
 * 若参数是显式参数，则选择并精译下一个位置实参。若没有位置实参：
   * 若参数声明为{tech (key := "optional parameter")}[可选参数]，则选择其默认值作为实参。
   * 若参数是{tech (key := "automatic parameter")}[自动参数]，则执行其关联的策略脚本来构造实参。
   * 若参数既非可选也非自动，且没有省略号，则选择一个新变量作为实参。若有省略号，则像实参为隐式的一样选择一个新元变量。

有一种特殊情况：当函数应用出现在{ref "pattern-matching"}[模式]中且存在省略号时，可选实参和自动实参会变为通配模式（`_`），而不是被插入。

若类型不是函数类型但仍有实参剩余，则会报错。
插入所有实参后，若存在省略号，则所有缺失的实参都会设为新元变量，如同它们是隐式实参一样。
若为缺失的显式位置实参创建了新变量，则整个应用会包裹在绑定这些变量的 {keywordOf Lean.Parser.Term.fun}`fun` 项中。
最后调用实例合成，并尽可能求解更多元变量：
 1. 推断整个函数应用的类型。类型推断期间发生的合一可能会求解某些元变量。
 2. 合成实例元变量。仅当推断类型是某个实例的输出参数元变量时，才使用{tech (key := "Default instances")}[默认实例]。
 3. 若存在预期类型，则将其与推断类型合一；但会丢弃此次合一产生的错误。若预期类型与推断类型可能相等，合一就能求解剩余的隐式实参元变量。若二者不可能相等，也不会抛出错误，因为外围精译器或许能插入{tech (key := "coercions")}[强制转换]或{tech (key := "lift")}[单子提升]。


::::keepEnv
:::example "具名实参"
```lean -show
set_option linter.unusedVariables false
```
可以使用 {keywordOf Lean.Parser.Command.check}`#check` 命令查看为函数调用插入了哪些实参。

函数 {name}`sum3` 接受三个显式的 {lean}`Nat` 参数，名称分别为 `x`、`y` 和 `z`。
```lean
def sum3 (x y z : Nat) : Nat := x + y + z
```

三个实参都可以按位置提供。
```lean (name := sum31)
#check sum3 1 3 8
```
```leanOutput sum31
sum3 1 3 8 : Nat
```

它们也可以按名称提供。
```lean (name := sum32)
#check sum3 (x := 1) (y := 3) (z := 8)
```
```leanOutput sum32
sum3 1 3 8 : Nat
```

按名称提供实参时，可以采用任意顺序。
```lean (name := sum33)
#check sum3 (y := 3) (z := 8) (x := 1)
```
```leanOutput sum33
sum3 1 3 8 : Nat
```

具名实参与位置实参可以自由混用。
```lean (name := sum34)
#check sum3 1 (z := 8) (y := 3)
```
```leanOutput sum34
sum3 1 3 8 : Nat
```

具名实参与位置实参可以自由混用。
若按名称提供了实参，就会使用该实参，即使它出现在本可使用的位置实参之后。
```lean (name := sum342)
#check sum3 1 (x := 8) (y := 3)
```
```leanOutput sum342
sum3 8 3 1 : Nat
```

若要在尚未提供的实参之后插入具名实参，则会创建一个已填入所提供实参的函数。
```lean (name := sum35)
#check sum3 (z := 8)
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```

在幕后，实参名称会保留在函数类型中。
这意味着其余实参仍可再次按名称传递。
```lean (name := sum36)
#check (sum3 (z := 8)) (y := 1)
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```

参数名称取自函数的_类型_，函数参数所用名称不必与类型中使用的名称匹配。
这意味着，与参数名称冲突的局部绑定不会妨碍具名参数的使用，因为 Lean 会重命名函数参数以避免冲突，同时保持类型中的名称不变。
```lean (name := sum15)
#check let x := 15; sum3 (z := x)
```
这里，用于命名 {name}`sum3` 第一个实参的 `x` 已被替换，以免与外围的 {keywordOf Parser.Term.let}`let` 冲突：
```leanOutput sum15
let x := 15;
fun x_1 y => sum3 x_1 y x : Nat → Nat → Nat
```
尽管 `x` 已被重命名，仍可按名称传递它：
```lean (name := xNoCapture)
#check (let x := 15; sum3 (z := x)) (x := 4)
```
```leanOutput xNoCapture
(let x := 15;
  fun x_1 y => sum3 x_1 y x)
  4 : Nat → Nat
```
这是因为类型中仍使用名称 `x`。
启用选项 {option}`pp.piBinderNames` 可显示类型中的参数名称：
```lean (name := xRenamed)
set_option pp.piBinderNames true in
#check let x := 15; sum3 (z := x)
```
```leanOutput xRenamed
let x := 15;
fun x_1 y => sum3 x_1 y x : (x y : Nat) → Nat
```
:::
::::


可选参数和自动参数并非 Lean 核心类型论的一部分。
它们使用 {name}`optParam` 和 {name}`autoParam` {tech (key := "gadgets")}[辅助机制]进行编码。

{docstring optParam}

{docstring autoParam}

## 广义字段表示法
%%%
tag := "generalized-field-notation"
%%%

{ref "structure-fields"}[关于结构字段的小节]介绍了从类型为结构的项中投影字段的表示法。
广义字段表示法由一个项、一个点号（`.`）和一个标识符依次组成，三者之间不能有空格。

:::syntax term (title := "字段表示法")
```grammar
$e:term.$f:ident
```
:::

如果一个项的类型是应用于零个或多个参数的常量，那么无论该项是不是拥有字段的结构或类型类实例，都可以用{deftech (key := "field notation")}[字段表示法]将一个函数应用于它。
使用字段表示法应用其他函数称为{deftech (key := "generalized field notation")}_广义字段表示法_。

点号后的标识符会在该项类型的命名空间中查找，也就是在这个常量名称所对应的命名空间中查找。
如果类型不是常量的应用（例如，它是一个元变量或宇宙），那么它就没有命名空间，因而不能使用广义字段表示法。
特别地，如果表达式是函数，广义字段表示法会在 `Function` 命名空间中查找。因此，{lean}`Nat.add.uncurry` 是广义字段表示法的一种用法，它等价于 {lean}`Function.uncurry Nat.add`。

如果找不到该字段，但可以展开这个常量，得到另一个常量或常量应用类型，那么就用新的常量重复这一过程。

找到函数后，点号前的项会成为该函数的一个参数。
具体而言，它会成为第一个不会导致类型错误的显式参数。
除此之外，该应用会照常精译。

:::example "广义字段表示法"
类型 {lean}`Username` 是常量，因此可以用广义字段表示法，将 {name}`Username` 命名空间中的函数应用于类型为 {lean}`Username` 的项。
```lean
def Username := String
```

{name}`Username.validate` 就是这样的函数之一，它检查用户名是否没有前导空白，且是否只使用了少量允许的字符。
在其定义中，广义字段表示法用于调用函数 {lean}`String.isPrefixOf`、{name}`String.any`、{lean}`Char.isAlpha` 和 {lean}`Char.isDigit`。
{lean}`String.isPrefixOf` 接受两个 {lean}`String` 参数；在这里，{lean}`" "` 用作第一个参数，因为它是点号前的项。
虽然 {lean}`name` 的类型是 {lean}`Username`，但仍可用广义字段表示法对它调用 {name}`String.any`，这是因为 `Username.any` 没有定义，而 {lean}`Username` 可展开为 {lean}`String`。

```lean
def Username.validate (name : Username) : Except String Unit := do
  if " ".isPrefixOf name then
    throw "Unexpected leading whitespace"
  if name.any notOk then
    throw "Unexpected character"
  return ()
where
  notOk (c : Char) : Bool :=
    !c.isAlpha &&
    !c.isDigit &&
    !c ∈ ['_', ' ']

def adminUser : Username := "admin"
```

然而，不能用字段表示法对 {lean}`"admin"` 调用 {lean}`Username.validate`，因为 {lean}`String` 不会展开为 {lean}`Username`。
```lean +error (name := notString)
#eval "admin".validate
```
```leanOutput notString
Invalid field `validate`: The environment does not contain `String.validate`, so it is not possible to project the field `validate` from an expression
  "admin"
of type `String`
```

另一方面，{lean}`adminUser` 的类型是 {lean}`Username`，因此可以用广义字段表示法调用 {lean}`Username.validate` 函数：
```lean (name := isUsername)
#eval adminUser.validate
```
```leanOutput isUsername
Except.ok ()
```

反过来，确实可以用广义字段表示法对 {lean}`Username` 值 {lean}`adminUser` 调用 {name}`String.any`，因为类型 {lean}`Username` 可展开为 {lean}`String`。
```lean (name := isString1)
#eval adminUser.any (· == 'm')
```
```leanOutput isString1
true
```
:::

{optionDocs pp.fieldNotation}

:::syntax attr (title := "控制字段表示法")
{attr}`pp_nodot` 属性使 Lean 的美化打印器在打印函数时不使用字段表示法。
```grammar
pp_nodot
```
:::

::::keepEnv
:::example "关闭字段表示法"
默认情况下，{lean}`Nat.half` 使用字段表示法打印。
```lean
def Nat.half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n.half + 1
```
```lean (name := succ1)
#check Nat.half Nat.zero
```
```leanOutput succ1
Nat.zero.half : Nat
```
为 {name}`Nat.half` 添加 {attr}`pp_nodot` 后，显示该项时会改用普通的函数应用语法。
```lean (name := succ2)
attribute [pp_nodot] Nat.half

#check Nat.half Nat.zero
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
:::
::::

## 管道语法
%%%
tag := "The-Lean-Language-Reference--Terms--Function-Application--Pipeline-Syntax"
%%%

管道语法提供了函数应用的其他写法。
重复使用管道时，可借助解析优先级把函数依次应用于位置参数，而不必使用嵌套括号。

:::syntax term (title := "管道")
右管道表示法把管道右侧的项应用于左侧的项。
```grammar
$e |> $e
```
左管道表示法把管道左侧的项应用于右侧的项。
```grammar
$e <| $e
```
:::

右管道表示法背后的直观理解是：左侧的值被送入第一个函数，其结果再送入第二个函数，以此类推。
在左管道表示法中，右侧的值向左传递。

:::example "右管道表示法"
右管道可以在一个项上依次调用一系列函数。
对读者而言，它往往更强调正在变换的数据。
```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
:::

:::example "左管道表示法"
左管道可以在一个项上依次调用一系列函数。
它往往更强调函数而非数据。
```lean (name := lPipe)
#eval List.head! <| List.reverse <| String.toList <| "Hello!"
```
```leanOutput lPipe
'!'
```
:::

:::syntax term (title := "管道字段")
管道表示法还有一个用于{tech (key := "generalized field notation")}[广义字段表示法]的版本。
```grammar
$e |>.$_:ident
```
```grammar
$e |>.$_:fieldIdx
```
:::

::::keepEnv
```lean -show
section
universe u
axiom T : Nat → Type u
variable {e : T 3} {arg : Char}
axiom T.f : {n : Nat} → Char → T n → String
```

{lean}`e |>.f arg` 是 {lean}`(e).f arg` 的另一种语法。


:::example "管道字段"

有些函数的参数顺序不便于使用管道。
例如，{name}`Array.push` 的第一个参数是数组，而不是 {lean}`Nat`，因而会产生以下错误：
```lean (name := arrPush) +error
#eval #[1, 2, 3] |> Array.push 4
```
```leanOutput arrPush
failed to synthesize instance of type class
  OfNat (Array ?m.2) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.2
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

使用管道字段表示法会把数组插入第一个类型正确的位置：
```lean (name := arrPush2)
#eval #[1, 2, 3] |>.push 4
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```

这一过程可以反复进行：
```lean (name := arrPush3)
#eval #[1, 2, 3] |>.push 4 |>.reverse |>.push 0 |>.reverse
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
:::


```lean -show
end
```
::::

# 数值字面量
%%%
tag := "numeric-literals"
file := "Numeric-Literals"
%%%

数值字面量分为两类：自然数字面量和{deftech (key := "scientific literals")}[科学计数字面量]。
二者都通过{tech (key := "type class")}[类型类]重载。

## 自然数
%%%
tag := "nat-literals"
%%%

```lean -show
section
variable {n : Nat}
```

自然数可以用以下几种形式指定：

 - 由数字 0 至 9 组成的序列是十进制字面量
 - `0b` 或 `0B` 后跟由一个或多个 0 与 1 组成的序列，是二进制字面量
 - `0o` 或 `0O` 后跟由一个或多个 0 至 7 的数字组成的序列，是八进制字面量
 - `0x` 或 `0X` 后跟由一个或多个十六进制数字（0 至 9 以及 A 至 F，不区分大小写）组成的序列，是十六进制字面量

所有数值字面量内部都可以包含下划线，但二进制、八进制或十六进制字面量的前两个字符之间除外。
这些下划线旨在帮助以自然方式对数字分组，例如 {lean}`1_000_000` 或 {lean}`0x_c0de_cafe`。
（虽然可以将数字 123 写成 {lean}`1_2__3`，但不推荐这样做。）

Lean 遇到自然数字面量 {lean}`n` 时，会通过重载方法 {lean}`OfNat.ofNat n` 解释它。
{lean}`OfNat Nat n` 的一个{tech (key := "default instance")}[默认实例]确保在没有其他类型信息时可以推断出类型 {lean}`Nat`。

{docstring OfNat}

```lean -show
end
```

:::example "自定义自然数字面量"
结构 {lean}`NatInterval` 表示一个自然数区间。
```lean
structure NatInterval where
  low : Nat
  high : Nat
  low_le_high : low ≤ high

instance : Add NatInterval where
  add
    | ⟨lo1, hi1, le1⟩, ⟨lo2, hi2, le2⟩ =>
      ⟨lo1 + lo2, hi1 + hi2, by grind⟩
```

{name}`OfNat` 实例使自然数字面量可以用来表示区间：
```lean
instance : OfNat NatInterval n where
  ofNat := ⟨n, n, by omega⟩
```
```lean (name := eval8Interval)
#eval (8 : NatInterval)
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
```lean (name := eval7Interval)
#eval (0b111 : NatInterval)
```
```leanOutput eval7Interval
{ low := 7, high := 7, low_le_high := _ }
```
:::

并没有单独的整数字面量。
{lean}`-5` 这样的项由应用于自然数字面量的前缀取负操作构成（它可以通过 {name}`Neg` 类型类重载）。

## 科学计数
%%%
tag := "The-Lean-Language-Reference--Terms--Numeric-Literals--Scientific-Numbers"
%%%

科学计数字面量由一个十进制数字序列、一个可选的小数部分（句点后跟零个或多个十进制数字）和一个可选的指数部分（字母 `e` 后跟可选的 `+` 或 `-`，再跟一个或多个十进制数字）组成，各部分之间不能有空白。
科学计数字面量通过 {name}`OfScientific` 类型类重载。

{docstring OfScientific}

存在用于 {name}`Float` 和 {name}`Float32` 的 {lean}`OfScientific` 实例，但不存在单独的浮点字面量。

## 字符串
%%%
tag := "The-Lean-Language-Reference--Terms--Numeric-Literals--Strings"
%%%

字符串字面量在{ref "string-syntax"}[关于字符串的章节]中介绍。

## 列表与数组
%%%
tag := "The-Lean-Language-Reference--Terms--Numeric-Literals--Lists-and-Arrays"
%%%

列表和数组字面量是在方括号内以逗号分隔的元素序列，数组的方括号前还带有井号（`#`）。
数组字面量会被解释为由转换调用包裹的列表字面量。
出于性能考虑，非常长的列表和数组字面量会被转换为一系列局部定义，而不仅仅是列表构造器的迭代应用。

:::syntax term (title := "列表字面量")
```grammar
[$_,*]
```
:::

:::syntax term (title := "数组字面量")
```grammar
#[$_,*]
```
:::

:::example "长列表字面量"
此列表包含 32 个元素。
生成的代码是 {name}`List.cons` 的迭代应用：
```lean (name := almostLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1]
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```

包含 33 个元素时，列表字面量会变成一系列局部定义：
```lean (name := indeedLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1]
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```

:::

# 结构与构造器
%%%
tag := "structures-and-constructors"
file := "Structures-and-Constructors"
%%%

{ref "anonymous-constructor-syntax"}[匿名构造器]和{ref "structure-constructors"}[结构实例语法]在各自的小节中介绍。

# 条件表达式
%%%
tag := "if-then-else"
file := "Conditionals"
%%%

条件表达式用于检查一个命题是真是假。{margin}[尽管语法相似，{ref "tactic-language-branching"}[策略语言中]使用的 {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` 和{ref "tactic-language-branching"}[`do` 记法中]使用的 {keywordOf Lean.Parser.Term.doIf}`if` 是各自独立的语法形式，并在各自的小节中介绍。]
这要求该命题具有 {name}`Decidable` 实例，因为不可能检查_任意_命题是真是假。
从 {name}`Bool` 到 {lean}`Prop` 还有一个{tech (key := "coercion")}[强制转换]，它会产生一个可判定命题（即所涉及的 {name}`Bool` 等于 {name}`true`）；这在{ref "decidable-propositions"}[关于可判定性的小节]中介绍。

条件表达式有两个版本：一个只进行情况区分，另一个还会向局部上下文中加入关于该命题为真或为假的假设。
这使运行时检查能够生成编译时证据，以便静态排除错误。

:::syntax term (title := "条件表达式")
没有名称标注时，条件表达式只表达控制流。
```grammar
if $e then
  $e
else
  $e
```

有名称标注时，{keywordOf termDepIfThenElse}`if` 的两个分支可以分别使用关于该命题为真或为假的局部假设。
```grammar
if $h : $e then
  $e
else
  $e
```
:::


::::keepEnv
:::example "检查数组边界"

数组索引要求有证据表明相应索引位于数组边界内，因此 {name}`getThird` 无法精译。

```lean +error -keep (name := getThird1)
def getThird (xs : Array α) : α := xs[2]
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

将返回类型放宽为 {name}`Option` 并添加边界检查后，仍会得到相同的错误。
这是因为索引位于边界内的证明没有被加入局部上下文。
```lean +error -keep (name := getThird2)
def getThird (xs : Array α) : Option α :=
  if xs.size ≤ 2 then none
  else xs[2]
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

为证明命名为 `h`，就足以使执行边界检查的策略成功，尽管它并未显式出现在程序文本中。
```lean
def getThird (xs : Array α) : Option α :=
  if h : xs.size ≤ 2 then none
  else xs[2]
```

:::
::::

{keywordOf termIfLet}`if` 还有一个模式匹配版本。
如果模式匹配，就进入第一个分支并绑定模式变量。
如果模式不匹配，就进入第二个分支。

:::syntax term (title := "模式匹配条件表达式")
```grammar
if let $p := $e then
  $e
else
  $e
```
:::


如果需要只接受 {name}`Bool` 的条件语句，可以使用 {keywordOf boolIfThenElse}`bif` 变体。
:::syntax term (title := "仅布尔值条件表达式")
```grammar
bif $e then
  $e
else
  $e
```
:::


# Pattern Matching
%%%
tag := "pattern-matching"
%%%


{deftech}_Pattern matching_ is a way to recognize and destructure values using a syntax of {deftech}_patterns_ that are a subset of the terms.
A pattern that recognizes and destructures a value is similar to the syntax that would be used to construct the value.
One or more {deftech}_match discriminants_ are simultaneously compared to a series of {deftech}_match alternatives_.
Discriminants may be named.
Each alternative contains one or more comma-separated sequences of patterns; all pattern sequences must contain the same number of patterns as there are discriminants.
When a pattern sequence matches all of the discriminants, the term following the corresponding {keywordOf Lean.Parser.Term.match}`=>` is evaluated in an environment extended with values for each {tech}[pattern variable] as well as an equality hypothesis for each named discriminant.
This term is called the {deftech}_right-hand side_ of the match alternative.

:::syntax term (title := "Pattern Matching")
```grammar
match
    $[(generalizing := $e)]?
    $[(motive := $e)]?
    $[$d:matchDiscr],*
  with
$[| $[$e,*]|* => $e]*
```
:::

:::syntax matchDiscr (title := "Match Discriminants") -open
```grammar
$e:term
```
```grammar
$h:ident : $e:term
```
:::

Pattern matching expressions may alternatively use {tech}[quasiquotations] as patterns, matching the corresponding {name}`Lean.Syntax` values and treating the contents of {tech}[antiquotations] as ordinary patterns.
Quotation patterns are compiled differently than other patterns, so if one pattern in a {keywordOf Lean.Parser.Term.match}`match` is syntax, then all of them must be.
Quotation patterns are described in {ref "quote-patterns"}[the section on quotations].

Patterns are a subset of the terms.
They consist of the following:

: Catch-All Patterns

  The hole syntax {lean}`_` is a pattern that matches any value and binds no pattern variables.
  Catch-all patterns are not entirely equivalent to unused pattern variables.
  They can be used in positions where the pattern's typing would otherwise require a more specific {tech}[inaccessible pattern], while variables cannot be used in these positions.

: Identifiers

  If an identifier is not bound in the current scope and is not applied to arguments, then it represents a pattern variable.
  {deftech}_Pattern variables_ match any value, and the values thus matched are bound to the pattern variable in the local environment in which the {tech}[right-hand side] is evaluated.
  If the identifier is bound, it is a pattern if it is bound to the {tech}[constructor] of an {tech}[inductive type] or if its definition has the {attr}`match_pattern` attribute.

: Applications

  Function applications are patterns if the function being applied is an identifier that is bound to a constructor or that has the {attr}`match_pattern` attribute and if all arguments are also patterns.
  If the identifier is a constructor, the pattern matches values built with that constructor if the argument patterns match the constructor's arguments.
  If it is a function with the {attr}`match_pattern` attribute, then the function application is unfolded and the resulting term's {tech}[normal form] is used as the pattern.
  Default arguments are inserted as usual, and their normal forms are used as patterns.
  {tech (key := "ellipsis")}[Ellipses], however, result in all further arguments being treated as universal patterns, even those with associated default values or tactics.

: Literals

  {ref "char-syntax"}[Character literals] and {ref "string-syntax"}[string literals] are patterns that match the corresponding character or string.
  {ref "raw-string-literals"}[Raw string literals] are allowed as patterns, but {ref "string-interpolation"}[interpolated strings] are not.
  {ref "nat-syntax"}[Natural number literals] in patterns are interpreted by synthesizing the corresponding {name}`OfNat` instance and reducing the resulting term to {tech}[normal form], which must be a pattern.
  Similarly, {tech}[scientific literals] are interpreted via the corresponding {name}`OfScientific` instance.

: Structure Instances

  {tech}[Structure instances] may be used as patterns.
  They are interpreted as the corresponding structure constructor.

: Quoted names

  Quoted names, such as {lean}`` `x `` and {lean}``` ``none ```, match the corresponding {name}`Lean.Name` value.

: Macros

  Macros in patterns are expanded.
  They are patterns if the resulting expansions are patterns.

: Inaccessible patterns

  {deftech}[Inaccessible patterns] are patterns that are forced to have a particular value by later typing constraints.
  Any term may be used as an inaccessible term.
  Inaccessible terms are parenthesized, with a preceding period (`.`).

:::syntax term (title := "Inaccessible Patterns")
```grammar
.($e)
```
:::

:::example "Inaccessible Patterns"
A number's _parity_ is whether it's even or odd:
```lean
inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by omega
      eq ▸ .even (h + 1)
```

Because a value of type {lean}`Parity` contains half of a number (rounded down) as part of its representation of evenness or oddness, division by two can be implemented (in an unconventional manner) by finding a parity and then extracting the number.
```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
Because the index structure of {name}`Parity.even` and {name}`Parity.odd` force the number to have a certain form that is not otherwise a valid pattern, patterns that match on it must use inaccessible patterns for the number being divided.
:::

Patterns may additionally be named.
{deftech}[Named patterns] associate a name with a pattern; in subsequent patterns and on the right-hand side of the match alternative, the name refers to the part of the value that was matched by the given pattern.
Named patterns are written with an `@` between the name and the pattern.
Just like discriminants, named patterns may also be provided with names for equality assumptions.

:::syntax term (title := "Named Patterns")
```grammar
$x:ident@$e
```
```grammar
$x:ident@$h:ident:$e
```
:::


```lean -show -keep
-- Check claims about patterns

-- Literals
/-- error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]` -/
#guard_msgs in
def foo (x : String) : String :=
  match x with
  | "abc" => ""
  | r#"hey"# => ""
  | s!"a{x}y" => _
  | _ => default

structure Blah where
  n : Nat
deriving Inhabited

instance : OfNat Blah n where
  ofNat := ⟨n + 1⟩

def isFiveOh : Float → Bool
  | 5.0 => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval isFiveOh 5.0

/-- info: false -/
#guard_msgs in
#eval isFiveOh 0.5

def isZeroFloat : Float → Bool
  | 0.0 => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval isZeroFloat 0.0

/-- info: -0.000000 -/
#guard_msgs in
#eval (0.0 / -1.0)

/-- info: false -/
#guard_msgs in
#eval isZeroFloat (0.0 / -1.0)

/--
error: Missing cases:
(Blah.mk Nat.zero)
(Blah.mk (Nat.succ (Nat.succ _)))
-/
#check_msgs in
def abc (n : Blah) : Bool :=
  match n with
  | 0 => true

partial instance : OfNat Blah n where
  ofNat :=
    let rec f (x : Nat) : Blah :=
      match x with
      | 0 => f 99
      | n + 1 => f n
    f n

-- This shows that the partial instance was not unfolded
/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive (instOfNatBlah_1.f 0)
but is expected to have type
  motive n✝
-/
#check_msgs in
def defg (n : Blah) : Bool :=
  match n with
  | 0 => true

/--
info: @Neg.neg.{0} Float instNegFloat
  (@OfScientific.ofScientific.{0} Float instOfScientificFloat (nat_lit 320) Bool.true (nat_lit 1)) : Float
-/
#check_msgs in
set_option pp.all true in
#check -32.0

structure OnlyThreeOrFive where
  val : Nat
  val2 := false
  ok : val = 3 ∨ val = 5 := by rfl


-- Default args are not synthesized in patterns
/--
error: Fields missing: `val2`, `ok`
-/
#check_msgs in
def ggg : OnlyThreeOrFive → Nat
  | {val := n} => n

/--
error: Fields missing: `val2`
-/
#check_msgs in
def hhh : OnlyThreeOrFive → Nat
  | {val := n, ok := p} => n

-- Ellipses don't synth default args in patterns
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- Ellipses do synth default args via tactics, but not exprs, otherwise
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  3 = 3
is not definitionally equal to the right-hand side
  3 = 5

⊢ 3 = 3 ∨ 3 = 5
---
info: { val := 3, val2 := ?m.2647, ok := ⋯ } : OnlyThreeOrFive
-/
#check_msgs in
#check OnlyThreeOrFive.mk 3 ..

/-- info: { val := 3, val2 := ?_, ok := ⋯ } : OnlyThreeOrFive -/
#check_msgs in
set_option pp.mvars.anonymous false in
#check OnlyThreeOrFive.mk 3 (ok := .inl rfl) ..

/--
info: fun y =>
  match
    have this := ⟨y * 3, ⋯⟩;
    this with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), ⋯ => () : Nat → Unit
-/
#check_msgs in
#check fun (y : Nat) => match show {n : Nat// n = y * 3} from ⟨y*3, rfl⟩ with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), rfl => ()

```

## Types

Each discriminant must be well typed.
Because patterns are a subset of terms, their types can also be checked.
Each pattern that matches a given discriminant must have the same type as the corresponding discriminant.

The {tech}[right-hand side] of each match alternative should have the same type as the overall {keywordOf Lean.Parser.Term.match}`match` term.
To support dependent types, matching a discriminant against a pattern refines the types that are expected within the scope of the pattern.
In both subsequent patterns in the same match alternative and the right-hand side's type, occurrences of the discriminant are replaced by the pattern that it was matched against.


::::keepEnv
```lean -show
variable {α : Type u}
```

:::example "Type Refinement"
This {tech}[indexed family] describes mostly-balanced trees, with the depth encoded in the type.
```lean
inductive BalancedTree (α : Type u) : Nat → Type u where
  | empty : BalancedTree α 0
  | branch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 1)
  | lbranch
    (left : BalancedTree α (n + 1))
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 2)
  | rbranch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α (n + 1)) :
    BalancedTree α (n + 2)
```

To begin the implementation of a function to construct a perfectly balanced tree with some initial element and a given depth, a {tech}[hole] can be used for the definition.
```lean -keep (name := fill1) +error
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  _
```
The error message demonstrates that the tree should have the indicated depth.
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```

Matching on the expected depth and inserting holes results in an error message for each hole.
These messages demonstrate that the expected type has been refined, with `depth` replaced by the matched values.
```lean +error (name := fill2)
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
The first hole yields the following message:
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
The second hole yields the following message:
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```

Matching on the depth of a tree and the tree itself leads to a refinement of the tree's type according to the depth's pattern.
This means that certain combinations are not well-typed, such as {lean}`0` and {name BalancedTree.branch}`branch`, because refining the second discriminant's type yields {lean}`BalancedTree α 0` which does not match the constructor's type.
```lean (name := patfail) +error
def BalancedTree.isPerfectlyBalanced
    (n : Nat) (t : BalancedTree α n) : Bool :=
  match n, t with
  | 0, .empty => true
  | 0, .branch left val right =>
    isPerfectlyBalanced left &&
    isPerfectlyBalanced right
  | _, _ => false
```
```leanOutput patfail
Type mismatch
  left.branch val right
has type
  BalancedTree ?m.54 (?m.51 + 1)
but is expected to have type
  BalancedTree α 0
```
:::
::::

### Pattern Equality Proofs

When a discriminant is named, {keywordOf Lean.Parser.Term.match}`match` generates a proof that the pattern and discriminant are equal, binding it to the provided name in the {tech}[right-hand side].
This is useful to bridge the gap between dependent pattern matching on indexed families and APIs that expect explicit propositional arguments, and it can help tactics that make use of assumptions to succeed.

:::example "Pattern Equality Proofs"
The function {lean}`last?`, which either throws an exception or returns the last element of its argument, uses the standard library function {lean}`List.getLast`.
This function expects a proof that the list in question is nonempty.
Naming the match on `xs` ensures that there's an assumption in scope that states that `xs` is equal to `_ :: _`, which {tactic}`simp_all` uses to discharge the goal.
```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```

Without the name, {tactic}`simp_all` is unable to find the contradiction.
```lean +error (name := namedHyp)
def last?' (xs : List α) : Except String α :=
  match xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```leanOutput namedHyp
simp_all made no progress
```
:::

### Explicit Motives

Pattern matching is not a built-in primitive of Lean.
Instead, it is translated to applications of {tech}[recursors] via {tech}[auxiliary matching functions].
Both require a {tech}_motive_ that explains the relationship between the discriminant and the resulting type.
Generally, the {keywordOf Lean.Parser.Term.match}`match` elaborator is capable of synthesizing an appropriate motive, and the refinement of types that occurs during pattern matching is a result of the motive that was selected.
In some specialized circumstances, a different motive may be needed and may be provided explicitly using the `(motive := …)` syntax of {keywordOf Lean.Parser.Term.match}`match`.
This motive should be a function type that expects at least as many parameters as there are discriminants.
The type that results from applying a function with this type to the discriminants in order is the type of the entire {keywordOf Lean.Parser.Term.match}`match` term, and the type that results from applying a function with this type to all patterns in each alternative is the type of that alternative's {tech}[right-hand side].

:::example "Matching with an Explicit Motive"
An explicit motive can be used to provide type information that is otherwise unavailable from the surrounding context.
Attempting to match on a number and a proof that it is in fact {lean}`5` is an error, because there's no reason to connect the number to the proof:
```lean +error (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
Invalid match expression: This pattern contains metavariables:
  Eq.refl ?m.76
```
An explicit motive explains the relationship between the discriminants:
```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
:::

### Discriminant Refinement

When matching on an indexed family, the indices must also be discriminants.
Otherwise, the pattern would not be well typed: it is a type error if an index is just a variable but the type of a constructor requires a more specific value.
However, a process called {deftech}[discriminant refinement] automatically adds indices as additional discriminants.

::::keepEnv
:::example "Discriminant Refinement"
In the definition of {lean}`f`, the equality proof is the only discriminant.
However, equality is an indexed family, and the match is only valid when `n` is an additional discriminant.
```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
Using {keywordOf Lean.Parser.Command.print}`#print` demonstrates that the additional discriminant was added automatically.
```lean (name := fDef)
#print f
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
:::
::::

### Generalization
%%%
tag := "match-generalization"
%%%

The pattern match elaborator automatically determines the motive by finding occurrences of the discriminants in the expected type, generalizing them in the types of subsequent discriminants so that the appropriate pattern can be substituted.
Additionally, occurrences of the discriminants in the types of variables in the context are generalized and substituted by default.
This latter behavior can be turned off by passing the `(generalizing := false)` flag to {keywordOf Lean.Parser.Term.match}`match`.

:::::keepEnv
::::example "Matching, With and Without Generalization"
```lean -show
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
In this definition of {lean}`boolCases`, the assumption {lean}`b` is generalized in the type of `h` and then replaced with the actual pattern.
This means that {lean}`ifTrue` and {lean}`ifFalse` have the types {lean}`true = true → α` and {lean}`false = false → α` in their respective cases, but `h`'s type mentions the original discriminant.

```lean +error (name := boolCases1) -keep
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
The error for the first case is typical of both:
```leanOutput boolCases1
Application type mismatch: The argument
  h
has type
  b = true
but is expected to have type
  true = true
in the application
  ifTrue h
```
Turning off generalization allows type checking to succeed, because {lean}`b` remains in the types of {lean}`ifTrue` and {lean}`ifFalse`.
```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
In the generalized version, {name}`rfl` could have been used as the proof arguments as an alternative.
::::
:::::

## Custom Pattern Functions
%%%
tag := "match_pattern-functions"
%%%

```lean -show
section
variable {n : Nat}
```

In patterns, defined constants with the {attr}`match_pattern` attribute are unfolded and normalized rather than rejected.
This allows a more convenient syntax to be used for many patterns.
In the standard library, {name}`Nat.add`, {name}`HAdd.hAdd`, {name}`Add.add`, and {name}`Neg.neg` all have this attribute, which allows patterns like {lean}`n + 1` instead of {lean}`Nat.succ n`.
Similarly, {name}`Unit` and {name}`Unit.unit` are definitions that set the respective {tech}[universe parameters] of {name}`PUnit` and {name}`PUnit.unit` to 0; the {attr}`match_pattern` attribute on {name}`Unit.unit` allows it to be used in patterns, where it expands to {lean}`PUnit.unit.{0}`.

:::syntax attr (title := "Attribute for Match Patterns")
The {attr}`match_pattern` attribute indicates that a definition should be unfolded, rather than rejected, in a pattern.
```grammar
match_pattern
```
:::

::::keepEnv
```lean -show
section
variable {k : Nat}
```
:::example "Match Patterns Follow Reduction"
The following function can't be compiled:
```lean +error (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
The error message on the pattern `1 + _` is:
```leanOutput nonPat
Invalid pattern(s): `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 1 k)
```

This is because {name}`Nat.add` is defined by recursion on its second parameter, equivalently to:
```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

No {tech}[ι-reduction] is possible, because the value being matched is a variable, not a constructor.
{lean}`1 + k` gets stuck as {lean}`Nat.add 1 k`, which is not a valid pattern.

In the case of {lean}`k + 1`, that is, {lean}`Nat.add k (.succ .zero)`, the second pattern matches, so it reduces to {lean}`Nat.succ (Nat.add k .zero)`.
The second pattern now matches, yielding {lean}`Nat.succ k`, which is a valid pattern.
:::
```lean -show
end
```

::::


```lean -show
end
```


## Pattern Matching Functions
%%%
tag := "pattern-fun"
%%%

:::syntax term (title := "Pattern-Matching Functions")
Functions may be specified via pattern matching by writing a sequence of patterns after {keywordOf Lean.Parser.Term.fun}`fun`, each preceded by a vertical bar (`|`).
```grammar
fun
  $[| $pat,* => $term]*
```
This desugars to a function that immediately pattern-matches on its arguments.
:::

::::keepEnv
:::example "Pattern-Matching Functions"
{lean}`isZero` is defined using a pattern-matching function abstraction, while {lean}`isZero'` is defined using a pattern match expression:
```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
Because the former is syntactic sugar for the latter, they are definitionally equal:
```lean
example : isZero = isZero' := rfl
```
The desugaring is visible in the output of {keywordOf Lean.Parser.Command.print}`#print`:
```lean (name := isZero)
#print isZero
```
outputs
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
while
```lean (name := isZero')
#print isZero'
```
outputs
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
:::
::::

## Other Pattern Matching Operators

In addition to {keywordOf Lean.Parser.Term.match}`match` and {keywordOf termIfLet}`if let`, there are a few other operators that perform pattern matching.

:::syntax term (title := "The {keyword}`matches` Operator")
The {keywordOf Lean.«term_Matches_|»}`matches` operator returns {lean}`true` if the term on the left matches the pattern on the right.
```grammar
$e matches $e
```
:::

When branching on the result of {keywordOf Lean.«term_Matches_|»}`matches`, it's usually better to use {keywordOf termIfLet}`if let`, which can bind pattern variables in addition to checking whether a pattern matches.

```lean -show
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#check_msgs in
#check 4 matches (n + 1)
```

If there are no constructor patterns that could match a discriminant or sequence of discriminants, then the code in question is unreachable, as there must be a false assumption in the local context.
The {keywordOf Lean.Parser.Term.nomatch}`nomatch` expression is a match with zero cases that can have any type whatsoever, so long as there are no possible cases that could match the discriminants.

:::syntax term (title := "Caseless Pattern Matches")
```grammar
nomatch $e,*
```
:::

::::keepEnv
:::example "Inconsistent Indices"
There are no constructor patterns that can match both proofs in this example:
```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```

This is because they separately refine the value of `x` to unequal strings.
Thus, the {keywordOf Lean.Parser.Term.nomatch}`nomatch` operator allows the example's body to prove {lean}`False` (or any other proposition or type).
:::
::::

When the expected type is a function type, {keywordOf Lean.Parser.Term.nofun}`nofun` is shorthand for a function that takes as many parameters as the type indicates in which the body is {keywordOf Lean.Parser.Term.nomatch}`nomatch` applied to all of the parameters.
:::syntax term (title := "Caseless Functions")
```grammar
nofun
```
:::

::::keepEnv
:::example "Impossible Functions"
Instead of introducing arguments for both equality proofs and then using both in a {keywordOf Lean.Parser.Term.nomatch}`nomatch`, it is possible to use {keywordOf Lean.Parser.Term.nofun}`nofun`.
```lean
example : x = "Hello" → x = "world" → False := nofun
```
:::
::::

## Elaborating Pattern Matching
%%%
tag := "pattern-match-elaboration"
draft := true
%%%

:::planned 209
Specify the elaboration of pattern matching to {deftech}[auxiliary match functions].
:::

# Holes

A {deftech}_hole_ or {deftech}_placeholder term_ is a term that indicates the absence of instructions to the elaborator.{index}[placeholder term]{index (subterm := "placeholder")}[term]
In terms, holes can be automatically filled when the surrounding context would only allow one type-correct term to be written where the hole is.
Otherwise, a hole is an error.
In patterns, holes represent universal patterns that can match anything.


:::syntax term (title := "Holes")
Holes are written with underscores.
```grammar
_
```
:::

::::keepEnv
:::example "Filling Holes with Unification"
The function {lean}`the` can be used similarly to {keywordOf Lean.Parser.Term.show}`show` or a {tech}[type ascription].
```lean
def the (α : Sort u) (x : α) : α := x
```
If the second parameter's type can be inferred, then the first parameter can be a hole.
Both of these commands are equivalent:
```lean
#check the String "Hello!"

#check the _ "Hello"
```
:::
::::


When writing proofs, it can be convenient to explicitly introduce unknown values.
This is done via {deftech}_synthetic holes_, which are never solved by unification and may occur in multiple positions.
They are primarily useful in tactic proofs, and are described in {ref "metavariables-in-proofs"}[the section on metavariables in proofs].

:::syntax term (title := "Synthetic Holes")
```grammar
?$x:ident
```
```grammar
?_
```
:::

# Type Ascription

{deftech}_Type ascriptions_ explicitly annotate terms with their types.
They are a way to provide Lean with the expected type for a term.
This type must be definitionally equal to the type that is expected based on the term's context.
Type ascriptions are useful for more than just documenting a program:
 * There may not be sufficient information in the program text to derive a type for a term. Ascriptions are one way to provide the type.
 * An inferred type may not be the one that was desired for a term.
 * The expected type of a term is used to drive the insertion of {tech}[coercions], and ascriptions are one way to control where coercions are inserted.

:::syntax term (title := "Postfix Type Ascriptions")
Type ascriptions must be surrounded by parentheses.
They indicate that the first term's type is the second term.
```grammar
($_ : $_)
```
:::


In cases where the term that requires a type ascription is long, such as a tactic proof or a {keywordOf Lean.Parser.Term.do}`do` block, the postfix type ascription with its mandatory parentheses can be difficult to read.
Additionally, for both proofs and {keywordOf Lean.Parser.Term.do}`do` blocks, the term's type is essential to its interpretation.
In these cases, the prefix versions can be easier to read.
:::syntax term (title := "Prefix Type Ascriptions")
```grammar
show $_ from $_
```
When the term in the body of {keywordOf Lean.Parser.Term.show}`show` is a tactic proof, the keyword {keywordOf Lean.Parser.Term.show}`from` may be omitted.
```grammar
show $_ by $_
```
:::

:::example "Ascribing Statements to Proofs"
This example is unable to execute the tactic proof because the desired proposition is not known.
As part of running the earlier tactics, the proposition is automatically refined to be one that the tactics could prove.
However, their default cases fill it out incorrectly, leading to a proof that fails.
```lean (name := byBusted) +error
example (n : Nat) := by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```leanOutput byBusted
Invalid rewrite argument: Expected an equality or iff proof or definition name, but `ih` is a proof of
  0 ≍ n'
```

A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show` can be used to provide the proposition being proved.
This can be useful in syntactic contexts where adding it as a local definition would be inconvenient.
```lean
example (n : Nat) := show 0 + n = n by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
:::

:::example "Ascribing Types to {keywordOf Lean.Parser.Term.do}`do` Blocks"
This example lacks sufficient type information to synthesize the {name}`Pure` instance.
```lean (name := doBusted) +error
example := do
  return 5
```
```leanOutput doBusted
typeclass instance problem is stuck
  Pure ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show`, together with a {tech}[hole], can be used to indicate the monad.
The {tech (key := "default instance")}[default] {lean}`OfNat _ 5` instance provides enough type information to fill the hole with {lean}`Nat`.
```lean
example := show StateM String _ from do
  return 5
```
:::

There is an important difference between postfix type ascriptions and {keywordOf Lean.Parser.Term.show}`show`.
Ordinary postfix type ascriptions change the type that is expected for the term, which can change the way that the term elaborates.
After elaboration, however, Lean infers the type of the resulting term and uses that inferred type for further elaboration tasks.
On the other hand, {keywordOf Lean.Parser.Term.show}`show` elaborates to a term whose inferred type is the ascribed type.
The difference can be observed when using {tech}[generalized field notation], where the ascribed type is only guaranteed to be used to resolve fields when using {keywordOf Lean.Parser.Term.show}`show`.

::::example "Postfix Ascription vs `show`"

:::paragraph
This definition establishes an alternative name for {lean}`List String`:
```lean
def Colors := List String
```
:::

:::paragraph
A postfix type ascription provides the type information that's needed to determine the implicit argument {name}`String` to {name}`List.nil`, but the resulting type is still {lean}`List String`:
```lean (name := nil)
#check ([] : Colors)
```
```leanOutput nil
[] : List String
```
:::

:::paragraph
When using {keywordOf Lean.Parser.Term.show}`show`, on the other hand, the elaborated term is constructed in such a way that the inferred type is {lean}`Colors`:
```lean (name := nil2)
#check (show Colors from [])
```
```leanOutput nil2
have this := [];
this : Colors
```
:::

:::paragraph
This function is designed to be invoked using {tech}[generalized field notation]:
```lean
def Colors.hasYellow (cs : Colors) : Bool :=
  cs.any (·.toLower == "yellow")
```
:::

:::paragraph
Due to the differences in their inferred types, it can be used with {keywordOf Lean.Parser.Term.show}`show`, but not with the postfix type ascription:
```lean (name := nil3) +error
#eval ([] : Colors).hasYellow
```
```leanOutput nil3
Invalid field `hasYellow`: The environment does not contain `List.hasYellow`, so it is not possible to project the field `hasYellow` from an expression
  []
of type `List String`
```
```lean (name := nil4)
#eval (show Colors from []).hasYellow
```
```leanOutput nil4
false
```
:::
::::


# Quotation and Antiquotation

Quotation terms are described in the {ref "quotation"}[section on quotation].

# `do`-Notation

{keywordOf Lean.Parser.Term.do}`do`-notation is described {ref "do-notation"}[in the chapter on monads.]

# Proofs

The syntax for invoking tactics ({keywordOf Lean.Parser.Term.byTactic}`by`) is described in {ref "by"}[the section on proofs].
