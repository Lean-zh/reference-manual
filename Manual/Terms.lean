/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Terms

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
:::example "局部名称优先" (file := "Local Names Take Precedence")
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
:::example "当前命名空间的较长前缀优先" (file := "Longer Prefixes of Current Namespace Take Precedence")
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
:::example "较长的标识符前缀优先" (file := "Longer Identifier Prefixes Take Precedence")
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
:::example "当前命名空间的内容优先于已打开的命名空间" (file := "Current Namespace Contents Take Precedence Over Opened Namespaces")
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


:::example "有歧义的标识符" (file := "Ambiguous Identifiers")
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


:::example "通过类型消歧" (file := "Disambiguation via Typing")
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
file := "Leading `.`"
%%%

当标识符以点（`.`）开头时，会使用精译器对表达式的预期类型来解析它，而不是使用当前命名空间和已打开命名空间的集合。
{tech (key := "Generalized field notation")}[广义字段表示法]与此相关：这种{deftech (key := "leading dot notation")}_前导点表示法_使用标识符的预期类型将其解析为名称，而字段表示法使用紧邻点之前的项的推断类型。

带前导 `.` 的标识符会在{deftech (key := "expected type's namespace")}_预期类型的命名空间_中查找。
若项的预期类型是应用于零个或多个实参的常量，则其命名空间就是该常量的名称。
若该类型不是常量的应用（例如函数、元变量或宇宙），则它没有命名空间。

若在预期类型的命名空间中找不到该名称，但展开这个常量能得到另一常量，则转而查找后者的命名空间。
重复此过程，直到遇到并非常量应用的内容，或常量无法继续展开为止。

::::keepEnv
:::example "前导 `.`" (file := "Leading `.`")
{name List.replicate}`.replicate` 的预期类型是 `List Unit`。
该类型的命名空间是 `List`，因此 {name List.replicate}`.replicate` 解析为 {name List.replicate}`List.replicate`。
```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::

:::example "前导 `.` 与展开定义" (file := "Leading `.` and Unfolding Definitions")
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

:::example "多个同类型参数" (file := "Multiple Parameters, Same Type")
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
file := "Implicit Parameters"
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
:::example "普通隐式参数与严格隐式参数" (file := "Ordinary vs Strict Implicit Parameters")
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

:::example "来自类型的隐式参数" (file := "Implicit Parameters from Types")
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
:::example "具名实参" (file := "Named Arguments")
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

{zhdocstring optParam ZhDoc.Terms.optParam}

{zhdocstring autoParam ZhDoc.Terms.autoParam}

## 广义字段表示法
%%%
tag := "generalized-field-notation"
file := "Generalized Field Notation"
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

:::example "广义字段表示法" (file := "Generalized Field Notation")
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

{zhOptionDocs pp.fieldNotation ZhDoc.Terms.Option.pp.fieldNotation}

:::syntax attr (title := "控制字段表示法")
{attr}`pp_nodot` 属性使 Lean 的美化打印器在打印函数时不使用字段表示法。
```grammar
pp_nodot
```
:::

::::keepEnv
:::example "关闭字段表示法" (file := "Turning Off Field Notation")
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
file := "Pipeline Syntax"
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

:::example "右管道表示法" (file := "Right pipeline notation")
右管道可以在一个项上依次调用一系列函数。
对读者而言，它往往更强调正在变换的数据。
```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
:::

:::example "左管道表示法" (file := "Left pipeline notation")
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


:::example "管道字段" (file := "Pipeline Fields")

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
file := "Natural Numbers"
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

{zhdocstring OfNat ZhDoc.Terms.OfNat}

```lean -show
end
```

:::example "自定义自然数字面量" (file := "Custom Natural Number Literals")
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
file := "Scientific Numbers"
%%%

科学计数字面量由一个十进制数字序列、一个可选的小数部分（句点后跟零个或多个十进制数字）和一个可选的指数部分（字母 `e` 后跟可选的 `+` 或 `-`，再跟一个或多个十进制数字）组成，各部分之间不能有空白。
科学计数字面量通过 {name}`OfScientific` 类型类重载。

{zhdocstring OfScientific ZhDoc.Terms.OfScientific}

存在用于 {name}`Float` 和 {name}`Float32` 的 {lean}`OfScientific` 实例，但不存在单独的浮点字面量。

## 字符串
%%%
tag := "The-Lean-Language-Reference--Terms--Numeric-Literals--Strings"
file := "Strings"
%%%

字符串字面量在{ref "string-syntax"}[关于字符串的章节]中介绍。

## 列表与数组
%%%
tag := "The-Lean-Language-Reference--Terms--Numeric-Literals--Lists-and-Arrays"
file := "Lists and Arrays"
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

:::example "长列表字面量" (file := "Long List Literals")
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
:::example "检查数组边界" (file := "Checking Array Bounds")

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


# 模式匹配
%%%
tag := "pattern-matching"
file := "Pattern-Matching"
%%%


{deftech (key := "Pattern matching")}_模式匹配_是一种使用{deftech (key := "patterns")}_模式_语法识别值并解构值的方法；模式是项的一个子集。
用于识别并解构值的模式，其语法类似于构造该值时所使用的语法。
一个或多个{deftech (key := "match discriminants")}_匹配判别式_会同时与一系列{deftech (key := "match alternatives")}_匹配分支_进行比较。
判别式可以命名。
每个分支都包含一个或多个以逗号分隔的模式序列；所有模式序列所含的模式数都必须与判别式的数量相同。
当一个模式序列匹配全部判别式时，就在扩展后的环境中求值对应 {keywordOf Lean.Parser.Term.match}`=>` 之后的项；该环境包含每个{tech (key := "pattern variable")}[模式变量]的值，以及每个具名判别式的一个相等性假设。
这个项称为匹配分支的{deftech (key := "right-hand side")}_右侧_。

:::syntax term (title := "模式匹配")
```grammar
match
    $[(generalizing := $e)]?
    $[(motive := $e)]?
    $[$d:matchDiscr],*
  with
$[| $[$e,*]|* => $e]*
```
:::

:::syntax matchDiscr (title := "匹配判别式") -open
```grammar
$e:term
```
```grammar
$h:ident : $e:term
```
:::

模式匹配表达式也可以使用{tech (key := "quasiquotations")}[准引用]作为模式：它匹配对应的 {name}`Lean.Syntax` 值，并将{tech (key := "antiquotations")}[反引用]的内容视为普通模式。
引用模式的编译方式不同于其他模式，因此如果一个 {keywordOf Lean.Parser.Term.match}`match` 中有一个模式是语法，那么所有模式都必须是语法。
引用模式见{ref "quote-patterns"}[引用一节]。

模式是项的一个子集。
模式由以下形式组成：

: 全匹配模式

  空洞语法 {lean}`_` 是一种匹配任意值且不绑定任何模式变量的模式。
  全匹配模式并不完全等价于未使用的模式变量。
  在模式的类型检查原本会要求更具体的{tech (key := "inaccessible pattern")}[不可访问模式]的位置，可以使用全匹配模式，而变量不能用于这些位置。

: 标识符

  如果一个标识符未在当前作用域中绑定，也没有应用于实参，那么它表示一个模式变量。
  {deftech (key := "Pattern variables")}_模式变量_匹配任意值；如此匹配到的值会绑定到模式变量，并加入求值{tech (key := "right-hand side")}[右侧]时所使用的局部环境。
  如果标识符已绑定，那么当它绑定到某个{tech (key := "inductive type")}[归纳类型]的{tech (key := "constructor")}[构造器]，或其定义带有 {attr}`match_pattern` 属性时，它可以作为模式。

: 应用

  如果函数应用中的函数是绑定到构造器或带有 {attr}`match_pattern` 属性的标识符，并且所有实参也都是模式，那么该函数应用就是模式。
  如果该标识符是构造器，那么当实参模式与构造器的实参匹配时，此模式便匹配由该构造器构造的值。
  如果它是带有 {attr}`match_pattern` 属性的函数，则展开该函数应用，并将所得项的{tech (key := "normal form")}[范式]用作模式。
  默认实参会照常插入，并将其范式用作模式。
  不过，{tech (key := "ellipsis")}[省略号]会使后续所有实参都被视为全匹配模式，即便这些实参带有相关的默认值或策略。

: 字面量

  {ref "char-syntax"}[字符字面量]和{ref "string-syntax"}[字符串字面量]是匹配相应字符或字符串的模式。
  {ref "raw-string-literals"}[原始字符串字面量]可以用作模式，但{ref "string-interpolation"}[插值字符串]不可以。
  模式中的{ref "nat-syntax"}[自然数字面量]通过合成相应的 {name}`OfNat` 实例来解释，并将所得项归约为{tech (key := "normal form")}[范式]；该范式必须是模式。
  类似地，{tech (key := "scientific literals")}[科学记数法字面量]通过相应的 {name}`OfScientific` 实例解释。

: 结构体实例

  {tech (key := "Structure instances")}[结构体实例]可以用作模式。
  它们会被解释为相应的结构体构造器。

: 引用名称

  {lean}`` `x `` 和 {lean}``` ``none ``` 等引用名称会匹配相应的 {name}`Lean.Name` 值。

: 宏

  模式中的宏会被展开。
  如果展开结果是模式，那么这些宏就是模式。

: 不可访问模式

  {deftech (key := "Inaccessible patterns")}[不可访问模式]是因后续类型约束而被迫具有特定值的模式。
  任何项都可以用作不可访问项。
  不可访问项写在圆括号中，并以句点（`.`）开头。

:::syntax term (title := "不可访问模式")
```grammar
.($e)
```
:::

:::example "不可访问模式" (file := "Inaccessible Patterns")
一个数的_奇偶性_指它是偶数还是奇数：
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

由于 {lean}`Parity` 类型的值在表示奇偶性时包含该数的一半（向下取整），因此可以先求奇偶性再提取其中的数，以一种非常规方式实现除以二。
```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
由于 {name}`Parity.even` 和 {name}`Parity.odd` 的索引结构迫使该数具有某种原本不是合法模式的特定形式，因此匹配它的模式必须对被除数使用不可访问模式。
:::

模式还可以命名。
{deftech (key := "Named patterns")}[具名模式]把名称与模式关联起来；在后续模式和匹配分支的右侧中，该名称指代由给定模式匹配到的那部分值。
具名模式在名称与模式之间写一个 `@`。
与判别式一样，也可以为具名模式的相等性假设提供名称。

:::syntax term (title := "具名模式")
```grammar
$x:ident@$e
```
```grammar
$x:ident@$h:ident:$e
```
:::


```lean -show -keep
-- 检查关于模式的论断

-- 字面量
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

-- 这表明偏函数实例没有被展开
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


-- 模式中不会合成默认实参
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

-- 模式中的省略号不会合成默认实参
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- 省略号会通过策略合成默认实参，但不会以其他方式合成表达式默认实参
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

## 类型
%%%
tag := "The-Lean-Language-Reference--Terms--Pattern-Matching--Types"
file := "Types"
%%%

每个判别式都必须类型正确。
因为模式是项的一个子集，所以也可以检查它们的类型。
匹配某个判别式的每个模式，都必须与相应的判别式具有相同类型。

每个匹配分支的{tech (key := "right-hand side")}[右侧]都应与整个 {keywordOf Lean.Parser.Term.match}`match` 项具有相同类型。
为支持依赖类型，将判别式与模式匹配会精化模式作用域内的预期类型。
在同一匹配分支的后续模式以及右侧的类型中，出现的判别式都会替换为与之匹配的模式。


::::keepEnv
```lean -show
variable {α : Type u}
```

:::example "类型精化" (file := "Type Refinement")
这个{tech (key := "indexed family")}[索引族]描述近乎平衡的树，并将深度编码在类型中。
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

为了开始实现一个函数，用给定的初始元素构造指定深度的完全平衡树，可以在定义中使用{tech (key := "hole")}[空洞]。
```lean -keep (name := fill1) +error
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  _
```
错误消息表明树应具有指定的深度。
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```

对预期深度进行匹配并插入空洞，会为每个空洞产生一条错误消息。
这些消息表明预期类型已经精化，其中 `depth` 被匹配到的值替换。
```lean +error (name := fill2)
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
第一个空洞产生以下消息：
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
第二个空洞产生以下消息：
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```

同时匹配树的深度和树本身，会根据深度模式精化树的类型。
这意味着某些组合不是良类型的，例如 {lean}`0` 与 {name BalancedTree.branch}`branch`，因为精化第二个判别式的类型会得到 {lean}`BalancedTree α 0`，它与构造器的类型不匹配。
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

### 模式相等性证明
%%%
tag := "The-Lean-Language-Reference--Terms--Pattern-Matching--Types--Pattern-Equality-Proofs"
file := "Pattern Equality Proofs"
%%%

当判别式具名时，{keywordOf Lean.Parser.Term.match}`match` 会生成模式与判别式相等的证明，并在{tech (key := "right-hand side")}[右侧]中把它绑定到所提供的名称。
这有助于衔接对索引族的依赖模式匹配与要求显式命题实参的 API，也能帮助利用假设的策略成功执行。

:::example "模式相等性证明" (file := "Pattern Equality Proofs")
函数 {lean}`last?` 要么抛出异常，要么返回其实参的最后一个元素；它使用标准库函数 {lean}`List.getLast`。
该函数要求提供相关列表非空的证明。
为对 `xs` 的匹配命名，可确保作用域中存在一个断言 `xs` 等于 `_ :: _` 的假设，{tactic}`simp_all` 会用它完成目标。
```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```

如果没有该名称，{tactic}`simp_all` 就无法找到矛盾。
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

### 显式动机
%%%
tag := "The-Lean-Language-Reference--Terms--Pattern-Matching--Types--Explicit-Motives"
file := "Explicit Motives"
%%%

模式匹配并不是 Lean 的内建原语。
相反，它通过{tech (key := "auxiliary matching functions")}[辅助匹配函数]翻译成对{tech (key := "recursors")}[递归器]的应用。
二者都需要一个{tech (key := "motive")}_动机_来说明判别式与结果类型之间的关系。
通常，{keywordOf Lean.Parser.Term.match}`match` 精译器能够合成适当的动机，而模式匹配过程中发生的类型精化正是所选动机的结果。
在某些特殊情况下，可能需要不同的动机；可以使用 {keywordOf Lean.Parser.Term.match}`match` 的 `(motive := …)` 语法显式提供它。
该动机应当是函数类型，并且至少接受与判别式数量相同的参数。
依次将这种类型的函数应用于各判别式所得的类型，就是整个 {keywordOf Lean.Parser.Term.match}`match` 项的类型；将它应用于每个分支中的所有模式所得的类型，则是该分支{tech (key := "right-hand side")}[右侧]的类型。

:::example "使用显式动机进行匹配" (file := "Matching with an Explicit Motive")
显式动机可以提供周围上下文原本无法给出的类型信息。
试图同时匹配一个数以及它确实为 {lean}`5` 的证明会产生错误，因为没有理由把这个数与该证明联系起来：
```lean +error (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
Invalid match expression: This pattern contains metavariables:
  Eq.refl ?m.76
```
显式动机说明了各判别式之间的关系：
```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
:::

### 判别式精化
%%%
tag := "The-Lean-Language-Reference--Terms--Pattern-Matching--Types--Discriminant-Refinement"
file := "Discriminant Refinement"
%%%

匹配索引族时，其索引也必须作为判别式。
否则模式将不是良类型的：如果某个索引只是变量，而构造器的类型要求更具体的值，就会产生类型错误。
不过，称为{deftech (key := "discriminant refinement")}[判别式精化]的过程会自动把索引添加为额外的判别式。

::::keepEnv
:::example "判别式精化" (file := "Discriminant Refinement")
在 {lean}`f` 的定义中，相等性证明是唯一的判别式。
然而，相等性是索引族，只有将 `n` 作为额外的判别式时，该匹配才有效。
```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
使用 {keywordOf Lean.Parser.Command.print}`#print` 可以看出额外的判别式已自动添加。
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

### 泛化
%%%
tag := "match-generalization"
file := "Generalization"
%%%

模式匹配精译器通过在预期类型中查找判别式的出现位置，自动确定动机；它在后续判别式的类型中泛化这些出现位置，以便代入相应的模式。
此外，默认情况下，上下文中变量类型里出现的判别式也会被泛化并替换。
向 {keywordOf Lean.Parser.Term.match}`match` 传入 `(generalizing := false)` 标志可以关闭后一行为。

:::::keepEnv
::::example "启用与禁用泛化的匹配" (file := "Matching, With and Without Generalization")
```lean -show
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
在 {lean}`boolCases` 的这个定义中，假设 {lean}`b` 在 `h` 的类型中被泛化，随后替换为实际模式。
这意味着在各自的分支中，{lean}`ifTrue` 和 {lean}`ifFalse` 的类型分别为 {lean}`true = true → α` 和 {lean}`false = false → α`，但 `h` 的类型提到了原判别式。

```lean +error (name := boolCases1) -keep
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
第一个分支的错误是二者共有的典型错误：
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
关闭泛化后，类型检查能够成功，因为 {lean}`b` 会保留在 {lean}`ifTrue` 和 {lean}`ifFalse` 的类型中。
```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
在泛化版本中，也可以改用 {name}`rfl` 作为证明实参。
::::
:::::

## 自定义模式函数
%%%
tag := "match_pattern-functions"
file := "Custom Pattern Functions"
%%%

```lean -show
section
variable {n : Nat}
```

在模式中，带有 {attr}`match_pattern` 属性的已定义常量会被展开并规范化，而不是被拒绝。
这使许多模式可以使用更方便的语法。
标准库中的 {name}`Nat.add`、{name}`HAdd.hAdd`、{name}`Add.add` 和 {name}`Neg.neg` 都带有此属性，因此可以使用 {lean}`n + 1` 这样的模式，而不必写 {lean}`Nat.succ n`。
类似地，{name}`Unit` 和 {name}`Unit.unit` 是把 {name}`PUnit` 和 {name}`PUnit.unit` 各自的{tech (key := "universe parameters")}[宇宙参数]设为 0 的定义；{name}`Unit.unit` 上的 {attr}`match_pattern` 属性使其可用于模式，并在其中展开为 {lean}`PUnit.unit.{0}`。

:::syntax attr (title := "匹配模式属性")
{attr}`match_pattern` 属性表示某个定义在模式中应被展开，而不是被拒绝。
```grammar
match_pattern
```
:::

::::keepEnv
```lean -show
section
variable {k : Nat}
```
:::example "匹配模式遵循归约" (file := "Match Patterns Follow Reduction")
以下函数无法编译：
```lean +error (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
模式 `1 + _` 上的错误消息是：
```leanOutput nonPat
Invalid pattern(s): `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 1 k)
```

这是因为 {name}`Nat.add` 通过对第二个参数递归来定义，等价于：
```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

由于被匹配的值是变量而不是构造器，无法进行{tech (key := "ι-reduction")}[ι-归约]。
{lean}`1 + k` 停滞为 {lean}`Nat.add 1 k`，而后者不是合法模式。

对于 {lean}`k + 1`，即 {lean}`Nat.add k (.succ .zero)`，第二个模式匹配，因此它归约为 {lean}`Nat.succ (Nat.add k .zero)`。
此时第二个模式再次匹配，得到 {lean}`Nat.succ k`，这是一个合法模式。
:::
```lean -show
end
```

::::


```lean -show
end
```


## 模式匹配函数
%%%
tag := "pattern-fun"
file := "Pattern Matching Functions"
%%%

:::syntax term (title := "模式匹配函数")
可以通过模式匹配指定函数：在 {keywordOf Lean.Parser.Term.fun}`fun` 之后写一系列模式，每个模式前都加竖线（`|`）。
```grammar
fun
  $[| $pat,* => $term]*
```
它会脱糖为一个立即对其实参进行模式匹配的函数。
:::

::::keepEnv
:::example "模式匹配函数" (file := "Pattern-Matching Functions")
{lean}`isZero` 使用模式匹配函数抽象定义，而 {lean}`isZero'` 使用模式匹配表达式定义：
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
由于前者是后者的语法糖，两者在定义上相等：
```lean
example : isZero = isZero' := rfl
```
{keywordOf Lean.Parser.Command.print}`#print` 的输出可显示脱糖结果：
```lean (name := isZero)
#print isZero
```
输出
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
而
```lean (name := isZero')
#print isZero'
```
输出
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
:::
::::

## 其他模式匹配运算符
%%%
tag := "The-Lean-Language-Reference--Terms--Pattern-Matching--Other-Pattern-Matching-Operators"
file := "Other Pattern Matching Operators"
%%%

除 {keywordOf Lean.Parser.Term.match}`match` 和 {keywordOf termIfLet}`if let` 外，还有一些其他运算符会执行模式匹配。

:::syntax term (title := "{keyword}`matches` 运算符")
如果左侧的项与右侧的模式匹配，{keywordOf Lean.«term_Matches_|»}`matches` 运算符就返回 {lean}`true`。
```grammar
$e matches $e
```
:::

根据 {keywordOf Lean.«term_Matches_|»}`matches` 的结果进行分支时，通常最好使用 {keywordOf termIfLet}`if let`；它除了检查模式是否匹配外，还能绑定模式变量。

```lean -show
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#check_msgs in
#check 4 matches (n + 1)
```

如果没有任何构造器模式能够匹配一个判别式或一组判别式，那么相关代码不可达，因为局部上下文中必然存在一个错误假设。
{keywordOf Lean.Parser.Term.nomatch}`nomatch` 表达式是一个没有任何分支的匹配；只要不存在可能匹配判别式的分支，它就可以具有任意类型。

:::syntax term (title := "无分支模式匹配")
```grammar
nomatch $e,*
```
:::

::::keepEnv
:::example "不一致的索引" (file := "Inconsistent Indices")
本例中没有任何构造器模式能同时匹配这两个证明：
```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```

这是因为它们分别把 `x` 的值精化为两个不相等的字符串。
因此，{keywordOf Lean.Parser.Term.nomatch}`nomatch` 运算符使示例主体能够证明 {lean}`False`（或任意其他命题或类型）。
:::
::::

当预期类型是函数类型时，{keywordOf Lean.Parser.Term.nofun}`nofun` 是一种简写：它构造一个接受类型所指定数量参数的函数，并以应用于全部参数的 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 作为函数体。
:::syntax term (title := "无分支函数")
```grammar
nofun
```
:::

::::keepEnv
:::example "不可能的函数" (file := "Impossible Functions")
可以使用 {keywordOf Lean.Parser.Term.nofun}`nofun`，而不必为两个相等性证明都引入实参，再在 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 中使用二者。
```lean
example : x = "Hello" → x = "world" → False := nofun
```
:::
::::

## 精译模式匹配
%%%
tag := "pattern-match-elaboration"
draft := true
file := "Elaborating Pattern Matching"
%%%

:::planned 209
规定如何把模式匹配精译为{deftech (key := "auxiliary match functions")}[辅助匹配函数]。
:::

# 空洞
%%%
tag := "holes"
file := "Holes"
%%%

{deftech (key := "hole")}_空洞_或{deftech (key := "placeholder term")}_占位项_是一种表示没有向精译器提供指令的项。{index}[占位项]{index (subterm := "占位符")}[项]
在项中，如果周围上下文只允许在空洞处写下一个类型正确的项，空洞就可以自动填充。
否则，空洞会导致错误。
在模式中，空洞表示可以匹配任何值的全匹配模式。


:::syntax term (title := "空洞")
空洞用下划线书写。
```grammar
_
```
:::

::::keepEnv
:::example "通过合一填充空洞" (file := "Filling Holes with Unification")
函数 {lean}`the` 的用法类似于 {keywordOf Lean.Parser.Term.show}`show` 或{tech (key := "type ascription")}[类型标注]。
```lean
def the (α : Sort u) (x : α) : α := x
```
如果可以推断第二个参数的类型，那么第一个参数可以是空洞。
以下两个命令等价：
```lean
#check the String "Hello!"

#check the _ "Hello"
```
:::
::::


编写证明时，显式引入未知值可能很方便。
这通过{deftech (key := "synthetic holes")}_合成空洞_实现；合成空洞永远不会通过合一求解，并且可以出现在多个位置。
它们主要用于策略证明，详见{ref "metavariables-in-proofs"}[证明中的元变量一节]。

:::syntax term (title := "合成空洞")
```grammar
?$x:ident
```
```grammar
?_
```
:::

# 类型标注
%%%
tag := "type-ascription"
file := "Type-Ascription"
%%%

{deftech (key := "Type ascriptions")}_类型标注_显式地以类型标注项。
它们是向 Lean 提供项的预期类型的一种方式。
该类型必须与根据项的上下文所预期的类型定义相等。
类型标注不仅能用于记录程序，还可用于：
 * 程序文本中可能没有足够的信息来推导某项的类型。标注是提供该类型的一种方式。
 * 推断出的类型可能不是该项所需的类型。
 * 项的预期类型用于驱动{tech (key := "coercions")}[强制转换]的插入，而标注是控制强制转换插入位置的一种方式。

:::syntax term (title := "后缀类型标注")
类型标注必须由圆括号包围。
它们表示第一个项的类型是第二个项。
```grammar
($_ : $_)
```
:::


如果需要类型标注的项很长，例如策略证明或 {keywordOf Lean.Parser.Term.do}`do` 块，那么带有强制圆括号的后缀类型标注可能难以阅读。
此外，无论是证明还是 {keywordOf Lean.Parser.Term.do}`do` 块，项的类型对其解释都至关重要。
在这些情况下，前缀形式可能更易阅读。
:::syntax term (title := "前缀类型标注")
```grammar
show $_ from $_
```
当 {keywordOf Lean.Parser.Term.show}`show` 主体中的项是策略证明时，可以省略关键字 {keywordOf Lean.Parser.Term.show}`from`。
```grammar
show $_ by $_
```
:::

:::example "为证明标注命题" (file := "Ascribing Statements to Proofs")
此示例无法执行策略证明，因为所需的命题未知。
在运行前面的策略时，该命题会自动精化为策略能够证明的命题。
然而，它们的默认分支错误地补全了该命题，导致证明失败。
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

可以使用带 {keywordOf Lean.Parser.Term.show}`show` 的前缀类型标注来提供待证明的命题。
在不方便把它添加为局部定义的语法上下文中，这很有用。
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

:::example "为 {keywordOf Lean.Parser.Term.do}`do` 块标注类型" (file := "Ascribing Types to {keywordOf Lean.Parser.Term.do}`do` Blocks")
此示例缺少足够的类型信息来合成 {name}`Pure` 实例。
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

带 {keywordOf Lean.Parser.Term.show}`show` 的前缀类型标注与{tech (key := "hole")}[空洞]结合，可以用来指出单子。
{tech (key := "default instance")}[默认]的 {lean}`OfNat _ 5` 实例提供了足够的类型信息，可用 {lean}`Nat` 填充空洞。
```lean
example := show StateM String _ from do
  return 5
```
:::

后缀类型标注与 {keywordOf Lean.Parser.Term.show}`show` 之间有一项重要区别。
普通后缀类型标注会改变项的预期类型，从而可能改变项的精译方式。
然而，精译之后，Lean 会推断所得项的类型，并将该推断类型用于后续精译任务。
另一方面，{keywordOf Lean.Parser.Term.show}`show` 会精译为一个推断类型就是所标注类型的项。
使用{tech (key := "generalized field notation")}[广义字段表示法]时可以观察到这一区别：只有使用 {keywordOf Lean.Parser.Term.show}`show`，才能保证以所标注类型解析字段。

::::example "后缀标注与 `show`" (file := "Postfix Ascription vs `show`")

:::paragraph
此定义为 {lean}`List String` 建立了一个别名：
```lean
def Colors := List String
```
:::

:::paragraph
后缀类型标注提供了确定 {name}`List.nil` 的隐式实参 {name}`String` 所需的类型信息，但所得类型仍然是 {lean}`List String`：
```lean (name := nil)
#check ([] : Colors)
```
```leanOutput nil
[] : List String
```
:::

:::paragraph
另一方面，使用 {keywordOf Lean.Parser.Term.show}`show` 时，精译后的项会以一种使其推断类型为 {lean}`Colors` 的方式构造：
```lean (name := nil2)
#check (show Colors from [])
```
```leanOutput nil2
have this := [];
this : Colors
```
:::

:::paragraph
此函数设计为通过{tech (key := "generalized field notation")}[广义字段表示法]调用：
```lean
def Colors.hasYellow (cs : Colors) : Bool :=
  cs.any (·.toLower == "yellow")
```
:::

:::paragraph
由于推断类型不同，它可以与 {keywordOf Lean.Parser.Term.show}`show` 一起使用，却不能与后缀类型标注一起使用：
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


# 引用与反引用
%%%
tag := "quotation-and-antiquotation"
file := "Quotation-and-Antiquotation"
%%%

引用项见{ref "quotation"}[引用一节]。

# `do` 表示法
%%%
tag := "do-notation-terms"
file := "do--Notation"
%%%

{keywordOf Lean.Parser.Term.do}`do` 表示法见{ref "do-notation"}[单子一章]。

# 证明
%%%
tag := "proof-terms"
file := "Proofs"
%%%

调用策略的语法（{keywordOf Lean.Parser.Term.byTactic}`by`）见{ref "by"}[证明一节]。
