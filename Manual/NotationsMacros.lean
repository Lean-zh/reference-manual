/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.NotationsMacros.Operators
import Manual.NotationsMacros.Precedence
import Manual.NotationsMacros.Notations
import Manual.NotationsMacros.SyntaxDef
import Manual.NotationsMacros.Elab
import Manual.NotationsMacros.DoElab
import Manual.NotationsMacros.Delab

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "记法与宏" =>
%%%
tag := "language-extension"
%%%

不同的数学领域有各自的记法惯例，许多记法在不同领域中会以不同含义重复使用。
形式化开发必须能够使用既有记法：形式化数学本就困难，而在不同语法之间转换所带来的心智负担可能相当沉重。
与此同时，控制记法扩展的作用域也很重要。
许多领域使用形式相近但含义迥异的记法；应当能够把这些不同领域的开发组合起来，同时让读者和系统都知道文件任一区域中采用的是哪套惯例。

Lean 使用多种机制解决记法可扩展性问题，每种机制负责问题的不同方面。
它们可以灵活组合，以达到所需效果：

 * {ref "parser"}_可扩展解析器_ {index}[parser] 能以声明式方式实现种类繁多的记法惯例，并灵活地将它们组合起来。
 * {ref "macro-and-elab"}[宏]可以轻松地把新语法映射到现有语法，这是为新构造赋予含义的一种简单方法。
  得益于{tech (key := "hygiene")}[卫生性]和源位置的自动传播，这一过程不会干扰 Lean 的交互功能。
 * {ref "macro-and-elab"}[精译器]在宏的表达能力不足时，为新语法提供与 Lean 自身语法所用相同的工具。
 * {ref "notations"}[记法]可同时定义解析器扩展、宏和美化打印器。
   定义中缀、前缀或后缀运算符时，{ref "operators"}[自定义运算符]会自动处理优先级与结合性。
 * 底层解析器扩展能够以修改词法单元和空白规则的方式扩展解析器，甚至可以完全替换 Lean 的语法。这是一个需要熟悉 Lean 内部机制的高级主题；尽管如此，无需修改编译器便能做到这一点仍十分重要。本参考手册正是使用一种语言扩展编写的：它以类似 Markdown 的文档语言替换 Lean 的具体语法，但源文件仍然是 Lean 文件。

{include 0 Manual.NotationsMacros.Operators}

{include 0 Manual.NotationsMacros.Precedence}

{include 0 Manual.NotationsMacros.Notations}

{include 0 Manual.NotationsMacros.SyntaxDef}

# 宏
%%%
tag := "macros"
%%%

{deftech (key := "Macros")}_宏_是从 {name Lean.Syntax}`Syntax` 到 {name Lean.Syntax}`Syntax` 的变换，发生在{tech (key := "elaborator") -normalize}[精译]期间以及{ref "tactic-macros"}[策略执行]期间。
用宏变换所得的结果替换语法，称为{deftech (key := "macro expansion")}_宏展开_。
一个{tech (key := "syntax kind")}[语法种类]可以关联多个宏，Lean 会按定义顺序尝试它们。
宏在一种{tech (key := "monad")}[单子]中运行；该单子可访问一些编译期元数据，并能发出错误消息或委托给后续宏，但宏单子的能力远弱于精译单子。

```lean -show
section
open Lean (Syntax MacroM)
```

宏与{tech (key := "syntax kinds")}[语法种类]相关联。
内部表将语法种类映射到类型为 {lean}`Syntax → MacroM Syntax` 的宏。
宏通过抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常委托给表中的下一项。
当某个 {name}`Syntax` 值的语法种类关联了一个不会抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 的宏时，该值_就是宏_。
如果宏抛出任何其他异常，就会向用户报告错误。
{tech (key := "Syntax categories")}[语法类别]与宏展开无关；不过，由于每种语法种类通常只关联一个语法类别，实践中它们不会相互干扰。

::::keepEnv
:::example "宏错误报告" (file := "Macro Error Reporting")
以下宏会在参数是字面数值五时报告错误。
在其他所有情况下，它展开为自己的参数。
```lean
syntax &"notFive" term:arg : term
open Lean in
macro_rules
  | `(term|notFive 5) =>
    Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) =>
    pure e
```

应用于语法形式不是数值五的项时，精译成功：
```lean (name := notFiveAdd)
#eval notFive (2 + 3)
```
```leanOutput notFiveAdd
5
```

触发错误分支时，用户会收到错误消息：
```lean (name := notFiveFive) +error
#eval notFive 5
```
```leanOutput notFiveFive
'5' is not allowed here
```
:::
::::

精译一段语法之前，精译器会检查其{tech (key := "syntax kind")}[语法种类]是否关联了宏。
这些宏会依次尝试。
如果某个宏成功，并可能返回了不同种类的语法，则会重复检查并继续展开宏，直到语法最外层不再是宏。
随后便可继续精译或执行策略。
只有语法的最外层（通常是一个 {name Lean.Syntax.node}`node`）会被展开，而宏展开的输出可能包含本身也是宏的嵌套语法。
精译器到达这些嵌套宏时，会依次将其展开。

具体而言，Lean 中会在三种情形下进行宏展开：

 1. 在项精译期间，精译器会先展开待精译语法最外层的宏，再调用{ref "elaborators"}[该语法的项精译器]。

 2. 在命令精译期间，精译器会先展开待精译语法最外层的宏，再调用{ref "elaborators"}[该语法的命令精译器]。

 3. 在策略执行期间，最外层语法中的宏会在{ref "tactic-macros"}[将该语法作为策略执行之前]展开。


```lean -keep -show
-- 检验上一段的论断：宏可以在精译前放弃处理
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#check_msgs in
#eval doubled 5

/--
error: elaboration function for `termDoubled_` has not been implemented
  doubled (5 + 2)
-/
#check_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#check_msgs in
#eval doubled (5 + 2)
```

## 卫生性
%%%
tag := "macro-hygiene"
%%%

如果一个宏的展开不会导致标识符捕获，那么该宏就是{deftech (key:="hygiene")}_卫生的_。
{deftech (key := "Identifier capture")}[标识符捕获]是指标识符最终指向的绑定位置并非源代码中该标识符出现处作用域内的绑定位置。
标识符捕获有两类：
 * 如果宏的展开引入了绑定器，那么宏参数中的标识符可能会因名称恰好相同而最终指向这些新引入的绑定器。
 * 如果宏的展开意图引用某个名称，但宏所用的上下文在局部绑定了该名称，或其中新引入了同名全局名称，那么它最终可能引用错误的名称。

第一类变量捕获可通过确保宏引入的每个绑定都使用新生成且全局唯一的名称来避免；第二类则可通过始终使用完全限定名称引用常量来避免。
每次调用宏时都必须重新生成新名称，以免递归宏中发生变量捕获。
这些技巧容易出错。
变量捕获问题很难测试，因为它依赖名称选择上的巧合；而始终贯彻这些技巧又会产生冗杂代码。

Lean 具有自动卫生机制：在几乎所有情况下，宏都会自动保持卫生。
通过给宏引入的标识符标注{deftech (key := "macro scopes")}_宏作用域_来避免新引入绑定造成的捕获；宏作用域能唯一标识每次宏展开调用。
如果标识符的绑定处和使用处具有相同的宏作用域，那么它们由同一步宏展开引入，应当相互指代。
同理，宏生成代码中的全局名称使用处不会被展开上下文中的局部绑定捕获，因为这些使用处带有绑定出现处所没有的宏作用域。
为防止新引入的全局名称造成捕获，宏体生成代码中的潜在全局名称引用会被标注上引用时所有匹配全局名称的集合。
带有潜在指称对象标注的标识符称为{deftech (key := "pre-resolved identifiers")}_预解析标识符_；{name}`Syntax.ident` 构造器上的 {lean}`Syntax.Preresolved` 字段用于存储这些潜在指称对象。
精译期间，如果一个标识符关联了预解析的全局名称，那么其他全局名称不会被视为有效的引用目标。

在生成语法中引入宏作用域和预解析标识符发生于{tech (key := "quotation")}[引用]期间。
不通过引用来构造语法的宏也应以其他方式确保卫生性。
有关 Lean 卫生算法的更多细节，请参阅 {citet beyondNotations ullrich23}[].

## 宏单子
%%%
tag := "macro-monad"
%%%

宏单子 {name Lean.MacroM}`MacroM` 的能力足以实现卫生性并报告错误。
宏展开不能直接修改环境、执行合一、检查当前局部上下文，也不能进行任何只在某个特定上下文中才有意义的操作。
因此，同一套宏机制可以贯穿 Lean 使用，也使宏比{tech (key := "elaborators")}[精译器]更容易编写。

{docstring Lean.MacroM}

{docstring Lean.Macro.expandMacro?}

{docstring Lean.Macro.trace}

### 异常与错误
%%%
tag := "macro-exceptions"
%%%

{name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常用于宏展开期间的控制流。
它表示当前宏无法展开所收到的语法，但并未发生错误。
由 {name Lean.Macro.throwError}`throwError` 和 {name Lean.Macro.throwErrorAt}`throwErrorAt` 抛出的异常会终止宏展开，并向用户报告错误。

{docstring Lean.Macro.throwUnsupported}

{docstring Lean.Macro.Exception.unsupportedSyntax}

{docstring Lean.Macro.throwError}

{docstring Lean.Macro.throwErrorAt}

### 与卫生性相关的操作
%%%
tag := "macro-monad-hygiene"
%%%

{tech (key := "Hygiene")}[卫生性]通过向语法中出现的标识符添加{tech (key := "macro scopes")}[宏作用域]来实现。
通常，{tech (key := "quotation")}[引用]过程会添加所有必要的作用域，但直接构造语法的宏必须为其引入的标识符添加宏作用域。

{docstring Lean.Macro.withFreshMacroScope}

{docstring Lean.Macro.addMacroScope}

### 查询环境
%%%
tag := "macro-environment"
%%%

宏只能有限地查询环境。
它们可以检查常量是否存在并解析名称，但无法进行更深入的内省。

{docstring Lean.Macro.hasDecl}

{docstring Lean.Macro.getCurrNamespace}

{docstring Lean.Macro.resolveNamespace}

{docstring Lean.Macro.resolveGlobalName}

## 引用
%%%
tag := "quotation"
%%%

{deftech (key := "Quotation")}_引用_把代码标记为以 {name}`Syntax` 类型的数据表示。
被引用的代码会被解析，但不会被精译——它必须在语法上正确，却不必有意义。
引用让以编程方式生成代码容易得多：无需逆向推导 Lean 解析器会产生的 {name Lean.Syntax.node}`node` 值的具体嵌套结构，而可以直接调用解析器来创建它们。
这种方式面对语法重构也更稳健；重构可能改变解析树的内部结构，却不影响用户可见的具体语法。
Lean 中的引用由 `` `( `` 和 `)` 包围。

可以在开头的反引号和左括号之后写出被引用的语法类别或解析器名称，再跟一条竖线（`|`）。
作为特例，名称 `tactic` 可用于解析策略或策略序列。
若未提供语法类别或解析器，Lean 会同时尝试把引用解析为项和非空命令序列。
项引用的优先级高于命令引用，因此有歧义时会选择项解释；显式指明引用的是命令序列可覆盖这一选择。

::::keepEnv
:::example "项引用与命令引用的语法" (file := "Term vs Command Quotation Syntax")
```lean -show
open Lean
```

在以下示例中，引用的内容既可以是函数应用，也可以是命令序列。
二者匹配文件中的同一区域，因此{tech (key := "local longest-match rule")}[局部最长匹配规则]与此无关。
项引用的优先级高于命令引用，所以该引用被解释为项。
项要求其{tech (key := "antiquotations")}[反引用]具有 {lean}``TSyntax `term`` 类型，而不是 {lean}``TSyntax `command``。
```lean +error (name := cmdQuot)
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1 $cmd2)
```
结果是两个如下所示的类型错误：
```leanOutput cmdQuot
Application type mismatch: The argument
  cmd1
has type
  TSyntax `command
but is expected to have type
  TSyntax `term
in the application
  cmd1.raw
```

引用的类型（{lean}``MacroM (TSyntax `command)``）不会用于选择结果，因为语法优先级先于精译应用。
此处，指定反引用为命令即可消除歧义，因为函数应用要求这些位置是项：
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1:command $cmd2:command)
```
同样，在引用中插入一个命令，也会排除它是项的可能性：
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1 $cmd2 #eval "hello!")
```
:::
::::

```lean -show
-- 无法提取解析器优先级（它们只保存在已编译 Parser 代码旁的 Pratt 表中），
-- 因此，此优先级测试通过检查引用解析器可观察到的相对优先级来完成。
-- quote parsers.

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `Lean.Parser.Term.app { raw := Syntax.missing }.raw
            (Syntax.node1 info `null { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩) $(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `null { raw := Syntax.missing }.raw
            { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `command)
-/
#check_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#check_msgs in
#check (`(tactic| $(⟨.missing⟩):tactic) : MacroM _)

/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node1 info `Lean.Parser.Tactic.seq1
            (Syntax.node3 info `null { raw := Syntax.missing }.raw (Syntax.atom info ";")
              { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `tactic.seq)
-/
#check_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```

:::freeSyntax term -open (title := "引用")

Lean 的语法包含项、命令、策略和策略序列的引用，也包含一种通用引用语法，可引用 Lean 能够解析的任何输入。
项引用优先级最高，其后依次是策略引用、通用引用，最后是命令引用。

```grammar
`(term|`($_:term))
*******
"`("$_:command+")"
*******
`(term|`(tactic| $_:tactic))
*******
`(term|`(tactic| $_:tactic;*))
*******
"`("p:ident"|"/-- 在此解析一个 {p} -/")"
```
:::

```lean -show
section M
variable {m : Type → Type}
open Lean (MonadRef MonadQuotation)
open Lean.Elab.Term (TermElabM)
open Lean.Elab.Command (CommandElabM)
open Lean.Elab.Tactic (TacticM)
```

引用的类型不是 {name}`Syntax`，而是类型为 {lean}`m Syntax` 的单子动作。
引用之所以是单子的，是因为它会如{ref "macro-hygiene"}[卫生性一节]所述，通过添加{tech (key := "macro scopes")}[宏作用域]和预解析标识符来实现{tech (key := "hygiene")}[卫生性]。
要使用的具体单子是引用的隐式参数；只要某单子具有 {name}`MonadQuotation` 类型类的实例，就可以使用。
{name}`MonadQuotation` 扩展了 {name}`MonadRef`，后者使引用能够访问宏展开器或精译器当前正在处理的语法的源位置。{name}`MonadQuotation` 还提供了向标识符添加{tech (key := "macro scopes")}[宏作用域]以及为子任务使用新宏作用域的能力。
支持引用的单子包括 {name}`MacroM`、{name}`TermElabM`、{name}`CommandElabM` 和 {name}`TacticM`。

```lean -show
end M
```


```lean -show
-- 验证上文关于单子的论断
open Lean in
example [Monad m] [MonadQuotation m] : m Syntax := `(term|2 + 2)
```

### 准引用
%%%
tag := "quasiquotation"
%%%

{deftech (key := "Quasiquotation")}_准引用_是一种可包含{deftech (key := "antiquotations")}_反引用_的引用形式；反引用是引用中不被引用的区域，其中的表达式会被求值以产生语法。
准引用本质上是一个模板；外层被引用区域提供固定框架，总是产生相同的外层语法，而反引用则产生最终语法中会变化的部分。
Lean 中所有引用都是准引用，因此无需特殊语法来区分准引用和其他引用。
引用过程不会给通过反引用插入的标识符添加宏作用域，因为这些标识符要么来自另一处引用（此时已具有宏作用域），要么来自宏的输入（此时不应有宏作用域，因为它们并非由宏引入）。

基本反引用由美元符号（`$`）及其后紧邻的标识符组成。
这表示要在被引用语法的这个位置代入相应变量的值；该值应当是一棵语法树。
把表达式包在括号中，即可将整个表达式用作反引用。

```lean -show
section
open Lean
example (e : Term) : MacroM Syntax := `(term| $e)

example (e : Term) : MacroM Syntax := `(term| $(e))

--example (e : Term) : MacroM Syntax := `(term| $ (e))

end
```



```lean -show
section
open Lean (TSyntax SyntaxNodeKinds)
variable {c : SyntaxNodeKinds}
```

Lean 的解析器会根据给定位置所期待的内容，为每个反引用指派一个语法类别。
如果解析器期待语法类别 {lean}`c`，那么反引用的类型就是 {lean}`TSyntax c`。


某些语法类别可以由其他类别的元素匹配。
例如，数值和字符串字面量除了属于各自的语法类别外，也是有效的项。
可在反引用后附加冒号和类别名称来标注预期类别；这会让解析器验证所标注的类别在给定位置是否可接受，并在解析树中构造所需的中间层。

:::freeSyntax antiquot (title := "反引用") -open
```grammar
"$"ident(":"ident)?
*******
"$("term")"(":"ident)?
```
反引用起始的美元符号（'$'）与其后的标识符或带括号项之间不允许有空白。
同样，标注反引用语法类别的冒号两侧也不允许有空白。
:::

:::example "准引用" (file := "Quasiquotation")

本例使用了两种形式的反引用。
由于自然数不是语法，因此使用 {name Lean.quote}`quote` 将数转换为表示该数的语法。

```lean
open Lean in
example [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `($x + $(quote (n + 2)))
```
:::

:::::keepEnv
::::example "反引用标注" (file := "Antiquotation Annotations")
```lean -show
open Lean
```

本例要求 {lean}`m` 是能够执行引用的单子。
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

默认情况下，反引用 `$e` 应当是项，因为加法的第二个参数位置紧接着期待的就是这个语法类别。
```lean (name := ex1)
def ex1 (e) := show m _ from `(2 + $e)
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```

把 `$e` 标注为数值字面量是可行的，因为数值字面量也是有效的项。
参数 `e` 的预期类型变为 ``TSyntax `num``。
```lean (name := ex2)
def ex2 (e) := show m _ from `(2 + $e:num)
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```

美元符号与标识符之间不允许有空格。
```syntaxError ex2err1
def ex2 (e) := show m _ from `(2 + $ e:num)
```
```leanOutput ex2err1
<example>:1:34-1:36: unexpected token '$'; expected '`(tactic|', 'do' or no space before spliced term
```

冒号之前同样不允许有空格：
```syntaxError ex2err2
def ex2 (e) := show m _ from `(2 + $e :num)
```
```leanOutput ex2err2
<example>:1:37-1:39: unexpected token ':'; expected ')'
```
::::
:::::

```lean -show
end
```

:::::keepEnv
::::example "展开准引用" (file := "Expanding Quasiquotation")
打印 {name}`f` 的定义可以展示准引用的展开结果。
```lean (name := expansion)
open Lean in
def f [Monad m] [MonadQuotation m]
    (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```
```leanOutput expansion
def f : {m : Type → Type} → [Monad m] → [Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let quotCtx ← Lean.MonadQuotation.getContext
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toRawSubstring' (Lean.addMacroScope quotCtx `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toRawSubstring' (Lean.addMacroScope quotCtx `k scp) []))) }.raw
```

:::paragraph
```lean -show
section
open Lean (Term)
open Lean.Quote
variable {x : Term} {n : Nat}
```

在此输出中，引用是一个 {keywordOf Lean.Parser.Term.do}`do` 块。
它首先为所得语法构造源信息；该信息通过向编译器查询当前正在处理的用户语法而获得。
然后，它取得当前宏作用域和正在处理的模块名称，因为宏作用域会相对于模块添加，以便独立编译并避免使用全局计数器。
接着，它使用 {name}`Syntax.node1` 和 {name}`Syntax.node2` 等辅助函数构造节点；这些函数会创建具有指定子节点数量的 {name}`Syntax.node`。
每个标识符都会添加宏作用域，并使用 {name Lean.TSyntax.raw}`TSyntax.raw` 提取有类型语法包装器中的内容。
{lean}`x` 和 {lean  (type := "Term")}`quote (n + 2)` 的反引用直接出现在展开结果中，作为 {name}`Syntax.node3` 的参数。

```lean -show
end
```
:::

::::
:::::


### 拼接
%%%
tag := "splices"
%%%

除了通过反引用纳入其他语法外，准引用还可以包含{deftech (key := "splices")}_拼接_。
拼接表示要按顺序插入数组中的元素。
重复元素可以包含分隔符，例如列表或数组元素之间的逗号。
拼接可以是带有{deftech (key := "splice suffix")}_拼接后缀_的普通反引用，也可以是提供额外重复结构的{deftech (key := "extended splices")}_扩展拼接_。

拼接后缀由星号或一个有效原子后跟星号（`*`）组成。
后缀可以跟在任何标识符反引用或项反引用之后。
带有拼接后缀 `*` 的反引用对应 `many` 或 `many1` 的用法；语法规则中的 `*` 与 `+` 后缀都对应 `*` 拼接后缀。
星号前包含原子的拼接后缀对应 `sepBy` 或 `sepBy1` 的用法。
拼接后缀 `?` 对应 `optional` 或语法规则中的 `?` 后缀。
由于 `?` 是有效的标识符字符，要把它用作后缀时必须给标识符加括号。

尽管语法的重复说明符与反引用后缀有所重叠，它们的语法并不相同。
定义语法时，Lean 内置了后缀 `*`、`+`、`,*`、`,+`、`,*,?` 和 `,+,?`。
除了 `,` 以外，没有更简短的方式指定分隔符。
反引用后缀要么只是 `*`，要么是提供给 `sepBy` 或 `sepBy1` 的原子后跟 `*`。
语法重复 `+` 和 `*` 对应拼接后缀 `*`；重复 `,*`、`,+`、`,*,?` 和 `,+,?` 对应 `,*`。
语法和拼接中的可选后缀 `?` 相互对应。


:::table +header
 * - 语法重复
   - 拼接后缀
 * - `+` `*`
   - `*`
 * - `,*` `,+` `,*,?` `,+,?`
   - `,*`
 * - `sepBy(_, "S")` `sepBy1(_, "S")`
   - `S*`
 * - `?`
   - `?`
:::


::::keepEnv
:::example "带后缀的拼接" (file := "Suffixed Splices")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
open Lean.Elab.Command (CommandElabM)
```

本例要求 {lean}`m` 是能够执行引用的单子。
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

默认情况下，反引用 `$e` 应当是一个以逗号分隔的项数组，正如列表体中所期待的那样：
```lean (name := ex1)
def ex1 (xs) := show m _ from `(#[$xs,*])
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```

不过，Lean 提供了一组不同数组表示之间的强制转换，可自动插入或移除分隔符，因此普通的项数组也可接受：
```lean (name := ex2)
def ex2 (xs : Array (TSyntax `term)) :=
  show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```

重复标注也可用于项反引用和语法类别标注。
本例位于 {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中，以便方便地记录结果。
```lean (name := ex3)
def ex3 (size : Nat) := show CommandElabM _ from do
  let mut nums : Array Nat := #[]
  for i in [0:size] do
    nums := nums.push i
  let stx ← `(#[$(nums.map (Syntax.mkNumLit ∘ toString)):num,*])
  -- 在此使用 logInfo 会让语法经由
  -- 美化打印器渲染。
  logInfo stx

#eval ex3 4
```
```leanOutput ex3
#[0, 1, 2, 3]
```
:::
::::

::::keepEnv
:::example "非逗号分隔符" (file := "Non-Comma Separators")
以下非常规列表语法使用破折号或双星号分隔数值元素，而不是逗号。
```lean
syntax "⟦" sepBy1(num, " — ") "⟧": term
syntax "⟦" sepBy1(num, " ** ") "⟧": term
```
这意味着在 `⟦` 和 `⟧` 原子之间，`—*` 与 `***` 都是有效的拼接后缀。
对于 `***`，前两个星号是语法规则中的原子，第三个才是重复后缀。
```lean
macro_rules
  | `(⟦$n:num—*⟧) => `(⟦$n***⟧)
  | `(⟦$n:num***⟧) => `([$n,*])
```
```lean (name := nonComma)
#eval ⟦1 — 2 — 3⟧
```
```leanOutput nonComma
[1, 2, 3]
```
:::
::::

::::keepEnv
:::example "可选拼接" (file := "Optional Splices")
```imports -show
import Lean.Elab
```
以下语法声明可选地匹配两个词法单元之间的一个项。
嵌套 `term` 外的括号是必需的，因为 `term?` 是有效标识符。
```lean -show
open Lean
```
```lean
syntax "⟨| " (term)? " |⟩": term
```

项的 `?` 拼接后缀期待一个 {lean}`Option Term`：
```lean
def mkStx [Monad m] [MonadQuotation m]
    (e : Option Term) : m Term :=
  `(⟨| $(e)? |⟩)
```
```lean (name := checkMkStx)
#check mkStx
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option Term) : m Term
```

提供 {name}`some` 时，可选项会出现。
```lean (name := someMkStx)
#eval do logInfo (← mkStx (some (quote 5)))
```
```leanOutput someMkStx
⟨| 5 |⟩
```

提供 {name}`none` 时，可选项不会出现。
```lean (name := noneMkStx)
#eval do logInfo (← mkStx none)
```
```leanOutput noneMkStx
⟨| |⟩
```

:::
::::

```lean -show
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- 展示不同重复语法种类之间的强制转换

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```

### 词法单元反引用
%%%
tag := "token-antiquotations"
%%%

除了完整语法的反引用外，Lean 还提供{deftech (key := "token antiquotations")}_词法单元反引用_，它允许用其他语法的源信息替换某个原子的源信息。
所得合成源信息会被标记为{tech (key := "canonical")}[规范的]，从而用于错误消息、证明状态及其他反馈。
其主要用途是控制 Lean 向用户报告错误消息或其他信息的位置。
词法单元反引用不允许通过求值插入任意原子。
词法单元反引用由一个原子（即关键字）组成

:::freeSyntax antiquot +open (title := "词法单元反引用")
词法单元反引用会把词法单元上的源信息（类型为 {name Lean.SourceInfo}`SourceInfo`）替换为其他语法的源信息。

```grammar
atom"%$"ident
```
:::


::: TODO

带括号的更复杂拼接

:::

## 匹配语法
%%%
tag := "quote-patterns"
%%%

:::seeAlso
新语法使用{ref "syntax-rules"}[语法扩展]定义。
:::

准引用可以用于模式匹配，以识别符合某个模板的语法。
正如用作项的引用中的反引用区域会被当作普通未引用表达式处理，模式中的反引用区域也会被当作普通 Lean 模式处理。
引用模式的编译方式不同于其他模式，因此不能在同一个 {keywordOf Lean.Parser.Term.match}`match` 表达式中与非引用模式混用。
与普通引用一样，引用模式首先由 Lean 的解析器处理。
随后，解析器输出会被编译成判断是否匹配的代码。
语法匹配假定被匹配语法由 Lean 解析器产生——无论是通过引用还是直接来自用户代码——并利用这一点省略某些检查。
例如，如果某个位置只能出现特定关键字，就可以省略检查。

在以下情况下，语法与引用模式匹配：


 : 原子

  关键字原子（如 {keywordOf termIfThenElse}`if` 或 {keywordOf Lean.Parser.Term.match}`match`）会产生单例节点，其种类是以 `token.` 开头、后接该原子。
  在许多情况下，无需检查具体原子值，因为语法只允许一个关键字，此时不会执行检查。
  如果被匹配项的语法要求该检查，就会比较节点种类。

  字面量（如字符串或数值字面量）按其底层字符串表示比较。
  模式 `` `(0x15) `` 与引用 `` `(21) `` 不匹配。

 : 节点

  如果模式和被匹配值都表示 {name}`Syntax.node`，则当二者语法种类相同、子节点数相同，且每个子模式都匹配对应子值时，匹配成功。

 : 标识符

  如果模式和被匹配值都是标识符，则比较其字面 {name Lean.Name}`Name` 值在忽略宏作用域后的相等性。
  “看起来”相同的标识符会匹配，它们是否指向同一绑定并不重要。
  这一设计使引用模式匹配可用于无法访问编译期环境、因而无法按引用比较名称的上下文。


由于引用模式匹配基于解析器发出的节点种类，外观相同的引用如果来自不同语法类别，也可能不匹配。
拿不准时，在引用中写明语法类别会有所帮助。

:::leanSection
```lean -show
open Lean Syntax
variable {k : SyntaxNodeKinds} {sep : String}

```

语法模式匹配所绑定的变量具有 {lean}`TSyntax k` 类型，其中 {lean}`k` 描述可能的语法种类。
重复中的变量具有 {lean}`TSyntaxArray k` 类型；如果重复以字符串 {lean}`sep` 分隔，则类型为 {lean}`TSepArray k sep`。
{ref "typed-syntax"}[有类型语法一节]会更详细地介绍 {name}`TSyntax`。
:::

::::example "语法模式匹配" (file := "Syntax Pattern Matching")

```lean -show
open Lean Syntax
```

列表推导是一种受标准集合构造记法启发、用于书写列表的记法。
列表推导由方括号构成，其中先是结果项，随后是若干个_限定子_；每个限定子要么从另一个列表引入变量，要么施加必须满足的条件。
限定子是嵌套的：每个新变量的值都会针对之前的每个值求值。

```lean
syntax qbind := ident "←" term

syntax qpred := term

syntax qualifier := atomic(qbind) <|> qpred

syntax "[" term "|" qualifier,* "]" : term
```

列表推导可以脱糖为一系列对 {name}`List.flatMap` 的调用。
变量引入会被翻译成在该变量值表达式上调用 {name List.flatMap}`flatMap`，而谓词会被翻译为条件表达式：谓词为真或假时分别返回一个值或零个值。
最后一个 {name List.flatMap}`flatMap` 的函数体就是结果项。

这种脱糖可以实现为使用准引用模式的宏：
```lean
macro_rules
  | `(term|[$e | $qs,* ]) => do
    let init ← `([$e])
    qs.getElems.foldrM (β := Term) (init := init) fun
      | `(qualifier|$x ← $e'), r =>
        `(($e' : List _) |>.flatMap fun $x => $r)
      | `(qualifier|$e':term), r =>
        `((if $e' then [()] else []) |>.flatMap fun () => $r)
      | other, _ =>
        Macro.throwErrorAt other "Unknown qualifier"
```
起初，限定子序列的类型是 {lean}``TSepArray `qualifier ","``，表示它是以逗号分隔的限定子序列。
{lean}`TSepArray.getElems` 将其转换为 {lean}``TSyntaxArray `qualifier``，后者是 {lean}``Array (TSyntax `qualifier)`` 的缩写。
这样便可用{tech (key := "generalized field notation")}[广义字段记法]调用 {name}`Array.foldrM`。
谓词分支中的 `term` 标注是必需的，以防匹配值的语法种类为 {lean}`` `qualifier ``；必须从该值外解开一个 {name Syntax.node}`node`。

列表推导的行为符合预期：
```lean (name := evalComp)
#eval [ s!"{x}; {y}" |
  x ← (1...5).toList,
  x % 2 = 0,
  y ← [true, false]
]
```
```leanOutput evalComp
["2; true", "2; false", "4; true", "4; false"]
```
::::

## 定义宏
%%%
tag := "defining-macros"
%%%


定义宏主要有两种方式：{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令和 {keywordOf Lean.Parser.Command.macro}`macro` 命令。
{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令将宏关联到现有语法，而 {keywordOf Lean.Parser.Command.macro}`macro` 命令会同时定义新语法以及把它翻译为现有语法的宏。
{keywordOf Lean.Parser.Command.macro}`macro` 命令可视为 {keywordOf Lean.Parser.Command.notation}`notation` 的推广：它允许以编程方式生成展开结果，而不只是通过代入生成。

### `macro_rules` 命令
%%%
tag := "macro_rules"
%%%

:::syntax command (title := "使用 {keyword}`macro_rules` 的基于规则的宏")

{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令接受一系列以语法模式匹配指定的重写规则，并把每条规则添加为一个宏。
这些规则按顺序尝试，且先于之前定义的宏；之后的宏定义还可继续添加宏规则。

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro_rules $[(kind := $k)]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```
:::

宏中的模式必须是引用模式。
它们可以匹配任意语法类别的语法，但一个给定模式只能匹配一种语法种类。
如果引用没有指定类别或解析器，它可以匹配项或命令（序列），但不能二者都匹配。
有歧义时会选择项解析器。

在内部，宏存储于一张从每个{tech (key := "syntax kind")}[语法种类]映射到其宏的表中。
{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令可以显式标注语法种类。

如果显式提供了语法种类，宏定义会检查每个引用模式是否具有该种类。
如果引用的解析结果是一个{tech (key := "choice node")}[选择节点]（即解析有歧义），则模式会针对具有指定种类的每个备选项复制一次。
如果没有任何备选项具有指定种类，就会报错。

如果没有显式提供种类，则每个模式使用解析器确定的种类。
这些模式不必全都具有相同的语法种类；每种至少被一个模式使用的语法种类都会定义宏。
如果引用模式的解析结果是{tech (key := "choice node")}[选择节点]（即解析有歧义），就会报错。

与 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 关联的文档注释会在语法本身没有文档注释时显示给用户。
否则显示语法本身的文档注释。

与{ref "notations"}[记法]和{ref "operators"}[运算符]一样，宏规则也可声明为 `scoped` 或 `local`。
作用域宏仅在当前命名空间打开时有效，而局部宏规则仅在当前{tech (key := "section scope")}[节作用域]内有效。

::::keepEnv
:::example "习语括号" (file := "Idiom Brackets")
习语括号是使用应用函子时的一种替代语法。
如果习语括号包含函数应用，则函数会被包在 {name}`pure` 中，并使用 `<*>` 依次应用于每个参数。{TODO}[将运算符链接到文档]
Lean 默认不支持习语括号，但可以使用宏定义它们。
```lean
syntax (name := idiom) "⟦" (term:arg)+ "⟧" : term

macro_rules
  | `(⟦$f $args*⟧) => do
    let mut out ← `(pure $f)
    for arg in args do
      out ← `($out <*> $arg)
    return out
```

这套新语法可以立即使用。
```lean
def addFirstThird [Add α] (xs : List α) : Option α :=
  ⟦Add.add xs[0]? xs[2]?⟧
```
```lean (name := idiom1)
#eval addFirstThird (α := Nat) []
```
```leanOutput idiom1
none
```
```lean (name := idiom2)
#eval addFirstThird [1]
```
```leanOutput idiom2
none
```
```lean (name := idiom3)
#eval addFirstThird [1,2,3,4]
```
```leanOutput idiom3
some 4
```
:::
::::

::::keepEnv
:::example "有作用域的宏" (file := "Scoped Macros")
```lean -show
open Lean
```
作用域宏规则只在其命名空间内有效。
当命名空间 `ConfusingNumbers` 打开时，数值字面量会被赋予错误含义。
```lean
namespace ConfusingNumbers
```

以下宏识别作为奇数数值字面量的项，并将其替换为数值的两倍。
如果它无条件替换为两倍数值，宏展开就会陷入无限循环，因为同一规则总会匹配输出。

```lean
scoped macro_rules
  | `($n:num) => do
    if n.getNat % 2 = 0 then Lean.Macro.throwUnsupported
    let n' := (n.getNat * 2)
    `($(Syntax.mkNumLit (info := n.raw.getHeadInfo) (toString n')))
```

命名空间结束后，该宏不再使用。
```lean
end ConfusingNumbers
```

不打开命名空间时，数值字面量按通常方式工作。
```lean (name := nums1)
#eval (3, 4)
```
```leanOutput nums1
(3, 4)
```

命名空间打开时，宏会把 {lean}`3` 替换为 {lean}`6`。
```lean (name := nums2)
open ConfusingNumbers

#eval (3, 4)
```
```leanOutput nums2
(6, 4)
```

通常，用宏改变数值或其他字面量的解释并没有用处。
不过，在给 {tactic}`trivial` 这类可扩展策略添加新规则时，作用域宏非常有用：这些规则适合命名空间中的内容，却不应始终启用。
:::
::::

在幕后，一条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令会为其引用模式所匹配的每种语法种类生成一个宏函数。
该函数有一个抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常的默认分支，以便继续尝试其他宏。


一条包含两条规则的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令，并不总是等价于两条各含一个匹配的独立命令。
首先，一条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 中的规则按从上到下顺序尝试，但最近声明的宏会最先尝试，因此拆开时顺序需要反转。
此外，如果宏中较早的规则抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，后续规则不会再尝试；若它们位于不同的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令中，则仍会被尝试。

::::example "一组与两组宏规则" (file := "One vs. Two Sets of Macro Rules")
```lean -show
open Lean.Macro
```

`arbitrary!` 宏旨在展开为某个给定类型的任意选定值。

```lean
syntax (name := arbitrary!) "arbitrary! " term:arg : term
```

:::keepEnv
```lean
macro_rules
  | `(arbitrary! ()) => `(())
  | `(arbitrary! Nat) => `(42)
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
  | `(arbitrary! Nat) => `(0)
```

用户可以定义更多组宏规则来扩展它，例如这条针对 {lean}`Empty` 且会失败的规则：
```lean
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```

```lean (name := arb1)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb1
(42, 42)
```
:::

:::keepEnv
如果所有宏规则都定义为独立分支，那么结果会改用后定义的 {lean}`Nat` 分支。
这是因为单条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令中的规则按从上到下顺序检查，而较晚定义的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令优先于较早定义的命令。

```lean
macro_rules
  | `(arbitrary! ()) =>
    `(())
macro_rules
  | `(arbitrary! Nat) =>
    `(42)
macro_rules
  | `(arbitrary! ($t1 × $t2)) =>
    `((arbitrary! $t1, arbitrary! $t2))
macro_rules
  | `(arbitrary! Nat) =>
    `(0)
macro_rules
  | `(arbitrary! Empty) =>
    throwUnsupported
```

```lean (name := arb2)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb2
(0, 0)
```
:::

此外，如果任一规则抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，该命令中的后续规则都不会再检查。
```lean
macro_rules
  | `(arbitrary! (List Nat)) => throwUnsupported
  | `(arbitrary! (List $_)) => `([])

macro_rules
  | `(arbitrary! (Array Nat)) => `(#[42])
macro_rules
  | `(arbitrary! (Array $_)) => throwUnsupported
```

{lean}`List Nat` 分支精译失败，因为宏展开没有把 {keywordOf arbitrary!}`arbitrary!` 语法翻译为精译器支持的内容。
```lean (name := arb3) +error
#eval arbitrary! (List Nat)
```
```leanOutput arb3
elaboration function for `arbitrary!` has not been implemented
  arbitrary! (List Nat)
```

{lean}`Array Nat` 分支成功，因为第二组宏规则抛出异常后，会继续尝试第一组宏规则。
```lean (name := arb4)
#eval arbitrary! (Array Nat)
```
```leanOutput arb4
#[42]
```
::::


### `macro` 命令
%%%
tag := "macro-command"
%%%

```lean -show
section
open Lean
```

{keywordOf Lean.Parser.Command.macro}`macro` 命令会同时定义一条新的{tech (key := "syntax rule")}[语法规则]，并将其与一个{tech (key := "macro")}[宏]关联。
{keywordOf Lean.Parser.Command.notation}`notation` 只能定义新的项语法，其展开是将参数代入其中的项；与之不同，{keywordOf Lean.Parser.Command.macro}`macro` 命令可以在任意{tech (key := "syntax category")}[语法类别]中定义语法，并能在 {name}`MacroM` 单子中使用任意代码生成展开结果。
由于宏比记法灵活得多，Lean 无法自动生成逆展开器；这意味着通过 {keywordOf Lean.Parser.Command.macro}`macro` 命令实现的新语法可用于 Lean 的_输入_，但若不做进一步工作，Lean 的输出不会使用它。

:::syntax command (title := "宏声明")
```grammar
$[$_:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro$[:$p]? $[(name := $_)]? $[(priority := $_)]? $xs:macroArg* : $k:ident =>
  $tm
```
:::

:::syntax Lean.Parser.Command.macroArg -open (title := "宏参数")
宏的参数要么是语法项（用法与 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令中相同），要么是附带名称的语法项。
```grammar
$s:stx
```
```grammar
$x:ident:$stx
```
:::

在展开中，附加到语法项的名称会被绑定；它们的类型是适用于相应语法种类的 {name Lean.TSyntax}`TSyntax`。
如果解析器匹配的语法没有已定义的种类（例如因为名称应用于复杂说明），那么类型为 {lean}`TSyntax Name.anonymous`。

```lean -show -keep
-- 检查类型规则
open Lean Elab Term Macro Meta

elab "dbg_type " e:term ";" body:term : term => do
  let e' ← elabTerm e none
  let t ← inferType e'
  logInfoAt e t
  elabTerm body none

/--
info: TSyntax `str
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
---
info: Syntax.TSepArray `num ","
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
---
info: Syntax.TSepArray `num ","
-/
#check_msgs in
macro "gah!" thing:str other:(str <|> num) arg:num,* : term => do
  dbg_type thing; pure ()
  dbg_type other; pure ()
  dbg_type arg; pure ()
  return quote s!"{thing.raw} ||| {other.raw} ||| {arg.getElems}"

/-- info: "(str \"\\\"one\\\"\") ||| (num \"44\") ||| #[(num \"2\"), (num \"3\")]" : String -/
#check_msgs in
#check gah! "one" 44 2,3

```

文档注释与新语法关联；属性种类（无、`local` 或 `scoped`）像记法一样控制宏的可见性：`scoped` 宏在定义它的命名空间中，或任何打开该命名空间的{tech (key := "section scope")}[节作用域]中可用，而 `local` 宏仅在局部节作用域中可用。

在幕后，{keywordOf Lean.Parser.Command.macro}`macro` 命令本身由一个宏实现，该宏把它展开为一条 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令和一条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令。
应用于宏命令的任何属性都会应用于语法定义，但不会应用于 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令。

```lean -show
end
```

### 宏属性
%%%
tag := "macro-attribute"
%%%

可使用 {keywordOf Lean.Parser.Attr.macro}`macro` 属性手动把{tech (key := "Macros")}[宏]添加到某种语法种类。
这种指定宏的底层方式通常没有用处，除非它是由那些自身会生成宏定义的宏进行代码生成所得的结果。

:::syntax attr (title := "{keyword}`macro` 属性")
{keywordOf Lean.Parser.Attr.macro}`macro` 属性指定，应把某个函数视为指定语法种类的{tech (key := "macro")}[宏]。
```grammar
macro $_:ident
```
:::

::::keepEnv
:::example "宏属性" (file := "The Macro Attribute")
```lean -show
open Lean Macro
```
```lean
/-- 根据某个项在语法上的 N 份副本生成列表 -/
syntax (name := rep) "[" num " !!! " term "]" : term

@[macro rep]
def expandRep : Macro
  | `([ $n:num !!! $e:term]) =>
    let e' := Array.replicate n.getNat e
    `([$e',*])
  | _ =>
    throwUnsupported
```

对这个新表达式求值，可以看出宏已经存在。
```lean (name := attrEx1)
#eval [3 !!! "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
:::
::::

{include 0 Manual.NotationsMacros.Elab}

{include 0 Manual.NotationsMacros.DoElab}

{include 0 Manual.NotationsMacros.Delab}
