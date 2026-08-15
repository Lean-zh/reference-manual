/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "精译器" =>

%%%
tag := "elaborators"
file := "Elaborators"
%%%

:::seeAlso
* 精译器处理 {ref "syntax-ext"}[新的语法扩展]。

* {ref "quote-patterns"}[引用模式]是解构语法最典型的方式。
:::

宏通过把新语法翻译成已有语法来扩展 Lean，而 {deftech (key := "elaborators")}_精译器_ 则允许直接处理新语法。
精译器可以访问 Lean 自身为实现语言各项特性所使用的一切工具。
定义新的精译器后，语言扩展就能拥有与 Lean 任何内建特性同等的能力。

:::paragraph
精译器分为两类：

 * {deftech (key := "Command elaborators")}_命令精译器_ 用于向 Lean 添加新命令。
   命令通过副作用实现：它们可以向全局环境中加入新常量，扩展编译期表（例如跟踪 {tech (key := "instances")}[实例] 的表），也可以以信息、警告或错误的形式提供反馈，并且能完全访问 {name}`IO` 单子。
   命令精译器与它们能够处理的 {tech (key := "kind")}[语法种类] 相关联。

 * {deftech (key := "Term elaborators")}_项精译器_ 用于通过把语法翻译到 Lean 的核心类型论中来实现新项。
   它们能做命令精译器所能做的一切，此外还可以访问当前正在精译该项时所处的局部上下文。
   项精译器可以查找绑定变量、绑定新变量、统一两个项，等等。
   项精译器必须返回一个 {name}`Lean.Expr` 类型的值，也就是核心类型论的 AST。
:::

本节概述精译器，并给出若干示例。
Lean 自身的精译器也使用同样的工具，因此精译器源码本身就是进一步寻找示例的良好来源。
和宏一样，多个精译器可以与同一个语法种类相关联；它们会按顺序尝试，某个精译器也可以通过抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，把处理委托给表中的下一个精译器。

:::syntax command (title := "精译规则")

{keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 命令接受一组以语法模式匹配指定的精译规则，并将每一条都加入为精译器。
这些规则会按顺序尝试，并且会先于此前定义的精译器；之后的精译器还可以继续补充更多备选项。

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind elab_rules $[(kind := $k)]? $[: $_]? $[<= $_]?
  $[| `(free{(p:ident"|")?/-- 适用于 {p} 的语法 -/}) => $e]*
```

:::

命令、项和策略各自都维护着一张从语法种类映射到精译器的表。
冒号后指定精译器应当用于哪个语法类别，其值必须是 `term`、`command` 或 `tactic`。
{keywordOf Lean.Parser.Command.elab_rules}`<=` 会把给定标识符绑定到当前项精译上下文中的期望类型；它只能用于项精译器，并且一旦出现，就隐含语法类别为 `term`。


:::syntax attr (title := "精译器属性")
通过应用相应属性，可以把精译器直接关联到语法种类上。
每个属性都接受一个语法种类名，并把定义与该种类关联起来。

```grammar
term_elab $_
```
```grammar
command_elab $_
```
```grammar
tactic $_
```
:::

# 命令精译器
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Elaborators--Command-Elaborators"
%%%

:::::leanSection
```lean -show
open Lean Elab Command
```
命令精译器的类型是 {name}`CommandElab`，它是 {lean}`Syntax → CommandElabM Unit` 的缩写。
命令精译器既可以用 {keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 隐式定义，也可以通过定义一个函数并施加 {attr}`command_elab` 属性来显式定义。

:::example "查询环境" (file := "Querying the Environment")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

命令精译器可用于查询环境，从而发现有多少常量带有某个给定名称。
这个例子使用 {name}`MonadEnv` 类型类中的 {name}`getEnv` 来获取当前环境。
{name}`Environment.constants` 会给出一张从名称到其信息的映射（例如其类型，以及它是定义、{tech (key := "inductive type")}[归纳类型]声明等）。
{name}`logInfoAt` 允许把信息性输出关联到原程序中的语法上，并通过 {tech (key := "token antiquotation")}[词法单元反引用]来实现 Lean 的惯例：交互式命令的输出应当关联到其关键字。

```lean
syntax "#count_constants " ident : command

elab_rules : command
  | `(#count_constants%$tok $x) => do
    let pattern := x.getId
    let env ← getEnv
    let mut count : Nat := 0
    for (y, _) in env.constants do
      if pattern.isSuffixOf y then
        count := count + 1
    logInfoAt tok m!"Found {count} instances of '{pattern}'"
```

```lean (name := run)
def interestingName := 55
def NS.interestingName := "Another one"

#count_constants interestingName
```

```leanOutput run
Found 2 instances of 'interestingName'
```

:::

:::::

# 项精译器
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Elaborators--Term-Elaborators"
%%%

:::::leanSection
```lean -show
open Lean Elab Term
```
项精译器的类型是 {name}`TermElab`，它是 {lean}`Syntax → Option Expr → TermElabM Expr` 的缩写。
可选的 {lean}`Expr` 参数表示当前被精译的项的期望类型；如果尚未知晓类型，则为 `none`。
和命令精译器一样，项精译器既可以用 {keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 隐式定义，也可以通过定义函数并施加 {attr}`term_elab` 属性来显式定义。

:::example "避开某个类型" (file := "Avoiding a Type")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term
```

这个例子演示了一个与类型标注相反的语法精译器。
给定的项可以拥有除所指明类型之外的任何类型，并且元变量会以保守方式求解。
在此例中，{name}`elabType` 会调用项精译器，并确保得到的项确实是一个类型。
{name}`Meta.inferType` 为一个项推断类型，而 {name}`Meta.isDefEq` 则尝试通过合一让两个项 {tech (key := "definitional equality")}[定义等价]；成功时返回 {lean}`true`。

```lean
syntax (name := notType) "(" term  " !: " term ")" : term

@[term_elab notType]
def elabNotType : TermElab := fun stx _ => do
  let `(($tm:term !: $ty:term)) := stx
    | throwUnsupportedSyntax
  let unexpected ← elabType ty
  let e ← elabTerm tm none
  let eTy ← Meta.inferType e
  if (← Meta.isDefEq eTy unexpected) then
    throwErrorAt tm m!"Got unwanted type {eTy}"
  else pure e
```

如果类型位置上给出的并不是类型，那么 `elabType` 会抛出错误：
```lean (name := notType) +error
#eval ([1, 2, 3] !: "not a type")
```
```leanOutput notType
type expected, got
  ("not a type" : String)
```

如果该项的类型确定不等于所给类型，那么精译会成功：
```lean (name := ok)
#eval ([1, 2, 3] !: String)
```
```leanOutput ok
[1, 2, 3]
```

如果类型匹配，就会抛出错误：
```lean (name := nope) +error
#eval (5 !: Nat)
```
```leanOutput nope
Got unwanted type Nat
```

类型等价性检查可能会补全缺失信息，因此 {lean  (type := "String")}`sorry`（它可以有任意类型）也会被拒绝：
```lean (name := unif) +error
#eval (sorry !: String)
```
```leanOutput unif
Got unwanted type String
```
:::

:::example "使用任意局部变量" (file := "Using Any Local Variable")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

项精译器可以访问期望类型以及局部上下文。
这可用于构造一个与 {tactic}`assumption` 策略对应的项版本。

第一步是使用 {name}`getLocalHyps` 访问局部上下文。
它返回的上下文中，最外层绑定在左侧，因此这里按逆序遍历。
对于每个局部假设，都用 {name}`Meta.inferType` 推断其类型。
如果它有可能与期望类型相等，就返回该假设；若没有任何假设合适，则产生错误。

```lean
syntax "anything!" : term

elab_rules <= expected
  | `(anything!) => do
    let hyps ← getLocalHyps
    for h in hyps.reverse do
      let t ← Meta.inferType h
      if (← Meta.isDefEq t expected) then return h

    throwError m!"No assumption in {hyps} has type {expected}"
```

这个新语法会找到函数的绑定变量：
```lean (name := app)
#eval (fun (n : Nat) => 2 + anything!) 5
```
```leanOutput app
7
```

它会按预期选择最近的合适变量：
```lean (name := lets)
#eval
  let x := "x"
  let y := "y"
  "It was " ++ y
```
```leanOutput lets
"It was y"
```

当没有合适的假设时，它会返回一个描述此次尝试的错误：
```lean (name := noFun) +error
#eval
  let x := Nat.zero
  let y := "hello"
  fun (f : Nat → Nat) =>
    (anything! : Int → Int)
```
```leanOutput noFun
No assumption in [x, y, f] has type Int → Int
```

由于这里使用了合一，精译器会选择自然数字面量，因为数值字面量可以拥有任何带有 {name}`OfNat` 实例的类型。
遗憾的是，函数并没有 {name}`OfNat` 实例，因此后续的实例合成会失败。
```lean (name := poly) +error
#eval
  let x := 5
  let y := "hello"
  (anything! : Int → Int)
```
```leanOutput poly
failed to synthesize instance of type class
  OfNat (Int → Int) 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  Int → Int
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::::

# 自定义策略
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Elaborators--Custom-Tactics"
%%%

自定义策略见 {ref "custom-tactics"}[关于策略的小节]。
