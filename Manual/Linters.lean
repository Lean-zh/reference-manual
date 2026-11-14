/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Linter.CodeQuality
import Lean.Linter.EnvLinter

import Manual.Meta
import Manual.ZhDocString.Upstream

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Verso.Code.External

#doc (Manual) "代码检查器与代码质量" =>
%%%
file := "Linters-and-Code-Quality"
tag := "linters"
shortContextTitle := "代码检查器"
%%%

{deftech (key := "linter")}[代码检查器]是一种用于识别代码中有问题或易出错模式的检查机制。
代码检查器也可用于强制执行项目特定的文档、代码风格或文件结构标准。
Lean 提供多种代码检查器，以及用于定义自定义检查器和从中提取度量的框架。

对于独立处理小问题的用户，{ref "linters-editor"}[代码检查器]有助于尽早发现错误。
对于较大问题或团队合作，配置不同的{ref "linting-workflows"}[代码检查工作流]可以改善协作。
随着项目需求演进，甚至可能需要编写{ref "implementing-linters"}[自定义代码检查器]。

# 代码检查器与警告
%%%
file := "Linters-and-Warnings"
tag := "linters-editor"
%%%

交互使用 Lean 时，每个{tech (key := "command")}[命令]经过{tech (key := "Lean elaborator")}[精译]后，都会运行代码检查器。
检查器在单独线程上运行，因此其警告可能在该命令处理完成、精译已进入下一条命令后才到达。

:::paragraph
代码检查警告具有标准格式。
每条警告都以禁用对应检查器的说明结尾。
例如，未使用变量检查器会对以下代码发出警告：
```lean (name := lintWarn)
example :=
  let y := 2
  "hello"
```
警告说明可以使用 {option}`linter.unusedVariables` 禁用它：
```leanOutput lintWarn (severity := Lean.MessageSeverity.warning)
Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
按说明设置选项即可禁用该检查器：
```lean
set_option linter.unusedVariables false in
example :=
  let y := 2
  "hello"
```
:::

:::paragraph
检查器选项可以在三个作用域中设置：

: 命令作用域

  使用 {keywordOf Lean.Parser.Command.set_option}`set_option`{lit}` linter.x ... `{keywordOf Lean.Parser.Command.in}`in`{lit}` ...`，可在单个命令中启用或禁用检查器。

: 节作用域

  {keywordOf Lean.Parser.Command.set_option}`set_option` 命令可以在当前{tech (key := "section scope")}[节作用域]的剩余部分启用或禁用检查器。

: 包作用域

  Lean 选项（包括检查器选项）可以通过{ref "lake-config"}[Lake 配置文件]的 {tomlField Lake.PackageConfig}`leanOptions` 字段设置。
:::

检查器被组织为{deftech (key := "linter sets")}_检查器集合_。
一个选项就能同时启用集合内所有检查器。
一个检查器可以属于任意多个集合，任一所属集合启用时，它就会启用。

某个检查器是否启用由多个选项共同决定。
尽管每个选项都有默认值，Lean 仍会记录它是否被显式设置。
如果检查器自己的选项已设置，则使用该值。
若其自身选项未设置，但 {option}`linter.all` 已设置，则使用后者的值。
若自身选项和 {option}`linter.all` 都未设置，则在默认值为 {name}`true` 或任一包含它的检查器集合被显式启用时，启用该检查器。

这种优先级安排有几个结果。
首先，检查器集合只能启用检查器，不能禁用它们。
将集合的选项设为 {lean}`false` 没有效果。
其次，无论将 {option}`linter.all` 设为 {name}`true` 还是 {name}`false`，它都优先于所有检查器集合。
{option}`linter.all` 也优先于检查器选项的默认值，但不优先于显式设置的值。

{zhOptionDocsFrom linter.all}

{zhOptionDocsFrom linter.extra}

{zhOptionDocsFrom linter.coreInternal}

# 代码检查工作流
%%%
file := "Linting-Workflows"
tag := "linting-workflows"
%%%

除在模块开发期间对各个命令提供反馈外，代码检查器也可以应用于包级别。
模块精译时，检查警告会保存在其{tech (key := ".olean files")}[`.olean` 文件]中，以供重放。
对包进行代码检查，除收集这些交互结果外，还能运行{deftech (key := "environment linters")}_环境代码检查器_；它们报告导入一组模块后所得环境中的潜在问题，而非源文件本身的问题。

## 代码检查器的种类
%%%
file := "Kinds-of-Linters"
tag := "kinds-of-linters"
%%%

检查器在两种上下文中运行：
: 交互式代码检查器

  检查单个 Lean 文件时，在 Lean 精译器和语言服务器的上下文中运行。
  启用对应选项后，Lean 会调用这些检查器。

: 环境代码检查器

  在一组模块构建完成后，于导入这些模块所得的环境中运行。
  环境检查器仅由 {lake}`lint` 调用。

:::paragraph
交互式代码检查器分为三类：

: 命令检查器

  对每个顶层命令运行一次。

: 模块检查器

  在模块末尾运行。

: 有状态检查器

  有状态检查器是一类特殊的命令检查器，可以在相邻命令之间修改共享状态。
  它们可以检查文件结构等非局部不变量，同时在整个文件精译完毕前就提供反馈。
:::


## 运行 `lake lint`
%%%
file := "Running--lake-lint"
tag := "running-lake-lint"
%%%

通过 {lake}`lint` 进行检查时，可以调用当前项目的{tech (key := "lint driver")}[代码检查驱动程序]、Lake 的内置检查支持，或同时使用二者。
本章介绍的是内置检查器；驱动程序则用于运行不符合这一范式的额外检查工具。
当 Lake 配置中的 {tomlField Lake.PackageConfig}`builtinLint` 为 {lean}`true`，或向 {lake}`lint` 传入 {lakeOpt}`--builtin-lint` 或 {lakeOpt}`--builtin-only` 命令行选项时，会进行内置检查。

{lakeOptDef option}`--linters` 和 {lakeOptDef option}`--lint-only` 接受以逗号分隔的检查器选项名称列表。
{lakeOpt}`--linters` 设置指定选项；{lakeOpt}`--lint-only` 还会禁用所有其他检查器。
列表中的 `-` 前缀禁用该检查器，开头的句点是 `linter.` 的缩写，因此 `.XYZ` 等价于 `linter.XYZ`。
后面的条目优先于前面的条目。
位置模块实参将内置检查限制到指定模块；否则，检查从所有默认目标的模块根开始。
{lakeOptDef flag}`--record-exceptions` 标志会向文件添加 {keywordOf Lean.Parser.Command.set_option}`set_option` 命令以抑制警告。


## 环境检查器与导入层次
%%%
file := "Environment-Linters-and-the-Import-Hierarchy"
tag := "env-linters-imports"
%%%

环境检查器通常由两个模块组成。
一个模块定义检查器选项；每个要由此检查器检查的模块都必须导入它。
未传递导入该选项的模块不会被检查。
这样各模块就可以按需覆盖选项值。
另一个模块定义检查器本身；只有发起检查的根模块需要公开导入它。
环境检查器仅在被根模块传递导入时运行，但它可以检查自己导入的模块中的代码。
仅检查与根模块共享前缀的模块。

## 代码质量度量
%%%
file := "Code-Quality-Metrics"
tag := "code-quality-metrics"
%%%

除发出警告外，检查器还可以保存{deftech (key := "code quality metrics")}_代码质量度量_，即与模块或特定声明关联的具名值。
值可以是 {name}`Float`，也可以是从 {name}`String` 到 {name}`Float` 的映射；同一模块或声明可以关联任意多个具有同一名称的值。
这些关联称为{deftech (key := "code quality metric entry")}_条目_。

每个检查器已经隐式地是一项度量。
度量名称为检查器选项名，度量值为该检查器在给定模块中发出警告的次数。

代码质量度量以 JSON 格式输出，可由任意脚本处理。
例如，可以据此跟踪代码库的检查警告数随时间的变化，或确保一次修改没有引入新的检查问题。
自定义度量还可以跟踪每个 {tactic}`simp` 引理的使用次数等信息，从而获得仅检查代码本身无法直接得到的见解。

:::paragraph
以 {lakeOpt}`--code-quality` 标志运行 {lake}`lint` 时，会将度量条目的 JSON 表示以 JSON 对象序列输出到标准输出。
{tech (key := "lint driver")}[代码检查驱动程序]会被跳过。
每个条目是包含三个字段的对象：

* `name` 包含度量名称；
* `value` 包含度量值，是只有一个字段的对象，键名决定该字段的解释方式；
* `source` 包含该度量保存时对应的位置，也是只有一个字段的对象。

度量值要么包含数值键 `scalar`，要么包含键 `dict`，后者的值为将任意字符串映射到数字的对象。
来源要么是键 `module`，对应将 `name` 映射到字符串的对象；要么是键 `declaration`，对应将 `module` 和 `name` 映射到字符串的对象。
JSON 输出可能包含换行，应使用真正的 JSON 解析器解析。
:::

:::example "度量条目的 JSON 表示"
归属于模块的标量值，重放检查警告时会产生此类条目：
```codeQualityEntries
{"name": "linter.unusedVariables",
 "source": {"module": {"name": "Proj.Basic"}},
 "value": {"scalar": {"value": 2}}}
```

归属于声明的字典值，由检查器记录：
```codeQualityEntries
{"name": "linter.simpUsage.lemmas",
 "source": {"declaration": {"module": "Proj.Lemmas", "name": "t3"}},
 "value": {"dict": {"dictionary": {"Nat.add_zero": 1, "Nat.zero_add": 1}}}}
```
:::



以 {lakeOpt}`--code-quality` 标志运行 {lake}`lint` 时，还会执行 Lake 配置的 {tomlField Lake.PackageConfig}`checks` 字段及命令行 {lakeOpt}`--checks` 选项指定的代码质量检查。
配置字段和命令行选项都指向模块；会运行所有指定模块中全部{ref "package-code-quality-checks"}[已注册的检查]。
这些检查是 Lean 函数，可添加需要超出单个命令或模块状态的信息才能计算的额外度量。
这些检查可以用统一机制，取代 CI 和报告中的各种特设数据收集机制。


::::example "将现有警告用作度量" (tag := "example-warnings-as-metrics")
:::lakeSession
```toml -show
name = "metrics"
defaultTargets = ["Code"]

[[lean_lib]]
name = "Code"
```
无需额外配置，以 {lakeOpt}`--code-quality` 标志对项目运行 {lake}`lint`，就会为每个检查器返回一项度量，跟踪其在各模块中发出警告的次数。
此模块包含两条未使用变量警告：
```lean (file := "Code/Basic.lean")
module

public def first (x y : Nat) : Nat := x

public def second (x y : Nat) : Nat := y
```
```lean (file := "Code.lean")
module
public import Code.Basic
```
```lakeCmd "lake build" +ignoreOutput -show
```
对包执行检查会显示以下消息：
```lakeCmd "lake lint --builtin-only" +error
-- Text linter diagnostics in Code.Basic:
⟨project⟩/Code/Basic.lean:3:20: warning: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⟨project⟩/Code/Basic.lean:5:19: warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-- No environment linters were run for Code.
```
模块 `Code.Basic` 本身带有两条 {option}`linter.unusedVariables` 记录：
```lakeCmd "lake lint --code-quality"
{"value": {"scalar": {"value": 2}},
 "source": {"module": {"name": "Code.Basic"}},
 "name": "linter.unusedVariables"}
```
:::
::::

# 实现代码检查器
%%%
file := "Implementing-Linters"
tag := "implementing-linters"
%%%

许多大型项目需要自定义检查器来落实项目特定标准。
定义新检查器的步骤是：
1. 注册控制新检查器的选项。
2. 确定它应是命令检查器、模块检查器、有状态检查器还是环境检查器。
3. 决定需要保存哪些代码质量度量（若有）。
4. 实现所需的包级代码质量检查。

定义检查器首先要注册控制它的选项。
使用 {keywordOf Lean.Option.registerOption}`register_option` 注册选项，需要提供新选项的默认值和说明。
默认值决定检查器是否默认启用。
在模块中，该选项应公开并位于{tech (key := "meta phase")}[元阶段]。
检查器应由 {name}`Bool` 选项控制。
用于配置检查器的其他选项（例如阈值）可以添加到检查器自身的命名空间中。

检查器应使用 {name Lean.Linter.logLint}`logLint` 或 {name}`Lean.Linter.logLintIf` 显示检查警告，而不是使用 {name}`Lean.logWarning`。
这些辅助函数确保检查警告格式统一。
它们还会在内部将消息标记为检查器消息，使 Lake 和 Lean 将其包含在 {lake}`lint` 的输出中。
{name Lean.Linter.logLintIf}`logLintIf` 还会正确解析检查器选项值，考虑 {option}`linter.all` 和检查器集合。
{name Lean.Linter.logLint}`logLint` 应用于已经检查过该检查器选项的上下文。

一些检查器在准备记录警告前，就需要检查自己是否启用。
例如，计算开销大且不产生有用代码质量度量的检查器，可能希望在未启用时尽早退出。
这些检查器应使用正确考虑检查器集合及 {option}`linter.all` 的辅助函数判断是否启用。
具体做法是先调用 {name}`Lean.Linter.getLinterOptions`，再用 {name}`Lean.Linter.getLinterValue` 检查选项值。

最后，每个检查器实现都应使用 {name}`Lean.withSetOptionIn` 包裹针对具体命令的检查。
缺少这个包装时，针对被检查命令设置的 {keywordOf Lean.Parser.Command.set_option}`set_option`{lit}` ... `{keywordOf Lean.Parser.Command.in}`in`{lit}` ...` 将不会被考虑。
命令和有状态检查器应包装整个实现，模块检查器则应包装对单个命令的操作。


{zhdocstringFrom Lean.Linter.logLintIf}

{zhdocstringFrom Lean.Linter.logLint +allowMissing}

{zhdocstringFrom Lean.Linter.getLinterValue +allowMissing}

{zhdocstringFrom Lean.Linter.getLinterOptions +allowMissing}

{zhdocstringFrom Lean.withSetOptionIn}

## 命令检查器
%%%
file := "Command-Linters"
tag := "command-linters"
%%%

:::leanSection
```lean -show
open Lean Elab Command
```

命令检查器是最简单的检查器形式。
命令检查器是 {name Lean.Elab.Command.Linter}`Lean.Elab.Command.Linter` 类型的值；该结构体有一个类型为 {lean}`Syntax → CommandElabM Unit` 的 {name Lean.Elab.Command.Linter.run}`run` 字段。
{name}`addLinter` 保存一个新命令检查器，必须在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中运行。
在{tech (key := "module")}[模块]中使用时，{keywordOf Lean.Parser.Command.initialize}`initialize` 块必须位于{tech (key := "meta phase")}[元阶段]。

每条命令精译后都会运行命令检查器，与文件剩余部分的精译并发执行。
检查器的 {name Lean.Elab.Command.Linter.run}`run` 函数应用于命令语法，所在上下文可访问命令的信息树。
检查器对环境所作的修改会被丢弃，但新消息日志条目、代码操作及{ref "code-quality-metrics"}[代码质量度量]会被保存。
:::


{zhdocstringFrom Lean.Elab.Command.Linter +allowMissing}

{zhdocstringFrom Lean.Elab.Command.addLinter +allowMissing}


::::example "统计策略数量" (tag := "example-linter-enabled")
此自定义检查器在命令的策略数超过可配置阈值时发出警告。
它处理命令的信息树，记录具有策略信息且种类为策略种类的{tech (key := "original")}[原始]语法的唯一开始位置，以找到策略。
由于宏展开步骤及同一策略的重复执行都会保存策略信息，因此需要去重。
检查器未启用时会尽早退出，而不是到准备记录消息时才作决定。


:::leanModules (moduleRoot := Steps)
```leanModule (moduleName := Steps.Linter)
module
public meta import Lean.Linter.Basic
public meta import Lean.Elab.InfoTree.Util

open Lean Elab Command
open Std (HashSet)

meta section

public register_option linter.tacticCount : Bool := {
  defValue := true
  descr := "warn when a command runs many tactics"
}

public register_option linter.tacticCount.max : Nat := {
  defValue := 100
  descr := "the number of tactics a command may run before \
    `linter.tacticCount` warns"
}

 open Parser in
/--
Whether `kind` is the syntax kind of a tactic, as opposed to a tactic
sequence or block.
-/
def isTacticKind (env : Environment) (kind : SyntaxNodeKind) : Bool :=
  match (parserExtension.getState env).categories.find? `tactic with
  | some category => category.kinds.contains kind
  | none => false

/--
The number of distinct tactics from the source file that were run while
elaborating `tree`.
-/
def countTactics (env : Environment) (tree : InfoTree) : Nat :=
  let positions : HashSet String.Pos.Raw :=
    tree.foldInfo (init := {}) fun _ info positions =>
      match info with
      | .ofTacticInfo ti =>
        match ti.stx.getHeadInfo, ti.stx.getPos? with
        | .original .., some pos =>
          if isTacticKind env ti.stx.getKind then
            positions.insert pos
          else
            positions
        | _, _ => positions
      | _ => positions
  positions.size

open Linter in
/--
Warns when a command runs more than `linter.tacticCount.max` tactics.
-/
def tacticCount : Linter where
  run := withSetOptionIn fun stx => do
    -- Don't compute the result if it will never be shown
    unless getLinterValue linter.tacticCount (← getLinterOptions) do
      return
    let env ← getEnv
    let count :=
      (← getInfoState).trees.foldl (init := 0) fun n t =>
        n + countTactics env t
    let limit := linter.tacticCount.max.get (← getOptions)
    if count > limit then
      Linter.logLint linter.tacticCount stx m!"this command runs \
        {count} tactics, more than {limit}"

initialize addLinter tacticCount
```

此模块展示检查器确实运行，并且遵守局部设置的选项：
```leanModule (moduleName := Steps.Test) (name := tooMany)
module
import Steps.Linter

set_option linter.tacticCount.max 4

theorem short (n : Nat) : n + 0 = n := by
  simp

theorem long (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add]
    rw [ih]
    rfl

set_option linter.tacticCount false in
theorem silenced (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add]
    rw [ih]
    rfl
```
```leanOutput tooMany
this command runs 5 tactics, more than 4

Note: This linter can be disabled with `set_option linter.tacticCount false`
```
:::
::::


## 模块检查器
%%%
file := "Module-Linters"
tag := "module-linters"
%%%
:::leanSection
```lean -show
open Lean Elab Command
```
模块检查器在每个模块精译完成后运行。
模块检查器的类型为 {name}`Lean.Elab.Command.ModuleLinter`；该结构体具有类型为 {lean}`Array Syntax → CommandElabM Unit` 的 {name ModuleLinter.run}`run` 函数。
调用时会将该模块中的所有顶层命令传给此函数。
由于整个模块精译完毕后才调用检查器，警告要到精译末尾才会出现。

与命令检查器不同，模块检查器不能访问命令的信息树，也不能保存代码操作。
不过，它们可以访问模块的最终环境。
因此，它们主要适合语法检查。
若全文件检查需要信息树，应考虑使用{ref "stateful-linters"}[有状态检查器]。

{name}`addModuleLinter` 保存一个新模块检查器，必须在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中运行。
在{tech (key := "module")}[模块]中使用时，{keywordOf Lean.Parser.Command.initialize}`initialize` 块必须位于{tech (key := "meta phase")}[元阶段]。
:::


{zhdocstringFrom Lean.Elab.Command.ModuleLinter +allowMissing}

{zhdocstringFrom Lean.Elab.Command.addModuleLinter +allowMissing}

:::::example "限制声明数量" (tag := "example-module-linter")

::::leanModules (moduleRoot := Limit)
模块 `Limit.Linter` 包含一个模块检查器，在模块声明过多时发出警告。
上限由选项值决定。
虽然警告附着于首个超出限制的声明，但由于由模块检查器实现，它要到整个文件精译完成后才会出现。
```leanModule (moduleName := Limit.Linter)
module
public meta import Lean.Linter.Basic

open Lean Elab Command

meta section

public register_option linter.declarationLimit : Bool := {
  defValue := true
  descr := "warn when a file contains more declarations than \
    `linter.declarationLimit.max`"
}

public register_option linter.declarationLimit.max : Nat := {
  defValue := 200
  descr := "the number of declarations that a file may contain"
}

/-- Warns at the first declaration past the limit. -/
def declarationLimit : ModuleLinter where
  run cmds := do
    let limit := linter.declarationLimit.max.get (← getOptions)
    let decls := cmds.filter (·.isOfKind ``Parser.Command.declaration)
    if h : limit < decls.size then
      Linter.logLintIf linter.declarationLimit decls[limit]
        m!"this file contains {decls.size} declarations, more than \
          {limit}"

initialize addModuleLinter declarationLimit
```
此模块将最大声明数设为 {lean}`2`：
```leanModule (moduleName := Limit.Test) (name := limitTest)
module
import Limit.Linter

set_option linter.declarationLimit.max 2

def a := 1
def b := 2
def c := 3
```
构建文件时会显示检查警告：
:::TODO
下一个代码块本应使用 `leanOutput limitTest`。
该行为目前存在问题，见 <https://github.com/leanprover/subverso/issues/245>。
:::
```
this file contains 3 declarations, more than 2

Note: This linter can be disabled with `set_option linter.declarationLimit false`
```
::::
:::::



## 有状态检查器
%%%
file := "Stateful-Linters"
tag := "stateful-linters"
%%%
:::leanSection
```lean -show
open Lean Elab Command
```

与命令检查器一样，每条命令精译后都会调用有状态检查器。
它们同样可以访问命令的信息树与环境。
不同之处在于，它们并不独立于此前命令的检查结果。
相反，它们具有在整个模块中累积的状态。
因此可以检查非局部性质，并在违规发生后立即发出警告，而无需等待文件剩余部分处理完毕。

此外，有状态检查器分为“早期”和“晚期”两个阶段运行。
命令精译完成后，先运行所有有状态检查器的早期阶段，再运行所有晚期阶段。
这样就可以协作：早期阶段可以计算多个检查器的晚期阶段要使用的数据。
早期阶段是可选的，许多有用的有状态检查器并没有早期阶段。
通过注册检查器返回的句柄，有状态检查器不仅可以读取自己的已保存状态，也可以读取其他任何有状态检查器的状态。

有状态检查器通过 {name}`Lean.Elab.Command.registerStatefulLinter` 注册。
与其他检查器注册函数一样，必须在{tech (key := "meta phase")}[元阶段]的 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中调用。
检查器必须公开。
注册函数以早期和晚期阶段的实现为实参。
与其他检查器注册操作不同，该注册会返回一个有用的值，即可用于读取检查器状态的句柄。
{name}`StatefulLinter` 和 {name}`registerStatefulLinter` 都接受两个类型参数：第一个是在命令间传递的状态，第二个是早期阶段计算的数据。

有状态检查器也会在模块末尾运行。
由于它们已能从各命令中收集信息，因此可以提供模块检查器无法提供的反馈。
:::

{zhdocstringFrom Lean.Elab.Command.StatefulLinter}

{zhdocstringFrom Lean.Elab.Command.registerStatefulLinter}

{zhdocstringFrom Lean.Elab.Command.PrevStateFn}

{zhdocstringFrom Lean.Elab.Command.PreStateFn}

::::example "落实文件布局" (tag := "example-file-layout")
:::leanModules (moduleRoot := Layout)

此有状态检查器检查模块是否具有指定结构。
模块应先有模块文档字符串，再设置所需选项，最后包含声明。
检查器的状态是跟踪此顺序的简单状态机。
每当遇到命令，它就局部检查不变量并更新状态。
```leanModule (moduleName := Layout.Linter)
module
public meta import Lean.Linter.Basic

open Lean Elab Command

meta section

public register_option linter.fileLayout : Bool := {
  defValue := true
  descr := "warn when commands appear out of the expected order in a \
    file"
}

public inductive Region where
  | moduleDoc
  | setup
  | body
deriving Inhabited, Ord, DecidableEq

instance : LT Region := ltOfOrd

def Region.describe : Region → String
  | .moduleDoc => "module docstring"
  | .setup => "setup command"
  | .body => "declaration"

open Parser in
def Region.ofCommand (stx : Syntax) : Option Region :=
  if stx.isOfKind ``Command.moduleDoc then
    some .moduleDoc
  else if stx.isOfKind ``Command.open ||
          stx.isOfKind ``Command.set_option ||
          stx.isOfKind ``Command.universe ||
          stx.isOfKind ``Command.variable then
    some .setup
  else if stx.isOfKind ``Command.declaration then
    some .body
  else
    none

public structure LayoutState where
  current : Option Region := none
deriving Inhabited

def checkLayout (stx : Syntax) (st : LayoutState) :
    CommandElabM LayoutState := do
  let some region := Region.ofCommand stx | return st
  if let some current := st.current then
    if region < current then
      Linter.logLintIf linter.fileLayout stx
        m!"{region.describe} after {current.describe}"
  else if region != .moduleDoc then
    Linter.logLintIf linter.fileLayout stx
      m!"the first command in a file should be a module docstring"
  let current := st.current.getD region
  return {
    current := some (if region > current then region else current)
  }

public initialize fileLayoutLinter : StatefulLinter LayoutState Unit ←
  registerStatefulLinter {}
    (post := fun stx st _ _ _ => withSetOptionIn (checkLayout · st) stx)
```
此文件有三处违规：开头缺少模块文档注释，在声明后设置选项，以及在命令后放置模块文档注释：
```leanModule (moduleName := Layout.Test) (name := ordering)
module
import Layout.Linter

open Nat

/-! This module docstring comes too late. -/

def x := 1

set_option autoImplicit false

theorem y : x = 1 := rfl
```
```leanOutput ordering
the first command in a file should be a module docstring

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
```leanOutput ordering
setup command after declaration

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
```leanOutput ordering
module docstring after setup command

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
:::
::::



## 环境检查器
%%%
file := "Environment-Linters"
tag := "environment-linters"
%%%

项目构建完成后，若启用了 {lakeOpt}`--builtin-lint`，或在 Lake 配置中启用了 {tomlField Lake.PackageConfig}`builtinLint` 字段，{lake}`lint` 就会运行环境检查器。
Lake 构建项目后，其内置检查器会遍历各库目标的根模块，导入模块，再对所得环境运行所配置的环境检查器。
每个环境检查器由测试过程及成功、失败消息组成。
与命令和模块检查器不同，环境检查器不需要被待检查模块传递导入。

与其他检查器一样，环境检查器由选项控制。
与检查器本身不同，选项声明必须被传递导入。
控制环境检查器的选项会被特别注册，并在精译期间保存其值；因此检查器能从导入环境中取得这些值，包括使用 {keywordOf Lean.Parser.Command.in}`in` 局部设置的值。

定义环境检查器的步骤如下：
1. 在一个模块中，于{tech (key := "meta phase")}[元阶段]注册控制该检查器的公开选项。
   在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中运行 {name Lean.Linter.addEnvLinterOption}`addEnvLinterOption`，指示 Lean 在精译期间跟踪该选项值。
   每个需要使用此检查器的模块都应传递导入该模块。
   初始化块必须在元阶段运行。
2. 在第二个模块中定义检查器本身。
   使用 {attr}`builtin_env_linter` 属性将检查器与选项关联。
   待检查模块无需导入该模块，但被检查目标的根模块必须传递导入它。

:::syntax attr (title := "环境代码检查器")
```grammar
builtin_env_linter $_:ident
```
注册由指定选项名控制的环境检查器。
:::

{zhdocstringFrom Lean.Linter.EnvLinter.EnvLinter}

{zhdocstringFrom Lean.Linter.addEnvLinterOption +allowMissing}


::::example "API 完整性检查器" (tag := "example-env-linter")
一般来说，提供 `get!` 函数的数据结构也应提供 `get?` 和 `getD`。
不过，这些函数不必在同一模块中定义。
环境检查器可以确保：项目中任何定义了这些名称之一的命名空间，也定义了其余名称。

:::lakeSession
```toml -show
name = "envlint"
defaultTargets = ["Data"]

[[lean_lib]]
name = "Lints"

[[lean_lib]]
name = "Data"
```
检查器本身由两个模块组成：`Lints.Options` 定义控制它的选项，应由整个项目导入；`Lints.GetVariants` 则只需由根模块导入：
```lean (file := "Lints/Options.lean")
module
public meta import Lean.Linter.Init

open Lean

meta section

public register_option linter.envLinter.getVariants : Bool := {
  defValue := true
  descr := "warn when a namespace defines some but not all of `get!`, \
    `get?`, and `getD`"
}

initialize Linter.addEnvLinterOption linter.envLinter.getVariants
```
```lean (file := "Lints/GetVariants.lean")
module
public import Lints.Options
public meta import Lean.Linter.EnvLinter.Basic

open Lean Linter EnvLinter

meta section

/-- The variants that are expected to be defined together. -/
def getVariants : List String := ["get!", "get?", "getD"]

@[builtin_env_linter linter.envLinter.getVariants]
public def getVariantsLinter : EnvLinter where
  test declName := do
    let .str ns variant := declName | return none
    unless getVariants.contains variant do return none
    let env ← getEnv
    let missing := getVariants.filter fun v => !env.contains (.str ns v)
    if missing.isEmpty then return none
    let missing := missing.map fun v => m!"`{Name.str ns v}`"
    return some m!"`{declName}` is defined, but \
      {MessageData.andList missing} \
      {if missing.length == 1 then "is" else "are"} not"
  noErrorsFound := "Every namespace defines all of `get!`, `get?`, and \
    `getD`."
  errorsFound := "THE FOLLOWING NAMESPACES DEFINE ONLY SOME OF `get!`, \
    `get?`, AND `getD`:"
```
库本身包含多种数据结构，实现在多个模块中：
```lean (file := "Data/Stack.lean")
module
import Lints.Options

public structure Stack where
  items : Array Nat

public def Stack.get! (s : Stack) (i : Nat) : Nat := s.items[i]!
```
```lean (file := "Data/Queue.lean")
module
import Lints.Options

public structure Queue where
  items : Array Nat

public def Queue.get! (q : Queue) (i : Nat) : Nat := q.items[i]!
```
```lean (file := "Data/Safe.lean")
module
import Lints.Options
public import Data.Stack

public def Stack.get? (s : Stack) (i : Nat) : Option Nat := s.items[i]?

public def Stack.getD (s : Stack) (i : Nat) (default : Nat) : Nat :=
  s.items.getD i default
```
根模块导入全部实现模块以及检查器：
```lean (file := "Data.lean")
module
public import Lints.GetVariants
public import Data.Stack
public import Data.Queue
public import Data.Safe
```
```lakeCmd "lake build" +ignoreOutput -show
```
对包执行代码检查会返回以下警告：
```lakeCmd "lake lint --builtin-only" +error
-- Found 1 error in 12 declarations (plus 24 automatically generated ones) in Data with 1 linters

/- The `linter.envLinter.getVariants` linter reports:
THE FOLLOWING NAMESPACES DEFINE ONLY SOME OF `get!`, `get?`, AND `getD`: -/
-- Data.Queue
./Data/Queue.lean:7:1: error: Queue.get! `Queue.get!` is defined, but `Queue.get?` and `Queue.getD` are not
```
:::
::::

## 记录代码质量条目
%%%
file := "Recording-Code-Quality-Entries"
tag := "recording-code-quality"
%%%

每个保存的值称为一个 {name Lean.Linter.CodeQuality.Entry}`Entry`。
通过 {name}`Lean.Linter.logCodeQualityEntry` 保存它们。
类似于 {name Lean.Linter.logLintIf}`logLintIf`，{name Lean.Linter.logCodeQualityEntryIf}`logCodeQualityEntryIf` 接受检查器选项名，在对应检查器启用时记录条目，并考虑检查器集合、{option}`linter.all` 和 {lakeOpt}`--lint-only` 选项。

代码质量条目关联度量名称、来源和值。
度量名称可以是任意字符串，但为避免冲突，通常应以检查器选项名作为前缀。
仅使用检查器名称可能与 Lake 自动输出为代码质量度量的检查警告计数冲突。
辅助函数 {name}`Lean.Linter.findCodeQualitySource` 和 {name}`Lean.Linter.findCodeQualitySource?` 从文件解析出的语法确定 {name Lean.Linter.CodeQuality.Source}`Source`；前者找不到声明时会回退为当前模块。
来源只能是模块或声明，无法将条目归属于更小的单位。
不过，可以使用字典值编码更细的结构。
值可以是浮点值，或从字符串到浮点数的字典。
计数等整数度量也应使用浮点数。

对给定来源，同一度量名称可以记录任意多次。
使用方负责适当地汇总度量。

{zhdocstringFrom Lean.Linter.CodeQuality.Entry +allowMissing}

{zhdocstringFrom Lean.Linter.CodeQuality.Source +allowMissing}

{zhdocstringFrom Lean.Linter.CodeQuality.Value +allowMissing}

{zhdocstringFrom Lean.Linter.logCodeQualityEntry}

{zhdocstringFrom Lean.Linter.logCodeQualityEntryIf}

{zhdocstringFrom Lean.Linter.findMatchingDecl?}

{zhdocstringFrom Lean.Linter.findCodeQualitySource}

{zhdocstringFrom Lean.Linter.findCodeQualitySource?}


::::example "度量 simp 引理的使用" (tag := "example-simp-metrics")
虽然检查器主要用于警告潜在的问题代码，也可以仅收集度量，而由后续检查发出警告。
本示例展示一个记录显式 {tactic}`simp` 引理使用度量的命令检查器，可据此发现库中可能缺失的 {attrs}`@[simp]` 标注。
这些度量随后由一个小型 Lean 程序收集和汇总。

:::lakeSession
```toml
name = "simpstats"
defaultTargets = ["Code", "simp-stats"]

[[lean_lib]]
name = "Lints"

[[lean_lib]]
name = "Code"

[[lean_exe]]
name = "simp-stats"
root = "SimpStats"
```

检查器首先使用 {name}`simpLemmaStarts` 遍历命令语法，找出每个显式 {tactic}`simp` 引理的源码位置。
由于 {tactic}`simp` 引理列表允许将引理应用于实参，因此使用开始位置来标识引理。
随后 {name}`simpUsage` 检查器本身利用信息树，找到从这些位置开始的常量引用，记录一个字典度量，将完全解析后的名称映射为出现次数。

```lean (file := "Lints/SimpUsage.lean")
module
public meta import Lean.Linter.Basic
public meta import Lean.Linter.Util

open Lean Elab Command Linter
open Std (HashSet)

meta section

public register_option linter.simpUsage : Bool := {
  defValue := true
  descr := "record which lemmas are passed to `simp` as code quality \
    metrics"
}

partial def simpLemmaStarts (stx : Syntax) :
    Array String.Pos.Raw := Id.run do
  let mut starts := #[]
  if stx.isOfKind ``Parser.Tactic.simpLemma then
    -- The lemma itself follows the optional `↓`/`↑` and `←` modifiers.
    if let some pos := stx[2].getPos? then starts := starts.push pos
  for arg in stx.getArgs do
    starts := starts ++ simpLemmaStarts arg
  return starts

def simpUsage : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.simpUsage (← getLinterOptions) do return
    let starts := simpLemmaStarts stx
    if starts.isEmpty then return
    -- Each lemma occurrence is identified by its position, since the
    -- info tree can contain several nodes for the same syntax.
    let mut found : HashSet (String.Pos.Raw × Name) := {}
    for tree in (← getInfoState).trees do
      found := tree.foldInfo (init := found) fun _ info found =>
        match info with
        | .ofTermInfo ti =>
          match ti.expr.constName?, ti.stx.getRange? with
          | some n, some r =>
            if starts.contains r.start then
              found.insert (r.start, n)
            else found
          | _, _ => found
        | _ => found
    let mut counts : Std.TreeMap String Float := {}
    for (_, n) in found do
      counts := counts.alter n.toString fun c => some (c.getD 0.0 + 1)
    unless counts.isEmpty do
      Linter.logCodeQualityEntryIf linter.simpUsage {
        name := "linter.simpUsage.lemmas"
        source := ← Linter.findCodeQualitySource stx
        value := .dict counts
      }

initialize addLinter simpUsage
```

此脚本获取项目收集的度量并进行汇总。
函数 {name}`parseEntries` 解析 JSON 值序列，{name}`main` 则处理结果，并按使用次数排序 simp 引理。
```lean (file := "SimpStats.lean")
import Lean.Data.Json
open Lean

/--
Parses a sequence of JSON values, as printed by
`lake lint --code-quality`.
-/
def parseEntries (s : String) : Except String (Array Json) :=
  let p : Std.Internal.Parsec.String.Parser (Array Json) := do
    Std.Internal.Parsec.String.ws
    let entries ← Std.Internal.Parsec.many Json.Parser.anyCore
    Std.Internal.Parsec.eof
    return entries
  p.run s

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let entries ← IO.ofExcept (parseEntries input)
  let mut totals : Std.TreeMap String Float := {}
  for entry in entries do
    let .ok "linter.simpUsage.lemmas" := entry.getObjValAs? String "name"
      | continue
    let .ok (.obj dict) := do
      let v ← entry.getObjVal? "value"
      let d ← v.getObjVal? "dict"
      d.getObjVal? "dictionary"
      | continue
    for (lemma, count) in dict do
      let .ok n := count.getNum? | continue
      totals := totals.insert lemma (totals.getD lemma 0 + n.toFloat)
  let sorted := totals.toArray.qsort fun (_, a) (_, b) => a > b
  for (lemma, n) in sorted do
    IO.println s!"{n.toUInt64} {lemma}"
  return 0
```

项目本身包含四个引理 {name}`t1` 到 {name}`t4`，分布在两个模块中：
```lean (file := "Code.lean")
module
public import Code.Lemmas
import Lints.SimpUsage

public theorem t4 (n : Nat) : n * 1 = n := by
  simp [Nat.mul_one]
```
```lean (file := "Code/Lemmas.lean")
module
import Lints.SimpUsage

public theorem t1 (n : Nat) : n + 0 = n := by
  simp [Nat.add_zero]

public theorem t2 (n m : Nat) : n + m = m + n := by
  simp [Nat.add_comm]

public theorem t3 (n : Nat) : 0 + n + 0 = n := by
  simp [Nat.add_zero, Nat.zero_add]
```

```lakeCmd "lake build" +ignoreOutput -show
```

构建后，代码质量度量列出显式 {tactic}`simp` 引理的使用情况，排序脚本对其进行汇总：
```lakeCmd "lake lint --code-quality"
{"value": {"dict": {"dictionary": {"Nat.add_zero": 1}}},
 "source": {"declaration": {"name": "t1", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.add_comm": 1}}},
 "source": {"declaration": {"name": "t2", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.zero_add": 1, "Nat.add_zero": 1}}},
 "source": {"declaration": {"name": "t3", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.mul_one": 1}}},
 "source": {"declaration": {"name": "t4", "module": "Code"}},
 "name": "linter.simpUsage.lemmas"}
```
```lakeCmd "lake lint --code-quality | lake -q exe simp-stats"
2 Nat.add_zero
1 Nat.zero_add
1 Nat.add_comm
1 Nat.mul_one
```
:::
::::


## 包级代码质量检查
%%%
file := "Package-Code-Quality-Checks"
tag := "package-code-quality-checks"
%%%

包级代码质量检查可以度量整个库或可执行{tech (key := "target")}[目标]的性质，而不是孤立地度量单个声明或模块。
它们在 Lake 配置文件或命令行中配置，不需要被待度量的代码导入。
包级检查输出代码质量条目。
由于作为 Lean 和 Lake 的一部分运行，它们可以访问 Lean 的元编程功能，无需各自构建特设机制。
用于落实包级限制或不变量的脚本只需解析 JSON，而不必以复杂方式与 Lean 代码交互。

将定义检查的模块加入 Lake 配置中的 {tomlField Lake.PackageConfig}`checks` 字段，或使用 Lake 的 {lakeOpt}`--checks` 选项，即可启用包级检查。
在所配置的检查模块中，每个检查都是 `meta` 阶段中类型为 {name Lean.Linter.CodeQuality.PackageCheck}`PackageCheck` 的公开定义，并使用 {attr}`package_code_quality_check` 属性注册。
给定 {name Lean.Linter.CodeQuality.PackageCheckContext}`PackageCheckContext` 类型的实参，包级检查可以使用 {name Lean.MetaM}`MetaM` 的任意功能计算代码质量条目数组。
上下文指定库或可执行文件的{tech (key := "module roots")}[根模块]以及{tech (key := "workspace")}[工作区]的源码搜索路径。
包级检查不应通过抛出异常来表示包违反不变量或预期性质；应将问题作为条目返回，由数据使用方检查。

只有传入 {lakeOpt}`--code-quality` 或 {lakeOpt}`--checks` 选项时，才会运行启用的检查；否则 {lake}`lint` 不运行它们。
对于每个根模块，全部注册的包级检查会并发运行，结果条目追加到总体质量度量集合中。
通过库的{tech (key := "globs")}[模块匹配模式]字段纳入的模块不被视为根。
即使自定义目标会构建 Lean 代码，也不会纳入检查；非默认的库和可执行目标同样不会纳入。
若在命令行指定模块，则检查这些模块，代替默认目标的根模块。
包级检查抛出的异常会写入标准错误，但不会终止代码检查。
若抛出过任何异常，{lake}`lint` 返回非零退出码。

检查在已导入根模块的环境中运行。
被多个根模块导入的模块可能被包级检查重复检查。
若根模块使用{ref "module-scopes"}[模块系统]，即是一个{tech (key := "module")}[模块]，该环境仅包含公开和服务器信息，私有声明不可见。
若根模块不使用模块系统，私有信息也可见。
每个根模块都在新的环境中检查。

:::syntax attr (title := "包级代码质量检查")
```grammar
package_code_quality_check
```

注册一个包级代码质量检查。
:::

{zhdocstringFrom Lean.Linter.CodeQuality.PackageCheck +allowMissing}

{zhdocstringFrom Lean.Linter.CodeQuality.PackageCheckContext +allowMissing}

::::example "寻找重复定理" (tag := "example-package-check")

由于包级检查可以访问整个库，因此可用于寻找重复定理。
本示例检查有局限：它只找到几乎完全相同的定理，不考虑假设重排或定义展开。
更实际的检查可以使用更细致的相似性度量，报告超过某个相似阈值的定理。

首先将 `Checks` 模块加入包的 {tomlField Lake.PackageConfig}`checks` 字段：
:::lakeSession
```toml
name = "dups"
defaultTargets = ["Code"]
checks = ["Checks"]

[[lean_lib]]
name = "Checks"

[[lean_lib]]
name = "Code"
```

其唯一检查首先计算定理的等价类。
通过检查类型是否为命题来识别定理，并跳过作为其他声明辅助项生成的内部定理。
使用哈希表将非内部定理分成等价类；{lean}`Lean.Expr` 的 {lean}`BEq` 实例及对应的 {lean}`Hashable Lean.Expr` 实例在忽略绑定变量重命名和绑定信息变化的意义下检查相等性。
仅搜索根模块所在包中的模块。
因此，仅假设名称或隐式参数状态不同的定理会被归为一组，假设顺序不同的定理则不会。
确定等价类后，对包含多个元素的每个等价类中的每个元素，添加一个列出整个等价类的度量条目。
```lean (file := "Checks.lean")
module
public meta import Lean.Linter.CodeQuality.Frontend
public meta import Lean.Compiler.ModPkgExt

open Lean Meta Linter CodeQuality

meta section

@[package_code_quality_check]
public def duplicateTheorems : PackageCheck where
  run ctx := do
    let env ← getEnv
    let some rootIdx := env.getModuleIdx? ctx.topLevelModule | return #[]
    let pkg := env.getModulePackageByIdx? rootIdx
    -- Group the theorems of the package's modules by their statements.
    -- Each equivalence class is a dictionary that maps its members'
    -- names to 1.0 to facilitate reporting.
    let mut classes : ExprMap (Std.TreeMap String Float) := {}
    let mut theorems := #[]
    for h : i in 0 ... env.header.moduleData.size do
      unless env.getModulePackageByIdx? i == pkg do continue
      for declName in env.header.moduleData[i].constNames do
        if declName.isInternalDetail then continue
        let some info := env.find? declName | continue
        unless ← isProp info.type do continue
        classes := classes.alter info.type fun dups? =>
          some ((dups?.getD {}).insert declName.toString 1.0)
        let modName := env.header.moduleNames[i]!
        theorems := theorems.push (modName, declName, info.type)
    -- Report each theorem that has duplicates.
    let mut entries := #[]
    for (modName, declName, type) in theorems do
      let some dups := classes[type]? | continue
      if dups.size < 2 then continue
      entries := entries.push {
        name := "duplicateTheorems"
        source := .declaration modName declName
        value := .dict dups
      }
    return entries
```

代码本身包含同一定理的多个重述，其中三个属于同一等价类。
{name}`zero_add'` 和 {name}`add_zero_rev` 的陈述则不同。
```lean (file := "Code/Basic.lean")
module

public theorem add_zero' (n : Nat) : n + 0 = n := rfl

public theorem zero_add' (n : Nat) : 0 + n = n := Nat.zero_add n
```
```lean (file := "Code/Extra.lean")
module
public import Code.Basic

public theorem add_zero'' (m : Nat) : m + 0 = m := rfl

public theorem also_add_zero (k : Nat) : k + 0 = k := add_zero' k

public theorem add_zero_rev (n : Nat) : n = n + 0 := rfl
```
```lean (file := "Code.lean")
module
public import Code.Basic
public import Code.Extra
```
```lakeCmd "lake build Code Checks" +ignoreOutput -show
```
输出中，该定理的三个版本都标注了整个等价类：
```lakeCmd "lake lint --code-quality"
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "add_zero'", "module": "Code.Basic"}},
 "name": "duplicateTheorems"}
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "add_zero''", "module": "Code.Extra"}},
 "name": "duplicateTheorems"}
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "also_add_zero", "module": "Code.Extra"}},
 "name": "duplicateTheorems"}
```
:::
::::
