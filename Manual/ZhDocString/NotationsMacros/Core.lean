/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.NotationsMacros.Core

/--
`MacroM` 单子是宏展开使用的主要单子。它含有生成卫生名称所需的信息，
也是 `macro` 定义所在的单子。

这是一个（相对）纯的单子：它不提供 `IO`，也不能直接访问
`Environment`。因此无法在其中进行任意环境内省；只能使用 `Macro.Methods` 提供的受限查询，
也无法使用 `IO.Ref` 或其他有副作用的操作。若需要更多能力，可以改用 `elab`，并通过
`adaptExpander` 编写宏。
-/
abbrev MacroM := _root_.Lean.MacroM

namespace Macro

/--
若 `stx` 是宏，`expandMacro? stx` 返回 `some stxNew`，其中 `stxNew` 是它的展开结果；
否则返回 `none`。
-/
def expandMacro? (stx : Lean.Syntax) : Lean.MacroM (Option Lean.Syntax) :=
  _root_.Lean.Macro.expandMacro? stx

/-- 向给定的跟踪类添加一条具有给定消息的新跟踪消息。 -/
def trace (clsName : Lean.Name) (msg : String) : Lean.MacroM Unit :=
  _root_.Lean.Macro.trace clsName msg

/--
宏展开期间可能抛出的异常。
-/
inductive Exception where
  /-- 携带源码位置与消息的宏展开错误。 -/
  | error : Lean.Syntax → String → Exception
  /--
  不支持该语法的异常。它被单独保留，是因为宏展开器以它进行控制流：
  如果一个宏不支持某段语法，系统就会尝试下一个宏。
  -/
  | unsupportedSyntax : Exception

/-- 抛出 `unsupportedSyntax` 异常。 -/
def throwUnsupported {α : Type} : Lean.MacroM α :=
  _root_.Lean.Macro.throwUnsupported

/--
抛出带有给定消息的错误，并使用当前 `ref` 提供位置信息。
-/
def «throwError» {α : Type} (msg : String) : Lean.MacroM α :=
  _root_.Lean.Macro.throwError msg

/-- 抛出带有给定消息和位置信息的错误。 -/
def «throwErrorAt» {α : Type} (ref : Lean.Syntax) (msg : String) : Lean.MacroM α :=
  _root_.Lean.Macro.throwErrorAt ref msg

/--
递增宏作用域计数器，使动作 `x` 的主体内使用新的宏作用域。
-/
protected def withFreshMacroScope {α : Type} (x : Lean.MacroM α) : Lean.MacroM α :=
  _root_.Lean.Macro.withFreshMacroScope x

/-- 为名称 `n` 添加一个新的宏作用域。 -/
def addMacroScope (n : Lean.Name) : Lean.MacroM Lean.Name :=
  _root_.Lean.Macro.addMacroScope n

/-- 若环境含有名为 `declName` 的声明，则返回 `true`。 -/
def hasDecl (declName : Lean.Name) : Lean.MacroM Bool :=
  _root_.Lean.Macro.hasDecl declName

/-- 根据文件中的当前位置获取当前命名空间。 -/
def getCurrNamespace : Lean.MacroM Lean.Name :=
  _root_.Lean.Macro.getCurrNamespace

/-- 将给定名称解析为一组重载的命名空间。 -/
def resolveNamespace (n : Lean.Name) : Lean.MacroM (List Lean.Name) :=
  _root_.Lean.Macro.resolveNamespace n

/--
将给定名称解析为一组重载的全局定义。每个候选项中的 `List String` 是推导出的投影列表；
这些投影与名称的组成部分存在歧义。

注意，此函数不会触发与保留名称关联的动作。Lean 存在保留名称；例如，定义 `foo`
会为陈述 `foo` 等于其定义的定理保留名称 `foo.def`，而与 `foo.def` 关联的动作会自动证明
该定理。在宏层面，名称会被解析，但动作不会执行；这些动作由精译器在把 `Syntax`
转换为 `Expr` 时执行。
-/
def resolveGlobalName (n : Lean.Name) : Lean.MacroM (List (Lean.Name × List String)) :=
  _root_.Lean.Macro.resolveGlobalName n

end Macro

namespace PrettyPrinter

/--
尝试在反精译的后处理步骤中逆转宏展开的函数。它不如任意反精译器通用，
但无需导入 `Lean` 即可声明，并由 `[app_unexpander]` 属性使用。
-/
abbrev Unexpander := _root_.Lean.PrettyPrinter.Unexpander

/--
逆展开器单子，本质上是 `Syntax → Option α`。其中 `Syntax` 是 `ref`，
并且计算可以失败而不产生错误消息。
-/
abbrev UnexpandM := _root_.Lean.PrettyPrinter.UnexpandM

end PrettyPrinter

end Manual.ZhDocString.NotationsMacros.Core
