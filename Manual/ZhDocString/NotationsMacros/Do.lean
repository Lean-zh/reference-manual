/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean.Elab.Do
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.NotationsMacros.Do

open Lean Elab Meta Parser.Term

/- `Signature.forName` validates documentation on the real declaration before `zhdocstring`
reads the translated field/constructor documentation below. These five upstream internal API
components have no docstrings, so register the same Chinese descriptions as builtin documentation
when this scoped carrier module is loaded. -/
initialize do
  Lean.addBuiltinDocString ``_root_.Lean.Elab.Do.ContInfo.returnCont
    "提前 `return` 所使用的续延。"
  Lean.addBuiltinDocString ``_root_.Lean.Elab.Do.ContInfo.breakCont
    "当前循环的 `break` 续延；不在循环中时为 `none`。"
  Lean.addBuiltinDocString ``_root_.Lean.Elab.Do.ContInfo.continueCont
    "当前循环的 `continue` 续延；不在循环中时为 `none`。"
  Lean.addBuiltinDocString ``_root_.Lean.Elab.Do.DoElemContKind.nonDuplicable
    "续延不可复制，必要时应通过连接点共享。"
  Lean.addBuiltinDocString ``_root_.Lean.Elab.Do.DoElemContKind.duplicable
    "续延可以安全地在多个控制流分支中精译。"

/--
选项 `backward.do.legacy` 控制是否使用旧版 `do` 记法精译器。
默认值为 `false`；此时启用可扩展的新版 `do` 精译器。将它设为 `true` 可临时恢复旧版行为。
-/
def backwardDoLegacy : Bool := false

/--
`do` 块精译期间共享的上下文。它缓存单子信息、跟踪可变变量与控制流续延，
并保存构造 `pure`、`bind` 及单子应用所需的操作。
-/
structure Context where
  /-- 已推断并缓存的单子信息。 -/
  monadInfo : _root_.Lean.Elab.Do.MonadInfo
  /-- 按声明顺序排列的可变变量；它与 `mutVarDefs` 保持同步。 -/
  mutVars : Array _root_.Lean.Elab.Do.MutVar := #[]
  /-- 从可变变量名到其 `MutVar` 记录的映射；它与 `mutVars` 保持同步。 -/
  mutVarDefs : Std.HashMap Name _root_.Lean.Elab.Do.MutVar := {}
  /-- 当前 `do` 块的预期结果类型。 -/
  doBlockResultType : Expr
  /-- `return`、`break` 和 `continue` 续延的信息引用。 -/
  contInfo : _root_.Lean.Elab.Do.ContInfoRef
  /-- 当前 `do` 元素是否为死代码。 -/
  deadCode : _root_.Lean.Elab.Do.CodeLiveness := .alive
  /-- 构造 `pure`、`bind` 和单子应用的可插拔操作。 -/
  ops : _root_.Lean.Elab.Do.DoOpsRef

/-- 已推断出的单子及其宇宙层级信息，并缓存相应的 `PUnit` 表达式。 -/
structure MonadInfo where
  /-- 已推断的单子类型，形如 `m : Type u → Type v`。 -/
  m : Expr
  /-- `m : Type u → Type v` 中的 `u`。 -/
  u : Level
  /-- `m : Type u → Type v` 中的 `v`。 -/
  v : Level
  /-- 缓存的 `PUnit` 类型表达式；当 `u = 0` 时使用 `Unit`。 -/
  cachedPUnit : Expr :=
    if u matches .zero then mkConst ``Unit else mkConst ``PUnit [mkLevelSucc u]
  /-- 缓存的 `PUnit.unit` 表达式；当 `u = 0` 时使用 `Unit.unit`。 -/
  cachedPUnitUnit : Expr :=
    if u matches .zero then mkConst ``Unit.unit else mkConst ``PUnit.unit [mkLevelSucc u]

/-- 代码块是活代码还是死代码。 -/
inductive CodeLiveness where
  /-- 已推断代码在语法上不可达，因此完全不必精译。 -/
  | deadSyntactically
  /-- 已推断代码在语义上不可达，但仍须精译以生成程序。 -/
  | deadSemantically
  /-- 代码可达，或虽不可达但系统未能证明这一点。 -/
  | alive

namespace ContInfoRef

/-- 从为打破实现循环依赖而使用的引用中取回控制续延信息。 -/
def toContInfo (m : _root_.Lean.Elab.Do.ContInfoRef) : _root_.Lean.Elab.Do.ContInfo :=
  _root_.Lean.Elab.Do.ContInfoRef.toContInfo m

end ContInfoRef

/-- `do` 精译器的 `return`、`break` 与 `continue` 续延信息。 -/
structure ContInfo where
  /-- 提前 `return` 所使用的续延。 -/
  returnCont : _root_.Lean.Elab.Do.ReturnCont
  /-- 当前循环的 `break` 续延；不在循环中时为 `none`。 -/
  breakCont : Option (_root_.Lean.Elab.Do.DoElabM Expr) := none
  /-- 当前循环的 `continue` 续延；不在循环中时为 `none`。 -/
  continueCont : Option (_root_.Lean.Elab.Do.DoElabM Expr) := none
  deriving Inhabited

namespace DoOpsRef

/-- 从为打破实现循环依赖而使用的引用中取回 `do` 精译操作。 -/
def toDoOps (r : _root_.Lean.Elab.Do.DoOpsRef) : _root_.Lean.Elab.Do.DoOps :=
  _root_.Lean.Elab.Do.DoOpsRef.toDoOps r

end DoOpsRef

/-- `do` 精译器生成 `pure`、`bind` 与单子类型应用时使用的可插拔操作。 -/
structure DoOps where
  /-- 构造 `pure (α := α) e : m α`。 -/
  mkPureApp : (α e : Expr) → _root_.Lean.Elab.Do.DoElabM Expr
  /-- 构造 `bind (α := α) (β := β) e k : m β`。 -/
  mkBindApp : (α β e k : Expr) → _root_.Lean.Elab.Do.DoElabM Expr
  /-- 若 `e` 在语法上是 `pure …` 应用，则返回纯值；否则返回 `none`。 -/
  isPureApp? : Expr → Option Expr
  /-- 匹配单子应用 `m α`，并返回 `m` 的信息与 `α`。 -/
  splitMonadApp? : Expr → Term.TermElabM (Option (_root_.Lean.Elab.Do.MonadInfo × Expr))
  /-- 从结果类型 `α` 构造 `m α`。 -/
  mkMonadApp : Expr → _root_.Lean.Elab.Do.DoElabM Expr
  deriving Inhabited

/--
`do` 块元素精译器的类型。精译器接收一个 `DoElem` 及描述块中剩余部分的
`DoElemCont`，并在 `DoElabM` 中生成表达式。
-/
abbrev DoElab := _root_.Lean.Elab.Do.DoElab

/--
把 `do` 元素精译器注册到给定语法结点种类。精译器应具有 `DoElab` 类型。
通常应优先使用 `elab` 或 `elab_rules` 命令，而不是直接使用此属性。
-/
def doElemElabAttribute :
    _root_.Lean.KeyedDeclsAttribute _root_.Lean.Elab.Do.DoElab :=
  _root_.Lean.Elab.Do.doElemElabAttribute

/-- 精译单个 `do` 元素，并把结果交给给定续延。默认捕获并处理延后精译异常。 -/
def elabDoElem (stx : DoElem) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoElem stx cont catchExPostpone

/-- 精译完整的 `doSeq`，并把结果交给给定续延。默认捕获并处理延后精译异常。 -/
def elabDoSeq (doSeq : DoSeq) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoSeq doSeq cont catchExPostpone

/-- 精译非空的 `do` 元素数组；若数组为空则报错。默认捕获并处理延后精译异常。 -/
def elabDoElems1 (doElems : Array DoElem) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoElems1 doElems cont catchExPostpone

/-- 从结果类型 `α` 构造当前单子的类型应用 `m α`。 -/
def mkMonadApp (resultType : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkMonadApp resultType

/-- 构造表达式 `pure (α := α) e`。 -/
def mkPureApp (α e : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkPureApp α e

/-- 构造表达式 `Bind.bind (α := α) (β := β) e k`。 -/
def mkBindApp (α β e k : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkBindApp α β e k

/-- 返回缓存的 `PUnit.unit` 表达式。 -/
def mkPUnitUnit : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkPUnitUnit

/--
描述一个 `do` 元素之后其余代码的精译。元素精译器应把结果绑定为 `resultName`，
确保它具有 `resultType`，再运行 `k`；`kind` 说明该续延能否安全复制。
-/
structure DoElemCont where
  mk ::
  /-- 单子结果变量的名字。 -/
  resultName : Name
  /-- 单子结果的类型。 -/
  resultType : Expr
  /-- 精译 `do` 块剩余部分的续延动作。 -/
  k : _root_.Lean.Elab.Do.DoElabM Expr
  /-- 是否允许多次生成该续延的代码。 -/
  kind : _root_.Lean.Elab.Do.DoElemContKind := .nonDuplicable
  deriving Inhabited

/-- `do` 元素续延能否复制；标记为 `nonDuplicable` 始终安全。 -/
inductive DoElemContKind where
  /-- 续延不可复制，必要时应通过连接点共享。 -/
  | nonDuplicable
  /-- 续延可以安全地在多个控制流分支中精译。 -/
  | duplicable
  deriving Inhabited

namespace DoElemCont

/--
返回一个结果类型为 `PUnit` 的续延。若原续延已具有该结果类型则原样返回；否则记录
类型错误，并返回一个用错误恢复占位值调用原续延的新续延。
-/
def ensureUnit (dec : _root_.Lean.Elab.Do.DoElemCont) : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureUnit dec

/--
与 `ensureUnit` 相同，但把类型错误报告在 `ref` 指定的语法位置。
-/
def ensureUnitAt (dec : _root_.Lean.Elab.Do.DoElemCont) (ref : Syntax) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureUnitAt dec ref

/--
令续延的结果类型为 `elementType`。若原类型不定义等价，则在 `ref` 处报告错误，
并在允许错误恢复时返回一个以占位结果调用原续延的新续延。
-/
def ensureHasTypeAt (dec : _root_.Lean.Elab.Do.DoElemCont) (ref : Syntax)
    (elementType : Expr) : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureHasTypeAt dec ref elementType

/--
把 `PUnit.unit` 绑定到续延的结果名后继续运行，并立即对该绑定进行 ζ 约简。
-/
def continueWithUnit (dec : _root_.Lean.Elab.Do.DoElemCont) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.continueWithUnit dec

/--
在“语法死代码”标志下精译续延，仅保留精译产生的警告；用于诊断不可达代码。
-/
def elabAsSyntacticallyDeadCode (dec : _root_.Lean.Elab.Do.DoElemCont) :
    _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode dec

/--
构造 `e >>= fun (resultName : resultType) => k`，但会消去 `e >>= pure`，并在 `e` 是纯计算时
把绑定收缩为局部 `let`。
-/
def mkBindUnlessPure (dec : _root_.Lean.Elab.Do.DoElemCont) (e : Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.mkBindUnlessPure dec e

/--
以可复制的代理续延调用 `caller`。若代理被精译多次，则引入连接点，确保原续延只精译一次。
这适用于多个尾调用分支共享同一续延的 `if`、`match` 等控制流结构。
-/
def withDuplicableCont (nondupDec : _root_.Lean.Elab.Do.DoElemCont)
    (callerInfo : _root_.Lean.Elab.Do.ControlInfo)
    (caller : _root_.Lean.Elab.Do.DoElemCont → _root_.Lean.Elab.Do.DoElabM Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.withDuplicableCont nondupDec callerInfo caller

end DoElemCont

/-- 取得当前 `return` 续延。 -/
def getReturnCont : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.ReturnCont :=
  _root_.Lean.Elab.Do.getReturnCont

/-- 取得当前循环的 `break` 续延；不在循环中时返回 `none`。 -/
def getBreakCont : _root_.Lean.Elab.Do.DoElabM (Option (_root_.Lean.Elab.Do.DoElabM Expr)) :=
  _root_.Lean.Elab.Do.getBreakCont

/-- 取得当前循环的 `continue` 续延；不在循环中时返回 `none`。 -/
def getContinueCont : _root_.Lean.Elab.Do.DoElabM (Option (_root_.Lean.Elab.Do.DoElabM Expr)) :=
  _root_.Lean.Elab.Do.getContinueCont

/--
在精译循环体 `body` 时安装新的 `break`、`continue` 和 `return` 续延。
-/
def enterLoopBody (breakCont continueCont : _root_.Lean.Elab.Do.DoElabM Expr)
    (returnCont : _root_.Lean.Elab.Do.ReturnCont) (body : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.enterLoopBody breakCont continueCont returnCont body

/--
把 `doElem_control_info` 属性注册到给定语法结点种类。处理器应具有
`ControlInfoHandler` 类型；纯处理器可以返回 `ControlInfo.pure`。
-/
def controlInfoElemAttribute :
    _root_.Lean.KeyedDeclsAttribute _root_.Lean.Elab.Do.ControlInfoHandler :=
  _root_.Lean.Elab.Do.controlInfoElemAttribute

/-- 从一个 `doElem` 的语法推断 `ControlInfo` 的处理器类型。 -/
abbrev ControlInfoHandler := _root_.Lean.Elab.Do.ControlInfoHandler

/--
描述 `do` 块具有的控制效应。`breaks`、`continues`、`returnsEarly`、`reassigns` 与
`numRegularExits` 是语法信息；`noFallthrough` 则断言控制不会落入外围序列的下一元素。
必须满足 `numRegularExits = 0 → noFallthrough`。
-/
structure ControlInfo where
  /-- 源代码中是否出现 `break`。 -/
  breaks : Bool := false
  /-- 源代码中是否出现 `continue`。 -/
  continues : Bool := false
  /-- 源代码中是否出现提前 `return`。 -/
  returnsEarly : Bool := false
  /-- 精译后表达式把外围续延接入控制流的次数。 -/
  numRegularExits : Nat := 1
  /-- 为 `true` 时，断言控制绝不会落入外围序列的下一元素。 -/
  noFallthrough : Bool := false
  /-- 源代码中被重新赋值的变量名集合。 -/
  reassigns : NameSet := {}
  deriving Inhabited

namespace ControlInfo

/--
`ControlInfo.sequence` 的左单位元：描述总会经由唯一常规出口继续执行的纯元素。
-/
def pure : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.pure

/--
`ControlInfo.alternative` 的单位元：描述完全没有分支的块，因此没有常规出口且下一元素不可达。
-/
def empty : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.empty

/--
组合顺序执行 `a; b` 的控制信息：合并语法效应，常规出口数取自 `b`，且任一部分不落入时
整个序列都不落入下一元素。
-/
def sequence (a b : _root_.Lean.Elab.Do.ControlInfo) : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.sequence a b

/--
合并分支 `a | b` 的控制信息：合并语法效应并相加常规出口数；只有所有分支都不落入时，
整个分支结构才不落入下一元素。
-/
def alternative (a b : _root_.Lean.Elab.Do.ControlInfo) : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.alternative a b

end ControlInfo

/-- 推断单个 `doElem` 的控制信息。 -/
def inferControlInfoElem (doElem : DoElem) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.inferControlInfoElem doElem

/-- 推断整个 `doSeq` 的控制信息。 -/
def inferControlInfoSeq (doSeq : DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.inferControlInfoSeq doSeq

namespace InferControlInfo

/--
递归分析单个 `doElem` 的语法并计算其控制信息。宏会先展开；自定义语法则查询
`doElem_control_info` 处理器。
-/
def ofElem (stx : DoElem) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofElem stx

/-- 按顺序组合 `doSeq` 中每个元素的控制信息。 -/
def ofSeq (stx : DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofSeq stx

/-- 可选序列为 `none` 时返回纯控制信息，否则分析其中的 `doSeq`。 -/
def ofOptionSeq (stx? : Option DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofOptionSeq stx?

/--
计算 `let`、模式绑定或重新赋值的控制信息：组合右侧、失败分支与后续主体，并记录所有
被重新赋值的标识符。
-/
def ofLetOrReassign (reassigned : Array Ident) (rhs? : Option DoElem)
    (otherwise? : Option (TSyntax ``doSeqIndent)) (body? : Option (TSyntax ``doSeqIndent)) :
    TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofLetOrReassign reassigned rhs? otherwise? body?

/--
分析使用 `←` 的标识符或模式声明；`reassignment` 指明该声明是重新赋值而非新绑定。
-/
def ofLetOrReassignArrow (reassignment : Bool)
    (decl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow reassignment decl

end InferControlInfo

/-- `do` 块中由 `let mut` 声明的可变变量。 -/
structure MutVar where
  /-- `let mut` 声明中的标识符。 -/
  ident : Ident
  /-- 初始 `let mut` 绑定所产生的自由变量标识符。 -/
  baseId : FVarId
  deriving Inhabited

/--
把标识符注册为可变变量，并在扩展后的 `DoElabM` 读取器上下文中运行 `k`。
-/
def declareMutVar (x : Ident) (k : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.declareMutVar x k

/--
把标识符数组按顺序注册为可变变量，并在扩展后的 `DoElabM` 读取器上下文中运行 `k`。
-/
def declareMutVars (xs : Array Ident) (k : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.declareMutVars xs k

/-- 若标识符不是由 `let mut` 声明的可变变量，则在该标识符处抛出错误。 -/
def throwUnlessMutVarDeclared (x : Ident) : _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.throwUnlessMutVarDeclared x

/-- 若数组中的任一标识符不是由 `let mut` 声明的可变变量，则抛出错误。 -/
def throwUnlessMutVarsDeclared (xs : Array Ident) : _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.throwUnlessMutVarsDeclared xs

/--
把非尾位置可恢复主体嵌入 `origCont` 的单子变换器栈方案。它记录需要转发的提前返回、
循环控制和状态效应，以及主体在提升后栈中的结果类型。
-/
structure EffectForwarder where
  /-- 外围 `do` 块的续延；主体结束后会恢复它。 -/
  origCont : _root_.Lean.Elab.Do.DoElemCont
  /-- 若安装了提前返回处理器，则为安装位置处的子栈。 -/
  returnBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 若安装了 `break` 处理器，则为安装位置处的子栈。 -/
  breakBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 若安装了 `continue` 处理器，则为安装位置处的子栈。 -/
  continueBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 位于基础单子之上的完整变换器栈。 -/
  liftedStack : _root_.Lean.Elab.Do.ControlStack
  /-- 主体的精译结果类型，即 `stM dec.resultType`。 -/
  liftedDoBlockResultType : Expr

namespace EffectForwarder

/--
根据 `info` 汇总的效应与续延 `dec` 构造转发方案。方案只为实际需要的提前返回、状态、
`break` 和 `continue` 安装相应的变换器层。
-/
def ofCont (info : _root_.Lean.Elab.Do.ControlInfo) (dec : _root_.Lean.Elab.Do.DoElemCont) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.EffectForwarder :=
  _root_.Lean.Elab.Do.EffectForwarder.ofCont info dec

/--
在提升后的变换器栈中运行 `elabElem`：安装所需的 `break`、`continue` 与 `return` 处理器，
并把 `do` 块结果类型设为 `liftedDoBlockResultType`。
-/
def lift (l : _root_.Lean.Elab.Do.EffectForwarder)
    (elabElem : _root_.Lean.Elab.Do.DoElemCont → _root_.Lean.Elab.Do.DoElabM Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.EffectForwarder.lift l elabElem

/-- 构造一个续延：解包提升后主体的结果，再恢复并运行原续延 `origCont.k`。 -/
def restoreCont (l : _root_.Lean.Elab.Do.EffectForwarder) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.EffectForwarder.restoreCont l

end EffectForwarder

end ZhDoc.NotationsMacros.Do
