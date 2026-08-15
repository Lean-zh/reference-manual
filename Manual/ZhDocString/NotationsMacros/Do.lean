/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean.Elab.Do
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.NotationsMacros.Do

open Lean Elab Meta Parser.Term

/- `Signature.forName` 会先验证真实声明的文档，之后 `zhdocstring` 才会读取下方已翻译的
字段/构造器文档。上游这五个内部接口组件没有文档字符串，因此在加载这个限定作用域的
载体模块时，将相同的中文说明注册为内建文档。 -/
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
使用旧版 `do` 精译器，而不是新的可扩展实现。
-/
def backwardDoLegacy : Bool := false

/--
`do` 块精译期间共享的上下文。它缓存单子信息、跟踪可变变量与控制流续延，
并保存构造 `pure`、`bind` 及单子应用所需的操作。
-/
structure Context where
  /-- 已推断并缓存的单子信息。 -/
  monadInfo : _root_.Lean.Elab.Do.MonadInfo
  /--
  按声明顺序排列的可变变量。它与 `mutVarDefs` 保持同步；只能通过 `declareMutVar` /
  `declareMutVars` 插入。
  -/
  mutVars : Array _root_.Lean.Elab.Do.MutVar := #[]
  /-- 从可变变量名到其 `MutVar` 记录的映射；它与 `mutVars` 保持同步。 -/
  mutVarDefs : Std.HashMap Name _root_.Lean.Elab.Do.MutVar := {}
  /--
  当前 `do` 块的预期类型。
  例如，在 `for` 循环的 `do` 块中，它可能不同于 `ReturnCont.resultType`。
  -/
  doBlockResultType : Expr
  /-- `return`、`break` 和 `continue` 续延的信息引用。 -/
  contInfo : _root_.Lean.Elab.Do.ContInfoRef
  /-- 当前 `do` 元素是否为死代码。如果它不是 `.alive`，`elabDoElem` 将发出警告。 -/
  deadCode : _root_.Lean.Elab.Do.CodeLiveness := .alive
  /-- 构造 `pure`、`bind` 和单子应用的可插拔操作。 -/
  ops : _root_.Lean.Elab.Do.DoOpsRef

/-- 已推断出的单子及其宇宙层级信息，并缓存相应的 `PUnit` 表达式。 -/
structure MonadInfo where
  /-- 已推断出的单子，其类型为 `Type u → Type v`。 -/
  m : Expr
  /-- `m : Type u → Type v` 中的 `u`。 -/
  u : Level
  /-- `m : Type u → Type v` 中的 `v`。 -/
  v : Level
  /-- 缓存的 `PUnit` 表达式。 -/
  cachedPUnit : Expr :=
    if u matches .zero then mkConst ``Unit else mkConst ``PUnit [mkLevelSucc u]
  /-- 缓存的 `PUnit.unit` 表达式。 -/
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

/--
有关成功、`return`、`break` 或 `continue` 续延的信息；使用这些续延的代码精译完毕后，
才会填充它们。
-/
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

/-- `do` 精译器所生成的 `pure` / `bind` 应用的可插拔构造器。 -/
structure DoOps where
  /-- 构造 `pure (α:=α) e : m α`。 -/
  mkPureApp : (α e : Expr) → _root_.Lean.Elab.Do.DoElabM Expr
  /-- 构造 `bind (α:=α) (β:=β) e k : m β`。 -/
  mkBindApp : (α β e k : Expr) → _root_.Lean.Elab.Do.DoElabM Expr
  /--
  如果 `e` 在语法上是 `pure …` 应用，则返回纯值；否则返回 `none`。
  `DoElemCont.mkBindUnlessPure` 用它将 `e >>= pure` 收缩为 `e`，并将
  `pure e >>= k` 收缩为 `let x := e; k x`。
  -/
  isPureApp? : Expr → Option Expr
  /-- 匹配单子应用 `m α`，返回 `m` 的 `MonadInfo` 和 `α`。 -/
  splitMonadApp? : Expr → Term.TermElabM (Option (_root_.Lean.Elab.Do.MonadInfo × Expr))
  /-- 从结果类型 `α` 构造 `m α`。 -/
  mkMonadApp : Expr → _root_.Lean.Elab.Do.DoElabM Expr
  deriving Inhabited

/--
`do` 块元素精译器的类型。

它满足 ``elabTerm `(do $e; $rest) = elabDoElem e dec``，其中 `elabDoElem e ·` 是 `do`
元素 `e` 的精译器，而 `dec` 是描述块中剩余部分 `rest` 如何精译的 `DoElemCont`。
-/
abbrev DoElab := _root_.Lean.Elab.Do.DoElab

/--
为给定的语法结点种类注册一个 `do` 元素精译器。

`do` 元素精译器应具有 `DoElab` 类型（即
`Lean.Syntax → DoElemCont → DoElabM Expr`）：它应以给定语法结点种类的语法和一个
`DoElemCont` 为参数，并生成一个表达式。

精译 `do` 块 `do e; rest` 时，会以 `e` 的语法和表示 `rest` 的 `DoElemCont` 调用 `e`
的精译器。

通常应优先使用 `elab_rules` 和 `elab` 命令，而不是直接使用此属性。
-/
def doElemElabAttribute :
    _root_.Lean.KeyedDeclsAttribute _root_.Lean.Elab.Do.DoElab :=
  _root_.Lean.Elab.Do.doElemElabAttribute

/--
精译单个 `do` 元素 `stx`，并以 `cont` 表示其余 `do` 块。它会先处理死代码、宏展开与
嵌套动作，再依语法结点种类调用已注册的元素精译器；默认捕获精译延后异常并安排重试。
-/
def elabDoElem (stx : DoElem) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoElem stx cont catchExPostpone

/--
精译完整的 `doSeq`，并把结果交给 `cont`。默认捕获精译延后异常、恢复精译状态，并把
整个序列安排为稍后重试。
-/
def elabDoSeq (doSeq : DoSeq) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoSeq doSeq cont catchExPostpone

/--
从右向左为非空 `do` 元素数组构造续延链并精译它；若数组为空则报错。默认让每个元素
捕获并处理精译延后异常。
-/
def elabDoElems1 (doElems : Array DoElem) (cont : _root_.Lean.Elab.Do.DoElemCont)
    (catchExPostpone : Bool := true) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.elabDoElems1 doElems cont catchExPostpone

/-- 从 `α` 构造 `m α`。 -/
def mkMonadApp (resultType : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkMonadApp resultType

/-- 表达式 ``pure (α:=α) e``。 -/
def mkPureApp (α e : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkPureApp α e

/-- 表达式 ``Bind.bind (α:=α) (β:=β) e k``。 -/
def mkBindApp (α β e k : Expr) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkBindApp α β e k

/-- 缓存的 ``PUnit.unit`` 表达式。 -/
def mkPUnitUnit : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.mkPUnitUnit

/--
精译 `do` 块 `do $e; $rest` 会产生调用
``elabTerm `(do $e; $rest) = elabDoElem e dec``，其中 `elabDoElem e ·` 是 `do` 元素 `e`
的精译器，而 `dec` 是描述块中剩余部分 `rest` 如何精译的 `DoElemCont`。

如果 `e` 的语义会恢复其续延 `rest`，则它的精译器必须把结果绑定到 `resultName`，确保
结果具有 `resultType` 类型，然后使用 `dec` 精译 `rest`。

显然，对于项元素 `e : m α`，结果类型是 `α`。
较微妙的是，对于绑定元素 `let x := e` 或 `let x ← e`，结果类型是 `PUnit`，与被绑定变量
`x` 的类型无关。

示例：
* `return` 丢弃续延；`return x; pure ()` 精译为 `pure x`。
* `let x ← e; rest x` 精译为 `e >>= fun x => rest x`。
* `let x := 3; let y ← (let x ← e); rest x` 精译为
  `let x := 3; e >>= fun x_1 => let y := (); rest x`，随后立即进行 ζ 约简，得到
  `let x := 3; e >>= fun x_1 => rest x`。
* `one; two` 精译为 `one >>= fun (_ : PUnit) => two`；如果 `one` 的类型不是 `PUnit`，
  则会报错。
-/
structure DoElemCont where
  mk ::
  /-- 单子结果变量的名字。 -/
  resultName : Name
  /-- 单子结果的类型。 -/
  resultType : Expr
  /--
  用于精译块中 `rest` 的续延。它假定 `do` 块的结果已经以正确类型绑定到
  `resultName`（即 `resultType`，但依赖 `match` 可能会细化该类型）。
  -/
  k : _root_.Lean.Elab.Do.DoElabM Expr
  /-- 是否允许多次生成续延的代码，例如在 `match` 或 `if` 的不同分支中生成。 -/
  kind : _root_.Lean.Elab.Do.DoElemContKind := .nonDuplicable
  deriving Inhabited

/-- `do` 元素的续延是否可以复制。指定 `nonDuplicable` 始终安全；`duplicable` 允许更多优化。 -/
inductive DoElemContKind where
  /-- 续延不可复制，必要时应通过连接点共享。 -/
  | nonDuplicable
  /-- 续延可以安全地在多个控制流分支中精译。 -/
  | duplicable
  deriving Inhabited

namespace DoElemCont

/--
给定续延 `dec`，返回一个从 `dec` 派生且结果类型为 `PUnit` 的续延。
如果 `dec` 的结果类型已经是 `PUnit`，则直接返回 `dec`。否则记录错误，并返回一个以
`sorry` 为结果调用 `dec` 的新续延。
-/
def ensureUnit (dec : _root_.Lean.Elab.Do.DoElemCont) : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureUnit dec

/--
给定续延 `dec` 和引用 `ref`，返回一个从 `dec` 派生且结果类型为 `PUnit` 的续延。
如果 `dec` 的结果类型已经是 `PUnit`，则直接返回 `dec`。否则记录错误，并返回一个以
`sorry` 为结果调用 `dec` 的新续延。错误报告在 `ref` 处。
-/
def ensureUnitAt (dec : _root_.Lean.Elab.Do.DoElemCont) (ref : Syntax) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureUnitAt dec ref

/--
给定续延 `dec`、引用 `ref` 和元素结果类型 `elementType`，返回一个从 `dec` 派生且结果
类型为 `elementType` 的续延。
如果 `dec` 的结果类型已经是 `elementType`，则直接返回 `dec`。
若二者不定义相等，则记录错误，并返回一个以 `sorry` 为结果调用 `dec`
的新续延。错误报告在 `ref` 处。
-/
def ensureHasTypeAt (dec : _root_.Lean.Elab.Do.DoElemCont) (ref : Syntax)
    (elementType : Expr) : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.DoElemCont.ensureHasTypeAt dec ref elementType

/--
返回 `let $k.resultName : PUnit := PUnit.unit; $(← k.k)`，并确保 `k.k` 的结果类型是
`PUnit`，然后立即对这个 `let` 进行 ζ 约简。
-/
def continueWithUnit (dec : _root_.Lean.Elab.Do.DoElemCont) : _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.continueWithUnit dec

/-- 将 `deadCode` 标志设为 `deadSyntactically` 来精译 `DoElemCont`，以便发出警告。 -/
def elabAsSyntacticallyDeadCode (dec : _root_.Lean.Elab.Do.DoElemCont) :
    _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode dec

/--
返回 `$e >>= fun ($dec.resultName : $dec.resultType) => $(← dec.k)`；如果 `$(← dec.k)` 是
`pure $dec.resultName`，或 `e` 是某个 `pure` 计算，则消去此绑定。
-/
def mkBindUnlessPure (dec : _root_.Lean.Elab.Do.DoElemCont) (e : Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.mkBindUnlessPure dec e

/--
以 `dec` 的可复制代理调用 `caller`。
当代理被精译多次时，会引入一个连接点，使 `dec` 只精译一次，以填充该连接点的右侧。

这适用于 `if` 和 `match` 等控制流构造：其中多个尾调用分支共享同一续延。
-/
def withDuplicableCont (nondupDec : _root_.Lean.Elab.Do.DoElemCont)
    (callerInfo : _root_.Lean.Elab.Do.ControlInfo)
    (caller : _root_.Lean.Elab.Do.DoElemCont → _root_.Lean.Elab.Do.DoElabM Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.DoElemCont.withDuplicableCont nondupDec callerInfo caller

end DoElemCont

/-- 从当前 `do` 精译上下文取得 `return` 续延。 -/
def getReturnCont : _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.ReturnCont :=
  _root_.Lean.Elab.Do.getReturnCont

/-- 从当前 `do` 精译上下文取得 `break` 续延；不在循环中时返回 `none`。 -/
def getBreakCont : _root_.Lean.Elab.Do.DoElabM (Option (_root_.Lean.Elab.Do.DoElabM Expr)) :=
  _root_.Lean.Elab.Do.getBreakCont

/-- 从当前 `do` 精译上下文取得 `continue` 续延；不在循环中时返回 `none`。 -/
def getContinueCont : _root_.Lean.Elab.Do.DoElabM (Option (_root_.Lean.Elab.Do.DoElabM Expr)) :=
  _root_.Lean.Elab.Do.getContinueCont

/--
准备好用于精译循环体的上下文。
这包括设置返回续延、中断续延、继续续延，以及循环体中 `do` 块已改变的结果类型。
-/
def enterLoopBody (breakCont continueCont : _root_.Lean.Elab.Do.DoElabM Expr)
    (returnCont : _root_.Lean.Elab.Do.ReturnCont) (body : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.enterLoopBody breakCont continueCont returnCont body

/--
为给定的 `doElem` 语法结点种类注册一个 `ControlInfo` 推断处理器。

处理器应具有 `ControlInfoHandler` 类型（即 `DoElem → TermElabM ControlInfo`）。
对于纯处理器，请使用 `fun stx => return ControlInfo.pure`。
-/
def controlInfoElemAttribute :
    _root_.Lean.KeyedDeclsAttribute _root_.Lean.Elab.Do.ControlInfoHandler :=
  _root_.Lean.Elab.Do.controlInfoElemAttribute

/-- 从 `doElem` 语法推断 `ControlInfo` 的处理器。用 `@[doElem_control_info parserName]` 注册。 -/
abbrev ControlInfoHandler := _root_.Lean.Elab.Do.ControlInfoHandler

/--
表示 `do` 块具有哪些控制效应的信息。

各字段按性质分为：

* `breaks`、`continues`、`returnsEarly` 和 `reassigns` 属于**语法层面**：当且仅当相应构造
  出现在块源代码的任意位置时，它们才为 `true` / 非空，与该构造在语义上是否可达无关。
  下游精译器必须假定每个这样的语法效应都可能发生，因为精译器会访问每一个 do 元素
  （只有顶层 `return`/`break`/`continue` 会通过 `elabAsSyntacticallyDeadCode` 短路）。
* `numRegularExits` 也属于**语法层面**：它是块在精译所得表达式中接入外围续延的次数。
  `withDuplicableCont` 将它读作连接点复制的触发条件（`> 1`）。
* `noFallthrough = true` 断言外围序列中的下一个 do 元素 在语义上无关（控制绝不会落入
  其中）。`noFallthrough = false` 不作任何断言。当此字段为 `true` 时，会在下一个元素上
  发出死代码警告。

不变量：`numRegularExits = 0 → noFallthrough`。其逆命题不成立。
-/
structure ControlInfo where
  /-- `do` 块在语法上包含 `break`。 -/
  breaks : Bool := false
  /-- `do` 块在语法上包含 `continue`。 -/
  continues : Bool := false
  /-- `do` 块在语法上包含提前 `return`。 -/
  returnsEarly : Bool := false
  /--
  块在精译所得表达式中接入外围续延的次数。
  `withDuplicableCont` 用它判断是否引入连接点（`> 1`）。
  -/
  numRegularExits : Nat := 1
  /--
  为 `true` 时，断言外围序列中的下一个 do 元素 在语义上无关（控制绝不会落入其中）。
  `false` 不作任何断言。
  -/
  noFallthrough : Bool := false
  /-- `do` 块中某处在语法上被重新赋值的变量。 -/
  reassigns : NameSet := {}
  deriving Inhabited

namespace ControlInfo

/--
`ControlInfo.sequence` 的左单位元：描述总会正常落入后续代码、且只有一个常规出口的
元素的 `ControlInfo`。
-/
def pure : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.pure

/--
`ControlInfo.alternative` 的单位元：描述完全没有任何分支的块的 `ControlInfo`（因此没有
常规出口，且下一个元素显然不可达）。
-/
def empty : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.empty

/--
序列 `a; b` 的 `ControlInfo`：效应标志取并集，常规出口就是 `b` 的常规出口，并且当且
仅当两部分都能落入后续代码时，该序列才会落入后续代码。
-/
def sequence (a b : _root_.Lean.Elab.Do.ControlInfo) : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.sequence a b

/--
分支 `a | b` 的 `ControlInfo`：效应标志取并集，常规出口数相加，并且当且仅当至少一个
分支能落入后续代码时，该选择结构才会落入后续代码。
-/
def alternative (a b : _root_.Lean.Elab.Do.ControlInfo) : _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.ControlInfo.alternative a b

end ControlInfo

/-- 推断单个 do 元素 的 `ControlInfo`。 -/
def inferControlInfoElem (doElem : DoElem) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.inferControlInfoElem doElem

/-- 推断 `doSeq` 的 `ControlInfo`。 -/
def inferControlInfoSeq (doSeq : DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.inferControlInfoSeq doSeq

namespace InferControlInfo

/--
递归推断单个 `doElem` 的 `ControlInfo`。它先展开宏，再按内建 `do` 元素的语法形式分析；
对于自定义语法，则依次尝试通过 `@[doElem_control_info ...]` 注册的处理器。
-/
def ofElem (stx : DoElem) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofElem stx

/--
依次推断 `doSeq` 中每个元素的 `ControlInfo`，并用 `ControlInfo.sequence` 按顺序组合它们。
-/
def ofSeq (stx : DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofSeq stx

/--
如果可选序列是 `none`，则返回纯 `ControlInfo`；否则推断其中 `doSeq` 的控制信息。
-/
def ofOptionSeq (stx? : Option DoSeq) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofOptionSeq stx?

/--
推断 `let`、模式绑定或重新赋值的控制信息：分别推断可选右侧、模式匹配失败分支与后续
主体，将右侧同“主体或失败分支”的选择顺序组合，并记录 `reassigned` 中所有标识符。
-/
def ofLetOrReassign (reassigned : Array Ident) (rhs? : Option DoElem)
    (otherwise? : Option (TSyntax ``doSeqIndent)) (body? : Option (TSyntax ``doSeqIndent)) :
    TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofLetOrReassign reassigned rhs? otherwise? body?

/--
推断使用 `←` 的标识符声明或模式声明的控制信息；`reassignment` 指明该声明是重新赋值
而非新绑定，并据此收集被重新赋值的标识符。
-/
def ofLetOrReassignArrow (reassignment : Bool)
    (decl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM _root_.Lean.Elab.Do.ControlInfo :=
  _root_.Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow reassignment decl

end InferControlInfo

/-- `do` 块中由 `let mut` 声明的可变变量。 -/
structure MutVar where
  /-- `let mut` 声明中的标识符。 -/
  ident : Ident
  /-- `let mut` 所产生的初始绑定的 `FVarId`。 -/
  baseId : FVarId
  deriving Inhabited

/-- 将给定名称注册为一个 `mut` 变量。 -/
def declareMutVar (x : Ident) (k : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.declareMutVar x k

/-- 将给定的各个名称注册为 `mut` 变量。 -/
def declareMutVars (xs : Array Ident) (k : _root_.Lean.Elab.Do.DoElabM α) :
    _root_.Lean.Elab.Do.DoElabM α :=
  _root_.Lean.Elab.Do.declareMutVars xs k

/-- 如果给定名称不是已声明的 `mut` 变量，则抛出错误。 -/
def throwUnlessMutVarDeclared (x : Ident) : _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.throwUnlessMutVarDeclared x

/-- 如果给定的各个名称不是已声明的 `mut` 变量，则抛出错误。 -/
def throwUnlessMutVarsDeclared (xs : Array Ident) : _root_.Lean.Elab.Do.DoElabM Unit :=
  _root_.Lean.Elab.Do.throwUnlessMutVarsDeclared xs

/-- 通过单子变换器栈把非尾位置的可恢复主体嵌入 `origCont` 的方案。 -/
structure EffectForwarder where
  /-- 外围 `do` 块的续延；主体结束后恢复。 -/
  origCont : _root_.Lean.Elab.Do.DoElemCont
  /-- 安装提前返回处理器处的子栈（如果安装了该处理器）。 -/
  returnBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 安装 `break` 处理器处的子栈（如果安装了该处理器）。 -/
  breakBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 安装 `continue` 处理器处的子栈（如果安装了该处理器）。 -/
  continueBase? : Option _root_.Lean.Elab.Do.ControlStack
  /-- 位于基础单子之上的完整变换器栈。 -/
  liftedStack : _root_.Lean.Elab.Do.ControlStack
  /-- 主体的精译类型，即 `stM dec.resultType`。 -/
  liftedDoBlockResultType : Expr

namespace EffectForwarder

/-- 为效应由 `info` 汇总的主体构造提升器方案。 -/
def ofCont (info : _root_.Lean.Elab.Do.ControlInfo) (dec : _root_.Lean.Elab.Do.DoElemCont) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.EffectForwarder :=
  _root_.Lean.Elab.Do.EffectForwarder.ofCont info dec

/--
在提升后的栈中精译 `elabElem`：安装汇入 `liftedStack` 的 `break`/`continue`/`return`
处理器，并将 do 块的结果类型设为 `liftedDoBlockResultType`。其语义为
`MonadControl.liftWith fun runInBase => elabElem (runInBase pure)`。传给 `elabElem` 的续延会
隐式包装在 `runInBase` 中；一旦通过汇总此提升器*所有* `lift` 调用点上的效应确定了变换器栈
`t`，随后便由 `ControlStack.mkBreak`/`mkContinue`/`mkReturn` 实现这一包装。
-/
def lift (l : _root_.Lean.Elab.Do.EffectForwarder)
    (elabElem : _root_.Lean.Elab.Do.DoElemCont → _root_.Lean.Elab.Do.DoElabM Expr) :
    _root_.Lean.Elab.Do.DoElabM Expr :=
  _root_.Lean.Elab.Do.EffectForwarder.lift l elabElem

/-- 构造一个 `DoElemCont`，它解包提升后主体的结果，并恢复执行 `origCont.k`。 -/
def restoreCont (l : _root_.Lean.Elab.Do.EffectForwarder) :
    _root_.Lean.Elab.Do.DoElabM _root_.Lean.Elab.Do.DoElemCont :=
  _root_.Lean.Elab.Do.EffectForwarder.restoreCont l

end EffectForwarder

end ZhDoc.NotationsMacros.Do
