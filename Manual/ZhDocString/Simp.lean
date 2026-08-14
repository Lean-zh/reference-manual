import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc

/--
将给定名称注册为自定义 simp 集。把该名称作为属性应用于声明时，会将声明加入此
simp 集；把该名称作为参数传给 `simp` 策略时，`simp` 会使用其中的引理。

自定义 simp 集必须在[初始化](lean-manual://section/initialization)期间注册。

描述文字应当是概括该自定义 simp 集内容的简短单数名词短语。
-/
def registerSimpAttr : Unit := ()

/--
包含 simp 集的环境扩展，由 `Lean.Meta.registerSimpAttr` 返回。

可使用该 simp 集的属性或 `Lean.Meta.addSimpTheorem` 向其中添加定理；使用
`Lean.Meta.SimpExtension.getTheorems` 获取其中的内容。
-/
def SimpExtension : Type := Unit

namespace Simp

/--
`simp` 的配置。

例如，可通过 `simp +contextual` 或 `simp (maxSteps := 100000)` 语法把配置传给
`simp`。

另见 `Lean.Meta.Simp.neutralConfig` 和 `Lean.Meta.DSimp.Config`。
-/
structure Config where
  /-- 简化时最多访问的子表达式数量。默认值为 100000。 -/
  maxSteps : Nat := 100000
  /--
  简化器在解除条件引理的旁条件时，可以递归地应用简化。
  `maxDischargeDepth`（默认为 2）是对旁条件递归应用简化时的最大递归深度。
  -/
  maxDischargeDepth : Nat := 2
  /--
  当 `contextual` 为 `true`（默认为 `false`），且简化遇到蕴含 `p → q` 时，
  简化器会在简化 `q` 时把 `p` 作为额外的 simp 引理。
  -/
  contextual : Bool := false
  /-- 为 `true`（默认如此）时，简化器会尽可能缓存每个子表达式的简化结果。 -/
  memoize : Bool := true
  /--
  当 `singlePass` 为 `true`（默认为 `false`）时，简化器只执行一轮简化：先运行
  前置方法，再使用同余引理递归处理子表达式，最后运行后置方法。为 `false` 时，
  则迭代应用这一简化过程。
  -/
  singlePass : Bool := false
  /--
  为 `true`（默认如此）时，对 `let` 和 `have` 表达式执行 zeta 归约；也就是说，
  `let x := v; e[x]` 归约为 `e[v]`。若 `zetaHave` 为 `false`，则不对 `have`
  表达式执行 zeta 归约。另见 `zetaDelta`。
  -/
  zeta : Bool := true
  /--
  为 `true`（默认如此）时，对 `fun` 表达式的应用执行 beta 归约；也就是说，
  `(fun x => e[x]) v` 归约为 `e[v]`。
  -/
  beta : Bool := true
  /--
  尚未实现。为 `true`（默认如此）时，对 `fun` 表达式执行 eta 归约；也就是说，
  `(fun x => f x)` 归约为 `f`。
  -/
  eta : Bool := true
  /-- 配置如何判定两个结构体实例的定义相等性。参见 `Lean.Meta.EtaStructMode` 的文档。 -/
  etaStruct : Lean.Meta.EtaStructMode := .all
  /-- 为 `true`（默认如此）时，归约作用于构造子应用的 `match` 表达式。 -/
  iota : Bool := true
  /-- 为 `true`（默认如此）时，归约结构体构造子的投影。 -/
  proj : Bool := true
  /--
  为 `true`（默认为 `false`）时，简化器会推断 `Decidable p` 实例并将其归约，
  从而把命题 `p` 重写为 `True` 或 `False`。
  -/
  decide : Bool := false
  /-- 为 `true`（默认为 `false`）时，简化简单的算术表达式。 -/
  arith : Bool := false
  /--
  为 `true`（默认为 `false`）时，如果模式匹配所定义函数的某个模式适用，就展开
  该函数的应用。可用 `simp!` 语法启用此项。
  -/
  autoUnfold : Bool := false
  /--
  为 `true`（默认如此）时，如果没有同余定理可让 `simp` 访问依赖参数，就在该参数上
  切换到 `dsimp`。当 `dsimp` 为 `false` 时，不访问该参数。
  -/
  dsimp : Bool := true
  /--
  若 `failIfUnchanged` 为 `true`（默认如此），则 `simp`、`dsimp` 或 `simp_all`
  在没有取得进展时失败。
  -/
  failIfUnchanged : Bool := true
  /--
  若 `ground` 为 `true`（默认为 `false`），则归约基项。基项是不含自由变量或元变量的项。
  如果遇到标记为不可展开的函数应用 `f ...`，归约会在此中断。基项归约会应用
  `@[seval]` 引理。
  -/
  ground : Bool := false
  /--
  若 `unfoldPartialApp` 为 `true`（默认为 `false`），则当要求展开 `f` 时，
  `simp`、`dsimp` 或 `simp_all` 连 `f` 的部分应用也会展开。
  -/
  unfoldPartialApp : Bool := false
  /--
  为 `true`（默认为 `false`）时，展开局部定义。也就是说，若局部上下文含有
  `x : t := e`，则自由变量 `x` 归约为 `e`；否则必须把 `x` 作为 `simp` 参数提供。
  -/
  zetaDelta : Bool := false
  /--
  当 `index` 为 `false`（默认为 `true`）时，`simp` 只使用根符号查找候选 simp 定理。
  这近似于 Lean 3 的 `simp` 行为。
  -/
  index : Bool := true
  /--
  若 `implicitDefEqProofs := true`，则输入项和输出项定义相等时，`simp` 不创建证明项。
  -/
  implicitDefEqProofs : Bool := true
  /--
  为 `true`（默认如此）时，`simp` 会移除未使用的 `let` 和 `have` 表达式：若 `x`
  不在 `e` 中出现，则 `let x := v; e` 简化为 `e`。此选项优先于 `zeta` 和
  `zetaHave`。
  -/
  zetaUnused : Bool := true
  /--
  为 `true`（默认如此）时，`simp` 捕获运行时异常，并将其转换为 `simp` 异常。
  -/
  catchRuntime : Bool := true
  /--
  设为 `false`（默认为 `true`）时，禁用 `have` 表达式的 zeta 归约。如果 `zeta`
  为 `false`，此选项不起作用。若 `zeta` 或 `zetaUnused` 为 `true`，未使用的
  `have` 仍会被移除。
  -/
  zetaHave : Bool := true
  /--
  为 `true`（默认如此）时，`simp` 会尝试把非依赖的 `let` 转换成 `have`。
  这只在 `zeta := false` 时适用。
  -/
  letToHave : Bool := true
  /--
  为 `true`（默认如此）时，`simp` 在为 `f` 构造辅助同余证明时会尝试实现常量
  `f.congr_simp`。此选项之所以存在，是因为终止性证明器在构造终止性证明时会在
  `withoutModifyingEnv` 中使用 `simp`，所以 `simp` 实现的任何常量随后都会被删除。
  -/
  congrConsts : Bool := true
  /--
  为 `true`（默认如此）时，位向量简化过程使用 `BitVec.ofNat` 表示位向量字面量。
  -/
  bitVecOfNat : Bool := true
  /--
  为 `true`（默认如此）时，如果指数过大，处理 `^` 的简化过程会生成警告。
  -/
  warnExponents : Bool := true
  /--
  若 `suggestions` 为 `true`，`simp?` 会在当前目标上调用目前配置的库建议引擎，
  并尝试把所得建议用作 `simp` 策略的参数。
  -/
  suggestions : Bool := false
  /--
  最多使用多少条库建议。为 `none` 时使用默认上限。仅当 `suggestions` 为 `true`
  时相关。
  -/
  maxSuggestions : Option Nat := none
  /--
  若 `locals` 为 `true`，`simp` 会展开当前文件中的所有定义。对于局部定理，
  请改用 `+suggestions`。
  -/
  locals : Bool := false
  /--
  若 `instances` 为 `true`，`simp` 会访问实例参数。如果选项
  `backward.dsimp.instances` 为 `true`，它会覆盖此字段。
  -/
  instances : Bool := false

/-- 关闭所有归约及其他内建简化的 `simp` 中性配置。 -/
def neutralConfig : Unit := ()

end Simp

namespace DSimp

/--
`dsimp` 的配置。

例如，可通过 `dsimp (config := {zeta := false})` 语法把配置传给 `dsimp`。

实现说明：此结构体只用于处理 `(config := ...)` 语法，内部并不直接使用它；
`Lean.Elab.Tactic.elabSimpConfig` 会立即把它转换为 `Lean.Meta.Simp.Config`。
-/
structure Config where
  /--
  为 `true`（默认如此）时，对 `let` 和 `have` 表达式执行 zeta 归约；也就是说，
  `let x := v; e[x]` 归约为 `e[v]`。若 `zetaHave` 为 `false`，则不对 `have`
  表达式执行 zeta 归约。另见 `zetaDelta`。
  -/
  zeta : Bool := true
  /--
  为 `true`（默认如此）时，对 `fun` 表达式的应用执行 beta 归约；也就是说，
  `(fun x => e[x]) v` 归约为 `e[v]`。
  -/
  beta : Bool := true
  /--
  尚未实现。为 `true`（默认如此）时，对 `fun` 表达式执行 eta 归约；也就是说，
  `(fun x => f x)` 归约为 `f`。
  -/
  eta : Bool := true
  /-- 配置如何判定两个结构体实例的定义相等性。参见 `Lean.Meta.EtaStructMode` 的文档。 -/
  etaStruct : Lean.Meta.EtaStructMode := .all
  /-- 为 `true`（默认如此）时，归约作用于构造子应用的 `match` 表达式。 -/
  iota : Bool := true
  /-- 为 `true`（默认如此）时，归约结构体构造子的投影。 -/
  proj : Bool := true
  /--
  为 `true`（默认为 `false`）时，通过推断 `Decidable p` 实例并将其归约，把命题
  `p` 重写为 `True` 或 `False`。
  -/
  decide : Bool := false
  /--
  为 `true`（默认为 `false`）时，如果模式匹配所定义函数的某个模式适用，就展开
  该函数的应用。可用 `simp!` 语法启用此项。
  -/
  autoUnfold : Bool := false
  /--
  若 `failIfUnchanged` 为 `true`（默认如此），则 `simp`、`dsimp` 或 `simp_all`
  在没有取得进展时失败。
  -/
  failIfUnchanged : Bool := true
  /--
  若 `unfoldPartialApp` 为 `true`（默认为 `false`），则当要求展开 `f` 时，
  `simp`、`dsimp` 或 `simp_all` 连 `f` 的部分应用也会展开。
  -/
  unfoldPartialApp : Bool := false
  /--
  为 `true`（默认为 `false`）时，展开局部定义。若局部上下文含有 `x : t := e`，
  则自由变量 `x` 归约为 `e`；否则必须把 `x` 作为 `simp` 参数提供。
  -/
  zetaDelta : Bool := false
  /--
  当 `index` 为 `false`（默认为 `true`）时，`simp` 只使用根符号查找候选 simp 定理。
  这近似于 Lean 3 的 `simp` 行为。
  -/
  index : Bool := true
  /--
  为 `true`（默认如此）时，`simp` 会移除未使用的 `let` 和 `have` 表达式：若 `x`
  不在 `e` 中出现，则 `let x := v; e` 简化为 `e`。
  -/
  zetaUnused : Bool := true
  /--
  设为 `false`（默认为 `true`）时，禁用 `have` 表达式的 zeta 归约。如果 `zeta`
  为 `false`，此选项不起作用。若 `zeta` 或 `zetaUnused` 为 `true`，未使用的
  `have` 仍会被移除。
  -/
  zetaHave : Bool := true
  /--
  若 `locals` 为 `true`，`dsimp` 会展开当前文件中的所有定义。对于局部定理，
  请改用 `+suggestions`。
  -/
  locals : Bool := false
  /--
  若 `instances` 为 `true`，`dsimp` 会访问实例参数。如果选项
  `backward.dsimp.instances` 为 `true`，它会覆盖此字段。
  -/
  instances : Bool := false

end DSimp

namespace Option

/-- 启用或禁用简化过程（simproc）。 -/
def simprocs : Prop := True

/--
启用跟踪时，调用 `simp` 或 `dsimp` 会输出一个等价的 `simp only` 调用。
-/
def tactic.simp.trace : Prop := True

/--
启用“不必要的 `simpa`”代码检查器；当某次 `simpa` 可改用 `simp` 或 `simp at h`
证明时，该检查器会报告提示。
-/
def linter.unnecessarySimpa : Prop := True

/-- 启用后，输出简化器应用重写规则时的跟踪消息。 -/
def trace.Meta.Tactic.simp.rewrite : Prop := True

/-- 启用后，输出简化器尝试解除重写规则旁条件时的跟踪消息。 -/
def trace.Meta.Tactic.simp.discharge : Prop := True

end Option

end ZhDoc
