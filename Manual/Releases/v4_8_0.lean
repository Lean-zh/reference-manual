/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.8.0 (2024-06-05)" =>
%%%
tag := "release-v4.8.0"
file := "v4.8.0"
%%%

````markdown
### 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

* **函数归纳原理。**
  [#3432](https://github.com/leanprover/lean4/pull/3432), [#3620](https://github.com/leanprover/lean4/pull/3620),
  [#3754](https://github.com/leanprover/lean4/pull/3754), [#3762](https://github.com/leanprover/lean4/pull/3762),
  [#3738](https://github.com/leanprover/lean4/pull/3738), [#3776](https://github.com/leanprover/lean4/pull/3776),
  [#3898](https://github.com/leanprover/lean4/pull/3898)。

  系统会从一个（可能是互）递归函数的定义中，导出一个专门适用于证明该函数性质的**函数归纳原理**。

  例如，由下面这个定义：
  ```
  def ackermann : Nat → Nat → Nat
    | 0, m => m + 1
    | n+1, 0 => ackermann n 1
    | n+1, m+1 => ackermann n (ackermann (n + 1) m)
  ```
  可以得到
  ```
  ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
    (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
    (x x : Nat) : motive x x
  ```

  它可以通过 `using` 语法在 `induction` 策略中使用：
  ```
  induction n, m using ackermann.induct
  ```
* 终止性检查器现在能识别更多无需显式 `termination_by` 的递归模式。特别地，像下面这样“向上计数直到某个上界”的惯用写法：
  ```
  def Array.sum (arr : Array Nat) (i acc : Nat) : Nat :=
    if _ : i < arr.size then
      Array.sum arr (i+1) (acc + arr[i])
    else
      acc
  ```
  现在无需写出 `termination_by arr.size - i` 也能识别。
  * [#3630](https://github.com/leanprover/lean4/pull/3630) 让 `termination_by?` 在不需要时不再使用 `sizeOf`
  * [#3652](https://github.com/leanprover/lean4/pull/3652) 改进了 `termination_by` 语法。
  * [#3658](https://github.com/leanprover/lean4/pull/3658) 修改了终止性参数的精译方式。
  * [#3665](https://github.com/leanprover/lean4/pull/3665) 重构了 GuessLex，使其能推断更复杂的终止性参数
  * [#3666](https://github.com/leanprover/lean4/pull/3666) 能推断出如 `xs.size - i` 这样的终止性参数
* [#3629](https://github.com/leanprover/lean4/pull/3629),
  [#3655](https://github.com/leanprover/lean4/pull/3655),
  [#3747](https://github.com/leanprover/lean4/pull/3747)：
  添加了 `@[induction_eliminator]` 和 `@[cases_eliminator]` 属性，以便为 `induction` 和 `cases` 策略定义自定义消去器，从而替代 `@[eliminator]` 属性。
  为 `Nat` 提供了自定义消去器，使 `induction` 与 `cases` 将目标状态写成 `0` 和 `n + 1`，而不是 `Nat.zero` 与 `Nat.succ n`。
  新增选项 `tactic.customEliminators` 用于控制是否使用自定义消去器。
  还为 `rcases`/`rintro`/`obtain` 添加了一个特殊处理，使它们会使用 `Nat` 的自定义消去器。
* **更短的实例名。** 生成匿名实例名字的算法已更新。
  在 Std 与 Mathlib 中，新名字长度相对于旧名字长度的比值中位数约为 72%。
  使用旧算法时，最长名字有 1660 个字符；现在最长仅有 202 个字符。
  新算法下，95 百分位的名字长度为 67 个字符，而旧算法为 278。
  尽管新算法生成的名字唯一性降低了 1.2%，
  它会在所引用的声明不来自同一“项目”（即共享相同根模块的一组模块）时
  添加基于模块的后缀，以避免跨项目冲突。
  [#3089](https://github.com/leanprover/lean4/pull/3089)
  和 [#3934](https://github.com/leanprover/lean4/pull/3934)。
* [8d2adf](https://github.com/leanprover/lean4/commit/8d2adf521d2b7636347a5b01bfe473bf0fcfaf31)
  导入两个不同文件、且它们都包含同一定理的证明，如今不再被视为错误。
  这一特性对那些按需自动生成的定理（例如方程定理）尤其有用。
* [84b091](https://github.com/leanprover/lean4/commit/84b0919a116e9be12f933e764474f45d964ce85c)
  如果一个定理的类型**不是**命题，Lean 现在会报错。
* **定义透明性。** [47a343](https://github.com/leanprover/lean4/commit/47a34316fc03ce936fddd2d3dce44784c5bcdfa9)。`@[reducible]`、`@[semireducible]` 和 `@[irreducible]` 现在是作用域化的，并且可设置到已导入的声明上。
* `simp`/`dsimp`
  * [#3607](https://github.com/leanprover/lean4/pull/3607) 在 `dsimp` 中启用了内核投影化简
  * [b24fbf](https://github.com/leanprover/lean4/commit/b24fbf44f3aaa112f5d799ef2a341772d1eb222d)
    和 [acdb00](https://github.com/leanprover/lean4/commit/acdb0054d5a0efa724cff596ac26852fad5724c4)：
    `dsimproc` 命令
    用于定义保持 defeq 的化简过程。
  * [#3624](https://github.com/leanprover/lean4/pull/3624) 让 `dsimp` 将原始自然数字面量规范化为 `OfNat.ofNat` 应用。
  * [#3628](https://github.com/leanprover/lean4/pull/3628) 让 `simp` 正确处理 `OfScientific.ofScientific` 字面量。
  * [#3654](https://github.com/leanprover/lean4/pull/3654) 让 `dsimp?` 报告所使用的 simproc。
  * [dee074](https://github.com/leanprover/lean4/commit/dee074dcde03a37b7895a4901df2e4fa490c73c7) 修复了 `simp` 对非递归定义的方程定理处理。
  * [#3819](https://github.com/leanprover/lean4/pull/3819) 改进了 simp 遇到循环时的性能。
  * [#3821](https://github.com/leanprover/lean4/pull/3821) 修复了 discharger 与缓存之间的交互。
  * [#3824](https://github.com/leanprover/lean4/pull/3824) 防止 `simp` 破坏 `Char` 字面量。
  * [#3838](https://github.com/leanprover/lean4/pull/3838) 让 `Nat` 实例匹配更宽松。
  * [#3870](https://github.com/leanprover/lean4/pull/3870) 添加了 `simp` 配置选项的文档。
  * [#3972](https://github.com/leanprover/lean4/pull/3972) 修复了 simp 缓存。
  * [#4044](https://github.com/leanprover/lean4/pull/4044) 改进了“表现良好”的 discharger 的缓存行为。
* `omega`
  * [#3639](https://github.com/leanprover/lean4/pull/3639), [#3766](https://github.com/leanprover/lean4/pull/3766),
    [#3853](https://github.com/leanprover/lean4/pull/3853), [#3875](https://github.com/leanprover/lean4/pull/3875)：
    引入了一个项规范化器。
  * [#3736](https://github.com/leanprover/lean4/pull/3736) 改进了对 `Int` 模运算符正性的处理。
  * [#3828](https://github.com/leanprover/lean4/pull/3828) 让它可以作为 `simp` 的 discharger 工作。
  * [#3847](https://github.com/leanprover/lean4/pull/3847) 添加了有帮助的错误消息。
* `rfl`
  * [#3671](https://github.com/leanprover/lean4/pull/3671), [#3708](https://github.com/leanprover/lean4/pull/3708)：将 `@[refl]` 属性和 `rfl` 策略上游化。
  * [#3751](https://github.com/leanprover/lean4/pull/3751) 让 `apply_rfl` 不会对 `Eq` 自身起作用。
  * [#4067](https://github.com/leanprover/lean4/pull/4067) 改进了在没有目标时的错误消息。
* [#3719](https://github.com/leanprover/lean4/pull/3719) 将 `rw?` 策略上游化，并在
  [#3783](https://github.com/leanprover/lean4/pull/3783), [#3794](https://github.com/leanprover/lean4/pull/3794),
  [#3911](https://github.com/leanprover/lean4/pull/3911) 中修复并改进。
* `conv`
  * [#3659](https://github.com/leanprover/lean4/pull/3659) 为 `calc` 策略添加了一个 `conv` 版本。
  * [#3763](https://github.com/leanprover/lean4/pull/3763) 让 `conv` 使用 `try with_reducible rfl` 而不是 `try rfl` 做清理。
* `#guard_msgs`
  * [#3617](https://github.com/leanprover/lean4/pull/3617) 引入了使用 `⏎` 字符的空白保护。
  * [#3883](https://github.com/leanprover/lean4/pull/3883)：
    `#guard_msgs` 命令现在具有可更改空白规范化和消息顺序敏感度的选项。
    例如，`#guard_msgs (whitespace := lax) in cmd` 会在检查消息前折叠空白，
    而 `#guard_msgs (ordering := sorted) in cmd` 会先按字典序对消息排序再进行检查。
  * [#3931](https://github.com/leanprover/lean4/pull/3931) 为 `#guard_msgs` 添加了忽略未使用变量的功能。
  * [#3912](https://github.com/leanprover/lean4/pull/3912) 添加了期望输出与实际输出之间的 diff。该特性当前默认关闭，但可通过 `set_option guard_msgs.diff true` 启用。
    根据用户反馈，该选项未来版本可能默认设为 `true`。
* `do` **记法**
  * [#3820](https://github.com/leanprover/lean4/pull/3820) 现在将 `(<- ...)` 从纯 `if ... then ... else ...` 中提取出来视为错误
* **惰性判别树**
  * [#3610](https://github.com/leanprover/lean4/pull/3610) 修复了 `LazyDiscrTree` 的命名冲突，该问题可能导致缓存污染。
  * [#3677](https://github.com/leanprover/lean4/pull/3677) 简化并修复了 `LazyDiscrTree` 在 `exact?`/`apply?` 中的处理。
  * [#3685](https://github.com/leanprover/lean4/pull/3685) 将通用的 `exact?`/`apply?` 功能迁入 `LazyDiscrTree`。
  * [#3769](https://github.com/leanprover/lean4/pull/3769) 改进了 `rw?` 和 `LazyDiscrTree` 的引理选择。
  * [#3818](https://github.com/leanprover/lean4/pull/3818) 改进了匹配的排序。
* [#3590](https://github.com/leanprover/lean4/pull/3590) 添加了 `inductive.autoPromoteIndices` 选项，以便在 `inductive` 命令中禁用索引自动提升。
* **杂项错误修复与改进**
  * [#3606](https://github.com/leanprover/lean4/pull/3606) 在 `Lean.Meta.Simp.Result.mkEqSymm` 中保留了 `cache` 和 `dischargeDepth` 字段。
  * [#3633](https://github.com/leanprover/lean4/pull/3633) 让 `elabTermEnsuringType` 尊重 `errToSorry`，改进了 `have` 策略的错误恢复。
  * [#3647](https://github.com/leanprover/lean4/pull/3647) 允许 `noncomputable unsafe` 定义，以便把实现延后。
  * [#3672](https://github.com/leanprover/lean4/pull/3672) 调整了策略的命名空间。
  * [#3725](https://github.com/leanprover/lean4/pull/3725) 修复了带未使用分支的索引归纳类型的 `Ord` deriving 处理器。
  * [#3893](https://github.com/leanprover/lean4/pull/3893) 提升了自动派生 `Ord` 实例的性能。
  * [#3771](https://github.com/leanprover/lean4/pull/3771) 修改了策略宏失败时的错误报告，并改进了 `rfl` 的错误消息。
  * [#3745](https://github.com/leanprover/lean4/pull/3745) 修复了当字段记法的对象是可选参数时，广义字段记法的精译。
  * [#3799](https://github.com/leanprover/lean4/pull/3799) 让诸如 `universe`、`variable`、`namespace` 等命令要求其参数出现在更靠后的列中。
    那些可选解析 `ident` 或可解析任意多个 `ident` 的命令通常都应要求 `ident` 使用 `colGt`。
    这可避免把命令中的拼写错误误解释成标识符。
  * [#3815](https://github.com/leanprover/lean4/pull/3815) 让 `split` 策略可用于编写代码。
  * [#3822](https://github.com/leanprover/lean4/pull/3822) 为 `induction` 策略中形如 `| cstr a b c => ?_` 的 `with` 子句补充了缺失信息。
  * [#3806](https://github.com/leanprover/lean4/pull/3806) 修复了 `withSetOptionIn` 组合子。
  * [#3844](https://github.com/leanprover/lean4/pull/3844) 移除了未使用的 `trace.Elab.syntax` 选项。
  * [#3896](https://github.com/leanprover/lean4/pull/3896) 改进了 `attribute` 命令的悬停与跳转到定义。
  * [#3989](https://github.com/leanprover/lean4/pull/3989) 让 linter 选项更容易被发现。
  * [#3916](https://github.com/leanprover/lean4/pull/3916) 修复了用 `@[builtin_term_parser]` 定义的语法的跳转到定义。
  * [#3962](https://github.com/leanprover/lean4/pull/3962) 修复了 `solveByElim` 对 `symm` 引理的处理，使 `exact?`/`apply?` 再次可用。
  * [#3968](https://github.com/leanprover/lean4/pull/3968) 改进了 `@[deprecated]` 属性，新增 `(since := "<date>")` 字段。
  * [#3768](https://github.com/leanprover/lean4/pull/3768) 让 `#print` 命令显示结构体字段。
  * [#3974](https://github.com/leanprover/lean4/pull/3974) 让 `exact?%` 的行为更像 `by exact?` 而不是 `by apply?`。
  * [#3994](https://github.com/leanprover/lean4/pull/3994) 让 `he ▸ h` 记法的精译更可预测。
  * [#3991](https://github.com/leanprover/lean4/pull/3991) 调整了 `decreasing_trivial` 宏的透明性。
  * [#4092](https://github.com/leanprover/lean4/pull/4092) 提升了 `binop%` 与 `binrel%` 表达式树精译器的性能。
* **文档：** [#3748](https://github.com/leanprover/lean4/pull/3748), [#3796](https://github.com/leanprover/lean4/pull/3796),
  [#3800](https://github.com/leanprover/lean4/pull/3800), [#3874](https://github.com/leanprover/lean4/pull/3874),
  [#3863](https://github.com/leanprover/lean4/pull/3863), [#3862](https://github.com/leanprover/lean4/pull/3862),
  [#3891](https://github.com/leanprover/lean4/pull/3891), [#3873](https://github.com/leanprover/lean4/pull/3873),
  [#3908](https://github.com/leanprover/lean4/pull/3908), [#3872](https://github.com/leanprover/lean4/pull/3872)。

### 语言服务器与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Language-server-and-IDE-extensions"
%%%

* [#3602](https://github.com/leanprover/lean4/pull/3602) 启用了 `import` 自动补全。
* [#3608](https://github.com/leanprover/lean4/pull/3608) 修复了问题 [leanprover/vscode-lean4#392](https://github.com/leanprover/vscode-lean4/issues/392)。
  诊断范围存在 off-by-one 错误，例如会把目标状态放错位置。
* [#3014](https://github.com/leanprover/lean4/pull/3014) 引入了快照树，这是增量策略与并行化的基础工作。
  [#3849](https://github.com/leanprover/lean4/pull/3849) 添加了基础增量 API。
* [#3271](https://github.com/leanprover/lean4/pull/3271) 添加了对 server-to-client 请求的支持。
* [#3656](https://github.com/leanprover/lean4/pull/3656) 修复了当不同文件存在冲突名称时的跳转到定义。
  修复了问题 [#1170](https://github.com/leanprover/lean4/issues/1170)。
* [#3691](https://github.com/leanprover/lean4/pull/3691), [#3925](https://github.com/leanprover/lean4/pull/3925),
  [#3932](https://github.com/leanprover/lean4/pull/3932) 让语义 token（用于语义高亮）保持同步，并改进了性能。
* [#3247](https://github.com/leanprover/lean4/pull/3247) 和 [#3730](https://github.com/leanprover/lean4/pull/3730)
  添加了这样的诊断：当文件依赖被保存时，提示执行 “Restart File”。
* [#3722](https://github.com/leanprover/lean4/pull/3722) 在显示引用时使用正确的模块名。
* [#3728](https://github.com/leanprover/lean4/pull/3728) 让头部中的错误稳定显示，并将 “Import out of date” 警告的严重级别设为 “hint”。
  [#3739](https://github.com/leanprover/lean4/pull/3739) 简化了该警告的文本。
* [#3778](https://github.com/leanprover/lean4/pull/3778) 修复了 [#3462](https://github.com/leanprover/lean4/issues/3462)，
  即会使用光标之前的信息节点来计算补全的问题。
* [#3985](https://github.com/leanprover/lean4/pull/3985) 让跟踪计时显示在 Infoview 中。

### 漂亮打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Pretty-printing"
%%%

* [#3797](https://github.com/leanprover/lean4/pull/3797) 修复了对 binder 的悬停，使其显示类型。
* [#3640](https://github.com/leanprover/lean4/pull/3640) 和 [#3735](https://github.com/leanprover/lean4/pull/3735)：添加了属性 `@[pp_using_anonymous_constructor]`，使结构体被漂亮打印为 `⟨x, y, z⟩`
  而不是 `{a := x, b := y, c := z}`。
  该属性已应用于 `Sigma`、`PSigma`、`PProd`、`Subtype`、`And` 和 `Fin`。
* [#3749](https://github.com/leanprover/lean4/pull/3749)
  结构体实例现在会以内联父结构字段的方式进行漂亮打印。
  也就是说，如果 `B` 扩展了 `A`，那么 `{ toA := { x := 1 }, y := 2 }` 现在会被漂亮打印为 `{ x := 1, y := 2 }`。
  将选项 `pp.structureInstances.flatten` 设为 false 可关闭此行为。
* [#3737](https://github.com/leanprover/lean4/pull/3737), [#3744](https://github.com/leanprover/lean4/pull/3744)
  和 [#3750](https://github.com/leanprover/lean4/pull/3750)：
  选项 `pp.structureProjections` 已重命名为 `pp.fieldNotation`，并新增子选项 `pp.fieldNotation.generalized`
  以启用使用广义字段记法对函数应用进行漂亮打印（默认开启）。
  字段记法可通过 `@[pp_nodot]` 属性在单个函数上禁用。
  该记法不会用于定理。
* [#4071](https://github.com/leanprover/lean4/pull/4071) 修复了 app unexpanders 与 `pp.fieldNotation.generalized` 之间的交互
* [#3625](https://github.com/leanprover/lean4/pull/3625) 让 `delabConstWithSignature`（由 `#check` 使用）能够把参数放到“冒号后面”，以避免打印不可访问名称。
* [#3798](https://github.com/leanprover/lean4/pull/3798),
  [#3978](https://github.com/leanprover/lean4/pull/3978),
  [#3798](https://github.com/leanprover/lean4/pull/3980)：
  新增选项 `pp.mvars`（默认：true）和 `pp.mvars.withType`（默认：false）。
  当 `pp.mvars` 为 false 时，表达式元变量会被漂亮打印为 `?_`，宇宙元变量会被漂亮打印为 `_`。
  当 `pp.mvars.withType` 为 true 时，表达式元变量会带类型标注进行漂亮打印。
  在使用 `#guard_msgs` 时可设置这些选项，使测试不依赖元变量的具体名字。
* [#3917](https://github.com/leanprover/lean4/pull/3917) 让 binder 可悬停，并为其提供文档字符串。
* [#4034](https://github.com/leanprover/lean4/pull/4034) 让 Infoview 中 `match` 表达式右侧项的悬停信息能够稳定显示正确项。

### 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Library"
%%%

* `Bool`/`Prop`
  * [#3508](https://github.com/leanprover/lean4/pull/3508) 改进了 `Bool` 与 `Prop` 项上的 `simp` 合流性。
  * 定理：[#3604](https://github.com/leanprover/lean4/pull/3604)
* `Nat`
  * [#3579](https://github.com/leanprover/lean4/pull/3579) 现在由于 `induction`/`cases` 使用 `n + 1` 而不是 `Nat.succ n`，将 `Nat.succ_eq_add_one` 设为 simp 引理。
  * [#3808](https://github.com/leanprover/lean4/pull/3808) 用 simproc 取代了 `Nat.succ` 的 simp 规则。
  * [#3876](https://github.com/leanprover/lean4/pull/3876) 添加了更快的 C 实现 `Nat.repr`。
* `Int`
  * 定理：[#3890](https://github.com/leanprover/lean4/pull/3890)
* `UInt`s
  * [#3960](https://github.com/leanprover/lean4/pull/3960) 提升了向上类型转换的性能。
* `Array` 和 `Subarray`
  * [#3676](https://github.com/leanprover/lean4/pull/3676) 移除了 `Array.eraseIdxAux`、`Array.eraseIdxSzAux` 和 `Array.eraseIdx'`。
  * [#3648](https://github.com/leanprover/lean4/pull/3648) 简化了 `Array.findIdx?`。
  * [#3851](https://github.com/leanprover/lean4/pull/3851) 重命名了 `Subarray` 的字段。
* `List`
  * [#3785](https://github.com/leanprover/lean4/pull/3785) 将尾递归的 List 操作和 `@[csimp]` 引理上游化。
* `BitVec`
  * 定理：[#3593](https://github.com/leanprover/lean4/pull/3593),
  [#3593](https://github.com/leanprover/lean4/pull/3593), [#3597](https://github.com/leanprover/lean4/pull/3597),
  [#3598](https://github.com/leanprover/lean4/pull/3598), [#3721](https://github.com/leanprover/lean4/pull/3721),
  [#3729](https://github.com/leanprover/lean4/pull/3729), [#3880](https://github.com/leanprover/lean4/pull/3880),
  [#4039](https://github.com/leanprover/lean4/pull/4039)。
  * [#3884](https://github.com/leanprover/lean4/pull/3884) 保护了 `Std.BitVec`。
* `String`
  * [#3832](https://github.com/leanprover/lean4/pull/3832) 修复了 `String.splitOn`。
  * [#3959](https://github.com/leanprover/lean4/pull/3959) 添加了 `String.Pos.isValid`。
  * [#3959](https://github.com/leanprover/lean4/pull/3959) UTF-8 字符串校验。
  * [#3961](https://github.com/leanprover/lean4/pull/3961) 添加了 UTF-8 编码和解码的模型实现。
* `IO`
  * [#4097](https://github.com/leanprover/lean4/pull/4097) 添加了 `IO.getTaskState`，用于返回任务是已完成、正在主动运行，还是在等待其他 Task 完成。

* **重构**
  * [#3605](https://github.com/leanprover/lean4/pull/3605) 减少了 `Init.Data.Nat` 和 `Init.Data.Int` 的导入。
  * [#3613](https://github.com/leanprover/lean4/pull/3613) 减少了 `Init.Omega.Int` 的导入。
  * [#3634](https://github.com/leanprover/lean4/pull/3634) 将 `Std.Data.Nat` 上游化，
    而 [#3635](https://github.com/leanprover/lean4/pull/3635) 将 `Std.Data.Int` 上游化。
  * [#3790](https://github.com/leanprover/lean4/pull/3790) 进一步减少了 `omega` 的导入。
  * [#3694](https://github.com/leanprover/lean4/pull/3694) 通过为 `GetElem` 接口扩展 `getElem!` 与 `getElem?`，简化了 `RBMap` 这类容器。
  * [#3865](https://github.com/leanprover/lean4/pull/3865) 重命名了 `Option.toMonad`（见下方破坏性变更）。
  * [#3882](https://github.com/leanprover/lean4/pull/3882) 将 `lexOrd` 与 `compareLex` 统一。
* **其他修复或改进**
  * [#3765](https://github.com/leanprover/lean4/pull/3765) 将 `Quotient.sound` 改为 `theorem`。
  * [#3645](https://github.com/leanprover/lean4/pull/3645) 修复了绝对路径情况下的 `System.FilePath.parent`。
  * [#3660](https://github.com/leanprover/lean4/pull/3660) `ByteArray.toUInt64LE!` 与 `ByteArray.toUInt64BE!` 之前是对调的。
  * [#3881](https://github.com/leanprover/lean4/pull/3881), [#3887](https://github.com/leanprover/lean4/pull/3887) 修复了 `HashMap.insertIfNew`、`HashSet.erase` 和 `HashMap.erase` 中的线性性问题。
    对 `HashMap.insertIfNew` 的修复还提升了 `import` 性能。
  * [#3830](https://github.com/leanprover/lean4/pull/3830) 确保了 `Parsec.many*Core` 的线性性。
  * [#3930](https://github.com/leanprover/lean4/pull/3930) 添加了 `FS.Stream.isTty` 字段。
  * [#3866](https://github.com/leanprover/lean4/pull/3866) 弃用了 `Option.toBool`，改用 `Option.isSome`。
  * [#3975](https://github.com/leanprover/lean4/pull/3975) 将来自 Std 的 `Data.List.Init` 与 `Data.Array.Init` 材料上游化。
  * [#3942](https://github.com/leanprover/lean4/pull/3942) 添加了若干实例，使 `ac_rfl` 在没有 Mathlib 的情况下也能工作。
  * [#4010](https://github.com/leanprover/lean4/pull/4010) 将 `Fin.induction` 改为使用结构归纳。
  * [02753f](https://github.com/leanprover/lean4/commit/02753f6e4c510c385efcbf71fa9a6bec50fce9ab)
    修复了 `reduceLeDiff` simproc 中的一个错误。
  * [#4097](https://github.com/leanprover/lean4/pull/4097)
    添加了 `IO.TaskState` 和 `IO.getTaskState`，以便从 Lean 运行时的任务管理器获取任务状态。
* **文档：** [#3615](https://github.com/leanprover/lean4/pull/3615), [#3664](https://github.com/leanprover/lean4/pull/3664),
  [#3707](https://github.com/leanprover/lean4/pull/3707), [#3734](https://github.com/leanprover/lean4/pull/3734),
  [#3868](https://github.com/leanprover/lean4/pull/3868), [#3861](https://github.com/leanprover/lean4/pull/3861),
  [#3869](https://github.com/leanprover/lean4/pull/3869), [#3858](https://github.com/leanprover/lean4/pull/3858),
  [#3856](https://github.com/leanprover/lean4/pull/3856), [#3857](https://github.com/leanprover/lean4/pull/3857),
  [#3867](https://github.com/leanprover/lean4/pull/3867), [#3864](https://github.com/leanprover/lean4/pull/3864),
  [#3860](https://github.com/leanprover/lean4/pull/3860), [#3859](https://github.com/leanprover/lean4/pull/3859),
  [#3871](https://github.com/leanprover/lean4/pull/3871), [#3919](https://github.com/leanprover/lean4/pull/3919)。

### Lean 内部机制
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Lean-internals"
%%%

* **Defeq 与 WHNF 算法**
  * [#3616](https://github.com/leanprover/lean4/pull/3616) 为化简 `Nat.rec` 表达式提供了更好的支持。
  * [#3774](https://github.com/leanprover/lean4/pull/3774) 为“非简单”WHNF 情形添加了跟踪。
  * [#3807](https://github.com/leanprover/lean4/pull/3807) 修复了一个 `isDefEq` 性能问题，现在会在惰性 delta 化简之后才尝试结构 eta。
  * [#3816](https://github.com/leanprover/lean4/pull/3816) 修复了 `.yesWithDeltaI` 的行为，以避免在化简投影时提升透明度级别。
  * [#3837](https://github.com/leanprover/lean4/pull/3837) 改进了 `isDefEq` 中的启发式。
  * [#3965](https://github.com/leanprover/lean4/pull/3965) 改进了对形如 `t.i =?= s.i` 约束的 `isDefEq`。
  * [#3977](https://github.com/leanprover/lean4/pull/3977) 改进了 `isDefEqProj`。
  * [#3981](https://github.com/leanprover/lean4/pull/3981) 添加了宇宙约束近似，以便用 `?v = u` 解出 `u =?= max u ?v`。
    这些近似只会在宇宙约束已经无法再推迟时应用。
  * [#4004](https://github.com/leanprover/lean4/pull/4004) 改进了类型类解析期间的 `isDefEqProj`。
  * [#4012](https://github.com/leanprover/lean4/pull/4012) 添加了 `backward.isDefEq.lazyProjDelta` 和 `backward.isDefEq.lazyWhnfCore` 向后兼容标志。
* **内核**
  * [#3966](https://github.com/leanprover/lean4/pull/3966) 移除了死代码。
  * [#4035](https://github.com/leanprover/lean4/pull/4035) 修复了 Lean 与 C++ 之间 `TheoremVal` 的不匹配。
* **判别树**
  * [423fed](https://github.com/leanprover/lean4/commit/423fed79a9de75705f34b3e8648db7e076c688d7)
    和 [3218b2](https://github.com/leanprover/lean4/commit/3218b25974d33e92807af3ce42198911c256ff1d)：
    简化了依赖/非依赖 pi 类型的处理。
* **类型类实例合成**
  * [#3638](https://github.com/leanprover/lean4/pull/3638) 会对合成出的实例做 eta 化简
  * [ce350f](https://github.com/leanprover/lean4/commit/ce350f348161e63fccde6c4a5fe1fd2070e7ce0f) 修复了一个线性性问题
  * [917a31](https://github.com/leanprover/lean4/commit/917a31f694f0db44d6907cc2b1485459afe74d49)
    通过对不包含元变量的子目标至多只考虑一个答案来提升性能。
    [#4008](https://github.com/leanprover/lean4/pull/4008) 添加了 `backward.synthInstance.canonInstances` 向后兼容标志。
* **定义处理**
  * [#3661](https://github.com/leanprover/lean4/pull/3661), [#3767](https://github.com/leanprover/lean4/pull/3767) 修改了自动生成的方程定理命名，
    改为使用后缀 `.eq_<idx>` 而不是 `._eq_<idx>`，并使用 `.eq_def` 而不是 `._unfold`。（见下方破坏性变更。）
    [#3675](https://github.com/leanprover/lean4/pull/3675) 添加了名字保留机制。
    [#3803](https://github.com/leanprover/lean4/pull/3803) 修复了命名空间内保留名字的解析，并修复了对 `match`er 声明和方程引理的处理。
  * [#3662](https://github.com/leanprover/lean4/pull/3662) 让嵌套在定理中的辅助定义在它们不是证明时变成 `def`。
  * [#4006](https://github.com/leanprover/lean4/pull/4006) 让 `structure` 中的命题字段变成定理。
  * [#4018](https://github.com/leanprover/lean4/pull/4018) 现在将定理声明为 `extern` 视为错误。
  * [#4047](https://github.com/leanprover/lean4/pull/4047) 提升了为良基递归定义生成方程时的性能。
* **重构**
  * [#3614](https://github.com/leanprover/lean4/pull/3614) 避免了在 `Lean.Meta.evalNat` 中展开。
  * [#3621](https://github.com/leanprover/lean4/pull/3621) 将 `Fix`/`GuessLex`/`FunInd` 的功能集中到 `ArgsPacker` 模块中。
  * [#3186](https://github.com/leanprover/lean4/pull/3186) 重写了 UnusedVariable linter 以提升性能。
  * [#3589](https://github.com/leanprover/lean4/pull/3589) 移除了从 `String` 到 `Name` 的强制转换（见下方破坏性变更）。
  * [#3237](https://github.com/leanprover/lean4/pull/3237) 从 `FileMap` 中移除了 `lines` 字段。
  * [#3951](https://github.com/leanprover/lean4/pull/3951) 让 `throwTacticEx` 的 msg 参数变为可选。
* **诊断**
  * [#4016](https://github.com/leanprover/lean4/pull/4016), [#4019](https://github.com/leanprover/lean4/pull/4019),
    [#4020](https://github.com/leanprover/lean4/pull/4020), [#4030](https://github.com/leanprover/lean4/pull/4030),
    [#4031](https://github.com/leanprover/lean4/pull/4031),
    [c3714b](https://github.com/leanprover/lean4/commit/c3714bdc6d46845c0428735b283c5b48b23cbcf7),
    [#4049](https://github.com/leanprover/lean4/pull/4049) 为 `set_option diagnostics true` 添加了诊断计数器。
    它会跟踪已展开声明数、实例数、可约声明数、已使用实例数、递归子化简次数、
    `isDefEq` 启发式应用次数等。
    该选项建议在一些特殊情形下使用，例如确定性超时和最大递归深度时。
  * [283587](https://github.com/leanprover/lean4/commit/283587987ab2eb3b56fbc3a19d5f33ab9e04a2ef)
    为 `simp` 添加了诊断信息。
  * [#4043](https://github.com/leanprover/lean4/pull/4043) 为 congruence 定理添加了诊断信息。
  * [#4048](https://github.com/leanprover/lean4/pull/4048) 为
    `set_option diagnostics true in <tactic>` 和 `set_option diagnostics true in <term>`
    显示诊断信息。
* **其他特性**
  * [#3800](https://github.com/leanprover/lean4/pull/3800) 添加了环境扩展，用于记录哪些定义使用结构递归或良基递归。
  * [#3801](https://github.com/leanprover/lean4/pull/3801) `trace.profiler` 现在可以导出到 Firefox Profiler。
  * [#3918](https://github.com/leanprover/lean4/pull/3918), [#3953](https://github.com/leanprover/lean4/pull/3953) 添加了 `@[builtin_doc]` 属性，使声明的文档和位置可作为内建信息使用。
  * [#3939](https://github.com/leanprover/lean4/pull/3939) 添加了 `lean --json` CLI 选项，以 JSON 输出消息。
  * [#3075](https://github.com/leanprover/lean4/pull/3075) 改进了 `test_extern` 命令。
  * [#3970](https://github.com/leanprover/lean4/pull/3970) 给出了 `FindExpr` 的单子化泛化。
* **文档：** [#3743](https://github.com/leanprover/lean4/pull/3743), [#3921](https://github.com/leanprover/lean4/pull/3921),
  [#3954](https://github.com/leanprover/lean4/pull/3954)。
* **其他修复：** [#3622](https://github.com/leanprover/lean4/pull/3622),
  [#3726](https://github.com/leanprover/lean4/pull/3726), [#3823](https://github.com/leanprover/lean4/pull/3823),
  [#3897](https://github.com/leanprover/lean4/pull/3897), [#3964](https://github.com/leanprover/lean4/pull/3964),
  [#3946](https://github.com/leanprover/lean4/pull/3946), [#4007](https://github.com/leanprover/lean4/pull/4007),
  [#4026](https://github.com/leanprover/lean4/pull/4026)。

### 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Compiler___-runtime___-and-FFI"
%%%

* [#3632](https://github.com/leanprover/lean4/pull/3632) 让那些不是由 Lean 自身启动的线程也能分配和释放线程局部运行时资源。
* [#3627](https://github.com/leanprover/lean4/pull/3627) 改进了关于压缩闭包（compacting closures）的错误消息。
* [#3692](https://github.com/leanprover/lean4/pull/3692) 修复了 `IO.Promise.resolve` 中的死锁。
* [#3753](https://github.com/leanprover/lean4/pull/3753) 在 Windows 上捕获 `MoveFileEx` 的错误码。
* [#4028](https://github.com/leanprover/lean4/pull/4028) 修复了 `ResetReuse` 变换中的双重 `reset` 错误。
* [6e731b](https://github.com/leanprover/lean4/commit/6e731b4370000a8e7a5cfb675a7f3d7635d21f58)
  移除了 `interpreter` 的复制构造函数，以避免潜在的内存安全问题。

### Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Lake"
%%%

* **TOML Lake 配置。** [#3298](https://github.com/leanprover/lean4/pull/3298), [#4104](https://github.com/leanprover/lean4/pull/4104)。

  Lake 包现在可以使用 TOML 作为 Lean 之外的另一种配置文件格式。如果默认的 `lakefile.lean` 缺失，Lake 也会查找 `lakefile.toml`。TOML 版本的配置支持 Lake 配置选项中的一个受限子集，只包含那些能够较容易映射到 TOML 数据结构的部分。TOML 语法本身则完全符合 TOML v1.0.0 规范。

  作为这项新特性引入的一部分，我们一直在帮助生态中一些重要包的维护者迁移到这种格式。例如，下面就是 Aesop 的新 `lakefile.toml`：


  **[leanprover-community/aesop/lakefile.toml](https://raw.githubusercontent.com/leanprover-community/aesop/de11e0ecf372976e6d627c210573146153090d2d/lakefile.toml)**
  ```toml
  name = "aesop"
  defaultTargets = ["Aesop"]
  testRunner = "test"
  precompileModules = false

  [[require]]
  name = "batteries"
  git = "https://github.com/leanprover-community/batteries"
  rev = "main"

  [[lean_lib]]
  name = "Aesop"

  [[lean_lib]]
  name = "AesopTest"
  globs = ["AesopTest.+"]
  leanOptions = {linter.unusedVariables = false}

  [[lean_exe]]
  name = "test"
  srcDir = "scripts"
  ```

  为帮助希望在两种配置文件格式之间迁移包配置的用户，现在还新增了 `lake translate-config` 命令。

  运行 `lake translate-config toml` 会为某个包的 `lakefile.lean` 生成对应的 `lakefile.toml`。任何 TOML 格式不支持的配置选项都会在翻译过程中被丢弃，但原始 `lakefile.lean` 会被保留，以便你在删除它之前检查翻译结果是否合理。

* **构建进度重构。** [#3835](https://github.com/leanprover/lean4/pull/3835), [#4115](https://github.com/leanprover/lean4/pull/4115), [#4127](https://github.com/leanprover/lean4/pull/4127), [#4220](https://github.com/leanprover/lean4/pull/4220), [#4232](https://github.com/leanprover/lean4/pull/4232), [#4236](https://github.com/leanprover/lean4/pull/4236)。

  构建现在由顶层的 Lake 构建监视器统一管理，这使 Lake 构建的输出更加标准化，并且能够生成更美观、可配置性更高的进度报告。

  作为这一改动的一部分，任务隔离得到了改善。自定义 target 中游离的 I/O 以及其他构建相关错误现在都能被正确隔离，并作为其自身任务的一部分被捕获。导入错误也不再导致 Lake 中止整个构建，而是会被局限在对应模块的构建任务中。

  Lake 现在还会使用 ANSI 转义序列添加颜色，并生成可原位更新的进度行；可以用 `--ansi` / `--no-ansi` 来打开或关闭这一行为。


  新增了 `--wfail` 和 `--iofail` 选项：如果任何任务记录了警告（`--wfail`），或者输出/记录了任何信息消息（`--iofail`），就会让构建失败。与某些其他构建系统不同，这些选项**不会**把这些日志转换成错误，Lake 也不会因为这种日志而中止任务（也就是说，依赖它的任务仍会继续执行，不受影响）。

* `lake test`。 [#3779](https://github.com/leanprover/lean4/pull/3779)。

  Lake 现在内置了 `test` 命令，它会运行根包中标记为 `@[test_runner]`（Lean 中）或定义为 `testRunner`（TOML 中）的脚本或可执行文件。

  Lake 还提供了 `lake check-test` 命令：若包已正确配置测试运行器，它会以退出码 `0` 退出，否则报错并以 `1` 退出。

* `lake lean`。 [#3793](https://github.com/leanprover/lean4/pull/3793)。

  新命令 `lake lean <file> [-- <args...>]` 的作用类似于 `lake env lean <file> <args...>`，不同之处在于它会在运行 `lean` 前先构建 `file` 的导入。这使得它非常适合运行那些导入了尚未保证事先构建好的模块的测试或示例代码。

* **杂项错误修复与改进**
  * [#3609](https://github.com/leanprover/lean4/pull/3609) 新增 `LEAN_GITHASH` 环境变量，可在计算 trace 时覆盖为 Lean 检测到的 Git 哈希，这对于测试 Lean 的自定义构建很有用。
  * [#3795](https://github.com/leanprover/lean4/pull/3795) 改进了重命名前检查中的相对包目录路径规范化。
  * [#3957](https://github.com/leanprover/lean4/pull/3957) 修复了依赖树中同一个包出现多次时的处理。
  * [#3999](https://github.com/leanprover/lean4/pull/3999) 现在如果包名与其被 require 的名称不匹配就会报错。还为 `std` 到 `batteries` 的重命名添加了专门的提示消息。
  * [#4033](https://github.com/leanprover/lean4/pull/4033) 修复了 quiet 模式。
* **文档：** [#3704](https://github.com/leanprover/lean4/pull/3704)。

### DevOps
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--DevOps"
%%%

* [#3536](https://github.com/leanprover/lean4/pull/3536) 和 [#3833](https://github.com/leanprover/lean4/pull/3833)
  为发布流程添加了检查清单。
* [#3600](https://github.com/leanprover/lean4/pull/3600) 让 nix-ci 的运行方式更加统一。
* [#3612](https://github.com/leanprover/lean4/pull/3612) 避免了在 Windows 上构建时触及参数数量限制。
* [#3682](https://github.com/leanprover/lean4/pull/3682) 让 Lean 的 `.o` 文件与核心其余部分并行构建。
* [#3601](https://github.com/leanprover/lean4/pull/3601)
  修改了 Lean 在 Windows 上的构建方式（见下方破坏性变更）。
  因此，Lake 现在会在 Windows 上为 `supportInterpreter := true` 的可执行文件动态链接 `libleanshared.dll` 和 `libInit_shared.dll`。
  因而，除非这些共享库与可执行文件放在同一目录，或位于 `PATH` 中，否则此类可执行文件将无法运行。
  通过 `lake exe` 运行可执行文件会确保这些库位于 `PATH` 中。

  与此相关的另一项变更是，Lake 配置选项 `nativeFacets` 的签名已从静态 `Array` 改为函数 `(shouldExport : Bool) → Array`。
  更多细节请参见其文档字符串或 Lake 的 [README](https://github.com/leanprover/lean4/blob/releases/v4.8.0/src/lake/README.md) 中关于该选项变更的说明。
* [#3690](https://github.com/leanprover/lean4/pull/3690) 在构建被取消时，将 “Build matrix complete” 标记为 canceled。
* [#3700](https://github.com/leanprover/lean4/pull/3700), [#3702](https://github.com/leanprover/lean4/pull/3702),
  [#3701](https://github.com/leanprover/lean4/pull/3701), [#3834](https://github.com/leanprover/lean4/pull/3834),
  [#3923](https://github.com/leanprover/lean4/pull/3923)：为 std 和 mathlib CI 提供修复与改进。
* [#3712](https://github.com/leanprover/lean4/pull/3712) 修复了 macOS 上的 `nix build .`。
* [#3717](https://github.com/leanprover/lean4/pull/3717) 在 devShell 中用 `flake.nix` 取代了 `shell.nix`。
* [#3715](https://github.com/leanprover/lean4/pull/3715) 和 [#3790](https://github.com/leanprover/lean4/pull/3790) 添加了测试结果摘要。
* [#3971](https://github.com/leanprover/lean4/pull/3971) 通过合并队列阻止了 stage0 变更。
* [#3979](https://github.com/leanprover/lean4/pull/3979) 添加了对 `changes-stage0` 标签的处理。
* [#3952](https://github.com/leanprover/lean4/pull/3952) 添加了一个脚本，用于汇总 GitHub issue。
* [18a699](https://github.com/leanprover/lean4/commit/18a69914da53dbe37c91bc2b9ce65e1dc01752b6)
  修复了 asan 链接

### 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___8___0-_LPAR_2024-06-05_RPAR_--Breaking-changes"
%%%

* 由于 Lake 构建的大规模重构，任何使用 Lake API 受影响部分的代码，或依赖 Lake 构建旧输出格式的代码，都很可能已经损坏。我们已尽力将破坏降到最低；在可能的情况下，旧定义已被标记为 `@[deprecated]`，并附带对新替代方案的引用。

* 在 Windows 上，配置了 `supportInterpreter := true` 的可执行文件现在应通过 `lake exe` 运行，才能正常工作。

* 自动生成的方程定理现在使用后缀 `.eq_<idx>` 命名，而不再是 `._eq_<idx>`；使用 `.eq_def` 命名，而不再是 `._unfold`。示例：
```
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem ex : fact 0 = 1 := by unfold fact; decide

#check fact.eq_1
-- fact.eq_1 : fact 0 = 1

#check fact.eq_2
-- fact.eq_2 (n : Nat) : fact (Nat.succ n) = (n + 1) * fact n

#check fact.eq_def
/-
fact.eq_def :
  ∀ (x : Nat),
    fact x =
      match x with
      | 0 => 1
      | Nat.succ n => (n + 1) * fact n
-/
```

* 从 `String` 到 `Name` 的强制转换已被移除。此前它等同于 `Name.mkSimple`，这不会按点号拆分字符串，但实践表明这并不总是想要的转换。若要恢复先前行为，请手动插入对 `Name.mkSimple` 的调用。

* `Subarray` 的字段 `as`、`h₁` 和 `h₂` 现已分别重命名为 `array`、`start_le_stop` 和 `stop_le_array_size`。这更符合 Lean 的标准约定。我们为字段投影添加了弃用别名；这些别名会在未来版本中移除。

* 实例命名算法的变更（如上所述）会破坏那些依赖自动生成名称的项目。

* `Option.toMonad` 已重命名为 `Option.getM`，并移除了不再需要的 `[Monad m]` 实例参数。

````
