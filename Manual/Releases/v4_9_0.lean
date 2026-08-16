/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.9.0 (2024-07-01)" =>
%%%
tag := "release-v4.9.0"
file := "v4.9.0"
%%%

````markdown
````
# 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

````markdown

* **定义透明性**
  * [#4053](https://github.com/leanprover/lean4/pull/4053) 新增了 `seal` 与 `unseal` 命令，使定义在局部范围内变为不可约或半可约。
  * [#4061](https://github.com/leanprover/lean4/pull/4061) 默认将通过良基递归定义的函数标记为 `@[irreducible]`，
    这应能阻止对此类定义进行代价高昂且往往无益的展开（见下方破坏性变更）。
* **增量化**
  * [#3940](https://github.com/leanprover/lean4/pull/3940) 将增量精译扩展到声明内部的多个步骤：
    定义头部、主体以及策略。

    [录屏](https://github.com/leanprover/lean4/assets/109126/c9d67b6f-c131-4bc3-a0de-7d63eaf1bfc9)。
  * [250994](https://github.com/leanprover/lean4/commit/250994166ce036ab8644e459129f51ea79c1c2d2)
    和 [67338b](https://github.com/leanprover/lean4/commit/67338bac2333fa39a8656e8f90574784e4c23d3d)
    添加了 `@[incremental]` 属性，用于标记某个精译器支持增量精译。
  * [#4259](https://github.com/leanprover/lean4/pull/4259) 通过确保仅以受支持的方式进入增量命令与策略，提高了稳健性。
  * [#4268](https://github.com/leanprover/lean4/pull/4268) 为 `:= by` 添加了特殊处理，使策略块中的游离 token 不会妨碍增量化。
  * [#4308](https://github.com/leanprover/lean4/pull/4308) 为 `have` 策略加入增量支持。
  * [#4340](https://github.com/leanprover/lean4/pull/4340) 修复了错误复用信息树的问题。
  * [#4364](https://github.com/leanprover/lean4/pull/4364) 为一些谨慎型命令宏加入增量支持，例如 `set_option in theorem`、`theorem foo.bar` 和 `lemma`。
  * [#4395](https://github.com/leanprover/lean4/pull/4395) 为空白字符处理加入了保守修复，以避免增量复用导致显示文本光标前方的目标。
  * [#4407](https://github.com/leanprover/lean4/pull/4407) 修复了宏中的非增量命令会阻塞后续增量报告的问题。
  * [#4436](https://github.com/leanprover/lean4/pull/4436) 修复了项中嵌套策略时的增量报告。
  * [#4459](https://github.com/leanprover/lean4/pull/4459) 为 `next` 与 `if` 策略加入增量支持。
  * [#4554](https://github.com/leanprover/lean4/pull/4554) 禁用了“策略中的项里的策略”的增量化。
* **函数归纳**
  * [#4135](https://github.com/leanprover/lean4/pull/4135) 确保函数归纳所使用的名字会被保留。
  * [#4327](https://github.com/leanprover/lean4/pull/4327) 新增了对反身类型上结构递归的支持。
    例如，
    ```lean4
    inductive Many (α : Type u) where
      | none : Many α
      | more : α → (Unit → Many α) → Many α

    def Many.map {α β : Type u} (f : α → β) : Many α → Many β
      | .none => .none
      | .more x xs => .more (f x) (fun _ => (xs ()).map f)

    #check Many.map.induct
    /-
    Many.map.induct {α β : Type u} (f : α → β) (motive : Many α → Prop)
      (case1 : motive Many.none)
      (case2 : ∀ (x : α) (xs : Unit → Many α), motive (xs ()) → motive (Many.more x xs)) :
      ∀ (a : Many α), motive a
    -/
    ```
* [#3903](https://github.com/leanprover/lean4/pull/3903) 让 Lean 前端在处理前将所有行尾规范化为 LF。
  这让 Lean 不再区分 CRLF 与 LF 行尾，提升了跨平台体验，也让 Lake 的哈希真正对应 Lean 实际处理的内容。
* [#4130](https://github.com/leanprover/lean4/pull/4130) 让策略框架能够从运行时错误中恢复（例如确定性超时或最大递归深度错误）。
* `split` 策略
  * [#4211](https://github.com/leanprover/lean4/pull/4211) 修复了当 `h` 有前向依赖时的 `split at h`。
  * [#4349](https://github.com/leanprover/lean4/pull/4349) 让用于 `if` 表达式的 `split` 可以作用于非命题目标。
* `apply` 策略
  * [#3929](https://github.com/leanprover/lean4/pull/3929) 让 `apply` 的错误消息在需要时显示合一错误中的隐式参数。
    这修改了 `MessageData` 类型（见下方破坏性变更）。
* `cases` 策略
  * [#4224](https://github.com/leanprover/lean4/pull/4224) 为 `cases` 策略加入了对 `x + 20000 = 20001` 这类偏移量合一的支持。
* `omega` 策略
  * [#4073](https://github.com/leanprover/lean4/pull/4073) 让 `omega` 在构造矛盾证明时可回退为使用经典 `Decidable` 实例。
  * [#4141](https://github.com/leanprover/lean4/pull/4141) 和 [#4184](https://github.com/leanprover/lean4/pull/4184) 修复了错误。
  * [#4264](https://github.com/leanprover/lean4/pull/4264) 在局部上下文中找不到事实时，改进了 `omega` 的错误消息。
  * [#4358](https://github.com/leanprover/lean4/pull/4358) 通过使用 `match_expr` 改进了 `omega` 中的表达式匹配。
* `simp` 策略
  * [#4176](https://github.com/leanprover/lean4/pull/4176) 让被擦除引理的名字可以点击。
  * [#4208](https://github.com/leanprover/lean4/pull/4208) 为判别树键添加了漂亮打印器。
  * [#4202](https://github.com/leanprover/lean4/pull/4202) 新增 `Simp.Config.index` 配置选项，
    用于控制在选择候选 simp 引理时是否使用完整的判别树。
    当 `index := false` 时，只考虑头函数，与 Lean 3 相同。
    这一特性可以帮助用户诊断棘手的 simp 失败，或诊断那些先用 Lean 3 开发、后移植到 Lean 4 的库代码中的问题。

    在下面的示例中，它会报告 `foo` 是一个有问题的定理。
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (x, y).2 = y := by sorry

    example : f a b ≤ b := by
      set_option diagnostics true in
      simp (config := { index := false })
    /-
    [simp] theorems with bad keys
      foo, key: f _ (@Prod.mk ℕ ℕ _ _).2
    -/
    ```
    有了上述信息，用户就可以对 `foo` 这样的定理，在有问题的子项上使用 `no_index` 进行标注。示例：
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (no_index (x, y).2) = y := by sorry

    example : f a b ≤ b := by
      simp -- `foo` is still applied with `index := true`
    ```
  * [#4274](https://github.com/leanprover/lean4/pull/4274) 防止内部 `match` 方程定理出现在 simp 跟踪中。
  * [#4177](https://github.com/leanprover/lean4/pull/4177) 和 [#4359](https://github.com/leanprover/lean4/pull/4359) 让 `simp` 在策略状态处于恢复模式时，即便某条 simp 引理无法精译，也能继续执行。
  * [#4341](https://github.com/leanprover/lean4/pull/4341) 修复了对格式错误的定理语法施加 `@[simp]` 时的 panic。
  * [#4345](https://github.com/leanprover/lean4/pull/4345) 修复了 `simp` 错误使用用户指定反向定理的正向版本的问题。
  * [#4352](https://github.com/leanprover/lean4/pull/4352) 为生成的 congruence 定理的固定参数补上了缺失的 `dsimp` 化简。
  * [#4362](https://github.com/leanprover/lean4/pull/4362) 改进了 `simp` 的跟踪消息，使其中的常量可以悬停。
* **精译**
  * [#4046](https://github.com/leanprover/lean4/pull/4046) 让 subst 记法（`he ▸ h`）即便在没有期望类型时，也会尝试双向重写。
  * [#3328](https://github.com/leanprover/lean4/pull/3328) 为 autoparam 中的标识符提供支持（例如 `(h : x = y := by exact rfl)` 中的 `rfl`）。
  * [#4096](https://github.com/leanprover/lean4/pull/4096) 修改了 `let` 和 `have` 中类型的精译方式，要求类型中的任何策略都必须先求值后再继续，从而提升性能。
  * [#4215](https://github.com/leanprover/lean4/pull/4215) 确保表达式树精译器会对整个算术表达式采用计算出的 “max type”。
  * [#4267](https://github.com/leanprover/lean4/pull/4267) 让 cases 签名的精译错误即便在主体存在解析错误时也会显示出来。
  * [#4368](https://github.com/leanprover/lean4/pull/4368) 改进了数值字面量无法合成 `OfNat` 实例时的错误消息，
    包括当该数值的期望类型可能是命题时给出专门的警告消息。
  * [#4643](https://github.com/leanprover/lean4/pull/4643) 修复了一个会导致嵌套错误消息和信息树消失的问题，其原因是在复用时没有恢复快照子树。
  * [#4657](https://github.com/leanprover/lean4/pull/4657) 按快照计算错误抑制，因此即便后面还有解析错误，精译错误也能显示出来（[RFC #3556](https://github.com/leanprover/lean4/issues/3556)）。
* **元编程**
  * [#4167](https://github.com/leanprover/lean4/pull/4167) 新增 `Lean.MVarId.revertAll`，用于回退所有自由变量。
  * [#4169](https://github.com/leanprover/lean4/pull/4169) 新增 `Lean.MVarId.ensureNoMVar`，用于确保目标的 target 中不含表达式元变量。
  * [#4180](https://github.com/leanprover/lean4/pull/4180) 为 `forallTelescope` 方法新增 `cleanupAnnotations` 参数。
  * [#4307](https://github.com/leanprover/lean4/pull/4307) 为语法引用中的解析器别名提供支持。
* 为实现 `grind` 策略所做的工作
  * [0a515e](https://github.com/leanprover/lean4/commit/0a515e2ec939519dafb4b99daa81d6bf3c411404)
    和 [#4164](https://github.com/leanprover/lean4/pull/4164)
    添加了 `grind_norm` 与 `grind_norm_proc` 属性，以及 `@[grind_norm]` 定理。
  * [#4170](https://github.com/leanprover/lean4/pull/4170), [#4221](https://github.com/leanprover/lean4/pull/4221),
    和 [#4249](https://github.com/leanprover/lean4/pull/4249) 创建了 `grind` 预处理器与核心模块。
  * [#4235](https://github.com/leanprover/lean4/pull/4235) 和 [d6709e](https://github.com/leanprover/lean4/commit/d6709eb1576c5d40fc80462637dc041f970e4d9f)
    为 `grind` 添加了专用 `cases` 策略，并新增 `@[grind_cases]` 属性，用于标记哪些类型应自动应用该 `cases` 策略。
  * [#4243](https://github.com/leanprover/lean4/pull/4243) 为 `grind` 添加了专用 `injection?` 策略。
* **其他修复或改进**
  * [#4065](https://github.com/leanprover/lean4/pull/4065) 修复了 `Nat.reduceLeDiff` simproc 中的一个错误。
  * [#3969](https://github.com/leanprover/lean4/pull/3969) 让弃用警告即便在广义字段记法（“点记法”）中也会生效。
  * [#4132](https://github.com/leanprover/lean4/pull/4132) 修复了 `sorry` 项会激活隐式 lambda 特性的问题
  * [9803c5](https://github.com/leanprover/lean4/commit/9803c5dd63dc993628287d5f998525e74af03839)
    和 [47c8e3](https://github.com/leanprover/lean4/commit/47c8e340d65b01f4d9f011686e3dda0d4bb30a20)
    将 `cdot` 与 `calc` 解析器移动到 `Lean` 命名空间。
  * [#4252](https://github.com/leanprover/lean4/pull/4252) 修复了 `case` 策略，使其通过擦除 tag 上的宏作用域而可在宏中使用。
  * [26b671](https://github.com/leanprover/lean4/commit/26b67184222e75529e1b166db050aaebee323d2d)
    和 [cc33c3](https://github.com/leanprover/lean4/commit/cc33c39cb022d8a3166b1e89677c78835ead1fc7)
    提取出了 `haveId` 语法。
  * [#4335](https://github.com/leanprover/lean4/pull/4335) 修复了部分 `calc` 策略在存在 mdata 或元变量时的错误。
  * [#4329](https://github.com/leanprover/lean4/pull/4329) 让 `termination_by?` 将每个未使用参数都报告为 `_`。
* **文档：** [#4238](https://github.com/leanprover/lean4/pull/4238), [#4294](https://github.com/leanprover/lean4/pull/4294),
  [#4338](https://github.com/leanprover/lean4/pull/4338).

````
# 语言服务器、小部件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

````markdown
* [#4066](https://github.com/leanprover/lean4/pull/4066) 修复了浏览 Lean 核心源码时 “Find References” 等功能的问题。
* [#4254](https://github.com/leanprover/lean4/pull/4254) 允许在结构化消息中嵌入用户小部件。
  配套 PR 为 [vscode-lean4#449](https://github.com/leanprover/vscode-lean4/pull/449)。
* [#4445](https://github.com/leanprover/lean4/pull/4445) 让 watchdog 在面对行为不良的客户端时更加稳健。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Library"
%%%

````markdown
* [#4059](https://github.com/leanprover/lean4/pull/4059) 将来自 Batteries 的许多 `List` 与 `Array` 操作和定理上游化。
* [#4055](https://github.com/leanprover/lean4/pull/4055) 移除了 `Subtype` 上未使用的 `Inhabited` 实例。
* [#3967](https://github.com/leanprover/lean4/pull/3967) 为现有 `@[deprecated]` 属性添加了日期。
* [#4231](https://github.com/leanprover/lean4/pull/4231) 为 `Char`、`UInt` 与 `Fin` 添加了样板定理。
* [#4205](https://github.com/leanprover/lean4/pull/4205) 修复了 `MonadStore` 类型类，使其使用 `semiOutParam`。
* [#4350](https://github.com/leanprover/lean4/pull/4350) 将 `IsLawfulSingleton` 重命名为 `LawfulSingleton`。
* `Nat`
  * [#4094](https://github.com/leanprover/lean4/pull/4094) 交换了 `Nat.zero_or` 与 `Nat.or_zero`。
  * [#4098](https://github.com/leanprover/lean4/pull/4098) 和 [#4145](https://github.com/leanprover/lean4/pull/4145)
    修改了 `Nat.mod` 的定义，使得当 `n` 是字面量时，`n % (m + n)` 可以化简，而不依赖良基递归，
    后者在 [#4061](https://github.com/leanprover/lean4/pull/4061) 中默认会变为不可约。
  * [#4188](https://github.com/leanprover/lean4/pull/4188) 重新定义了 `Nat.testBit` 以提升性能。
  * 定理：[#4199](https://github.com/leanprover/lean4/pull/4199)。
* `Array`
  * [#4074](https://github.com/leanprover/lean4/pull/4074) 改进了函数归纳原理 `Array.feraseIdx.induct`。
* `List`
  * [#4172](https://github.com/leanprover/lean4/pull/4172) 从 `List.length_pos` 上移除了 `@[simp]`。
* `Option`
  * [#4037](https://github.com/leanprover/lean4/pull/4037) 添加了用于化简取值于 `Option` 的依赖 if-then-else 的定理。
  * [#4314](https://github.com/leanprover/lean4/pull/4314) 从 `Option.bind_eq_some` 上移除了 `@[simp]`。
* `BitVec`
  * 定理：[#3920](https://github.com/leanprover/lean4/pull/3920), [#4095](https://github.com/leanprover/lean4/pull/4095),
    [#4075](https://github.com/leanprover/lean4/pull/4075), [#4148](https://github.com/leanprover/lean4/pull/4148),
    [#4165](https://github.com/leanprover/lean4/pull/4165), [#4178](https://github.com/leanprover/lean4/pull/4178),
    [#4200](https://github.com/leanprover/lean4/pull/4200), [#4201](https://github.com/leanprover/lean4/pull/4201),
    [#4298](https://github.com/leanprover/lean4/pull/4298), [#4299](https://github.com/leanprover/lean4/pull/4299),
    [#4257](https://github.com/leanprover/lean4/pull/4257), [#4179](https://github.com/leanprover/lean4/pull/4179),
    [#4321](https://github.com/leanprover/lean4/pull/4321), [#4187](https://github.com/leanprover/lean4/pull/4187)。
  * [#4193](https://github.com/leanprover/lean4/pull/4193) 为 `x >>> i` 与 `x <<< i` 的化简添加了 simproc，其中 `i` 是位向量字面量。
  * [#4194](https://github.com/leanprover/lean4/pull/4194) 为 `(x <<< i) <<< j` 与 `(x >>> i) >>> j` 的化简添加了 simproc，其中 `i` 与 `j` 是自然数字面量。
  * [#4229](https://github.com/leanprover/lean4/pull/4229) 重新定义了 `rotateLeft`/`rotateRight`，使其对移位偏移先做按位宽取模。
  * [0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba) 将 `<num>#<term>` 位向量字面量记法改为全局可用。
* `Char`/`String`
  * [#4143](https://github.com/leanprover/lean4/pull/4143) 修改了 `String.substrEq`，以避免下游代码中的 linter 警告。
  * [#4233](https://github.com/leanprover/lean4/pull/4233) 为 `Char` 和 `String` 的不等式添加了 simproc。
  * [#4348](https://github.com/leanprover/lean4/pull/4348) 将 Mathlib 引理上游化。
  * [#4354](https://github.com/leanprover/lean4/pull/4354) 将基础 `String` 引理上游化。
* `HashMap`
  * [#4248](https://github.com/leanprover/lean4/pull/4248) 修复了 `HashMap.ofList` 中类型类参数的隐式性。
* `IO`
  * [#4036](https://github.com/leanprover/lean4/pull/4036) 新增 `IO.Process.getCurrentDir` 与 `IO.Process.setCurrentDir`，用于调整当前进程的工作目录。
* **清理：** [#4077](https://github.com/leanprover/lean4/pull/4077), [#4189](https://github.com/leanprover/lean4/pull/4189),
  [#4304](https://github.com/leanprover/lean4/pull/4304)。
* **文档：** [#4001](https://github.com/leanprover/lean4/pull/4001), [#4166](https://github.com/leanprover/lean4/pull/4166),
  [#4332](https://github.com/leanprover/lean4/pull/4332)。

````
# Lean 内部机制
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Lean-internals"
%%%

````markdown
* **Defeq 与 WHNF 算法**
  * [#4029](https://github.com/leanprover/lean4/pull/4029) 移除了不必要的 `checkpointDefEq`
  * [#4206](https://github.com/leanprover/lean4/pull/4206) 修复了 `isReadOnlyOrSyntheticOpaque`，使其遵守元变量深度。
  * [#4217](https://github.com/leanprover/lean4/pull/4217) 修复了延迟赋值中缺失的 occurs check。
* **定义透明性**
  * [#4052](https://github.com/leanprover/lean4/pull/4052) 为 `@[reducible]`/`@[semireducible]`/`@[irreducible]` 属性的应用添加了校验（也包括 `local`/`scoped` 修饰符）。
    设置 `set_option allowUnsafeReductibility true` 可关闭该校验。
* **归纳类型**
  * [#3591](https://github.com/leanprover/lean4/pull/3591) 修复了索引可能被错误提升为参数的问题。
  * [#3398](https://github.com/leanprover/lean4/pull/3398) 修复了单射性定理生成器中的一个错误。
  * [#4342](https://github.com/leanprover/lean4/pull/4342) 修复了带实例参数的互归纳类型的精译。
* **诊断与性能分析**
  * [#3986](https://github.com/leanprover/lean4/pull/3986) 添加了 `trace.profiler.useHeartbeats` 选项，用于把 `trace.profiler.threshold` 从按毫秒切换为按 heartbeat 计。
  * [#4082](https://github.com/leanprover/lean4/pull/4082) 让 `set_option diagnostics true` 会报告内核诊断信息。
* **类型类解析**
  * [#4119](https://github.com/leanprover/lean4/pull/4119) 修复了 TC 缓存与 `synthPendingDepth` 交互时的多个问题，并新增默认值为 `1` 的 `maxSynthPendingDepth` 选项。
  * [#4210](https://github.com/leanprover/lean4/pull/4210) 确保局部实例缓存中不会包含同一实例的多个副本。
  * [#4216](https://github.com/leanprover/lean4/pull/4216) 修复了元变量处理，以避免必须将选项 `backward.synthInstance.canonInstances` 设为 `false`。
* **其他修复或改进**
  * [#4080](https://github.com/leanprover/lean4/pull/4080) 修复了 `Lean.Elab.Command.liftCoreM` 和 `Lean.Elab.Command.liftTermElabM` 的状态传播。
  * [#3944](https://github.com/leanprover/lean4/pull/3944) 让 `Repr` deriving 处理器在 `structure` 与 `inductive` 中对类型和证明的擦除行为保持一致。
  * [#4113](https://github.com/leanprover/lean4/pull/4113) 将 `maxHeartbeats` 传递给内核，以控制 “(kernel) deterministic timeout” 错误。
  * [#4125](https://github.com/leanprover/lean4/pull/4125) 回退了 [#3970](https://github.com/leanprover/lean4/pull/3970)（`FindExpr` 的单子化泛化）。
  * [#4128](https://github.com/leanprover/lean4/pull/4128) 捕获了自动绑定隐式特性中的栈溢出。
  * [#4129](https://github.com/leanprover/lean4/pull/4129) 添加了 `tryCatchRuntimeEx` 组合子，以取代 `catchRuntimeEx` 的 reader 状态。
  * [#4155](https://github.com/leanprover/lean4/pull/4155) 简化了表达式规范化器。
  * [#4151](https://github.com/leanprover/lean4/pull/4151) 和 [#4369](https://github.com/leanprover/lean4/pull/4369)
    补充了许多缺失的跟踪类。
  * [#4185](https://github.com/leanprover/lean4/pull/4185) 让 congruence 定理生成器会清理参数类型上的类型标注。
  * [#4192](https://github.com/leanprover/lean4/pull/4192) 修复了自动绑定隐式特性启用时信息树恢复的问题，
    从而修复了悬停中的一个漂亮打印错误，并增强了未使用变量 linter。
  * [dfb496](https://github.com/leanprover/lean4/commit/dfb496a27123c3864571aec72f6278e2dad1cecf) 修复了 `declareBuiltin`，使其每个声明可被多次调用。
  * [#4569](https://github.com/leanprover/lean4/pull/4569) 修复了一个由合并冲突引入的问题：中断异常会被某些 `tryCatchRuntimeEx` 的用法吞掉。
  * [#4584](https://github.com/leanprover/lean4/pull/4584)（回移植为 [b056a0](https://github.com/leanprover/lean4/commit/b056a0b395bb728512a3f3e83bf9a093059d4301)）使内核中断适配新的取消系统。
  * 清理：[#4112](https://github.com/leanprover/lean4/pull/4112), [#4126](https://github.com/leanprover/lean4/pull/4126), [#4091](https://github.com/leanprover/lean4/pull/4091), [#4139](https://github.com/leanprover/lean4/pull/4139), [#4153](https://github.com/leanprover/lean4/pull/4153)。
  * 测试：[030406](https://github.com/leanprover/lean4/commit/03040618b8f9b35b7b757858483e57340900cdc4), [#4133](https://github.com/leanprover/lean4/pull/4133)。

````
# 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Compiler___-runtime___-and-FFI"
%%%

````markdown
* [#4100](https://github.com/leanprover/lean4/pull/4100) 改进了 reset/reuse 算法；现在它会进行第二遍处理，放宽“复用的内存单元必须仅用于完全相同构造子”的限制。
* [#2903](https://github.com/leanprover/lean4/pull/2903) 修复了旧编译器因错误处理 `noConfusion` 应用而导致的段错误。
* [#4311](https://github.com/leanprover/lean4/pull/4311) 修复了常量折叠中的错误。
* [#3915](https://github.com/leanprover/lean4/pull/3915) 记录了归纳类型的运行时内存布局。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Lake"
%%%

````markdown
* [#4518](https://github.com/leanprover/lean4/pull/4518) 让 trace 读取更加稳健。现在若 trace 文件无效或不可读，Lake 会重新构建，并且向后兼容旧的纯数字 trace。
* [#4057](https://github.com/leanprover/lean4/pull/4057) 为 `require` 命令上的文档字符串提供支持。
* [#4088](https://github.com/leanprover/lean4/pull/4088) 改进了 `family_def` 与 `library_data` 命令的悬停信息。
* [#4147](https://github.com/leanprover/lean4/pull/4147) 为包模板添加默认 `README.md`
* [#4261](https://github.com/leanprover/lean4/pull/4261) 扩展了 `lake test` 帮助页，添加了 `lake check-test` 帮助页，
  增加了 `lake lint` 与标签 `@[lint_driver]`，支持从依赖中指定测试和 lint 驱动，
  增加了 `testDriverArgs` 与 `lintDriverArgs` 选项，增加了对库测试驱动的支持，
  并让 `lake check-test` 与 `lake check-lint` 只加载包本身而不加载依赖。
* [#4270](https://github.com/leanprover/lean4/pull/4270) 新增 `lake pack` 与 `lake unpack`，用于将 Lake 构建产物打包到归档中或从归档中解包。
* [#4083](https://github.com/leanprover/lean4/pull/4083)
  将 manifest 格式切换为使用 `major.minor.patch` 语义化版本。
  主版本号递增表示破坏性变更（例如新增必填字段，或已有字段语义发生改变）。
  次版本号递增（在 `0.x` 之后）表示向后兼容的扩展（例如新增可选字段、移除字段）。
  此变更向后兼容。Lake 仍能成功读取旧的数字版本 manifest，
  并会将数字版本 `N` 视为语义版本 `0.N.0`。Lake 还会接受带 `-` 后缀的 manifest 版本
  （例如 `x.y.z-foo`），并忽略该后缀。
* [#4273](https://github.com/leanprover/lean4/pull/4273) 出于向后兼容原因，添加了从 `JobM` 到 `FetchM` 的提升。
* [#4351](https://github.com/leanprover/lean4/pull/4351) 修复了 `LogIO` 到 `CliM` 提升的性能问题。
* [#4343](https://github.com/leanprover/lean4/pull/4343) 让 Lake 在缓存的构建日志中存储一次构建的依赖 trace，并在重放日志前验证其是否与当前构建的 trace 一致。
* [#4402](https://github.com/leanprover/lean4/pull/4402) 将缓存日志移入 trace 文件（不再有 `.log.json`）。
  这意味着致命错误时日志不再被缓存，并确保不会把过期日志关联到最新 trace 上。
  此外，`.hash` 文件的生成也变得更可靠了。
  `.hash` 文件会作为构建过程的一部分被删除，并在使用 `--rehash` 时总是重新生成。
* **其他修复或改进**
  * [#4056](https://github.com/leanprover/lean4/pull/4056) 清理了测试
  * [#4244](https://github.com/leanprover/lean4/pull/4244) 修复了 Lean 仓库打标签时的 `noRelease` 测试
  * [#4346](https://github.com/leanprover/lean4/pull/4346) 改进了 `tests/serve`
  * [#4356](https://github.com/leanprover/lean4/pull/4356) 在缺失或无效构建日志的警告中加入了构建日志路径。

````
# DevOps
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--DevOps"
%%%

````markdown
* [#3984](https://github.com/leanprover/lean4/pull/3984) 添加了一个用于 `git rebase -i` 的脚本（`script/rebase-stage0.sh`），可自动更新每个 stage0。
* [#4108](https://github.com/leanprover/lean4/pull/4108) 完成了从 Std 过渡到 Batteries 的相关重命名。
* [#4109](https://github.com/leanprover/lean4/pull/4109) 调整了 Github bug 模板，提及使用 [live.lean-lang.org](https://live.lean-lang.org) 进行测试。
* [#4136](https://github.com/leanprover/lean4/pull/4136) 让 CI 仅在添加或移除 `full-ci` 标签时重新运行。
* [#4175](https://github.com/leanprover/lean4/pull/4175) 和 [72b345](https://github.com/leanprover/lean4/commit/72b345c621a9a06d3a5a656da2b793a5eea5f168)
  尽可能切换为使用 `#guard_msgs` 运行测试。
* [#3125](https://github.com/leanprover/lean4/pull/3125) 解释了 Lean4 的 `pygments` 词法分析器。
* [#4247](https://github.com/leanprover/lean4/pull/4247) 建立了准备发布说明的流程。
* [#4032](https://github.com/leanprover/lean4/pull/4032) 现代化了构建说明与工作流。
* [#4255](https://github.com/leanprover/lean4/pull/4255) 将一些耗费较大的检查从合并队列移到了发布流程中。
* [#4265](https://github.com/leanprover/lean4/pull/4265) 为 CI 增加了 aarch64 macOS 作为原生编译目标。
* [f05a82](https://github.com/leanprover/lean4/commit/f05a82799a01569edeb5e2594cd7d56282320f9e) 在 CI 中恢复了 macOS aarch64 的安装后缀
* [#4317](https://github.com/leanprover/lean4/pull/4317) 更新了 macOS 的构建说明。
* [#4333](https://github.com/leanprover/lean4/pull/4333) 调整了工作流，以便在创建 `lean-pr-testing-NNNN` Mathlib 分支时更新 manifest 中的 Batteries。
* [#4355](https://github.com/leanprover/lean4/pull/4355) 简化了发布检查清单中的 `lean4checker` 步骤。
* [#4361](https://github.com/leanprover/lean4/pull/4361) 在 `pr-release` CI 步骤中加入了 elan 安装。
* [#4628](https://github.com/leanprover/lean4/pull/4628) 修复了缺少导出符号的 Windows 构建。

````
# 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___9___0-_LPAR_2024-07-01_RPAR_--Breaking-changes"
%%%

````markdown
尽管大多数改动都可能被视为破坏性变更，本节特别指出了 API 变更。

* `Nat.zero_or` 与 `Nat.or_zero` 已互换（[#4094](https://github.com/leanprover/lean4/pull/4094)）。
* `IsLawfulSingleton` 现为 `LawfulSingleton`（[#4350](https://github.com/leanprover/lean4/pull/4350)）。
* `BitVec` 字面量记法现在是 `<num>#<term>` 而不是 `<term>#<term>`，并且它是全局而非作用域化的。当 `x` 不是数值字面量时，应使用 `BitVec.ofNat w x`，而不是 `x#w`（[0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba)）。
* `BitVec.rotateLeft` 与 `BitVec.rotateRight` 现在会对移位量按位宽取模（[#4229](https://github.com/leanprover/lean4/pull/4229)）。
* 以下不再是 simp 引理：
  `List.length_pos`（[#4172](https://github.com/leanprover/lean4/pull/4172)）、
  `Option.bind_eq_some`（[#4314](https://github.com/leanprover/lean4/pull/4314)）。
* 由于对何种精译问题可以推迟施加了新的限制，`let` 和 `have` 中的类型（包括表达式形式与策略形式）现在可能精译失败（[#4096](https://github.com/leanprover/lean4/pull/4096)）。
  特别地，嵌入在类型中的策略将不再利用 `let x : type := value; body` 这类表达式里 `value` 的类型。
* 通过良基递归定义的函数现在默认会被标记为 `@[irreducible]`（[#4061](https://github.com/leanprover/lean4/pull/4061)）。
  现有那些依赖定义相等成立的证明（例如 `rfl`）可以
  改写为显式展开函数定义（使用 `simp`、
  `unfold`、`rw`），或者暂时将递归函数设为
  半可约（在命令前使用 `unseal f in`），或者将函数
  定义本身标记为 `@[semireducible]` 以恢复先前
  的行为。
* 由于 [#3929](https://github.com/leanprover/lean4/pull/3929)：
  * `MessageData.ofPPFormat` 构造子已被移除。
    它的功能被拆分成两部分：

    - 若要构造惰性的结构化消息，请使用 `MessageData.lazy`；
    - 若要嵌入 `Format` 或 `FormatWithInfos`，请使用 `MessageData.ofFormatWithInfos`。

    一个迁移示例可见 [#3929](https://github.com/leanprover/lean4/pull/3929/files#diff-5910592ab7452a0e1b2616c62d22202d2291a9ebb463145f198685aed6299867L109)。

  * `MessageData.ofFormat` 构造子已改为函数。
    如果需要检查 `MessageData`，可以对 `MessageData.ofFormatWithInfos` 进行模式匹配。

````
