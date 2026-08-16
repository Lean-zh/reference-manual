/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.14.0 (2024-12-02)" =>
%%%
tag := "release-v4.14.0"
file := "v4.14.0"
%%%

````markdown

**完整变更日志**：https://github.com/leanprover/lean4/compare/v4.13.0...v4.14.0

````
# 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

````markdown

* `structure` 与 `inductive` 命令
  * [#5517](https://github.com/leanprover/lean4/pull/5517) 改进了对 `inductive` 或 `structure.` 结果类型的宇宙层级推断。回顾一下：若一个取值于 `Prop` 的归纳类型至多只有一个构造子，且该构造子的所有参数都位于 `Prop` 中，那么它就是语法上的子单例。这类类型具有大消去，因此定义在 `Type` 或 `Prop` 中都没有问题。现在推断规则改为：如果某个类型是语法上的子单例、恰好只有一个构造子，并且该构造子至少有一个参数/字段，那么 `inductive`/`structure` 命令会优先创建 `Prop` 而不是 `Type`。因此，`structure S : Prop` 中的 `: Prop` 往往不再需要。（与 @arthur-adjedj 合作）
  * [#5842](https://github.com/leanprover/lean4/pull/5842) 和 [#5783](https://github.com/leanprover/lean4/pull/5783) 实现了一项功能：`structure` 命令现在可以定义递归归纳类型：
    ```lean
    structure Tree where
      n : Nat
      children : Fin n → Tree

    def Tree.size : Tree → Nat
      | {n, children} => Id.run do
        let mut s := 0
        for h : i in [0 : n] do
          s := s + (children ⟨i, h.2⟩).size
        pure s
    ```
  * [#5814](https://github.com/leanprover/lean4/pull/5814) 修复了一个 bug：Mathlib 的 `Type*` 精译器可能导致 `inductive` 命令生成错误的宇宙参数。
  * [#3152](https://github.com/leanprover/lean4/pull/3152) 和 [#5844](https://github.com/leanprover/lean4/pull/5844) 修复了结构体实例记法中默认值处理的 bug。（与 @arthur-adjedj 合作）
  * [#5399](https://github.com/leanprover/lean4/pull/5399) 将实例合成顺序计算失败从软错误提升为硬错误。
  * [#5542](https://github.com/leanprover/lean4/pull/5542) 弃用了 `inductive` 和 `structure` 的 `:=` 变体（见破坏性变更）。

* **应用精译改进**
  * [#5671](https://github.com/leanprover/lean4/pull/5671) 令 `@[elab_as_elim]` 至少需要一个判别式，否则这种替代精译器就没有优势。
  * [#5528](https://github.com/leanprover/lean4/pull/5528) 在显式模式下启用字段记法。语法 `@x.f` 会被精译为 `@S.f`，并将 `x` 提供给相应参数。
  * [#5692](https://github.com/leanprover/lean4/pull/5692) 修改了点记法解析算法，使其可以应用 `CoeFun` 实例。例如，Mathlib 中有 `Multiset.card : Multiset α →+ Nat`；现在若 `m : Multiset α`，记法 `m.card` 会解析为 `⇑Multiset.card m`。
  * [#5658](https://github.com/leanprover/lean4/pull/5658) 修复了一个 bug：启用 eta 参数特性时，'don't know how to synthesize implicit argument' 错误可能显示错误的局部上下文。
  * [#5933](https://github.com/leanprover/lean4/pull/5933) 修复了模式中的 `..` 省略号会使用 optparams 和 autoparams 的 bug。
  * [#5770](https://github.com/leanprover/lean4/pull/5770) 让结构体的点记法解析基于*全部*祖先进行。它还为广义字段记法加入了*解析顺序*：在解析名称时，按此顺序访问各个命名空间。该顺序使用常见的 C3 线性化算法（例如 Python 也采用它）计算；若计算成功，就能保证在考虑较远祖先命名空间之前，先考虑直接父级的命名空间。默认使用能容忍不一致的宽松版本；若设置 `set_option structure.strictResolutionOrder true`，则不一致的父级顺序会变成警告。

* **递归与归纳原理**
  * [#5619](https://github.com/leanprover/lean4/pull/5619) 修复了函数式归纳原理生成过程，避免在预处理步骤中过度 eta 展开。
  * [#5766](https://github.com/leanprover/lean4/pull/5766) 修复了结构化嵌套递归，使其在嵌套类型先出现时不会混淆。
  * [#5803](https://github.com/leanprover/lean4/pull/5803) 修复了含有 `let` 绑定时函数式归纳原理生成中的一个 bug。
  * [#5904](https://github.com/leanprover/lean4/pull/5904) 改进了函数式归纳原理生成，使其在展开辅助定义时更加谨慎。
  * [#5850](https://github.com/leanprover/lean4/pull/5850) 重构了 `Predefinition.Structural` 的代码。

* **错误消息**
  * [#5276](https://github.com/leanprover/lean4/pull/5276) 修复了 “type mismatch” 错误中的一个 bug：在暴露差异的算法中，它原本会对元变量做结构性赋值。
  * [#5919](https://github.com/leanprover/lean4/pull/5919) 让 “type mismatch” 错误在数值字面量处添加类型标注，以暴露差异。
  * [#5922](https://github.com/leanprover/lean4/pull/5922) 让 “type mismatch” 错误能够暴露函数体和 pi 类型体中的差异。
  * [#5888](https://github.com/leanprover/lean4/pull/5888) 改进了 `match` 表达式中无效归纳分支名称的错误消息。（@josojo）
  * [#5719](https://github.com/leanprover/lean4/pull/5719) 改进了 `calc` 的错误消息。

* [#5627](https://github.com/leanprover/lean4/pull/5627) 和 [#5663](https://github.com/leanprover/lean4/pull/5663) 改进了 **`#eval` 命令**，并引入了一些新特性。
  * 现在如果存在 `ToExpr` 实例，结果就可以被美观打印，这意味着会有**可悬停的输出**。若 `ToExpr` 失败，则与以前一样继续尝试查找 `Repr` 或 `ToString` 实例。设置 `set_option eval.pp false` 可禁用对 `ToExpr` 实例的使用。
  * 现在支持 **`Repr` 实例的自动派生**，由 `pp.derive.repr` 选项控制（默认为 **true**）。例如：
    ```lean
    inductive Baz
    | a | b

    #eval Baz.a
    -- Baz.a
    ```
    当没有表示 `Baz` 的方式时，它会简单地执行 `deriving instance Repr for Baz`。
  * `eval.type` 选项控制输出中是否包含类型。目前默认值为 false。
  * 现在像 `#eval do return 2` 这样单子未知的表达式也可以工作。它会尝试把该单子与 `CommandElabM`、`TermElabM` 或 `IO` 统一。
  * `Lean.Eval` 和 `Lean.MetaEval` 类已被移除。它们过去分别负责适配单子和打印结果。现在 `MonadEval` 类负责为求值适配单子（它类似于 `MonadLift`，但其实例在初始化状态时允许使用默认数据），而结果表示则交由独立流程处理。
  * 关于实例合成失败的错误消息现在更加精确。一旦检测到适用了 `MonadEval` 类，错误消息就会明确指出缺少的是 `ToExpr`/`Repr`/`ToString` 实例中的哪一个。
  * 修复了求值 `MetaM` 和 `CoreM` 时不会收集日志消息的 bug。
  * 修复了 `#eval` 中无法使用 `let rec` 的 bug。

* `partial` 定义
  * [#5780](https://github.com/leanprover/lean4/pull/5780) 改进了 `partial` 无法证明某个类型可居住时的错误消息。加入 delta deriving。
  * [#5821](https://github.com/leanprover/lean4/pull/5821) 让 `partial` 的可居住性推导能够根据参数创建局部 `Inhabited` 实例。

* **新的策略配置语法。** 现在，所有核心策略的配置语法都得到了升级。过去写作 `simp (config := { contextual := true, maxSteps := 22})`，现在可以写成 `simp +contextual (maxSteps := 22)`。策略作者可将策略语法中的 `(config)?` 改为 `optConfig`，并且可能可以删除精译器中的 `mkOptionalNode`，以完成迁移。[#5883](https://github.com/leanprover/lean4/pull/5883)、[#5898](https://github.com/leanprover/lean4/pull/5898)、[#5928](https://github.com/leanprover/lean4/pull/5928) 和 [#5932](https://github.com/leanprover/lean4/pull/5932)。（策略作者请参见破坏性变更。）

* `simp` 策略
  * [#5632](https://github.com/leanprover/lean4/pull/5632) 修复了 `Fin` 字面量 simpproc，使其规约行为更加一致。
  * [#5648](https://github.com/leanprover/lean4/pull/5648) 修复了 `simpa ... using t` 中的一个 bug：`t` 里的元变量此前没有被正确处理；同时也改进了类型不匹配错误。
  * [#5838](https://github.com/leanprover/lean4/pull/5838) 修复了 `simp!` 的文档字符串，使其真正描述 `simp!`。
  * [#5870](https://github.com/leanprover/lean4/pull/5870) 增加了对 `attribute [simp ←]` 的支持（注意反向方向）。这会把定理的逆向形式加入全局 simp 定理集。

* `decide` 策略
  * [#5665](https://github.com/leanprover/lean4/pull/5665) 添加了 `decide!` 策略，用于使用内核规约（注意：在未来版本中它会重命名为 `decide +kernel`）。

* `bv_decide` 策略
  * [#5714](https://github.com/leanprover/lean4/pull/5714) 增加了不等式回归测试。（@alexkeizer）
  * [#5608](https://github.com/leanprover/lean4/pull/5608) 为 `toNat_ofInt` 添加了 `bv_toNat` 标签。（@bollu）
  * [#5618](https://github.com/leanprover/lean4/pull/5618) 为 `ac_nf` 增加了 `at` 支持，并在 `bv_normalize` 中使用它。（@tobiasgrosser）
  * [#5628](https://github.com/leanprover/lean4/pull/5628) 添加了 udiv 支持。
  * [#5635](https://github.com/leanprover/lean4/pull/5635) 为取负和减法添加了辅助 bitblaster。
  * [#5637](https://github.com/leanprover/lean4/pull/5637) 增加了更多 `getLsbD` bitblaster 理论。
  * [#5652](https://github.com/leanprover/lean4/pull/5652) 添加了 umod 支持。
  * [#5653](https://github.com/leanprover/lean4/pull/5653) 为模运算添加了性能基准。
  * [#5655](https://github.com/leanprover/lean4/pull/5655) 将 `bv_check` 上的错误降为警告。
  * [#5670](https://github.com/leanprover/lean4/pull/5670) 增加了对 `~~~(-x)` 的支持。
  * [#5673](https://github.com/leanprover/lean4/pull/5673) 默认禁用 `ac_nf`。
  * [#5675](https://github.com/leanprover/lean4/pull/5675) 修复了 `bv_decide` 反例中的上下文跟踪。
  * [#5676](https://github.com/leanprover/lean4/pull/5676) 在 LRAT 证明无效时增加了错误。
  * [#5781](https://github.com/leanprover/lean4/pull/5781) 在所有地方引入未解释符号。
  * [#5823](https://github.com/leanprover/lean4/pull/5823) 添加了 `BitVec.sdiv` 支持。
  * [#5852](https://github.com/leanprover/lean4/pull/5852) 添加了 `BitVec.ofBool` 支持。
  * [#5855](https://github.com/leanprover/lean4/pull/5855) 添加了 `if` 支持。
  * [#5869](https://github.com/leanprover/lean4/pull/5869) 增加了对全部 SMTLIB BitVec 除法/取余运算的支持。
  * [#5886](https://github.com/leanprover/lean4/pull/5886) 增加了嵌入式约束替换。
  * [#5918](https://github.com/leanprover/lean4/pull/5918) 修复了 `bv_normalize` 中游离 mvar 的 bug。
  * 文档：
    * [#5636](https://github.com/leanprover/lean4/pull/5636) 增加了关于乘法的说明。

* `conv` 模式
  * [#5861](https://github.com/leanprover/lean4/pull/5861) 改进了 `congr` conv 策略，使其能够处理“过度应用”的函数。
  * [#5894](https://github.com/leanprover/lean4/pull/5894) 改进了 `arg` conv 策略，使其可以访问更多参数，并能处理“过度应用”的函数（它会为相关参数生成专用的同余引理）。同时让 `arg 1` 和 `arg 2` 在更多情况下可用于 pi 类型。还增加了负索引，例如 `arg -2` 等价于 `lhs` 策略。`enter [...]` 策略现在会像 `rw` 一样显示中间状态。

* **其他策略**
  * [#4846](https://github.com/leanprover/lean4/pull/4846) 修复了 `generalize ... at *` 会作用于实现细节的 bug。（@ymherklotz）
  * [#5730](https://github.com/leanprover/lean4/pull/5730) 上游合入了 `classical` 策略组合子。
  * [#5815](https://github.com/leanprover/lean4/pull/5815) 改进了尝试展开一个并非局部定义的局部假设时的错误消息。
  * [#5862](https://github.com/leanprover/lean4/pull/5862) 和 [#5863](https://github.com/leanprover/lean4/pull/5863) 修改了 `apply` 和 `simp` 的精译方式，使其不再禁用错误恢复。这提升了术语存在精译错误时的悬停和补全体验。

* `deriving` 子句
  * [#5899](https://github.com/leanprover/lean4/pull/5899) 为 delta 派生的实例增加了声明范围。
  * [#5265](https://github.com/leanprover/lean4/pull/5265) 移除了 `deriving` 子句中用于给 deriving handler 传参的未使用语法（见破坏性变更）。

* [#5065](https://github.com/leanprover/lean4/pull/5065) 上游合入并更新了 `#where`，这是一个报告当前作用域信息的命令。

* **代码检查器**
  * [#5338](https://github.com/leanprover/lean4/pull/5338) 让未使用变量 linter 现在默认忽略策略中定义的变量，从而避免性能瓶颈。
  * [#5644](https://github.com/leanprover/lean4/pull/5644) 确保各类 linter 一般都不会在 `#guard_msgs` 自身上运行。

* **元编程接口**
  * [#5720](https://github.com/leanprover/lean4/pull/5720) 添加了 `pushGoal`/`pushGoals` 和 `popGoal`，用于操作目标状态。它们是 `replaceMainGoal` 和 `getMainGoal` 的替代方案；使用它们时，不必再担心在给主目标赋值后、调用 `replaceMainGoal` 之前，有东西把已赋值元变量从目标列表中清掉。还修改了 `closeMainGoalUsing`，它类似 `liftMetaTactic` 的 `TacticM` 版本。现在回调会在主目标已从目标列表移除的上下文中运行，且回调可以自由修改目标列表。此外，`checkUnassigned` 参数被替换为 `checkNewUnassigned`，它检查给目标赋的值相对于回调执行开始时，是否包含任何*新的*元变量。`withCollectingNewGoalsFrom` 现在显式接收 `parentTag` 参数，而不是通过 `getMainTag` 间接获取。`elabTermWithHoles` 现在也可选择接收 `parentTag?`。
  * [#5563](https://github.com/leanprover/lean4/pull/5563) 修复了 `getFunInfo` 和 `inferType`，使其使用 `withAtLeastTransparency` 而不是 `withTransparency`。
  * [#5679](https://github.com/leanprover/lean4/pull/5679) 修复了 `RecursorVal.getInduct`，使其返回主参数类型的名称。这让嵌套归纳类型上的 “structure eta” 能够工作。
  * [#5681](https://github.com/leanprover/lean4/pull/5681) 移除了未使用的 `mkRecursorInfoForKernelRec`。
  * [#5686](https://github.com/leanprover/lean4/pull/5686) 让 discrimination tree 为 forall 的定义域建立索引，从而提升简化和类型类搜索的性能。
  * [#5760](https://github.com/leanprover/lean4/pull/5760) 为 `Name` 表达式添加了 `Lean.Expr.name?` 识别器。
  * [#5800](https://github.com/leanprover/lean4/pull/5800) 修改了 `liftCommandElabM`，使其保留更多状态，修复了使用它会丢失消息的问题。
  * [#5857](https://github.com/leanprover/lean4/pull/5857) 允许在 `m!` 字符串中使用点记法，例如 `m!"{.ofConstName n}"`。
  * [#5841](https://github.com/leanprover/lean4/pull/5841) 和 [#5853](https://github.com/leanprover/lean4/pull/5853) 在 `StructureInfo` 环境扩展中记录了 `structure` 父级的完整列表。

* **其他修复或改进**
  * [#5566](https://github.com/leanprover/lean4/pull/5566) 修复了 [#4781](https://github.com/leanprover/lean4/pull/4781) 引入的一个 bug：heartbeat 异常不再被正确处理。现在这类异常会带上 `runtime.maxHeartbeats` 标签。（@eric-wieser）
  * [#5708](https://github.com/leanprover/lean4/pull/5708) 修改了反射证明策略 `ac_nf0` 和 `simp_arith` 生成的证明对象，使内核不那么容易规约昂贵的原子。
  * [#5768](https://github.com/leanprover/lean4/pull/5768) 添加了 `#version` 命令，用于打印 Lean 的版本信息。
  * [#5822](https://github.com/leanprover/lean4/pull/5822) 修复了精译器算法，使其与内核对原始投影（`Expr.proj`）的算法保持一致。
  * [#5811](https://github.com/leanprover/lean4/pull/5811) 改进了 `rwa` 策略的文档字符串。


````
# 语言服务器、组件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

````markdown

* [#5224](https://github.com/leanprover/lean4/pull/5224) 按照 LSP 规范修复了 `WorkspaceClientCapabilities`，使 `applyEdit` 成为可选项。（@pzread）
* [#5340](https://github.com/leanprover/lean4/pull/5340) 修复了关闭语言服务器时的服务器死锁，以及文件 worker 崩溃后客户端与语言服务器不同步的问题。
* [#5560](https://github.com/leanprover/lean4/pull/5560) 让 `initialize` 和 `builtin_initialize` 参与调用层次结构及其他请求。
* [#5650](https://github.com/leanprover/lean4/pull/5650) 让 attribute 中的引用参与调用层次结构及其他请求。
* [#5666](https://github.com/leanprover/lean4/pull/5666) 在策略块中加入自动补全，无需先输入策略的首字符；同时为策略自动补全条目加入策略补全文档。
* [#5677](https://github.com/leanprover/lean4/pull/5677) 修复了若干在某些文本光标位置下不显示目标状态的情况。
* [#5707](https://github.com/leanprover/lean4/pull/5707) 在自动补全条目中标示弃用信息。
* [#5736](https://github.com/leanprover/lean4/pull/5736)、[#5752](https://github.com/leanprover/lean4/pull/5752)、[#5763](https://github.com/leanprover/lean4/pull/5763)、[#5802](https://github.com/leanprover/lean4/pull/5802) 和 [#5805](https://github.com/leanprover/lean4/pull/5805) 修复了语言服务器中的多项性能问题。
* [#5801](https://github.com/leanprover/lean4/pull/5801) 将定理自动补全与非定理自动补全区分开来。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Pretty-printing"
%%%

````markdown

* [#5640](https://github.com/leanprover/lean4/pull/5640) 修复了一个 bug：消息中的目标状态可能会把换行打印为空格。
* [#5643](https://github.com/leanprover/lean4/pull/5643) 添加了选项 `pp.mvars.delayed`（默认 false）；当其为 false 时，延迟赋值元变量会被美观打印为它们已赋的内容。现在 `fun x : Nat => ?a` 会打印为 `fun x : Nat => ?a`，而不是 `fun x ↦ ?m.7 x`。
* [#5711](https://github.com/leanprover/lean4/pull/5711) 添加了选项 `pp.mvars.anonymous` 和 `pp.mvars.levels`；当它们为 false 时，表达式元变量和层级元变量会分别被美观打印为 `?_`。
* [#5710](https://github.com/leanprover/lean4/pull/5710) 调整了 `⋯` 精译警告，使其提到 `pp.maxSteps`。

* [#5759](https://github.com/leanprover/lean4/pull/5759) 修复了 `sorryAx` 的应用反展开器。
* [#5827](https://github.com/leanprover/lean4/pull/5827) 提高了签名美观打印器（如 `#check` 输出）中 binder 名称的准确性。同时修复了连续 hygienic 名称打印时缺少空格分隔的问题，因此现在会得到 `(x✝ y✝ : Nat)`，而不是 `(x✝y✝ : Nat)`。
* [#5830](https://github.com/leanprover/lean4/pull/5830) 确保所有核心反精译器在适当情况下都会响应 `pp.explicit`。
* [#5639](https://github.com/leanprover/lean4/pull/5639) 确保名称字面量在美观打印时使用转义。
* [#5854](https://github.com/leanprover/lean4/pull/5854) 为 `<|>`、`<*>`、`>>`、`<*` 和 `*>` 添加了反精译器。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Library"
%%%

````markdown

* `Array`
  * [#5687](https://github.com/leanprover/lean4/pull/5687) 弃用了 `Array.data`。
  * [#5705](https://github.com/leanprover/lean4/pull/5705) 为 `Array.swapAt!` 使用了更好的默认值。
  * [#5748](https://github.com/leanprover/lean4/pull/5748) 将 `Array.mapIdx` 引理移到新文件中。
  * [#5749](https://github.com/leanprover/lean4/pull/5749) 简化了 `Array.mapIdx` 的签名。
  * [#5758](https://github.com/leanprover/lean4/pull/5758) 上游合入了 `Array.reduceOption`。
  * [#5786](https://github.com/leanprover/lean4/pull/5786) 为 `Array.isEqv` 和 `BEq` 添加了 simp 引理。
  * [#5796](https://github.com/leanprover/lean4/pull/5796) 将 `Array.shrink` 重命名为 `Array.take`，并把它与 `List.take` 关联起来。
  * [#5798](https://github.com/leanprover/lean4/pull/5798) 上游合入了 `List.modify`，添加了相关引理，并将其与 `Array.modify` 关联起来。
  * [#5799](https://github.com/leanprover/lean4/pull/5799) 将 `Array.forIn` 与 `List.forIn` 关联起来。
  * [#5833](https://github.com/leanprover/lean4/pull/5833) 添加了 `Array.forIn'`，并将其与 `List` 关联起来。
  * [#5848](https://github.com/leanprover/lean4/pull/5848) 修复了 `Init.Data.Array.Basic` 中的弃用提示，使其不再推荐已弃用常量。
  * [#5895](https://github.com/leanprover/lean4/pull/5895) 添加了 `LawfulBEq (Array α) ↔ LawfulBEq α`。
  * [#5896](https://github.com/leanprover/lean4/pull/5896) 将 `@[simp]` 从 `back_eq_back?` 移到 `back_push`。
  * [#5897](https://github.com/leanprover/lean4/pull/5897) 将 `Array.back` 重命名为 `back!`。

* `List`
  * [#5605](https://github.com/leanprover/lean4/pull/5605) 移除了 `List.redLength`。
  * [#5696](https://github.com/leanprover/lean4/pull/5696) 上游合入了 `List.mapIdx`，并添加了相关引理。
  * [#5697](https://github.com/leanprover/lean4/pull/5697) 上游合入了 `List.foldxM_map`。
  * [#5701](https://github.com/leanprover/lean4/pull/5701) 将 `List.join` 重命名为 `List.flatten`。
  * [#5703](https://github.com/leanprover/lean4/pull/5703) 上游合入了 `List.sum`。
  * [#5706](https://github.com/leanprover/lean4/pull/5706) 将 `prefix_append_right_inj` 标记为 simp 引理。
  * [#5716](https://github.com/leanprover/lean4/pull/5716) 修复了 `List.drop_drop` 中加法顺序的问题。
  * [#5731](https://github.com/leanprover/lean4/pull/5731) 将 `List.bind` 和 `Array.concatMap` 重命名为 `flatMap`。
  * [#5732](https://github.com/leanprover/lean4/pull/5732) 将 `List.pure` 重命名为 `List.singleton`。
  * [#5742](https://github.com/leanprover/lean4/pull/5742) 上游合入了 `ne_of_mem_of_not_mem`。
  * [#5743](https://github.com/leanprover/lean4/pull/5743) 上游合入了 `ne_of_apply_ne`。
  * [#5816](https://github.com/leanprover/lean4/pull/5816) 添加了更多 `List.modify` 引理。
  * [#5879](https://github.com/leanprover/lean4/pull/5879) 将 `List.groupBy` 重命名为 `splitBy`。
  * [#5913](https://github.com/leanprover/lean4/pull/5913) 将 `List` 上的 `for` 循环与 `foldlM` 关联起来。

* `Nat`
  * [#5694](https://github.com/leanprover/lean4/pull/5694) 移除了 `instBEqNat`；它与 `instBEqOfDecidableEq` 重复，但不是 defeq。
  * [#5746](https://github.com/leanprover/lean4/pull/5746) 弃用了 `Nat.sum`。
  * [#5785](https://github.com/leanprover/lean4/pull/5785) 添加了 `Nat.forall_lt_succ` 及其变体。

* 定宽整数
  * [#5323](https://github.com/leanprover/lean4/pull/5323) 以 `BitVec` 为基础重新定义了无符号定宽整数。
  * [#5735](https://github.com/leanprover/lean4/pull/5735) 添加了 `UIntX.[val_ofNat, toBitVec_ofNat]`。
  * [#5790](https://github.com/leanprover/lean4/pull/5790) 定义了 `Int8`。
  * [#5901](https://github.com/leanprover/lean4/pull/5901) 移除了 `UInt8.modn` 的原生代码。

* `BitVec`
  * [#5604](https://github.com/leanprover/lean4/pull/5604) 补全了移位情况下的 `BitVec.[getMsbD|getLsbD|msb]`。（@luisacicolini）
  * [#5609](https://github.com/leanprover/lean4/pull/5609) 添加了分母为零时除法的引理。（@bollu）
  * [#5620](https://github.com/leanprover/lean4/pull/5620) 为 Bitblasting 编写了文档。（@bollu）
  * [#5623](https://github.com/leanprover/lean4/pull/5623) 将 `BitVec.udiv/umod/sdiv/smod` 移到 `add/sub/mul/lt` 之后。（@tobiasgrosser）
  * [#5645](https://github.com/leanprover/lean4/pull/5645) 将 `udiv` 的范式定义为 `/`，相应地将 `umod` 定义为 `%`。（@bollu）
  * [#5646](https://github.com/leanprover/lean4/pull/5646) 添加了关于算术不等式的引理。（@bollu）
  * [#5680](https://github.com/leanprover/lean4/pull/5680) 扩展了与 `toFin` 的关系。（@tobiasgrosser）
  * [#5691](https://github.com/leanprover/lean4/pull/5691) 添加了 `BitVec.(getMSbD, msb)_(add, sub)` 和 `BitVec.getLsbD_sub`。（@luisacicolini）
  * [#5712](https://github.com/leanprover/lean4/pull/5712) 添加了 `BitVec.[udiv|umod]_[zero|one|self]`。（@tobiasgrosser）
  * [#5718](https://github.com/leanprover/lean4/pull/5718) 添加了 `BitVec.sdiv_[zero|one|self]`。（@tobiasgrosser）
  * [#5721](https://github.com/leanprover/lean4/pull/5721) 添加了 `BitVec.(msb, getMsbD, getLsbD)_(neg, abs)`。（@luisacicolini）
  * [#5772](https://github.com/leanprover/lean4/pull/5772) 添加了 `BitVec.toInt_sub`，并简化了 `BitVec.toInt_neg`。（@tobiasgrosser）
  * [#5778](https://github.com/leanprover/lean4/pull/5778) 证明了 `intMin` 是最小的有符号位向量。（@alexkeizer）
  * [#5851](https://github.com/leanprover/lean4/pull/5851) 添加了 `(msb, getMsbD)_twoPow`。（@luisacicolini）
  * [#5858](https://github.com/leanprover/lean4/pull/5858) 添加了 `BitVec.[zero_ushiftRight|zero_sshiftRight|zero_mul]`，并清理了 BVDecide。（@tobiasgrosser）
  * [#5865](https://github.com/leanprover/lean4/pull/5865) 添加了 `BitVec.(msb, getMsbD)_concat`。（@luisacicolini）
  * [#5881](https://github.com/leanprover/lean4/pull/5881) 添加了 `Hashable (BitVec n)`。

* `String`/`Char`
  * [#5728](https://github.com/leanprover/lean4/pull/5728) 上游合入了 `String.dropPrefix?`。
  * [#5745](https://github.com/leanprover/lean4/pull/5745) 修改了 `String.dropPrefix?` 的签名。
  * [#5747](https://github.com/leanprover/lean4/pull/5747) 添加了 `Hashable Char` 实例。

* `HashMap`
  * [#5880](https://github.com/leanprover/lean4/pull/5880) 添加了 `HashMap.modify`/`alter` 的过渡实现。

* **其他**
  * [#5704](https://github.com/leanprover/lean4/pull/5704) 从 `Option.isSome_eq_isSome` 移除了 `@[simp]`。
  * [#5739](https://github.com/leanprover/lean4/pull/5739) 上游合入了 `Prod` 的相关内容。
  * [#5740](https://github.com/leanprover/lean4/pull/5740) 将 `Antisymm` 移至 `Std.Antisymm`。
  * [#5741](https://github.com/leanprover/lean4/pull/5741) 上游合入了 `Sum` 的基础内容。
  * [#5756](https://github.com/leanprover/lean4/pull/5756) 添加了 `Nat.log2_two_pow`。（@spinylobster）
  * [#5892](https://github.com/leanprover/lean4/pull/5892) 移除了重复的 `ForIn` 实例。
  * [#5900](https://github.com/leanprover/lean4/pull/5900) 从 `Sum.forall` 和 `Sum.exists` 移除了 `@[simp]`。
  * [#5812](https://github.com/leanprover/lean4/pull/5812) 移除了冗余的 `Decidable` 假设。（@FR-vdash-bot）

````
# 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Compiler___-runtime___-and-FFI"
%%%

````markdown

* [#5685](https://github.com/leanprover/lean4/pull/5685) 修复了帮助消息中的标志，移除了 `-f` 标志，并添加了 `-g` 标志。（@James-Oswald）
* [#5930](https://github.com/leanprover/lean4/pull/5930) 添加了 `--short-version`（`-V`）选项，用于显示简短版本信息。（@juhp）
* [#5144](https://github.com/leanprover/lean4/pull/5144) 将所有 64 位平台统一切换为始终使用 GMP 进行大整数运算。
* [#5753](https://github.com/leanprover/lean4/pull/5753) 将支持的最低 Windows 版本提升到 Windows 10 1903（发布于 2019 年 5 月）。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Lake"
%%%

````markdown

* [#5715](https://github.com/leanprover/lean4/pull/5715) 将 `lake new math` 改为使用 `autoImplicit false`。（@eric-wieser）
* [#5688](https://github.com/leanprover/lean4/pull/5688) 让 `Lake` 不再在 `Lake` 命名空间中创建核心别名。
* [#5924](https://github.com/leanprover/lean4/pull/5924) 为 `buildFile*` 工具函数添加了 `text` 选项。
* [#5789](https://github.com/leanprover/lean4/pull/5789) 让 `lake init` 在 Git 工作树内部时不再执行 `git init`。（@haoxins）
* [#5684](https://github.com/leanprover/lean4/pull/5684) 让 Lake 在执行 `lake update` 时，如果发现某个包的直接依赖使用了更新但兼容的工具链，就更新该包的 `lean-toolchain` 文件。若要跳过此步骤，可使用 `--keep-toolchain` CLI 选项。（见破坏性变更。）
* [#6218](https://github.com/leanprover/lean4/pull/6218) 让 Lake 在包的构建目录已存在时，不再自动抓取 GitHub cloud release（与 Reservoir 缓存的行为保持一致）。这可避免缓存覆盖现有的预构建产物。用户仍可通过运行 `lake build <pkg>:release` 手动抓取缓存并覆盖构建目录。
* [#6231](https://github.com/leanprover/lean4/pull/6231) 改进了 Lake 在无法从 Reservoir 获取依赖时给出的错误信息。如果该包未被索引，它会给出如何从 GitHub 引入该包的建议。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Documentation"
%%%

````markdown

* [#5617](https://github.com/leanprover/lean4/pull/5617) 修复了 MSYS2 的构建说明。
* [#5725](https://github.com/leanprover/lean4/pull/5725) 指出 `OfScientific` 接收的是原始字面量。（@eric-wieser）
* [#5794](https://github.com/leanprover/lean4/pull/5794) 为应用省略号记法添加了一个文档占位条目。（@eric-wieser）

````
# 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___14___0-_LPAR_2024-12-02_RPAR_--Breaking-changes"
%%%

````markdown

* 用于向 deriving handler 提供参数的语法已被移除，因为生态中的主要 Lean 项目都没有使用它。因此，`applyDerivingHandlers` 现在少接收一个参数，`registerDerivingHandlerWithArgs` 现在简化为 `registerDerivingHandler`，`DerivingHandler` 不再包含那个未使用的参数，而 `DerivingHandlerNoArgs` 已被弃用。迁移代码时，请删除未使用的 `none` 参数，并改用 `registerDerivingHandler` 与 `DerivingHandler`。([#5265](https://github.com/leanprover/lean4/pull/5265))
* 支持的最低 Windows 版本已提升到 Windows 10 1903（2019 年 5 月发布）。([#5753](https://github.com/leanprover/lean4/pull/5753))
* `lake` 的 `--lean` CLI 选项已被移除。请改用 `LEAN` 环境变量。([#5684](https://github.com/leanprover/lean4/pull/5684))
* `inductive ... :=`、`structure ... :=` 和 `class ... :=` 语法已弃用，推荐改用 `... where` 变体。旧语法会产生警告，由 `linter.deprecated` 选项控制。([#5542](https://github.com/leanprover/lean4/pull/5542))
* 生成的策略配置精译器现在落在 `TacticM` 中，以利用当前恢复状态。希望精译配置的命令现在应使用 `declare_command_config_elab` 而不是 `declare_config_elab`，以得到落在 `CommandElabM` 中的精译器。语法应从 `(config)?` 迁移到 `optConfig`，不过这些精译器保持反向兼容。([#5883](https://github.com/leanprover/lean4/pull/5883))
````
