/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.13.0 (2024-11-01)" =>
%%%
tag := "release-v4.13.0"
file := "v4.13.0"
%%%

```markdown
**完整变更日志**：https://github.com/leanprover/lean4/compare/v4.12.0...v4.13.0

### 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

* `structure` 命令
  * [#5511](https://github.com/leanprover/lean4/pull/5511) 允许结构体父类型是类型同义词。
  * [#5531](https://github.com/leanprover/lean4/pull/5531) 允许结构体字段的默认值是 noncomputable 的。

* `rfl` 与 `apply_rfl` tactic
  * [#3714](https://github.com/leanprover/lean4/pull/3714)、[#3718](https://github.com/leanprover/lean4/pull/3718) 改进了 `rfl` tactic，并提供了更好的错误消息。
  * [#3772](https://github.com/leanprover/lean4/pull/3772) 让 `rfl` 不再对封闭项使用内核 defeq。
  * [#5329](https://github.com/leanprover/lean4/pull/5329) 为 `Iff.refl` 添加了 `@[refl]` 标记。（@Parcly-Taxel）
  * [#5359](https://github.com/leanprover/lean4/pull/5359) 确保 `rfl` tactic 会尝试 `Iff.rfl`。（@Parcly-Taxel）

* `unfold` tactic
  * [#4834](https://github.com/leanprover/lean4/pull/4834) 让 `unfold` 可以对局部定义执行 zeta-delta 规约，纳入了 Mathlib `unfold_let` tactic 的功能。

* `omega` tactic
  * [#5382](https://github.com/leanprover/lean4/pull/5382) 修复了 [#5315](https://github.com/leanprover/lean4/issues/5315) 中的伪错误。
  * [#5523](https://github.com/leanprover/lean4/pull/5523) 支持 `Int.toNat`。

* `simp` tactic
  * [#5479](https://github.com/leanprover/lean4/pull/5479) 让 `simp` 能应用带高阶模式的规则。

* `induction` tactic
  * [#5494](https://github.com/leanprover/lean4/pull/5494) 修复了 `induction` 的 “pre-tactic” 代码块，使其始终带有缩进，从而避免意外使用。

* `ac_nf` tactic
  * [#5524](https://github.com/leanprover/lean4/pull/5524) 添加了 `ac_nf`，作为 `ac_rfl` 的对应物，用于按结合律与交换律规范化表达式。并用 BitVec 表达式对其进行了测试。

* `bv_decide`
  * [#5211](https://github.com/leanprover/lean4/pull/5211) 让 `extractLsb'` 而不是 `extractLsb` 成为 `bv_decide` 识别的原语。（@alexkeizer）
  * [#5365](https://github.com/leanprover/lean4/pull/5365) 添加了 `bv_decide` 诊断信息。
  * [#5375](https://github.com/leanprover/lean4/pull/5375) 为 `ofBool (a.getLsbD i)` 和 `ofBool a[i]` 添加了 `bv_decide` 规范化规则。（@alexkeizer）
  * [#5423](https://github.com/leanprover/lean4/pull/5423) 增强了 `bv_decide` 的重写规则。
  * [#5433](https://github.com/leanprover/lean4/pull/5433) 在 API 层展示 `bv_decide` 的反例。
  * [#5484](https://github.com/leanprover/lean4/pull/5484) 在 `bv_decide` 中处理带 `Nat` 自由变量的 `BitVec.ofNat`。
  * [#5506](https://github.com/leanprover/lean4/pull/5506)、[#5507](https://github.com/leanprover/lean4/pull/5507) 添加了 `bv_normalize` 规则。
  * [#5568](https://github.com/leanprover/lean4/pull/5568) 泛化了 `bv_normalize` 流水线，以支持更一般的预处理过程。
  * [#5573](https://github.com/leanprover/lean4/pull/5573) 让 `bv_normalize` 与当前的 BitVec 重写规则保持同步。
  * 清理工作：[#5408](https://github.com/leanprover/lean4/pull/5408)、[#5493](https://github.com/leanprover/lean4/pull/5493)、[#5578](https://github.com/leanprover/lean4/pull/5578)


* 精化改进
  * [#5266](https://github.com/leanprover/lean4/pull/5266) 在 `elab_as_elim` 过程中保留过度应用参数的顺序。
  * [#5510](https://github.com/leanprover/lean4/pull/5510) 泛化了 `elab_as_elim`，允许任意 motive 应用。
  * [#5283](https://github.com/leanprover/lean4/pull/5283)、[#5512](https://github.com/leanprover/lean4/pull/5512) 改进了具名参数抑制显式参数的方式。破坏性变更：某些此前可省略的显式参数现在可能需要显式写出 `_`。
  * [#5376](https://github.com/leanprover/lean4/pull/5376) 修改了实例投影的 binder 信息：对于实例，如果其类型中某参数是实例隐式参数，那么投影中该参数也会变为隐式。
  * [#5402](https://github.com/leanprover/lean4/pull/5402) 尽可能将宇宙元变量错误定位到 `let` 绑定和 `fun` binder 上；并让 “cannot synthesize metavariable” 错误优先于未解宇宙层级错误。
  * [#5419](https://github.com/leanprover/lean4/pull/5419) 在可约性设置为 `.reducible` 时，不再在 `match` 表达式判别式中规约 `ite`。
  * [#5474](https://github.com/leanprover/lean4/pull/5474) 让 autoparam 在失败时报告对应的参数/字段。
  * [#5530](https://github.com/leanprover/lean4/pull/5530) 让带 hygienic 名称类型的自动实例名本身也保持 hygienic。

* deriving 处理器
  * [#5432](https://github.com/leanprover/lean4/pull/5432) 让 `Repr` 的 deriving 实例支持显式类型参数。

* 函数式归纳
  * [#5364](https://github.com/leanprover/lean4/pull/5364) 在上下文中加入更多等式，并进行更谨慎的清理。

* 代码检查器
  * [#5335](https://github.com/leanprover/lean4/pull/5335) 修复了未使用变量 linter 会对 match/tactic 组合误报的问题。
  * [#5337](https://github.com/leanprover/lean4/pull/5337) 修复了未使用变量 linter 会对某些通配符模式误报的问题。

* 其他修复
  * [#4768](https://github.com/leanprover/lean4/pull/4768) 修复了当 `..` 与下一行的 `.` 同时出现时的解析错误。

* 元编程
  * [#3090](https://github.com/leanprover/lean4/pull/3090) 在 `Meta.evalExpr` 中处理层级参数。（@eric-wieser）
  * [#5401](https://github.com/leanprover/lean4/pull/5401) 为 `Inhabited (TacticM α)` 添加实例。（@alexkeizer）
  * [#5412](https://github.com/leanprover/lean4/pull/5412) 出于调试目的公开 Kernel.check。
  * [#5556](https://github.com/leanprover/lean4/pull/5556) 改进了 `inferType` 中 “invalid projection” 的类型推断错误。
  * [#5587](https://github.com/leanprover/lean4/pull/5587) 允许 `MVarId.assertHypotheses` 设置 `BinderInfo` 和 `LocalDeclKind`。
  * [#5588](https://github.com/leanprover/lean4/pull/5588) 添加了 `MVarId.tryClearMany'`，作为 `MVarId.tryClearMany` 的变体。



### 语言服务器、组件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

* [#5205](https://github.com/leanprover/lean4/pull/5205) 降低了 tactic 块中自动补全的延迟。
* [#5237](https://github.com/leanprover/lean4/pull/5237) 修复了 VS Code 中的符号出现高亮：当从标识符右侧将光标移入时，不会高亮其出现位置的问题。
* [#5257](https://github.com/leanprover/lean4/pull/5257) 修复了若干自动补全错误报告的情况。
* [#5299](https://github.com/leanprover/lean4/pull/5299) 允许在精化器无法提供上下文相关补全时，自动补全回退报告全局标识符补全项。
* [#5312](https://github.com/leanprover/lean4/pull/5312) 修复了模块头之后修改空白会导致服务器损坏的问题。
* [#5322](https://github.com/leanprover/lean4/pull/5322) 修复了多处自动补全报告不存在命名空间的情况。
* [#5428](https://github.com/leanprover/lean4/pull/5428) 确保在等待精化时，总会将某个最近的文件范围作为进度进行报告。


### 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Pretty-printing"
%%%

* [#4979](https://github.com/leanprover/lean4/pull/4979) 让美观打印器对作为 token 的标识符进行转义。
* [#5389](https://github.com/leanprover/lean4/pull/5389) 让格式化器使用当前的 token 表。
* [#5513](https://github.com/leanprover/lean4/pull/5513) 在格式化 token 时使用可换行空白而不是不可换行空白。


### 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Library"
%%%

* [#5222](https://github.com/leanprover/lean4/pull/5222) 减少了 `Json.compress` 的分配。
* [#5231](https://github.com/leanprover/lean4/pull/5231) 上游合入了 `Zero` 和 `NeZero`。
* [#5292](https://github.com/leanprover/lean4/pull/5292) 重构了 `Lean.Elab.Deriving.FromToJson`。（@arthur-adjedj）
* [#5415](https://github.com/leanprover/lean4/pull/5415) 实现了 `Repr Empty`。（@TomasPuverle）
* [#5421](https://github.com/leanprover/lean4/pull/5421) 实现了 `To/FromJSON Empty`。（@TomasPuverle）

* 逻辑
  * [#5263](https://github.com/leanprover/lean4/pull/5263) 允许仅凭 `Decidable (¬p)` 来简化 `dite_not`/`decide_not`。
  * [#5268](https://github.com/leanprover/lean4/pull/5268) 修复了 `ite_eq_left_iff` 的 binder。
  * [#5284](https://github.com/leanprover/lean4/pull/5284) 关闭了 `Inhabited (Sum α β)` 实例。
  * [#5355](https://github.com/leanprover/lean4/pull/5355) 为 `LawfulBEq` 添加了 simp 引理。
  * [#5374](https://github.com/leanprover/lean4/pull/5374) 为积类型添加了 `Nonempty` 实例，使更多 `partial` 函数能成功精化。
  * [#5447](https://github.com/leanprover/lean4/pull/5447) 更新了 Pi 实例名称。
  * [#5454](https://github.com/leanprover/lean4/pull/5454) 让某些实例参数变为隐式。
  * [#5456](https://github.com/leanprover/lean4/pull/5456) 添加了 `heq_comm`。
  * [#5529](https://github.com/leanprover/lean4/pull/5529) 将 `@[simp]` 从 `exists_prop'` 移到 `exists_prop`。

* `Bool`
  * [#5228](https://github.com/leanprover/lean4/pull/5228) 补齐了 Bool 引理中的空缺。
  * [#5332](https://github.com/leanprover/lean4/pull/5332) 为 Bool.xor 添加了记法 `^^`。
  * [#5351](https://github.com/leanprover/lean4/pull/5351) 移除了 `_root_.and`（以及 or/not/xor），改为导出/使用 `Bool.and`（等）。

* `BitVec`
  * [#5240](https://github.com/leanprover/lean4/pull/5240) 移除了右侧过于复杂的 `BitVec` simp。
  * [#5247](https://github.com/leanprover/lean4/pull/5247) 添加了 `BitVec.getElem_zeroExtend`。
  * [#5248](https://github.com/leanprover/lean4/pull/5248) 为 BitVec 添加了 simp 引理，改进了合流性。
  * [#5249](https://github.com/leanprover/lean4/pull/5249) 从某些 BitVec 引理上移除了 `@[simp]`。
  * [#5252](https://github.com/leanprover/lean4/pull/5252) 将 `BitVec.intMin/Max` 从 abbrev 改为 def。
  * [#5278](https://github.com/leanprover/lean4/pull/5278) 添加了 `BitVec.getElem_truncate`。（@tobiasgrosser）
  * [#5281](https://github.com/leanprover/lean4/pull/5281) 为 `bv_decide` 添加 udiv/umod bitblasting。（@bollu）
  * [#5297](https://github.com/leanprover/lean4/pull/5297) 添加了 BitVec 的无符号序理论结果。
  * [#5313](https://github.com/leanprover/lean4/pull/5313) 为 UInt 增加了更多基本的 BitVec 次序理论。
  * [#5314](https://github.com/leanprover/lean4/pull/5314) 添加了 `toNat_sub_of_le`。（@bollu）
  * [#5357](https://github.com/leanprover/lean4/pull/5357) 添加了 `BitVec.truncate` 引理。
  * [#5358](https://github.com/leanprover/lean4/pull/5358) 引入 `BitVec.setWidth` 以统一 zeroExtend 和 truncate。（@tobiasgrosser）
  * [#5361](https://github.com/leanprover/lean4/pull/5361) 添加了一些 BitVec GetElem 引理。
  * [#5385](https://github.com/leanprover/lean4/pull/5385) 添加了 `BitVec.ofBool_[and|or|xor]_ofBool` 定理。（@tobiasgrosser）
  * [#5404](https://github.com/leanprover/lean4/pull/5404) 添加了更多 `BitVec.getElem_*`。（@tobiasgrosser）
  * [#5410](https://github.com/leanprover/lean4/pull/5410) 为 `BitVec` 添加了 `Nat.{mul_two, two_mul, mul_succ, succ_mul}` 的对应结果。（@bollu）
  * [#5411](https://github.com/leanprover/lean4/pull/5411) 添加了 `BitVec.toNat_{add,sub,mul_of_lt}`，用于位向量无溢出推理。（@bollu）
  * [#5413](https://github.com/leanprover/lean4/pull/5413) 为 `BitVec.[and|or|xor]` 添加了 `_self`、`_zero` 和 `_allOnes`。（@tobiasgrosser）
  * [#5416](https://github.com/leanprover/lean4/pull/5416) 为 `BitVec.[and|or|xor]` 添加了 LawCommIdentity 和 IdempotentOp。（@tobiasgrosser）
  * [#5418](https://github.com/leanprover/lean4/pull/5418) 为 BitVec 添加可判定量词。
  * [#5450](https://github.com/leanprover/lean4/pull/5450) 添加了 `BitVec.toInt_[intMin|neg|neg_of_ne_intMin]`。（@tobiasgrosser）
  * [#5459](https://github.com/leanprover/lean4/pull/5459) 补充了缺失的 `BitVec` 引理。
  * [#5469](https://github.com/leanprover/lean4/pull/5469) 添加了 `BitVec.[not_not, allOnes_shiftLeft_or_shiftLeft, allOnes_shiftLeft_and_shiftLeft]`。（@luisacicolini）
  * [#5478](https://github.com/leanprover/lean4/pull/5478) 添加了 `BitVec.(shiftLeft_add_distrib, shiftLeft_ushiftRight)`。（@luisacicolini）
  * [#5487](https://github.com/leanprover/lean4/pull/5487) 添加了 `sdiv_eq`、`smod_eq`，以支持 `sdiv`/`smod` 的 bitblasting。（@bollu）
  * [#5491](https://github.com/leanprover/lean4/pull/5491) 添加了 `BitVec.toNat_[abs|sdiv|smod]`。（@tobiasgrosser）
  * [#5492](https://github.com/leanprover/lean4/pull/5492) 添加了 `BitVec.(not_sshiftRight, not_sshiftRight_not, getMsb_not, msb_not)`。（@luisacicolini）
  * [#5499](https://github.com/leanprover/lean4/pull/5499) 对 `BitVec.Lemmas` 进行处理：去掉非终端 simp。（@tobiasgrosser）
  * [#5505](https://github.com/leanprover/lean4/pull/5505) 取消了 `BitVec.divRec_succ'` 的 simp 化。
  * [#5508](https://github.com/leanprover/lean4/pull/5508) 添加了 `BitVec.getElem_[add|add_add_bool|mul|rotateLeft|rotateRight…`。（@tobiasgrosser）
  * [#5554](https://github.com/leanprover/lean4/pull/5554) 添加了 `Bitvec.[add, sub, mul]_eq_xor` 和 `width_one_cases`。（@luisacicolini）

* `List`
  * [#5242](https://github.com/leanprover/lean4/pull/5242) 改进了 `List.mergeSort` 引理的命名。
  * [#5302](https://github.com/leanprover/lean4/pull/5302) 为 `mergeSort` 比较器提供 autoParam。
  * [#5373](https://github.com/leanprover/lean4/pull/5373) 修复了 `List.length_mergeSort` 的名称。
  * [#5377](https://github.com/leanprover/lean4/pull/5377) 上游合入了 `map_mergeSort`。
  * [#5378](https://github.com/leanprover/lean4/pull/5378) 修改了与 `mergeSort` 相关引理的签名。
  * [#5245](https://github.com/leanprover/lean4/pull/5245) 避免在没有 List.Impl 的情况下导入 `List.Basic`。
  * [#5260](https://github.com/leanprover/lean4/pull/5260) 审查了 List API。
  * [#5264](https://github.com/leanprover/lean4/pull/5264) 审查了 List API。
  * [#5269](https://github.com/leanprover/lean4/pull/5269) 移除了 HashMap 中重复的 Pairwise 和 Sublist。
  * [#5271](https://github.com/leanprover/lean4/pull/5271) 从 `List.head_mem` 及类似引理中移除了 @[simp]。
  * [#5273](https://github.com/leanprover/lean4/pull/5273) 添加了关于 `List.attach` 的引理。
  * [#5275](https://github.com/leanprover/lean4/pull/5275) 反转了 `List.tail_map` 的方向。
  * [#5277](https://github.com/leanprover/lean4/pull/5277) 添加了更多 `List.attach` 引理。
  * [#5285](https://github.com/leanprover/lean4/pull/5285) 添加了 `List.count` 引理。
  * [#5287](https://github.com/leanprover/lean4/pull/5287) 在 `List.filter` 中使用布尔谓词。
  * [#5289](https://github.com/leanprover/lean4/pull/5289) 添加了 `List.mem_ite_nil_left` 及类似结果。
  * [#5293](https://github.com/leanprover/lean4/pull/5293) 清理了 `List.findIdx` / `List.take` 引理。
  * [#5294](https://github.com/leanprover/lean4/pull/5294) 调整了 `List.getElem_take` 上 prime 的使用。
  * [#5300](https://github.com/leanprover/lean4/pull/5300) 添加了更多 `List.findIdx` 定理。
  * [#5310](https://github.com/leanprover/lean4/pull/5310) 修复了 `List.all/any` 引理。
  * [#5311](https://github.com/leanprover/lean4/pull/5311) 修复了 `List.countP` 引理。
  * [#5316](https://github.com/leanprover/lean4/pull/5316) 添加了 `List.tail` 引理。
  * [#5331](https://github.com/leanprover/lean4/pull/5331) 修复了 `List.getElem_mem` 的隐式性。
  * [#5350](https://github.com/leanprover/lean4/pull/5350) 添加了 `List.replicate` 引理。
  * [#5352](https://github.com/leanprover/lean4/pull/5352) 添加了 `List.attachWith` 引理。
  * [#5353](https://github.com/leanprover/lean4/pull/5353) 添加了 `List.head_mem_head?`。
  * [#5360](https://github.com/leanprover/lean4/pull/5360) 添加了关于 `List.tail` 的引理。
  * [#5391](https://github.com/leanprover/lean4/pull/5391) 审查了 `List.erase` / `List.find` 引理。
  * [#5392](https://github.com/leanprover/lean4/pull/5392) 添加了 `List.fold` / `attach` 引理。
  * [#5393](https://github.com/leanprover/lean4/pull/5393) 添加了 `List.fold` 关系子。
  * [#5394](https://github.com/leanprover/lean4/pull/5394) 添加了关于 `List.maximum?` 的引理。
  * [#5403](https://github.com/leanprover/lean4/pull/5403) 添加了关于 `List.toArray` 的定理。
  * [#5405](https://github.com/leanprover/lean4/pull/5405) 反转了 `List.set_map` 的方向。
  * [#5448](https://github.com/leanprover/lean4/pull/5448) 添加了关于 `List.IsPrefix` 的引理。（@Command-Master）
  * [#5460](https://github.com/leanprover/lean4/pull/5460) 补上了缺失的 `List.set_replicate_self`。
  * [#5518](https://github.com/leanprover/lean4/pull/5518) 将 `List.maximum?` 重命名为 `max?`。
  * [#5519](https://github.com/leanprover/lean4/pull/5519) 上游合入了 `List.fold` 引理。
  * [#5520](https://github.com/leanprover/lean4/pull/5520) 恢复了 `List.getElem_mem` 等上的 `@[simp]`。
  * [#5521](https://github.com/leanprover/lean4/pull/5521) 修复了 List simp。
  * [#5550](https://github.com/leanprover/lean4/pull/5550) 添加了 `List.unattach` 及相关 simp 引理。
  * [#5594](https://github.com/leanprover/lean4/pull/5594) 添加了更适合归纳使用的 `List.min?_cons`。

* `Array`
  * [#5246](https://github.com/leanprover/lean4/pull/5246) 清理了 Array.Lemmas 的导入。
  * [#5255](https://github.com/leanprover/lean4/pull/5255) 拆分了 Init.Data.Array.Lemmas，以改善自举过程。
  * [#5288](https://github.com/leanprover/lean4/pull/5288) 将 `Array.data` 重命名为 `Array.toList`。
  * [#5303](https://github.com/leanprover/lean4/pull/5303) 清理了 `List.getElem_append` 的各个变体。
  * [#5304](https://github.com/leanprover/lean4/pull/5304) 添加了 `Array.not_mem_empty`。
  * [#5400](https://github.com/leanprover/lean4/pull/5400) 重组了 Array/Basic。
  * [#5420](https://github.com/leanprover/lean4/pull/5420) 让 `Array` 函数要么是 semireducible，要么使用结构化递归。
  * [#5422](https://github.com/leanprover/lean4/pull/5422) 重构了 `DecidableEq (Array α)`。
  * [#5452](https://github.com/leanprover/lean4/pull/5452) 重构了 Array。
  * [#5458](https://github.com/leanprover/lean4/pull/5458) 在重构后清理了 Array 文档字符串。
  * [#5461](https://github.com/leanprover/lean4/pull/5461) 恢复了 `Array.swapAt!_def` 上的 `@[simp]`。
  * [#5465](https://github.com/leanprover/lean4/pull/5465) 改进了 Array GetElem 引理。
  * [#5466](https://github.com/leanprover/lean4/pull/5466) 添加了 `Array.foldX` 引理。
  * [#5472](https://github.com/leanprover/lean4/pull/5472) 添加了关于 `List.toArray` 的 @[simp] 引理。
  * [#5485](https://github.com/leanprover/lean4/pull/5485) 反转了 `toArray_concat` 的 simp 方向。
  * [#5514](https://github.com/leanprover/lean4/pull/5514) 添加了 `Array.eraseReps`。
  * [#5515](https://github.com/leanprover/lean4/pull/5515) 上游合入了 `Array.qsortOrd`。
  * [#5516](https://github.com/leanprover/lean4/pull/5516) 上游合入了 `Subarray.empty`。
  * [#5526](https://github.com/leanprover/lean4/pull/5526) 修复了 `Array.length_toList` 的名称。
  * [#5527](https://github.com/leanprover/lean4/pull/5527) 减少了 Array 中对已弃用引理的使用。
  * [#5534](https://github.com/leanprover/lean4/pull/5534) 清理了 Array GetElem 引理。
  * [#5536](https://github.com/leanprover/lean4/pull/5536) 修复了 `Array.modify` 引理。
  * [#5551](https://github.com/leanprover/lean4/pull/5551) 上游合入了 `Array.flatten` 引理。
  * [#5552](https://github.com/leanprover/lean4/pull/5552) 将数组 “bang” 索引 `[]!` 的明显情形改为依赖现有假设。（@TomasPuverle）
  * [#5577](https://github.com/leanprover/lean4/pull/5577) 为 `Array.size_feraseIdx` 添加缺失的 simp。
  * [#5586](https://github.com/leanprover/lean4/pull/5586) 添加了 `Array/Option.unattach`。

* `Option`
  * [#5272](https://github.com/leanprover/lean4/pull/5272) 从 `Option.pmap/pbind` 移除了 @[simp]，并添加了 simp 引理。
  * [#5307](https://github.com/leanprover/lean4/pull/5307) 恢复了 Option simp 的合流性。
  * [#5354](https://github.com/leanprover/lean4/pull/5354) 从 `Option.bind_map` 移除了 @[simp]。
  * [#5532](https://github.com/leanprover/lean4/pull/5532) 添加了 `Option.attach`。
  * [#5539](https://github.com/leanprover/lean4/pull/5539) 修复了 `Option.mem_toList` 的显式性。

* `Nat`
  * [#5241](https://github.com/leanprover/lean4/pull/5241) 为 `Nat.add_eq_zero_iff` 添加了 @[simp]。
  * [#5261](https://github.com/leanprover/lean4/pull/5261) 添加了 Nat 按位运算引理。
  * [#5262](https://github.com/leanprover/lean4/pull/5262) 让 `Nat.testBit_add_one` 不再是全局 simp 引理。
  * [#5267](https://github.com/leanprover/lean4/pull/5267) 保护了一些 Nat 按位运算定理。
  * [#5305](https://github.com/leanprover/lean4/pull/5305) 重命名了 Nat 按位运算引理。
  * [#5306](https://github.com/leanprover/lean4/pull/5306) 添加了 `Nat.self_sub_mod` 引理。
  * [#5503](https://github.com/leanprover/lean4/pull/5503) 为上游合入的 `Nat.lt_off_iff` 恢复了 @[simp]。

* `Int`
  * [#5301](https://github.com/leanprover/lean4/pull/5301) 将 `Int.div/mod` 重命名为 `Int.tdiv/tmod`。
  * [#5320](https://github.com/leanprover/lean4/pull/5320) 向 DivModLemmas 添加了 `ediv_nonneg_of_nonpos_of_nonpos`。（@sakehl）

* `Fin`
  * [#5250](https://github.com/leanprover/lean4/pull/5250) 补充了关于 `Fin.ofNat'` 的缺失引理。
  * [#5356](https://github.com/leanprover/lean4/pull/5356) 让 `Fin.ofNat'` 使用 `NeZero`。
  * [#5379](https://github.com/leanprover/lean4/pull/5379) 从部分 Fin 引理中移除了 @[simp]。
  * [#5380](https://github.com/leanprover/lean4/pull/5380) 补充了缺失的 Fin @[simp] 引理。

* `HashMap`
  * [#5244](https://github.com/leanprover/lean4/pull/5244) 添加了 (`DHashMap`|`HashMap`|`HashSet`).(`getKey?`|`getKey`|`getKey!`|`getKeyD`)。
  * [#5362](https://github.com/leanprover/lean4/pull/5362) 移除了对 `Lean.(HashSet|HashMap)` 的最后一次使用。
  * [#5369](https://github.com/leanprover/lean4/pull/5369) 添加了 `HashSet.ofArray`。
  * [#5370](https://github.com/leanprover/lean4/pull/5370) 添加了 `HashSet.partition`。
  * [#5581](https://github.com/leanprover/lean4/pull/5581) 为 `HashMap`/`Set` 添加了 `Singleton`/`Insert`/`Union` 实例。
  * [#5582](https://github.com/leanprover/lean4/pull/5582) 添加了 `HashSet.all`/`any`。
  * [#5590](https://github.com/leanprover/lean4/pull/5590) 为 `HashMap`/`Set.Raw` 添加了 `Insert`/`Singleton`/`Union` 实例。
  * [#5591](https://github.com/leanprover/lean4/pull/5591) 添加了 `HashSet.Raw.all/any`。

* `Monads`
  * [#5463](https://github.com/leanprover/lean4/pull/5463) 上游合入了一些单子引理。
  * [#5464](https://github.com/leanprover/lean4/pull/5464) 调整了单子引理上的 simp 属性。
  * [#5522](https://github.com/leanprover/lean4/pull/5522) 添加了更多 monadic simp 引理。

* simp 引理清理
  * [#5251](https://github.com/leanprover/lean4/pull/5251) 移除了冗余的 simp 标注。
  * [#5253](https://github.com/leanprover/lean4/pull/5253) 移除了不会触发的 Int simp 引理。
  * [#5254](https://github.com/leanprover/lean4/pull/5254) 让 iff 两侧都出现的变量变为隐式。
  * [#5381](https://github.com/leanprover/lean4/pull/5381) 清理了冗余的 simp 引理。


### 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Compiler___-runtime___-and-FFI"
%%%

* [#4685](https://github.com/leanprover/lean4/pull/4685) 修复了 C 语言 `run_new_frontend` 签名中的一个拼写错误。
* [#4729](https://github.com/leanprover/lean4/pull/4729) 让 IR 检查器提示使用 `noncomputable`。
* [#5143](https://github.com/leanprover/lean4/pull/5143) 为 Lake 添加了共享库。
* [#5437](https://github.com/leanprover/lean4/pull/5437) 移除了（语法上）重复的导入。（@euprunin）
* [#5462](https://github.com/leanprover/lean4/pull/5462) 更新了 `src/lake/lakefile.toml`，以适配调整后的 Lake 构建流程。
* [#5541](https://github.com/leanprover/lean4/pull/5541) 在构建前移除新的共享库，以更好支持 Windows。
* [#5558](https://github.com/leanprover/lean4/pull/5558) 让 `lean.h` 能被 MSVC 编译。（@kant2002）
* [#5564](https://github.com/leanprover/lean4/pull/5564) 移除了不合规范的 0 大小数组。（@eric-wieser）


### Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Lake"
%%%
* Reservoir 构建缓存。Lake 现在会在构建前尝试从 Reservoir 获取该包的预构建副本。此功能仅对 leanprover 或 leanprover-community 组织中、且版本已被 Reservoir 索引的包启用。用户可以通过在 CLI 上传入 --no-cache，或将环境变量 LAKE_NO_CACHE 设为 true，强制 Lake 从源码构建包。[#5486](https://github.com/leanprover/lean4/pull/5486)、[#5572](https://github.com/leanprover/lean4/pull/5572)、[#5583](https://github.com/leanprover/lean4/pull/5583)、[#5600](https://github.com/leanprover/lean4/pull/5600)、[#5641](https://github.com/leanprover/lean4/pull/5641)、[#5642](https://github.com/leanprover/lean4/pull/5642)。
* [#5504](https://github.com/leanprover/lean4/pull/5504) 让 lake new 和 lake init 默认生成 TOML 配置。
* [#5878](https://github.com/leanprover/lean4/pull/5878) 修复了一个严重问题：当 Lake 试图清理以错误名称声明的依赖时，可能会删除路径依赖。

* **破坏性变更**
  * [#5641](https://github.com/leanprover/lean4/pull/5641) 在包内构建某个目标时，Lake 将不再构建该包依赖项的包级额外目标依赖。从技术上说，一个包的 extraDep facet 不再传递性地构建其依赖项的 extraDep facet（其中包括它们的 extraDepTargets）。

### 文档修复
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Documentation-fixes"
%%%

* [#3918](https://github.com/leanprover/lean4/pull/3918) 添加了 `@[builtin_doc]` attribute。（@digama0）
* [#4305](https://github.com/leanprover/lean4/pull/4305) 解释了借用语法。（@eric-wieser）
* [#5349](https://github.com/leanprover/lean4/pull/5349) 为 `groupBy.loop` 添加了文档。（@vihdzp）
* [#5473](https://github.com/leanprover/lean4/pull/5473) 修复了 `BitVec.mul` 文档字符串中的拼写错误。（@llllvvuu）
* [#5476](https://github.com/leanprover/lean4/pull/5476) 修复了 `Lean.MetavarContext` 中的拼写错误。
* [#5481](https://github.com/leanprover/lean4/pull/5481) 移除了对 `Lean.withSeconds` 的提及。（@alexkeizer）
* [#5497](https://github.com/leanprover/lean4/pull/5497) 更新了 `toUIntX` 函数的文档与测试。（@TomasPuverle）
* [#5087](https://github.com/leanprover/lean4/pull/5087) 说明了 `inferType` 并不保证类型正确性。
* @euprunin 对文档字符串中的拼写做了大量修复：[#5425](https://github.com/leanprover/lean4/pull/5425) [#5426](https://github.com/leanprover/lean4/pull/5426) [#5427](https://github.com/leanprover/lean4/pull/5427) [#5430](https://github.com/leanprover/lean4/pull/5430) [#5431](https://github.com/leanprover/lean4/pull/5431) [#5434](https://github.com/leanprover/lean4/pull/5434) [#5435](https://github.com/leanprover/lean4/pull/5435) [#5436](https://github.com/leanprover/lean4/pull/5436) [#5438](https://github.com/leanprover/lean4/pull/5438) [#5439](https://github.com/leanprover/lean4/pull/5439) [#5440](https://github.com/leanprover/lean4/pull/5440) [#5599](https://github.com/leanprover/lean4/pull/5599)

### CI 变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___13___0-_LPAR_2024-11-01_RPAR_--Changes-to-CI"
%%%

* [#5343](https://github.com/leanprover/lean4/pull/5343) 允许通过评论添加 `release-ci` 标签。（@thorimur）
* [#5344](https://github.com/leanprover/lean4/pull/5344) 在工作流中正确设置检查级别。（@thorimur）
* [#5444](https://github.com/leanprover/lean4/pull/5444) 让 Mathlib 的 `lean-pr-testing-NNNN` 分支使用 Batteries 的 `lean-pr-testing-NNNN` 分支。
* [#5489](https://github.com/leanprover/lean4/pull/5489) 在更新 `lean-pr-testing` 分支时提交 `lake-manifest.json`。
* [#5490](https://github.com/leanprover/lean4/pull/5490) 在 `pr-release.yml` 中为评论和分支操作使用分离的 secrets。

```
