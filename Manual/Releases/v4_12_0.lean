/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.12.0 (2024-10-01)" =>
%%%
tag := "release-v4.12.0"
file := "v4.12.0"
%%%

````markdown
````
# 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

````markdown

* `bv_decide` 策略。本次发布引入了一个新策略，用于证明涉及 `BitVec` 和 `Bool` 的目标。它会将目标化简为一个 SAT 实例，由外部求解器将其驳倒，然后在 Lean 中检查生成的 LRAT 证明。接着通过反射合成该目标的证明。由于这一过程使用的是经过验证的算法，因此这个策略生成的证明会用到 `Lean.ofReduceBool`，也就是说该策略将 Lean 编译器纳入了可信计算基。外部求解器 CaDiCaL 已随 Lean 一起提供，使用 `bv_decide` 时无需另行安装。

  例如，我们可以用 `bv_decide` 验证某个位运算公式至多只保留一个置位比特：
  ```lean
  def popcount (x : BitVec 64) : BitVec 64 :=
    let rec go (x pop : BitVec 64) : Nat → BitVec 64
      | 0 => pop
      | n + 1 => go (x >>> 2) (pop + (x &&& 1)) n
    go x 0 64

  example (x : BitVec 64) : popcount ((x &&& (x - 1)) ^^^ x) ≤ 1 := by
    simp only [popcount, popcount.go]
    bv_decide
  ```
  当外部求解器无法驳倒 `bv_decide` 生成的 SAT 实例时，它可以报告一个反例：
  ```lean
  /--
  error: The prover found a counterexample, consider the following assignment:
  x = 0xffffffffffffffff#64
  -/
  #guard_msgs in
  example (x : BitVec 64) : x < x + 1 := by
    bv_decide
  ```

  更详细的概览请参阅 `Lean.Elab.Tactic.BVDecide`，示例可见 `tests/lean/run/bv_*`。

  [#5013](https://github.com/leanprover/lean4/pull/5013)、[#5074](https://github.com/leanprover/lean4/pull/5074)、[#5100](https://github.com/leanprover/lean4/pull/5100)、[#5113](https://github.com/leanprover/lean4/pull/5113)、[#5137](https://github.com/leanprover/lean4/pull/5137)、[#5203](https://github.com/leanprover/lean4/pull/5203)、[#5212](https://github.com/leanprover/lean4/pull/5212)、[#5220](https://github.com/leanprover/lean4/pull/5220)。

* `simp` 策略
  * [#4988](https://github.com/leanprover/lean4/pull/4988) 修复了 `reducePow` simproc 中的 panic。
  * [#5071](https://github.com/leanprover/lean4/pull/5071) 将在 [#4202](https://github.com/leanprover/lean4/pull/4202) 中为 `simp` 引入的 `index` 选项暴露给了 `dsimp` 策略。
  * [#5159](https://github.com/leanprover/lean4/pull/5159) 修复了 `Fin.isValue` simproc 中的 panic。
  * [#5167](https://github.com/leanprover/lean4/pull/5167) 和 [#5175](https://github.com/leanprover/lean4/pull/5175) 将 `simpCtorEq` simproc 重命名为 `reduceCtorEq`，并让它变为可选项。（见破坏性变更。）
  * [#5187](https://github.com/leanprover/lean4/pull/5187) 确保在 `norm_cast` 策略中启用 `reduceCtorEq`。
  * [#5073](https://github.com/leanprover/lean4/pull/5073) 修改了 simp 调试 trace 消息：在定义性重写模式下，用 “dpre” 和 “dpost” 代替 “pre” 和 “post” 作为标签。[#5054](https://github.com/leanprover/lean4/pull/5054) 解释了 `trace.Debug.Meta.Tactic.simp` trace 消息中的 `reduce` 步骤。
* `ext` 策略
  * [#4996](https://github.com/leanprover/lean4/pull/4996) 将默认最大迭代深度从 1000000 降到 100。
* `induction` 策略
  * [#5117](https://github.com/leanprover/lean4/pull/5117) 修复了一个 bug：小前提中的 `let` 绑定此前不会被正确计数。

* `omega` 策略
  * [#5157](https://github.com/leanprover/lean4/pull/5157) 修复了一个 panic。

* `conv` 策略
  * [#5149](https://github.com/leanprover/lean4/pull/5149) 改进了 `arg n`，使其能够处理子单例实例参数。

* [#5044](https://github.com/leanprover/lean4/pull/5044) 上游合入了 `#time` 命令。
* [#5079](https://github.com/leanprover/lean4/pull/5079) 让 `#check` 和 `#reduce` 对精译后的项进行类型检查。

* **增量化**
  * [#4974](https://github.com/leanprover/lean4/pull/4974) 修复了一个回归：此前不会中断旧文档版本的精译。
  * [#5004](https://github.com/leanprover/lean4/pull/5004) 修复了一个性能回归。
  * [#5001](https://github.com/leanprover/lean4/pull/5001) 在声明带有 `where` 子句时禁用增量化主体精译。
  * [#5018](https://github.com/leanprover/lean4/pull/5018) 为 ilean 生成在命令行上启用了 infotree。
  * [#5040](https://github.com/leanprover/lean4/pull/5040) 和 [#5056](https://github.com/leanprover/lean4/pull/5056) 改进了信息树的性能。
  * [#5090](https://github.com/leanprover/lean4/pull/5090) 在 `case .. | ..` 策略中禁用增量化。
  * [#5312](https://github.com/leanprover/lean4/pull/5312) 修复了一个 bug：在模块头之后修改空白可能会破坏后续命令。

* **定义**
  * [#5016](https://github.com/leanprover/lean4/pull/5016) 和 [#5066](https://github.com/leanprover/lean4/pull/5066) 添加了 `clean_wf` 策略，用于在 `decreasing_by` 中清理策略状态。可通过 `set_option debug.rawDecreasingByGoal false` 禁用。
  * [#5055](https://github.com/leanprover/lean4/pull/5055) 统一了结构化递归与良基递归的等式定理。
  * [#5041](https://github.com/leanprover/lean4/pull/5041) 允许互递归函数在“固定参数前缀”中使用不同的参数名。
  * [#4154](https://github.com/leanprover/lean4/pull/4154) 和 [#5109](https://github.com/leanprover/lean4/pull/5109) 为非递归函数添加了细粒度等式引理。见破坏性变更。
  * [#5129](https://github.com/leanprover/lean4/pull/5129) 统一了递归定义和非递归定义的等式引理。可将 `backward.eqns.deepRecursiveSplit` 选项设为 `false` 以恢复旧行为。见破坏性变更。
  * [#5141](https://github.com/leanprover/lean4/pull/5141) 添加了 `f.eq_unfold` 引理。现在 Lean 会生成如下这组重写规则：
    ```
    Option.map.eq_1      : Option.map f none = none
    Option.map.eq_2      : Option.map f (some x) = some (f x)
    Option.map.eq_def    : Option.map f p = match o with | none => none | (some x) => some (f x)
    Option.map.eq_unfold : Option.map = fun f p => match o with | none => none | (some x) => some (f x)
    ```
    `f.eq_unfold` 这一变体特别适合配合 `rw` 在 binder 下进行重写。
  * [#5136](https://github.com/leanprover/lean4/pull/5136) 修复了对谓词进行递归时的一些 bug。

* **变量引入**
  * [#5206](https://github.com/leanprover/lean4/pull/5206) 记录了 `include` 目前只作用于定理。

* **精译**
  * [#4926](https://github.com/leanprover/lean4/pull/4926) 修复了一个 bug：autoparam 错误此前会关联到错误的源码位置。
  * [#4833](https://github.com/leanprover/lean4/pull/4833) 修复了 cdot 匿名函数（例如 `(· + ·)`）在处理歧义记法时的问题。它会为参数编号，因此该示例现在展开为 `fun x1 x2 => x1 + x2`，而不是 `fun x x_1 => x + x_1`。
  * [#5037](https://github.com/leanprover/lean4/pull/5037) 增强了用于证明数组索引未越界的策略。
  * [#5119](https://github.com/leanprover/lean4/pull/5119) 修复了用于证明索引未越界的策略中的一个 bug：它在存在 mvar 时可能会陷入循环。
  * [#5072](https://github.com/leanprover/lean4/pull/5072) 让结构体实例记法的 “not a field of structure” 错误中的结构体类型可点击。
  * [#4717](https://github.com/leanprover/lean4/pull/4717) 修复了一个 bug：互递归 `inductive` 命令可能生成会被内核拒绝的项。
  * [#5142](https://github.com/leanprover/lean4/pull/5142) 修复了一个 bug：在混合 binder 更新与声明时，`variable` 可能失败。

* **其他修复或改进**
  * [#5118](https://github.com/leanprover/lean4/pull/5118) 更改了 `syntheticHole` 解析器的定义，因此悬停在 `?_` 中的 `_` 上时会显示 synthetic hole 的文档字符串。
  * [#5173](https://github.com/leanprover/lean4/pull/5173) 在消息中为 ✅️、❌️、💥️ 使用 emoji 变体选择符，从而改进字体选择。
  * [#5183](https://github.com/leanprover/lean4/pull/5183) 修复了 `rename_i` 中一个 bug：实现细节假设此前可能被重命名。

````
# 语言服务器、组件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

````markdown

* [#4821](https://github.com/leanprover/lean4/pull/4821) 解决了两个尤其影响 Windows 用户的语言服务器 bug。(1) 编辑头部可能导致 watchdog 无法正确重启文件 worker，从而使文件看起来一直在处理中。(2) 在特别慢的 Windows 机器上，我们发现启动语言服务器有时根本无法成功。该 PR 还解决了一个问题：文件 worker 重启期间收到的消息此前不会在重启后正确转发给相应的文件 worker。
* [#5006](https://github.com/leanprover/lean4/pull/5006) 更新了用户组件手册。
* [#5193](https://github.com/leanprover/lean4/pull/5193) 使用 Lean 4 扩展的新显示名（“Lean 4”）更新了快速入门指南。
* [#5185](https://github.com/leanprover/lean4/pull/5185) 修复了一个 bug：随着时间推移，“import out of date” 消息会不断累积。
* [#4900](https://github.com/leanprover/lean4/pull/4900) 将 ilean 加载性能提高了大约两倍。它优化了 JSON 解析器以及从 JSON 到 Lean 数据结构的转换；详见 PR 描述。
* **其他修复或改进**
  * [#5031](https://github.com/leanprover/lean4/pull/5031) 将 `Lsp.Diagnostics` 中的一个实例局部化。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Pretty-printing"
%%%

````markdown

* [#4976](https://github.com/leanprover/lean4/pull/4976) 引入了 `@[app_delab]`，这是一个用于为特定常量创建反精译器的宏。语法 `@[app_delab ident]` 会将 `ident` 解析为其常量名 `name`，然后展开为 `@[delab app.name]`。
* [#4982](https://github.com/leanprover/lean4/pull/4982) 修复了一个 bug：美观打印器此前假设结构体投影一定类型正确（这类项可能出现在类型不匹配错误中）。同时改进了结构体 `#print` 输出的可悬停性。
* [#5218](https://github.com/leanprover/lean4/pull/5218) 和 [#5239](https://github.com/leanprover/lean4/pull/5239) 添加了调试选项 `pp.exprSizes`。当其为 true 时，每个美观打印表达式前都会带上 `[size a/b/c]`，其中 `a` 是不共享时的大小，`b` 是实际大小，`c` 是最大可能共享时的大小。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Library"
%%%

````markdown

* [#5020](https://github.com/leanprover/lean4/pull/5020) 交换了 `Membership.mem` 的参数。这样做的一个目的是让类似集合的 `CoeSort` 强制转换引用 eta 展开的函数 `fun x => Membership.mem s x`，从而可在许多计算中发生规约。另一个目的是让将 `s` 参数放在前面可以得到更好的 discrimination tree 键。（见破坏性变更。）
* `Array`
  * [#4970](https://github.com/leanprover/lean4/pull/4970) 为 `Array.ext` 添加了 `@[ext]` attribute。
  * [#4957](https://github.com/leanprover/lean4/pull/4957) 弃用了 `Array.get_modify`。
* `List`
  * [#4995](https://github.com/leanprover/lean4/pull/4995) 上游合入了 `List.findIdx` 引理。
  * [#5029](https://github.com/leanprover/lean4/pull/5029)、[#5048](https://github.com/leanprover/lean4/pull/5048) 和 [#5132](https://github.com/leanprover/lean4/pull/5132) 添加了 `List.Sublist` 引理，其中一部分已上游合入。[#5077](https://github.com/leanprover/lean4/pull/5077) 修复了 refl/rfl 引理 binder 的隐式性。添加了 `List.Sublist` 定理。
  * [#5047](https://github.com/leanprover/lean4/pull/5047) 上游合入了 `List.Pairwise` 引理。
  * [#5053](https://github.com/leanprover/lean4/pull/5053)、[#5124](https://github.com/leanprover/lean4/pull/5124) 和 [#5161](https://github.com/leanprover/lean4/pull/5161) 添加了 `List.find?/findSome?/findIdx?` 定理。
  * [#5039](https://github.com/leanprover/lean4/pull/5039) 添加了 `List.foldlRecOn` 和 `List.foldrRecOn` 递归原理，用于证明关于 `List.foldl` 和 `List.foldr` 的性质。
  * [#5069](https://github.com/leanprover/lean4/pull/5069) 上游合入了 `List.Perm`。
  * [#5092](https://github.com/leanprover/lean4/pull/5092) 和 [#5107](https://github.com/leanprover/lean4/pull/5107) 添加了 `List.mergeSort` 及其高效的 `@[csimp]` 实现。
  * [#5103](https://github.com/leanprover/lean4/pull/5103) 让 `List.subset` 的 simp 引理更激进。
  * [#5106](https://github.com/leanprover/lean4/pull/5106) 修改了 `List.getLast?_cons` 的陈述。
  * [#5123](https://github.com/leanprover/lean4/pull/5123) 和 [#5158](https://github.com/leanprover/lean4/pull/5158) 添加了 `List.range` 和 `List.iota` 引理。
  * [#5130](https://github.com/leanprover/lean4/pull/5130) 添加了 `List.join` 引理。
  * [#5131](https://github.com/leanprover/lean4/pull/5131) 添加了 `List.append` 引理。
  * [#5152](https://github.com/leanprover/lean4/pull/5152) 添加了 `List.erase(|P|Idx)` 引理。
  * [#5127](https://github.com/leanprover/lean4/pull/5127) 做了若干引理更新。
  * [#5153](https://github.com/leanprover/lean4/pull/5153) 和 [#5160](https://github.com/leanprover/lean4/pull/5160) 添加了关于 `List.attach` 和 `List.pmap` 的引理。
  * [#5164](https://github.com/leanprover/lean4/pull/5164)、[#5177](https://github.com/leanprover/lean4/pull/5177) 和 [#5215](https://github.com/leanprover/lean4/pull/5215) 添加了 `List.find?` 与 `List.range'/range/iota` 引理。
  * [#5196](https://github.com/leanprover/lean4/pull/5196) 添加了 `List.Pairwise_erase` 及相关引理。
  * [#5151](https://github.com/leanprover/lean4/pull/5151) 和 [#5163](https://github.com/leanprover/lean4/pull/5163) 改进了 `List` simp 引理的合流性。[#5105](https://github.com/leanprover/lean4/pull/5105) 和 [#5102](https://github.com/leanprover/lean4/pull/5102) 也调整了 `List` simp 引理。
  * [#5178](https://github.com/leanprover/lean4/pull/5178) 让 `List.getLast_eq_iff_getLast_eq_some` 不再是 simp 引理。
  * [#5210](https://github.com/leanprover/lean4/pull/5210) 反转了 `List.getElem_drop` 和 `List.getElem_drop'` 的含义。
  * [#5214](https://github.com/leanprover/lean4/pull/5214) 在可能时将 `@[csimp]` 引理前移。
* `Nat` 与 `Int`
  * [#5104](https://github.com/leanprover/lean4/pull/5104) 添加了 `Nat.add_left_eq_self` 及相关结果。
  * [#5146](https://github.com/leanprover/lean4/pull/5146) 添加了缺失的 `Nat.and_xor_distrib_(left|right)`。
  * [#5148](https://github.com/leanprover/lean4/pull/5148) 和 [#5190](https://github.com/leanprover/lean4/pull/5190) 改进了 `Nat` 和 `Int` simp 引理的合流性。
  * [#5165](https://github.com/leanprover/lean4/pull/5165) 调整了 `Int` simp 引理。
  * [#5166](https://github.com/leanprover/lean4/pull/5166) 添加了将 `neg` 与 `emod`/`mod` 联系起来的 `Int` 引理。
  * [#5208](https://github.com/leanprover/lean4/pull/5208) 反转了 `Int.toNat_sub` simp 引理的方向。
  * [#5209](https://github.com/leanprover/lean4/pull/5209) 添加了 `Nat.bitwise` 引理。
  * [#5230](https://github.com/leanprover/lean4/pull/5230) 修正了整数除法与取模的文档字符串。
* `Option`
  * [#5128](https://github.com/leanprover/lean4/pull/5128) 和 [#5154](https://github.com/leanprover/lean4/pull/5154) 添加了 `Option` 引理。
* `BitVec`
  * [#4889](https://github.com/leanprover/lean4/pull/4889) 添加了 `sshiftRight` 的 bitblasting。
  * [#4981](https://github.com/leanprover/lean4/pull/4981) 为 `BitVec.[and|or|xor]` 添加了 `Std.Associative` 和 `Std.Commutative` 实例。
  * [#4913](https://github.com/leanprover/lean4/pull/4913) 为 `BitVec` 模块启用了 `missingDocs` 错误。
  * [#4930](https://github.com/leanprover/lean4/pull/4930) 让 `BitVec` 的参数名更一致。
  * [#5098](https://github.com/leanprover/lean4/pull/5098) 添加了 `BitVec.intMin`。并引入 `boolToPropSimps` simp 集，用于把布尔表达式转换为命题表达式。
  * [#5200](https://github.com/leanprover/lean4/pull/5200) 和 [#5217](https://github.com/leanprover/lean4/pull/5217) 将 `BitVec.getLsb` 等重命名为 `BitVec.getLsbD` 等，以与 `List`/`Array`/等保持命名一致。
  * **定理：** [#4977](https://github.com/leanprover/lean4/pull/4977)、[#4951](https://github.com/leanprover/lean4/pull/4951)、[#4667](https://github.com/leanprover/lean4/pull/4667)、[#5007](https://github.com/leanprover/lean4/pull/5007)、[#4997](https://github.com/leanprover/lean4/pull/4997)、[#5083](https://github.com/leanprover/lean4/pull/5083)、[#5081](https://github.com/leanprover/lean4/pull/5081)、[#4392](https://github.com/leanprover/lean4/pull/4392)
* `UInt`
  * [#4514](https://github.com/leanprover/lean4/pull/4514) 修复了 `UInt` 引理的命名约定。
* `Std.HashMap` 与 `Std.HashSet`
  * [#4943](https://github.com/leanprover/lean4/pull/4943) 弃用了哈希映射查询方法的若干变体。（见破坏性变更。）
  * [#4917](https://github.com/leanprover/lean4/pull/4917) 让库和 Lean 几乎所有地方都切换到 `Std.HashMap` 和 `Std.HashSet`。
  * [#4954](https://github.com/leanprover/lean4/pull/4954) 弃用了 `Lean.HashMap` 和 `Lean.HashSet`。
  * [#5023](https://github.com/leanprover/lean4/pull/5023) 清理了引理参数。

* `Std.Sat`（供 `bv_decide` 使用）
  * [#4933](https://github.com/leanprover/lean4/pull/4933) 添加了 SAT 与 CNF 的定义。
  * [#4953](https://github.com/leanprover/lean4/pull/4953) 按照 [Davis-Swords 2013](https://arxiv.org/pdf/1304.7861.pdf) 第 3 节定义了 “and-inverter graphs”（AIG）。

* **Parsec**
  * [#4774](https://github.com/leanprover/lean4/pull/4774) 泛化了 `Parsec` 库，使其不仅能解析 `String`，还可解析诸如 `ByteArray` 之类的可迭代数据。（见破坏性变更。）
  * [#5115](https://github.com/leanprover/lean4/pull/5115) 出于自举原因，将 `Lean.Data.Parsec` 移到了 `Std.Internal.Parsec`。

* `Thunk`
  * [#4969](https://github.com/leanprover/lean4/pull/4969) 上游合入了 `Thunk.ext`。

* **IO**
  * [#4973](https://github.com/leanprover/lean4/pull/4973) 修改了 `IO.FS.lines`，使其在所有操作系统上都能处理 `\r\n`，而不只是在 Windows 上。
  * [#5125](https://github.com/leanprover/lean4/pull/5125) 添加了 `createTempFile` 和 `withTempFile`，用于创建只能由当前用户读写的临时文件。

* **其他修复或改进**
  * [#4945](https://github.com/leanprover/lean4/pull/4945) 添加了来自 LeanSAT 的 `Array`、`Bool` 和 `Prod` 工具。
  * [#4960](https://github.com/leanprover/lean4/pull/4960) 添加了 `Relation.TransGen.trans`。
  * [#5012](https://github.com/leanprover/lean4/pull/5012) 使用 `<` 而不是 `Nat.lt` 来表述 `WellFoundedRelation Nat`。
  * [#5011](https://github.com/leanprover/lean4/pull/5011) 在 `Fin.ne_of_val_ne` 中使用 `≠` 替代 `Not (Eq ...)`。
  * [#5197](https://github.com/leanprover/lean4/pull/5197) 上游合入了 `Fin.le_antisymm`。
  * [#5042](https://github.com/leanprover/lean4/pull/5042) 减少了对 `refine'` 的使用。
  * [#5101](https://github.com/leanprover/lean4/pull/5101) 添加了关于 `if-then-else` 与 `Option` 的内容。
  * [#5112](https://github.com/leanprover/lean4/pull/5112) 为 `ULift` 和 `PLift` 添加了基础实例。
  * [#5133](https://github.com/leanprover/lean4/pull/5133) 和 [#5168](https://github.com/leanprover/lean4/pull/5168) 修复了在 Lean 上运行 simpNF linter 时发现的问题。
  * [#5156](https://github.com/leanprover/lean4/pull/5156) 移除了 `omega` 理论中的一个错误 simp 引理。
  * [#5155](https://github.com/leanprover/lean4/pull/5155) 改进了 `Bool` simp 引理的合流性。
  * [#5162](https://github.com/leanprover/lean4/pull/5162) 改进了 `Function.comp` simp 引理的合流性。
  * [#5191](https://github.com/leanprover/lean4/pull/5191) 改进了 `if-then-else` simp 引理的合流性。
  * [#5147](https://github.com/leanprover/lean4/pull/5147) 为 `Quot.rec`、`Nat.strongInductionOn` 和 `Nat.casesStrongInductionOn` 添加了 `@[elab_as_elim]`，并将后两者重命名为 `Nat.strongRecOn` 和 `Nat.casesStrongRecOn`（后者在 [#5179](https://github.com/leanprover/lean4/pull/5179) 中被弃用）。
  * [#5180](https://github.com/leanprover/lean4/pull/5180) 禁用了部分 discrimination tree 键不佳的 simp 引理。
  * [#5189](https://github.com/leanprover/lean4/pull/5189) 清理了泄漏出来的内部 simp 引理。
  * [#5198](https://github.com/leanprover/lean4/pull/5198) 清理了 `allowUnsafeReducibility`。
  * [#5229](https://github.com/leanprover/lean4/pull/5229) 从若干 `simp` 策略中移除了未使用的引理。
  * [#5199](https://github.com/leanprover/lean4/pull/5199) 移除了已弃用超过 6 个月的内容。

````
# Lean 内部实现
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Lean-internals"
%%%

````markdown

* **性能**
  * 一些核心算法已用 C++ 重写以提升性能。
    * [#4910](https://github.com/leanprover/lean4/pull/4910) 和 [#4912](https://github.com/leanprover/lean4/pull/4912) 重新实现了 `instantiateLevelMVars`。
    * [#4915](https://github.com/leanprover/lean4/pull/4915)、[#4922](https://github.com/leanprover/lean4/pull/4922) 和 [#4931](https://github.com/leanprover/lean4/pull/4931) 重新实现了 `instantiateExprMVars`，在某个基准上快了 30%。
  * [#4934](https://github.com/leanprover/lean4/pull/4934) 优化了内核中 `Expr` 相等性测试。
  * [#4990](https://github.com/leanprover/lean4/pull/4990) 修复了内核 `Expr` 相等性测试中的哈希 bug。
  * [#4935](https://github.com/leanprover/lean4/pull/4935) 和 [#4936](https://github.com/leanprover/lean4/pull/4936) 在不需要时跳过部分 `PreDefinition` 变换。
  * [#5225](https://github.com/leanprover/lean4/pull/5225) 在 `ExprDefEq` 的 `CheckAssignmentQuick` 中为已访问表达式添加了缓存。
  * [#5226](https://github.com/leanprover/lean4/pull/5226) 在 `instantiateMVarDeclMVars` 中最大化项共享；`runTactic` 会使用它。
* **诊断与性能分析**
  * [#4923](https://github.com/leanprover/lean4/pull/4923) 为 `Lean.Elab.MutualDef` 中的 `instantiateMVars` 增加了性能分析，因为它可能是瓶颈。
  * [#4924](https://github.com/leanprover/lean4/pull/4924) 添加了大定理诊断，由 `diagnostics.threshold.proofSize` 选项控制。
  * [#4897](https://github.com/leanprover/lean4/pull/4897) 改进了诊断结果的显示。
* **其他修复或改进**
  * [#4921](https://github.com/leanprover/lean4/pull/4921) 清理了 `Expr.betaRev`。
  * [#4940](https://github.com/leanprover/lean4/pull/4940) 通过避免直接写 stdout 修复了测试；在精译和报告分别由不同线程执行的情况下，直接写 stdout 现在并不可靠。
  * [#4955](https://github.com/leanprover/lean4/pull/4955) 记录了 `stderrAsMessages` 现在在命令行上也默认开启。
  * [#4647](https://github.com/leanprover/lean4/pull/4647) 调整了 macOS 上构建的文档。
  * [#4987](https://github.com/leanprover/lean4/pull/4987) 让普通 mvar 赋值在 `instantiateMVars` 中优先于延迟赋值。通常延迟赋值元变量不会被直接赋值，但在出错时 Lean 会给未赋值的元变量赋上 `sorry`。
  * [#4967](https://github.com/leanprover/lean4/pull/4967) 当某个 linter 崩溃时，在错误中加入 linter 名称。
  * [#5043](https://github.com/leanprover/lean4/pull/5043) 清理了命令行快照逻辑。
  * [#5067](https://github.com/leanprover/lean4/pull/5067) 最小化了一些导入。
  * [#5068](https://github.com/leanprover/lean4/pull/5068) 泛化了 `addMatcherInfo` 所用的单子。
  * [f71a1f](https://github.com/leanprover/lean4/commit/f71a1fb4ae958fccb3ad4d48786a8f47ced05c15) 为 [#5126](https://github.com/leanprover/lean4/issues/5126) 添加了缺失的测试。
  * [#5201](https://github.com/leanprover/lean4/pull/5201) 恢复了一个测试。
  * [#3698](https://github.com/leanprover/lean4/pull/3698) 修复了一个 bug：label attribute 之前不会传递 attribute kind。
  * 拼写修复：[#5080](https://github.com/leanprover/lean4/pull/5080)、[#5150](https://github.com/leanprover/lean4/pull/5150)、[#5202](https://github.com/leanprover/lean4/pull/5202)

````
# 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Compiler___-runtime___-and-FFI"
%%%

````markdown

* [#3106](https://github.com/leanprover/lean4/pull/3106) 将前端迁移到新的快照架构。注意 `Frontend.processCommand` 和 `FrontendM` 不再被 Lean 核心使用，但它们会保留。
* [#4919](https://github.com/leanprover/lean4/pull/4919) 为 Windows 上运行时的 `AUTO_THREAD_FINALIZATION` 特性补上了缺失的 include。
* [#4941](https://github.com/leanprover/lean4/pull/4941) 为 Windows 添加了更多 `LEAN_EXPORT`。
* [#4911](https://github.com/leanprover/lean4/pull/4911) 改进了前端 CLI 帮助文本的格式。
* [#4950](https://github.com/leanprover/lean4/pull/4950) 改进了文件读写。
  * `readBinFile` 和 `readFile` 现在只需要两次系统调用（`stat` + `read`），而不再是每 1024 字节执行一次 `read`。
  * `Handle.getLine` 和 `Handle.putStr` 不再会被 NUL 字符绊住。
* [#4971](https://github.com/leanprover/lean4/pull/4971) 在检测栈溢出时处理 SIGBUS 信号。
* [#5062](https://github.com/leanprover/lean4/pull/5062) 避免覆盖现有信号处理器，例如 [rust-lang/rust#69685](https://github.com/rust-lang/rust/pull/69685) 中的做法。
* [#4860](https://github.com/leanprover/lean4/pull/4860) 改进了 Windows 构建的变通方案。它在 Windows 上拆分 `libleanshared` 以规避符号数限制，移除了 `LEAN_EXPORT` denylist 的变通做法，并补上了缺失的 `LEAN_EXPORT`。
* [#4952](https://github.com/leanprover/lean4/pull/4952) 将 panic 输出到 Lean 重定向后的 stderr，确保在语言服务器中，panic 会以常规消息可见，并且在命令行上与其他消息保持正确顺序。
* [#4963](https://github.com/leanprover/lean4/pull/4963) 链接了 LibUV。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Lake"
%%%

````markdown

* [#5030](https://github.com/leanprover/lean4/pull/5030) 移除了死代码。
* [#4770](https://github.com/leanprover/lean4/pull/4770) 为包配置添加了额外字段，Reservoir 将会使用它们。详情见 PR 描述。


````
# DevOps/CI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--DevOps___CI"
%%%

````markdown
* [#4914](https://github.com/leanprover/lean4/pull/4914) 和 [#4937](https://github.com/leanprover/lean4/pull/4937) 改进了发布检查清单。
* [#4925](https://github.com/leanprover/lean4/pull/4925) 忽略了过时的 leanpkg 测试。
* [#5003](https://github.com/leanprover/lean4/pull/5003) 在 CI 中升级了 `actions/cache`。
* [#5010](https://github.com/leanprover/lean4/pull/5010) 在 CI 的缓存 action 中设置了 `save-always`。
* [#5008](https://github.com/leanprover/lean4/pull/5008) 为 speedcenter 添加了更多 libuv 搜索模式。
* [#5009](https://github.com/leanprover/lean4/pull/5009) 将 speedcenter 中“fast”基准的运行次数从 10 次降为 3 次。
* [#5014](https://github.com/leanprover/lean4/pull/5014) 调整了 lakefile 编辑，以在 `pr-release` 工作流中使用新的 `git` 语法。
* [#5025](https://github.com/leanprover/lean4/pull/5025) 让 `pr-release` 工作流向 `curl` 传递 `--retry`。
* [#5022](https://github.com/leanprover/lean4/pull/5022) 默认也为 PR 构建 MacOS Aarch64 发布包。
* [#5045](https://github.com/leanprover/lean4/pull/5045) 在 macOS 文档中的所需软件包标题下加入了 libuv。
* [#5034](https://github.com/leanprover/lean4/pull/5034) 修复了 macOS 上 `libleanshared_1` 的 install name。
* [#5051](https://github.com/leanprover/lean4/pull/5051) 修复了 Windows stage 0。
* [#5052](https://github.com/leanprover/lean4/pull/5052) 修复了 CI 中的 32 位 stage 0 构建。
* [#5057](https://github.com/leanprover/lean4/pull/5057) 避免在每次构建中都重新构建 `leanmanifest`。
* [#5099](https://github.com/leanprover/lean4/pull/5099) 让 `restart-on-label` 工作流也按 commit SHA 过滤。
* [#4325](https://github.com/leanprover/lean4/pull/4325) 添加了 CaDiCaL。

````
# 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___12___0-_LPAR_2024-10-01_RPAR_--Breaking-changes"
%%%

````markdown

* 现在构建 Lean 需要 [LibUV](https://libuv.org/)。此变更只影响自行编译 Lean、而不是通过 `elan` 获取工具链的开发者。我们已经更新了官方构建说明，加入了如何在受支持平台上获取 LibUV 的信息。([#4963](https://github.com/leanprover/lean4/pull/4963))

* 以 `simp_wf` 开头的 `decreasing_by` 子句中的递归定义可能会失效。请尝试移除 `simp_wf`，或将其替换为 `simp`。([#5016](https://github.com/leanprover/lean4/pull/5016))

* 当 `f` 是由模式匹配定义的非递归函数时，`rw [f]` 的行为发生了变化。

  例如，过去 `rw [Option.map]` 会把 `Option.map f o` 重写为 `match o with … `。现在这种重写会失败，因为它将使用等式引理，而这些引理和 `List.map` 一样需要构造子。

  补救办法：
  * 在重写之前先对 `o` 做分类讨论。
  * 使用 `rw [Option.map.eq_def]`，它会重写 `Option.map` 的任意（饱和）应用。
  * 在*定义*相关函数时，使用 `set_option backward.eqns.nonrecursive false`。
  ([#4154](https://github.com/leanprover/lean4/pull/4154))

* 对递归函数和非递归函数的等式引理的统一处理可能会破坏现有代码，因为现在可能会有额外的等式引理：

  * 如果编号发生变化，对 `f.eq_2` 的显式使用可能需要调整。

  * 过去会匹配（并引入 `match` 语句）的 `rw [f]` 或 `simp [f]` 现在可能不再适用，因为等式引理变得更细粒度了。

    这种情况下，可以在重写前先对参数做分类讨论，或者在*定义*函数时设置选项 `backward.eqns.deepRecursiveSplit false`。

  ([#5129](https://github.com/leanprover/lean4/pull/5129)、[#5207](https://github.com/leanprover/lean4/pull/5207))

* `reduceCtorEq` simproc 现在是可选的，因此它可能需要被显式放入 simp 引理列表中，例如 `simp only [reduceCtorEq]`。这个 simproc 负责规约构造子的相等式。([#5167](https://github.com/leanprover/lean4/pull/5167))

* `Nat.strongInductionOn` 现在改名为 `Nat.strongRecOn`，`Nat.caseStrongInductionOn` 改名为 `Nat.caseStrongRecOn`。([#5147](https://github.com/leanprover/lean4/pull/5147))

* `Membership.mem` 的参数顺序已交换，这会影响所有 `Membership` 实例。([#5020](https://github.com/leanprover/lean4/pull/5020))

* `List.getElem_drop` 和 `List.getElem_drop'` 的含义已被对调，并且前者现在是 simp 引理。([#5210](https://github.com/leanprover/lean4/pull/5210))

* `Parsec` 库已从 `Lean.Data.Parsec` 移到 `Std.Internal.Parsec`。`Parsec` 类型现在更加泛化，多了一个可迭代对象参数。解析字符串的用户可以迁移到 `Std.Internal.Parsec.String` 命名空间中的 `Parser`，其中还包括面向字符串的解析组合子。([#4774](https://github.com/leanprover/lean4/pull/4774))

* `Lean` 模块已从 `Lean.HashMap` 和 `Lean.HashSet` 切换到 `Std.HashMap` 和 `Std.HashSet` ([#4943](https://github.com/leanprover/lean4/pull/4943))。`Lean.HashMap` 和 `Lean.HashSet` 现已弃用 ([#4954](https://github.com/leanprover/lean4/pull/4954))，并将在未来版本中移除。对使用哈希映射的 `Lean` API（例如 `Lean.Environment.const2ModIdx`）的用户来说，从 `Lean.HashMap` 迁移到 `Std.HashMap` 可能会遇到如下轻微破坏：
  * 查询函数使用术语 `get` 而不是 `find`，([#4943](https://github.com/leanprover/lean4/pull/4943))
  * 记法 `map[key]` 不再返回可选值，而是要求提供键确实存在于映射中的证明。之前的行为可通过记法 `map[key]?` 获得。

````
