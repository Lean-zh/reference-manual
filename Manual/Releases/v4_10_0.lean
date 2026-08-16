/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.10.0 (2024-07-31)" =>
%%%
tag := "release-v4.10.0"
file := "v4.10.0"
%%%

````markdown
### 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

* `split` 策略：
  * [#4401](https://github.com/leanprover/lean4/pull/4401) 改进了 `split` 在泛化 match 判别式时采用的策略，并新增 `trace.split.failure` 跟踪类以便诊断问题。

* `rw` 策略：
  * [#4385](https://github.com/leanprover/lean4/pull/4385) 防止该策略把已有目标误称为新子目标。
  * [dac1da](https://github.com/leanprover/lean4/commit/dac1dacc5b39911827af68247d575569d9c399b5) 添加了用于排列新目标顺序的配置，类似于 `apply`。

* `simp` 策略：
  * [#4430](https://github.com/leanprover/lean4/pull/4430) 为 `if` 表达式（`ite` 与 `dite`）新增 `dsimproc`。
  * [#4434](https://github.com/leanprover/lean4/pull/4434) 改进了展开启发式。方程引理现在带有优先级；在可能的兜底规则之前，会优先尝试更具体的方程引理。
  * [#4481](https://github.com/leanprover/lean4/pull/4481) 修复了函数值的 `OfNat` 数值字面量会被去规范化的问题。
  * [#4467](https://github.com/leanprover/lean4/pull/4467) 修复了 dsimp 定理可能无法应用于字面量的问题。
  * [#4484](https://github.com/leanprover/lean4/pull/4484) 修复了已弃用 simp 参数警告的源码位置。
  * [#4258](https://github.com/leanprover/lean4/pull/4258) 为 `dsimp` 配置新增文档字符串。
  * [#4567](https://github.com/leanprover/lean4/pull/4567) 提高了 `simp?` 报告已使用 simp 引理时的准确性。
  * [fb9727](https://github.com/leanprover/lean4/commit/fb97275dcbb683efe6da87ed10a3f0cd064b88fd) 添加了（但尚未实现）simp 配置选项 `implicitDefEqProofs`，该选项将允许在证明项中包含 `rfl` 定理。
* `omega` 策略：
  * [#4360](https://github.com/leanprover/lean4/pull/4360) 让该策略惰性生成错误消息，从而提升其在策略组合子中使用时的性能。
* `bv_omega` 策略：
  * [#4579](https://github.com/leanprover/lean4/pull/4579) 为本次发布中 `Fin.sub` 定义的变更提供了兼容处理。
* [#4490](https://github.com/leanprover/lean4/pull/4490) 为生成文档中的策略索引奠定了基础，类似 Lean 3 中已有的机制。详情见 PR 说明。

* **命令**
  * [#4370](https://github.com/leanprover/lean4/pull/4370) 让 `variable` 命令在校验期间完全精译 binder，修复了某些错误只会在下一条声明处才报告的问题。
  * [#4408](https://github.com/leanprover/lean4/pull/4408) 修复了 `theorem` 与 `def` 声明在宇宙参数顺序上的不一致。
  * [#4493](https://github.com/leanprover/lean4/pull/4493) 和
    [#4482](https://github.com/leanprover/lean4/pull/4482) 修复了 `theorem`、`def` 与 `example` 精译器之间的不一致，
    使得取值于 `Prop` 的 `example` 以及其他定义命令能像 `theorem` 一样精译。
  * [8f023b](https://github.com/leanprover/lean4/commit/8f023b85c554186ae562774b8122322d856c674e)、[3c4d6b](https://github.com/leanprover/lean4/commit/3c4d6ba8648eb04d90371eb3fdbd114d16949501) 和 [0783d0](https://github.com/leanprover/lean4/commit/0783d0fcbe31b626fbd3ed2f29d838e717f09101) 修改了 `#reduce` 命令，使其能够控制要化简的内容。
    例如，`#reduce (proofs := true) (types := false) e` 会在表达式 `e` 中同时化简证明和类型。
    默认情况下，证明和类型都不会被化简。
  * [#4489](https://github.com/leanprover/lean4/pull/4489) 修复了 `#check_tactic` 中的一个精译错误。
  * [#4505](https://github.com/leanprover/lean4/pull/4505) 新增对 `open _root_.<namespace>` 的支持。

* **选项**
  * [#4576](https://github.com/leanprover/lean4/pull/4576) 新增 `debug.byAsSorry` 选项。设置 `set_option debug.byAsSorry true` 会让所有 `by ...` 项都按 `sorry` 精译。
  * [7b56eb](https://github.com/leanprover/lean4/commit/7b56eb20a03250472f4b145118ae885274d1f8f7) 和 [d8e719](https://github.com/leanprover/lean4/commit/d8e719f9ab7d049e423473dfc7a32867d32c856f) 新增 `debug.skipKernelTC` 选项。设置 `set_option debug.skipKernelTC true` 会关闭内核类型检查。该选项旨在临时绕过内核性能问题，但会损害可靠性，因为若有错误策略生成了无效证明，在此选项为 true 时将不会被捕获。

* [#4301](https://github.com/leanprover/lean4/pull/4301)
  添加了一个 linter，用于标记局部变量名恰好是其类型的无参构造子之一的情况。当用户没有打开命名空间，或没有添加点号/前导限定符时，就可能出现这种情况，如下所示：

  ```lean
  inductive Tree (α : Type) where
    | leaf
    | branch (left : Tree α) (val : α) (right : Tree α)

  def depth : Tree α → Nat
    | leaf => 0
  ```

  有了这个 linter，`leaf` 模式会被标记为一个局部变量，因为它的名字与构造子 `Tree.leaf` 重叠。

  可以用 `set_option linter.constructorNameAsVariable false` 关闭这个 linter。

  此外，当模式中一个带参数的名字无效时，错误消息现在还会提示相近且有效的名字。这意味着下面这个定义：

  ```lean
  def length (list : List α) : Nat :=
    match list with
    | nil => 0
    | cons x xs => length xs + 1
  ```

  现在会产生如下警告：

  ```
  warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
  note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
  ```

  以及错误：

  ```
  invalid pattern, constructor or constant marked with '[match_pattern]' expected

  Suggestion: 'List.cons' is similar
  ```

* **元编程**
  * [#4454](https://github.com/leanprover/lean4/pull/4454) 添加了公开的 `Name.isInternalDetail` 函数，用于按照内部名称的命名约定过滤声明。

* **其他修复或改进**
  * [#4416](https://github.com/leanprover/lean4/pull/4416) 对 `#print axioms` 的输出排序，以确保结果确定。
  * [#4528](https://github.com/leanprover/lean4/pull/4528) 修复了 cdot 聚焦策略的错误消息范围。

### 语言服务器、小部件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

* [#4443](https://github.com/leanprover/lean4/pull/4443) 让 watchdog 在面对行为不良的客户端时更加稳健。

### 漂亮打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Pretty-printing"
%%%

* [#4433](https://github.com/leanprover/lean4/pull/4433) 在上下文不可用时恢复了后备漂亮打印器，并为 `addMessageContext` 添加了文档。
* [#4556](https://github.com/leanprover/lean4/pull/4556) 引入 `pp.maxSteps` 选项，并将 `pp.deepTerms` 的默认值设为 `false`。两者共同避免了过大或过深的项压垮 Infoview。

### 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Library"
%%%
* [#4560](https://github.com/leanprover/lean4/pull/4560) 将 `GetElem` 类拆分为 `GetElem` 与 `GetElem?`。
  这使得可以从 `GetElem.getElem?` 与 `GetElem.getElem!` 中移除 `Decidable` 实例参数，从而提升它们的可重写性。
  更多信息请参见这些类的文档字符串。
* `Array`
  * [#4389](https://github.com/leanprover/lean4/pull/4389) 将 `Array.toArrayAux_eq` 设为 `simp` 引理。
  * [#4399](https://github.com/leanprover/lean4/pull/4399) 提高了 `Array.reverse_data` 证明的稳健性。
* `List`
  * [#4469](https://github.com/leanprover/lean4/pull/4469) 和 [#4475](https://github.com/leanprover/lean4/pull/4475) 改进了 `List` API 的组织结构。
  * [#4470](https://github.com/leanprover/lean4/pull/4470) 改进了 `List.set` 与 `List.concat` 的 API。
  * [#4472](https://github.com/leanprover/lean4/pull/4472) 将来自 Batteries 的 `List.filter` 相关引理上游化。
  * [#4473](https://github.com/leanprover/lean4/pull/4473) 调整了 `@[simp]` 属性。
  * [#4488](https://github.com/leanprover/lean4/pull/4488) 将 `List.getElem?_eq_getElem` 设为 simp 引理。
  * [#4487](https://github.com/leanprover/lean4/pull/4487) 补充了缺失的 `List.replicate` API。
  * [#4521](https://github.com/leanprover/lean4/pull/4521) 新增 `List.map` 相关引理。
  * [#4500](https://github.com/leanprover/lean4/pull/4500) 将 `List.length_cons` 从使用 `as.length.succ` 改为使用 `as.length + 1`。
  * [#4524](https://github.com/leanprover/lean4/pull/4524) 修复了 `List.filter_congr` 的陈述。
  * [#4525](https://github.com/leanprover/lean4/pull/4525) 修改了 `List.bind_map` 中 binder 的显式性。
  * [#4550](https://github.com/leanprover/lean4/pull/4550) 新增 `maximum?_eq_some_iff'` 与 `minimum?_eq_some_iff?`。
* [#4400](https://github.com/leanprover/lean4/pull/4400) 将 `List` 与 `Array` 的索引规范形切换为 `xs[n]` 与 `xs[n]?`。
* `HashMap`
  * [#4372](https://github.com/leanprover/lean4/pull/4372) 修复了 `HashMap.insert` 与 `HashMap.erase` 中的线性性问题，使重替换负载下的速度提升了 40%。
* `Option`
  * [#4403](https://github.com/leanprover/lean4/pull/4403) 将 `Option.forM` 的类型从 `Unit` 泛化为 `PUnit`。
  * [#4504](https://github.com/leanprover/lean4/pull/4504) 移除了 `Option.elim` 的 simp 属性，转而将 simp 属性加到各个化简引理上，从而让展开不那么激进。
* `Nat`
  * [#4242](https://github.com/leanprover/lean4/pull/4242) 为 `n + 1` 与 `n - 1` 规范形补充了缺失定理。
  * [#4486](https://github.com/leanprover/lean4/pull/4486) 将 `Nat.min_assoc` 设为 simp 引理。
  * [#4522](https://github.com/leanprover/lean4/pull/4522) 将 `@[simp]` 从 `Nat.pred_le` 移到 `Nat.sub_one_le`。
  * [#4532](https://github.com/leanprover/lean4/pull/4532) 将多处 `Nat.succ n` 改为 `n + 1`。
* `Int`
  * [#3850](https://github.com/leanprover/lean4/pull/3850) 为 `Int` 添加了完整的 div/mod simproc。
* `String`/`Char`
  * [#4357](https://github.com/leanprover/lean4/pull/4357) 将字节大小接口改为返回 `Nat`，并提供函数 `Char.utf8Size` 与 `String.utf8ByteSize`。
  * [#4438](https://github.com/leanprover/lean4/pull/4438) 将来自 Batteries 的 `Char.ext` 上游化，并为手册补充了一些 `Char` 文档。
* `Fin`
  * [#4421](https://github.com/leanprover/lean4/pull/4421) 调整了 `Fin.sub`，使其在定义相等检查中性能更好。
* `Prod`
  * [#4526](https://github.com/leanprover/lean4/pull/4526) 补充了缺失的 `Prod.map` 引理。
  * [#4533](https://github.com/leanprover/lean4/pull/4533) 修复了引理中 binder 的显式性。
* `BitVec`
  * [#4428](https://github.com/leanprover/lean4/pull/4428) 为 `BitVec` 相等性补充了缺失的 `simproc`。
  * [#4417](https://github.com/leanprover/lean4/pull/4417) 新增 `BitVec.twoPow` 及相关引理，以推进 LeanSAT 的乘法 bitblasting。
* `Std` 库
  * [#4499](https://github.com/leanprover/lean4/pull/4499) 引入了 `Std`：一个位于 `Init` 与 `Lean` 之间的库，为 Lean 的实现和外部用户同时提供 prelude 中没有的功能。
* **其他修复或改进**
  * [#3056](https://github.com/leanprover/lean4/pull/3056) 统一改用 `(· == a)`，而不再使用 `(a == ·)`。
  * [#4502](https://github.com/leanprover/lean4/pull/4502) 修复了使用 Batteries linter 检查库时报告的错误。

### Lean 内部机制
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Lean-internals"
%%%

* [#4391](https://github.com/leanprover/lean4/pull/4391) 让 `getBitVecValue?` 能识别 `BitVec.ofNatLt`。
* [#4410](https://github.com/leanprover/lean4/pull/4410) 调整了 `instantiateMVars` 算法，使其在对已实例化的元变量做 beta 化简时，也会对 `let` 表达式做 zeta 化简。
* [#4420](https://github.com/leanprover/lean4/pull/4420) 修复了元变量赋值的 occurs check，使其也会考虑元变量的类型。
* [#4425](https://github.com/leanprover/lean4/pull/4425) 修复了 `forEachModuleInDir`，使其对每个 Lean 文件恰好迭代一次。
* [#3886](https://github.com/leanprover/lean4/pull/3886) 添加了使用 Lake 构建 Lean 核心 olean 的支持。
* **Defeq 与 WHNF 算法**
  * [#4387](https://github.com/leanprover/lean4/pull/4387) 改进了 `isDefEq` 的性能：在元变量赋值期间会对 lambda 抽象项做 eta 化简，因为这些项在元变量实例化时本来也会做 beta 化简。
  * [#4388](https://github.com/leanprover/lean4/pull/4388) 移除了 `isDefEqQuickOther` 中的冗余代码。
* **类型类推断**
  * [#4530](https://github.com/leanprover/lean4/pull/4530) 修复了 `synthInstance?` 在缓存结果时对元变量的处理。
* **精译**
  * [#4426](https://github.com/leanprover/lean4/pull/4426) 让 “don't know how to synthesize implicit argument” 错误报告参数名这一特性更加可靠。
  * [#4497](https://github.com/leanprover/lean4/pull/4497) 修复了广义字段记法（点记法）的名称解析错误。
  * [#4536](https://github.com/leanprover/lean4/pull/4536) 禁止在 `(e :)` 记法中触发隐式 lambda 特性。
  * [#4562](https://github.com/leanprover/lean4/pull/4562) 现在在 `where`/`let rec` 块中若存在两个同名函数会报错。
* 递归原理
  * [#4549](https://github.com/leanprover/lean4/pull/4549) 重构了 `findRecArg`，提取出 `withRecArgInfo`。
    错误现在按参数顺序而非尝试顺序报告（会先尝试非索引参数）。
    对于每个参数，系统都会说明它为何未被尝试，即便理由很明显（例如属于固定前缀或类型为 `Prop` 等）。
* 将核心 C++ 移植到 Lean
  * [#4474](https://github.com/leanprover/lean4/pull/4474) 朝着未来移植到 Lean 的方向，对 `constructions` 做了进一步重构。
  * [#4498](https://github.com/leanprover/lean4/pull/4498) 将 `mk_definition_inferring_unsafe` 移植到了 Lean。
  * [#4516](https://github.com/leanprover/lean4/pull/4516) 将 `recOn` 构造移植到了 Lean。
  * [#4517](https://github.com/leanprover/lean4/pull/4517)、[#4653](https://github.com/leanprover/lean4/pull/4653) 和 [#4651](https://github.com/leanprover/lean4/pull/4651) 将 `below` 与 `brecOn` 构造移植到了 Lean。
* 文档
  * [#4501](https://github.com/leanprover/lean4/pull/4501) 为 `PersistentEnvExtension` 添加了更详细的文档字符串。
* **其他修复或改进**
  * [#4382](https://github.com/leanprover/lean4/pull/4382) 从 `NameMap.find?` 上移除了 `@[inline]` 属性，该属性会导致每个调用点都重新特化。
  * [5f9ded](https://github.com/leanprover/lean4/commit/5f9dedfe5ee9972acdebd669f228f487844a6156) 改进了 `trace.Elab.snapshotTree` 的输出。
  * [#4424](https://github.com/leanprover/lean4/pull/4424) 移除了 “you might need to open '{dir}' in your editor” 消息；这一提示现在由 Lake 与 VS Code 扩展处理。
  * [#4451](https://github.com/leanprover/lean4/pull/4451) 提升了 `CollectMVars` 与 `FindMVar` 的性能。
  * [#4479](https://github.com/leanprover/lean4/pull/4479) 为 `BitVec` 和 `Fin` simproc 使用的中间结构补充了缺失的 `DecidableEq` 与 `Repr` 实例。
  * [#4492](https://github.com/leanprover/lean4/pull/4492) 为先前的一个 `isDefEq` 问题补充了测试。
  * [9096d6](https://github.com/leanprover/lean4/commit/9096d6fc7180fe533c504f662bcb61550e4a2492) 移除了 `PersistentHashMap.size`。
  * [#4508](https://github.com/leanprover/lean4/pull/4508) 修复了 `@[implemented_by]` 在良基递归定义函数上的行为。
  * [#4509](https://github.com/leanprover/lean4/pull/4509) 为 `apply?` 策略补充了额外测试。
  * [d6eab3](https://github.com/leanprover/lean4/commit/d6eab393f4df9d473b5736d636b178eb26d197e6) 修复了一个基准测试。
  * [#4563](https://github.com/leanprover/lean4/pull/4563) 为 `IndPredBelow.mkBelowMatcher` 中的一个错误添加了变通方案。
* **清理：** [#4380](https://github.com/leanprover/lean4/pull/4380), [#4431](https://github.com/leanprover/lean4/pull/4431), [#4494](https://github.com/leanprover/lean4/pull/4494), [e8f768](https://github.com/leanprover/lean4/commit/e8f768f9fd8cefc758533bc76e3a12b398ed4a39), [de2690](https://github.com/leanprover/lean4/commit/de269060d17a581ed87f40378dbec74032633b27), [d3a756](https://github.com/leanprover/lean4/commit/d3a7569c97123d022828106468d54e9224ed8207), [#4404](https://github.com/leanprover/lean4/pull/4404), [#4537](https://github.com/leanprover/lean4/pull/4537).

### 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Compiler___-runtime___-and-FFI"
%%%

* [d85d3d](https://github.com/leanprover/lean4/commit/d85d3d5f3a09ff95b2ee47c6f89ef50b7e339126) 修复了所有权计算中尾调用判定准则的问题。
* [#3963](https://github.com/leanprover/lean4/pull/3963) 在运行时的 C++ 到 Lean 边界上新增 UTF-8 校验。
* [#4512](https://github.com/leanprover/lean4/pull/4512) 修复了解释器在加载已初始化值时缺失 unboxing 的问题。
* [#4477](https://github.com/leanprover/lean4/pull/4477) 暴露了内置 C 编译器（clang）的编译器标志。

### Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Lake"
%%%

* [#4384](https://github.com/leanprover/lean4/pull/4384) 弃用了 `inputFile`，并以 `inputBinFile` 和 `inputTextFile` 取代。不同于 `inputBinFile`（以及 `inputFile`），`inputTextFile` 会规范化行尾，从而有助于保证文本文件跟踪与平台无关。
* [#4371](https://github.com/leanprover/lean4/pull/4371) 简化了依赖解析代码。
* [#4439](https://github.com/leanprover/lean4/pull/4439) 调整了 Lake 配置 DSL，并做了其他改进：
  现在可以用字符串字面量而不是标识符来表示名称，
  避免在 `lake new` 和 `lake init` 模板中使用法式引号，
  将 `exe` 模板的主模块改为 `Main`，
  改进了 `lean-toolchain` 下载失败时 `math` 模板的错误消息，
  并将未知配置字段从错误降级为警告，以提升跨版本兼容性。
* [#4496](https://github.com/leanprover/lean4/pull/4496) 微调了 `require` 语法并更新了文档。现在在 TOML 中，像 `doc-gen4` 这样的包名在 `require` 里不再需要法式引号。
* [#4485](https://github.com/leanprover/lean4/pull/4485) 修复了间接依赖中的包版本会优先于直接依赖的问题。
* [#4478](https://github.com/leanprover/lean4/pull/4478) 修复了 Lake 会在平台无关的跟踪中错误包含模块动态库的问题。
* [#4529](https://github.com/leanprover/lean4/pull/4529) 修复了一些 bad import 错误相关问题。
  可执行文件中的 bad import 不再阻止其根模块被构建。
  这也修复了传递性 bad import 的位置不会显示的问题。
  该可执行文件的根模块现在会遵循 `nativeFacets`。
* [#4564](https://github.com/leanprover/lean4/pull/4564) 修复了非标识符脚本名若不加法式引号便无法在 CLI 中输入的问题。
* [#4566](https://github.com/leanprover/lean4/pull/4566) 处理了若干预编译库相关问题。
  * 修复了 Lake 总是会预编译某个模块所属包的问题。
  * 如果一个模块被预编译，它现在也会预编译其导入；之前只有在这些导入被直接导入时才会如此。
* [#4495](https://github.com/leanprover/lean4/pull/4495), [#4692](https://github.com/leanprover/lean4/pull/4692), [#4849](https://github.com/leanprover/lean4/pull/4849)
  新增了一种 `require`：它会先从注册表 API 端点（例如 Reservoir）获取包元数据，
  再根据提供的信息克隆对应的 Git 包。要声明此类依赖，新语法是：

  ```lean
  require <scope> / <pkg-name> [@ git <rev>]
  -- Examples:
  require "leanprover" / "doc-gen4"
  require "leanprover-community" / "proofwidgets" @ git "v0.0.39"
  ```

  或者在 TOML 中：
  ```toml
  [[require]]
  name = "<pkg-name>"
  scope = "<scope>"
  rev = "<rev>"
  ```

  与 Git 依赖不同，Lake 可以利用注册表提供的更丰富信息来确定包的默认分支。
  这意味着，对于像 `doc-gen4` 这样默认分支不是 `master` 的包仓库，
  Lake 现在会使用它们的默认分支（例如 `doc-gen4` 的默认分支是 `main`）。

  Lake 还支持通过环境变量 `RESERVIOR_API_URL` 配置注册表端点。
  因此，任何提供与 Reservoir 类似接口的服务器都可以作为注册表使用。
  未来还会加入更多配置选项，与 Cargo 的[替代注册表](https://doc.rust-lang.org/cargo/reference/registries.html)
  和[源替换](https://doc.rust-lang.org/cargo/reference/source-replacement.html)
  相对应。

### DevOps/CI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--DevOps___CI"
%%%
* [#4427](https://github.com/leanprover/lean4/pull/4427) 为 `leanprover/lean4` 的 CI 使用 Namespace runners。
* [#4440](https://github.com/leanprover/lean4/pull/4440) 修复了 CI 中的 speedcenter 测试。
* [#4441](https://github.com/leanprover/lean4/pull/4441) 修复了工作流变更会破坏未 rebase PR 的 CI 的问题。
* [#4442](https://github.com/leanprover/lean4/pull/4442) 修复了 Wasm release-ci。
* [6d265b](https://github.com/leanprover/lean4/commit/6d265b42b117eef78089f479790587a399da7690) 修复了 `github.event.pull_request.merge_commit_sha` 有时不可用的问题。
* [16cad2](https://github.com/leanprover/lean4/commit/16cad2b45c6a77efe4dce850dcdbaafaa7c91fc3) 为 CI 添加优化，不再抓取完整历史。
* [#4544](https://github.com/leanprover/lean4/pull/4544) 让发布在 GitHub 上被标记为预发布。
* [#4446](https://github.com/leanprover/lean4/pull/4446) 将 Lake 切换为使用 `src/lake/lakefile.toml`，以避免为了构建 Lake 而先加载某个版本的 Lake。
* Nix
  * [5eb5fa](https://github.com/leanprover/lean4/commit/5eb5fa49cf9862e99a5bccff8d4ca1a062f81900) 修复了 Nix 下的 `update-stage0-commit`。
  * [#4476](https://github.com/leanprover/lean4/pull/4476) 在 Nix shell 中加入了 gdb。
  * [e665a0](https://github.com/leanprover/lean4/commit/e665a0d716dc42ba79b339b95e01eb99fe932cb3) 修复了 Nix 下的 `update-stage0`。
  * [4808eb](https://github.com/leanprover/lean4/commit/4808eb7c4bfb98f212b865f06a97d46c44978a61) 修复了 Nix 下的 `cacheRoots`。
  * [#3811](https://github.com/leanprover/lean4/pull/3811) 为 lib target 添加了平台相关标志。
  * [#4587](https://github.com/leanprover/lean4/pull/4587) 在 darwin 上把 `-lStd` 的链接重新加入 nix 构建标志。

### 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___10___0-_LPAR_2024-07-31_RPAR_--Breaking-changes"
%%%

* `Char.csize` 已被 `Char.utf8Size` 取代（[#4357](https://github.com/leanprover/lean4/pull/4357)）。
* 库引理现在统一写作 `(· == a)`，而不是 `(a == ·)`（[#3056](https://github.com/leanprover/lean4/pull/3056)）。
* `List` 与 `Array` 的索引规范形现在是 `xs[n]` 和 `xs[n]?`，而不再使用 `List.get` 之类的函数（[#4400](https://github.com/leanprover/lean4/pull/4400)）。
* 通过一系列合一创建出的项有时会比以前做更多 eta 化简，因此证明可能需要调整（[#4387](https://github.com/leanprover/lean4/pull/4387)）。
* `GetElem` 类已拆分为两个；更多信息请参见 `GetElem` 与 `GetElem?` 的文档字符串（[#4560](https://github.com/leanprover/lean4/pull/4560)）。

````
