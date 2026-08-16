/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.21.0 (2025-06-30)" =>
%%%
tag := "release-v4.21.0"
file := "v4.21.0"
%%%

````markdown
本次发布共合入 295 项变更。除下文列出的 100 项功能新增和 83 项修复外，还有 2 项重构、4 项文档改进、6 项性能改进、2 项测试套件改进以及 98 项其他变更。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Highlights"
%%%

````markdown

_`'Unknown identifier'` 代码操作_

* [#7665](https://github.com/leanprover/lean4/pull/7665) 和 [#8180](https://github.com/leanprover/lean4/pull/8180) 增加了
  用于处理 `'Unknown identifier'` 错误的代码操作支持：既可以导入缺失的声明，也可以
  将该标识符改为环境中已有的某个标识符。

_新的语言特性_

* [#8449](https://github.com/leanprover/lean4/pull/8449) 和 [#8516](https://github.com/leanprover/lean4/pull/8516)
  将 Mathlib 的 `clear_value` 策略上游化并加以扩展。给定一个
  局部定义 `x : T := v`，`clear_value x` 策略会将其替换为
  一个假设 `x : T`；如果目标不依赖值 `v`，则会报错。
  语法 `clear_value (h : x = _)` 会在清除 `x` 的值之前先创建
  假设 `h : x = _`。任何与 `x` 定义相等的表达式
  都可以替代下划线。
  此外，`clear_value *` 会清除所有可清除的值；如果一个都无法清除，
  则会报错。

* [#8512](https://github.com/leanprover/lean4/pull/8512) 新增了 `value_of% ident` 项，它会展开为
  局部或全局常量 `ident` 的值。这对于创建
  定义性假设很有用：
  ```lean
  let x := ... complicated expression ...
  have hx : x = value_of% x := rfl
  ```

* [#8450](https://github.com/leanprover/lean4/pull/8450) 为 `subst` 策略增加了一项功能：当 `x : X := v`
  是局部定义时，`subst x` 会在目标中用 `v` 替换 `x`，并
  移除 `x`。此前该策略会报错。

* [#8037](https://github.com/leanprover/lean4/pull/8037) 引入了一种规模低于二次的 `noConfusionType`
  构造，并且约简速度更快。此前带有两个嵌套 `match`
  语句的 `noConfusion` 构造在规模和约简行为上都是二次的。
  借助一些辅助定义，可以实现线性规模的构造。

* [#8104](https://github.com/leanprover/lean4/pull/8104) 让 `fun_induction` 和 `fun_cases`（尝试）
  在目标中展开相关的函数应用。旧行为可以通过
  `set_option tactic.fun_induction.unfolding false` 启用。对于
  `fun_cases`，当函数的结果类型依赖于某个参数时，这一行为暂时还不起作用；
  参见问题 [#8296](https://github.com/leanprover/lean4/issues/8296)。

* [#8171](https://github.com/leanprover/lean4/pull/8171) 会在函数归纳/分类原则中省略那些以
  `by contradiction`（更一般地说，`False.elim`、
  `absurd` 或 `noConfusion`）实现的分支。从这个意义上说，这是一个
  **破坏性变更**：使用函数归纳后需要证明的目标会更少。

* [#8106](https://github.com/leanprover/lean4/pull/8106) 新增 `register_linter_set` 命令，用于声明检查器集合。
  `getLinterValue` 函数现在会检查当前检查器是否
  属于某个已启用的集合（通过 `set_option` 命令
  或命令行启用）。

* [#8267](https://github.com/leanprover/lean4/pull/8267) 让 `#guard_msgs` 将 `trace` 消息与
  `info`、`warning` 和 `error` 分开处理。它还引入了
  `#guard_msgs (pass info)` 的写法，类似此前的 `(drop info)`，
  并补充了 `(check info)` 作为 `(info)` 的显式形式。

_库亮点_

* [#8358](https://github.com/leanprover/lean4/pull/8358) 引入了新版迭代器库的一个极简版本。
  它包含列表迭代器以及多种消费者，即 `toArray`、
  `toList`、`toListRev`、`ForIn`、`fold`、`foldM` 和 `drain`。所有
  消费者还都提供了一个无需任何证明即可使用的 `partial` 变体。
  即便使用旧代码生成器，这个受限版本的迭代器库也能生成相当不错的代码。

* [#7352](https://github.com/leanprover/lean4/pull/7352) 重做了围绕 `Id` 单子的 `simp` 集，
  使其不会省略或展开 `pure` 与 `Id.run`。

* [#8313](https://github.com/leanprover/lean4/pull/8313) 修改了 `Vector` 的定义，使其不再扩展
  `Array`。这可以防止 `Array` API“泄漏”进来。

_其他亮点_

* `dsimp` 的性能优化：

  - [#6973](https://github.com/leanprover/lean4/pull/6973) 让 `dsimp` 不再访问证明项，这应当能使
    `simp` 和 `dsimp` 更高效。

  - [#7428](https://github.com/leanprover/lean4/pull/7428) 为 `simp` 增加了 `dsimp` 缓存。此前 `simp`
    发起的每次 `dsimp` 调用都会从一个全新的缓存开始。因此，在编译
    Mathlib 时，`simp` 所花的时间减少了 45% 以上，Mathlib 整体编译速度
    提升了 8%。

* [#8221](https://github.com/leanprover/lean4/pull/8221) 调整了实验性模块系统：默认不导出
  `def` 的函数体，除非通过 `def` 上的新属性 `@[expose]`
  或外围 `section` 显式退出这一行为。

* [#8559](https://github.com/leanprover/lean4/pull/8559) 和 [#8560](https://github.com/leanprover/lean4/pull/8560) 修复了
  [#8554](https://github.com/leanprover/lean4/pull/8554) 中描述的一种对抗性健全性攻击。该攻击利用了
  `assert!` 不再中止执行，以及用户
  可以重定向错误消息这两个事实。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Language"
%%%

````markdown

* [#6973](https://github.com/leanprover/lean4/pull/6973) 让 `dsimp` 不再访问证明项，这应当能使
  `simp` 和 `dsimp` 更高效。

* [#7428](https://github.com/leanprover/lean4/pull/7428) 为 `simp` 增加了 `dsimp` 缓存。此前 `simp` 发起的每次 `dsimp` 调用都从一个全新的缓存开始。因此，在编译 Mathlib 时，`simp` 所花的时间减少了 45% 以上，Mathlib 整体编译速度提升了 8%。

* [#7631](https://github.com/leanprover/lean4/pull/7631) 修复了 `Lean.Level.mkIMaxAux`（内核中的 `mk_imax`），使得
  `imax 1 u` 会约简为 `u`。

* [#7977](https://github.com/leanprover/lean4/pull/7977) 为 `grind` 增加了对 eta-约简的基础支持。

* [#8002](https://github.com/leanprover/lean4/pull/8002) 修复了一个问题：对被 `induction` 和 `cases`
  策略泛化出来的变量执行“跳转到定义”时无法正常工作。关闭了
  #2873。

* [#8024](https://github.com/leanprover/lean4/pull/8024) 为 `lean` 命令行添加了 `--setup` 选项。它接受一个
  JSON 文件路径，其中包含模块的导入列表和
  配置信息，并以此覆盖模块自身文件头中的对应信息。Lake 将使用它来
  指定模块产物（例如 `olean` 和 `ilean` 文件）的路径，
  并将其与 `LEAN_PATH` 方案分离。

* [#8037](https://github.com/leanprover/lean4/pull/8037) 引入了一种规模低于二次的 `noConfusionType`
  构造，并且约简更快。

* [#8104](https://github.com/leanprover/lean4/pull/8104) 让 `fun_induction` 和 `fun_cases`（尝试）
  在目标中展开相关的函数应用。旧行为可以通过
  `set_option tactic.fun_induction.unfolding false` 启用。对于
  `fun_cases`，当函数的结果类型依赖于某个参数时，这一行为暂时还不起作用；
  参见问题 #8296。

* [#8106](https://github.com/leanprover/lean4/pull/8106) 新增 `register_linter_set` 命令，用于声明检查器集合。
  `getLinterValue` 函数现在会检查当前检查器是否
  属于某个已启用的集合（通过 `set_option` 命令
  或命令行启用）。

* [#8169](https://github.com/leanprover/lean4/pull/8169) 让 `omit` 和
  `include` 语法中的空白处理与 `variable` 保持一致。

* [#8171](https://github.com/leanprover/lean4/pull/8171) 会在函数归纳/分类原则中省略那些以
  `by contradiction`（更一般地说，`False.elim`、
  `absurd` 或 `noConfusion`）实现的分支。从这个意义上说，这是一个破坏性变更：
  使用函数归纳后需要证明的目标会更少。

* [#8196](https://github.com/leanprover/lean4/pull/8196) 改进了 `grind` 中 E 匹配模式推断的过程。
  考虑下面这个定理：
  ```lean
  @[grind →]
  theorem eq_empty_of_append_eq_empty {xs ys : Array α} (h : xs ++ ys = #[]) : xs = #[] ∧ ys = #[] :=
    append_eq_empty_iff.mp h
  ```
  在这个 PR 之前，`grind` 会推断出如下模式：
  ```lean
  @HAppend.hAppend _ _ _ _ #2 #1
  ```
  请注意，这个模式会匹配任意 `++` 应用，即使它
  与数组毫无关系。有了这个 PR，推断出的模式变为：
  ```lean
  @HAppend.hAppend (Array #3) (Array _) (Array _) _ #2 #1
  ```
  有了这个新模式，`grind` 在不涉及 `Array` 的目标上
  就不会再考虑这个定理。

* [#8198](https://github.com/leanprover/lean4/pull/8198) 修复了 `grind` 中理论传播使用的一个问题。当
  两个等价类合并时，核心模块可能需要向附属理论求解器（例如
  `cutsat`、交换环等）下推额外的
  等式或不等式。一些求解器（例如 `cutsat`）假设在收到这些事实之前，
  核心模块的全部不变量都已经成立。
  因此立即传播会有在合并过程中过早破坏求解器前置条件的风险。
  为了将合并操作与传播解耦，并保持核心模块与具体求解器无关，这个 PR 添加了
  辅助类型 `PendingTheoryPropagation`。

* [#8208](https://github.com/leanprover/lean4/pull/8208) 通过将常用的 `bv_decide` 重写规则改写为
  基于结构相等工作的 `simproc`，降低了对 `defeq` 的需求。
  这些重写本来的意图就是只依赖结构相等，因此这不会改变
  `bv_decide` 重写器的证明能力，只会让它在某些超大问题上运行得更快。

* [#8209](https://github.com/leanprover/lean4/pull/8209) 修复了 `grind` 策略中的一个非确定性问题。
  这是模型驱动理论组合模块中的一个缺陷。

* [#8221](https://github.com/leanprover/lean4/pull/8221) 调整了实验性模块系统：默认不导出
  `def` 的函数体，除非通过 `def` 上的新属性 `@[expose]`
  或外围 `section` 显式退出这一行为。

* [#8224](https://github.com/leanprover/lean4/pull/8224) 为 `grind` 中的交换环过程增加了诊断信息。

* [#8226](https://github.com/leanprover/lean4/pull/8226) 修复了 `grind` 中交换环过程的
  `simplifyBasis` 过程。

* [#8231](https://github.com/leanprover/lean4/pull/8231) 改变了 `apply?` 的行为，使它用于
  关闭目标的 `sorry` 变为非 `synthetic`。（请记住，正确使用 `synthetic`
  `sorry` 要求策略同时生成一条错误消息，而在这个场景下我们并不希望如此。）
  这一改动可防御 [#8212](https://github.com/leanprover/lean4/issues/8212) 中报告的问题。

* [#8232](https://github.com/leanprover/lean4/pull/8232) 修复了 `rewrite` 策略中常量的精化。
  此前，`rw [eq_self]` 会对 `eq_self` 做两次精化，并把它
  在信息树中加入两次。这会导致 “Expected type”
  在反展开时带着一个未知的宇宙元变量。

* [#8241](https://github.com/leanprover/lean4/pull/8241) 修改了 `rename` 策略的行为，使其在查找要重命名的假设时跳过
  实现细节性质的假设。

* [#8254](https://github.com/leanprover/lean4/pull/8254) 修复了 `ToJson`、`FromJson` 和 `Repr`
  实例被意外内联的问题；这个问题会导致大型结构的 `deriving`
  子句出现指数级编译时间。

* [#8259](https://github.com/leanprover/lean4/pull/8259) 在被投影值的类型是元变量时，
  澄清了 `invalid field notation` 错误消息。

* [#8260](https://github.com/leanprover/lean4/pull/8260) 在类型是 `sort` 时，
  澄清了 `invalid dotted identifier notation` 错误消息。

* [#8261](https://github.com/leanprover/lean4/pull/8261) 调整了 `apply` 统一失败时的错误消息。
  它更清楚地区分了被应用的项与目标，
  也更清楚地区分了给定项的“结论”和该项本身。

* [#8262](https://github.com/leanprover/lean4/pull/8262) 改进了 `type-as-hole` 错误消息。针对
  定理声明中的 `type-as-hole` 错误，不应暗示可以完全省略类型。

* [#8264](https://github.com/leanprover/lean4/pull/8264) 重写了 `application type mismatch` 错误消息，
  更明确地指出问题出在最后一个参数上。
  当同一个参数被多次传给函数时，这尤其有用。

* [#8267](https://github.com/leanprover/lean4/pull/8267) 让 `#guard_msgs` 将 `trace` 消息与
  `info`、`warning` 和 `error` 分开处理。它还引入了
  `#guard_msgs (pass info)` 的写法，类似此前的 `(drop info)`，并补充了
  `(check info)` 作为 `(info)` 的显式形式。

* [#8270](https://github.com/leanprover/lean4/pull/8270) 让 `bv_decide` 的枚举阶段能处理
  宇宙多态的枚举类型。

* [#8271](https://github.com/leanprover/lean4/pull/8271) 修改了 `addPPExplicitToExposeDiff`，使其显示宇宙层级差异，
  并深入访问投影，例如：
  ```
  error: tactic 'rfl' failed, the left-hand side
    (Test.mk (∀ (x : PUnit.{1}), True)).1
  is not definitionally equal to the right-hand side
    (Test.mk (∀ (x : PUnit.{2}), True)).1
  ```
    对于
  ```lean
  inductive Test where
    | mk (x : Prop)

* [#8275](https://github.com/leanprover/lean4/pull/8275) 让 `grind` 中的同余闭包能够找到非依赖箭头的同余，
  也就是说，它现在可以应用 `implies_congr` 定理。

* [#8276](https://github.com/leanprover/lean4/pull/8276) 添加了实例 `Grind.CommRing (Fin n)` 和 `Grind.IsCharP
  (Fin n) n`。新的测试：
  ```lean
  example (x y z : Fin 13) :
      (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
    grind +ring

* [#8277](https://github.com/leanprover/lean4/pull/8277) 通过更可靠地重写 `match` 语句，改进了
  `.induct_unfolding` 的生成；其做法是使用 #8284 中引入的新“同余方程”。
  修复了 #8195。

* [#8280](https://github.com/leanprover/lean4/pull/8280) 为 `grind` 使用的同余闭包过程增加了
  对箭头类型的支持。

* [#8281](https://github.com/leanprover/lean4/pull/8281) 改进了 `grind` 中用于证明辅助类型转换等式的模块。

* [#8284](https://github.com/leanprover/lean4/pull/8284) 为匹配器增加了一类新的方程，即
  “同余方程”，它推广了普通匹配器方程。它们具有
  不受限制的左侧、把判别式与模式联系起来的额外等式假设，
  因而可以证明异构等式。从这个意义上说，它们把同余与重写结合了起来。
  它们可用于重写匹配器应用，尤其是在依赖关系存在时 `simp`
  无法重写判别式的情形，并将用于生成 unfolding 归纳定理。

* [#8285](https://github.com/leanprover/lean4/pull/8285) 修复了为带命名模式的 `match` 语句生成
  分裂器时出现的 “declaration has free variables” 错误。修复了 #8274。

* [#8299](https://github.com/leanprover/lean4/pull/8299) 在 `grind` 中实现了一个缺失的预处理步骤：
  对目标中的元变量做抽象化。

* [#8301](https://github.com/leanprover/lean4/pull/8301) 在 unfolding 归纳原则使用 `bif`
  （也就是 `Bool.cond`）时，能够正确展开函数。

* [#8302](https://github.com/leanprover/lean4/pull/8302) 让 `cases` 在 motive 含有复杂参数、
  且该参数类型依赖于目标时能够优雅失败。`induction` 策略能较好处理这种情况，
  但 `cases` 不能。这个改动至少能优雅退化为不实例化那个 motive 参数。
  更多细节参见问题 [#8296](https://github.com/leanprover/lean4/issues/8296)。

* [#8303](https://github.com/leanprover/lean4/pull/8303) 修复了 `grind` 中缺失 `foldProjs` 调用的问题。

* [#8306](https://github.com/leanprover/lean4/pull/8306) 让 `bv_decide` 能处理一种情况：在其
  枚举类型预处理中，枚举本身出现在依赖类型上下文中
  （例如 `GetElem` 的函数体里），因此 `simp`
  不能轻易地对它们做重写。为此，我们会尽可能早地在管线中去掉
  `BitVec` 上的 `GetElem` 以及 `dite`。

* [#8321](https://github.com/leanprover/lean4/pull/8321) 让终止性参数推断会考虑 Nat 比较的否定形式。
  修复了 [#8257](https://github.com/leanprover/lean4/issues/8257)。

* [#8323](https://github.com/leanprover/lean4/pull/8323) 让 bv_decide 在 bitblasting 中支持理解
  `BitVec.reverse`。

* [#8330](https://github.com/leanprover/lean4/pull/8330) 改进了 `grind` 对结构外延性的支持。它现在
  对结构使用 eta 展开，而不是使用 `[ext]` 生成的外延性定理。例如：

  ```lean
  opaque f (a : Nat) : Nat × Bool

* [#8338](https://github.com/leanprover/lean4/pull/8338) 改进了 `inductive`
  声明在类型参数无效或缺失时显示的错误消息。

* [#8341](https://github.com/leanprover/lean4/pull/8341) 修复了 `grind` 中使用的
  `propagateCtor` 约束传播器。

* [#8343](https://github.com/leanprover/lean4/pull/8343) 将 `Lean.Grind.CommRing` 拆分为 4 个类型类，
  以覆盖 semiring 和非交换环。这暂时还不会改变 `grind` 的行为，
  因为它仍然期望找到全部这 4 个类型类。之后我们会做进一步泛化。

* [#8344](https://github.com/leanprover/lean4/pull/8344) 修复了 `grind` 中项规范化的问题，并新增了
  选项 `grind +etaStruct`。

* [#8347](https://github.com/leanprover/lean4/pull/8347) 为 `grind` 添加了用于处理有序模事实的
  草案类型类。这些接口会随着实现推进继续演化。

* [#8354](https://github.com/leanprover/lean4/pull/8354) 确保在生成 unfolding 的函数归纳定理时，
  `mdata` 不会碍事。

* [#8356](https://github.com/leanprover/lean4/pull/8356) 更努力地清理函数归纳定理中
  n 元函数参数打包的内部细节，尤其是 unfolding 变体。

* [#8359](https://github.com/leanprover/lean4/pull/8359) 改进了函数分类原则：它能更合理地猜测
  哪些函数参数应当成为目标，哪些应当保留为参数（或被丢弃）。
  这会简化这些原则，并提高 `fun_cases` 能展开函数调用的概率。

* [#8361](https://github.com/leanprover/lean4/pull/8361) 修复了 #3188 中引入的 `cases` 策略缺陷：
  当 `cases`（不是 `induction`）配合 `using` 的非原子表达式使用时，
  参数索引会混乱。

* [#8363](https://github.com/leanprover/lean4/pull/8363) 以无冲突的方式统一了各种辅助声明的命名方法，
  并确保该方法兼容精化过程中的分叉分支，例如并行化或类似 Aesop 的
  回溯加重放搜索。

* [#8365](https://github.com/leanprover/lean4/pull/8365) 修复了基底模式的透明度模式。
  这对隐式实例很重要。下面是一个在 Mathlib 中测试 `grind`
  时发现的问题的最小示例。
  ```lean
  example (a : Nat) : max a a = a := by
    grind

* [#8368](https://github.com/leanprover/lean4/pull/8368) 改进了无效模式匹配
  分支产生的错误消息，并提升了模式匹配策略与精化器在错误位置上的一致性。

* [#8369](https://github.com/leanprover/lean4/pull/8369) 修复了 `grind` 使用的
  `instantiateTheorem` 函数中的一个类型错误。此前它无法实例化如下定理
  ```lean
  theorem getElem_reverse {xs : Array α} {i : Nat} (hi : i < xs.reverse.size)
      : (xs.reverse)[i] = xs[xs.size - 1 - i]'(by simp at hi; omega)
  ```
  在如下示例中：
  ```lean
  example (xs : Array Nat) (w : xs.reverse = xs) (j : Nat) (hj : 0 ≤ j) (hj' : j < xs.size / 2)
      : xs[j] = xs[xs.size - 1 - j]
  ```
  并产生如下问题
  ```lean
    [issue] type error constructing proof for Array.getElem_reverse
        when assigning metavariable ?hi with
          ‹j < xs.toList.length›
        has type
          j < xs.toList.length : Prop
        but is expected to have type
          j < xs.reverse.size : Prop
  ```

* [#8375](https://github.com/leanprover/lean4/pull/8375) 确保使用 `mapError` 扩展错误消息时，会调用
  `addMessageContext` 来包含当前上下文，从而正确渲染表达式。
  此外还增加了 `preprendError` 变体，在常见的
  “前置并缩进”场景下拥有更方便的参数顺序。

* [#8403](https://github.com/leanprover/lean4/pull/8403) 补充了全称量词所缺失的单调性引理，
  这些引理会用于定义（余）归纳谓词。

* [#8410](https://github.com/leanprover/lean4/pull/8410) 修复了 `grind` 中的一个 case-splitting 启发式，
  并简化了测试 `grind_palindrome2.lean` 的证明。

* [#8412](https://github.com/leanprover/lean4/pull/8412) 修复了 `grind` 使用的 `markNestedProofs`
  预处理器。此前缺少一种情况（例如 `Expr.mdata`）。

* [#8413](https://github.com/leanprover/lean4/pull/8413) 实现了把全称量词拉过析取的规范化规则。
  这是一级定理证明器常见的规范化步骤。

* [#8417](https://github.com/leanprover/lean4/pull/8417) 引入了 `Lean.Grind.Field`，证明了
  `IsCharP 0` 的域满足 `NoNatZeroDivisors`，并为 `grind`
  建立了一些基础测试（目前仍会失败）。

* [#8426](https://github.com/leanprover/lean4/pull/8426) 新增属性 `[grind?]`。它与 `[grind]` 类似，
  但会显示推断得到的 E 匹配模式。比手工书写更方便。
  感谢 @kim-em 提出这一功能建议。
  ```lean
  set_option trace.grind.ematch.pattern true
  ```
  它还改进了一些测试，并添加了辅助函数
  `ENode.isRoot`。

* [#8429](https://github.com/leanprover/lean4/pull/8429) 添加了 `Lean.Grind.Ring.IsOrdered`，并清理了
  环/模的 `grind` API。这些类型类目前尚未被使用，但会支撑
  `grind` 未来的算法改进。

* [#8437](https://github.com/leanprover/lean4/pull/8437) 修复了目标中存在元变量时 `split`
  的行为。

* [#8438](https://github.com/leanprover/lean4/pull/8438) 确保即使达到 `maxHeartbeats`，
  也能拿到 `grind` 的诊断信息。
  同时删除了一些死代码。

* [#8440](https://github.com/leanprover/lean4/pull/8440) 为 `grind`
  策略实现了非按时间顺序的回溯。这一特性确保 `grind`
  在执行了一个并不相关的分支拆分之后，不需要继续处理无关分支。
  这不仅关系到性能，也关系到最终证明项的大小。
  新测试展示了这一特性的实际效果。
  ```lean
  -- In the following test, the first 8 case-splits are irrelevant,
  -- and non-choronological backtracking is used to avoid searching
  -- (2^8 - 1) irrelevant branches
  /--
  trace:
  [grind.split] p8 ∨ q8, generation: 0
  [grind.split] p7 ∨ q7, generation: 0
  [grind.split] p6 ∨ q6, generation: 0
  [grind.split] p5 ∨ q5, generation: 0
  [grind.split] p4 ∨ q4, generation: 0
  [grind.split] p3 ∨ q3, generation: 0
  [grind.split] p2 ∨ q2, generation: 0
  [grind.split] p1 ∨ q1, generation: 0
  [grind.split] ¬p ∨ ¬q, generation: 0
  -/
  #guard_msgs (trace) in
  set_option trace.grind.split true in
  theorem ex
      : p ∨ q →
        ¬ p ∨ q →
        p ∨ ¬ q →
        ¬ p ∨ ¬ q →
        p1 ∨ q1 →
        p2 ∨ q2 →
        p3 ∨ q3 →
        p4 ∨ q4 →
        p5 ∨ q5 →
        p6 ∨ q6 →
        p7 ∨ q7 →
        p8 ∨ q8 →
        False := by
    grind (splits := 10)
  ```

* [#8443](https://github.com/leanprover/lean4/pull/8443) 增加了关于有序环和有序域的引理，
  这些引理将被 `grind` 新的代数规范化组件使用。

* [#8449](https://github.com/leanprover/lean4/pull/8449) 将 Mathlib 的 `clear_value` 策略上游化并加以扩展。给定一个
  局部定义 `x : T := v`，`clear_value x` 策略会将其替换为
  一个假设 `x : T`；如果目标不依赖值 `v`，则会报错。
  语法 `clear_value x with h` 会在清除 `x` 的值之前创建
  假设 `h : x = v`。此外，
  `clear_value *` 会清除所有可清除的值；如果一个都无法清除，则会报错。

* [#8450](https://github.com/leanprover/lean4/pull/8450) 为 `subst` 策略增加了一项功能：当 `x : X := v`
  是局部定义时，`subst x` 会在目标中用 `v` 替换 `x`，并
  移除 `x`。此前该策略会报错。

* [#8466](https://github.com/leanprover/lean4/pull/8466) 修复了 `grind` 中另一处
  “unexpected kernel projection term during internalization” 问题。

* [#8472](https://github.com/leanprover/lean4/pull/8472) 避免了在查找定理名称时，
  名称解析被定理证明的精化阻塞。

* [#8479](https://github.com/leanprover/lean4/pull/8479) 为 `grind` 实现了考虑 alpha 等价的
  hash-consing。

* [#8483](https://github.com/leanprover/lean4/pull/8483) 确保 `grind` 会在不同调用之间复用 `simp`
  缓存。请记住，`grind` 在内部化期间使用 `simp`
  来规范化项。

* [#8491](https://github.com/leanprover/lean4/pull/8491) 修复了 `simp_all?` 和 `simp_all?!` 的行为，
  分别使其与 `simp_all` 和 `simp_all!` 保持一致。

* [#8506](https://github.com/leanprover/lean4/pull/8506) 在 `grind` 中借助 `match`
  同余方程实现了 `match` 表达式。目标是尽量减少
  需要插入的 `cast` 操作，并避免对函数做 `cast`。
  新方法支持形如 `match h : ... with ...` 的 `match` 表达式。

* [#8512](https://github.com/leanprover/lean4/pull/8512) 新增了 `value_of% ident` 项，它会展开为
  局部或全局常量 `ident` 的值。这对于创建
  定义性假设很有用：
  ```lean
  let x := ... complicated expression ...
  have hx : x = value_of% x := rfl
  ```
* [#8516](https://github.com/leanprover/lean4/pull/8516) 是 #8449 的后续，用于细化 `clear_value` 的语法。
  现在，在清除值之前添加等式假设的语法是
  `clear_value (h : x = _)`。任何与 `x` 定义相等的表达式
  都可以替代下划线。

* [#8536](https://github.com/leanprover/lean4/pull/8536) 修复了 `grind` 中对 `LawfulBEq` 和 `BEq` 的支持。

* [#8541](https://github.com/leanprover/lean4/pull/8541) 确保对于目标中的任意嵌套证明 `h : p`，
  `grind` 策略都会传播 “`p` 为真” 这一事实。

* [#8542](https://github.com/leanprover/lean4/pull/8542) 修复了 `grind` 中两处对 `whnfD` 的不恰当使用。
  它们既是潜在的性能陷阱，也会产生意外错误，
  因为 `whnfD` 并不会、也不应当在所有模块中一致使用。

* [#8544](https://github.com/leanprover/lean4/pull/8544) 在 `grind` 策略中实现了对过量应用
  `ite` 和 `dite` 的支持，并增加了传播和分支拆分的支持。

* [#8549](https://github.com/leanprover/lean4/pull/8549) 修复了 `grind` 中用于实现同余闭包的哈希函数。
  `Expr` 的哈希值不应依赖表达式是否已经被内部化。

* [#8564](https://github.com/leanprover/lean4/pull/8564) 简化了 `grind` 核心与 `cutsat`
  过程之间的接口。在这个 PR 之前，核心会尝试最小化
  需要在 `cutsat` 中内部化的数字字面量数量。这个优化有缺陷
  （见 `grind_cutsat_zero.lean` 测试），而且会产生违反直觉的反例。

* [#8569](https://github.com/leanprover/lean4/pull/8569) 为任意定理增加了对广义 E-match 模式的支持。

* [#8570](https://github.com/leanprover/lean4/pull/8570) 修复了在更新 `stage0` 之后，
  E 匹配广义模式支持中的一些问题。

* [#8572](https://github.com/leanprover/lean4/pull/8572) 为 `grind` 增加了一些广义的 `Option` 定理，
  以避免在 E 匹配过程中发生 `cast` 操作。

* [#8576](https://github.com/leanprover/lean4/pull/8576) 将 `grind` 中的 `ring := true` 设为默认值。
  它还修复了 reification 过程中的一个缺陷，并改进了 `ring` 和 `cutsat`
  模块中的项内部化。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Library"
%%%

````markdown

* [#7352](https://github.com/leanprover/lean4/pull/7352) 重做了围绕 `Id` 单子的 `simp` 集，
  使其不会省略或展开 `pure` 与 `Id.run`。

* [#7995](https://github.com/leanprover/lean4/pull/7995) 为 `Array.qsort` 的性质添加了验证，
  尽可能使用 `grind` 和 `fun_induction`。
  目前这些内容在 `tests/` 目录下，但一旦 `grind` 准备好投入生产使用，
  我们就会把它移入库中。

* [#8182](https://github.com/leanprover/lean4/pull/8182) 为所有 哈希/树映射类型增加了
  `ofList_eq_insertMany_empty` 引理，唯一例外是
  `Std.HashSet.Raw.ofList_eq_insertMany_empty`。

* [#8188](https://github.com/leanprover/lean4/pull/8188) 对 `HashMap` 各变体现有的 `getElem_map`
  语句（以及 `getElem?`、`getElem!`、`getD` 语句）做了调整：
  在名称后加了 prime，并添加了解释性注释；同时将原先不带 prime 的语句替换为
  一个更简单、但只在存在 `LawfulBEq` 时成立的语句。原本那些作为 simp 引理的语句
  现在变成了低优先级 simp 引理，因此在可用 `LawfulBEq` 时，
  更友好的语句会优先触发。

* [#8202](https://github.com/leanprover/lean4/pull/8202) 添加了一条在证明
  `BitVec.msb_sdiv` 时反复需要用到的推理，它是
  `BitVec.one_eq_zero_iff` 的对称版本。

* [#8206](https://github.com/leanprover/lean4/pull/8206) 证明了：对一个由自然数构造出的 bitvector 取负，
  等同于由该数的相反数（视为整数）构造 bitvector。

* [#8216](https://github.com/leanprover/lean4/pull/8216) 完成了为 `Option` 引理添加 `@[grind]`
  标注的工作，并顺带补齐了 `Option` API 中的一些缺口/缺陷。

* [#8218](https://github.com/leanprover/lean4/pull/8218) 继续为 List/Array/Vector 添加 `@[grind]`
  属性，尤其是涉及 `toList`/`toArray` 函数的引理。

* [#8246](https://github.com/leanprover/lean4/pull/8246) 为 HashMap 及其变体添加了 `@[grind]` 标注。

* [#8272](https://github.com/leanprover/lean4/pull/8272) 为 `List.intersperse` 的结果增加了
  关于长度和 `[]?` 用法的引理。

* [#8291](https://github.com/leanprover/lean4/pull/8291) 在可能的地方，将 `Fin` 引理的陈述改为使用
  `[NeZero n] (i : Fin n)`，而不是 `(i : Fin (n+1))`。

* [#8298](https://github.com/leanprover/lean4/pull/8298) 添加了多条 `Option` 引理，并为
  applicative functor 定义了 `Option.filterM`。

* [#8313](https://github.com/leanprover/lean4/pull/8313) 修改了 `Vector` 的定义，使其不再扩展
  `Array`。这可以防止 `Array` API“泄漏”进来。

* [#8315](https://github.com/leanprover/lean4/pull/8315) 将 `Std.Classes.Ord` 拆分为
  `Std.Classes.Ord.Basic`（只带少量导入）、`Std.Classes.Ord.SInt`
  和 `Std.Classes.Ord.Vector`。这些改动避免了
  在多个基础文件中不必要地导入 `Init.Data.BitVec.Lemmas`。
  由于新的纯导入文件 `Std.Classes.Ord` 会导入这三个模块，
  因而终端用户不受影响。

* [#8318](https://github.com/leanprover/lean4/pull/8318) 是 #8272 的后续工作，它把
  `getElem_intersperse` 的条件引理合并成了一条右侧带 `if` 的单一引理。

* [#8327](https://github.com/leanprover/lean4/pull/8327) 为通用的
  `getElem?_eq_none_iff`、`isSome_getElem?` 和 `get_getElem?`
  添加了 `@[grind]` 标注。

* [#8328](https://github.com/leanprover/lean4/pull/8328) 为所有 `contains_iff_mem`
  引理添加了 `@[grind =]` 属性。

* [#8331](https://github.com/leanprover/lean4/pull/8331) 改进了 `PlainDateTime.now` 及其变体的文档字符串。

* [#8346](https://github.com/leanprover/lean4/pull/8346) 补充了若干缺失引理，说明
  `a * b : Int` 为正/非负时的推论。

* [#8349](https://github.com/leanprover/lean4/pull/8349) 修复了预期用于 `ExtDHashMap` 的
  `Inhabited` 实例的签名。

* [#8357](https://github.com/leanprover/lean4/pull/8357) 为 `dite_eq_left_iff` 增加了若干变体，
  它们会在未来的 PR 中派上用场。

* [#8358](https://github.com/leanprover/lean4/pull/8358) 引入了新版迭代器库的一个极简版本。
  它包含列表迭代器以及多种消费者，即 `toArray`、
  `toList`、`toListRev`、`ForIn`、`fold`、`foldM` 和 `drain`。所有
  消费者还都提供了一个无需任何证明即可使用的 `partial` 变体。
  即便使用旧代码生成器，这个受限版本的迭代器库也能生成相当不错的代码。

* [#8378](https://github.com/leanprover/lean4/pull/8378) 改进并扩展了围绕 `Ord` 和 `Ordering` 的 API。

* [#8379](https://github.com/leanprover/lean4/pull/8379) 补充了缺失的 `Option` 引理。

* [#8380](https://github.com/leanprover/lean4/pull/8380) 为迭代器库提供了关于 `toArray`、`toList` 和 `toListRev`
  的简单引理。

* [#8384](https://github.com/leanprover/lean4/pull/8384) 为通过 `List.iter` 和
  `List.iterM` 创建的列表迭代器，提供了关于 `step`、`toArray`、
  `toList` 和 `toListRev` 行为的引理。

* [#8389](https://github.com/leanprover/lean4/pull/8389) 添加了 `List/Array/Vector.ofFnM`，
  即 `ofFn` 的单子版本，并附带基础理论。

* [#8392](https://github.com/leanprover/lean4/pull/8392) 修正了一些 `Array` 引理，使它们讨论的确实是
  `Array` 而不是 `List`。

* [#8397](https://github.com/leanprover/lean4/pull/8397) 清理了许多重复实例（或者某些情况下，
  不必要重复的 `def X := ...; instance Y := X`）。

* [#8399](https://github.com/leanprover/lean4/pull/8399) 为 `HashMap.getElem?_filter` 增加了若干变体，
  它们假设有 `LawfulBEq`，并带有更简单的右侧。`simp` 已经可以通过
  在 lambda 内使用 `getKey_eq` 重写来得到这些结果，但 `grind` 做不到，
  而这些引理能帮助 `grind` 处理 `HashMap` 目标。
  它为所有 `HashMap` 变体、`getElem?/getElem/getElem!/getD` 以及
  `filter` 和 `filterMap` 都提供了相应版本。

* [#8405](https://github.com/leanprover/lean4/pull/8405) 提供了关于循环构造 `ForIn`、`fold`、
  `foldM` 和 `drain` 及其在迭代器上下文中相互关系的引理。

* [#8418](https://github.com/leanprover/lean4/pull/8418) 提供了 `take` 迭代器组合子，它会把任意
  迭代器变成在给定步数后停止的迭代器。该改动包含实现和引理。

* [#8422](https://github.com/leanprover/lean4/pull/8422) 为
  `Std.Time.Timestamp` 和 `Std.Time.Duration` 增加了 `LT` 与 `Decidable` `LT` 实例。

* [#8434](https://github.com/leanprover/lean4/pull/8434) 为 `List.drop` 添加了与 `List.take_cons`
  对应的引理。

* [#8435](https://github.com/leanprover/lean4/pull/8435) 将 Batteries 中的 `LawfulMonadLift(T)` 类型类、
  引理和实例上游到 Core，因为迭代器库需要它们来证明
  `mapM` 运算符的相关引理，而 `mapM` 依赖于 `MonadLiftT`。

* [#8445](https://github.com/leanprover/lean4/pull/8445) 添加了一条 `@[simp]` 引理，并通过注释解释：
  有意不为 `Vector.take`、`Vector.drop` 或 `Vector.tail`
  提供验证 API，因为它们都应当改写为基于
  `Vector.extract` 的形式。

* [#8446](https://github.com/leanprover/lean4/pull/8446) 为 `TreeMap` 及其变体增加了基础的 `@[grind]`
  标注。等我们探索更多示例后，可能还会继续补充。

* [#8451](https://github.com/leanprover/lean4/pull/8451) 提供了纯版本和 monadic 版本的
  迭代器组合子 `filterMap`，以及专门化的 `map` 和 `filter`。这个新
  组合子允许在对流发出的值应用函数的同时过滤掉某些元素。

* [#8460](https://github.com/leanprover/lean4/pull/8460) 继续为 `Option` 添加 `@[grind]` 标注，
  作为 #8379 和 #8298 中近期 `Option` API 增补的后续工作。

* [#8465](https://github.com/leanprover/lean4/pull/8465) 继续补充了关于 `LawfulGetElem` 的引理，
  其中一些还标注了 `@[grind]`。

* [#8470](https://github.com/leanprover/lean4/pull/8470) 为 `getElem_pos/neg` 添加了 `@[simp]`
  （`getElem!` 也类似）。对于具体类型，这些往往本来就已经是 simp 引理。

* [#8482](https://github.com/leanprover/lean4/pull/8482) 为 `List.Pairwise` 和
  `List.Nodup` 添加了初步的 `@[grind]` 标注。

* [#8484](https://github.com/leanprover/lean4/pull/8484) 提供了纯版本和 monadic 版本的
  迭代器组合子 `zip`。

* [#8492](https://github.com/leanprover/lean4/pull/8492) 在“不会溢出”的假设下，为带算术操作的
  `toInt_*` 和 `toNat_*` 添加了 `simp` 引理
  （`toNat_add_of_not_uaddOverflow`、`toInt_add_of_not_saddOverflow`、
  `toNat_sub_of_not_usubOverflow`、`toInt_sub_of_not_ssubOverflow`、
  `toInt_neg_of_not_negOverflow`、`toNat_mul_of_not_umulOverflow`、
  `toInt_mul_of_not_smulOverflow`）。尤其是，它们之所以适合作为 `simp`，
  是因为（1）`rhs` 严格比 `lhs` 更简单；（2）在假设可用时，这个版本
  也比标准操作更简单。

* [#8493](https://github.com/leanprover/lean4/pull/8493) 提供了迭代器组合子 `takeWhile`
  （在谓词变为假之前转发另一个迭代器发出的所有值）
  和 `dropWhile`（丢弃值直到某个关于这些值的谓词变为假，之后转发其余全部值）。

* [#8497](https://github.com/leanprover/lean4/pull/8497) 为
  `List.Sublist`/`IsInfix`/`IsPrefix`/`IsSuffix` 增加了初步的 grind 标注，
  并附带测试用例。

* [#8499](https://github.com/leanprover/lean4/pull/8499) 将 `Array.ofFn.go` 的定义改为对
  `Nat` 递归（而不是良基递归）。这解决了在
  [Zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Memory.20issues.20with.20.60Vector.2EofFn.60.2E/near/520622564)
  上报告的一个问题。

* [#8513](https://github.com/leanprover/lean4/pull/8513) 移除了 `Array.size` 上的 `@[reducible]`
  标注。无论如何，这样做都有助于保持 `List`
  与 `Array` API 的分离，同时也能避免 `grind` 在处理 `List`
  问题时无谓地实例化 `Array` 定理。

* [#8515](https://github.com/leanprover/lean4/pull/8515) 去掉了 `Fin.ofNat'` 名称中的 prime：旧的
  `Fin.ofNat` 已完成其 6 个月弃用周期，现已被移除。

* [#8527](https://github.com/leanprover/lean4/pull/8527) 为关于 `List.countP` 和
  `List.count` 的定理添加了 `grind` 标注。

* [#8552](https://github.com/leanprover/lean4/pull/8552) 提供了数组迭代器（`Array.iter(M)`、
  `Array.iterFromIdx(M)`）、由步进函数产生的无限迭代器
  （`Iter.repeat`），以及一个基于 `ForIn` 实现的有限迭代器 `ForM`
  实例。

* [#8620](https://github.com/leanprover/lean4/pull/8620) 移除了 `NatCast (Fin n)` 全局实例（包括
  直接实例，以及通过 `Lean.Grind.Semiring` 间接获得的实例），因为该实例会使
  `x < n`（其中 `x : Fin k`、`n : Nat`）被精化为
  `x < ↑n`，而不是 `↑x < n`，这并不理想。不过需要注意，
  在 Mathlib 中这仍然会发生！

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Compiler"
%%%

````markdown

* [#8211](https://github.com/leanprover/lean4/pull/8211) 为从新编译器的 LCNF 表示生成 IR 增加了支持。

* [#8236](https://github.com/leanprover/lean4/pull/8236) 修复了 `extern_lib` 与
  `precompileModules` 组合使用时会导致 “symbol not found” 错误的问题。

* [#8268](https://github.com/leanprover/lean4/pull/8268) 针对标量操作数优化了 `lean_nat_shiftr`。
  新编译器会把 Nat 除法转成右移，因此这在一些 profile 中已经变成热点。

* [#8308](https://github.com/leanprover/lean4/pull/8308) 让新编译器的 特化流程
  按照与旧编译器相同的方式计算闭包，尤其是在涉及 lambda 捕获变量时。

* [#8367](https://github.com/leanprover/lean4/pull/8367) 为新编译器增加了新的 `structProjCases`
  pass，对应旧编译器中的 `struct_cases_on` pass；它会把所有来自结构的
  projection 转成 `cases` 表达式。降到 IR 时，
  这会把来自同一结构的所有 projection 聚在一起，而 IR 的 RC pass
  依赖这一不变量（至少在线性性方面如此，甚至可能也关乎一般正确性）。

* [#8409](https://github.com/leanprover/lean4/pull/8409) 为 LCNF 增加了对原生
  UInt8/UInt16/UInt32/UInt64 字面量的支持。

* [#8456](https://github.com/leanprover/lean4/pull/8456) 为 LCNF 增加了对原生 USize 字面量的支持。

* [#8458](https://github.com/leanprover/lean4/pull/8458) 为新编译器增加了闭项提取功能，基本沿用了
  旧编译器的方法。未来我们还会探索一些改进这一方法的思路。

* [#8462](https://github.com/leanprover/lean4/pull/8462) 默认启用了 LCNF 的 extractClosed 流程。

* [#8468](https://github.com/leanprover/lean4/pull/8468) 将 LCNF 的 baseExt/monoExt 环境扩展改为使用
  基于 PersistentHashMap 的自定义环境扩展。优化器依赖于
  多次更新同一 decl 的能力，而 `SimplePersistentEnvExtension`
  无法做到这一点。

* [#8502](https://github.com/leanprover/lean4/pull/8502) 让新编译器改用内核环境查找定义，
  因而当某个声明带有内核错误（例如含有未解决的元变量）时，会跳过编译。
  这与旧编译器的行为一致。

* [#8521](https://github.com/leanprover/lean4/pull/8521) 让 `LCNF.toMono` 递归处理 jmp 参数。

* [#8523](https://github.com/leanprover/lean4/pull/8523) 将新编译器的 noncomputable 检查移入 `toMono`，
  与旧编译器近期的变更保持一致。这会稍微更复杂一些，
  因为我们不能在仅仅使用常量时就抛错，而需要检查后续是否有相关使用。
  围绕 join point 和局部函数，这种实现仍比理论上可能做到的更保守一点，
  但很难想象这在实践中会有影响（若真有，我们也很容易继续放宽）。

* [#8535](https://github.com/leanprover/lean4/pull/8535) 通过修复逻辑中的一个小疏忽，
  让 extractClosed 能提取出更多的 Nat（以及它们的下游用户）。

* [#8540](https://github.com/leanprover/lean4/pull/8540) 修改了 LCNF 特化流程，
  允许 ground 变量依赖局部函数声明（只要没有非 ground 的自由变量）。
  这使得依赖局部 lambda 的 Monad 实例也能进行特化。

* [#8559](https://github.com/leanprover/lean4/pull/8559) 修复了 #8554 中描述的一种对抗性健全性攻击。
  该攻击利用了 `assert!` 不再中止执行，以及用户可以重定向错误消息
  这两个事实。另一个 PR 将为 `Expr.Data` 实现同样的修复。

* [#8560](https://github.com/leanprover/lean4/pull/8560) 与 #8559 类似，不过针对的是 `Expr.mkData`。
  这个漏洞尚未被利用，但对抗性用户可能会找到利用方式。

* [#8561](https://github.com/leanprover/lean4/pull/8561) 提高了 isDefEqProjIssue 测试中的 maxHeartbeats，
  因为在新编译器下运行时，`run_meta` 调用会把编译器自身的分配也算进去。
  在旧编译器中，许多对应的分配发生在 C++ 内部代码里，因此不会
  增加 heartbeat 计数。

* [#8565](https://github.com/leanprover/lean4/pull/8565) 让 LCNF 特化流程 只把类型/实例参数
  当作 ground 变量。此前的策略过于宽松，会导致计算被提升进 specialization 之后的循环里。

* [#8566](https://github.com/leanprover/lean4/pull/8566) 修改了 LCNF 常量折叠 pass，
  使其不再把 Nat 乘法转换为按 2 的幂左移。这个优化的快路径测试相当复杂，
  简单起见直接对乘法走快路径更合理。

* [#8575](https://github.com/leanprover/lean4/pull/8575) 让 LCNF 的 `simpAppApp?` 按预期在
  遇到平凡别名时直接退出。原有逻辑里似乎有一个笔误，而这个 PR
  还把范围从局部变量别名扩展到了全局常量别名。

* [#8582](https://github.com/leanprover/lean4/pull/8582) 修复了 `Param.toMono` 中状态被意外丢弃的问题。
  这段代码最初编写时，除 `typeParams` 外并没有其他状态。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Pretty-Printing"
%%%

````markdown

* [#8041](https://github.com/leanprover/lean4/pull/8041) 修改了 `pp.showLetValues` 的行为，
  现在会使用一个可悬停的 `⋯` 来隐藏 let 的值。这个选项现在默认是 false，
  并新增了 `pp.showLetValues.threshold`，允许小表达式仍然被显示。
  对于策略元变量，还有额外的选项
  `pp.showLetValues.tactic.threshold`，其默认值设置为最大值，
  因为在策略状态中局部值通常很重要。

* [#8372](https://github.com/leanprover/lean4/pull/8372) 修改了 pretty printer，使其使用 `have` 语法
  而不是 `let_fun` 语法。

* [#8457](https://github.com/leanprover/lean4/pull/8457) 修复了 `Format` 中包含硬换行时的一个问题：
  后续（普通）换行会被错误地压平成空格。

* [#8504](https://github.com/leanprover/lean4/pull/8504) 修改了 pretty printer，使其对类父投影使用
  点记法。此前类从不使用点记法。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Documentation"
%%%

````markdown

* [#8199](https://github.com/leanprover/lean4/pull/8199) 增加了一份文档风格指南，其中既包含一般原则，
  也包含文档字符串特有的注意事项。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Server"
%%%

````markdown

* [#7665](https://github.com/leanprover/lean4/pull/7665) 和 [#8180](https://github.com/leanprover/lean4/pull/8180) 增加了
  用于处理 `'Unknown identifier'` 错误的代码操作支持：既可以导入缺失的声明，也可以
  将该标识符改为环境中已有的某个标识符。

* [#8091](https://github.com/leanprover/lean4/pull/8091) 提升了 workspace symbol 请求的性能。

* [#8242](https://github.com/leanprover/lean4/pull/8242) 修复了 `'goals accomplished'` 诊断。
  它们在 #7902 中被意外破坏了。

* [#8350](https://github.com/leanprover/lean4/pull/8350) 修改了命名空间补全，使其使用与
  声明标识符补全相同的算法，因此补全时会使用短名
  （名称的最后一个组成部分）而不是全名，从而避免命名空间重复。

* [#8362](https://github.com/leanprover/lean4/pull/8362) 修复了一个缺陷：某些
  `Unknown identifier` 错误区间上的代码操作无法正常工作；同时还调整了
  若干 `Unknown identifier` 区间，使其真正结束在对应的标识符上。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Lake"
%%%

````markdown

* [#8383](https://github.com/leanprover/lean4/pull/8383) 修复了 `import Lake` 与预编译模块配合使用的问题，
  该功能此前在 MacOS 上已损坏。

* [#8411](https://github.com/leanprover/lean4/pull/8411) 修复了 `Resolve.lean` 中的一个文档缺陷；
  在逆序中，B 应排在 A 前面。

* [#8528](https://github.com/leanprover/lean4/pull/8528) 修复了 Lake 用来判断某个 `lean_lib`
  应通过 `lean --plugin` 而非 `lean --load-dynlib` 加载的启发式。
  此前，如果单一根的名称与库名不匹配，这个问题不会被捕获，
  并会导致加载失败。

* [#8529](https://github.com/leanprover/lean4/pull/8529) 修改了 `lake lean` 和 `lake setup-file`，
  使其会使用 `import` 对应的整个库，来预编译非工作区文件的导入。
  这样能确保额外的链接对象在精化期间已被链接并可用。

* [#8539](https://github.com/leanprover/lean4/pull/8539) 修改了 Lake，使模块构建产出的 Lean 消息使用相对路径。
  这使这些消息能在不同机器之间可移植，这对 Mathlib 的缓存很有用。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___21___0-_LPAR_2025-06-30_RPAR_--Other"
%%%

````markdown

* [#8192](https://github.com/leanprover/lean4/pull/8192) 包含了在发布 v4.20.0-rc1 期间准备的
  `release_checklist.py` 脚本升级。

* [#8366](https://github.com/leanprover/lean4/pull/8366) 为 `Ordering.then` 添加了 `expose` 属性。
  这对使用新编译器构建是必需的；而在旧编译器下也能正常工作，
  因为旧编译器会静默忽略缺失的定义。


````
