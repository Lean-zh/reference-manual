/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: 搞清楚为什么在新的代码生成器下需要这个
set_option maxRecDepth 9000

#doc (Manual) "Lean 4.20.0 (2025-06-02)" =>
%%%
tag := "release-v4.20.0"
file := "v4.20.0"
%%%

````markdown
本次发布共合入 346 项变更。除下文列出的 108 项功能新增和 85 项修复外，还有 6 项重构、7 项文档改进、8 项性能提升、4 项测试套件改进以及 126 项其他变更。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Highlights"
%%%

````markdown

Lean v4.20.0 带来了多项新特性、缺陷修复、Lake 改进，以及为模块系统奠定的基础工作。

````
## 语言特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Highlights--Language-Features"
%%%

````markdown

* [#6432](https://github.com/leanprover/lean4/pull/6432) 实现了 `extract_lets` 和 `lift_lets` 两个策略，
  用于操作 `let`/`let_fun` 表达式。`extract_lets` 策略
  会从主目标中的任意 `let` 和 `let_fun`
  表达式里抽取出新的局部声明。对于目标中的顶层 let，它
  类似于 `intros` 策略，但一般来说也能从更深层的
  子表达式中抽取 let。`lift_lets` 策略会把 `let` 和 `let_fun`
  表达式尽可能外提，但不会
  抽取任何新的局部声明。选项 `extract_lets +lift`
  结合了这两种行为。

* [#7806](https://github.com/leanprover/lean4/pull/7806) 修改了 `ext`、`intro` 和 `enter` 这几个 conv
  策略的语法，使其接受 `_`。引入的绑定器会是一个不可访问名。

* [#7830](https://github.com/leanprover/lean4/pull/7830) 修改了 `induction`、`cases` 以及其他使用
  `Lean.Parser.Tactic.inductionAlts` 的策略的语法。如果某个分支省略了
  `=> ...`，则会被视为 `=> ?_`。例如：
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    cases p with | _ p1 p2
    /-
    case mk
    p1 p2 : Nat
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  这对多个 case 同样适用。例如：
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    induction n with | zero | succ n ih
    /-
    case zero
    ⊢ 0 + 1 = 1 + 0

    case succ
    n : Nat
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  `induction n with | zero | succ n ih` 是 `induction n with
  | zero | succ n ih => ?_` 的简写，而后者又是 `induction n with | zero
  => ?_ | succ n ih => ?_` 的简写。请注意，作为语法解析的结果，
  只有最后一个分支可以省略 `=>`。任何位于带 `=>`
  分支之前、且不含 `=>` 的分支都会被视为该分支的一部分。

* [#7831](https://github.com/leanprover/lean4/pull/7831) 为实现 `try?` 所用的
  `evalAndSuggest` 过程增加了可扩展性。用户现在可以为任意
  策略实现自己的处理器。
  ```lean
  -- Install a `TryTactic` handler for `assumption`
  @[try_tactic assumption]
  def evalTryApply : TryTactic := fun tac => do
    -- We just use the default implementation, but return a different tactic.
    evalAssumption tac
    `(tactic| (trace "worked"; assumption))

  /-- info: Try this: · trace "worked"; assumption -/
  #guard_msgs (info) in
  example (h : False) : False := by
    try? (max := 1) -- at most one solution

  -- `try?` uses `evalAndSuggest` the attribute `[try_tactic]` is used to extend `evalAndSuggest`.
  -- Let's define our own `try?` that uses `evalAndSuggest`
  elab stx:"my_try?" : tactic => do
    -- Things to try
    let toTry ← `(tactic| attempt_all | assumption | apply True | rfl)
    evalAndSuggest stx toTry

  /--
  info: Try these:
  • · trace "worked"; assumption
  • rfl
  -/
  #guard_msgs (info) in
  example (a : Nat) (h : a = a) : a = a := by
    my_try?
  ```

* [#8055](https://github.com/leanprover/lean4/pull/8055) 增加了一个异步 IO 多路复用框架的实现，
  并以 `Timer` API 为例给出了一个实现，
  用于演示其用法。

* [#8088](https://github.com/leanprover/lean4/pull/8088) 为函数归纳原则和函数分类原则增加了
  “unfolding” 变体，名称分别为 `foo.induct_unfolding`
  和 `foo.fun_cases_unfolding`。这些定理把对递归函数结构的归纳
  与函数本身的展开结合起来，
  因而预计会比单纯先做分支拆分再用等式定理重写
  更可靠、更易用，也更高效。

  例如，不再得到

  ```
  ackermann.induct
    (motive : Nat → Nat → Prop)
    (case1 : ∀ (m : Nat), motive 0 m)
    (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
    (x x : Nat) : motive x x
  ```

  而是得到

  ```
  ackermann.fun_cases_unfolding
    (motive : Nat → Nat → Nat → Prop)
    (case1 : ∀ (m : Nat), motive 0 m (m + 1))
    (case2 : ∀ (n : Nat), motive n.succ 0 (ackermann n 1))
    (case3 : ∀ (n m : Nat), motive n.succ m.succ (ackermann n (ackermann (n + 1) m)))
    (x✝ x✝¹ : Nat) : motive x✝ x✝¹ (ackermann x✝ x✝¹)
  ```

* [#8097](https://github.com/leanprover/lean4/pull/8097) 增加了对使用 `Prop` 上格论结构定义的
  归纳与余归纳谓词的支持。它们在语法上是通过
  为递归的、取值于 `Prop` 的函数添加 `greatest_fixpoint` 或 `least_fixpoint`
  终止性子句来定义的。该功能依赖
  `partial_fixpoint` 机制，并要求函数定义具有
  单调性。对于非互递归谓词，会自动生成适当的
  （余）归纳证明原则（由 Park 归纳给出）。

````
## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Highlights--Library-Highlights"
%%%

````markdown

[#8004](https://github.com/leanprover/lean4/pull/8004) 增加了外延哈希映射与哈希集合，
  名称为 `Std.ExtDHashMap`、`Std.ExtHashMap` 和 `Std.ExtHashSet`。外延
  哈希映射的工作方式与普通哈希映射类似，只是它们拥有
  外延性引理，因此在证明中更易使用。不过，
  这也意味着无法再像普通哈希映射那样常规地遍历其条目。

本次发布中其他值得注意的库改进还包括：
- `Option` API 的更新，
- 异步运行时方面的进展：新增了通过 UDP、TCP 套接字以及通道 进行多路复用的支持，
- 与溢出处理相关的 `BitVec` 新定义，
- `Nat.lcm` 的新引理，以及 `Nat.gcd` 与 `Nat.lcm` 的 `Int` 版本，
- 与 `Nat` 和 `Int` 相关的 Mathlib 上游同步，
- 数值类型 API 的补充，例如 `UIntX.ofInt`、`Fin.ofNat'_mul`、`Fin.mul_ofNat'`、`Int.toNat_sub''`，
- `Array`、`List` 中 `Perm` API 的更新，并新增了对 `Vector` 的支持，
- `Array`/`List`/`Vector` 的更多引理。

````
## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Highlights--Lake"
%%%

````markdown

* [#7909](https://github.com/leanprover/lean4/pull/7909) 为 Lake 增加了根据模块源文件路径
  构建模块的支持。命令行和服务器都会用到这一能力。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Highlights--Breaking-Changes"
%%%

````markdown

* [#7474](https://github.com/leanprover/lean4/pull/7474) 更新了 `rw?`、`show_term` 及其他提供策略建议的策略，
  使其在必要时建议使用 `expose_names`，并像 `exact?` 那样在给出建议前先验证策略；
  同时还确保所有这类策略都会在显示建议的消息中生成可悬停信息。

  这对 `TryThis` API 引入了一项**破坏性变更**：`addRewriteSuggestion`
  的 `type?` 参数现在是 `LOption`，而不是 `Option`，从而不再需要
  先前用来表示某次重写已关闭目标的那种权宜写法。

* [#7789](https://github.com/leanprover/lean4/pull/7789) 修复了 `lean` 可能在 `--run`
  之后更改或解释参数的问题。

  **破坏性变更**：现在必须把要运行的 Lean 文件直接放在
  `--run` 之后；此前这一点是意外地没有被强制执行的。

* [#7813](https://github.com/leanprover/lean4/pull/7813) 修复了 Infoview 中
  `let n : Nat := sorry` 被美观打印成 ``n : ℕ := sorry `«Foo:17:17»`` 的问题。其原因是
  顶层表达式被按与 Infoview 悬停信息相同的规则来美观打印。关闭了
  [#6715](https://github.com/leanprover/lean4/issues/6715)。同时重构了 `Lean.Widget.ppExprTagged`；现在
  它接收一个反展开器，如有需要，下游用户若使用了 `explicit`
  参数，应自行配置美观打印器选项覆盖（参见 `Lean.Widget.makePopup.ppExprForPopup`
  的示例）。
  **破坏性变更：** `ppExprTagged` 不会在根表达式上设置 `pp.proofs`。

* [#7855](https://github.com/leanprover/lean4/pull/7855) 将 `ReflBEq` 移至 `Init.Core`，
  并让 `LawfulBEq` 改为扩展 `ReflBEq`。

  **破坏性变更：**
  - `ReflBEq` 的 `refl` 字段已重命名为 `rfl`，以与
    `LawfulBEq` 保持一致；
  - `LawfulBEq` 现在扩展 `ReflBEq`，因此 `LawfulBEq.rfl`
    不再有效。

* [#7873](https://github.com/leanprover/lean4/pull/7873) 修复了语言服务器中与源代码
  搜索路径处理相关的一系列缺陷：删除文件可能导致
  多项功能失效，而未命名文件与磁盘上不存在的文件
  还可能拥有冲突的模块名。

  有关 URI 与模块名之间转换变更的细节，请参见该 PR 的说明。

  **破坏性变更：**
  - `Server.documentUriFromModule` 已重命名为
    `Server.documentUriFromModule?`，并且不再接受 `SearchPath` 参数，
    因为 `SearchPath` 现在会从环境变量 `LEAN_SRC_PATH`
    计算得到。它也已从 `Lean.Server.GoTo` 移至
    `Lean.Server.Utils`。
  - `Server.moduleFromDocumentUri` 也不再接受 `SearchPath` 参数，
    并且不再返回 `Option`。它同样已从
    `Lean.Server.GoTo` 移至 `Lean.Server.Utils`。
  - `System.SearchPath.searchModuleNameOfUri` 函数
    已被移除。建议改用 `Server.moduleFromDocumentUri`。
  - `initSrcSearchPath` 函数已重命名为
    `getSrcSearchPath`，并从 `Lean.Util.Paths` 移至
    `Lean.Util.Path`。它也不再需要接受 `pkgSearchPath`
    参数。

* [#7967](https://github.com/leanprover/lean4/pull/7967) 为 Lake 增加了一个 `bootstrap`
  选项，用于标识 Lean 核心包。这使得 Lake 在用 Lean
  编译 core 中的 Lean 代码时，可以使用当前阶段的 include
  目录，而不是 Lean 工具链中的目录。

  **破坏性变更：** Lean 库目录不再属于
  `getLeanLinkSharedFlags` 的一部分。FFI 用户在链接 Lean 时
  应单独提供这一选项（例如通过 `s!"-L{(←getLeanLibDir).toString}"`）。
  可参见 FFI 示例了解具体做法。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Language"
%%%

````markdown

* [#6325](https://github.com/leanprover/lean4/pull/6325) 确保环境可以被重复加载，
  且不会执行任意代码。

* [#6432](https://github.com/leanprover/lean4/pull/6432) 实现了 `extract_lets` 和 `lift_lets` 两个策略，
  用于操作 `let`/`let_fun` 表达式。`extract_lets` 策略
  会从主目标中的任意 `let` 和 `let_fun`
  表达式里抽取出新的局部声明。对于目标中的顶层 let，它
  类似于 `intros` 策略，但一般来说也能从更深层的
  子表达式中抽取 let。`lift_lets` 策略会把 `let` 和 `let_fun`
  表达式尽可能外提，但不会
  抽取任何新的局部声明。选项 `extract_lets +lift`
  结合了这两种行为。

* [#7474](https://github.com/leanprover/lean4/pull/7474) 更新了 `rw?`、`show_term` 及其他提供策略建议的策略，
  使其在必要时建议使用 `expose_names`，并像 `exact?` 那样在给出建议前先验证策略；
  同时还确保所有这类策略都会在显示建议的消息中生成可悬停信息。

* [#7797](https://github.com/leanprover/lean4/pull/7797) 增加了一个一体化的 `CommRing` 类型类，
  供 `grind` 内部使用，并提供了 `Int`/`BitVec`/`IntX`/`UIntX` 的实例。

* [#7803](https://github.com/leanprover/lean4/pull/7803) 为 `grind` 增加了函数组合的规范化规则。

* [#7806](https://github.com/leanprover/lean4/pull/7806) 修改了 `ext`、`intro` 和 `enter` 这几个 conv
  策略的语法，使其接受 `_`。引入的绑定器会是一个不可访问名。

* [#7808](https://github.com/leanprover/lean4/pull/7808) 为 `grind` 补上了缺失的全称量词规范化规则。

* [#7816](https://github.com/leanprover/lean4/pull/7816) 修复了这样一个问题：当 `x.f`
  是广义字段记法时，`x.f.g` 无法工作，但 `(x.f).g` 却可以。问题在于 `x.f.g`
  会假定 `x : T` 应当是 `T.f` 的第一个显式参数。现在它采用了一致的参数插入规则。
  关闭了 #6400。

* [#7825](https://github.com/leanprover/lean4/pull/7825) 改进了 `grind` 所用 `cutsat`
  过程对 `Nat` 的支持：

  - `cutsat` 不再为每个 `x : Nat` 都向局部上下文*污染性地*加入
    `-1 * NatCast.natCast x <= 0` 这类事实。现在这些事实会
    存储在 `cutsat` 的内部状态中。
  - 现在所有 `Nat` 项都共用同一个上下文。

* [#7829](https://github.com/leanprover/lean4/pull/7829) 修复了 cutsat 反例中的一个问题。它移除了
  为绕开新定理 `eq_def` 而使用的优化（`Cutsat.State.terms`）。在新增的两个测试中，
  此 PR 之前 `cutsat` 会给出一个伪造的反例，其中 `b := 2`。

* [#7830](https://github.com/leanprover/lean4/pull/7830) 修改了 `induction`、`cases` 以及其他使用
  `Lean.Parser.Tactic.inductionAlts` 的策略的语法。如果某个分支省略了
  `=> ...`，则会被视为 `=> ?_`。例如：
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    cases p with | _ p1 p2
    /-
    case mk
    p1 p2 : Nat
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  这对多个 case 同样适用。例如：
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    induction n with | zero | succ n ih
    /-
    case zero
    ⊢ 0 + 1 = 1 + 0

    case succ
    n : Nat
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  `induction n with | zero | succ n ih` 是 `induction n with
  | zero | succ n ih => ?_` 的简写，而后者又是 `induction n with | zero
  => ?_ | succ n ih => ?_` 的简写。请注意，作为语法解析的结果，
  只有最后一个 alternative 可以省略 `=>`。任何位于带 `=>`
  备选分支之前、且不含 `=>` 的备选分支 都会被视为该备选分支的一部分。

* [#7831](https://github.com/leanprover/lean4/pull/7831) 为实现 `try?` 所用的
  `evalAndSuggest` 过程增加了可扩展性。用户现在可以为任意
  策略实现自己的处理器。新增测试展示了这一特性的用法。

* [#7859](https://github.com/leanprover/lean4/pull/7859) 让 LRAT 解析器接受任意在某一处
  推导出空子句的证明，而不要求必须出现在最后一行。像 lrat-trim 这样的某些工具
  偶尔会在推出空子句之后仍包含删除步骤，但只要证明确实在某处正确推导出
  空子句，它就是健全的。

* [#7861](https://github.com/leanprover/lean4/pull/7861) 修复了导致定理无法在 `grind`
  中被激活的问题。

* [#7862](https://github.com/leanprover/lean4/pull/7862) 改进了 `grind` 中 `Bool` 项的规范化。
  请注意，`grind` 目前不会对布尔项做分支拆分，以减小搜索空间。

* [#7864](https://github.com/leanprover/lean4/pull/7864) 为 `grind` 增加了对
  `p -> q` 和 `(h : p) -> q h` 形式蕴含进行分支拆分的支持。参见新选项
  `(splitImp := true)`。

* [#7865](https://github.com/leanprover/lean4/pull/7865) 为 `grind` 补上了一条缺失的
  蕴含传播规则，同时避免了对蕴含做不必要的分支拆分。

* [#7870](https://github.com/leanprover/lean4/pull/7870) 为 `Lean.Grind.CommRing` 增加了一个
  用来记录环特征的 mixin 类型类，并为 `Int`、`IntX`、
  `UIntX` 和 `BitVec` 构造了实例。

* [#7885](https://github.com/leanprover/lean4/pull/7885) 修复了 `grind` 中 cutsat
  过程在包含 `Nat` 项的示例里产生反例的问题。

* [#7892](https://github.com/leanprover/lean4/pull/7892) 改进了 `grind` 对 `funext` 的支持。
  后续还会再提交一个 PR 来减少分支拆分的数量。

* [#7902](https://github.com/leanprover/lean4/pull/7902) 引入了一个专用选项，用于检查
  精译器是否正运行在语言服务器中。

* [#7905](https://github.com/leanprover/lean4/pull/7905) 修复了由 #6125 引入的问题：当某个
  `inductive` 或 `structure` 具有带元变量类型的自动隐式参数时，
  会触发 panic。关闭了 #7788。

* [#7907](https://github.com/leanprover/lean4/pull/7907) 修复了 `grind` 中的两个缺陷。
  1. 基于模型的理论组合会构造出类型错误的项。
  2. 规范化过程中存在 `Nat.cast` 与 `NatCast.natCast` 的问题。

* [#7914](https://github.com/leanprover/lean4/pull/7914) 增加了函数钩子
  `PersistentEnvExtension.saveEntriesFn`，可用于存储仅服务器使用的元数据，
  例如位置信息和文档字符串，而这些信息不应影响（重新）构建。

* [#7920](https://github.com/leanprover/lean4/pull/7920) 在 `bv_decide` 的 bitblaster 中，
  为核心表达式数据类型的 `DecidableEq` 比较引入了一条基于（缓存）哈希值的快路径。

* [#7926](https://github.com/leanprover/lean4/pull/7926) 修复了导致 `grind` 无法证明
  `getElem?_eq_some_iff` 的两个问题。
  1. 缺少针对 `Exists p = False` 的传播规则。
  2. `isCongrToPrevSplit` 这个用于丢弃不必要分支拆分的过滤器缺少条件。

* [#7937](https://github.com/leanprover/lean4/pull/7937) 为 `grind` 实现了前瞻特性，
  以减小搜索空间。目前它只对算术原子有效。

* [#7949](https://github.com/leanprover/lean4/pull/7949) 增加了属性 `[grind ext]`。
  它用于选择哪些 `[ext]` 定理应由 `grind` 使用。选项 `grind +extAll`
  则会指示 `grind` 使用环境中所有可用的 `[ext]` 定理。
  在更新 stage0 之后，我们需要为 `funext` 之类的关键定理
  添加内建的 `[grind ext]` 标注。

* [#7950](https://github.com/leanprover/lean4/pull/7950) 修改了 `all_goals`，使其在恢复模式下
  仅对策略成功的那些目标提交状态变更（同时保留新的消息日志状态）。
  以前我们默认失败的策略也会把状态留在一个还算合理的样子，
  现在则会回滚并承认该目标。此改动还修复了一个缺陷：我们过去只回滚了
  元编程上下文状态而没有回滚策略状态，导致状态不一致
  （即目标列表中含有不在元编程上下文中的元变量）。关闭了 #7883。

* [#7952](https://github.com/leanprover/lean4/pull/7952) 在 `variable` 中存在 autobound implicit 时，
  对局部上下文做了两项改进。首先，局部上下文不再为每个变量保留两份副本
  （如果自动绑定的隐式参数类型含有元变量，就会重建局部上下文）。
  其次，这些元变量现在会使用与声明中绑定器相同的命名算法
  来命名（使用 `mkForallFVars'` 而非 `mkForallFVars`）。

* [#7957](https://github.com/leanprover/lean4/pull/7957) 确保 `mkAppM` 即使在
  `withReducible` 中（例如在 `simp` 里），也能用于构造那些仅在默认透明度下
  类型正确的项，从而避免 `simp` 在化简带有可化简类型的 `let`
  表达式时出错。

* [#7961](https://github.com/leanprover/lean4/pull/7961) 修复了 `bv_decide` 中的一个缺陷：
  当它遇到对某个枚举的 match，其分支数与构造子数相同，但最后一个分支是
  默认分支时，它会错误地放弃处理该 match。

* [#7975](https://github.com/leanprover/lean4/pull/7975) 降低了 `Lean.Grind.CommRing`
  父投影的优先级，以避免它们在 Mathlib 的类型类推断中被使用。

* [#7976](https://github.com/leanprover/lean4/pull/7976) 确保 `bv_decide` 能处理位移操作的
  simp 规范形。

* [#7978](https://github.com/leanprover/lean4/pull/7978) 为 `grind` 中的一个非确定性问题添加了复现用例。

* [#7980](https://github.com/leanprover/lean4/pull/7980) 增加了一个简单类型，用于表示
  `CommRing` 中的单项式。它将用于 `grind`。

* [#7986](https://github.com/leanprover/lean4/pull/7986) 为 `CommRing` 单项式实现了
  逆字典序和分次逆字典序。

* [#7989](https://github.com/leanprover/lean4/pull/7989) 为 `CommRing` 多元多项式增加了
  函数和定理。

* [#7992](https://github.com/leanprover/lean4/pull/7992) 增加了一个函数，用于将
  `CommRing` 表达式转换为多元多项式。

* [#7997](https://github.com/leanprover/lean4/pull/7997) 从函数归纳原则的类型中移除了
  所有类型注解（可选参数、自动参数、输出参数、半输出参数，
  不再像以前那样只移除可选参数）。

* [#8011](https://github.com/leanprover/lean4/pull/8011) 为 `CommRing` 中的多元多项式库增加了
  `IsCharP` 支持。

* [#8012](https://github.com/leanprover/lean4/pull/8012) 增加了选项
  `debug.terminalTacticsAsSorry`。启用后，`grind`、`omega` 等终结型策略
  会被替换为 `sorry`。这对调试和修复 bootstrap 问题很有用。

* [#8014](https://github.com/leanprover/lean4/pull/8014) 让 `RArray` 成为宇宙多态。

* [#8016](https://github.com/leanprover/lean4/pull/8016) 修复了 `CommRing` 多元多项式库中的若干问题：
  1. 用宇宙多态的 `RArray` 替换了先前的数组类型。
  2. 正确消除了被抵消的单项式。
  3. 按降序排列单项式。
  4. 将 `IsCharP` 类型类中的参数 `p` 标记为输出参数。
  5. 为 `Power`、`Mon` 和 `Poly` 这几个类型增加了 `LawfulBEq` 实例。

* [#8025](https://github.com/leanprover/lean4/pull/8025) 简化了 `CommRing` 单项式，并新增了
  1. 单项式 `lcm`
  2. 单项式除法
  3. S-多项式

* [#8029](https://github.com/leanprover/lean4/pull/8029) 在 `grind` 中实现了对 `CommRing` 的基础支持。
  目前已经可以对项做 reify 和规范化。虽然仍需处理方程，
  但 `grind` 已经能证明如下简单示例：
  ```lean
  open Lean.Grind in
  example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
    grind +ring

* [#8032](https://github.com/leanprover/lean4/pull/8032) 为 `grind` 增加了在已知环特征时
  检测不可满足交换环方程的支持。例如：
  ```lean
  example (x : Int) : (x + 1)*(x - 1) = x^2 → False := by
    grind +ring

* [#8033](https://github.com/leanprover/lean4/pull/8033) 增加了把 `CommRing`
  的 reify 后项转换回 Lean 表达式的函数。

* [#8036](https://github.com/leanprover/lean4/pull/8036) 修复了 `bv_decide` 的 bitblaster 中的
  线性性问题，其原因是高阶组合子 `AIG.RefVec.zip` 和
  `AIG.RefVec.fold` 没有被正确特化。

* [#8042](https://github.com/leanprover/lean4/pull/8042) 将 `IntCast` 变为 `Lean.Grind.CommRing`
  的一个字段，并添加了一些把它与 `OfNat` 的取负联系起来的额外公理。
  这样就能使用那些在定义上不等同于先前构造方式的现有实例。

* [#8043](https://github.com/leanprover/lean4/pull/8043) 增加了 `NullCert` 类型，
  用于表示 `grind` 中新的交换环过程将产生的 Nullstellensatz 证书。

* [#8050](https://github.com/leanprover/lean4/pull/8050) 修复了在 `realizeConst` 内部产生
  trace 消息时消息丢失的问题。

* [#8055](https://github.com/leanprover/lean4/pull/8055) 增加了一个异步 IO 多路复用框架的实现，
  并以 `Timer` API 为例给出了一个实现，
  用于演示其用法。

* [#8064](https://github.com/leanprover/lean4/pull/8064) 新增了一个会失败的 `grind` 测试，
  用来展示 grind 错误赋值某个元变量的缺陷。

* [#8065](https://github.com/leanprover/lean4/pull/8065) 为在给 `HashMap` 配置 `grind`
  时遇到的一个障碍增加了一个（失败的）测试用例。

* [#8068](https://github.com/leanprover/lean4/pull/8068) 确保对于启用了实验性模块系统的模块，
  不会导入模块文档字符串或声明范围。

* [#8076](https://github.com/leanprover/lean4/pull/8076) 修复了 `simp?!`、`simp_all?!` 和 `dsimp?!`，
  使其执行自动展开。

* [#8077](https://github.com/leanprover/lean4/pull/8077) 增加了 simproc，用于化简互不重叠的
  位向量加法拼接。之所以添加 simproc 而不只是 `simp` 引理，
  是为了确保能正确重写位向量拼接。由于位向量拼接会在
  位向量宽度层面引发计算，因此使用 simproc 看起来更稳妥。

* [#8083](https://github.com/leanprover/lean4/pull/8083) 修复了 #8081。

* [#8086](https://github.com/leanprover/lean4/pull/8086) 确保带额外参数的互递归结构函数的
  函数归纳原则会按预期做深层拆分。

* [#8088](https://github.com/leanprover/lean4/pull/8088) 为函数归纳原则和函数分类原则增加了
  “unfolding” 变体，名称分别为 `foo.induct_unfolding`
  和 `foo.fun_cases_unfolding`。这些定理把对递归函数结构的归纳
  与函数本身的展开结合起来，
  因而预计会比单纯先做分支拆分再用等式定理重写
  更可靠、更易用，也更高效。

* [#8090](https://github.com/leanprover/lean4/pull/8090) 调整了实验性模块系统，
  使定理体（即证明）不会被导入到其他模块中。

* [#8094](https://github.com/leanprover/lean4/pull/8094) 修复了带有嵌套良基递归与后置固定参数的
  函数之函数归纳原则的生成。这是 #7166 的后续工作。修复了 #8093。

* [#8096](https://github.com/leanprover/lean4/pull/8096) 让 `induction` 能接受这样一种消去子：
  其结论中的 motive 应用带有复杂参数；若可能，这些参数会通过
  `kabstract` 抽象出来。此特性与 unfolding 归纳原则（#8088）
  配合得很好。

* [#8097](https://github.com/leanprover/lean4/pull/8097) 增加了对使用 `Prop` 上格论结构定义的
  归纳与余归纳谓词的支持。它们在语法上是通过
  为递归的、取值于 `Prop` 的函数添加 `greatest_fixpoint` 或 `least_fixpoint`
  终止性子句来定义的。该功能依赖
  `partial_fixpoint` 机制，并要求函数定义具有
  单调性。对于非互递归谓词，会自动生成适当的
  （余）归纳证明原则（由 Park 归纳给出）。

* [#8101](https://github.com/leanprover/lean4/pull/8101) 修复了一个并行性回归问题：
  例如检查命令中错误的检查器不再能找到这些消息。

* [#8102](https://github.com/leanprover/lean4/pull/8102) 允许在 `if let` 子句中使用 ASCII `<-`，
  以与 bind 保持一致；bind 中两种写法都允许。修复了 #8098。

* [#8111](https://github.com/leanprover/lean4/pull/8111) 为 `grind` 中的交换环过程增加了
  辅助类型类 `NoZeroNatDivisors`。Core 里目前只为
  `Int` 实现了它。对于任何实现了 `NoZeroSMulDivisors Nat A`
  的类型 `A`，都可以在 Mathlib 中提供该实例。
  关于这一实例如何影响交换环过程的细节，可参见 `findSimp?`
  和 `PolyDerivation`。

* [#8122](https://github.com/leanprover/lean4/pull/8122) 在 `grind` 新的交换环过程中，
  实现了为 Nullstellensatz 证书生成紧凑证明项的功能。示例如下：
  ```lean
  example [CommRing α] (x y : α) : x = 1 → y = 2 → 2*x + y = 4 := by
    grind +ring

* [#8126](https://github.com/leanprover/lean4/pull/8126) 实现了 `grind` 新交换环过程的主循环。
  在主循环中，对于待办队列中的每个多项式 `p`，该过程会：
  - 使用当前基对它做化简；
  - 计算它与基中已有多项式的 critical pair，并把结果加入队列。

* [#8128](https://github.com/leanprover/lean4/pull/8128) 在 `grind` 新的交换环过程中实现了
  等式传播。思路是把蕴含出来的等式回传给执行同余闭包的 `grind`
  核心模块。在下面的例子中，等式 `x^2*y = 1` 与 `x*y^2 - y = 0`
  蕴含 `y*x` 等于 `y*x*y`，进而由同余可知
  `f (y*x) = f (y*x*y)`。
  ```lean
  example [CommRing α] (x y : α) (f : α → Nat) : x^2*y = 1 → x*y^2 - y = 0 → f (y*x) = f (y*x*y) := by
    grind +ring
  ```

* [#8129](https://github.com/leanprover/lean4/pull/8129) 更新了 If-Normalization 示例：
  现在先给出实现，再随后证明其规格（使用 fun_induction），
  而不是像以前那样直接在子类型中构造一个项。同时还添加了一个
  （失败的）`grind` 测试用例，用于展示未使用 match witness 的问题。

* [#8131](https://github.com/leanprover/lean4/pull/8131) 增加了一个配置选项，用于控制
  `grind` 中交换环过程执行的最大步数。

* [#8133](https://github.com/leanprover/lean4/pull/8133) 修复了 `grind` 交换环过程中使用的
  单项式顺序。下面这个新增测试现在能很快终止。
  ```lean
  example [CommRing α] (a b c : α)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      a^4 + b^4 + c^4 = 9 := by
    grind +ring
  ```

* [#8134](https://github.com/leanprover/lean4/pull/8134) 确保在使用 `grind +ring` 时，
  `set_option grind.debug true` 能正确工作。同时还增加了辅助函数
  `mkPropEq` 和 `mkExpectedPropHint`。

* [#8137](https://github.com/leanprover/lean4/pull/8137) 改进了不实现
  `NoZeroNatDivisors` 类型类之环上的等式传播（也称理论组合）
  和多项式化简。应用这些修复后，`grind` 现在可以证明：
  ```lean
  example [CommRing α] (a b c : α) (f : α → Nat)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by
    grind +ring
  ```
  这个例子同时使用了交换环过程、线性整数算术求解器以及同余闭包。
  对于实现了 `NoZeroNatDivisors` 的环，现在一个多项式在被插入基时，
  还会除以其系数的最大公约数（gcd）。

* [#8157](https://github.com/leanprover/lean4/pull/8157) 修复了例如 `aesop` 使用的
  `replayConst` 与 `bv_decide` 这类使用 `native_decide` 的策略
  之间的不兼容问题。

* [#8158](https://github.com/leanprover/lean4/pull/8158) 修复了 `grind +splitImp` 与箭头传播器。
  给定 `p : Prop` 时，该传播器会错误地假定箭头 `A -> p`
  中的 `A` 总是命题。此 PR 还为 `grind` 增加了一条缺失的规范化规则。

* [#8159](https://github.com/leanprover/lean4/pull/8159) 为实验性模块系统增加了对以下
  import 变体的支持：

  * `private import`：使导入的常量仅在非导出上下文中可用，
    例如证明里。特别是，当当前模块被其他模块导入时，
    该导入既不会被加载，也根本不要求存在。
  * `import all`：使导入模块中的非导出信息（例如证明）在当前模块的
    非导出上下文中可用。其主要目的是允许对原本会保持 opaque 的
    导入定义进行推理。后续还会调整名称解析，使导入的 `private`
    声明也能通过语法访问。

* [#8161](https://github.com/leanprover/lean4/pull/8161) 修改了 `Lean.Grind.CommRing`，
  使其内联 `NatCast` 实例（即由用户提供），而不是从现有数据中构造一个。
  没有这一改动，我们就无法在 Mathlib 中构造可供 `grind` 使用的实例。

* [#8163](https://github.com/leanprover/lean4/pull/8163) 为 `grind +ring` 增加了一些当前会失败的测试，
  它们要么触发内核类型不匹配（缺陷），要么触发内核深度递归
  （也可能只是问题规模过大）。

* [#8167](https://github.com/leanprover/lean4/pull/8167) 改进了 `grind` 所用交换过程里
  计算基与化简多项式的启发式。

* [#8168](https://github.com/leanprover/lean4/pull/8168) 修复了为 `grind` 新交换环过程产生的
  Nullstellensatz 证书构造证明项时的一个缺陷。此前内核会拒绝该证明项。

* [#8170](https://github.com/leanprover/lean4/pull/8170) 为 `grind` 所用交换过程增加了
  构造分步证明项的基础设施。

* [#8189](https://github.com/leanprover/lean4/pull/8189) 在 `grind` 所用的交换环过程中
  实现了**分步证明项**。这些证明项可作为传统 Nullstellensatz
  证书的替代表示，旨在缓解证书构造中常见的**最坏情况下指数级复杂度**问题。

* [#8231](https://github.com/leanprover/lean4/pull/8231) 修改了 `apply?` 的行为，使其用于
  关闭目标的 `sorry` 变为非 synthetic。（请记住，正确使用 synthetic
  sorry 要求策略同时生成一条错误消息，而在这个场景下我们并不希望如此。）
  此 PR 或 #8230 任意一个都足以防御 #8212 中报告的问题。

* [#8254](https://github.com/leanprover/lean4/pull/8254) 修复了 `ToJson`、`FromJson` 和 `Repr`
  实例被意外内联的问题；这个问题会导致大型结构的 `deriving`
  子句出现指数级编译时间。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Library"
%%%

````markdown

* [#6081](https://github.com/leanprover/lean4/pull/6081) 为 `IO.Process.SpawnArgs` 增加了
  `inheritEnv` 字段。若其为 `false`，新建进程不会继承父进程环境。

* [#7108](https://github.com/leanprover/lean4/pull/7108) 证明了 `List.head_of_mem_head?`
  及其对应的 `List.getLast_of_mem_getLast?`。

* [#7400](https://github.com/leanprover/lean4/pull/7400) 为 hash map 的 `filter`、`map`
  和 `filterMap` 函数增加了引理。

* [#7659](https://github.com/leanprover/lean4/pull/7659) 按照
  [这里](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2)
  的定义，为检测溢出增加了 SMT-LIB 运算符
  `BitVec.(umul_overflow, smul_overflow)`，并证明了这些定义与
  `BitVec` 库函数（`umulOverflow_eq`、`smulOverflow_eq`）等价。
  这些证明所需的辅助定理包括 `BitVec.toInt_one_of_lt, BitVec.toInt_mul_toInt_lt, BitVec.le_toInt_mul_toInt, BitVec.toNat_mul_toNat_lt, BitVec.two_pow_le_toInt_mul_toInt_iff, BitVec.toInt_mul_toInt_lt_neg_two_pow_iff`
  以及 `Int.neg_mul_le_mul, Int.bmod_eq_self_of_le_mul_two, Int.mul_le_mul_of_natAbs_le, Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonpos, Int.pow_lt_pow`。
  该 PR 还包含一组测试。

* [#7671](https://github.com/leanprover/lean4/pull/7671) 包含了一个定理，证明有符号除法
  x.toInt / y.toInt 只有在 `x = intMin w` 且 `y = allOnes w`
  （其中 `0 < w`）时才会溢出。
  为了说明这是溢出的*唯一*情形，我们会借助关于取负溢出的结论
  （`BitVec.sdivOverflow_eq_negOverflow_of_neg_one`）：事实上，
  `x.toInt/(allOnes w).toInt = - x.toInt`，也就是说溢出条件与 `x`
  的 `negOverflow` 相同，然后再利用相应定理推理操作数的符号。
  这些 BitVec 定理本身又依赖大量 `Int.ediv_*` 定理，
  它们精细地刻画了整数有符号除法的边界。

* [#7761](https://github.com/leanprover/lean4/pull/7761) 实现了 Bitwuzla 重写
  [NORM_BV_NOT_OR_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510)
  以及
  [BV_ADD_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L395-L401),
  所需的核心定理，它们会把布尔/算术混合表达式转换成纯算术表达式：

  ```lean
  theorem add_shiftLeft_eq_or_shiftLeft {x y : BitVec w} :
      x + (y <<< x) =  x ||| (y <<< x)
  ```

* [#7770](https://github.com/leanprover/lean4/pull/7770) 新增共享互斥锁（读写锁）`Std.SharedMutex`。

* [#7774](https://github.com/leanprover/lean4/pull/7774) 增加了 `Option.pfilter`，
  这是 `Option.filter` 的一个变体，同时还增加了与其及其他 `Option`
  函数有关的若干引理。这些引理是从 #7400 中拆分出来的。

* [#7791](https://github.com/leanprover/lean4/pull/7791) 增加了关于 `Nat.lcm` 的引理。

* [#7802](https://github.com/leanprover/lean4/pull/7802) 为所有 `Nat.gcd` 与 `Nat.lcm`
  的引理增加了 `Int.gcd` 和 `Int.lcm` 版本。

* [#7818](https://github.com/leanprover/lean4/pull/7818) 弃用了 `Option.merge` 和
  `Option.liftOrGet`，改用 `Option.zipWith`。

* [#7819](https://github.com/leanprover/lean4/pull/7819) 扩展了 `Std.Channel`，
  提供完整的同步/异步 API，以及无界、零容量和有界 channel。

* [#7835](https://github.com/leanprover/lean4/pull/7835) 增加了 `BitVec.[toInt_append|toFin_append]`。

* [#7847](https://github.com/leanprover/lean4/pull/7847) 从所有已弃用定理上移除了 `@[simp]`。
  `simp` 仍会使用这些引理，但不会给出警告消息。

* [#7851](https://github.com/leanprover/lean4/pull/7851) 部分回滚了 #7818，因为该 PR 中名为
  `Option.zipWith` 的函数实际上并不对应
  `List.zipWith`。因此改用 `Option.merge` 作为名称。

* [#7855](https://github.com/leanprover/lean4/pull/7855) 将 `ReflBEq` 移至 `Init.Core`，
  并让 `LawfulBEq` 改为扩展 `ReflBEq`。

* [#7856](https://github.com/leanprover/lean4/pull/7856) 修改了定义和定理：
  除非定理专门讨论成员关系实例，否则不再使用 `Option` 上的成员关系实例。

* [#7869](https://github.com/leanprover/lean4/pull/7869) 修复了 #7445 引入的回归问题：
  新的 `Array.emptyWithCapacity` 意外没有用上实际分配容量的正确函数标记。

* [#7871](https://github.com/leanprover/lean4/pull/7871) 泛化了单子化 `Option` 函数上的
  类型类假设。

* [#7879](https://github.com/leanprover/lean4/pull/7879) 增加了 `Int.toNat_emod`，
  与 `Int.toNat_add/mul` 类似。

* [#7880](https://github.com/leanprover/lean4/pull/7880) 增加了函数 `UIntX.ofInt` 及其基础引理。

* [#7886](https://github.com/leanprover/lean4/pull/7886) 增加了 `UIntX.pow` 和
  `Pow UIntX Nat` 实例，有符号定宽整数也做了类似支持。
  目前这些都只是朴素实现，后续需要通过 `@[extern]`
  替换为快速实现（见 #7887）。

* [#7888](https://github.com/leanprover/lean4/pull/7888) 增加了 `Fin.ofNat'_mul` 和
  `Fin.mul_ofNat'`，与现有关于 `add` 的引理相对应。

* [#7889](https://github.com/leanprover/lean4/pull/7889) 增加了 `Int.toNat_sub''`，
  这是 `Int.toNat_sub` 的一个变体：它接受不等式假设，
  而不是要求参数必须是自然数的强制转换。这与现有的 `toNat_add`
  和 `toNat_mul` 相对应。

* [#7890](https://github.com/leanprover/lean4/pull/7890) 补充了关于 `Int.bmod` 的缺失引理，
  与其他 `mod` 变体的引理保持平行。

* [#7891](https://github.com/leanprover/lean4/pull/7891) 为 `x : Int` 增加了 rfl simp 引理
  `Int.cast x = x`。

* [#7893](https://github.com/leanprover/lean4/pull/7893) 增加了 `BitVec.pow` 和
  `Pow (BitVec w) Nat`。当前实现是朴素版本，后续应改为 `@[extern]`
  实现。跟踪见 https://github.com/leanprover/lean4/issues/7887.

* [#7897](https://github.com/leanprover/lean4/pull/7897) 清理了 `Option` 相关开发，
  并在过程中同步了一些来自 Mathlib 的结果。

* [#7899](https://github.com/leanprover/lean4/pull/7899) 重新整理了一些关于整数的结果，
  以确保当前所有关于 `Int.bmod` 的内容都位于
  `DivMod/Lemmas.lean` 中，而不是它的下游文件里。

* [#7901](https://github.com/leanprover/lean4/pull/7901) 增加了
  `instance [Pure f] : Inhabited (OptionT f α)`，
  从而能合成出 `Inhabited (OptionT Id Empty)`。

* [#7912](https://github.com/leanprover/lean4/pull/7912) 增加了 `List.Perm.take/drop`
  和 `Array.Perm.extract`，用于在其他部分保持不变时，
  将置换限制到子列表 / 子数组上。

* [#7913](https://github.com/leanprover/lean4/pull/7913) 补充了一些缺失的
  `List/Array/Vector lemmas`，涉及 `isSome_idxOf?`、
  `isSome_finIdxOf?`、`isSome_findFinIdx?, ` isSome_findIdx?，
  `and the corresponding` isNone 版本。

* [#7933](https://github.com/leanprover/lean4/pull/7933) 增加了关于 `Int.bmod` 的引理，
  以使 `Int.bmod` 与 `Int.emod`/`Int.fmod`/`Int.tmod` 保持对齐。
  此外还补充了 `emod`/`fmod`/`tmod` 的缺失引理，并整理了这四种运算的
  名称和陈述，以提高与对应 `Nat.mod` 引理的一致性。

* [#7938](https://github.com/leanprover/lean4/pull/7938) 增加了关于
  `List/Array/Vector.countP/count` 与 `replace` 交互的引理。
  （特化成 `_self` 和 `_ne` 引理似乎没什么用，因为右侧仍然会有一个 `if`。）

* [#7939](https://github.com/leanprover/lean4/pull/7939) 增加了 `Array.count_erase` 及其特化版本。

* [#7953](https://github.com/leanprover/lean4/pull/7953) 泛化了 `List.Perm` API 中的一些
  类型类假设（不再局限于 `DecidableEq`），并为 `Array`
  复现了 `List.Perm.mem_iff`，同时修复了 `Array.Perm.extract`
  陈述中的一个错误。

* [#7971](https://github.com/leanprover/lean4/pull/7971) 上游同步了
  `Mathlib/Data/Nat/Init.lean` 和 `Mathlib/Data/Nat/Basic.lean`
  中的大量内容。

* [#7983](https://github.com/leanprover/lean4/pull/7983) 上游同步了
  `Mathlib/Data/Int/Init.lean` 中的许多结果。

* [#7994](https://github.com/leanprover/lean4/pull/7994) 为 `Vector` 复现了
  `Array.Perm` API。两者相较 `List.Perm` 的 API 仍都明显欠完整。

* [#7999](https://github.com/leanprover/lean4/pull/7999) 将 `Array.Perm` 和
  `Vector.Perm` 替换为单字段结构。这避免了对 `List` 使用点记法时
  出现例如 `h.cons 3`（其中 `h` 是 `Array.Perm`）这样的行为。

* [#8000](https://github.com/leanprover/lean4/pull/8000) 弃用了若干 `Int.ofNat_*` 引理，
  改用 `Int.natCast_*`。

* [#8004](https://github.com/leanprover/lean4/pull/8004) 增加了外延哈希映射与哈希集合，
  名称为 `Std.ExtDHashMap`、`Std.ExtHashMap` 和 `Std.ExtHashSet`。外延
  哈希映射的工作方式与普通哈希映射类似，只是它们拥有
  外延性引理，因此在证明中更易使用。不过，
  这也意味着无法再像普通哈希映射那样常规地遍历其条目。

* [#8030](https://github.com/leanprover/lean4/pull/8030) 补充了关于
  `List/Array/Vector.findIdx?/findFinIdx?/findSome?/idxOf?` 的一些缺失引理。

* [#8044](https://github.com/leanprover/lean4/pull/8044) 引入模块
  `Std.Data.DTreeMap.Raw`、`Std.Data.TreeMap.Raw` 和 `Std.Data.TreeSet.Raw`，
  并将它们导入 `Std.Data`。所有与原始 tree map 相关的模块
  都被导入到这些新模块中，因此它们现在成了 `Std` 的传递依赖。

* [#8067](https://github.com/leanprover/lean4/pull/8067) 修复了 `Substring.isNat` 的行为，
  使其不再允许空字符串。

* [#8078](https://github.com/leanprover/lean4/pull/8078) 是 #8055 的后续工作，
  实现了异步 TCP 的 `Selector`，从而允许使用 TCP 套接字进行 IO 多路复用。

* [#8080](https://github.com/leanprover/lean4/pull/8080) 修复了 `Json.parse`，
  使其能正确处理代理对。

* [#8085](https://github.com/leanprover/lean4/pull/8085) 将强制转换 `α → Option α`
  移到了新文件 `Init.Data.Option.Coe`。该文件不得在 `Init`
  或 `Std` 中的任何地方被导入。

* [#8089](https://github.com/leanprover/lean4/pull/8089) 为 `Int` 和 `Nat` 增加了优化过的除法函数，
  适用于已知参数可整除的情况（例如规范化有理数时）。其底层依赖 gmp 函数
  `mpz_divexact` 和 `mpz_divexact_ui`。另见 leanprover-community/batteries#1202。

* [#8136](https://github.com/leanprover/lean4/pull/8136) 为
  `List`/`Array`/`Vector` 增加了一批初始的 `@[grind]` 标注，已足以搭建
  一些在 `List` 证明中使用 `grind` 的回归测试。后续还会继续补充。

* [#8139](https://github.com/leanprover/lean4/pull/8139) 是 #8055 的后续工作，
  实现了异步 UDP 的 `Selector`，从而允许使用 UDP 套接字进行 IO 多路复用。

* [#8144](https://github.com/leanprover/lean4/pull/8144) 将 `Option.guard` 的谓词
  从 `p : α → Prop` 改为 `p : α → Bool`。这使它与
  `Option.filter` 等类似函数保持一致。

* [#8147](https://github.com/leanprover/lean4/pull/8147) 增加了 `List.findRev?` 和
  `List.findSomeRev?`，以与现有 Array API 保持对齐，
  并增加了将它们转换为现有操作的 simp 引理。

* [#8148](https://github.com/leanprover/lean4/pull/8148) 泛化了 `List.eraseDups`，
  使其允许任意比较关系。此外还证明了
  `eraseDups_append : (as ++ bs).eraseDups = as.eraseDups ++ (bs.removeAll as).eraseDups`。

* [#8150](https://github.com/leanprover/lean4/pull/8150) 是 #8055 的后续工作，
  为 `Std.Channel` 实现了 Selector，从而允许使用 channel 进行多路复用。

* [#8154](https://github.com/leanprover/lean4/pull/8154) 为
  `HashMap.getElem?_insertMany_list` 增加了无条件引理，作为现有那些
  前提较强的引理的补充。TreeMap（及其依赖/外延变体）也同样增加了对应版本。

* [#8175](https://github.com/leanprover/lean4/pull/8175) 增加了关于
  `List`/`Array`/`Vector.contains` 的 simp/grind 引理。
  在存在 `LawfulBEq` 时，这些结论原本已经可通过把 `contains`
  化简为 `mem` 获得；现在即使没有 `LawfulBEq`，这些引理也会触发。

* [#8184](https://github.com/leanprover/lean4/pull/8184) 为所有 map 变体增加了
  `insertMany_append` 引理。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Compiler"
%%%

````markdown

* [#6063](https://github.com/leanprover/lean4/pull/6063) 将 Lean 使用并随附发布的
  LLVM 与 clang 版本更新到了 19.1.2。

* [#7824](https://github.com/leanprover/lean4/pull/7824) 修复了对 'noncomputable' 定义的使用
  可能被错误编译的问题，同时也彻底移除了对 'noncomputable'
  定义的使用方式。某些 'noncomputable' 定义的用法（例如
  Classical.propDecidable）在类型擦除后不会被正确编译。
  对结果运行优化器可能会把它们优化掉，从而绕过稍后 IR 层面对
  noncomputable 定义使用情况的检查。

* [#7838](https://github.com/leanprover/lean4/pull/7838) 为 `shareCommon` 函数增加了对
  mpz 对象（即大整数）的支持。

* [#7854](https://github.com/leanprover/lean4/pull/7854) 引入了基础 API，
  以便将模块数据分布到多个文件中，为模块系统做准备。

* [#7945](https://github.com/leanprover/lean4/pull/7945) 修复了 `IO.getTaskState`
  与相应任务结束之间潜在的竞态条件，否则会导致未定义行为。

* [#7958](https://github.com/leanprover/lean4/pull/7958) 确保在 `main` 结束后，
  仍会等待专用任务完成，而不是强行退出。若用户确实希望在 main
  结束时直接杀掉这些专用任务，则可在 `main` 末尾调用
  `IO.Process.exit`。

* [#7990](https://github.com/leanprover/lean4/pull/7990) 在新代码生成器的更多类型擦除场景中
  使用了 lcAny。

* [#7996](https://github.com/leanprover/lean4/pull/7996) 在新编译器的 base 阶段禁用了
  局部函数声明的公共子表达式消除（CSE）。此前这会在 lambda 之间引入共享，
  用于绑定带 `do` 记法的调用，进而导致它们后来无法再被内联。

* [#8006](https://github.com/leanprover/lean4/pull/8006) 调整了新代码生成器的内联启发式，
  使之与旧版保持一致，从而确保单子化 fold 会被充分内联，
  使其尾递归结构能暴露给代码生成器。

* [#8007](https://github.com/leanprover/lean4/pull/8007) 调整了新编译器中积极 lambda lifting
  的启发式，使其与旧编译器一致，从而确保对单子代码做内联/特化时，
  不会意外产生代码生成器无法处理的互相尾递归。

* [#8008](https://github.com/leanprover/lean4/pull/8008) 修改了新代码生成器中的 specialization，
  使其将被调函数参数视为 ground 变量，从而改进多态函数的特化效果。

* [#8009](https://github.com/leanprover/lean4/pull/8009) 限制了对 Decidable 类型值上的
  cases 表达式向外提升的行为，因为在编译器后续阶段我们无法正确表示
  对已擦除命题的依赖。

* [#8010](https://github.com/leanprover/lean4/pull/8010) 修复了带有 implemented_by 的
  caseOn 表达式与哈希共享的协作问题，即使精译器生成的是
  重构判别式的项，而非仅复用一个变量，也能正确工作。

* [#8015](https://github.com/leanprover/lean4/pull/8015) 修复了 IR elim_dead_branches pass，
  使其能正确处理没有参数的汇合点；此前这类汇合点
  会被当成不可达。虽然不容易在旧编译器上找到简单复现，
  但在用新编译器 bootstrap Lean 时确实会发生。

* [#8017](https://github.com/leanprover/lean4/pull/8017) 让 IR elim_dead_branches pass
  通过将 extern 函数视为拥有 top 返回值，来正确处理它们。
  这一修复是使用新编译器 bootstrap Init/ 目录所必需的。

* [#8023](https://github.com/leanprover/lean4/pull/8023) 修复了 IR expand_reset_reuse pass，
  使其能正确处理来自相同 base/index 的重复投影。这在旧编译器下
  至少不太容易出现，但在使用新编译器 bootstrap Lean 时会出现。

* [#8124](https://github.com/leanprover/lean4/pull/8124) 在 LCNF elimDeadBranches pass 中，
  通过将所有参数设为 top 而非可能保留为默认的 bottom 值，
  正确处理了逃逸函数。

* [#8125](https://github.com/leanprover/lean4/pull/8125) 为新编译器增加了对 `init` 属性的支持。

* [#8127](https://github.com/leanprover/lean4/pull/8127) 为新编译器增加了对 borrowed 参数的支持，
  这要求在 LCNF 类型处理中增加对 .mdata 表达式的支持。

* [#8132](https://github.com/leanprover/lean4/pull/8132) 为新编译器增加了对内建类型
  `casesOn` 降低的支持。

* [#8156](https://github.com/leanprover/lean4/pull/8156) 修复了旧编译器中 LCNF 转换
  expr 缓存的一个缺陷：其键未包含所有相关信息，导致项会被意外擦除。
  `root` 变量用于决定应用中的 lambda 参数是否应获得 let 绑定，
  这又会影响后续关于类型擦除的决策（erase_irrelevant 假定任何非原子参数
  都是无关的）。

* [#8236](https://github.com/leanprover/lean4/pull/8236) 修复了 `extern_lib` 与
  `precompileModules` 组合使用时会导致 “symbol not found” 错误的问题。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Pretty-Printing"
%%%

````markdown

* [#7805](https://github.com/leanprover/lean4/pull/7805) 修改了原始自然数字面量的美观打印；
  现在 `pp.explicit` 和 `pp.natLit` 都会启用 `nat_lit` 前缀。
  其结果之一是，Infoview 中此类字面量的悬停信息会带上
  `nat_lit` 前缀。

* [#7812](https://github.com/leanprover/lean4/pull/7812) 修改了 Pi 类型的美观打印。
  现在若定义域不是命题，那么对命题会优先使用 `∀` 而不是 `→`。
  例如，`∀ (n : Nat), True` 会被美观打印为 `∀ (n : Nat), True`，
  而不是 `Nat → True`。此外，现在还新增了选项 `pp.foralls`
  （默认值为 true）；若设为 false，则完全禁用 `∀`，可用于教学目的。
  此外还调整了实例隐式绑定器的美观打印——非依赖的 Pi 类型
  不会显示实例绑定器的名字。关闭了 #1834。

* [#7813](https://github.com/leanprover/lean4/pull/7813) 修复了 Infoview 中
  `let n : Nat := sorry` 被美观打印成 ``n : ℕ := sorry `«Foo:17:17»`` 的问题。其原因是
  顶层表达式被按与 Infoview 悬停信息相同的规则来美观打印。关闭了 #6715。
  同时重构了 `Lean.Widget.ppExprTagged`；现在它接收一个反展开器，
  如有需要，下游用户若使用了 `explicit` 参数，应自行配置美观打印器选项覆盖
  （参见 `Lean.Widget.makePopup.ppExprForPopup` 的示例）。
  破坏性变更：`ppExprTagged` 不会在根表达式上设置 `pp.proofs`。

* [#7840](https://github.com/leanprover/lean4/pull/7840) 使结构实例记法在
  `pp.tagAppFns` 为 true 时会用构造子打标签。
  这将让 docgen 中的 `{` 和 `}` 成为指向结构构造子的链接。

* [#8022](https://github.com/leanprover/lean4/pull/8022) 修复了一个缺陷：此前美观打印是在
  清除了局部实例的上下文中完成的。之所以会清除它们，是因为在名称净化步骤中
  局部上下文会被更新；但由于这一步只影响用户名，因此保留局部实例其实是合法的。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Documentation"
%%%

````markdown

* [#7947](https://github.com/leanprover/lean4/pull/7947) 为
  `Lean.mkFreshId`、`Lean.Core.mkFreshUserName`、
  `Lean.Elab.Term.mkFreshBinderName` 和
  `Lean.Meta.mkFreshBinderNameForTactic` 增加了一些文档字符串，以澄清其功能。

* [#8018](https://github.com/leanprover/lean4/pull/8018) 按照 #8014 之后的新现实，
  调整了 RArray 的文档字符串。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Server"
%%%

````markdown

* [#7610](https://github.com/leanprover/lean4/pull/7610) 调整了 `TryThis` widget，
  使其不仅能作为面板 widget 工作，也能在 widget 消息中工作。
  另外还补充了文档，解释为什么需要这一改动。

* [#7873](https://github.com/leanprover/lean4/pull/7873) 修复了语言服务器中与源代码
  搜索路径处理相关的一系列缺陷：删除文件可能导致
  多项功能失效，而未命名文件与磁盘上不存在的文件
  还可能拥有冲突的模块名。

* [#7882](https://github.com/leanprover/lean4/pull/7882) 修复了一个回归问题：
  文档发生变化时，先前版本文档的精译不会被取消。

* [#8242](https://github.com/leanprover/lean4/pull/8242) 修复了 'goals accomplished'
  诊断。它们在 #7902 中被意外破坏了。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Lake"
%%%

````markdown

* [#7796](https://github.com/leanprover/lean4/pull/7796) 在 Lake 增强后的环境
  （例如 `lake env`）中，将 Lean 的共享库路径放到了工作区路径之前。

* [#7809](https://github.com/leanprover/lean4/pull/7809) 修复了在 `lean` 中通过
  `--load-dynlib` 或 `--plugin` 加载库时，以及把它们链接进共享库或可执行文件时，
  库的顺序问题。`Dynlib` 现在会跟踪其依赖，并在传递给链接或加载过程前
  先做拓扑排序。

* [#7822](https://github.com/leanprover/lean4/pull/7822) 修改了 Lake，
  使其对各种文件和目录使用规范化后的绝对路径。

* [#7860](https://github.com/leanprover/lean4/pull/7860) 恢复了 DSL 特性对内建项
  （例如初始化器、精译器和宏）的使用，以及服务器中对
  Lake 插件的使用。

* [#7906](https://github.com/leanprover/lean4/pull/7906) 修改了 Lake 的构建跟踪，
  使其跟踪混合输入。被跟踪的输入会作为 `.trace` 文件的一部分保存，
  这能显著帮助调试跟踪问题。此外，该 PR 还微调了一些现有的 Lake 跟踪。
  其中最重要的是，模块的 olean 跟踪不再包含该模块的源跟踪。

* [#7909](https://github.com/leanprover/lean4/pull/7909) 为 Lake 增加了根据模块源文件路径
  构建模块的支持。命令行和服务器都会用到这一能力。

* [#7963](https://github.com/leanprover/lean4/pull/7963) 增加了在 `Lake.EStateT` 与
  `EStateM` 之间转换的辅助函数。

* [#7967](https://github.com/leanprover/lean4/pull/7967) 为 Lake 增加了一个 `bootstrap`
  选项，用于标识 Lean 核心包。这使得 Lake 在用 Lean
  编译 core 中的 Lean 代码时，可以使用当前阶段的 include
  目录，而不是 Lean 工具链中的目录。

* [#7987](https://github.com/leanprover/lean4/pull/7987) 修复了 #7967 中破坏外部库链接的一个缺陷。

* [#8026](https://github.com/leanprover/lean4/pull/8026) 修复了 #7809 和 #7909 中的缺陷；
  这些缺陷之所以没被发现，部分原因是 `badImport` 测试此前被禁用了。

* [#8048](https://github.com/leanprover/lean4/pull/8048) 将 Lake DSL 语法移入一个
  单独的模块，并把导入压到最小。

* [#8152](https://github.com/leanprover/lean4/pull/8152) 修复了一个回归问题：
  非预编译模块构建会对包的 `extern_lib` 目标执行 `--load-dynlib`。

* [#8183](https://github.com/leanprover/lean4/pull/8183) 让 Lake 测试输出变得详细得多。
  它还修复了一些因测试被禁用而遗漏的缺陷。其中最重要的是，
  目标说明符 `@pkg`（例如在 `lake build` 中）现在始终会被解释为包。
  由于 #7909 的改动，它此前存在歧义。

* [#8190](https://github.com/leanprover/lean4/pull/8190) 在 Lake README 中补充了
  原生库选项（例如 `dynlibs`、`plugins`、`moreLinkObjs`、`moreLinkLibs`）
  与 `needs` 的文档。还加入了关于如何在 Lake 命令行、Lean 配置文件
  和 TOML 配置文件中指定目标的信息。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___20___0-_LPAR_2025-06-02_RPAR_--Other"
%%%

````markdown

* [#7785](https://github.com/leanprover/lean4/pull/7785) 进一步自动化了发布流程，
  包括处理打标签、自动创建新的 `bump/v4.X.0` 分支，以及修复若干缺陷。

* [#7789](https://github.com/leanprover/lean4/pull/7789) 修复了 `lean` 可能在 `--run`
  之后更改或解释参数的问题。

* [#8060](https://github.com/leanprover/lean4/pull/8060) 修复了 Lean 内核中的一个缺陷。
  在归约 `Nat.pow` 时，内核在把第一个参数解释为 `mpz` 数之前，
  没有验证其 WHNF 是否为 `Nat` 字面量。该 PR 补上了这一缺失检查。


````
