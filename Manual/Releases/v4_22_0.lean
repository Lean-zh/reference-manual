/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.22.0 (2025-08-14)" =>
%%%
tag := "release-v4.22.0"
file := "v4.22.0"
%%%

````markdown
本次发布共合入 468 项变更。除下文列出的 185 项功能新增和 85 项修复外，还有 15 项重构、5 项文档改进、4 项性能提升、0 项测试套件改进以及 174 项其他变更。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights"
%%%

````markdown

````
## grind 正式发布！
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Grind-is-released___"
%%%

````markdown

Lean 现在内置了新的 SMT 风格策略 `grind`，并为 Lean 标准库配套提供了相应标注。
`grind` 附带按理论划分的求解器，包括 cutsat（取代 `omega`，并支持模型构造）
以及一个新的 Gröbner 基求解器。

另请参见[参考手册中关于 grind 的章节](https://lean-lang.org/doc/reference/latest//The--grind--tactic/#grind)。

````
## 新编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--New-compiler"
%%%

````markdown

旧编译器已被新编译器取代（[#8577](https://github.com/leanprover/lean4/pull/8577)）！
这解决了许多长期存在的问题，也为未来的大量功能与性能改进
打下了基础。

````
## 新的 `math` 项目模板
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--New-math-project-template"
%%%

````markdown

[#8866](https://github.com/leanprover/lean4/pull/8866) 升级了 `lake init` 与
`lake new` 的 `math` 模板，使其满足严格的 Mathlib 维护标准。
与旧版本（现可通过 `lake new ... math-lax` 使用）相比，新模板会自动提供：
* 与 Mathlib 一致的严格检查选项。
* 用于自动升级到较新 Lean 与 Mathlib 版本的 GitHub 工作流。
* 针对工具链升级的自动发布打标签。
* 由 [doc-gen4](https://github.com/leanprover/doc-gen4) 生成并托管在 `github.io` 上的 API 文档。
* 带有若干 GitHub 专用说明的 README。

````
## 签名帮助
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Signature-help"
%%%

````markdown

[#8511](https://github.com/leanprover/lean4/pull/8511) 在编辑器中实现了签名帮助支持。
演示可参见该 PR 的说明。

````
## 显示导入层级
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Displaying-import-hierarchy"
%%%

````markdown

[#8654](https://github.com/leanprover/lean4/pull/8654)（以及 vscode-lean4 的
[#620](https://github.com/leanprover/vscode-lean4/pull/620)）在
VS Code 中增加了一个新的模块层级组件，可用于同时导航模块的
导入树和被导入树。

````
## have/let 语义重构
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Refactor-of-have___let-semantics"
%%%

````markdown

简而言之：为提升性能，非依赖的 `let` 绑定现在会被转换成 `have` 绑定。
`have` 与 `let` 的语法现已统一，并新增了一些选项。

* [#8373](https://github.com/leanprover/lean4/pull/8373) 启用了将非依赖 `let`
  转换为 `have` 的机制，从而使 `simp` 在不做 zeta 归约时也能工作得更好。
  可通过 `set_option cleanup.letToHave false` 禁用。

* [#8804](https://github.com/leanprover/lean4/pull/8804) 在精译器中实现了对
  非依赖 `let` 表达式的一等支持。这一能力已经在元编程接口与
  精译器中得到完整支持。

* [#8914](https://github.com/leanprover/lean4/pull/8914) 修改了 `let` 与 `have` 的项语法，
  使二者保持一致。新增了配置选项；例如，对于*非依赖* let，
  `have` 等价于 `let +nondep`。其他选项包括 `+usedOnly`
  （用于 `let_tmp`）、`+zeta`（用于 `letI`/`haveI`）和
  `+postponeValue`（用于 `let_delayed`）。此外还支持
  `let (eq := h) x := v; b`，用于在精译 `b` 时引入
  `h : x = v`。`eq` 选项同样适用于模式匹配，例如
  `let (eq := h) (x, y) := p; b`。

* [#8935](https://github.com/leanprover/lean4/pull/8935) 为 `let` 与 `have` 语法增加了
  `+generalize` 选项。例如，`have +generalize n := a + b; body`
  会在精译 `body` 时，把期望类型中所有 `a + b` 的出现都替换为 `n`。
  这可以看作 `generalize` 策略的项级版本。还可以把它与 `eq` 结合，
  写成 `have +generalize (eq := h) n := a + b; body`，对应于
  `generalize h : n = a + b`。

* [#8954](https://github.com/leanprover/lean4/pull/8954) 增加了一个高效地将 `let`
  表达式转换为 `have` 表达式的过程（`Meta.letToHave`）。
  这一过程以 `let_to_have` 策略的形式对外暴露。

* [#9086](https://github.com/leanprover/lean4/pull/9086) 弃用了 `let_fun` 语法，改用 `have`，
  并从 WHNF 与 `simp` 中移除了对 `letFun` 的支持。

````
## Simp
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Simp"
%%%

````markdown

* **标记未使用的 `simp` 参数**

  [#8901](https://github.com/leanprover/lean4/pull/8901) 增加了一个检查器（`linter.unusedSimpArgs`），当
  simp 参数（`simp [foo]`）未被使用时会发出提示，并附带一个可点击的删除建议。
  它能正确处理重复执行的 `simp` 调用（例如在 `all_goals` 内），但会跳过宏。

* **检测可能导致循环的引理**

  [#8865](https://github.com/leanprover/lean4/pull/8865) 让 `simp` 能识别并警告当前 simp 集中
  可能导致循环的 simp 引理。每当化简因令人头疼的
  “max recursion depth” 错误而失败时，它会自动执行这一检查；
  也可以通过 `set_option linter.loopingSimpArgs true`
  让它始终执行。该检查默认未开启，因为它开销不小，
  而且可能会对实际上仍能工作的 simp 调用发出警告。

* **通过复用缓存加速 simp**

  [#8880](https://github.com/leanprover/lean4/pull/8880) 让 `simp`
  更频繁地查询自己的缓存，以避免重复工作。

* **为 dsimp 提供显式 `defeq` 属性**

  [#8419](https://github.com/leanprover/lean4/pull/8419) 引入了显式 `defeq` 属性，
  用于标记可供 `dsimp` 使用的定理。与先前通过查看证明体的逻辑相比，
  显式属性的好处是我们可以可靠地在跨模块边界时省略定理体。
  它也有助于文件内并行化。

````
## 带解释的命名错误
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Named-errors-with-explanations"
%%%

````markdown

Lean 现在支持带有关联解释的命名错误消息。

[#8649](https://github.com/leanprover/lean4/pull/8649) 和 [#8730](https://github.com/leanprover/lean4/pull/8730)
增加了用于注册和抛出命名错误的宏语法、在 Infoview 与命令行中显示
错误名的机制，以及链接到[参考手册中的错误解释](https://lean-lang.org/doc/reference/latest/Error-Explanations/#The-Lean-Language-Reference--Error-Explanations)的能力。

这套基础设施为可搜索的错误索引与更好的诊断打下了基础。

````
## `finally` 代码段
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--finally-section"
%%%

````markdown

[#8723](https://github.com/leanprover/lean4/pull/8723) 实现了位于（可能为空的）
`where` 代码块之后的 `finally` 段。`where ... finally` 会打开一个
策略序列块，其中的目标是定义体及其因使用 `let rec` 和
`where` 而产生的辅助定义中那些尚未赋值的元变量。
这使得我们可以通过一次调用诸如 `all_goals` 之类的策略，
来解决定义体中的多个证明义务：
```lean
example (i j : Nat) (xs : Array Nat) (hi : i < xs.size) (hj: j < xs.size) :=
  match i with
  | 0 => x
  | _ => xs[i]'?_ + xs[j]'?_
where x := 13
finally all_goals assumption
```

````
## 多态范围与切片
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Polymorphic-ranges-and-slices"
%%%

````markdown

[#8784](https://github.com/leanprover/lean4/pull/8784) 引入了新的范围语法：
`1...*`, `1...=3`, `1...<3`, `1<...=2`, `*...=3.`.

[#8947](https://github.com/leanprover/lean4/pull/8947) 将这一语法扩展到切片，
从而允许写出 `xs[*...end]` 这样的表达式。

````
## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Library-highlights"
%%%

````markdown

标准库中的值得注意的新增内容包括：

* 迭代器（[#8420](https://github.com/leanprover/lean4/pull/8420)、[#8545](https://github.com/leanprover/lean4/pull/8545)、[#8615](https://github.com/leanprover/lean4/pull/8615)、[#8629](https://github.com/leanprover/lean4/pull/8629)、[#8768](https://github.com/leanprover/lean4/pull/8768)），

* `Async` 操作的单子化接口（[#8003](https://github.com/leanprover/lean4/pull/8003)），

* DNS 函数（[#8072](https://github.com/leanprover/lean4/pull/8072)），

* 系统信息函数（[#8109](https://github.com/leanprover/lean4/pull/8109)）。

````
## 实验性：单子化验证框架
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Experimental___-monadic-verification-framework"
%%%

````markdown

[#8995](https://github.com/leanprover/lean4/pull/8995) 在 `Std.Do.Triple` 中为单子程序
引入了 Hoare 逻辑，并配套提供若干策略：

* `mspec`，用于应用 Hoare 三元组规格；
* `mvcgen`，用于将 Hoare 三元组证明义务 `⦃P⦄ prog ⦃Q⦄`
  转换为纯验证条件。

````
## 实验性：模块系统
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Experimental___-module-system"
%%%

````markdown

新模块系统（通过在 import 语句前加 `module` 关键字启用）现已可供试验。

````
## 实验性：在同一仓库的不同 checkout 之间共享 oleans
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Experimental___-sharing-oleans-between-different-checkouts-of-the-same-repository"
%%%

````markdown

[#8922](https://github.com/leanprover/lean4/pull/8922) 为 Lake 引入了本地产物缓存。启用后，Lake
会通过基于输入与内容寻址的缓存，在同一包的不同实例之间共享
构建产物（已构建文件）。目前需要设置 `export LAKE_ARTIFACT_CACHE=true`。

````
## 关于 `sorry` 的警告
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Warnings-about-sorrys"
%%%

````markdown

[#8662](https://github.com/leanprover/lean4/pull/8662) 增加了 `warn.sorry` 选项（默认值为 true），
当声明包含 `sorryAx` 时，会记录
“declaration uses 'sorry'” 警告；若设为 false，则不记录该警告。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Highlights--Breaking-changes"
%%%

````markdown

* [#8751](https://github.com/leanprover/lean4/pull/8751) 将 `Expr.letE` 的 `nondep`
  字段加入了 C++ 数据模型。

  破坏性变更：`Expr.updateLet!` 已重命名为 `Expr.updateLetE!`。

* [#8105](https://github.com/leanprover/lean4/pull/8105) 增加了对服务端 `RpcRef` 复用的支持，
  并修复了一个缺陷：文件仍在处理时，InfoView 中的 trace 节点会提前关闭。

  破坏性变更：由于 `WithRpcRef` 现在能够跟踪自身标识，以判断哪些
  `WithRpcRef` 的使用构成复用，因此 `WithRpcRef` 的构造子已被设为 `private`，
  以避免下游用户手动设置 `id` 来创建 `WithRpcRef` 实例。现在更推荐使用
  `WithRpcRef.mk`（位于 `BaseIO`）来创建 `WithRpcRef` 实例。

* [#8654](https://github.com/leanprover/lean4/pull/8654) 为 VS Code 中新的模块层级组件
  增加了服务端支持。

  破坏性变更：为了实现 `$/lean/moduleHierarchy/importedBy` 请求，
  此 PR 在 .ilean 格式中加入了文件的直接导入，并提升了 .ilean 格式版本。

* [#8804](https://github.com/leanprover/lean4/pull/8804) 在精译器中实现了对
  非依赖 `let` 表达式的一等支持。

  破坏性变更：使用 `letLambdaTelescope`/`mkLetFVars` 时需要设置
  `generalizeNondepLet := false`；详情见 PR 说明。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Language"
%%%

````markdown

* [#6672](https://github.com/leanprover/lean4/pull/6672) 将 `Lean.*`、`*.Tactic.*` 和
  `*.Linter.*` 下的所有声明从 `exact?` 与 `rw?` 的结果中过滤掉。

* [#7395](https://github.com/leanprover/lean4/pull/7395) 修改了 `show t` 策略，
  使其行为与文档一致。此前它只是 `change t` 的同义词，
  现在它会找到第一个能与项 `t` 统一的目标，并把它移到目标列表前端。

* [#7639](https://github.com/leanprover/lean4/pull/7639) 修改了反身归纳类型生成的
  `below` 与 `brecOn` 实现，使其支持位于 `Sort u` 中的 motive，
  而不再仅限于 `Type u`。

* [#8337](https://github.com/leanprover/lean4/pull/8337) 调整了实验性模块系统，
  使其不再从模块中导出任何 private 声明。

* [#8373](https://github.com/leanprover/lean4/pull/8373) 在多种上下文中启用了将
  非依赖 `let` 转换为 `have` 的机制：包括非递归定义体、方程引理、
  智能展开定义以及定理类型。这样做的一个动机是：当关闭 zeta 归约时，
  `simp` 只能有效重写 `have` 表达式（例如 `split` 会在关闭 zeta 归约时使用 `simp`），
  因而我们通过把 `let` 转成 `have` 来缓存非依赖性计算。
  可通过 `set_option cleanup.letToHave false` 禁用这一转换。

* [#8387](https://github.com/leanprover/lean4/pull/8387) 改进了 `end` 产生的错误消息，
  并阻止非法的 `end` 命令在失败时关闭作用域。

* [#8419](https://github.com/leanprover/lean4/pull/8419) 引入了显式 `defeq` 属性，
  用于标记可供 `dsimp` 使用的定理。与先前通过查看证明体的逻辑相比，
  显式属性的好处是我们可以可靠地在跨模块边界时省略定理体。
  它也有助于文件内并行化。

* [#8519](https://github.com/leanprover/lean4/pull/8519) 将未暴露定义的等式定理设为 private。
  如果模块作者选择不暴露某个函数的函数体，那么通常也不希望其实现
  通过等式定理泄露出来。这也有助于 #8419。

* [#8543](https://github.com/leanprover/lean4/pull/8543) 为 `grind` 增加了将类型嵌入到
  `Int` 中、供 cutsat 使用的类型类。例如，这使得 `Fin n` 或
  Mathlib 的 `ℕ+` 都能以统一且可扩展的方式处理。

* [#8568](https://github.com/leanprover/lean4/pull/8568) 修改了 `structure` 精译器，
  为结构字段和显式父投影增加局部 terminfo，从而在存在依赖字段时也能
  “跳转到定义”。

* [#8574](https://github.com/leanprover/lean4/pull/8574) 为错误消息提示建议 widget
  增加了一种额外的 diff 模式，按单词而非按字符显示差异。

* [#8596](https://github.com/leanprover/lean4/pull/8596) 将 `guard_msgs.diff=true` 设为默认值。
  `#guard_msgs` 的主要用途是编写测试，这会让查看变动后的测试输出轻松不少。

* [#8609](https://github.com/leanprover/lean4/pull/8609) 用 `grind` 缩短了 LRAT 检查器中的一些证明。
  目的倒不特别在于改善这些证明的质量或可维护性（尽管希望这会是附带收益），
  而是为了让 `grind` 得到更多实战检验。

* [#8619](https://github.com/leanprover/lean4/pull/8619) 修复了 `grind` 在应用单射性定理时
  的内部化（也就是预处理）问题。

* [#8621](https://github.com/leanprover/lean4/pull/8621) 修复了 `grind` 使用的
  等式归解过程中的一个缺陷。
  该过程现在会执行拓扑排序，以确保每个化简后的定理声明都在其被引用的
  任何位置**之前**生成。
  先前，对
  ```lean
  h : ∀ x, p x a → ∀ y, p y b → x ≠ y
  ```
  在下例中应用等式归解时
  ```lean
  example
    (p : Nat → Nat → Prop)
    (a b c : Nat)
    (h  : ∀ x, p x a → ∀ y, p y b → x ≠ y)
    (h₁ : p c a)
    (h₂ : p c b) :
    False := by
    grind
  ```
  会导致 `grind` 生成错误的项
  ```lean
  p ?y a → ∀ y, p y b → False
  ```
  该补丁消除了这一错误，并会生成下面这个正确的化简定理
  ```lean
  ∀ y, p y a → p y b → False
  ```

* [#8622](https://github.com/leanprover/lean4/pull/8622) 为 `grind` 增加了一个测试 / 用例示例，
  搭建了 `IndexMap` 的最基本形态，仿照 Rust 的
  [`indexmap`](https://docs.rs/indexmap/latest/indexmap/)。
  这并不打算成为完整实现，只是足够拿来锻炼 `grind`。

* [#8625](https://github.com/leanprover/lean4/pull/8625) 改进了 `grind` 成功时产生的
  诊断信息。现在会包含执行过的分支拆分列表，以及每个函数符号的应用次数。

* [#8633](https://github.com/leanprover/lean4/pull/8633) 在 `grind` 中实现了对分支拆分的跟踪。
  当 `grind` 失败或请求诊断信息时，就会显示这些信息。
  例如：

  - 失败时

* [#8637](https://github.com/leanprover/lean4/pull/8637) 增加了使用反射来规范化
  `IntModule` 表达式所需的后台定理。

* [#8638](https://github.com/leanprover/lean4/pull/8638) 改进了 `grind` 产生的诊断信息。
  现在会先按生成次序、再按 `Expr.lt` 对等价类排序。

* [#8639](https://github.com/leanprover/lean4/pull/8639) 补全了 `ToInt` 这一组类型类，
  `grind` 会用它们把类型嵌入整数中供 `cutsat` 使用。它包含常见具体数据类型
  （`Fin`、`UIntX`、`IntX`、`BitVec`）的实例，并且可扩展
  （例如可支持 Mathlib 的 `PNat`）。

* [#8641](https://github.com/leanprover/lean4/pull/8641) 为 `#print` 命令增加了
  `#print sig $ident` 变体，它会省略函数体。这在如下
  ```
  #guard_msgs (drop trace, all) in #print sig foo
  ```
  这种写法下对测试元代码很有用。相较 `#check`，它的好处在于会显示声明种类、
  可约化属性（以及未来可能显示更多内建属性，例如 #8419 中的 `@[defeq]`）。
  （缺点之一是 `#check` 会显示未使用的函数参数名，例如在归纳原则中；
  这一点之后大概还能继续改进。）

* [#8645](https://github.com/leanprover/lean4/pull/8645) 为 `grind` 未来的 `IntModule`
  线性算术过程增加了许多辅助定理。
  它还为输入原子的规范化增加了辅助定理，并在 `grind` 新的线性算术过程中
  加入了对不相等约束（disequality）的支持。

* [#8650](https://github.com/leanprover/lean4/pull/8650) 为系数规范化和等式检测增加了辅助定理。
  这些定理将用于 `grind` 的线性算术过程。

* [#8662](https://github.com/leanprover/lean4/pull/8662) 增加了 `warn.sorry` 选项（默认值为 true），
  当声明包含 `sorryAx` 时，会记录
  “declaration uses 'sorry'” 警告；若设为 false，则不记录该警告。

* [#8670](https://github.com/leanprover/lean4/pull/8670) 增加了若干辅助定理，
  供 `grind` 中 `CommRing` 模块与 linarith 过程对接时使用。

* [#8671](https://github.com/leanprover/lean4/pull/8671) 允许 structure 使用不带括号的绑定器，
  从而与 `inductive` 保持一致。

* [#8677](https://github.com/leanprover/lean4/pull/8677) 为 `grind` 中的 linarith 模块
  增加了基础设施。

* [#8680](https://github.com/leanprover/lean4/pull/8680) 为 `grind` 的新 linarith 模块
  增加了 `reify?` 与 `denoteExpr`。

* [#8682](https://github.com/leanprover/lean4/pull/8682) 使用 `CommRing` 模块
  来规范化 linarith 不等式。

* [#8687](https://github.com/leanprover/lean4/pull/8687) 实现了在 `grind` 的 linarith 过程中
  构造证明项所需的基础设施，同时还为 reify 后的对象增加了 `ToExpr` 实例。

* [#8689](https://github.com/leanprover/lean4/pull/8689) 为 `CommRing` 与 `linarith` 的接口
  实现了证明项生成，并修复了 `CommRing` 的辅助定理。

* [#8690](https://github.com/leanprover/lean4/pull/8690) 实现了 grind 中 linarith 组件
  模型搜索过程的主框架。目前它只能处理不等式，
  但已经可以解决如下简单目标：
  ```lean
  example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c : α)
      : a < b → b < c → c < a → False := by
    grind

* [#8693](https://github.com/leanprover/lean4/pull/8693) 修复了用于在 grind 中
  对接 ring 与 linarith 模块的语义函数。

* [#8694](https://github.com/leanprover/lean4/pull/8694) 当结构是有序环时，
  为 linarith 实现了对 `One.one` 的特殊支持。它还修复了初始化期间的缺陷。

* [#8697](https://github.com/leanprover/lean4/pull/8697) 在 `grind` 线性算术过程中
  实现了对不等式的支持，并简化了其设计。已经可以解决的示例如下：
  ```lean
  open Lean.Grind
  example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c d : α)
      : a + d < c → b = a + (2:Int)*d → b - d > c → False := by
    grind

* [#8708](https://github.com/leanprover/lean4/pull/8708) 修复了 `grind` 中 linarith 与 ring 模块
  接口里的一个内部化缺陷。`CommRing` 模块在规范化过程中可能会创建新项。

* [#8713](https://github.com/leanprover/lean4/pull/8713) 修复了 `grind` 所用交换环模块中的一个缺陷。
  它此前错过了一些化简机会。

* [#8715](https://github.com/leanprover/lean4/pull/8715) 为 `grind linarith` 模块中处理
  不相等约束实现了基础设施。回溯机制仍待实现。

* [#8723](https://github.com/leanprover/lean4/pull/8723) 实现了位于（可能为空的）
  `where` 代码块之后的 `finally` 段。`where ... finally` 会打开一个
  策略序列块，其中的目标是定义体及其因使用 `let rec` 和
  `where` 而产生的辅助定义中那些尚未赋值的元变量。

* [#8730](https://github.com/leanprover/lean4/pull/8730) 增加了抛出带有关联错误解释的
  命名错误的支持。  具体来说，它为 #8649 定义的语法增加了精译器，
  并使用了 #8651 加入的错误解释基础设施。这还包括错误名的补全、
  悬停和跳转到定义。

* [#8733](https://github.com/leanprover/lean4/pull/8733) 为 `grind` 的 linarith 过程
  实现了不等式分裂与非按时间顺序的回溯。
  ```lean
  example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c d : α)
      : a ≤ b → a - c ≥ 0 + d → d ≤ 0 → d ≥ 0 → b = c → a ≠ b → False := by
    grind
  ```

* [#8751](https://github.com/leanprover/lean4/pull/8751) 将 `Expr.letE` 的 `nondep`
  字段加入了 C++ 数据模型。此前该字段一直未被使用，后续 PR 中精译器
  将利用它来编码 `have` 表达式（即非依赖 `let`）。
  内核在类型检查期间并不会验证 `nondep` 是否被正确应用。
  `letE` 的反展开器现在在 `nondep` 为 true 时会打印 `have`，
  尽管目前 `have` 仍被精译为 `letFun`。
  破坏性变更：`Expr.updateLet!` 已重命名为 `Expr.updateLetE!`。

* [#8753](https://github.com/leanprover/lean4/pull/8753) 修复了 `simp` 的一个缺陷：
  它在不同 `simp` 调用之间不会重置已做 zeta-delta 归约的 let 定义集合。
  它还修复了另一个缺陷：`simp` 会报告那些并未作为 simp 参数给出的
  ζ-δ 归约 let 定义（这些多余的 let 定义是由于某些过程临时将
  `zetaDelta := true` 而出现的）。该 PR 还修改了 zeta-delta 跟踪函数的
  元编程接口，使其可重入，并防止这类“不重置”缺陷再次出现。关闭了 #6655。

* [#8756](https://github.com/leanprover/lean4/pull/8756) 为 grind linarith 实现了反例生成功能。例如：
  ```lean
  example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
      : b ≥ 0 → c > b → d > b → a ≠ b + c → a > b + c → a < b + d →  False := by
    grind
  ```
  会产生如下反例
  ```
  a := 7/2
  b := 1
  c := 2
  d := 3
  ```

* [#8759](https://github.com/leanprover/lean4/pull/8759) 为 grind linarith 实现了
  基于模型的理论组合。例如：
  ```lean
  example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (f : α → α → α) (x y z : α)
      : z ≤ x → x ≤ 1 → z = 1 → f x y = 2 → f 1 y = 2 := by
    grind
  ```

* [#8763](https://github.com/leanprover/lean4/pull/8763) 修正了互递归
  `partial_fixpoint` 定义中显式 `monotonicity` 证明的处理方式。

* [#8773](https://github.com/leanprover/lean4/pull/8773) 在有序模中实现了对异构
  `(k : Nat) * (a : R)` 的支持。例如：
  ```lean
  variable (R : Type u) [IntModule R] [LinearOrder R] [IntModule.IsOrdered R]

* [#8774](https://github.com/leanprover/lean4/pull/8774) 增加了一个用于禁用 `grind`
  中 cutsat 过程的选项。此时 linarith 模块会接管线性整数/自然数约束。例如：

  ```lean
  set_option trace.grind.cutsat.assert true in -- cutsat should **not** process the following constraints
  example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) : ¬ 12*y - 4* z < 0 := by
    grind -cutsat -- `linarith` module solves it
  ```

* [#8775](https://github.com/leanprover/lean4/pull/8775) 为 `Int.negSucc` 增加了一条
  `grind` 规范化定理。例如：

  ```lean
  example (p : Int) (n : Nat) (hmp : Int.negSucc (n + 1) + 1 = p)
      (hnm : Int.negSucc (n + 1 + 1) + 1 = Int.negSucc (n + 1)) : p = Int.negSucc n := by
    grind
  ```

* [#8776](https://github.com/leanprover/lean4/pull/8776) 确保用户提供的 `natCast`
  应用在 grind 的 cutsat 模块中会被正确内部化。

* [#8777](https://github.com/leanprover/lean4/pull/8777) 在 `grind` 的交换环模块中
  实现了基础的 `Field` 支持。目前只支持按数字做除法。示例如下：
  ```lean
  open Lean Grind

* [#8780](https://github.com/leanprover/lean4/pull/8780) 让 Lean 代码生成遵从
  通过 `lean --setup` 提供的模块名。

* [#8786](https://github.com/leanprover/lean4/pull/8786) 改进了 `grind` 对域的支持。
  现在支持的新示例如下：
  ```lean
  example [Field α] [IsCharP α 0] (x : α) : x ≠ 0 → (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by grind
  example [Field α] (a : α) : 2 * a ≠ 0 → 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] [IsCharP α 0] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] [IsCharP α 0] (a b : α) : 2*b - a = a + b → 1 / a + 1 / (2 * a) = 3 / b := by grind
  example [Field α] [NoNatZeroDivisors α] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] {x y z w : α} : x / y = z / w → y ≠ 0 → w ≠ 0 → x * w = z * y := by grind
  example [Field α] (a : α) : a = 0 → a ≠ 1 := by grind
  example [Field α] (a : α) : a = 0 → a ≠ 1 - a := by grind
  ```

* [#8789](https://github.com/leanprover/lean4/pull/8789) 在 `grind` 中为 `Field`
  的不相等约束实现了 Rabinowitsch 变换。例如，要解决下面这个问题，
  就需要这一变换：
  ```lean
  example [Field α] (a : α) : a^2 = 0 → a = 0 := by
    grind
  ```

* [#8791](https://github.com/leanprover/lean4/pull/8791) 确保对任何仅实现了
  `IntModule` 的类型，`grind linarith` 模块都会被激活。也就是说，
  该类型不再需要是 preorder。

* [#8792](https://github.com/leanprover/lean4/pull/8792) 让 `clear_value` 策略
  保持局部上下文中变量的顺序。其做法是新增
  `Lean.MVarId.withRevertedFrom`，它会从给定变量开始回退所有局部变量，
  而不是只回退依赖于它的那些变量。

* [#8794](https://github.com/leanprover/lean4/pull/8794) 增加了模块
  `Lean.Util.CollectLooseBVars`，其中包含函数
  `Expr.collectLooseBVars`，用于收集表达式中的自由绑定变量集合。
  也就是说，它会计算所有满足 `e.hasLooseBVar i` 为真的 `i` 的集合。

* [#8795](https://github.com/leanprover/lean4/pull/8795) 确保辅助项不会被 ring 与
  linarith 模块内部化。

* [#8796](https://github.com/leanprover/lean4/pull/8796) 修复了 `grind linarith` 中
  项的内部化以及对 `HSMul` 的支持。

* [#8798](https://github.com/leanprover/lean4/pull/8798) 增加了如下实例
  ```
  instance [Field α] [LinearOrder α] [Ring.IsOrdered α] : IsCharP α 0
  ```
  目的是确保我们的测试套件中不会进行不必要的分支拆分。

* [#8804](https://github.com/leanprover/lean4/pull/8804) 在精译器中实现了对
  非依赖 let 表达式的一等支持。回忆一下，若 `fun x : t => b` 能通过类型检查，
  则 let 表达式 `let x : t := v; b` 被称为*非依赖*，其对应记法是
  `have x := v; b`。此前我们用 `letFun` 函数来编码 `have`，
  现在则改用 `Expr.letE` 构造子中的 nondep 标志来编码。
  这一能力已经在元编程接口与精译器中得到完整支持。元编程接口中的关键变化如下：
  - 在局部上下文中，带 `nondep := true` 的 `ldecl` 通常会被当作
    `cdecl` 处理。这是因为在 `have` 表达式的函数体中，该变量是 opaque 的。
    像 `LocalDecl.isLet` 这样的函数，默认会对非依赖 `ldecl`
    返回 `false`。在少数确有需要的情况下，如果变量正在一个其值相关的上下文中被处理，
    可以通过额外的可选参数 `allowNondep : Bool`（默认 `false`）来放宽。
  - `mkLetFVars` 等函数默认会将非依赖 let 变量泛化并为其创建 lambda 表达式。
    如果希望生成 `have` 表达式，则可将 `generalizeNondepLet`
    标志（默认值为 true）设为 false。**破坏性变更：**
    使用 `letLambdaTelescope`/`mkLetFVars` 时需要设置
    `generalizeNondepLet := false`。见下一条。
  - 现在新增了一些映射函数，使 telescope 操作更方便。参见
    `mapLetTelescope` 和 `mapLambdaLetTelescope`。
    还新增了 `mapLetDecl`，作为 `withLetDecl` 的对应物，用于创建
    `let`/`have` 表达式。
  - 关于 `generalizeNondepLet` 标志，一个重要说明是：它只应当用于
    元程序“拥有”的局部上下文变量。由于非依赖 let 变量在大多数情况下会被当作常量处理，
    `value` 字段可能引用一些已不存在的变量，例如这些变量被清除或回退过。
    使用 `mapLetDecl` 总是安全的。
  - 简化器会把 let 依赖关系的计算结果缓存到 let 表达式的 `nondep` 字段中。
  - `intro` 策略仍然会生成*依赖*的局部变量。既然简化器会把 let
    转换为 have，那么如果这会阻止 `intro` 创建值无法使用的局部变量，
    反而会显得很奇怪。

* [#8809](https://github.com/leanprover/lean4/pull/8809) 为 `grind` 引入了
  Nat 上有序模（即没有减法）的基础理论。这里的问题将通过把它们嵌入
  `IntModule` 包络中来解决。

* [#8810](https://github.com/leanprover/lean4/pull/8810) 在 `grind linarith` 中实现了
  等式消去。当前实现只支持 `IntModule` 以及
  `IntModule` + `NoNatZeroDivisors`。

* [#8813](https://github.com/leanprover/lean4/pull/8813) 增加了一些关于 `grind`
  内部模概念的基础引理。

* [#8815](https://github.com/leanprover/lean4/pull/8815) 重构了 simp 参数的精译
  方式：不再是一边处理一边修改 `SimpTheorems` 结构，而是先把每个参数
  精译成对其作用的更声明式描述，再统一应用。
  这使得一些更有意思的 simp 参数检查成为可能：既包括必须在最终构造出的
  simp 上下文中进行的检查（#8688），也包括 simp 运行后才能做的检查
  （如未使用参数检查器 #8901）。

* [#8828](https://github.com/leanprover/lean4/pull/8828) 扩展了实验性模块系统，
  使其支持解析通过 `import all`（传递地）导入的私有名称。

* [#8835](https://github.com/leanprover/lean4/pull/8835) 定义了将 `CommSemiring`
  嵌入其 `CommRing` 包络中的方式；当该 `CommSemiring` 可消去时，这一嵌入是单射的。
  这将被 `grind` 用来证明 `Nat` 中的结果。

* [#8836](https://github.com/leanprover/lean4/pull/8836) 将 #8835 推广到非交换情形，
  使我们可以把 `Lean.Grind.Semiring` 嵌入到 `Lean.Grind.Ring` 中。

* [#8845](https://github.com/leanprover/lean4/pull/8845) 实现了通过反射证明来将
  semiring 项嵌入 ring 项的基础设施。

* [#8847](https://github.com/leanprover/lean4/pull/8847) 将 `Lean.Grind.IsCharP` 的假设
  从 `Ring` 放宽到 `Semiring`，并为环提供了一个替代构造子。

* [#8848](https://github.com/leanprover/lean4/pull/8848) 将内部 `grind` 实例
  ```
  instance [Field α] [LinearOrder α] [Ring.IsOrdered α] : IsCharP α 0
  ```
  推广为
  ```
  instance [Ring α] [Preorder α] [Ring.IsOrdered α] : IsCharP α 0
  ```

* [#8855](https://github.com/leanprover/lean4/pull/8855) 重构了
  `Lean.Grind.NatModule/IntModule/Ring.IsOrdered`。

* [#8859](https://github.com/leanprover/lean4/pull/8859) 证明了在 `IntModule` 上，
  `Lean.Grind.NatModule.IsOrdered` 与 `Lean.Grind.IntModule.IsOrdered`
  的等价性。

* [#8865](https://github.com/leanprover/lean4/pull/8865) 让 `simp` 能识别并警告当前 simp 集中
  可能导致循环的 simp 引理。每当化简因令人头疼的
  “max recursion depth” 错误而失败时，它会自动执行这一检查；
  也可以通过 `set_option linter.loopingSimpArgs true`
  让它始终执行。该检查默认未开启，因为它开销不小，
  而且可能会对实际上仍能工作的 simp 调用发出警告。

* [#8874](https://github.com/leanprover/lean4/pull/8874) 如果已经通过
  `lean --setup` 提供了模块名，就不再尝试从文件名和根目录
  （也即 `lean -R`）推算模块名。

* [#8880](https://github.com/leanprover/lean4/pull/8880) 让 `simp` 更频繁地查询自己的缓存，
  以避免重复工作。

* [#8882](https://github.com/leanprover/lean4/pull/8882) 为出现在 `grind` 证明证书中的项
  增加了 `@[expose]` 标注，从而使 `grind` 能在模块系统中使用。
  目前仍有可能尚未找全所有这类项。

* [#8890](https://github.com/leanprover/lean4/pull/8890) 为 `Lean.Grind` 的代数类型类
  增加了文档字符串，因为它们将出现在参考手册中，用于说明如何把
  `grind` 的代数求解器扩展到新类型。同时还移除了一些冗余字段。

* [#8892](https://github.com/leanprover/lean4/pull/8892) 修正了 `grind` 修饰符的美观打印。
  此前 `@[grind →]` 会被打印成 `@[grind→ ]`
  （空格跑到了符号右侧，而不是左侧）。这一改动修复了属性的美观打印，
  并保留了 `grind?` 输出中符号后空格的存在。

* [#8893](https://github.com/leanprover/lean4/pull/8893) 修复了 cutsat 中 `dvd`
  传播函数的一个缺陷。

* [#8901](https://github.com/leanprover/lean4/pull/8901) 增加了一个检查器（`linter.unusedSimpArgs`），当
  simp 参数（`simp [foo]`）未被使用时会发出提示。如果 `simp` 调用会被多次执行，
  例如位于 `all_goals` 中，它也应能做出正确判断。若 `simp` 调用位于
  宏内部，则不会触发。检查器消息中还包含可点击的提示，
  方便删除该 simp 参数。

* [#8903](https://github.com/leanprover/lean4/pull/8903) 确保局部实例缓存的计算会应用更多归约。
  在 #2199 中，曾出现元变量会阻止局部变量被视为局部实例的问题。
  这里采用了稍有不同的方法，确保例如 telescope 末端的 `let`
  不会引发类似问题。这些归约本来就在计算，因此不需要额外工作量。

* [#8909](https://github.com/leanprover/lean4/pull/8909) 重构了 `NoNatZeroDivisors`，
  以确保它能与新的 `Semiring` 支持配合工作。

* [#8910](https://github.com/leanprover/lean4/pull/8910) 为 `OfSemiring.Q α` 增加了
  `NoNatZeroDivisors` 实例。

* [#8913](https://github.com/leanprover/lean4/pull/8913) 清理了 `grind` 内部的顺序类型类，
  移除了不必要的重复。

* [#8914](https://github.com/leanprover/lean4/pull/8914) 修改了 `let` 与 `have` 的项语法，
  使二者保持一致。新增了配置选项；例如，对于*非依赖* let，
  `have` 等价于 `let +nondep`。其他选项包括 `+usedOnly`
  （用于 `let_tmp`）、`+zeta`（用于 `letI`/`haveI`）和
  `+postponeValue`（用于 `let_delayed`）。此外还支持
  `let (eq := h) x := v; b`，用于在精译 `b` 时引入
  `h : x = v`。`eq` 选项同样适用于模式匹配，例如
  `let (eq := h) (x, y) := p; b`。

* [#8918](https://github.com/leanprover/lean4/pull/8918) 修复了 `guard_msgs.diff`
  的默认行为，使选项定义中声明的默认值在所有地方都真正生效。

* [#8921](https://github.com/leanprover/lean4/pull/8921) 在 `grind` 中实现了对（交换）
  半环的支持。它使用 Grothendieck 完备化，从（交换）semiring `α`
  构造出（交换）环 `Lean.Grind.Ring.OfSemiring.Q α`。这一构造主要对实现了
  `AddRightCancel α` 的 semiring 有用；否则 `toQ` 函数并非单射。
  例如：
  ```lean
  example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
    grind

* [#8935](https://github.com/leanprover/lean4/pull/8935) 为 `let` 与 `have` 语法增加了
  `+generalize` 选项。例如，`have +generalize n := a + b; body`
  会在精译 `body` 时，把期望类型中所有 `a + b` 的出现都替换为 `n`。
  这可以看作 `generalize` 策略的项级版本。还可以把它与 `eq` 结合，
  写成 `have +generalize (eq := h) n := a + b; body`，对应于
  `generalize h : n = a + b`。

* [#8937](https://github.com/leanprover/lean4/pull/8937) 修改了为非反身归纳类型生成的
  `below` 实现的输出宇宙层级，使其与 #7639 中反身归纳类型的实现一致。

* [#8940](https://github.com/leanprover/lean4/pull/8940) 引入了反单调性引理，
  用于支持使用 `least_fixpoint` / `greatest_fixpoint` 构造定义的
  混合归纳-余归纳谓词的精译。

* [#8943](https://github.com/leanprover/lean4/pull/8943) 为不实现 `AddRightCancel`
  的 semiring 增加了规范化辅助定理。

* [#8953](https://github.com/leanprover/lean4/pull/8953) 为不实现 `AddRightCancel`
  的交换 semiring 实现了规范化支持。示例如下：
  ```lean
  variable (R : Type u) [CommSemiring R]

* [#8954](https://github.com/leanprover/lean4/pull/8954) 增加了一个高效地将 `let`
  表达式转换为 `have` 表达式的过程（`Meta.letToHave`）。
  这一过程以 `let_to_have` 策略的形式对外暴露。

* [#8955](https://github.com/leanprover/lean4/pull/8955) 修复了
  `Lean.MVarId.deltaLocalDecl`，此前它会用目标替换局部定义。

* [#8957](https://github.com/leanprover/lean4/pull/8957) 为 `let`/`have` 策略语法
  增加了配置选项。例如，`let (eq := h) x := v` 会把 `h : x = v`
  加入局部上下文。这些配置选项与 `let`/`have` 项语法中的一致。

* [#8958](https://github.com/leanprover/lean4/pull/8958) 改进了 `grind` 使用的
  分支拆分策略，并确保 `grind` 也会把简单的 `match` 条件纳入
  分支拆分考量。例如：

  ```lean
  example (x y : Nat)
      : 0 < match x, y with
            | 0, 0   => 1
            | _, _ => x + y := by -- x or y must be greater than 0
    grind
  ```

* [#8959](https://github.com/leanprover/lean4/pull/8959) 增加了实例，用来说明：
  若原半环有序（且满足 ExistsAddOfLE），则它的 Grothendieck
  （即加法）包络是一个有序环，并且在这种情况下嵌入是单调的。

* [#8963](https://github.com/leanprover/lean4/pull/8963) 将 NatModule 嵌入到它的
  IntModule 完备化中；当具备 AddLeftCancel 时，这一嵌入是单射的，
  当模块有序时，它是单调的。还增加了一些（当前失败的）grind 测试用例，
  待 `grind` 使用这一嵌入后即可验证。

* [#8964](https://github.com/leanprover/lean4/pull/8964) 为 `grind` 构造、且需要在
  内核中求值的证明项增加了 `@[expose]` 属性。

* [#8965](https://github.com/leanprover/lean4/pull/8965) 修订了 Nat 按位运算上的
  @[grind] 标注。

* [#8968](https://github.com/leanprover/lean4/pull/8968) 为 `simp` 增加了以下特性：
  - 一种化简 `have` telescope 的例程，可避免局部无名表达式表示带来的
    二次复杂度，类似 #6220 对 `letFun` telescope 所做的工作。
    此外，simp 现在会把 `letFun` 转换为 `have`（非依赖 let），
    而我们也删除了 #6220 的那套例程，因为正逐步摆脱用 `letFun`
    来编码非依赖 let 的方式。
  - `+letToHave` 配置选项（默认启用）：当设置了 `-zeta` 时，
    会在可能时把 `let` 转换成 `have`。此前 Lean 需要对 let 的函数体做完整类型检查，
    但 `letToHave` 过程可以跳过某些子表达式的检查，并且会一次性修改
    整个表达式中的 let，而不是逐个修改。
  - `+zetaHave` 配置选项：专门关闭对 `have` 的 zeta 归约。
    其动机在于，依赖 `let` 只能通过 `let` 的方式做 `dsimp`，因此仅对依赖 let
    做 zeta 归约是一种合理的推进方式。`+zetaHave` 也被加入了元配置。
  - 当 `simp` 执行 zeta 归约时，现在使用的算法可避免 `let` 望远镜深度带来的
    二次复杂度。
  - 此外，`simp`、`whnf` 和 `isDefEq` 中的 zeta 归约例程，现在在应用
    `zeta`、`zetaHave` 和 `zetaUnused` 配置时彼此保持一致。

* [#8971](https://github.com/leanprover/lean4/pull/8971) 修复了
  `linter.simpUnusedSimpArgs`，使其会检查语法种类，从而不会对
  宏背后的 `simp` 调用误报。修复了 #8969。

* [#8973](https://github.com/leanprover/lean4/pull/8973) 重构了线性
  `noConfusionType` 构造中对宇宙层级的处理：不再使用 `PUnit.{…} → `
  来把 `withCtorType` 的各个分支拉到同一宇宙层级，而是改用 `PULift`。

* [#8978](https://github.com/leanprover/lean4/pull/8978) 更新了 `monotonicity`
  策略所用的 `solveMonoStep` 函数，使其检查当前目标与递归调用得到的
  单调性证明之间是否定义相等。这样能在 `Lean.Order.PartialOrder`
  实例不同时阻止错误应用，从而保证健全性——这一问题可能出现在使用
  `partial_fixpoint` 关键字定义的 `mutual` 块中，因为其中可能涉及不同的
  `Lean.Order.CCPO` 结构。

* [#8980](https://github.com/leanprover/lean4/pull/8980) 通过把若干现有错误消息的附加说明
  渲染为带标签的注释与提示，提升了错误消息格式的一致性。

* [#8983](https://github.com/leanprover/lean4/pull/8983) 修复了 `grind` 在对过量应用函数
  生成同余证明时的一个缺陷。

* [#8986](https://github.com/leanprover/lean4/pull/8986) 改进了非法投影与字段记法产生的错误消息。
  它还在 “function expected” 错误消息中增加了一个提示，指出该项正被应用到哪个参数上，
  这有助于排查那些实际上由语法错误引起的伪 “function expected” 报错。

* [#8991](https://github.com/leanprover/lean4/pull/8991) 为 `grind` 补充了一些缺失的
  `ToInt.X` 类型类实例。

* [#8995](https://github.com/leanprover/lean4/pull/8995) 在 `Std.Do.Triple` 中为单子程序
  引入了 Hoare 逻辑，并配套提供若干策略：

  * `mspec`，用于应用 Hoare 三元组规格；
  * `mvcgen`，用于将 Hoare 三元组证明义务 `⦃P⦄ prog ⦃Q⦄`
    转换为纯验证条件（也就是不再残留 Hoare 三元组或类似 `prog` 的最弱前置条件痕迹）。
    得到的验证条件位于 `Std.Do.SPred` 的有状态逻辑中，
    可以手动用其自定义证明模式附带的策略解决，
    也可以借助 `simp`、`grind` 等自动化手段处理。

* [#8996](https://github.com/leanprover/lean4/pull/8996) 补齐了 `Lean.Grind.ToInt`
  类型类剩余的实例。

* [#9004](https://github.com/leanprover/lean4/pull/9004) 确保插值字符串中的类型类合成失败错误
  会显示在实际出错的插值位置上。

* [#9005](https://github.com/leanprover/lean4/pull/9005) 修改了 `Lean.Grind.ToInt.OfNat`
  的定义，在右侧引入了一个 `wrap`。

* [#9008](https://github.com/leanprover/lean4/pull/9008) 为 `cutsat` 中通用 `ToInt`
  支持实现了基础设施。

* [#9022](https://github.com/leanprover/lean4/pull/9022) 补全了通用 `toInt`
  基础设施，用于将实现了 `ToInt` 类型类的项嵌入到 `Int` 中。

* [#9026](https://github.com/leanprover/lean4/pull/9026) 在 `grind cutsat` 中实现了对
  （非严格）`ToInt` 不等式的支持。`grind cutsat` 已可解决如下简单问题：
  ```lean
  example (a b c : Fin 11) : a ≤ b → b ≤ c → a ≤ c := by
    grind

* [#9030](https://github.com/leanprover/lean4/pull/9030) 修复了新加入的 `Std.Do`
  模块中几个与 bootstrap 有关的小故障。更具体地说，

* [#9035](https://github.com/leanprover/lean4/pull/9035) 扩展了可接受字符列表，
  纳入了所有法语字符以及一些其他字符，具体做法是加入
  Latin-1-Supplement 与 Latin-Extended-A Unicode 块中的字符。

* [#9038](https://github.com/leanprover/lean4/pull/9038) 为 VC 生成器增加了测试用例，
  并做了若干细小但繁琐的修复，以确保测试通过。

* [#9041](https://github.com/leanprover/lean4/pull/9041) 让 `mspec` 能通过 `rfl`
  检测到更多可行赋值，而不是生成 VC。

* [#9044](https://github.com/leanprover/lean4/pull/9044) 调整了实验性模块系统，
  使 `module` 中默认可见性修饰符变为 `private`，并相应引入新的 `public`
  修饰符。可以使用 `public section` 为整个 section 恢复旧默认值，
  不过这主要是为了方便逐步采纳新语义，例如在 `Init`（以及很快的 `Std`）中，
  之后仍应通过逐声明重新审查可见性来取代这种过渡手段。

* [#9045](https://github.com/leanprover/lean4/pull/9045) 修复了 `mvcgen` 中的一个类型错误，
  并减少了它把自然目标转成 synthetic opaque 目标的数量，
  使得 `trivial` 等策略更容易对其进行实例化。

* [#9048](https://github.com/leanprover/lean4/pull/9048) 为 `grind cutsat` 所用的
  `ToInt` 适配器实现了对严格不等式的支持。例如：
  ```lean
  example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b < c → a < c + 1 := by
    grind
  ```

* [#9050](https://github.com/leanprover/lean4/pull/9050) 确保在 `grind cutsat`
  中，每个被内部化的 `toInt a` 应用都会附带其 `ToInt` 边界断言。

* [#9051](https://github.com/leanprover/lean4/pull/9051) 在 `grind cutsat` 中实现了对
  等式与不相等约束的支持。编码方式仍有待改进。示例如下：
  ```lean
  example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
    grind

* [#9057](https://github.com/leanprover/lean4/pull/9057) 为 `cutsat` 引入了一个简单的
  变量重排启发式。`ToInt` 适配器需要它来支持诸如 `UInt64`
  这样的有限类型。当前嵌入 `Int` 的编码会产生较大的系数，
  在变量顺序不佳时会扩大搜索空间。例如：
  ```lean
  example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
    grind
  ```

* [#9059](https://github.com/leanprover/lean4/pull/9059) 为未知特征的环中系数规范化
  增加了辅助定理。

* [#9062](https://github.com/leanprover/lean4/pull/9062) 在未知特征的环与域中，
  实现了对 `<num> = 0` 这类方程的支持。示例如下：
  ```lean
  example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind

* [#9065](https://github.com/leanprover/lean4/pull/9065) 改进了在使用 `ToInt` 辅助机制时，
  `grind` 中 `cutsat` 过程产生的反例。

* [#9067](https://github.com/leanprover/lean4/pull/9067) 为 `grind` 策略增加了文档字符串。

* [#9069](https://github.com/leanprover/lean4/pull/9069) 实现了对类型类 `LawfulEqCmp`
  的支持。示例如下：
  ```lean
  example (a b c : Vector (List Nat) n)
      : b = c → a.compareLex (List.compareLex compare) b = o → o = .eq → a = c := by
    grind

* [#9073](https://github.com/leanprover/lean4/pull/9073) 参照 #9069 同样处理了 `ReflCmp`；
  我们需要在 propagateUp 而非 propagateDown 中调用它。

* [#9074](https://github.com/leanprover/lean4/pull/9074) 使用交换环模块来规范化
  `grind cutsat` 中的非线性多项式。示例如下：
  ```lean
  example (a b : Nat) (h₁ : a + 1 ≠ a * b * a) (h₂ : a * a * b ≤ a + 1) : b * a^2 < a + 1 := by
    grind

* [#9076](https://github.com/leanprover/lean4/pull/9076) 为 `OfSemiring.toQ` 增加了
  unexpander。它是 `grind` 中 `ring` 模块使用的辅助函数，
  但我们希望减少 `grind` 诊断信息中的杂乱程度。例如：
  ```
  example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y : α)
      : x^2*y = 1 → x*y^2 = y → x + y = 2 → False := by
    grind
  ```
  会产生
  ```
    [ring] Ring `Ring.OfSemiring.Q α` ▼
      [basis] Basis ▼
        [_] ↑x + ↑y + -2 = 0
        [_] ↑y + -1 = 0
  ```

* [#9086](https://github.com/leanprover/lean4/pull/9086) 弃用了 `let_fun` 语法，改用 `have`，
  并从 WHNF 与 `simp` 中移除了对 `letFun` 的支持。

* [#9087](https://github.com/leanprover/lean4/pull/9087) 从 `letFun` 上移除了
  `irreducible` 属性，这是移除专门 `letFun` 支持的步骤之一；属于 #9086 的一部分。

````
````markdown

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Library"
%%%

````markdown

* [#8003](https://github.com/leanprover/lean4/pull/8003) 为 `Async` 操作增加了新的单子化接口。

* [#8072](https://github.com/leanprover/lean4/pull/8072) 在标准库中增加了 DNS 函数。

* [#8109](https://github.com/leanprover/lean4/pull/8109) 在标准库中增加了系统信息函数。

* [#8178](https://github.com/leanprover/lean4/pull/8178) 为 sdiv 的 MSB 给出了一个紧凑公式。
  该 PR 的大部分工作都在处理除法溢出的边界情形
  （例如 `intMin / -1 = intMin`）。

* [#8203](https://github.com/leanprover/lean4/pull/8203) 为无符号和有符号比较增加了三歧性引理，
  断言三种情形中只会发生一种：`x < y`、`x = y` 或 `x > y`
  （对有符号和无符号比较都成立）。这里使用显式参数，
  使用户可以写 `rcases slt_trichotomy x y with hlt | heq | hgt`。

* [#8205](https://github.com/leanprover/lean4/pull/8205) 增加了一条 simp 引理，
  可将分子为 `Nat` 的 T-division 化简为 E-division：


  ```lean
  @[simp] theorem ofNat_tdiv_eq_ediv {a : Nat} {b : Int} : (a : Int).tdiv b = a / b :=
     tdiv_eq_ediv_of_nonneg (by simp)
  ```

* [#8210](https://github.com/leanprover/lean4/pull/8210) 为 tree map 增加了一种
  类似于现有 哈希表上的等价关系的关系。为了最终得到大量可用于在外延树映射
  上定义函数的同余引理，几乎所有剩余的 树映射函数也都补充了与 列表函数对应的引理，
  尽管这些引理目前除了同余引理外还未用于证明其他内容。

* [#8253](https://github.com/leanprover/lean4/pull/8253) 增加了 `toInt_smod`
  及其证明所需的辅助引理
  (`msb_intMin_umod_neg_of_msb_true`,
  `msb_neg_umod_neg_of_msb_true_of_msb_true`, `toInt_dvd_toInt_iff`,
  `toInt_dvd_toInt_iff_of_msb_true_msb_false`,
  `toInt_dvd_toInt_iff_of_msb_false_msb_true`,
  `neg_toInt_neg_umod_eq_of_msb_true_msb_true`, `toNat_pos_of_ne_zero`,
  `toInt_umod_neg_add`、`toInt_sub_neg_umod` 以及
  `BitVec.[lt_of_msb_false_of_msb_true, msb_umod_of_msb_false_of_ne_zero`,
  `neg_toInt_neg]`)

* [#8420](https://github.com/leanprover/lean4/pull/8420) 提供了迭代器组合子 `drop`，
  可将任意迭代器变为跳过前 `n` 个元素的迭代器。

* [#8534](https://github.com/leanprover/lean4/pull/8534) 修复了 Windows 上的
  `IO.FS.realPath`，使其会考虑符号链接。

* [#8545](https://github.com/leanprover/lean4/pull/8545) 提供了推理“等价”迭代器的手段。
  简单来说，只要消费者不去窥探其状态，两个迭代器的行为相同，它们就是等价的。

* [#8546](https://github.com/leanprover/lean4/pull/8546) 增加了新的 `BitVec.clz` 运算，
  并为 `bv_decide` 增加了对应的 `clz` 电路，从而可以对“前导零计数”操作做 bitblast。
  该 AIG 电路相对于原表达式的位数是线性的，因此在重写语境下做 bitblast 也很方便。
  `clz` 在许多编译器内建中都很常见（见
  [here](https://clang.llvm.org/docs/LanguageExtensions.html#intrinsics-support-within-constant-expressions))
  ）以及各种体系结构中（见
  [here](https://en.wikipedia.org/wiki/Find_first_set)).

* [#8573](https://github.com/leanprover/lean4/pull/8573) 避免了 `removeDirAll`
  穿过符号链接删除内容这一大概率令人意外的行为，并新增函数
  `IO.FS.symlinkMetadata`。

* [#8585](https://github.com/leanprover/lean4/pull/8585) 通过更频繁地使用“简单情形”，
  让引理 `BitVec.extractLsb'_append_eq_ite` 更易用，并利用这一简化加强了
  `BitVec.extractLsb'_append_eq_of_add_lt`，将其重命名为
  `BitVec.extractLsb'_append_eq_of_add_le`。

* [#8587](https://github.com/leanprover/lean4/pull/8587) 调整了
  `Std.HashMap.map_fst_toList_eq_keys` 及其变体上的 grind 标注，
  使 `grind` 能在 `m.keys` 与 `m.toList` 之间做双向推理。

* [#8590](https://github.com/leanprover/lean4/pull/8590) 为 `getElem?_pos` 及其变体
  增加了 `@[grind]` 标注。

* [#8615](https://github.com/leanprover/lean4/pull/8615) 提供了一个专门的空迭代器类型。
  尽管这种行为也可例如用列表迭代器来模拟，但专门的类型更利于编译器优化。

* [#8620](https://github.com/leanprover/lean4/pull/8620) 移除了 `NatCast (Fin n)` 的全局实例
  （包括直接实例以及经由 `Lean.Grind.Semiring` 的间接实例），因为该实例会使
  `x < n`（其中 `x : Fin k`、`n : Nat`）被精译为
  `x < ↑n` 而不是 `↑x < n`，这并不理想。不过需要注意，
  在 Mathlib 中这仍然会发生！

* [#8629](https://github.com/leanprover/lean4/pull/8629) 用经过验证的默认实现替换了那些
  特殊优化版的 `IteratorLoop` 实例，因为它们并未给出 lawfulness 证明。
  循环/收集实现的特化优先级较低，但为为所有迭代器提供合法性实例
  对验证工作很重要。

* [#8631](https://github.com/leanprover/lean4/pull/8631) 泛化了
  `Std.Sat.AIG. relabel(Nat)_unsat_iff`，使 AIG 类型可以为空。
  证明的泛化方式是：说明当 `α` 为空时，环境其实无关紧要，
  因为所有 `α → Bool` 环境彼此同构。

* [#8640](https://github.com/leanprover/lean4/pull/8640) 将 `BitVec.setWidth'_eq`
  加入 `bv_normalize`，从而让 `bv_decide` 能对其做归约，并证明涉及
  `setWidth'_eq` 的引理。

* [#8669](https://github.com/leanprover/lean4/pull/8669) 将 `unsafeBaseIO` 设为 `noinline`。
  新编译器更擅长优化 `Result` 一类的类型，这可能导致 `unsafeBaseIO`
  代码块中的最后一个操作被删掉，因为 `unsafeBaseIO` 会丢弃状态。

* [#8678](https://github.com/leanprover/lean4/pull/8678) 让 `isSome_finIdxOf?` 和
  `isNone_finIdxOf?` 的左侧更一般化。

* [#8703](https://github.com/leanprover/lean4/pull/8703) 修正了 `DropWhile` 中的
  `IteratorLoop` 实例，此前它会对任意迭代器类型触发。

* [#8719](https://github.com/leanprover/lean4/pull/8719) 为
  List/Array/Vector.eraseP/erase/eraseIdx 增加了 grind 标注，
  并补充了一些缺失引理。

* [#8721](https://github.com/leanprover/lean4/pull/8721) 增加了外延树映射 / set 类型
  `Std.ExtDTreeMap`、`Std.ExtTreeMap` 和 `Std.ExtTreeSet`。
  它们在构造上与现有外延 hash map 很相似，但有一个例外：
  外延树映射 / set 提供普通树映射/集合 的全部函数。
  这之所以可行，是因为与哈希表不同，树映射 始终是有序的。

* [#8734](https://github.com/leanprover/lean4/pull/8734) 增加了缺失的实例
  ```
  instance decidableExistsFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ i, P i)
  ```

* [#8740](https://github.com/leanprover/lean4/pull/8740) 引入了结合律规则，
  以及对 `(umul, smul, uadd, sadd)Overflow` 标志的保持性质。

* [#8741](https://github.com/leanprover/lean4/pull/8741) 为
  `List/Array/Vector.find?/findSome?/idxOf?/findIdx?` 增加了标注。

* [#8742](https://github.com/leanprover/lean4/pull/8742) 修复了一个缺陷：单引号字符
  `Char.ofNat 39` 会被反展开为 `'''`，若把它粘回源码中就会导致解析错误。

* [#8745](https://github.com/leanprover/lean4/pull/8745) 在 `Std.Do` 中增加了有状态谓词逻辑
  `SPred`，用于支持对单子程序进行推理。它附带一个专用证明模式，
  其策略可通过导入 `Std.Tactic.Do` 使用。

* [#8747](https://github.com/leanprover/lean4/pull/8747) 为 List/Array/Vector.finRange
  的定理增加了 grind 标注。

* [#8748](https://github.com/leanprover/lean4/pull/8748) 为 `Array/Vector.mapIdx`
  和 `mapFinIdx` 定理增加了 grind 标注。

* [#8749](https://github.com/leanprover/lean4/pull/8749) 为 `List/Array/Vector.ofFn`
  定理以及额外的 `List.Impl` 查找操作增加了 grind 标注。

* [#8750](https://github.com/leanprover/lean4/pull/8750) 为
  `List/Array/Vector.zipWith/zipWithAll/unzip` 函数增加了 grind 标注。

* [#8765](https://github.com/leanprover/lean4/pull/8765) 为 `List.Perm`
  增加了 grind 标注；同时也修订了 `List.countP/count` 上的 grind 标注。

* [#8768](https://github.com/leanprover/lean4/pull/8768) 以最小形式为迭代器引入了
  `ForIn'` 实例与 `size` 函数。`ForIn'` 并未被标记为 instance，
  因为目前尚不清楚哪种 `Membership` 关系足够有用。随着 `ForIn'`
  作为 `def` 存在并诱导出 `ForIn` 实例，未来就能为不同类型的迭代器提供
  更专门的 `ForIn'` 实例以及更合适的 `Membership` 关系。`size` 目前还没有引理。

* [#8784](https://github.com/leanprover/lean4/pull/8784) 引入了多态范围，
  与仅支持自然数的现有 `Std.Range` 相对。

* [#8805](https://github.com/leanprover/lean4/pull/8805) 继续为 `List/Array/Vector`
  的引理补充 `grind` 标注。

* [#8808](https://github.com/leanprover/lean4/pull/8808) 补充了缺失的
  `le_of_add_left_le {n m k : Nat} (h : k + n ≤ m) : n ≤ m`
  和 `le_add_left_of_le {n m k : Nat} (h : n ≤ m) : n ≤ k + m`。

* [#8811](https://github.com/leanprover/lean4/pull/8811) 增加了定理
  `BitVec.(toNat, toInt, toFin)_shiftLeftZeroExtend`，
  从而补全了 `BitVec.shiftLeftZeroExtend` 的 API。

* [#8826](https://github.com/leanprover/lean4/pull/8826) 修正了 `Lean.Grind.NatModule`
  的定义；此前它实际上并不好用。

* [#8827](https://github.com/leanprover/lean4/pull/8827) 将 `BitVec.getLsb'`
  重命名为 `BitVec.getLsb`，因为此前占用该名称的旧弃用定义已经移除。
  （`BitVec.getMsb'` 也做了类似处理。）

* [#8829](https://github.com/leanprover/lean4/pull/8829) 避免将整个
  `BitVec.Lemmas` 与 `BitVec.BitBlast` 导入到 `UInt.Lemmas` 中。
  （它们仍会导入到 `SInt.Lemmas`；这似乎更难避免。）

* [#8830](https://github.com/leanprover/lean4/pull/8830) 重新整理了 `Init.Grind`
  下的文件，把具体代数类型的实例移到 `Init.GrindInstances` 中。

* [#8849](https://github.com/leanprover/lean4/pull/8849) 为 `Sum` 增加了 `grind` 标注。

* [#8850](https://github.com/leanprover/lean4/pull/8850) 为 `Prod` 增加了 `grind` 标注。

* [#8851](https://github.com/leanprover/lean4/pull/8851) 为 `Function.curry`/`uncurry`
  增加了 grind 标注。

* [#8852](https://github.com/leanprover/lean4/pull/8852) 为 `Nat.testBit`
  以及 `Nat` 上的按位运算增加了 grind 标注。

* [#8853](https://github.com/leanprover/lean4/pull/8853) 增加了 `grind` 标注，
  用于把 `Nat.fold/foldRev/any/all` 与 `Fin.foldl/foldr/foldlM/foldrM`
  关联到 `List.finRange` 上对应的操作。

* [#8877](https://github.com/leanprover/lean4/pull/8877) 为
  `List/Array/Vector.attach/attachWith/pmap` 增加了 grind 标注。

* [#8878](https://github.com/leanprover/lean4/pull/8878) 为 List/Array/Vector 的单子函数
  增加了 grind 标注。

* [#8886](https://github.com/leanprover/lean4/pull/8886) 增加了 `IO.FS.Stream.readToEnd`，
  与 `IO.FS.Handle.readToEnd` 对应，同时也上游同步了其依赖定义
  （即 `readBinToEndInto` 和 `readBinToEnd`）。此外还从
  `IO.FS.Handle.readBinToEnd` 中移除了一个不必要的 `partial`。

* [#8887](https://github.com/leanprover/lean4/pull/8887) 将 `IO.FS.lines` 泛化为
  `IO.FS.Handle.lines`，并为 stream 增加了对应的 `IO.FS.Stream.lines`。

* [#8897](https://github.com/leanprover/lean4/pull/8897) 简化了一些 `simp` 调用。

* [#8905](https://github.com/leanprover/lean4/pull/8905) 使用
  https://github.com/leanprover/lean4/pull/8901 中的检查器
  清理了 simp 参数。

* [#8920](https://github.com/leanprover/lean4/pull/8920) 继续使用 #8901 中的检查器
  清理更多 simp 参数，从而完成 #8905。

* [#8928](https://github.com/leanprover/lean4/pull/8928) 在 `Std.Do` 中增加了有状态谓词逻辑
  `SPred`，用于支持对单子程序进行推理。它附带一个专用证明模式，
  其策略可通过导入 Std.Tactic.Do 使用。

* [#8941](https://github.com/leanprover/lean4/pull/8941) 增加了
  `BitVec.(getElem, getLsbD, getMsbD)_(smod, sdiv, srem)` 定理，
  从而补全了 `sdiv`、`srem`、`smod` 的 API。尽管这些定理的 rhs
  并不算特别简洁（“有符号除法/模运算结果的第 n 位”本身就不太容易直观理解），
  但它们能避免必须去 `unfold` 这些操作。

* [#8947](https://github.com/leanprover/lean4/pull/8947) 以最基础的形式引入了多态切片。
  它们带有与新范围记法类似的表示法。`Subarray` 现在也属于切片，
  并且可以生成迭代器。后续计划将 `Subarray` 的更多操作迁移到 `Slice`
  包装类型中，从而也能用于其他类型的切片。

* [#8950](https://github.com/leanprover/lean4/pull/8950) 增加了 `BitVec.toFin_(sdiv, smod, srem)`
  以及 `BitVec.toNat_srem`。`toFin_*` 引理的 `rhs` 策略是参考对应的
  `toNat_*` 定理，并把 `toFin` 尽量推近操作数。至于 `BitVec.toNat_srem`
  的 `rhs`，则采用了与 `BitVec.toNat_smod` 相同的策略。

* [#8967](https://github.com/leanprover/lean4/pull/8967) 一方面为 `BitVec` 增加了首批
  `@[grind]` 标注，另一方面也用 `grind` 删除了 `BitVec/Lemmas`
  中大量原有证明。

* [#8974](https://github.com/leanprover/lean4/pull/8974) 增加了 `BitVec.msb_(smod, srem)`。

* [#8977](https://github.com/leanprover/lean4/pull/8977) 增加了通用的
  `MonadLiftT Id m` 实例。我们没有实现 `MonadLift Id m` 实例，
  因为那会拖慢实例解析，并产生更多非典范实例。这一改动使得在任意单子中
  遍历纯迭代器（例如 `[1, 2, 3].iter`）成为可能。

* [#8992](https://github.com/leanprover/lean4/pull/8992) 增加了 `PULift`，
  它是比 `ULift` 和 `PLift` 更一般的形式，并将两者统一其中。

* [#8995](https://github.com/leanprover/lean4/pull/8995) 在 `Std.Do.Triple` 中为单子程序
  引入了 Hoare 逻辑，并配套提供若干策略：

  * `mspec`，用于应用 Hoare 三元组规格；
  * `mvcgen`，用于将 Hoare 三元组证明义务 `⦃P⦄ prog ⦃Q⦄`
    转换为纯验证条件（也就是不再残留 Hoare 三元组或类似 `prog` 的最弱前置条件痕迹）。
    得到的验证条件位于 `Std.Do.SPred` 的有状态逻辑中，
    可以手动用其自定义证明模式附带的策略解决，
    也可以借助 `simp`、`grind` 等自动化手段处理。

* [#9027](https://github.com/leanprover/lean4/pull/9027) 提供了一个迭代器组合子，
  可通过 `ULift` 将发出的值提升到更高的宇宙层级。随后利用这一组合子，
  使 subarray 迭代器成为宇宙多态。此前它们只对 `α : Type`
  的 `Subarray α` 可用。

* [#9030](https://github.com/leanprover/lean4/pull/9030) 修复了新加入的 `Std.Do`
  模块中几个与 bootstrap 有关的小故障。更具体地说，

* [#9038](https://github.com/leanprover/lean4/pull/9038) 为 VC 生成器增加了测试用例，
  并做了若干细小但繁琐的修复，以确保测试通过。

* [#9049](https://github.com/leanprover/lean4/pull/9049) 证明了切片上默认的
  `toList`、`toListRev` 和 `toArray` 函数都可用切片迭代器来描述。
  借助 `uLift` 与 `attachWith` 迭代器组合子的新引理，
  还为 `Subarray` 给出了这些函数的更具体描述。

* [#9054](https://github.com/leanprover/lean4/pull/9054) 修正了 `TreeMap`/`HashMap`
  上一些 grind 标注的不一致之处，涉及 `isSome_get?_eq_contains`
  和 `empty_eq_emptyc`。

* [#9055](https://github.com/leanprover/lean4/pull/9055) 将
  `Array/Vector.extract_push` 重命名为 `extract_push_of_le`，
  并用一条没有 side condition 的引理替换原引理。

* [#9058](https://github.com/leanprover/lean4/pull/9058) 为切片提供了 `ToStream`
  实例，使其可用于 `for i in xs, j in ys do` 记法。

* [#9075](https://github.com/leanprover/lean4/pull/9075) 为 `ByteArray` 和 `FloatArray`
  增加了 `BEq` 实例（`ByteArray` 还额外有 `DecidableEq` 实例）。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Compiler"
%%%

````markdown

* [#8594](https://github.com/leanprover/lean4/pull/8594) 从旧编译器中移除了对
  strictOr/strictAnd 的错误优化，并删除了一个错误的测试。要正确实现这些优化，
  需要依赖非终止分析。严格来说，表达这类优化的正确方式，
  应当是把 strictOr/strictAnd 的实现暴露给编译器中一个感知非终止性的阶段，
  然后让它们作为更一般变换的推论出现。

* [#8595](https://github.com/leanprover/lean4/pull/8595) 将对新编译器的调用包裹在
  `withoutExporting` 中。旧编译器不需要这样做，因为它对内核环境的访问更直接。

* [#8602](https://github.com/leanprover/lean4/pull/8602) 为新编译器增加了对 `Eq.recOn`
  的支持（旧编译器本就支持，只是缺少测试）。

* [#8604](https://github.com/leanprover/lean4/pull/8604) 为新编译器增加了对
  `compiler.extract_closed` 选项的支持，因为 `unsafeBaseIO`
  的定义会用到它。等我们切换到新编译器后，还会重新审视它与 IO 的关系。

* [#8614](https://github.com/leanprover/lean4/pull/8614) 在新编译器中为 `toNat`
  实现了常量折叠，从而提升了与旧编译器的一致性。

* [#8616](https://github.com/leanprover/lean4/pull/8616) 为新编译器增加了 `Nat.pow`
  的常量折叠，采用与旧编译器相同的限制条件。

* [#8618](https://github.com/leanprover/lean4/pull/8618) 为 `Nat.nextPowerOfTwo`
  实现了 LCNF 常量折叠。

* [#8634](https://github.com/leanprover/lean4/pull/8634) 让 `hasTrivialStructure?`
  在构造子的类型会被擦除时返回 false，例如当它们构造的是 `Prop` 时。

* [#8636](https://github.com/leanprover/lean4/pull/8636) 增加了名为 `lean_setup_libuv`
  的函数，用于初始化所需的 LIBUV 组件。它必须放在
  `lean_initialize_runtime_module` 之外，因为正确工作需要 `argv` 和 `argc`。

* [#8647](https://github.com/leanprover/lean4/pull/8647) 提升了新编译器对投影项的
  `noncomputable` 检查精度。这里没有附带测试，因为尽管该问题是从 Mathlib
  规约出来的，旧编译器却不能正确处理规约后的测试用例。旧编译器之所以能通过
  这项检查，是否出于正确原因，目前也并不完全清楚。测试会补到新编译器分支上。

* [#8675](https://github.com/leanprover/lean4/pull/8675) 提升了新编译器
  noncomputable 检查的精度，尤其是对应用中无关位置使用
  `noncomputable` 定义的处理。

* [#8681](https://github.com/leanprover/lean4/pull/8681) 为 LCNF 化简流程 增加了一项优化：
  `cases` 构造的判别式只有在存在非默认分支时才会被标记为已使用。

* [#8683](https://github.com/leanprover/lean4/pull/8683) 为 LCNF 化简流程 增加了另一项优化：
  对只有单个分支的 cases，其判别式只有在某个参数被使用时才会被标记为已使用。

* [#8709](https://github.com/leanprover/lean4/pull/8709) 在 `toMonoType` 中处理了
  类型被擦除的常量。为这一点编写测试用例比看上去难得多，
  因为对这类类型的大多数引用都会更早地被替换成 `lcErased`。

* [#8712](https://github.com/leanprover/lean4/pull/8712) 将被擦除类型的 let 声明优化为
  擦除值。specialization 可能会生成返回 Prop 的局部函数，
  把它们保留下来并没有意义。

* [#8716](https://github.com/leanprover/lean4/pull/8716) 使得已擦除项上的任何类型应用
  也都会被擦除。在 Lean 自身的实现中，这种情况比想象中更常见。

* [#8717](https://github.com/leanprover/lean4/pull/8717) 使用 fvar 替换机制来替换已擦除代码。
  这还不算完全令人满意，因为 LCNF 的 `.return` 并不支持一般的 Arg
  （而 `Arg` 有 `.erased` 构造子），它只支持 `FVarId`。
  这与 IR 的 `.ret` 不同，后者支持一般的 `Arg`。

* [#8729](https://github.com/leanprover/lean4/pull/8729) 将 LCNF 的 `FVarSubst`
  从使用 `Expr` 改为使用 `Arg`。这会强制满足替换所需条件，而这些条件与
  `Arg` 的要求一致。

* [#8752](https://github.com/leanprover/lean4/pull/8752) 修复了这样一个问题：
  `extendJoinPointContext` 流程 会把含有投影的 汇合点 提升到顶层，
  作为对同一 base value 的其他投影做匹配之 `cases` 构造的同级节点。
  这会阻止 `structProjCases` pass 一次性投影两者，
  从而延长父值的生命周期，并在运行时破坏线性性。

* [#8754](https://github.com/leanprover/lean4/pull/8754) 修改了新编译器中
  计算字段的实现，这应能启用更多优化（并移除 `toLCNF` 中一个只适合 bringup 的、
  颇可疑的 hack）。我们像处理其他归纳类型那样把 `casesOn` 转成 `cases`，
  所有构造子会在 base 阶段稍后被替换为其真实实现，
  然后在 `toMono` 中把该 `cases` 表达式重写为使用真实构造子。

* [#8758](https://github.com/leanprover/lean4/pull/8758) 为 LCNF 类型上的
  `hasTrivialStructure?` 函数增加了缓存。这是新编译器中最热的小函数之一，
  因此加缓存很有价值。

* [#8764](https://github.com/leanprover/lean4/pull/8764) 修改了 LCNF pass 管线，
  使检查不再默认在每个 pass 后运行，而只在 `init`、`saveBase`、`toMono`
  和 `saveMono` 后运行。这能改善编译时间；并且在决定不再尝试于整个编译过程中
  保留类型之后，这些检查的实用性也有所下降。它们在新编译器开发中
  并不是发现问题的主要手段。

* [#8802](https://github.com/leanprover/lean4/pull/8802) 修复了 `floatLetIn` 中的一个缺陷：
  若某个声明（例如 汇合点）被提升进某个分支，并且它使用了另一个
  在该分支中没有其他现存用途的声明（例如另一个 汇合点），那么第二个声明
  尽管合法，却不会被一并提升进去。此前这会在
  `Lean.Elab.Tactic.BVDecide.LRAT.trim.useAnalysis` 中造成虚假的数组线性性问题。

* [#8816](https://github.com/leanprover/lean4/pull/8816) 在 LCNF simp 中为 Char.ofNat
  增加了常量折叠。这隐式依赖于把 `Char` 表示为 `UInt32`，
  而不是单独引入 `.char` 字面量类型；考虑到 `Char` 会在 `toMono`
  的平凡结构优化中被擦除，这样做是合理的。

* [#8822](https://github.com/leanprover/lean4/pull/8822) 在 toIR 中为构造子信息增加了缓存。
  这会被所有构造子、投影和 cases 分支调用，因此缓存很有必要。

* [#8825](https://github.com/leanprover/lean4/pull/8825) 改进了对由标量表示的归纳类型
  构造子的 IR 生成。令人意外的是，这对正确性并非必需，因为 boxing pass
  会把它修正回来。它额外插入的 `unbox` 操作在编译为原生代码时问题不大，
  因为 C 编译器很容易将其优化掉，但对解释器而言确实有影响。

* [#8831](https://github.com/leanprover/lean4/pull/8831) 缓存了 `lowerEnumToScalarType`
  的结果；该函数在 LCNF 到 IR 的转换中被大量使用。

* [#8885](https://github.com/leanprover/lean4/pull/8885) 移除了线程终结处理中，
  针对某些未实现 C++11 特性的旧兼容方案。

* [#8923](https://github.com/leanprover/lean4/pull/8923) 为 `Thunk` 和 `Task`
  实现了 `casesOn`。由于它们是内建类型，因此需要在 `toMono` 中做特殊处理。

* [#8952](https://github.com/leanprover/lean4/pull/8952) 修复了编译器 CSE pass 中
  对 `never_extract` 属性的处理。关于编译器究竟应多大程度避免复制那些
  传递性使用 `never_extract` 的内容，这里其实还有值得讨论的空间；
  不过当前实现是最简单的形式，并且大致匹配旧编译器的检查
  （虽然由于两个编译器处理局部函数声明的方式不同，后果可能略有差异）。

* [#8956](https://github.com/leanprover/lean4/pull/8956) 修改了 `toLCNF`，
  一旦看到带有 `never_extract` 标记的表达式，就停止缓存其翻译结果。
  这比理想情况更粗粒度，但要做得更细并不容易，因为新编译器的 `Expr`
  缓存基于结构同一性，而不是旧编译器中的指针同一性。

* [#9003](https://github.com/leanprover/lean4/pull/9003) 在新编译器中实现了对 `main`
  类型合法性的检查。此前没有相关测试，因此这个问题一直未被发现。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Pretty-Printing"
%%%

````markdown

* [#7954](https://github.com/leanprover/lean4/pull/7954) 改进了 `pp.oneline`，
  现在在把格式化语法截断为单行时会保留标签。需要注意的是，`[...]`
  续写部分目前还没有用于查看未截断语法的功能。关闭了 #3681。

* [#8617](https://github.com/leanprover/lean4/pull/8617) 修复了以下问题：
  1. private 名称在美观打印时不会被正确反解析；
  2. 在 `pp.universes` 模式下，名称可能遮蔽局部名；
  3. 在 `match` 模式中，遮蔽局部名的常量不会使用 `_root_`；
  4. 当设置 `pp.fullNames` 时，策略可能给出错误的 “try this”。
  此外还增加了更多用于名称反解析的反展开测试。

* [#8626](https://github.com/leanprover/lean4/pull/8626) 关闭了 #3791，确保
  Syntax 格式化器会在 Syntax 前后文本中的注释两侧插入空白，
  从而避免注释把后续语法一并注释掉，也避免把注释的词法语法解释为
  另一段语法的一部分。若文本在注释前后含有换行，则会被格式化为硬换行，
  而不是软换行。例如，`--` 注释之后会有一个硬换行。注意：
  生成带注释 Syntax 的元程序应确保在 `--` 注释末尾加入换行。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Documentation"
%%%

````markdown

* [#8934](https://github.com/leanprover/lean4/pull/8934) 为若干错误增加了解释，
  包括与 noncomputability、冗余 match 分支以及非法归纳声明有关的错误。

* [#8990](https://github.com/leanprover/lean4/pull/8990) 为 `grind` 内部代数类型类
  补充了缺失的文档字符串，以纳入参考手册。

* [#8998](https://github.com/leanprover/lean4/pull/8998) 使与 `Format` 和 `Repr`
  相关的文档字符串在格式和风格上保持一致，并补充了缺失的文档字符串。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Server"
%%%

````markdown

* [#8105](https://github.com/leanprover/lean4/pull/8105) 增加了对服务端 `RpcRef` 复用的支持，
  并修复了一个缺陷：文件仍在处理时，InfoView 中的 trace 节点会提前关闭。

* [#8511](https://github.com/leanprover/lean4/pull/8511) 实现了签名帮助支持。在输入函数应用时，
  支持签名帮助的编辑器现在会显示一个弹窗，指出当前（剩余的）函数类型。
  这使你不必在输入函数应用时记住函数签名，也不必不停在悬停函数标识符和输入应用之间来回切换。
  在 VS Code 中，可使用 `Ctrl+Shift+Space` 手动触发签名帮助。

* [#8654](https://github.com/leanprover/lean4/pull/8654) 为 VS Code 中新的模块层级组件
  增加了服务端支持，可用于同时导航模块的导入树和被导入树。具体来说，它实现了
  新请求 `$/lean/prepareModuleHierarchy`、
  `$/lean/moduleHierarchy/imports` 和
  `$/lean/moduleHierarchy/importedBy`。这些请求并不属于标准 LSP。
  对应的配套 PR 见
  [leanprover/vscode-lean4#620](https://github.com/leanprover/vscode-lean4/pull/620)。

* [#8699](https://github.com/leanprover/lean4/pull/8699) 通过调整 `lake setup-file`
  的使用方式，为服务器增加了对新模块 setup 流程的支持。

* [#8868](https://github.com/leanprover/lean4/pull/8868) 确保代码操作不必等整份文件
  完成精译之后才能运行。这一回归是 #7665 中意外引入的。

* [#9019](https://github.com/leanprover/lean4/pull/9019) 修复了语义高亮的一个缺陷：
  它此前只会高亮以字母数字字符开头的关键字。现在它改用 `Lean.isIdFirst`。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Lake"
%%%

````markdown

* [#7738](https://github.com/leanprover/lean4/pull/7738) 让内建 facet 的记忆化
  可以通过 facet 配置上的 `memoize` 选项来开关。那些本质上只是别名的
  内建 facet（例如 `default`、`o`）已禁用记忆化。

* [#8447](https://github.com/leanprover/lean4/pull/8447) 在 Lake 构建 Lean 模块时利用
  `lean --setup`，并为模块系统生成的新 `.olean` 产物增加了 Lake 支持。

* [#8613](https://github.com/leanprover/lean4/pull/8613) 修改了 Lake 的版本语法
  （改为 `5.0.0-src+<commit>`），以确保它是合法的 SemVer。

* [#8656](https://github.com/leanprover/lean4/pull/8656) 在 Lake 的 math 模板中启用了
  auto-implicit。这解决了一个问题：新用户有时会为数学形式化新建项目，
  随后却很快发现我们官方书籍和文档里使用 auto-implicit 的代码示例
  在他们的项目中都无法工作。随着[auto-implicit 的行内提示](https://github.com/leanprover/lean4/pull/6768)
  被引入，我们认为 auto-implicit 的使用体验已足够成熟，因而可以在 math 模板中默认启用。
  需要特别指出的是，这一改动并不影响 Mathlib 本身，后者仍会继续禁用 auto-implicit。

* [#8701](https://github.com/leanprover/lean4/pull/8701) 将 `Lake` 命名空间中的
  `LeanOption` 重新导出到 `Lean` 命名空间。`LeanOption` 在 #8447 中从
  `Lean` 移到了 `Lake`，若无此改动会导致不必要的破坏。

* [#8736](https://github.com/leanprover/lean4/pull/8736) 部分回滚了 #8024；
  该 PR 在构建期间引入了明显的 Lake 性能回退。等查明并修复原因后，
  还会通过类似 PR 把这里的回滚再撤销回来。

* [#8846](https://github.com/leanprover/lean4/pull/8846) 在不包含模块计算的前提下，
  重新把 `lean --setup` 的基础集成引入 Lake；模块计算部分仍在 #8787 中进行性能调试。

* [#8866](https://github.com/leanprover/lean4/pull/8866) 升级了 `lake init` 与
  `lake new` 的 `math` 模板，以将新项目配置到满足严格的 Mathlib 维护标准。
  与旧版本（现可通过 `lake new ... math-lax` 使用）相比，它会自动提供：

  * 与 Mathlib 一致的严格检查选项。
  * 用于自动升级到较新 Lean 与 Mathlib 版本的 GitHub 工作流。
  * 针对工具链升级的自动发布打标签。
  * 由 [doc-gen4](https://github.com/leanprover/doc-gen4) 生成并托管在
    `github.io` 上的 API 文档。
  * 带有若干 GitHub 专用说明的 README。

* [#8922](https://github.com/leanprover/lean4/pull/8922) 为 Lake 引入了本地产物缓存。启用后，
  Lake 会通过基于输入与内容寻址的缓存，在同一包的不同实例之间共享
  构建产物（已构建文件）。

* [#8981](https://github.com/leanprover/lean4/pull/8981) 移除了 Lake 通过
  `lean -R` 与 `moduleNameOfFileName` 向 Lean 传递模块名的做法。
  对工作区模块名，现在改为直接通过 `lean --setup` 传入。
  对于传给 `lake lean` 或 `lake setup-file` 的非工作区模块，
  则统一使用固定模块名 `_unknown`。

* [#9068](https://github.com/leanprover/lean4/pull/9068) 修复了本地 Lake 产物缓存的若干缺陷，
  并清理了周边 API。还增加了这样一种能力：对于未设置
  `enableArtifactCache` 的包，也可以通过 `LAKE_ARTIFACT_CACHE`
  环境变量选择启用缓存。

* [#9081](https://github.com/leanprover/lean4/pull/9081) 修复了 Lake 的一个缺陷：
  作业监视器此前会停留在顶层构建（例如 `mathlib/Mathlib:default`）上，
  而不是报告模块构建进度。

* [#9101](https://github.com/leanprover/lean4/pull/9101) 修复了 #9081 引入的一个缺陷：
  模块输入 trace 中会丢失源文件，同时模块作业日志中的部分条目也会丢失。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___22___0-_LPAR_2025-08-14_RPAR_--Other"
%%%

````markdown

* [#8702](https://github.com/leanprover/lean4/pull/8702) 增强了 PR 发布工作流，
  使其同时创建短格式与带 SHA 后缀的发布标签。它会同时创建
  pr-release-{PR_NUMBER} 和 pr-release-{PR_NUMBER}-{SHORT_SHA} 两类标签，
  分别生成对应发布，增加独立的 GitHub 状态检查，并更新
  Batteries/Mathlib 的测试分支，使其使用带 SHA 后缀的标签以精确追踪提交。

* [#8710](https://github.com/leanprover/lean4/pull/8710) 将 softprops/action-gh-release
  固定到了精确的哈希版本。

* [#9033](https://github.com/leanprover/lean4/pull/9033) 为参考手册增加了一个类似 Mathlib 的
  测试与反馈系统。Lean PR 将收到评论，反映语言参考相对于该 PR 的状态。

* [#9092](https://github.com/leanprover/lean4/pull/9092) 进一步更新了发布自动化。
  各仓库的更新脚本 `script/release_steps.py` 现在会真正执行测试，
  而不再只是输出一份供发布经理逐行运行的脚本。它已经在 `v4.21.0`
  上测试过（也就是稳定版发布这种较简单的情况），今晚还会在
  `v4.22.0-rc1` 上继续调试其行为。


````
