/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: investigate why the Markdown elaboration is taking this much stack in the new compiler
set_option maxRecDepth 9500

#doc (Manual) "Lean 4.17.0 (2025-03-03)" =>
%%%
tag := "release-v4.17.0"
file := "v4.17.0"
%%%

````markdown

本次发布共合入 319 项变更。除下方列出的 168 项功能新增和 57 项修复外，另有 12 项重构、13 项文档改进和 56 项杂项工作。


````
# 高亮
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Highlights"
%%%

````markdown

Lean v4.17 带来了一系列新特性、性能改进和问题修复。用户可见的重点更新包括：

* [#6368](https://github.com/leanprover/lean4/pull/6368) 实现了与精译并行执行的内核检查，这是精译本身实现并行化的前提。

* [#6711](https://github.com/leanprover/lean4/pull/6711) 通过加入一个预处理器，把 `UIntX` 和 `USize` 转换为对应位宽的 `BitVec`，从而为 `bv_decide` 增加了对它们的支持。

* [#6505](https://github.com/leanprover/lean4/pull/6505) 实现了基础异步框架，以及基于 libuv 的异步定时器运行机制。

* `docgen` 的文档能力得到改进，现在可以为 dot 记法（[#6703](https://github.com/leanprover/lean4/pull/6703)）、被 强制转换的函数（[#6729](https://github.com/leanprover/lean4/pull/6729)）以及 词元（[#6730](https://github.com/leanprover/lean4/pull/6730)）建立链接。

* 库方面有大量开发，尤其包括扩展 `BitVec` 的验证 API、统一 List / `Array` / `Vector` 的 API，并新增描述 `UInt` 行为的引理。

* [#6597](https://github.com/leanprover/lean4/pull/6597) 修复了信息视图中嵌套跟踪节点的缩进问题。

````
## 新语言特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Highlights--New-Language-Features"
%%%

````markdown

* **部分不动点**

 [#6355](https://github.com/leanprover/lean4/pull/6355) 增加了定义可能不终止函数的能力，同时仍可对其进行等式推理，只要这些函数是尾递归的，或运行在诸如 `Option` 这样的特定单子中。

 典型示例如下：

  ```lean
  def ack : (n m : Nat) → Option Nat
    | 0,   y   => some (y+1)
    | x+1, 0   => ack x 1
    | x+1, y+1 => do ack x (← ack (x+1) y)
  partial_fixpoint

  def whileSome (f : α → Option α) (x : α) : α :=
    match f x with
    | none => x
    | some x' => whileSome f x'
  partial_fixpoint

  def computeLfp {α : Type u} [DecidableEq α] (f : α → α) (x : α) : α :=
    let next := f x
    if x ≠ next then
      computeLfp f next
    else
      x
  partial_fixpoint
  ```

 更多细节请参阅[参考手册](https://lean-lang.org/doc/reference/latest/Recursive-Definitions/Partial-Fixpoint-Recursion/#partial-fixpoint)。

* [#6905](https://github.com/leanprover/lean4/pull/6905) 增加了 `try`? 交互式策略的首个草案，它会尝试多种策略，包括归纳：
  ```lean
  @[simp] def revAppend : List Nat → List Nat → List Nat
  | [],    ys => ys
  | x::xs, ys => revAppend xs (x::ys)

  example : (revAppend xs ys).length = xs.length + ys.length := by
    try?
    /-
    Try these:
    • · induction xs, ys using revAppend.induct
        · simp
        · simp +arith [*]
    • · induction xs, ys using revAppend.induct
        · simp only [revAppend, List.length_nil, Nat.zero_add]
        · simp +arith only [revAppend, List.length_cons, *]
    -/
  ```

* **零分支的 `induction`**

 [#6486](https://github.com/leanprover/lean4/pull/6486) 修改了 `induction`/`cases` 语法，使 `with` 子句后面不再必须跟任何分支。这提升了这些策略的易用性，因为它们现在可以直接显示缺失分支的名称：
  ```lean
  example (n : Nat) : True := by
    induction n with
  /-            ~~~~
  alternative 'zero' has not been provided
  alternative 'succ' has not been provided
  -/
  ```

* **转换模式中的 `simp?` 与 `dsimp?` 策略**

 [#6593](https://github.com/leanprover/lean4/pull/6593) 为转换模式中的 `simp?` 和 `dsimp?` 策略增加了支持。

* **`fun_cases`**

 [#6261](https://github.com/leanprover/lean4/pull/6261) 增加了 `foo.fun_cases`，这是一个自动生成的定理，会按照 `foo` 的分支结构拆分目标，类似函数归纳原理，但它适用于所有函数（不只是递归函数），并且不提供归纳假设。

````
## 新 CLI 特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Highlights--New-CLI-Features"
%%%

````markdown

* [#6427](https://github.com/leanprover/lean4/pull/6427) 为 Lean CLI 增加了 `--src-deps` 选项，对应于 `--deps`。它会解析 Lean 代码的头部，并打印（传递导入的）模块源码文件路径（根据 `LEAN_SRC_PATH` 推导）。

* [#6323](https://github.com/leanprover/lean4/pull/6323) 新增 Lake CLI 命令 `lake query`，既会构建目标，也会输出其结果。它可以生成原始文本或 JSON 格式的输出（使用 `--json` / `-J`）。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Highlights--Breaking-Changes"
%%%

````markdown

* [#6602](https://github.com/leanprover/lean4/pull/6602) 允许点标识符记法解析到当前定义，或者同一互递归代码块中的其他定义。现有使用点标识符记法的代码，如果标识符与定义同名，可能需要添加 `nonrec`。

* 引入 `zetaUnused` simp 与规约选项（[#6755](https://github.com/leanprover/lean4/pull/6755)）在少数情况下属于破坏性变更：`split` 策略不再以副作用方式移除未使用的 `let` 和 `have` 表达式。可以使用 `dsimp only` 移除未使用的 `have` 与 `let` 表达式。

_本高亮部分由 Violetta Sim 撰写。_

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Language"
%%%

````markdown

* [#5145](https://github.com/leanprover/lean4/pull/5145) 将内核使用的环境与精译器使用的环境分离开来，为跟踪异步精译的声明奠定了基础；后者中的这类声明只会作为概念存在于精译器一侧。

* [#6261](https://github.com/leanprover/lean4/pull/6261) 增加了 `foo.fun_cases`，这是一个自动生成的定理，会按照 `foo` 的分支结构拆分目标，类似函数归纳原理，但它适用于所有函数（不只是递归函数），并且不提供归纳假设。

* [#6355](https://github.com/leanprover/lean4/pull/6355) 增加了定义可能不终止函数的能力，同时仍可对其进行等式推理，只要它们是尾递归的或是单子式的。

* [#6368](https://github.com/leanprover/lean4/pull/6368) 实现了与精译并行执行的内核检查，这是精译本身实现并行化的前提。

* [#6427](https://github.com/leanprover/lean4/pull/6427) 为 Lean CLI 增加了 `--src-deps` 选项，对应于 `--deps`。它会解析 Lean 代码的头部，并打印（传递导入的）模块源码文件路径（根据 `LEAN_SRC_PATH` 推导）。

* [#6486](https://github.com/leanprover/lean4/pull/6486) 修改了 `induction`/`cases` 语法，使 `with` 子句后面不再必须跟任何分支。这提升了这些策略的易用性，因为它们现在可以直接显示缺失分支的名称：
  ```lean
  example (n : Nat) : True := by
    induction n with
  /-            ~~~~
  alternative 'zero' has not been provided
  alternative 'succ' has not been provided
  -/
  ```

* [#6505](https://github.com/leanprover/lean4/pull/6505) 实现了基础异步框架，以及基于 libuv 的异步定时器运行机制。

* [#6516](https://github.com/leanprover/lean4/pull/6516) 增强了 grind 策略中使用的 `cases` 策略，并确保它可以应用于任意表达式。

* [#6521](https://github.com/leanprover/lean4/pull/6521) 增加了把相关 `match` 方程作为 E-匹配定理激活的支持。它会使用 `match` 方程的左侧作为模式。

* [#6528](https://github.com/leanprover/lean4/pull/6528) 为仍在开发中的 grind 策略补上了一条缺失的传播规则。

* [#6529](https://github.com/leanprover/lean4/pull/6529) 为仍在开发中的 grind 策略增加了对 `let` 声明的支持。

* [#6530](https://github.com/leanprover/lean4/pull/6530) 修复了仍在开发中的 grind 策略中非确定性的失败问题。

* [#6531](https://github.com/leanprover/lean4/pull/6531) 修复了 grind 对 `let_fun` 的支持。

* [#6533](https://github.com/leanprover/lean4/pull/6533) 为 E-匹配的偏移模式增加支持。例如，我们希望能用模式 `f (#0 + 1)` 去 E-匹配项 `f (a + 2)`。

* [#6534](https://github.com/leanprover/lean4/pull/6534) 确保用户可以在 `grind` 策略中的 E-匹配模式里使用投影。

* [#6536](https://github.com/leanprover/lean4/pull/6536) 修复了 `grind` 策略中控制 E-匹配的若干阈值问题。

* [#6538](https://github.com/leanprover/lean4/pull/6538) 确保用户提供的模式会被规范化。为何需要这样做，可参见新增测试。

* [#6539](https://github.com/leanprover/lean4/pull/6539) 引入 `[grind_eq]` 属性，用于给等式定理和函数做标注，以便 `grind` 策略进行启发式实例化。应用于等式定理时，`[grind_eq]` 会指示 `grind` 在证明搜索期间自动使用被标注定理来实例化模式；如果应用于函数，则会标记与该函数关联的所有等式定理。

* [#6543](https://github.com/leanprover/lean4/pull/6543) 为 `grind` 增加了更多测试，展示了我们可以自动化 Mathlib 基础范畴论库中的一些手写证明，并减少对 Mathlib 的 `@[reassoc]` 技巧的依赖。

* [#6545](https://github.com/leanprover/lean4/pull/6545) 引入参数化属性 `[grind]`，用于标注定理和定义。同时还以 `[grind =]` 替换了 `[grind_eq]`。对于定义而言，`[grind]` 等价于 `[grind =]`。

* [#6556](https://github.com/leanprover/lean4/pull/6556) 为 `grind` 策略增加了针对蕴含的传播器。同时还禁用了规范化规则 `(p → q) = (¬ p ∨ q)`。

* [#6559](https://github.com/leanprover/lean4/pull/6559) 为 `grind` 策略增加了一种基础的分情况拆分策略。我们之后仍需加入用户自定义支持。

* [#6565](https://github.com/leanprover/lean4/pull/6565) 修复了当 `rintro` 和 `intro` 策略无法引入请求数量的绑定器时，其报错位置不正确的问题。

* [#6566](https://github.com/leanprover/lean4/pull/6566) 增加了删除 `[grind]` 属性的支持；该属性原本用于在 `grind` 策略中标记要进行启发式实例化的定理。

* [#6567](https://github.com/leanprover/lean4/pull/6567) 增加了删除 `[grind]` 属性的支持；该属性原本用于在 `grind` 策略中标记要进行启发式实例化的定理。

* [#6568](https://github.com/leanprover/lean4/pull/6568) 为 `grind` 策略增加了对 cast-like 运算符的基础支持。例如：
  ```lean
  example (α : Type) (β : Type) (a₁ a₂ : α) (b₁ b₂ : β)
          (h₁ : α = β)
          (h₂ : h₁ ▸ a₁ = b₁)
          (h₃ : a₁ = a₂)
          (h₄ : b₁ = b₂)
          : HEq a₂ b₂ := by
    grind
  ```

* [#6569](https://github.com/leanprover/lean4/pull/6569) 为 `grind` 增加了对 `match` 表达式进行分情况拆分的支持。之后仍需支持求解 `match` 条件方程的前件。

* [#6575](https://github.com/leanprover/lean4/pull/6575) 确保在 `classical` 的主体中，策略会被增量求值。

* [#6578](https://github.com/leanprover/lean4/pull/6578) 修复并改进了 `grind` 策略中针对 forall 表达式的传播器。

* [#6581](https://github.com/leanprover/lean4/pull/6581) 为 `Grind.Config` 增加以下配置项：`splitIte`、`splitMatch` 和 `splitIndPred`。

* [#6582](https://github.com/leanprover/lean4/pull/6582) 增加了为已知为真的全称命题创建局部 E-匹配定理的支持。这使 `grind` 可以自动解出如下示例：

* [#6584](https://github.com/leanprover/lean4/pull/6584) 添加了辅助定理，用于在 `grind` 中实现偏移约束。

* [#6585](https://github.com/leanprover/lean4/pull/6585) 修复了 `grind` 规范化器中的一个问题。

* [#6588](https://github.com/leanprover/lean4/pull/6588) 改进了 `grind` 规范化器的诊断信息。

* [#6593](https://github.com/leanprover/lean4/pull/6593) 为转换模式中的 `simp?` 与 `dsimp?` 策略增加支持。

* [#6595](https://github.com/leanprover/lean4/pull/6595) 改进了用于证明不等式偏移模块各步骤正确性的定理。它们未来如何使用，可见新增测试中的示例。

* [#6600](https://github.com/leanprover/lean4/pull/6600) 移除了 Environment 上用于编译声明的函数，并将所有调用方迁移到 CoreM 上的函数。这是支持新代码生成器所必需的，因为它的实现使用了 CoreM。

* [#6602](https://github.com/leanprover/lean4/pull/6602) 允许点标识符记法解析到当前定义，或者同一互递归代码块中的其他定义。现有使用点标识符记法的代码，如果标识符与定义同名，可能需要添加 `nonrec`。

* [#6603](https://github.com/leanprover/lean4/pull/6603) 在 `grind` 策略中实现了偏移约束支持。尽管仍缺少一些特性，例如约束传播和偏移相等式支持，但 `grind` 已经能解决如下示例：

* [#6606](https://github.com/leanprover/lean4/pull/6606) 修复了 `grind` 中模式选择的一个问题。

* [#6607](https://github.com/leanprover/lean4/pull/6607) 为 `grind` 策略增加了对 `<->`（以及 `@Eq Prop`）进行分情况拆分的支持。

* [#6608](https://github.com/leanprover/lean4/pull/6608) 修复了 `simp_arith` 策略中的一个问题。详见新增测试。

* [#6609](https://github.com/leanprover/lean4/pull/6609) 改进了 `grind` 使用的分情况拆分启发式，优先选择分支数更少的拆分。

* [#6610](https://github.com/leanprover/lean4/pull/6610) 修复了 `grind` 核心模块中的一个问题；该模块负责合并等价类和传播约束。

* [#6611](https://github.com/leanprover/lean4/pull/6611) 修复了 `grind` 使用的一项健全性检查测试。

* [#6613](https://github.com/leanprover/lean4/pull/6613) 改进了 `grind` 策略使用的分情况拆分启发式，确保它现在会避免对 `Iff` 做不必要的拆分。

* [#6614](https://github.com/leanprover/lean4/pull/6614) 通过自动处理被禁止的模式符号，改进了 `[grind =]` 属性的可用性。比如，考虑下面这个带有该属性的定理：
  ```lean
  getLast?_eq_some_iff {xs : List α} {a : α} : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a]
  ```
  这里选中的模式是 `xs.getLast? = some a`，但 `Eq` 是被禁止的模式符号。该函数不会直接报错，而是会把这个模式转换为多模式，从而让这个属性更方便使用。

* [#6615](https://github.com/leanprover/lean4/pull/6615) 添加了两个辅助函数 `mkEqTrueCore` 与 `mkOfEqTrueCore`，用于避免 `grind` 生成的证明中出现冗余证明项。

* [#6618](https://github.com/leanprover/lean4/pull/6618) 在 `grind` 策略中实现了穷尽式偏移约束传播。这个增强能尽量减少 `grind` 执行的分情况拆分次数。例如，它可以在不做任何分情况拆分的情况下解出如下示例：

* [#6633](https://github.com/leanprover/lean4/pull/6633) 改进了 `grind` 策略产生的失败消息。现在会包含已断言事实、已知为真和为假的命题，以及等价类等信息。

* [#6636](https://github.com/leanprover/lean4/pull/6636) 在 `grind` 策略中实现了偏移约束的模型构造。

* [#6639](https://github.com/leanprover/lean4/pull/6639) 将 bv_normalize 的 simp set 放入 simp_nf，并把 bv_normalize 的实现拆分到多个文件中，为后续变更做准备。

* [#6641](https://github.com/leanprover/lean4/pull/6641) 把 Bitwuzla 预处理过程中的若干优化技巧实现到 `bv_decide` 中对应的 Lean 版本里。请注意，这些改动主要面向大型证明状态，例如 SMT-Lib 中常见的那类场景。

* [#6645](https://github.com/leanprover/lean4/pull/6645) 在 `grind` 策略中实现了偏移相等约束支持，以及针对它们的穷尽式相等传播。`grind` 现在可以解决如下问题：

* [#6648](https://github.com/leanprover/lean4/pull/6648) 为 `grind` 策略中的偏移约束模块增加了对数值字面量、下界和上界的支持。`grind` 现在可以解出如下示例：
  ```lean
  example (f : Nat → Nat) :
          f 2 = a →
          b ≤ 1 → b ≥ 1 →
          c = b + 1 →
          f c = a := by
    grind
  ```
  在上面的例子中，字面量 `2` 以及上下界 `b ≤ 1` 和 `b ≥ 1` 现在都会由偏移约束模块处理。

* [#6649](https://github.com/leanprover/lean4/pull/6649) 修复了 `grind` 策略使用的项规范化器中的一个问题。

* [#6652](https://github.com/leanprover/lean4/pull/6652) 增加了 `int_toBitVec` simp set，用于把 UIntX 以及后续的 IntX 命题转换为 BitVec 命题。这将作为 `bv_decide` 的预处理器，为 UIntX/IntX 提供 `bv_decide` 支持。

* [#6653](https://github.com/leanprover/lean4/pull/6653) 改进了 `grind` 策略中 E-匹配的模式选择启发式。现在它们会考虑类型谓词和变换器。

* [#6654](https://github.com/leanprover/lean4/pull/6654) 改进了 `grind` 所使用的 E-匹配过程中对部分应用的支持。

* [#6656](https://github.com/leanprover/lean4/pull/6656) 改进了 `grind` 失败状态下提供的诊断信息。现在会包含搜索过程中发现的问题列表，以及所有达到过的搜索阈值；同时也改进了其格式化方式。

* [#6657](https://github.com/leanprover/lean4/pull/6657) 改进了 `grind` 的搜索过程，并新增配置项 `failures`。

* [#6658](https://github.com/leanprover/lean4/pull/6658) 确保 `grind` 会避免对那些与已经分情况拆分过的项 congruent 的项再次进行拆分。

* [#6659](https://github.com/leanprover/lean4/pull/6659) 修复了 `grind` 项预处理器中的一个问题。此前它会在展开 reducible 常量**之前**抽象嵌套证明。

* [#6662](https://github.com/leanprover/lean4/pull/6662) 改进了 `grind` 策略使用的规范化器及其产生的诊断信息。同时新增配置项 `canonHeartbeats`，以解决其中（部分）问题。下面的例子展示了新的诊断信息，我们通过设置一个很小的 heartbeat 数量来故意制造问题。

* [#6663](https://github.com/leanprover/lean4/pull/6663) 为 `grind` 策略实现了基础的相等式求解过程。

* [#6669](https://github.com/leanprover/lean4/pull/6669) 针对 Terminal/Emacs 与 VS Code 在显示信息树时的不一致行为，加入了一个变通方案。

* [#6675](https://github.com/leanprover/lean4/pull/6675) 为 `grind` 增加了类似 `simp` 的参数，以及类似 `simp only` 的 `grind only`。

* [#6679](https://github.com/leanprover/lean4/pull/6679) 修改了标识符解析器，允许使用 Unicode 字符 ⱼ；此前它被遗漏了，因为它单独位于一段包含科普特字符的代码块中。

* [#6682](https://github.com/leanprover/lean4/pull/6682) 为 `grind` 策略增加了对外延性定理（通过 `[ext]` 属性）的支持。用户可以通过 `grind -ext` 禁用该功能。下面的例子展示了现在可由 `grind` 解决的问题。

* [#6685](https://github.com/leanprover/lean4/pull/6685) 修复了 `#check_failure` 的输出被当成 warning 的问题。

* [#6686](https://github.com/leanprover/lean4/pull/6686) 修复了 `grind` 策略中参数处理、初始化和属性处理的问题。

* [#6691](https://github.com/leanprover/lean4/pull/6691) 引入了用于对环境进行并行修改的核心 API。

* [#6692](https://github.com/leanprover/lean4/pull/6692) 移除了 `[grind_norm]` 属性。`grind` 使用的规范化定理现在是固定的，用户无法修改。我们使用这些规范化定理来确保内建过程接收到期望“形状”的项，它们用于 `grind` 内建支持的那些类型。用户原本可能把这个特性误用为简化规则。比如，考虑下面的例子：

* [#6700](https://github.com/leanprover/lean4/pull/6700) 为 `grind` 策略增加了 beta reduction 支持。`grind` 现在可以解出如下目标：
  ```lean
  example (f : Nat → Nat) : f = (fun x : Nat => x + 5) → f 2 > 5 := by
    grind
  ```

* [#6702](https://github.com/leanprover/lean4/pull/6702) 为 `grind` 增加了相等式的反向推理支持。下面的例子可以说明这一新特性。假设我们有如下定理：
  ```lean
  theorem inv_eq {a b : α} (w : a * b = 1) : inv a = b
  ```
  并且我们希望在尝试证明某些项 `t` 与 `s` 满足 `inv t = s` 时实例化该定理。由于默认情况下 `=` 不能用于 E-匹配，所以属性 `[grind ←]` 不适用于此。新的属性 `[grind ←=]` 会指示 `grind` 使用相等式，并把 `grind` 证明状态中的不等式也视作 E-匹配候选。

* [#6705](https://github.com/leanprover/lean4/pull/6705) 增加了 `[grind cases]` 和 `[grind cases eager]` 属性，用于控制 `grind` 中的分情况拆分。它们将取代 `[grind_cases]` 和配置项 `splitIndPred`。

* [#6711](https://github.com/leanprover/lean4/pull/6711) 通过加入一个预处理器，把 `UIntX` 和 `USize` 转换为对应位宽的 `BitVec`，从而为 `bv_decide` 增加了对它们的支持。

* [#6717](https://github.com/leanprover/lean4/pull/6717) 引入了一项新特性，允许用户指定 `grind` 策略应对哪些归纳数据类型进行分情况拆分。配置项 `splitIndPred` 现在默认设为 `false`。属性 `[grind cases]` 用于标记那些可在搜索期间由 `grind` 进行分情况拆分的归纳数据类型和谓词；另外，`[grind cases eager]` 可用于标记那些既能在预处理阶段、也能在搜索期间进行分情况拆分的数据类型和谓词。

* [#6718](https://github.com/leanprover/lean4/pull/6718) 添加了消去乘法负号所需的 BitVec 引理，并把支持接入 bv_normalize，以便在规范化后的二补码形式中利用这些结果。

* [#6719](https://github.com/leanprover/lean4/pull/6719) 修复了 `match` 表达式等式定理生成器中的一个问题。可参见新增测试中的例子。

* [#6724](https://github.com/leanprover/lean4/pull/6724) 为 `bv_decide` 增加了自动拆解包含受支持类型信息的非递归结构体的支持。可以通过 `bv_decide` 配置中的新字段 `structures` 进行控制。

* [#6733](https://github.com/leanprover/lean4/pull/6733) 改进了 `grind` 对重叠 `match` 模式的支持。`grind` 现在可以解出如下示例：
  ```lean
  inductive S where
    | mk1 (n : Nat)
    | mk2 (n : Nat) (s : S)
    | mk3 (n : Bool)
    | mk4 (s1 s2 : S)

  def f (x y : S) :=
    match x, y with
    | .mk1 _, _ => 2
    | _, .mk2 1 (.mk4 _ _) => 3
    | .mk3 _, _ => 4
    | _, _ => 5

  example : b = .mk2 y1 y2 → y1 = 2 → a = .mk4 y3 y4 → f a b = 5 := by
    unfold f
    grind (splits := 0)
  ```

* [#6735](https://github.com/leanprover/lean4/pull/6735) 为 `grind` 策略增加了对带重叠模式的 `match` 表达式进行分情况拆分的支持。`grind` 现在可以解出如下示例：
  ```lean
  inductive S where
    | mk1 (n : Nat)
    | mk2 (n : Nat) (s : S)
    | mk3 (n : Bool)
    | mk4 (s1 s2 : S)

  def g (x y : S) :=
    match x, y with
    | .mk1 a, _ => a + 2
    | _, .mk2 1 (.mk4 _ _) => 3
    | .mk3 _, .mk4 _ _ => 4
    | _, _ => 5

  example : g a b > 1 := by
    grind [g.eq_def]
  ```

* [#6736](https://github.com/leanprover/lean4/pull/6736) 确保 `grind` 使用的规范化器不会浪费时间去检查不同类型的项是否定义相等。

* [#6737](https://github.com/leanprover/lean4/pull/6737) 确保 `if-then-else` 项的分支只会在确定条件真值之后才被内化。这一改动使其行为与 `grind` 中 `match` 表达式和依赖型 `if-then-else` 的处理保持一致。对于通过良基递归和 `if-then-else` 定义的递归函数而言，这个特性尤为重要；若不采用惰性的 `if-then-else` 分支内化，递归函数的方程定理会在执行任何 case 分析之前就一直展开到生成深度阈值。相关示例见新增测试。

* [#6739](https://github.com/leanprover/lean4/pull/6739) 为 `bv_decide` 中对常量乘法进行 bitblasting 增加了一条快速路径。

* [#6740](https://github.com/leanprover/lean4/pull/6740) 扩展了 `bv_decide` 的结构体推理支持，使其也能推理受支持结构体之间的相等性。

* [#6745](https://github.com/leanprover/lean4/pull/6745) 支持用 `extractLsb'` 重写 ushiftRight。这是 #6743 的配套 PR；#6743 增加了关于 `shiftLeft` 的类似引理。

* [#6746](https://github.com/leanprover/lean4/pull/6746) 确保 `grind` 能正确处理函数定义的条件方程定理。这里复用了为 `match` 表达式方程构建的同一套基础设施。回顾一下：在这两种场景下，只要存在重叠模式，这些定理都会是条件性的。

* [#6748](https://github.com/leanprover/lean4/pull/6748) 修复了 `grind` 策略中的一些问题：漏报问题、错误消息糟糕、规范化器中阈值不正确，以及 ground 模式内化器中的问题。

* [#6750](https://github.com/leanprover/lean4/pull/6750) 为 `grind` 策略所用的 E-匹配模块增加支持：在实例化量词时，可使用 `cast` 修复类型不匹配。

* [#6754](https://github.com/leanprover/lean4/pull/6754) 增加了 `+zetaUnused` 选项。

* [#6755](https://github.com/leanprover/lean4/pull/6755) 实现了 `zetaUnused` simp 与规约选项（见 #6754）。

* [#6761](https://github.com/leanprover/lean4/pull/6761) 修复了 `grind` 在处理带索引族的 `match` 表达式时的问题。

* [#6773](https://github.com/leanprover/lean4/pull/6773) 修复了一个拼写错误，该错误会导致 `Nat.reduceAnd` 无法正常工作。

* [#6777](https://github.com/leanprover/lean4/pull/6777) 修复了 `grind` 策略中偏移项内化的一个问题。例如，`grind` 之前就因为这个问题而无法解决下面这个例子。
  ```lean
  example (f : Nat → Nat) : f (a + 1) = 1 → a = 0 → f 1 = 1 := by
    grind
  ```

* [#6778](https://github.com/leanprover/lean4/pull/6778) 修复了 `grind` 生成的赋值，使其能够满足目标中的偏移约束。

* [#6779](https://github.com/leanprover/lean4/pull/6779) 改进了 `grind` 策略对 `match` 表达式的支持。

* [#6781](https://github.com/leanprover/lean4/pull/6781) 修复了 `grind` 策略中对数据进行分情况拆分的支持。下面这个例子现在可以工作了：
  ```lean
  inductive C where
    | a | b | c

  def f : C → Nat
    | .a => 2
    | .b => 3
    | .c => 4

  example : f x > 1 := by
    grind [
        f, -- instructs `grind` to use `f`-equation theorems,
        C -- instructs `grind` to case-split on free variables of type `C`
    ]
  ```

* [#6783](https://github.com/leanprover/lean4/pull/6783) 增加了使用 `grind` 策略状态中已知为真的 `match` 表达式条件来关闭目标的支持。`grind` 现在可以解出如下目标：
  ```lean
  def f : List Nat → List Nat → Nat
    | _, 1 :: _ :: _ => 1
    | _, _ :: _ => 2
    | _, _  => 0

  example : z = a :: as → y = z → f x y > 0
  ```

* [#6785](https://github.com/leanprover/lean4/pull/6785) 为 `grind?` 策略增加了基础设施。它还增加了新修饰符 `usr`，使用户能够写出 `grind only [use thmName]`，从而指示 `grind` 仅使用定理 `thmName`，但使用由 `grind_pattern` 命令指定的模式。

* [#6788](https://github.com/leanprover/lean4/pull/6788) 让 bv_normalize 认识到 `!(x < x)` 和 `!(x < 0)`。

* [#6790](https://github.com/leanprover/lean4/pull/6790) 修复了在需要分情况拆分时，由 `partial_fixpoint` 生成等式定理的问题。修复 #6786。

* [#6791](https://github.com/leanprover/lean4/pull/6791) 通过确保模式匹配中为不可访问变量生成的元数据会在 `casesOnStuckLHS` 中被相应消费，从而修复了 #6789。

* [#6801](https://github.com/leanprover/lean4/pull/6801) 修复了 `grind` 使用的穷尽式偏移约束传播模块中的一个问题。

* [#6810](https://github.com/leanprover/lean4/pull/6810) 为 `grind` 实现了一个基础的配套 `grind?` 策略。后续还会继续增强。

* [#6822](https://github.com/leanprover/lean4/pull/6822) 为 `grind` 增加了一些内建的分情况拆分。它们类似于内建 `simp` 定理，可以减少 `grind?` 生成策略时的噪音。

* [#6824](https://github.com/leanprover/lean4/pull/6824) 引入辅助命令 `%reset_grind_attrs` 以供调试之用。它对编写自包含测试尤其有帮助。

* [#6834](https://github.com/leanprover/lean4/pull/6834) 为 `grind` 增加了“性能”计数器（例如每个定理对应的实例数）。在失败时总会报告这些计数器；成功时若 `set_option diagnostics true`，也会报告。

* [#6839](https://github.com/leanprover/lean4/pull/6839) 确保 `grind` 可以把构造子和公理用于基于 E-匹配的启发式实例化。它还允许对诸如 `theorem evenz : Even 0` 这样的定理使用不带模式变量的模式。

* [#6851](https://github.com/leanprover/lean4/pull/6851) 让 bv_normalize 把以 `BitVec` 常量表示的移位重写为以 `Nat` 常量表示的移位。这是增强 bv_normalize 对常量移位化简支持这一更大工作的组成部分。

* [#6852](https://github.com/leanprover/lean4/pull/6852) 允许环境扩展选择不会阻塞截至当前整个环境的访问模式，这是实现并行证明精译所必需的前提。

* [#6854](https://github.com/leanprover/lean4/pull/6854) 为 `grind` 中的归纳谓词增加了一项便利功能。现在，给定归纳谓词 `C`，`grind [C]` 会把 `C` 项标记为可分情况拆分候选，**并且**把 `C` 的构造子标记为 E-匹配定理。示例如下：
  ```lean
  example {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
    grind [BigStep]
  ```
  用户仍可使用 `grind [cases BigStep]`，仅把 `C` 标记为分情况拆分候选。

* [#6858](https://github.com/leanprover/lean4/pull/6858) 为 `grind` 中的 `decide` 和相等式增加了新的传播规则。同时还增加了新测试并清理了旧测试。

* [#6861](https://github.com/leanprover/lean4/pull/6861) 为 `grind` 策略增加了 `Bool.and`、`Bool.or` 和 `Bool.not` 的传播规则。

* [#6870](https://github.com/leanprover/lean4/pull/6870) 为 `grind` 增加了两个新的规范化步骤，分别把 `a != b` 和 `a == b` 规约为 `decide (¬ a = b)` 与 `decide (a = b)`。

* [#6879](https://github.com/leanprover/lean4/pull/6879) 修复了 `grind` 策略所使用的 `mkMatchCondProf?` 中的一个问题。该问题会导致测试 `grind_constProp.lean` 失败。

* [#6880](https://github.com/leanprover/lean4/pull/6880) 改进了 `grind` 中使用的 E-匹配模式选择启发式。

* [#6881](https://github.com/leanprover/lean4/pull/6881) 改进了 `grind` 的错误消息，将 `grind` 应用 `cases` 类操作的那些项的跟踪一并包含其中。

* [#6882](https://github.com/leanprover/lean4/pull/6882) 确保 `grind` 的辅助装置在错误和诊断消息中会被“隐藏”起来。

* [#6888](https://github.com/leanprover/lean4/pull/6888) 增加了 `[grind intro]` 属性。它会指示 `grind` 把归纳谓词的引入规则标记为 E-匹配定理。

* [#6889](https://github.com/leanprover/lean4/pull/6889) 对 `bv_decide` 电路缓存中的一些函数进行了内联。

* [#6892](https://github.com/leanprover/lean4/pull/6892) 修复了 `grind` 中模式选择启发式的一个问题。此前它会展开本不该展开的定义/抽象。受影响的例子见 `grind_constProp.lean`。

* [#6895](https://github.com/leanprover/lean4/pull/6895) 修复了 `grind_constProp.lean` 测试暴露出的若干 `grind` 问题。
  - 支持在调用 `grind` 之前就已创建的等式定理假设，例如应用归纳原理时。
  - 支持 `Unit`-like 类型。
  - 补上缺失的递归深度检查。

* [#6897](https://github.com/leanprover/lean4/pull/6897) 增加了新的属性 `[grind =>]` 和 `[grind <=]`，用于控制模式选择，并尽量减少必须使用冗长 `grind_pattern` 命令的场景。它还修复了新模式选择过程中的一个问题，并改进了对局部引理的自动模式选择。

* [#6904](https://github.com/leanprover/lean4/pull/6904) 增加了 `grind` 配置项 `verbose`。例如，`grind -verbose` 会禁用所有诊断信息。我们将利用这个标志来实现 `try?`。

* [#6905](https://github.com/leanprover/lean4/pull/6905) 增加了 `try?` 策略；详见上文。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Library"
%%%

````markdown

* [#6177](https://github.com/leanprover/lean4/pull/6177) 实现了 `BitVec.*_fill`。

* [#6211](https://github.com/leanprover/lean4/pull/6211) 针对插入列表这一特殊情形，验证了 `HashMap` 上的 `insertMany` 方法。

* [#6346](https://github.com/leanprover/lean4/pull/6346) 补全了 `shiftLeft` 的 toNat/Int/Fin 系列。

* [#6347](https://github.com/leanprover/lean4/pull/6347) 增加了 `BitVec.toNat_rotateLeft` 和 `BitVec.toNat_rotateLeft`。

* [#6402](https://github.com/leanprover/lean4/pull/6402) 为无符号位向量除法增加了 `toFin` 和 `msb` 引理。我们*没有*提供 `toInt_udiv`，因为唯一真正通用的表述无非是展开定义，而如何展开 `toInt` 本身并没有无争议的统一方式（可参见当前提供的几个选项：`toInt_eq_msb_cond`/`toInt_eq_toNat_cond`/`toInt_eq_toNat_bmod`）。相反，我们提供了 `toInt_udiv_of_msb`，在额外假设 `x.msb = false` 下，它能够给出更有意义的重写。

* [#6404](https://github.com/leanprover/lean4/pull/6404) 为无符号位向量取模增加了 `toFin` 和 `msb` 引理。与 #6402 类似，我们不提供通用的 `toInt_umod` 引理，而是选择提供带额外侧条件的、更专门化的重写。

* [#6431](https://github.com/leanprover/lean4/pull/6431) 修复了 `Timestamp` 类型的 `Repr` 实例，并修改 `PlainTime` 类型，使其始终表示一个可能是闰秒的时钟时间。

* [#6476](https://github.com/leanprover/lean4/pull/6476) 为位向量定义了 `reverse`，并实现了首批相关定理（`getLsbD_reverse, getMsbD_reverse, reverse_append, reverse_replicate, reverse_cast, msb_reverse`）。我们还加入了一些必要的相关定理（`cons_append, cons_append_append, append_assoc, replicate_append_self, replicate_succ'`），并弃用了定理 `replicate_zero_eq` 和 `replicate_succ_eq`。

* [#6494](https://github.com/leanprover/lean4/pull/6494) 证明了关于函数 `Int.bdiv` 和 `Int.bmod` 的基础定理。

* [#6507](https://github.com/leanprover/lean4/pull/6507) 为 `Int.emod_add_emod`（`(a % n + b) % n = (a + b) % n`）和 `Int.add_emod_emod`（`(a + b % n) % n = (a + b) % n`）添加了对应的减法版本。它们像加法版本一样被标记为 @[simp]。

* [#6524](https://github.com/leanprover/lean4/pull/6524) 将 Batteries 中剩余的一些 `List.Perm` 引理上游化。

* [#6546](https://github.com/leanprover/lean4/pull/6546) 继续把 `Array` 与 `Vector` 的引理与 `List` 对齐，重点处理 `fold` 和 `map` 操作。

* [#6563](https://github.com/leanprover/lean4/pull/6563) 实现了 `Std.Net.Addr`，其中包含围绕 IP 和套接字地址的结构体。

* [#6573](https://github.com/leanprover/lean4/pull/6573) 用更底层、更高效的实现替换了现有的 `(D)HashMap.alter` 和 `(D)HashMap.modify`，并特别给出了它们会产生良构哈希映射（`WF` 类型类）的证明。

* [#6586](https://github.com/leanprover/lean4/pull/6586) 继续对齐 `List/Array/Vector` 的引理，完成了关于 `map` 的引理。

* [#6587](https://github.com/leanprover/lean4/pull/6587) 为 `Std.Time` 中定义的 `Offset` 类型上的 `LE` 与 `LT` 实例增加了可判定实例。

* [#6589](https://github.com/leanprover/lean4/pull/6589) 继续对齐 `List/Array` 的引理，完成了 `filter` 和 `filterMap` 相关部分。

* [#6591](https://github.com/leanprover/lean4/pull/6591) 为 `UInt32` 添加了小于与小于等于关系，与其他 `UIntN` 类型保持一致。

* [#6612](https://github.com/leanprover/lean4/pull/6612) 添加了关于 `Array.append` 的引理，进一步对齐 `List` API。

* [#6617](https://github.com/leanprover/lean4/pull/6617) 完成了 `List`/`Array`/`Vector` 上 `append` 引理的对齐。

* [#6620](https://github.com/leanprover/lean4/pull/6620) 添加了关于 HashMap.alter 和 .modify 的引理。这些引理描述了 alter 和 modify 与 HashMap 读取方法之间的交互。新增内容影响到 HashMap、DHashMap 以及它们各自的 raw 版本；此外，也定义了 alter 和 modify 的 raw 版本。

* [#6625](https://github.com/leanprover/lean4/pull/6625) 添加了描述 `UIntX.toBitVec` 在 `UIntX` 运算上行为的引理。

* [#6630](https://github.com/leanprover/lean4/pull/6630) 添加定理 `Nat.[shiftLeft_or_distrib`, shiftLeft_xor_distrib`, shiftLeft_and_distrib`, `testBit_mul_two_pow`, `bitwise_mul_two_pow`, `shiftLeft_bitwise_distrib]`，以模仿 `shiftRight_and_distrib` 的证明策略来证明 `Nat.shiftLeft_or_distrib`。

* [#6640](https://github.com/leanprover/lean4/pull/6640) 完成了 `List`/`Array`/`Vector` 上关于 `flatten` 的引理对齐。此前缺失的 `Vector.flatten` 也已加入（仅适用于矩形尺寸）。另外还补充了少量缺失的 `Option` 引理，以便相关证明可以通过。

* [#6660](https://github.com/leanprover/lean4/pull/6660) 定义了 `Vector.flatMap`，并为保持一致性修改了 `List.flatMap` 的参数顺序，同时对齐了 `List`/`Array`/`Vector` 的 `flatMap` 引理。

* [#6661](https://github.com/leanprover/lean4/pull/6661) 为 `Vector.flatMap` 添加了数组索引引理。（由于长度可变，这些引理对 `List` 和 `Array` 并不适用。）

* [#6667](https://github.com/leanprover/lean4/pull/6667) 对齐了 `List.replicate`/`Array.mkArray`/`Vector.mkVector` 的引理。

* [#6668](https://github.com/leanprover/lean4/pull/6668) 修复了负时间戳以及 1970 年之前的 `PlainDateTime`。

* [#6674](https://github.com/leanprover/lean4/pull/6674) 添加定理 `BitVec.[getMsbD_mul, getElem_udiv, getLsbD_udiv, getMsbD_udiv]`。

* [#6695](https://github.com/leanprover/lean4/pull/6695) 对齐了 `List/Array/Vector.reverse` 的引理。

* [#6697](https://github.com/leanprover/lean4/pull/6697) 将 `List/Array.mapFinIdx` 的参数从 `(f : Fin as.size → α → β)` 改为 `(f : (i : Nat) → α → (h : i < as.size) → β)`，以与 `List/Array` 其他地方的 API 设计保持一致。

* [#6701](https://github.com/leanprover/lean4/pull/6701) 完成了 `List/Array/Vector` 上 `mapIdx` 与 `mapFinIdx` 的对齐。

* [#6707](https://github.com/leanprover/lean4/pull/6707) 完成了 `List` / `Array` / `Vector` 上关于 `foldl`、`foldr` 及其单子式版本的引理对齐。

* [#6708](https://github.com/leanprover/lean4/pull/6708) 弃用了 `List.iota`，因为我们并未在本质上依赖它。`iota n` 可替换为 `(range' 1 n).reverse`。`range'` 的验证引理覆盖面已经优于 `iota`。任何仍在使用它的下游项目（我目前并不知道有哪一个）都建议迁移。

* [#6712](https://github.com/leanprover/lean4/pull/6712) 对齐了 `List`/`Array`/`Vector` 上关于 `countP` 和 `count` 的定理。

* [#6723](https://github.com/leanprover/lean4/pull/6723) 完成了 {List/Array/Vector}.{attach,attachWith,pmap} 引理的对齐。我还不得不补齐 `List` API 中的若干空缺。

* [#6728](https://github.com/leanprover/lean4/pull/6728) 移除了定理 `Nat.mul_one`，以简化 `BitVec.getMsbD_rotateLeft_of_lt` 证明中的一次重写。

* [#6742](https://github.com/leanprover/lean4/pull/6742) 添加了若干引理，用来说明任意项乘以 twoPow，以及 `twoPow` 与另一个 `twoPow` 相乘时会发生什么。

* [#6743](https://github.com/leanprover/lean4/pull/6743) 增加了若干重写规则，通过提取比特并连接零来规范化左移。如果移位量大于位宽，那么结果位向量就是零。

* [#6747](https://github.com/leanprover/lean4/pull/6747) 增加了让 `BitVec.extractLsb` 和 `BitVec.extractLsb'` 穿过按位运算的能力。这对对 extract 进行常量折叠很有用。

* [#6767](https://github.com/leanprover/lean4/pull/6767) 添加引理，把由 `BitVec.ofNat` 指定的 `BitVec.shiftLeft,shiftRight,sshiftRight'` 重写为按自然数移位。这将用于把按常量位向量的移位规范化成按常量数值的移位；如果该数值是 2 的幂，还可继续应用进一步的重写。

* [#6799](https://github.com/leanprover/lean4/pull/6799) 为 BitVec 的顶/底元素添加了一些简单比较引理。随后利用它们让 `bv_normalize` 知道 `(a<1) = (a==0)`，并顺带移除了一个不再需要的中间证明。

* [#6800](https://github.com/leanprover/lean4/pull/6800) 统一了 `enum`/`enumFrom`（在 `List` 上）与 `zipWithIndex`（在 `Array` 和 `Vector` 上）的命名，全部替换为 `zipIdx`。同时还进一步泛化，增加了一个可选的 `Nat` 参数来指定索引的初始值（此前这只在 `List` 上以独立函数 `enumFrom` 的形式存在）。

* [#6808](https://github.com/leanprover/lean4/pull/6808) 增加 simp 引理，把 `BitVec.setWidth'` 替换为 `setWidth`，并在适当条件下简化 `setWidth v (setWidth w v)`。

* [#6818](https://github.com/leanprover/lean4/pull/6818) 增加了一个 BitVec 引理 `(x >> x) = 0`，并把支持接入 `bv_normalize`。我还把一些有用的定理移动到了 `ushiftRight` 章节的前面。

* [#6821](https://github.com/leanprover/lean4/pull/6821) 添加了关于 `Ordering` 的基础引理，描述 `isLT`/`isLE`/`isGE`/`isGT`、`swap` 与各构造子之间的相互作用。此外，它还重构了实例派生代码，使 `LawfulBEq Ordering` 实例也能自动派生。

* [#6826](https://github.com/leanprover/lean4/pull/6826) 为那些未能自动获得单射性定理（因为定义得过早）且后来也尚未手动补上的归纳类型添加这些定理。

* [#6828](https://github.com/leanprover/lean4/pull/6828) 为 BitVec 添加了加法/减法的单射性引理，并为 `bv_normalize` 的范式加入了带额外对称性的专门形式。

* [#6831](https://github.com/leanprover/lean4/pull/6831) 完成了 `List/Array/Vector` 上关于 `isEqv` 和 `==` 的引理对齐。

* [#6833](https://github.com/leanprover/lean4/pull/6833) 统一了 `List`/`Array`/`Vector` 上 `find` 系列函数的签名。验证引理将在后续 PR 中补上。

* [#6835](https://github.com/leanprover/lean4/pull/6835) 补齐了 `Vector` API 中的一些空缺，增加了 `mapM`、`zip`，以及 `ForIn'` 和 `ToStream` 实例。

* [#6838](https://github.com/leanprover/lean4/pull/6838) 完成了 `List/Array/Vector.ofFn` 的（有限）验证 API 对齐。

* [#6840](https://github.com/leanprover/lean4/pull/6840) 完成了 `List/Array/Vector.zip/zipWith/zipWithAll/unzip` 引理的对齐。

* [#6845](https://github.com/leanprover/lean4/pull/6845) 为 `List`/`Array`/`Vector` 增加了缺失的单子式高阶函数。目前只提供了最基础的验证引理（用于关联这三种容器类型上的操作）。

* [#6848](https://github.com/leanprover/lean4/pull/6848) 为 BitVec 添加了证明 `x + y = x ↔ x = 0` 的 simp 引理及其对称版本，并将它们加入 bv_normalize simpset。

* [#6860](https://github.com/leanprover/lean4/pull/6860) 让 `List`/`Array`/`Vector` 都具备 `take`/`drop`/`extract`。不过它们的 simp 范式并不相同：在 `List` 中，我们把 `extract` 简化为 `take+drop`；而在 `Array` 与 `Vector` 中，我们把 `take` 和 `drop` 简化为 `extract`。我们还提供了 `Array/Vector.shrink`，它会简化为 `take`，但实现方式是反复弹出元素。关于 `Array/Vector.extract` 的验证引理将在后续 PR 中补上。

* [#6862](https://github.com/leanprover/lean4/pull/6862) 按 Dejan Jovanović 和 Leonardo de Moura 的论文 “Cutting to the Chase: Solving Linear Integer Arithmetic”（DOI 10.1007/s10817-013-9281-x）中的表述，定义了带整除约束的 Cooper 消解。

* [#6863](https://github.com/leanprover/lean4/pull/6863) 通过允许在匹配模式中使用 `x * y`，修复了 nightly-2024-02-25 引入到 mathlib 中的回归。目前 mathlib 中已有 11 处明确标记了这一匹配模式的缺失。

* [#6864](https://github.com/leanprover/lean4/pull/6864) 添加了把 List 和 Array 上的 findIdx?/findFinIdx?/idxOf?/findIdxOf?/eraseP/erase 操作关联起来的引理。这是对齐 `find...` 与 `erase...` 验证引理的前置工作。

* [#6868](https://github.com/leanprover/lean4/pull/6868) 完成了 `List/Array/Vector` 上关于 `eraseP/erase/eraseIdx` 操作的引理对齐。

* [#6872](https://github.com/leanprover/lean4/pull/6872) 添加了关于 xor 的单射性，以及 and/or/xor 何时等于 allOnes 或 zero 的引理。随后我将这些新引理的支持接入了 `bv_normalize`。

* [#6875](https://github.com/leanprover/lean4/pull/6875) 添加了一个关联 `msb` 与 `getMsbD` 的引理，以及三个关于 `getElem` 和 `shiftConcat` 的引理。这些引理在 [Batteries#1078](https://github.com/leanprover-community/batteries/pull/1078) 中被需要，而将其上游化的请求是在该 PR 的 review 中提出的。

* [#6878](https://github.com/leanprover/lean4/pull/6878) 完成了 `List/Array/Vector` 上关于 `range`、`range'` 和 `zipIdx` 的引理对齐。

* [#6883](https://github.com/leanprover/lean4/pull/6883) 完成了 `List/Array/Vector` 上单子式函数引理的对齐。除其他变更外，我们还把 simp 范式从 `List.forM` 改为 `ForM.forM`，并修正了 `List.flatMapM` 的定义；它此前返回结果的顺序是错误的。关于单子式函数的验证引理仍有不少空缺；这个 PR 只是让这些引理在 `List/Array/Vector` 之间保持统一。

* [#6890](https://github.com/leanprover/lean4/pull/6890) 让 `bv_normalize` 学会把等式一侧的减法替换为另一侧的加法。这个重写消除了规范化形式中的某个 not + addition 组合，从而让求解器更容易处理。

* [#6912](https://github.com/leanprover/lean4/pull/6912) 对齐了 `List`/`Array`/`Vector` 上当前已覆盖的 `find` 类定理。这套 API 仍有不少空缺，后续会继续补齐。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Compiler"
%%%

````markdown

* [#6535](https://github.com/leanprover/lean4/pull/6535) 避免了 Windows 上的链接器警告。

* [#6547](https://github.com/leanprover/lean4/pull/6547) 应可防止 Lake 意外拾取机器上安装的其他链接器。

* [#6574](https://github.com/leanprover/lean4/pull/6574) 真实地阻止了 Lake 意外拾取机器上安装的其他工具链。

* [#6664](https://github.com/leanprover/lean4/pull/6664) 修改了 toMono pass，使其不再过滤掉类型类实例，因为后续编译实际上可能需要它们。

* [#6665](https://github.com/leanprover/lean4/pull/6665) 向 Prelude 添加了新的 lcAny 常量，供 LCNF 使用，用来表示那些在编译期间擦除了对其他项依赖的类型。这与现有的 lcErased 常量并列存在；后者表示无关的类型。

* [#6678](https://github.com/leanprover/lean4/pull/6678) 修改 LCNF.toMonoType，使其采用更细致的类型擦除方案，区分无关/已擦除信息（由 lcErased 表示）和已擦除的类型依赖（由 lcAny 表示）。这对应于旧代码生成器中的 irrelevant/object 区分。

* [#6680](https://github.com/leanprover/lean4/pull/6680) 让新代码生成器像旧代码生成器一样，跳过为带有 implemented_by 声明的 decl 生成代码。

* [#6757](https://github.com/leanprover/lean4/pull/6757) 在 toLCNF 中增加了应用 crimp 定理的支持。

* [#6758](https://github.com/leanprover/lean4/pull/6758) 防止了由非循环任务等待引发的死锁；这类死锁原本可能在小线程池规模下的并行精译中出现。

* [#6837](https://github.com/leanprover/lean4/pull/6837) 将 Float32 加入 LCNF 的 builtinRuntimeTypes 列表。这在最初实现 Float32 时被遗漏了，而这一遗漏的副作用是会在 IR 中把 Float32 降级为 obj。

````
# 漂亮打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Pretty-Printing"
%%%

````markdown

* [#6703](https://github.com/leanprover/lean4/pull/6703) 修改了 delaborator，使得在 `pp.tagAppFns` 模式下，广义字段记法会带上头常量的标签。其效果是 docgen 文档会为 dot 记法自动加链接。内部变更：现在格式化后的 `rawIdent` 也可以被加标签。

* [#6716](https://github.com/leanprover/lean4/pull/6716) 将选项 `infoview.maxTraceChildren` 重命名为 `maxTraceChildren`，并把它也应用到命令行驱动和那些缺少信息视图的语言服务器客户端。同时还实现了一个常见约定：选项值为 `0` 表示“不受限制”。

* [#6729](https://github.com/leanprover/lean4/pull/6729) 让带有 `.coeFun` 标签的函数的漂亮打印器遵守 `pp.tagAppFns`。其效果是在 docgen 中，当一个表达式被漂亮打印为 `f x y z` 且 `f` 是一个被强制转换的函数时，如果 `f` 是常量，它就会被自动加链接。

* [#6730](https://github.com/leanprover/lean4/pull/6730) 修改了应用反展开器的调用方式。以前 ref 是 `.missing`，现在则改为头常量的 delaborated syntax。这样一来，当 `pp.tagAppFns` 为真时，应用反展开器里的词元会带上头常量注解。其结果是在 docgen 中，这些词元也会被自动加链接。这一新行为与 `notation` 定义应用反展开器的方式保持一致。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Documentation"
%%%

````markdown

* [#6549](https://github.com/leanprover/lean4/pull/6549) 修复了 #6548。

* [#6638](https://github.com/leanprover/lean4/pull/6638) 更正了定理 `Bitvec.toNat_add_of_lt` 的文档字符串。

* [#6643](https://github.com/leanprover/lean4/pull/6643) 更新了 macOS 文档，说明 Lean 现在需要 pkgconf 才能构建。

* [#6646](https://github.com/leanprover/lean4/pull/6646) 更新了 Ubuntu 文档，说明 Lean 现在需要 pkgconf 才能构建。

* [#6738](https://github.com/leanprover/lean4/pull/6738) 更新了词法结构文档，加入了对新近支持的 ⱼ 的说明；它位于单独的 Unicode 区块中，因此不被当前范围捕获。

* [#6885](https://github.com/leanprover/lean4/pull/6885) 修复了 `HDiv.hDiv` 文档字符串（即悬停在 `/` 上时显示的内容）中截断整数除法函数的名称。该名称已在 #5301 中从 `Int.div` 改为 `Int.tdiv`。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Server"
%%%

````markdown

* [#6597](https://github.com/leanprover/lean4/pull/6597) 修复了信息视图中嵌套跟踪节点的缩进问题。

* [#6794](https://github.com/leanprover/lean4/pull/6794) 修复了一个严重的自动补全性能回归，该回归由 #5666（也就是 v4.14.0）引入。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Lake"
%%%

````markdown

* [#6290](https://github.com/leanprover/lean4/pull/6290) 使用 `StateRefT` 而非 `StateT`，为 Lake 构建单子配备构建存储。

* [#6323](https://github.com/leanprover/lean4/pull/6323) 新增 Lake CLI 命令 `lake query`，既会构建目标，也会输出其结果。它可以生成原始文本或 JSON 格式的输出（使用 `--json` / `-J`）。

* [#6418](https://github.com/leanprover/lean4/pull/6418) 调整所有内建 Lake facet，使其产出 `Job` 对象。

* [#6627](https://github.com/leanprover/lean4/pull/6627) 旨在修复 Mathlib 报告的跟踪问题；这些问题会导致下游项目中的 `lake exe cache` 失效。

* [#6631](https://github.com/leanprover/lean4/pull/6631) 为共享库设置 `MACOSX_DEPLOYMENT_TARGET`（此前只对可执行文件设置）。

* [#6771](https://github.com/leanprover/lean4/pull/6771) 允许从 `JobM` / `SpawnM` 运行 `FetchM`，反之亦然。这使 `fetch` 调用能够异步依赖其他作业的输出。

* [#6780](https://github.com/leanprover/lean4/pull/6780) 让所有 target 和所有 `fetch` 调用都产出某个值的 `Job`。作为这项改动的一部分，facet 定义（例如 `library_data`、`module_data`、`package_data`）和 Lake 类型族（例如 `FamilyOut`）的类型中不应再显式包含 `Job`（因为现在它已成为隐含内容）。

* [#6798](https://github.com/leanprover/lean4/pull/6798) 弃用了 `--update` 选项的 `-U` 简写。

* [#7209](https://github.com/leanprover/lean4/pull/7209) 修复了 Windows 新版 MSYS2 上失效的 Lake 测试。从 MSYS2 0.0.20250221 起，`OSTYPE` 现在报告为 `cygwin` 而不是 `msys`，因此需要在若干 Lake 测试中加以处理。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___17___0-_LPAR_2025-03-03_RPAR_--Other"
%%%

````markdown

* [#6479](https://github.com/leanprover/lean4/pull/6479) 通过使用查找表检查字符串是否需要转义，加快了 JSON 序列化速度。

* [#6519](https://github.com/leanprover/lean4/pull/6519) 添加了一个脚本，利用新的 `changelog-*` 标签和 “...” 约定自动生成发布说明。

* [#6542](https://github.com/leanprover/lean4/pull/6542) 引入了一个脚本，用于自动检查主要下游仓库是否已为新的工具链发布完成更新。

````
