/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0 (2023-09-08)" =>
%%%
tag := "release-v4.0.0"
file := "v4.0.0"
%%%

````markdown
* [`Lean.Meta.getConst?` 已重命名](https://github.com/leanprover/lean4/pull/2454)。
  我们将 `getConst?` 重命名为 `getUnfoldableConst?`（并将 `getConstNoEx?` 重命名为 `getUnfoldableConstNoEx?`）。
  它们原本并不打算成为公共 API 的一部分，但下游项目一直错误地用它们来代替 `Lean.getConstInfo`
  （有时还期待不同的行为）。

* [`dsimp` / `simp` / `simp_all` 现在在没有任何进展时默认失败](https://github.com/leanprover/lean4/pull/2336)。

  可以通过 `(config := { failIfUnchanged := false })` 选项覆盖此行为。
  这一改动旨在让手工使用 `simp` 更容易（目标复杂时，很难判断它是否真的起效），
  也便于在内部使用 `simp` 的策略中更轻松地控制流程。
  更多细节可参见 Zulip 上的[总结讨论](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/simp.20fails.20if.20no.20progress/near/380153295)。

* [`simp_all` 现在会保留假设顺序](https://github.com/leanprover/lean4/pull/2334)。

  为了支持 `dsimp` / `simp` / `simp_all` 的 `failIfUnchanged` 配置选项，
  `simp_all` 替换假设的方式已经改变。
  特别是，它现在更有可能保留假设原有的顺序。
  参见 [`simp_all` 会不必要地重排假设](https://github.com/leanprover/lean4/pull/2334)。
  （以前所有非依赖的命题假设都会被回退并重新引入。
  现在只有那些被修改的假设，或位于被修改假设之后的此类假设，
  才会被回退并重新引入。
  这样会保留非依赖命题假设彼此之间的顺序，
  但现在任何依赖型假设或非命题假设，都会在未改动的非依赖命题假设之间保留其原本位置。）
  这可能会影响使用 `rename_i`、`case ... =>` 或 `next ... =>` 的证明。

* [新的 `have this` 实现](https://github.com/leanprover/lean4/pull/2247)。

  `this` 现在再次成为普通标识符，它会在匿名 `have :=` 之后，隐式引入并在策略块剩余部分可见。过去它是一个在所有作用域中都可见的关键字，因此在显式用作绑定器名时会导致意外行为。

* [在性能分析输出中显示类型类与策略名称](https://github.com/leanprover/lean4/pull/2170)。

* [要求 `calc` 中关系列/证明列具有相同缩进](https://github.com/leanprover/lean4/pull/1844)，
  并且[为 `calc` 添加替代语法，允许在第一条关系中使用下划线 `_`](https://github.com/leanprover/lean4/pull/1844)。

  `calc` 中灵活的缩进过去常被用来对齐关系符号：
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
        (x + y) * (x + y) = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
                        -- improper indentation
                        _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
                        _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
                        _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```

  这种写法现在已不再合法。新语法将第一项直接写在 `calc` 后面，并要求每一步具有相同的缩进：
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```


* 将 Lake 更新到最新预发布版本。

* [让类型类投影应用上的“跳转到定义”跳到实例](https://github.com/leanprover/lean4/pull/1767)。

* [当 `profiler` 为 true 时，在跟踪消息中包含耗时](https://github.com/leanprover/lean4/pull/1995)。

* [在悬停信息和 `#check <ident>` 中美观打印签名](https://github.com/leanprover/lean4/pull/1943)。

* [引入解析器记忆化以避免指数级行为](https://github.com/leanprover/lean4/pull/1799)。

* [功能：在 `let x <- e | seq` 中允许 `doSeq`](https://github.com/leanprover/lean4/pull/1809)。

* [为选项添加悬停 / 跳转到定义 / 查找引用](https://github.com/leanprover/lean4/pull/1783)。

* [添加空类型标注语法 `(e :)`](https://github.com/leanprover/lean4/pull/1797)。

* [使 `<|>` 中的词元会影响语法匹配](https://github.com/leanprover/lean4/pull/1744)。

* [添加 `linter.deprecated` 选项以静默弃用警告](https://github.com/leanprover/lean4/pull/1768)。

* [改进模糊匹配启发式](https://github.com/leanprover/lean4/pull/1710)。

* [实现细节假设](https://github.com/leanprover/lean4/pull/1692)。

* [`cases`/`induction` 分支名的悬停信息](https://github.com/leanprover/lean4/pull/1660)。

* [即使解析失败，也优先选择更长的解析结果](https://github.com/leanprover/lean4/pull/1658)。

* [在悬停信息中显示声明所在模块](https://github.com/leanprover/lean4/pull/1638)。

* [新的 `conv` 模式结构化策略](https://github.com/leanprover/lean4/pull/1636)。

* `simp` 现在可以跟踪信息，并打印等价的 `simp only`。 [PR #1626](https://github.com/leanprover/lean4/pull/1626)。

* 强制策略块 / do 块使用统一缩进。参见 issue [#1606](https://github.com/leanprover/lean4/issues/1606)。

* 将 `AssocList`、`HashMap`、`HashSet`、`RBMap`、`RBSet`、`PersistentArray`、`PersistentHashMap`、`PersistentHashSet` 移入 Lean 包中。[标准库](https://github.com/leanprover/std4)中保留了会独立演进的版本，以简化自举过程。

* 标准库已迁移到 [std4 GitHub 仓库](https://github.com/leanprover/std4)。

* `InteractiveGoals` 现在携带了客户端信息视图可用的信息，以显示应用策略后目标的哪些部分发生了变化。[PR #1610](https://github.com/leanprover/lean4/pull/1610)。

* 添加 `[inheritDoc]` 属性。[PR #1480](https://github.com/leanprover/lean4/pull/1480)。

* 显式说明 `panic = default`。[PR #1614](https://github.com/leanprover/lean4/pull/1614)。

* 新的[代码生成器](https://github.com/leanprover/lean4/tree/master/src/Lean/Compiler/LCNF)项目已经启动。

* 从 `register_simp_attr` 中移除描述参数。[PR #1566](https://github.com/leanprover/lean4/pull/1566)。

* [额外的并发原语](https://github.com/leanprover/lean4/pull/1555)。

* [带消息的可折叠跟踪](https://github.com/leanprover/lean4/pull/1448)。

* [命名空间的卫生解析](https://github.com/leanprover/lean4/pull/1442)。

* [新的 `Float` 函数](https://github.com/leanprover/lean4/pull/1460)。

* `Init` 中的声明新增了许多文档字符串。

````
