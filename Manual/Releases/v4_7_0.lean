/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.7.0 (2024-04-03)" =>
%%%
tag := "release-v4.7.0"
file := "v4.7.0"
%%%

````markdown
* `simp` 和 `rw` 现在会使用通过合一找到的实例参数，
  而不再总是重新合成。为保持向后兼容，原有行为仍可通过
  `set_option tactic.skipAssignedInstances false` 使用。
  [#3507](https://github.com/leanprover/lean4/pull/3507) 和
  [#3509](https://github.com/leanprover/lean4/pull/3509).

* 当 `pp.proofs` 为 false 时，如今被省略的证明会显示为 `⋯` 而不是 `_`，
  这会在从 Infoview 复制时给出更有帮助的错误消息。
  `pp.proofs.threshold` 选项允许较小的证明始终以漂亮打印形式显示。
  [#3241](https://github.com/leanprover/lean4/pull/3241).

* `pp.proofs.withType` 现在默认设为 false，以减少信息视图中的噪音。

* 应用的漂亮打印器在应用反展开器时，
  现在会自行处理过量应用的情形。
  特别是，``| `($_ $a $b $xs*) => `(($a + $b) $xs*)`` 这一 `app_unexpander` 分支已不再必要。
  [#3495](https://github.com/leanprover/lean4/pull/3495).

* 新增 `simp`（以及 `dsimp`）配置选项：`zetaDelta`。其默认值为 `false`。
  `zeta` 选项默认仍为 `true`，但二者的含义已经改变。
  - 当 `zeta := true` 时，`simp` 和 `dsimp` 会将形如
    `let x := val; e[x]` 的项化简为 `e[val]`。
  - 当 `zetaDelta := true` 时，`simp` 和 `dsimp` 会展开上下文中的 let 变量。
    例如，若上下文中包含 `x := val`，则 `x` 的任意出现都会被替换为 `val`。

  更多细节见 [issue #2682](https://github.com/leanprover/lean4/pull/2682)。下面是一些示例：
  ```
  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp
    /-
    New goal:
    h : z = 9; x := 5 |- x + 4 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    -- Using both `zeta` and `zetaDelta`.
    simp (config := { zetaDelta := true })
    /-
    New goal:
    h : z = 9; x := 5 |- 9 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp [x] -- asks `simp` to unfold `x`
    /-
    New goal:
    h : z = 9; x := 5 |- 9 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp (config := { zetaDelta := true, zeta := false })
    /-
    New goal:
    h : z = 9; x := 5 |- let y := 4; 5 + y = z
    -/
    rw [h]
  ```

* 在向 `simp` 添加新的局部定理时，系统会假定函数应用的参数
  已使用 `no_index` 标注。此修改解决了 [issue #2670](https://github.com/leanprover/lean4/issues/2670)，
  并恢复了用户所期待的 Lean 3 行为。应用此修改后，以下示例现在可以工作：
  ```
  example {α β : Type} {f : α × β → β → β} (h : ∀ p : α × β, f p p.2 = p.2)
    (a : α) (b : β) : f (a, b) b = b := by
    simp [h]

  example {α β : Type} {f : α × β → β → β}
    (a : α) (b : β) (h : f (a,b) (a,b).2 = (a,b).2) : f (a, b) b = b := by
    simp [h]
  ```
  在这两种情形下，`h` 都可用，因为 `simp` 在把 `h` 加入 `simp` 集时
  不再为 f 的参数建立索引。不过，需要注意的是，全局定理仍会按通常方式建立索引。

* 改进了 `decide` 策略产生的错误消息。 [#3422](https://github.com/leanprover/lean4/pull/3422)

* 改进了自动补全性能。 [#3460](https://github.com/leanprover/lean4/pull/3460)

* 改进了语言服务器初始启动性能。 [#3552](https://github.com/leanprover/lean4/pull/3552)

* 调整了调用层次结构：现在会对条目排序，并去掉显示名称中的私有前缀。 [#3482](https://github.com/leanprover/lean4/pull/3482)

* 解析框架现在提供了一个底层的错误恢复组合子，主要面向 DSL。 [#3413](https://github.com/leanprover/lean4/pull/3413)

* 现在可以在声明后写 `termination_by?`，以查看自动推断出的
  终止性参数，并借助 “Try this” 小部件或代码操作将其转成 `termination_by …` 子句。 [#3514](https://github.com/leanprover/lean4/pull/3514)

* `Std` 的很大一部分现已移入 Lean 仓库。
  其动机包括：
  1. 让普遍有用的策略，如 `ext`、`by_cases`、`change at`、
     `norm_cast`、`rcases`、`simpa`、`simp?`、`omega` 和 `exact?`，
     可供所有 Lean 用户使用，而无需导入。
  2. 尽量减少纯 Lean 与带 `import Std` 的 Lean 之间的语法差异。
  3. 简化基本数据类型
     `Nat`、`Int`、`Fin`（及其变体，如 `UInt64`）、`List`、`Array`
     和 `BitVec` 的开发流程，因为我们开始让这些类型的 API 与 simp 规范形
     更加完整且一致。
  4. 为 Std 路线图奠定基础，使其成为一个专注于核心语言未提供的基础数据类型
     （例如 `RBMap`）以及基本 IO 等实用工具的库。
  虽然我们在 `v4.7.0-rc1` 中已实现大部分初始目标，
  但未来几个月仍会继续进行上游迁移。

* `Int` 中的 `/` 和 `%` 记法现在使用 `Int.ediv` 和 `Int.emod`
  （也就是说，舍入约定已发生变化）。
  之前 `Std` 会覆盖这些记法，因此这对 `Std` 用户来说没有变化。
  现在内核也已支持这些函数。
  [#3376](https://github.com/leanprover/lean4/pull/3376).

* `omega`——我们的整数线性算术策略——现在已在核心语言中可用。
  * 它还配有一个预处理策略 `bv_omega`，可用于解决关于 `BitVec` 的目标，
    这些目标能够自然地转化为线性算术问题。
    [#3435](https://github.com/leanprover/lean4/pull/3435).
  * `omega` 现已支持 `Fin` [#3427](https://github.com/leanprover/lean4/pull/3427)
    以及 `<<<` 运算符 [#3433](https://github.com/leanprover/lean4/pull/3433)。
  * 在移植过程中，`omega` 被修改为不再按定义相等识别原子
    （因此特别地，它现在无法再证明 `id x ≤ x`）。 [#3525](https://github.com/leanprover/lean4/pull/3525)。
    这可能会造成一些回归。
    我们计划之后提供一个通用的预处理策略，或一个 `omega!` 模式。
  * `omega` 现在也会在 Lean 的终止证明自动化中调用
    [#3503](https://github.com/leanprover/lean4/pull/3503)，以及数组索引证明中调用 [#3515](https://github.com/leanprover/lean4/pull/3515)。
    这套自动化将在中期进行较大调整；
    尽管 `omega` 的确有助于自动化部分证明，我们仍计划让它稳健得多。

* 最初位于 Mathlib 中的库搜索策略 `exact?` 和 `apply?`
  现在也已在 Lean 本身中提供。这些策略使用了来自 `Std` 的惰性判别树实现，
  因而不需要磁盘缓存，但启动时间会略长一些。用于选择引理的排序也已改变，
  改为纯粹依据头部模式中有多少项匹配当前目标来偏好目标。

* `solve_by_elim` 策略已从 `Std` 移植到 Lean，以便库搜索可以使用它。

* 新增了 `#check_tactic` 和 `#check_simp` 命令。
  它们对于在测试套件中检查策略（尤其是 `simp`）是否按预期工作很有用。

* 以前，应用反展开器只会应用于整个应用式。然而，一些记法会产生函数，
  而这些函数还可以再接受额外参数。到目前为止，解决办法一直是编写能够接受
  任意数量额外参数的应用反展开器。但这会在 Infoview 中造成误导性的悬停信息。
  例如，虽然 `HAdd.hAdd f g 1` 会被漂亮打印为 `(f + g) 1`，
  把鼠标悬停在 `f + g` 上却会显示 `f`。这个问题无法在应用反展开器内部修复；
  `HAdd.hAdd f g` 这一表达式位置并不存在，而且应用反展开器也无法注册 TermInfo。

  此次提交修改了 app 反精译器：它会对一个应用式的每个前缀都尝试运行
  应用反展开器，从最长前缀一直试到最短前缀。出于效率考虑，
  它只会在该头常量确实存在 app 反精译器时才这样做，并且还确保参数只会被反精译一次。
  这样一来，在 `(f + g) 1` 中，`f + g` 这个子表达式就会注册 TermInfo，
  从而可以正确悬停。

  [#3375](https://github.com/leanprover/lean4/pull/3375)

破坏性变更：
* `Lean.withTraceNode` 及其变体现在要求更强的 `MonadAlwaysExcept` 假设，
  以修复在精译运行时异常时不会构建跟踪树的问题。对于大多数基于 `EIO Exception`
  的精译单子，实例都应当能自动合成。
* 先前位于 Std 中的 `match ... with.` 与 `fun.` 记法已被
  `nomatch ...` 和 `nofun` 取代。 [#3279](https://github.com/leanprover/lean4/pull/3279) 以及 [#3286](https://github.com/leanprover/lean4/pull/3286)


其他改进：
* `simp` 的若干错误修复：
  * `simp` 循环时不应崩溃 [#3269](https://github.com/leanprover/lean4/pull/3269)
  * `simp` 在 `autoParam` 上卡住 [#3315](https://github.com/leanprover/lean4/pull/3315)
  * 当自定义 discharger 没有取得进展时，`simp` 会失败 [#3317](https://github.com/leanprover/lean4/pull/3317)
  * 即使能够将 `autoParam` 前提化简为 `True`，`simp` 仍无法消解它们 [#3314](https://github.com/leanprover/lean4/pull/3314)
  * `simp?` 建议生成的方程引理名称，修复见 [#3547](https://github.com/leanprover/lean4/pull/3547) [#3573](https://github.com/leanprover/lean4/pull/3573)
* `match` 表达式的修复：
  * 修复内建字面量上的回归 [#3521](https://github.com/leanprover/lean4/pull/3521)
  * 当模式覆盖 `BitVec` 有限类型的所有情况时接受 `match` [#3538](https://github.com/leanprover/lean4/pull/3538)
  * 修复对 `Int` 字面量的匹配 [#3504](https://github.com/leanprover/lean4/pull/3504)
  * 修复包含整数值与构造子的模式 [#3496](https://github.com/leanprover/lean4/pull/3496)
* 改进 `termination_by` 的错误消息 [#3255](https://github.com/leanprover/lean4/pull/3255)
* 修复宏中的 `rename_i`，修复见 [#3553](https://github.com/leanprover/lean4/pull/3553) [#3581](https://github.com/leanprover/lean4/pull/3581)
* 修复 `generalize` 中过度的资源占用，修复见 [#3524](https://github.com/leanprover/lean4/pull/3524) [#3575](https://github.com/leanprover/lean4/pull/3575)
* 带 autoParam 参数的方程引理无法重写，修复见 [#2243](https://github.com/leanprover/lean4/pull/2243) [#3316](https://github.com/leanprover/lean4/pull/3316)
* `add_decl_doc` 应检查声明是否为局部声明 [#3311](https://github.com/leanprover/lean4/pull/3311)
* 以正确参数实例化归纳类型的类型，关闭 [#3242](https://github.com/leanprover/lean4/pull/3242) [#3246](https://github.com/leanprover/lean4/pull/3246)
* 为许多基本类型新增 simprocs。 [#3407](https://github.com/leanprover/lean4/pull/3407)

Lake 修复：
* 在获取云端发布失败时给出警告 [#3401](https://github.com/leanprover/lean4/pull/3401)
* 修复云端发布跟踪与 `lake build :release` 错误 [#3248](https://github.com/leanprover/lean4/pull/3248)
````
