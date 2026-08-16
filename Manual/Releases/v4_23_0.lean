/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.23.0 (2025-09-15)" =>
%%%
tag := "release-v4.23.0"
file := "v4.23.0"
%%%

````markdown
本次发布共合入 610 项变更。除下文列出的 95 项功能新增和 139 项修复外，还有 61 项重构、12 项文档改进、71 项性能改进，以及 232 项其他改动。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Highlights"
%%%

````markdown

Lean v4.23.0 带来了显著的性能改进、更好的错误消息，以及 `grind`、编译器和 Lean 其他组件中的大量错误修复、打磨与整合。

就用户体验而言，值得注意的新特性包括：

- 改进的 “Go to Definition” 导航（[#9040](https://github.com/leanprover/lean4/pull/9040)）

  - 对类型类投影使用 “Go to Definition” 时，现在会提取参与其中的具体实例，并将它们作为可跳转的位置提供。例如，对 `toString 0` 中的 `toString` 使用该功能，会返回 `ToString.toString` 和 `ToString Nat`。
  - 对会生成带有类型类投影语法之宏使用 “Go to Definition” 时，现在也会提取参与其中的具体实例，并将它们作为可跳转的位置提供。例如，对 `1 + 1` 中的 `+` 使用该功能，会返回 `HAdd.hAdd`、`HAdd α α α` 和 `Add Nat`。
  - “Go to Declaration” 现在除了给出参与其中的精译器和解析器外，也会提供 “Go to Definition” 的全部结果。例如，对 `1 + 1` 中的 `+` 使用它，会返回 `HAdd.hAdd`、`HAdd α α α`、`Add Nat`、`` macro_rules | `($x + $y) => ... `` 以及 `infixl:65 " + " => HAdd.hAdd`。
  - 对类型中包含多个常量的值使用 “Go to Type Definition” 时，现在会为每个常量提供 “Go to Definition” 的结果。例如，对 `x : Array Nat` 中的 `x` 使用它，会返回 `Array` 和 `Nat`。

- 面向错误的交互式代码动作提示：

  - 对于 “invalid named argument” 错误，建议合法的参数名（[#9315](https://github.com/leanprover/lean4/pull/9315)）

  - 对于 “invalid case name” 错误，建议合法的分支名（[#9316](https://github.com/leanprover/lean4/pull/9316)）

  - 对于结构实例中的 “fields missing” 错误，建议插入全部缺失字段（[#9317](https://github.com/leanprover/lean4/pull/9317)）

你可以在 [Lean playground](https://live.lean-lang.org/#codez=PQWghAUAxABAEgSwHYBcDOMBmB7ATjZANwEMAbBAExiWIFsBTK43AcwFcHUNkYAHYlCnq4kaCCGAQIyCmwDGKBIXowAKjADuAC2H0IMGAB8YtANYBGGAAoAHjACeMAF4wAXDABC2bKQCUU+hs6XlIVKxQ3NV83AF59EwE5LRgIjQQULXjjADozSytHVxiU3DZ6aKsNWJKyipcirDI0cpgYgD5rfylQSFhELiw8GDliZuo6ejEJAKDaELCAI0ivH2j3ADkBaoX7eJHmjAW90ZUkbCRAhDQhVFa2+IM0UwRebvBoeGR0QfxaK7RkCwYNdSgo2LgVMhrsQkHIVJgEPRSBQppIICD5ChwSoAMqaHQQ+IIpEUSwbARExHIgBMkQAavQFENNhFicjzDNgqFIniivEAN4AXwgQA) 中尝试以上所有功能。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Highlights--Breaking-Changes"
%%%

````markdown

- [#9800](https://github.com/leanprover/lean4/pull/9800) 改进了 delta 派生处理器，使其能够处理带绑定器的定义，也能够递归地展开定义。**破坏性变更：** 派生实例的名称会使用 `instance` 命令的名称生成器，而新实例会被加入当前命名空间。

- [#9040](https://github.com/leanprover/lean4/pull/9040) 改进了 “Go to Definition” 的用户体验。**破坏性变更：** `InfoTree.hoverableInfoAt?` 已被泛化为 `InfoTree.hoverableInfoAtM?`；它现在接收一个通用的 `filter` 参数，而不再像以前那样携带若干布尔标志。

- [#9594](https://github.com/leanprover/lean4/pull/9594) 优化了 `Lean.Name.toString`，带来约 10% 的指令数收益。

  关键的是，这是一项**破坏性变更**：旧版 `Lean.Name.toString` 以前还承担了标识词法单元的功能。这个功能现在改由 `Lean.Name.toStringWithToken` 提供，从而可以专门优化极其常见的 `toString` 路径；在该路径上，这个函数只需返回 `false`。

- [#9729](https://github.com/leanprover/lean4/pull/9729) 引入了一种为类型赋予序结构的规范方式。**破坏性变更：**

  - `Vector`、`List` 与 `Array` 上 `lt_of_le_of_lt`/`le_trans` 这些引理的前提被简化了：它们现在要求一个 `IsLinearOrder` 实例。新前提在逻辑上与旧前提等价，但 `IsLinearOrder` 实例不会从更小的类型类自动推导出来。
  - 类型为 `Std.Total (¬ · < · : α → α → Prop)` 的假设会被等价的类型类 `Std.Asymm (· < · : α → α → Prop)` 取代。由于现在已经有实例能从前者导出后者，所以破坏面应当有限。
  - 在 `Init.Data.List.MinMax` 中，多个定理签名被修改：显式的反对称性、总性、`min_ex_or` 等参数都被替换成了对应的实例参数。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Language"
%%%

````markdown

* [#6732](https://github.com/leanprover/lean4/pull/6732) 为转换模式加入了对 `clear` 策略的支持。

* [#8666](https://github.com/leanprover/lean4/pull/8666) 调整了实验性模块系统，使其不再导入非 `meta` 声明的 IR。它通过在导出时用不透明的外部声明替换这类 IR，并相应调整新编译器来实现这一点。

* [#8842](https://github.com/leanprover/lean4/pull/8842) 修复了 `collectAxioms` 不会收集“被其他公理引用之公理”的错误。该错误的一个后果是：从用 `native_decide` 证明的定理中收集到的公理，可能不包含 `Lean.trustCompiler`。

* [#9015](https://github.com/leanprover/lean4/pull/9015) 让 `isDefEq` 能检测出更多因“智能展开”而卡住的定义等同性。具体来说，如果 `t =?= defn ?m` 且 `defn` 会对其参数做匹配，那么这个等式就会卡在 `?m` 上；在这项改动之前，我们看不到这种依赖，只会直接返回 `false`。

* [#9084](https://github.com/leanprover/lean4/pull/9084) 为 `Init.Core` 中定义的 `!=` 与 `≠` 记号添加了 `binrel%` 宏。这使精译器能够在关系两侧都插入强制转换，而不是直接固定左手边的类型。

* [#9090](https://github.com/leanprover/lean4/pull/9090) 修复了 `whnfCore` 中一个错误：它原本可能无法约化递归器/辅助定义的应用。

* [#9097](https://github.com/leanprover/lean4/pull/9097) 确保 `mspec` 使用已配置的透明度设置，并让 `mvcgen` 在调用 `mspec` 时使用默认透明度。

* [#9099](https://github.com/leanprover/lean4/pull/9099) 改进了 “expected type mismatch” 错误消息：当两边“类型的类型”在定义上相等时就省略它们；若不相等，则分成单独的行显示。

* [#9103](https://github.com/leanprover/lean4/pull/9103) 防止 `panic!` 中包含空字节时消息被截断。

* [#9108](https://github.com/leanprover/lean4/pull/9108) 修复了一个问题：它可能导致消息中的内联表达式被不必要地渲染到单独一行。

* [#9113](https://github.com/leanprover/lean4/pull/9113) 改进了 `grind` 的文档字符串，并尝试让它对新用户更有用。

* [#9130](https://github.com/leanprover/lean4/pull/9130) 修复了 `Grind.offset` 辅助项意外出现在基模式中的问题。详见新增测试。

* [#9131](https://github.com/leanprover/lean4/pull/9131) 为 `LocalContext.mkLambda` 与 `LocalContext.mkForall` 添加了 `usedLetOnly` 参数，以与 `MetavarContext` 版本保持一致。

* [#9133](https://github.com/leanprover/lean4/pull/9133) 在 `grind` 归一化器中加入了对 `a^(m+n)` 的支持。

* [#9143](https://github.com/leanprover/lean4/pull/9143) 清除了模块系统中的一个相当丑陋的权宜实现，从而暴露出那些类型提到 `WellFounded` 的定理之定义体。

* [#9146](https://github.com/leanprover/lean4/pull/9146) 在 `grind ring` 中加入了“安全”的多项式操作。它们使用通常的组合器：`withIncRecDepth` 与 `checkSystem`。

* [#9149](https://github.com/leanprover/lean4/pull/9149) 将 `a^(m+n)` 的 `grind` 归一化器推广到任意半环。示例：
  ```
  variable [Field R]

* [#9150](https://github.com/leanprover/lean4/pull/9150) 在 `grind` 使用的 `toPoly` 函数中补上了一个缺失分支。

* [#9153](https://github.com/leanprover/lean4/pull/9153) 改进了 linarith 的 `markVars`，并确保它不会产生伪造的问题消息。

* [#9168](https://github.com/leanprover/lean4/pull/9168) 解决了一个 defeq 菱形问题，它曾在 Mathlib 中引发问题：
  ```
import Mathlib

* [#9172](https://github.com/leanprover/lean4/pull/9172) 修复了 `matchEqBwdPat` 中的一个错误：类型里可能包含模式变量。

* [#9173](https://github.com/leanprover/lean4/pull/9173) 修复了实验性模块系统中的一个不兼容问题：当试图把良基递归与公开暴露的定义结合使用时会出错。

* [#9176](https://github.com/leanprover/lean4/pull/9176) 让 `mvcgen` 对 `if` 做拆分，而不是应用规格。这样修复了 Rish 报告的一个错误。

* [#9182](https://github.com/leanprover/lean4/pull/9182) 尝试改进 `grind` 的 E-匹配模式推断。尽管如此，我们仍然需要更好的工具来为库中的 `grind` 标注做注释和维护。

* [#9184](https://github.com/leanprover/lean4/pull/9184) 修复了新的总后置条件记号“抢占” `⇓` 语法的问题：把它降格为非内建语法，并把作用域限制在 `Std.Do` 中。

* [#9191](https://github.com/leanprover/lean4/pull/9191) 如果抽象后的证明原本会遮蔽递归调用，就让方程编译器重新展开它们。这修复了 #8939。

* [#9193](https://github.com/leanprover/lean4/pull/9193) 修复了 issue #9187 报告的意外内核投影问题。

* [#9194](https://github.com/leanprover/lean4/pull/9194) 让 `Std.Do` 的逻辑与策略在宇宙层面上实现多态化，其代价是失去了一些定义性质；这些定义性质原本来自把基例 `SPred []` 从 `Prop` 切换到 `ULift Prop`。

* [#9196](https://github.com/leanprover/lean4/pull/9196) 在 `grind` 中使用 simproc 而不是重写规则来实现 `forall` 归一化。这只是该 PR 的第一部分；待第 0 阶段更新后，我们必须移除那些归一化定理。

* [#9200](https://github.com/leanprover/lean4/pull/9200) 在 `grind` 中使用 simproc 而不是重写规则来实现 `exists` 归一化。这只是该 PR 的第一部分；待第 0 阶段更新后，我们必须移除那些归一化定理。

* [#9202](https://github.com/leanprover/lean4/pull/9202) 扩展了 `grind` 所使用的 `Eq` simproc。它现在覆盖更多情况，并在要展开的声明列表中新增了 3 个可约声明。

* [#9214](https://github.com/leanprover/lean4/pull/9214) 实现了对局部 `grind_pattern` 命令和 scoped `grind_pattern` 命令的支持。

* [#9225](https://github.com/leanprover/lean4/pull/9225) 改进了 `congr` 策略，使它能够处理参数个数少于头函数元数的函数应用。这也修复了 `congr` 在 Mathlib 中面对取值于 `Set` 的函数时无法推进的问题，因为 `Set` 会被展开，从而让这类函数看起来像具有更高元数。

* [#9228](https://github.com/leanprover/lean4/pull/9228) 通过按需生成所需类型类，改进了 `grind ring` 的启动时间。这项优化对会数百次调用 `grind` 的文件尤其相关，例如 `tests/lean/run/grind_bitvec2.lean`。例如，在这项改动之前，`grind` 在合成类型类上会花 6.87 秒；在这个 PR 之后则为 3.92 秒。

* [#9241](https://github.com/leanprover/lean4/pull/9241) 确保用于实现 `ToInt` 适配器（在 `grind cutsat` 中）的类型类实例会按需生成。

* [#9244](https://github.com/leanprover/lean4/pull/9244) 改进了 `grind linarith` 模块中的实例生成。

* [#9251](https://github.com/leanprover/lean4/pull/9251) 在 #9015 的 DefEq 改进之后，把 `Std.Do.PostCond.total` 与 `Std.Do.Triple` 的内建精译器降格为宏。

* [#9267](https://github.com/leanprover/lean4/pull/9267) 优化了 `grind` 对 `Decidable` 实例的支持。由于 `Decidable` 是子单例，规范化器不再浪费时间去归一化这些实例；在 `grind_bitvec2.lean` 之类基准中，这曾是一个显著的性能瓶颈。另外，一致闭包模块现在也会处理 `Decidable` 实例，并能解出如下例子：
  ```lean
  example (p q : Prop) (h₁ : Decidable p) (h₂ : Decidable (p ∧ q)) : (p ↔ q) → h₁ ≍ h₂ := by
    grind
  ```

* [#9271](https://github.com/leanprover/lean4/pull/9271) 改进了 `grind` 所用公式归一化器的性能。

* [#9287](https://github.com/leanprover/lean4/pull/9287) 重写了 “application type mismatch” 错误消息，使参数及其类型出现在应用表达式之前。

* [#9293](https://github.com/leanprover/lean4/pull/9293) 用一个高效得多的版本替换了 `grind` 中使用的 `reduceCtorEq` simproc。`simp` 中默认使用的那个版本在这里纯属额外开销，因为 `grind` 的归一化器已经会做算术归一化。后续我们会在单独的 PR 中把这些性能改进推回默认的 `reduceCtorEq`。

* [#9305](https://github.com/leanprover/lean4/pull/9305) 在 `simp` 中使用 `mkCongrSimpForConst?` API，以减少重复生成同一个 congruence 引理的次数。在这个 PR 之前，`grind` 在 `grind_bitvec2.lean` 基准的归一化阶段会花费 `1.5`s 来生成同余定理；现在降到了 `0.6`s。等我们合并 #9300 后，这一改动的效果还会更明显。

* [#9315](https://github.com/leanprover/lean4/pull/9315) 改进了函数应用与匹配模式中的 “invalid named argument” 错误消息：它会给出包含合法参数名的可点击提示。同时，它还修复了一个问题：这条错误消息此前会错误地把合法的匹配模式参数名标记为错误。

* [#9316](https://github.com/leanprover/lean4/pull/9316) 为 “invalid case name” 错误消息添加了可点击的代码动作提示。

* [#9317](https://github.com/leanprover/lean4/pull/9317) 为结构实例记号中的 “fields missing” 错误消息添加了代码动作提示，该提示会插入全部缺失字段。

* [#9324](https://github.com/leanprover/lean4/pull/9324) 改进了 `grind` 中用于检查两个项是否不相等的函数。

* [#9325](https://github.com/leanprover/lean4/pull/9325) 优化了 `grind` 中使用的布尔不等性传播器。

* [#9326](https://github.com/leanprover/lean4/pull/9326) 优化`grind` 所使用的`propagateEqUp`。

* [#9340](https://github.com/leanprover/lean4/pull/9340) 修改了 `grind cutsat` 中使用的从 `Nat` 到 `Int` 的编码。它更简单、更可扩展，也与通用的 `ToInt` 相似。在更新第 0 阶段后，我们将能删除遗留部分。

* [#9351](https://github.com/leanprover/lean4/pull/9351) 优化了 `grind` 的预处理步骤：当某个项已经出现在哈希驻留表中时，就会跳过相应步骤。

* [#9358](https://github.com/leanprover/lean4/pull/9358) 增加了对生成格论（协）归纳证明原理的支持，适用于通过 `mutual` 块并使用 `inductive_fixpoint`/`coinductive_fixpoint` 构造定义的谓词。

* [#9367](https://github.com/leanprover/lean4/pull/9367) 对 `grind` 预处理器做了一项小优化。

* [#9369](https://github.com/leanprover/lean4/pull/9369) 通过在可能时跳过不必要步骤，优化了 `grind` 预处理器。

* [#9371](https://github.com/leanprover/lean4/pull/9371) 修复了一个问题：当正在声明的类型名称与某个打开命名空间中的声明同名时，会导致某些 `deriving` 处理器失败。

* [#9372](https://github.com/leanprover/lean4/pull/9372) 修复了一个性能问题：当为使用了包含多个字面量之 match 表达式的函数生成方程引理时，会出现该问题。这个问题由 #9322 暴露出来，其成因包括：

1. 字面量会被编译成一串依赖型条件表达式。
2. 依赖型条件表达式的化简代价远高于普通版本。
3. `split` 策略会先选择目标并把它拆开，然后对生成的子目标调用 `simp`；而且 `simp` 会自底向上遍历整个目标，到达目标位置后也不会停止。

* [#9385](https://github.com/leanprover/lean4/pull/9385) 替换了 `grind` 中 `simpEq` simproc 使用的 `isDefEq` 测试。它的开销太大了。

* [#9386](https://github.com/leanprover/lean4/pull/9386) 改进了试图从零字段结构中做投影时产生的一条令人困惑的错误消息。

* [#9387](https://github.com/leanprover/lean4/pull/9387) 在 “invalid projection” 消息中加入了一个提示：对于形如 `t.n` 的表达式，如果 `t` 是元组且 `n > 2`，会建议正确的嵌套投影写法。

* [#9395](https://github.com/leanprover/lean4/pull/9395) 修复了 `mkCongrSimpCore?` 中的一个错误，也就是 @joehendrix 在 #9388 中报告的问题。实际修复只有提交 `afc4ba617fe2ca5828e0e252558d893d7791d56b`；该 PR 的其余部分只是清理文件。

* [#9398](https://github.com/leanprover/lean4/pull/9398) 避免了 `simpArith` 中代价高昂的 `inferType` 调用。它还清理了一些代码并移除了反模式。

* [#9408](https://github.com/leanprover/lean4/pull/9408) 实现了一个简单优化：依赖蕴含不再被长期当作 `grind` 中的 E-匹配定理。在 `grind_bitvec2.lean` 中，这项改动节省了大约 3 秒，因为会生成大量依赖蕴含。示例：
  ```lean
   ∀ (h : i + 1 ≤ w), x.abs.getLsbD i = x.abs[i]
   ```

* [#9414](https://github.com/leanprover/lean4/pull/9414) 增加了 `isArrowProposition` 返回 `.undef` 以外结果的情形数量。这个函数用于实现 `isProof` 谓词，而 `simp` 会对访问到的每个子项调用它。

* [#9421](https://github.com/leanprover/lean4/pull/9421) 修复了一个错误：它会让错误解释在 Lean 网页编辑器里“偷走” Infoview 的容器。

* [#9423](https://github.com/leanprover/lean4/pull/9423) 更新了 “unknown identifier” 错误的格式，并为绑定器与定义上的 “failed to infer type” 错误补充了解释。

* [#9424](https://github.com/leanprover/lean4/pull/9424) 改进了 `split` 策略产生的错误消息，包括给出语法修正建议，以及提示可能与之混淆的相关策略。

* [#9443](https://github.com/leanprover/lean4/pull/9443) 让 cdot 函数扩展把 hygiene 信息考虑在内，修复了 “parenthesis capturing” 错误；这类错误会使错误的 cdot 与宏结合时触发 cdot 扩展。例如，给定
  ```lean
  macro "baz% " t:term : term => `(1 + ($t))
  ```
`baz% ·` 过去会展开为 `1 + fun x => x`，但现在 `($t)` 中的括号不会再捕获 cdot。我们还修复了另一个疏漏：cdot 函数扩展此前忽略了类型标注和元组本应界定扩展边界这一事实；同时，引号预检查器现在也会忽略 `hygieneInfo` 中的标识符。（#9491 向括号与 cdot 语法加入了 hygiene 信息。）

* [#9447](https://github.com/leanprover/lean4/pull/9447) 确保 `mvcgen` 不仅会尝试通过假设关闭带状态的子目标，也会尝试关闭纯 Lean 目标。

* [#9448](https://github.com/leanprover/lean4/pull/9448) 处理了 #9018 报告的 Lean 崩溃（栈溢出）问题；该问题出现在嵌套归纳以及生成 `SizeOf` 规格引理时。

* [#9451](https://github.com/leanprover/lean4/pull/9451) 为 `mintro` 策略添加了在带状态目标中引入 `let`/`have` 绑定器的支持，行为类似 `intro`。当规格引入这类 `let` 绑定时，这一功能很有用。

* [#9454](https://github.com/leanprover/lean4/pull/9454) 引入了策略 `mleave`，它会通过穿过抽象做 eta 展开并施加一些温和的化简来退出 `SPred` 证明模式。这有助于随后应用诸如 `grind` 的自动化。

* [#9464](https://github.com/leanprover/lean4/pull/9464) 让 `PProdN.reduceProjs` 也去查找投影函数。此前，所有可约 redex 都由 `PProdN` 中的函数创建，它们使用原始投影；但使用 `mkAdmProj` 时，投影函数会通过 `admissible_pprod_fst` 定理的类型渗入。因此我们干脆把这两类都约化掉。

* [#9472](https://github.com/leanprover/lean4/pull/9472) 修复了 `congr_simp` 定理中的另一个问题，它会影响 Mathlib。非常感谢 Johan Commelin 提供最小复现用例。

* [#9476](https://github.com/leanprover/lean4/pull/9476) 修复了 `grind cutsat` 中 `Nat` 与 `Int` 之间的桥接。

* [#9479](https://github.com/leanprover/lean4/pull/9479) 改进了 `evalInt?` 函数，它用于求值从 `ToInt` 类型类引入的配置参数。该 PR 还新增了用于处理 `IsCharP` 类型类的 `evalNat?` 函数，并引入了如下配置选项：
  ```
  grind (exp := <num>)
  ```
  该选项控制表达式求值时考虑的最大指数大小。此前，`evalInt?` 使用 `whnf`，在约化诸如 `2^1024` 这样的项时可能会耗尽栈空间。

* [#9480](https://github.com/leanprover/lean4/pull/9480) 增加了一项功能：`structure` 构造器可以覆盖类型参数推断出的绑定器类别。下面这个例子中，`toLp` 上的 `(p)` 绑定器会让 `p` 成为 `WithLp.toLp` 的显式参数：
  ```lean
  structure WithLp (p : Nat) (V : Type) where toLp (p) ::
    ofLp : V
  ```
这反映了 #7742 中为覆盖结构投影绑定器类别而添加的语法。类似地，只有 `structure` 头部中的参数可以更新；尝试更新通过 `variable` 引入的参数之绑定器类别会报错。

* [#9481](https://github.com/leanprover/lean4/pull/9481) 修复了在对含有非标准 `OfNat.ofNat` 项的目标使用 `grind` 时出现的内核类型不匹配。例如，在 issue #9477 中，定理 `range_lower` 里的 `0` 具有如下形式：
  ```lean
  (@OfNat.ofNat
    (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.closed Std.PRange.BoundShape.open)) Nat)
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```
  而不是更标准的形式：
  ```lean
  (@OfNat.ofNat
    Nat
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```

* [#9487](https://github.com/leanprover/lean4/pull/9487) 修复了 `grind linarith` 构造出的一个错误证明项，正如 #9485 所报告的那样。

* [#9491](https://github.com/leanprover/lean4/pull/9491) 为括号、元组和类型标注语法加入了卫生信息，用于在 #9443 中实现具卫生性的 cdot 函数扩展。

* [#9496](https://github.com/leanprover/lean4/pull/9496) 改进了 `set_option` 命令生成的错误消息。

* [#9500](https://github.com/leanprover/lean4/pull/9500) 在 `Lean.Grind.Field` 中加入了 `HPow \a Int \a` 字段，并添加了足够的公理把它同相关运算联系起来，以便今后在 `grind` 中处理指数。为避免冲突，我们还把 `Semiring` 里的 `HPow \a Nat \a` 从 extends 子句移动成普通字段。最后，该 PR 增加了一些关于指数归一化的失败测试。

* [#9505](https://github.com/leanprover/lean4/pull/9505) 移除了 `Lean.Elab.Tactic.Do.VCGen` 中一些残留的语法定义；导入它们时会把 `mvcgen` 策略“取消定义”。现在应当可以导入 Mathlib 并继续使用 `mvcgen`。

* [#9506](https://github.com/leanprover/lean4/pull/9506) 为 `mleave` 补上了几个缺失的 simp 引理。

* [#9507](https://github.com/leanprover/lean4/pull/9507) 让 `mvcgen` 能用 `mintro` 引入 `let`/`have` 绑定。

* [#9509](https://github.com/leanprover/lean4/pull/9509) 即使在 `example` 中，也会显示内核诊断信息。

* [#9512](https://github.com/leanprover/lean4/pull/9512) 让 `mframe`、`mspec` 与 `mvcgen` 遵守卫生规则。无法访问的带状态假设现在可以用新的策略 `mrename_i` 命名，其行为类似 `rename_i`。

* [#9516](https://github.com/leanprover/lean4/pull/9516) 确保当模块系统使私有声明变得不可访问时，相关错误消息会注明这一点。

* [#9518](https://github.com/leanprover/lean4/pull/9518) 确保先前那些 “is marked as private” 消息在模块系统下仍然会被触发。

* [#9520](https://github.com/leanprover/lean4/pull/9520) 纠正了 #9500 对 `Lean.Grind.Field` 的修改。

* [#9522](https://github.com/leanprover/lean4/pull/9522) 使用 `withAbstractAtoms`，以防内核在类型检查时意外约化算术归一化器里的原子。该 PR 还在 `grind` 归一化器中设置了 `implicitDefEqProofs := false`。

* [#9532](https://github.com/leanprover/lean4/pull/9532) 将 `Process.output` 与 `Process.run` 泛化为可接收一个可选的 `String` 参数，并将其管道输入到 `stdin`。

* [#9551](https://github.com/leanprover/lean4/pull/9551) 修正了 `cases` 策略中 “dependent elimination failed” 错误的位置。

* [#9553](https://github.com/leanprover/lean4/pull/9553) 修复了 #7830 引入的一个错误：如果光标位于如下位置
  ```lean
  example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
    induction as with
    | nil => -- 光标
    | cons b bs ih =>
  ```
那么 Infoview 过去会显示 “no goals”，而不是 `nil` 目标。该 PR 还修复了另一个独立错误：当把光标放在 `induction`/`cases` 策略后的下一行时
  ```lean
    induction as with
    | nil => sorry
    | cons b bs ih => sorry
    I -- < 光标
  ```
它会在目标列表中错误地报告原始目标。此外，该 PR 还对错误恢复做了多项改进（包括针对前置策略的 `allGoals` 类逻辑），并改进了出错时可见的策略状态。还新增了 `Tactic.throwOrLogErrorAt`/`Tactic.throwOrLogError`，可根据恢复状态选择抛出或记录错误。

* [#9571](https://github.com/leanprover/lean4/pull/9571) 恢复了这样一个特性：在 `Nat` 的 `induction`/`cases` 中，`zero` 和 `succ` 标签可以悬停查看。这个功能最初在 #1660 中加入，但在 #3629 和 #3655 为归纳类型添加自定义消去器时被破坏。更一般地说，如果归纳类型 `T` 的自定义消去器 `T.elim` 有某个替代项 `foo`，且 `T.foo` 是常量，那么 `foo` 标签现在也会带有 `T.foo` 的悬停信息。

* [#9574](https://github.com/leanprover/lean4/pull/9574) 添加了选项 `abstractProof`，用于控制 `grind` 是否自动为生成的证明创建辅助定理。

* [#9575](https://github.com/leanprover/lean4/pull/9575) 优化了 `grind ring` 生成的证明项。例如，在这个 PR 之前，内核在 `grind_ring_5.lean` 基准中检查证明需要 2.22 秒（M4 Max 上）；现在只需 0.63 秒。

* [#9578](https://github.com/leanprover/lean4/pull/9578) 修复了 `grind` 在构造“不相等”证明时的一个问题：当某个等式被并入 `False` 的等价类，但它不是其一致闭包类的根，且该类的根又尚未并入 `False` 的等价类时，就会出错。

* [#9579](https://github.com/leanprover/lean4/pull/9579) 确保 `ite` 和 `dite` 不会被选作 E-匹配模式。它们是糟糕的模式，因为两个条件分支只有在 `grind` 判定条件为 `True`/`False` 之后才会被内部化。

* [#9592](https://github.com/leanprover/lean4/pull/9592) 更新了归纳类型声明与匿名构造子记号产生的错误消息的样式和措辞，包括关于可推断构造子可见性更新的提示。

* [#9595](https://github.com/leanprover/lean4/pull/9595) 改进了在函数类型自由变量上书写无效投影时显示的错误消息。

* [#9606](https://github.com/leanprover/lean4/pull/9606) 在废弃警告中补充说明：当替换用的常量与原常量类型、可见性和/或命名空间不同时，会在警告中注明。

* [#9625](https://github.com/leanprover/lean4/pull/9625) 改进了 `wf_preprocess` 周边的跟踪消息。

* [#9628](https://github.com/leanprover/lean4/pull/9628) 为互相定义的（协）归纳谓词所生成的（协）归纳证明原理引入了 `mutual_induct` 变体。与标准的（协）归纳原理不同（后者会分别投影出每个谓词的结论），`mutual_induct` 会生成所有结论的合取。

* [#9633](https://github.com/leanprover/lean4/pull/9633) 更新了多条由内建策略产生或与之相关的错误消息，使其格式适配当前约定。

* [#9634](https://github.com/leanprover/lean4/pull/9634) 修改了点标识符记号，使 `(.a : T)` 会像广义字段记号那样，相对于根命名空间解析为 `T.a`。这让该记号能够引用私有名称、跟随别名，并使用打开的命名空间。LSP 自动补全也改进为遵循点标识符的解析方式，不过它目前仍未考虑别名或打开的命名空间。

* [#9637](https://github.com/leanprover/lean4/pull/9637) 提高了 “maximum universe level offset exceeded” 错误消息的可读性。

* [#9646](https://github.com/leanprover/lean4/pull/9646) 对由良基递归定义的函数，改用一种更简单的方法来证明其展开定理。它不再循环调用一堆策略，而是尝试在单遍模式下用 `simp` 精确撤销 `WF.Fix` 所做的改动，并借助一个专用定理把额外参数推进到每个匹配器（或 `casesOn`）内部。

* [#9649](https://github.com/leanprover/lean4/pull/9649) 修复了一个问题：当某个宏会展开为多个命令时，它在 `mutual` 内原本不会被接受。

* [#9653](https://github.com/leanprover/lean4/pull/9653) 为两类由从 `Prop` 做大消去而引发的常见错误添加了解释。为支持这一功能，子策略抛出的“嵌套”具名错误现在也能够显示其错误代码和解释。

* [#9666](https://github.com/leanprover/lean4/pull/9666) 处理了模块系统中一个尚未完成的特性：自动把 `let rec` 和 `where` 生成的辅助声明标记为私有，除非这些定义位于诸如 `@[expose]` 之下的公开上下文中。

* [#9670](https://github.com/leanprover/lean4/pull/9670) 为 `CommRing.Expr` 添加了构造子 `.intCast k` 和 `.natCast k`。我们需要它们，因为诸如 `Nat.cast (R := α) 1` 与 `(1 : α)` 这样的项在定义上并不相等。这在 Mathlib 中对数字 `0` 和 `1` 的情况非常常见。

* [#9671](https://github.com/leanprover/lean4/pull/9671) 修复了 `grind ring` 对 `SMul.smul` 的支持。`SMul.smul` 应用现在会被归一化。例如：
  ```lean
  example (x : BitVec 2) : x - 2 • x + x = 0 := by
    grind
  ```

* [#9675](https://github.com/leanprover/lean4/pull/9675) 在 `grind cutsat` 中增加了对 `Fin.val` 的支持。示例：
  ```lean
  example (a b : Fin 2) (n : Nat) : n = 1 → ↑(a + b) ≠ n → a ≠ 0 → b = 0 → False := by
    grind

* [#9676](https://github.com/leanprover/lean4/pull/9676) 为非标准算术实例添加了规范化器。`Nat` 和 `Int` 在 `grind` 中有内建支持，它会使用这些类型的标准实例，并假定当前使用的就是这些实例。不过，用户也可能定义与标准实例在定义上相等的替代实例。该 PR 使用 simproc 来规范化这类实例，而 Mathlib 中确实会出现这种情况。示例：

  ```lean
  class Distrib (R : Type _) extends Mul R where

* [#9679](https://github.com/leanprover/lean4/pull/9679) 会对多余的 `grind` 参数发出警告。

* [#9682](https://github.com/leanprover/lean4/pull/9682) 修复了由 `grind` 归一化器中 `unfoldReducible` 步骤的一项优化所引入的回归。它还确保投影函数不会在这一阶段被约化，因为它们会在后续步骤里重新折叠。

* [#9686](https://github.com/leanprover/lean4/pull/9686) 在 `grind` 的预处理步骤中，会对实现细节用的局部声明应用 `clear`。

* [#9699](https://github.com/leanprover/lean4/pull/9699) 为接受单例类型参数的函数加入了传播规则。这一特性有助于消解 `mvcgen` 生成的验证条件，例如：

  ```lean
  example (h : (fun (_ : Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
    grind
  ```

* [#9700](https://github.com/leanprover/lean4/pull/9700) 修复了在 `grind` 中启用 `checkInvariants` 时出现的断言违规。

* [#9701](https://github.com/leanprover/lean4/pull/9701) 在 `SpecLemmas.lean` 中切换到不会重载的本地 `Std.Do.Triple` 记号，以绕开一个第 2 阶段构建失败问题。

* [#9702](https://github.com/leanprover/lean4/pull/9702) 修复了 `match` 精译器中的一个问题：像 `__x` 这样的模式变量在局部上下文中本应具有 `implDetail` 种类，但此前并没有。现在 `kindOfBinderName` 改为 `LocalDeclKind.ofBinderName`。

* [#9704](https://github.com/leanprover/lean4/pull/9704) 优化了 `grind cutsat` 生成的证明项。更多性能改进会在后续合并。

* [#9706](https://github.com/leanprover/lean4/pull/9706) 在 `grind cutsat` 的证明项里合并了 `Poly.combine_k` 与 `Poly.mul_k` 两个步骤。

* [#9710](https://github.com/leanprover/lean4/pull/9710) 改进了 `grind ring` 与 `grind cutsat` 生成的一些证明项。

* [#9714](https://github.com/leanprover/lean4/pull/9714) 为 `CommRing.Expr.toPoly` 增加了一个针对内核约化优化过的版本。我们使用这个函数不仅是为了实现 `grind ring`，也用它把 `ring` 模块同 `grind cutsat` 接起来。

* [#9716](https://github.com/leanprover/lean4/pull/9716) 将跨包 `import all` 的校验转移到了 Lake；导入关键字（`public`、`meta` 与 `all`）的语法校验则被移到了两个 `import` 解析器中。

* [#9728](https://github.com/leanprover/lean4/pull/9728) 修复了 #9724。

* [#9735](https://github.com/leanprover/lean4/pull/9735) 将 #9699 中实现的传播规则扩展到常值函数。

* [#9736](https://github.com/leanprover/lean4/pull/9736) 实现了选项 `mvcgen +jp`，用一种略有损失的连接点 VC 编码来避免控制流做朴素拆分时导致的 VC 指数爆炸。

* [#9754](https://github.com/leanprover/lean4/pull/9754) 让 `mleave` 可以用于 `at *`，并改进了它的 simp 集，以便消去更多平凡目标（#9581）。

* [#9755](https://github.com/leanprover/lean4/pull/9755) 实现了 `mrevert ∀n` 策略，它会对带状态目标做 eta-约简，并与 `mintro ∀x1 ... ∀xn` 构成伴随关系。

* [#9767](https://github.com/leanprover/lean4/pull/9767) 修复了 `grind` 构造的等式一致性证明项。

* [#9772](https://github.com/leanprover/lean4/pull/9772) 修复了 `grind` 中“跨构造器或投影传播投影”的一个错误。当某个等价类包含异质等式时，它此前可能构造出类型错误的项。

* [#9776](https://github.com/leanprover/lean4/pull/9776) 在 `grind` 中把“化简”和“展开可约常量”两个步骤合并起来，以确保不会错过任何可能的归一化步骤。

* [#9780](https://github.com/leanprover/lean4/pull/9780) 扩展了 `grind` 处理范畴论时的测试套件，以帮助调试 Mathlib 中尚未解决的问题。

* [#9781](https://github.com/leanprover/lean4/pull/9781) 确保 `mvcgen` 具备卫生性。它现在生成的目标会把所有局部变量都以不可访问的方式引入。

* [#9785](https://github.com/leanprover/lean4/pull/9785) 将 `MVarId.getMVarDependencies` 的一个实现细节拆分成了顶层函数。Aesop 依赖此前在 `where` 子句中定义的那个函数，而在 #9759 之后这已不再可行。

* [#9798](https://github.com/leanprover/lean4/pull/9798) 引入了 `Lean.realizeValue`，这是一个新的元编程 API，用于对 `MetaM` 计算结果做具备并行感知的缓存。

* [#9800](https://github.com/leanprover/lean4/pull/9800) 改进了 delta 派生处理器，使其既能处理带绑定器的定义，也能递归展开定义。此外，delta 派生现在会尝试一个类中所有显式的非 `outParam` 参数，因此也能处理“混入式”实例参数。`deriving` 语法也被修改为接受一般项，因此现在可以派生更具体的实例，例如 `deriving OfNat _ 1` 或 `deriving Module R`。类还允许是一个 Π 类型，以便加入额外假设；下面是一个 Mathlib 例子：
  ```lean
  def Sym (α : Type*) (n : ℕ) :=
    { s : Multiset α // Multiset.card s = n }
  deriving [DecidableEq α] → DecidableEq _
  ```
  这里的下划线表示可以插入 `Sym α n` 的位置；当使用 `→` 时这是必要的。`deriving instance` 命令在进行 delta 派生时也可以引用带作用域的变量。**破坏性变更：** 派生实例的名称会使用 `instance` 命令的名称生成器，而新实例会被加入当前命名空间。

* [#9804](https://github.com/leanprover/lean4/pull/9804) 允许在 `simp?`、`dsimp?`、`simpa` 等命令的参数列表里书写尾随逗号。此前，只有非 `?` 变体的 `simp`、`dsimp`、`simp_all` 才允许这样写。

* [#9807](https://github.com/leanprover/lean4/pull/9807) 把 `Std.List.Zipper.pref` 加入了 `mleave` 的 simp 集。

* [#9809](https://github.com/leanprover/lean4/pull/9809) 添加了一个用于分析 `grind` E-匹配标注的脚本，可用于检测匹配循环。我们计划在未来加入面向用户的命令来运行这个脚本。

* [#9813](https://github.com/leanprover/lean4/pull/9813) 修复了 `grind` 所用 `unfoldReducible` 中意外出现的绑定变量崩溃。

* [#9814](https://github.com/leanprover/lean4/pull/9814) 在 `grind` 中，当 `normalizeLevels` 预处理步骤并非必需时，会跳过该步骤。

* [#9818](https://github.com/leanprover/lean4/pull/9818) 修复了 `DecidableEq` deriving 处理器在处理枚举类型（即所有构造器都没有字段的归纳类型）时没有把宇宙层级纳入考虑的错误。关闭 #9541。

* [#9819](https://github.com/leanprover/lean4/pull/9819) 让 `unsafe t` 项生成一个辅助不透明声明，而不是一个带有不透明可约性提示的辅助定义。

* [#9831](https://github.com/leanprover/lean4/pull/9831) 为 `Std.Range` 记号添加了一个反精译器。

* [#9832](https://github.com/leanprover/lean4/pull/9832) 添加了 simp 引理 `SPred.entails_<n>`，用来替代 `SPred.entails_cons`；后者由于 #8074 而不适合作为 simp 引理。

* [#9833](https://github.com/leanprover/lean4/pull/9833) 规避了 `mspec` 中一个涉及延迟赋值的 DefEq 错误。

* [#9834](https://github.com/leanprover/lean4/pull/9834) 修复了 `mvcgen` 中一个由 `wp` 应用接收到过多状态参数触发的错误；这种情况会在处理 `StateT` 原语时出现。

* [#9841](https://github.com/leanprover/lean4/pull/9841) 将把纯命题 `p : Prop` 嵌入 `SPred σs` 的 ⌜p⌝ 记号改为展开成简单的一阶表达式 `SPred.pure p`，从而可以在 `grind` 中通过 E-匹配支持它。

* [#9843](https://github.com/leanprover/lean4/pull/9843) 使 `mvcgen` 为生成的 VC 产生确定性的分支标签。不变式会命名为 `inv<n>`，其余每个 VC 会命名为 `vc<n>.*`，其中 `*` 部分会大致指示其来源。

* [#9852](https://github.com/leanprover/lean4/pull/9852) 删除了 `grind` 预处理步骤里使用的快速过滤器 `inShareCommon`。`shareCommon` 已不再只用于完全预处理过的项。

* [#9853](https://github.com/leanprover/lean4/pull/9853) 在 `grind` 中加入了 `Nat` 与 `Int` 数值字面量归一化器。

* [#9857](https://github.com/leanprover/lean4/pull/9857) 确保 `grind` 可以对包含宇宙多态基子模式的模式做 E-匹配。例如，给定
  ```
  set_option pp.universes true in
  attribute [grind?] Id.run_pure
  ```
  模式
  ```
  Id.run_pure.{u_1}: [@Id.run.{u_1} #1 (@pure.{u_1, u_1} `[Id.{u_1}] `[Applicative.toPure.{u_1, u_1}] _ #0)]
  ```
  包含两个嵌套的宇宙多态基模式
  - `Id.{u_1}`
  - `Applicative.toPure.{u_1, u_1}`

* [#9860](https://github.com/leanprover/lean4/pull/9860) 修正 `grind` 中的 E-匹配定理激活。

* [#9865](https://github.com/leanprover/lean4/pull/9865) 为内核类型检查器加入了更好的反射式证明支持，以处理 #9854 暴露的性能问题。现在每当内核类型检查形如 `eagerReduce _` 的参数时，就会进入“急切约化”模式；在该模式下，内核会更积极地约化项。新的 `eagerReduce _` 提示常用于包裹 `Eq.refl true`，且不应对现有 Lean 包造成负面影响。

* [#9867](https://github.com/leanprover/lean4/pull/9867) 修复了 `grind ring` 中的一种非确定性行为。

* [#9880](https://github.com/leanprover/lean4/pull/9880) 确保在 `grind` 中，每个模式至多激活一次局部 `forall`。

* [#9883](https://github.com/leanprover/lean4/pull/9883) 改进了多余 `grind` 参数的警告消息。它不是基于实际推断出的模式，而是基于所提供参数的种类来给出提示。

* [#9885](https://github.com/leanprover/lean4/pull/9885) 这一改动最初是因为注意到 `Lean.Grind.Preorder.toLE` 会出现在冗长的 Mathlib 类型类搜索中；现在它会阻止这类搜索。这些修改也为未来可能移除自定义 `Lean.Grind.*` 类型类、并与 #9729 引入的新类型类统一做好了准备。
````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Library"
%%%

````markdown

* [#7450](https://github.com/leanprover/lean4/pull/7450) 实现了 `Nat.dfold`，它是 `Nat.fold` 的依赖类型版本。

* [#9096](https://github.com/leanprover/lean4/pull/9096) 通过使用 `Classical` 命名空间中的引理而不是 `Decidable` 命名空间中的引理，移除了一些不必要的 `Decidable*` 实例参数。

* [#9121](https://github.com/leanprover/lean4/pull/9121) 允许 `grind` 对 `Prod` 的宇宙变体做分情况分析。

* [#9129](https://github.com/leanprover/lean4/pull/9129) 修正了关于布尔等式的化简引理，使其写成 `(!x) = y`，而不是 `(!decide (x = y)) = true`。

* [#9135](https://github.com/leanprover/lean4/pull/9135) 允许纯迭代器（`Iter`）上的 `forIn`、`foldM` 和 `fold` 结果类型位于与迭代器不同的宇宙中。

* [#9142](https://github.com/leanprover/lean4/pull/9142) 把 `Fin.reverseInduction` 从使用良基递归改为使用 `let rec`，从而改善其定义等同性。与 @digama0 共同完成。

  ```lean
  namespace Fin

* [#9145](https://github.com/leanprover/lean4/pull/9145) 修正了两处拼写错误。

* [#9176](https://github.com/leanprover/lean4/pull/9176) 让 `mvcgen` 对 `if` 进行拆分，而不是应用规格；这样修复了 Rish 报告的一个错误。

* [#9194](https://github.com/leanprover/lean4/pull/9194) 使 `Std.Do` 的逻辑和策略具有宇宙多态性，代价是基础情形 `SPred []` 从 `Prop` 切换到 `ULift Prop` 后，会失去一些定义性性质。

* [#9249](https://github.com/leanprover/lean4/pull/9249) 添加了定理 `BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false`，它比 `BitVec.clzAuxRec_eq_clzAuxRec_of_le` 更一般，并在 bitblaster 中取代了后者。

* [#9260](https://github.com/leanprover/lean4/pull/9260) 在 Lean 自身中移除了对 `Lean.RBMap` 的使用。

* [#9263](https://github.com/leanprover/lean4/pull/9263) 修复了 `toISO8601String`，使其生成符合 ISO 8601 格式规范的字符串。先前的实现会用 `.` 而不是 `:` 分隔分钟和秒钟部分，并且在时区偏移中没有用 `:` 分隔小时和分钟部分。

* [#9285](https://github.com/leanprover/lean4/pull/9285) 移除了 `Array.any_push`、`Array.any_push'`、`Array.all_push`、`Array.all_push'` 以及 `Vector.any_push`、`Vector.all_push` 对 `BEq α` 的不必要要求。

* [#9301](https://github.com/leanprover/lean4/pull/9301) 为与 `Zipper` 相关的定理添加了 `simp` 和 `grind` 标注，以改进对 `Std.Do` 不变式的推理。

* [#9391](https://github.com/leanprover/lean4/pull/9391) 把化简引理 `Nat.zero_mod` 的证明替换为 `rfl`，因为它按设计就是定义等式。这修复了一个问题：此前该引理在 `dsimp` 模式下无法被化简器使用。

* [#9441](https://github.com/leanprover/lean4/pull/9441) 修复了 `String.prev` 的行为，使运行时实现与参考实现保持一致。具体来说，现在以下陈述成立：
  - `(s.prev p).byteIdx` 至少为 `p.byteIdx - 4`，至多为 `p.byteIdx - 1`
  - `s.prev 0 = 0`
  - `s.prev` 是单调的

* [#9449](https://github.com/leanprover/lean4/pull/9449) 修复了 `String.next` 在标量边界（64 位平台上的 `2 ^ 63 - 1`）处的行为。

* [#9451](https://github.com/leanprover/lean4/pull/9451) 让 `mintro` 策略支持像 `intro` 一样在带状态的目标中引入 `let`/`have` 绑定器。当规格引入此类 `let` 绑定时，这很有用。

* [#9454](https://github.com/leanprover/lean4/pull/9454) 引入了策略 `mleave`，它会通过对抽象做 eta 展开并应用一些温和的化简来退出 `SPred` 证明模式。这有助于在之后应用诸如 `grind` 之类的自动化。

* [#9504](https://github.com/leanprover/lean4/pull/9504) 又添加了一些 `*.by_wp`“充分性定理”，从而可以使用 `Std.Do` 框架证明关于 `ReaderM` 和 `ExceptM` 中程序的性质。

* [#9528](https://github.com/leanprover/lean4/pull/9528) 添加了 `List.zipWithM` 和 `Array.zipWithM`。

* [#9529](https://github.com/leanprover/lean4/pull/9529) 将 `NameSet` 的一些辅助实例从 Batteries 上游合入。

* [#9538](https://github.com/leanprover/lean4/pull/9538) 添加了两个与 `Iter.toArray` 相关的引理。

* [#9577](https://github.com/leanprover/lean4/pull/9577) 添加了关于 `UIntX.toBitVec`、`UIntX.ofBitVec` 和 `^` 的引理。

* [#9586](https://github.com/leanprover/lean4/pull/9586) 为 `Vector α n` 添加了按分量进行的代数运算以及相关实例。

* [#9594](https://github.com/leanprover/lean4/pull/9594) 优化了 `Lean.Name.toString`，带来约 10% 的指令数收益。

* [#9609](https://github.com/leanprover/lean4/pull/9609) 为 `Prod.lex_def` 添加了 `@[grind =]`。注意，`omega` 对 `Prod.Lex` 有特殊处理，而 `grind` 的 cutsat 模块要实现同等能力就需要它。

* [#9616](https://github.com/leanprover/lean4/pull/9616) 引入了检查，以确保当输入包含 NUL 字节时，IO 函数会报错（而不是忽略第一个 NUL 字节之后的所有内容）。

* [#9620](https://github.com/leanprover/lean4/pull/9620) 将 `List.pairwise_iff_forall_sublist` 的两个方向分别作为具名引理加入。

* [#9621](https://github.com/leanprover/lean4/pull/9621) 将 `Xor` 重命名为 `XorOp`，以与 `AndOp` 等保持一致。

* [#9622](https://github.com/leanprover/lean4/pull/9622) 补上了一个关于 `List.sum` 的缺失引理，并添加了一个 grind 标注。

* [#9701](https://github.com/leanprover/lean4/pull/9701) 在 `SpecLemmas.lean` 中切换到不会重载的本地 `Std.Do.Triple` 记号，以绕开一个第 2 阶段构建失败问题。

* [#9721](https://github.com/leanprover/lean4/pull/9721) 为更多 `SInt` 与 `UInt` 引理加上了 `int_toBitVec` 标记，从而让 `bv_decide` 能处理它们之间的类型转换以及取负。

* [#9729](https://github.com/leanprover/lean4/pull/9729) 引入了一种为类型赋予序结构的规范方式。基础运算（`LE`、`LT`、`Min`、`Max`，以及后续 PR 中的 `BEq`、`Ord` 等）与任何更高层次的性质（预序、偏序、线序等）都按需要与 `LE` 关联起来。该 PR 为许多核心类型提供了 `IsLinearOrder` 实例，并更新了若干引理的签名。

* [#9732](https://github.com/leanprover/lean4/pull/9732) 用 Lean 而不是 C++ 重新实现了 `IO.waitAny`。这样可以减小 `task_manager` 的体积和复杂度，从而便于未来重构。

* [#9736](https://github.com/leanprover/lean4/pull/9736) 实现了选项 `mvcgen +jp`，用一种略有损失的连接点 VC 编码来避免控制流做朴素拆分时导致的 VC 指数爆炸。

* [#9739](https://github.com/leanprover/lean4/pull/9739) 从 `Std.Classes.Ord.Basic` 中误加到 `lexOrd` 上的 `instance` 属性已被移除。

* [#9757](https://github.com/leanprover/lean4/pull/9757) 为关键的 `Std.Do.SPred` 引理添加了 `grind` 标注。

* [#9782](https://github.com/leanprover/lean4/pull/9782) 修正了 `StdGen` 的 `Inhabited` 实例，使其为伪随机数生成器使用一个有效的初始状态。此前 `default` 生成器满足 `Prod.snd (stdNext default) = default`，因此它只会产生常量序列。

* [#9787](https://github.com/leanprover/lean4/pull/9787) 添加了 simp 引理 `PostCond.const_apply`。

* [#9792](https://github.com/leanprover/lean4/pull/9792) 为两个带 `where` 子句且 Batteries 会为其证明定理的定义添加了 `@[expose]`。

* [#9799](https://github.com/leanprover/lean4/pull/9799) 修复了 #9410 中的问题。

* [#9805](https://github.com/leanprover/lean4/pull/9805) 改进了不变式和后置条件的 API，因此对现有的 `Std.Do` 预发布 API 引入了一些破坏性变更。它还把 Markus Himmel 的 `pairsSumToZero` 示例加入为测试用例。

* [#9832](https://github.com/leanprover/lean4/pull/9832) 添加了 simp 引理 `SPred.entails_<n>`，用来替代 `SPred.entails_cons`；后者由于 #8074 而不适合作为 simp 引理。

* [#9841](https://github.com/leanprover/lean4/pull/9841) 将把纯命题 `p : Prop` 嵌入 `SPred σs` 的 ⌜p⌝ 记号改为展开成简单的一阶表达式 `SPred.pure p`，从而可以在 `grind` 中通过 E-匹配支持它。

* [#9848](https://github.com/leanprover/lean4/pull/9848) 为 `Std.PRange` 中的 `forIn` 和 `forIn'` 添加了 `@[spec]` 引理。

* [#9850](https://github.com/leanprover/lean4/pull/9850) 为 `Std.PRange` 记号添加了反精译器。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Compiler"
%%%

````markdown

* [#8691](https://github.com/leanprover/lean4/pull/8691) 确保当使用新编译器进行编译失败时，状态会被回滚。这对于不可计算的 `section` 尤其重要，因为编译器可能会生成半编译的函数，而这些函数随后可能在编译其他函数时被错误地使用。

* [#9134](https://github.com/leanprover/lean4/pull/9134) 修改了 ToIR：调用 `lowerEnumToScalarType?` 时传入 `ConstructorVal.induct`，而不是构造器自身的名字。这是新编译器代码在落地前一次重构中的疏漏。它不应影响已编译代码的运行时间（因为额外的打标签/去标签会被 LLVM 优化掉），但会让解释器使用的 IR 稍微更高效一些。

* [#9144](https://github.com/leanprover/lean4/pull/9144) 增加了把更多归纳类型表示成枚举的支持，概括地说，就是把支持范围扩展到那些因为参数或无关字段而无法成为枚举的类型。虽然这本身就很有用，但真正动机是为了保证未来某项优化的正确性：如果我们实现 `object`/`tobject` 区分，以分别表示“保证是对象指针的值”和“也可能是带标签标量的值”，那么现有的类型表示规则其实并不健全。特别是，本 PR 测试中新加入的那类类型，其所有构造器都会被编码成带标签的值，但若按现有规则自然扩展，它们会被归为 `object` 而不是 `tobject`。

* [#9154](https://github.com/leanprover/lean4/pull/9154) 收紧了 IR 中关于闭包应用的类型规则。重读部分代码时我发现，`mkPartialApp` 里有一个明显的笔误——`.object` 和 `type` 应当互换。尽管之后的 IR 阶段会把这里的不匹配“抹平”，但更合理的做法仍然是在前端就严格要求：闭包应用始终返回 `.object`。

* [#9159](https://github.com/leanprover/lean4/pull/9159) 在 LCNF 编译的基础阶段，强制 `_override` 实现不被内联。当前做法会让构造器/`cases` 之间的不匹配暴露给化简器，从而触发断言失败。之所以这个问题没有更早在 `Expr` 上暴露出来，是因为 `Expr` 的计算字段取值函数有自定义的外部实现。

* [#9177](https://github.com/leanprover/lean4/pull/9177) 让 `pullInstances` 阶段避免拉取任何包含已擦除命题的实例表达式，因为我们并没有正确表示擦除后仍然存在的依赖关系。

* [#9198](https://github.com/leanprover/lean4/pull/9198) 修改了编译器的特化分析，使其把那类只会改变其 `Prop` 参数的重新打包高阶参数视为固定参数。这意味着它们只需 `@[specialize]` 即可被特化，而不必让编译器显式启用更激进的按参数特化。

* [#9207](https://github.com/leanprover/lean4/pull/9207) 让当某个对象应标记为 `noncomputable` 时所产生错误消息中的相关声明可点击跳转。

* [#9209](https://github.com/leanprover/lean4/pull/9209) 修改了 `elimDeadBranches` 的辅助函数 `getLiteral`，使其能够正确处理带构造器的归纳类型。这个函数平时没有尽可能多地被使用，所以除了定向测试用例之外，这个问题很少会被触发。

* [#9218](https://github.com/leanprover/lean4/pull/9218) 让 LCNF 的 `elimDeadBranches` 阶段在处理 `unsafe` 声明时更谨慎。现在，只有当递归调用存在值流出时，`unsafe` 声明的结果才会变成 `⊤`。

* [#9221](https://github.com/leanprover/lean4/pull/9221) 删除了基于错误假设的代码：它假定 LCNF 局部变量可能出现在类型中。`ElimDead.lean` 里其他注释都说这种情况不可能发生，因此这大概是新编译器开发早期遗留下来的改动。

* [#9224](https://github.com/leanprover/lean4/pull/9224) 修改了 `toMono` 阶段，使其会考虑应用的类型，并擦除所有对应于已擦除参数的实参。通过改变声明的单态类型，这提供了一种轻量级的相关性分析。我本来希望把它同构造器上的行为统一起来，但我在 #9222（为本 PR 做准备）中尝试让构造器也采用同样行为时引入了轻微性能回退，尽管这其实只是这项改动的副作用。因此我暂时按下不表。未来我们希望把这一做法扩展到构造器、外部声明等位置。

* [#9266](https://github.com/leanprover/lean4/pull/9266) 为 LCNF 单态类型增加了对 `.mdata` 的支持（然后在 IR 类型层面将其丢弃）。这更贴近旧编译器 C++ 代码中外部声明的行为；目前创建外部声明时仍在使用那套代码，但很快会被替换。

* [#9268](https://github.com/leanprover/lean4/pull/9268) 将 `lean_add_extern`/`addExtern` 的实现从 C++ 挪到了 Lean。我相信这是库/编译器目录中最后一个仍被新编译器依赖的 C++ 辅助函数。我把它放进了单独的文件，并复制了少量代码，因为该函数需要在 `CoreM` 中执行，而其他 IR 函数位于它们各自的单子栈里。等 C++ 编译器被移除后，我们就可以把这些 IR 函数也迁入 `CoreM`。

* [#9275](https://github.com/leanprover/lean4/pull/9275) 删除了用 C++ 编写的旧编译器。

* [#9279](https://github.com/leanprover/lean4/pull/9279) 在将 `compiler.extract_closed` 选项迁移到 Lean 之后修复了它（并新增了测试，以便将来及时发现同类问题）。

* [#9310](https://github.com/leanprover/lean4/pull/9310) 修复了 IR 构造器参数下调，以便在所有情况下都能正确处理“给相关参数传递无关实参”的情形。问题之所以出现，是因为构造器参数下调不完整地重写了一遍通用的 LCNF 到 IR 参数下调逻辑；修复方式就是直接采用通用辅助函数。这大概也是新编译器还在分支上时一次不完整重构留下的问题。

* [#9336](https://github.com/leanprover/lean4/pull/9336) 修改了 `trace.Compiler.result` 的实现：它现在直接使用提供给它的声明，而不是去 LCNF 单态环境扩展里重新查找。之前那么做看起来只是为了省去在打印声明前重新规范化自由变量 ID 的麻烦。这意味着由 `extractClosed` 阶段生成的 `._closed` 声明现在也会出现在输出里；如果你之前不知道发生了什么，这原本会非常令人困惑。

* [#9344](https://github.com/leanprover/lean4/pull/9344) 正确填充了 `IR.FnBody.case` 构造器的 `xType` 字段。事实证明，这个字段此前出错并没有明显后果，因为 `Boxing` 阶段会保守地重新计算它。

* [#9393](https://github.com/leanprover/lean4/pull/9393) 修复了一个不安全的小技巧：它会通过构造一个运行时表示永远不可能成为有效 `Expr` 的值，来为 `Expr` 哈希表（以指针为键）创建哨兵。此前选用的值是 `Unit.unit`，这违反了“`Expr` 没有标量构造器”的推断。现在改成一个新分配的 `Unit × Unit` 值。

* [#9411](https://github.com/leanprover/lean4/pull/9411) 增加了对子单例之 `casesOn` 的编译支持。我们依赖精译器的类型检查，把它限制在那些实际上能消去到 `Type n` 的 `Prop` 归纳类型上；它目前还不覆盖这些类型的其他递归器（更不用说不在 `Prop` 中的归纳类型了）。

* [#9703](https://github.com/leanprover/lean4/pull/9703) 更改了 LCNF `elimDeadBranches` 阶段，使其把所有非 `Nat` 的字面量类型都视为 `⊤`。事实证明，要在当前抽象值表示下正确处理所有这些类型，复杂度出人意料地高，因此最好先把这个修复落地。

* [#9720](https://github.com/leanprover/lean4/pull/9720) 删除了一条错误消息。它隐含地假定“新增测试中出现的那种、已擦除类型之间的类型依赖不可能发生”。仅凭 LCNF 类型中现有的信息，很难把这条错误消息做得更精确，而它持续存在的价值又很小（我不记得它曾真正发现过问题），所以删掉更合理。

* [#9827](https://github.com/leanprover/lean4/pull/9827) 修改了在 `toMono` 中对 `Quot.lcInv`（`Quot.lift` 的编译器内部形式）的下调方式，以支持过量应用。

* [#9847](https://github.com/leanprover/lean4/pull/9847) 在这条定制内联路径中加入了对递归声明的检查，从而修复了旧编译器中的一处回归。

* [#9864](https://github.com/leanprover/lean4/pull/9864) 为 `Array.getInternal` 与 `Array.get!Internal` 添加了新的变体，它们会以借用方式返回其参数，也就是不会增加引用计数。编译器可以在确认数组会在返回值生命周期内继续持有该元素的有效引用时使用它们。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Pretty-Printing"
%%%

````markdown

* [#8391](https://github.com/leanprover/lean4/pull/8391) 为 `Vector.mk` 添加了一个反精译器，它会把 `Vector.mk #[...] _` 反展开为 `#v[...]`。
  ```lean
  -- 之前：
  #check #v[1, 2, 3] -- { toArray := #[1, 2, 3], size_toArray := ⋯ } : Vector Nat 3
  -- 现在：
  #check #v[1, 2, 3] -- #v[1, 2, 3] : Vector Nat 3
  ```

* [#9475](https://github.com/leanprover/lean4/pull/9475) 修复了某些语法因缺失空白提示而导致的美观打印结果。

* [#9494](https://github.com/leanprover/lean4/pull/9494) 修复了一个问题：它会导致某些错误消息试图为不存在的标识符显示悬停信息。

* [#9555](https://github.com/leanprover/lean4/pull/9555) 允许消息数据中的提示指定自定义预览范围，使其可以超出代码动作指定的编辑区域。

* [#9778](https://github.com/leanprover/lean4/pull/9778) 修改了匿名元变量的美观打印方式，使其使用索引而不是内部名称。这样一来，`?m.123` 这类后缀里的数字会更小，因为索引是在给定的元变量上下文内编号，而不是在整个文件范围内编号，因此每个命令都会有自己的编号。这个改动目前还不影响宇宙层级元变量的美观打印。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Documentation"
%%%

````markdown

* [#9093](https://github.com/leanprover/lean4/pull/9093) 为 `ToFormat.toFormat` 补上了缺失的文档字符串。

* [#9152](https://github.com/leanprover/lean4/pull/9152) 修复了 `registerDerivingHandler` 的一条过时文档字符串。

* [#9593](https://github.com/leanprover/lean4/pull/9593) 大幅简化了 `propext` 的文档字符串。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Server"
%%%

````markdown

* [#9040](https://github.com/leanprover/lean4/pull/9040) 改进了 “Go to Definition” 的用户体验，具体包括：
  - 对类型类投影使用 “Go to Definition” 时，现在会提取参与其中的具体实例，并将它们作为可跳转的位置提供。例如，对 `toString 0` 中的 `toString` 使用该功能，会得到 `ToString.toString` 和 `ToString Nat`。
  - 对会生成带有类型类投影语法之宏使用 “Go to Definition” 时，现在也会提取参与其中的具体实例，并将它们作为可跳转的位置提供。例如，对 `1 + 1` 中的 `+` 使用该功能，会得到 `HAdd.hAdd`、`HAdd α α α` 和 `Add Nat`。
  - 使用 “Go to Declaration” 时，现在除了给出参与其中的精译器和解析器外，还会给出 “Go to Definition” 的全部结果。例如，对 `1 + 1` 中的 `+` 使用它，会得到 `HAdd.hAdd`、`HAdd α α α`、`Add Nat`、``macro_rules | `($x + $y) => ...`` 和 `infixl:65 " + " => HAdd.hAdd`。
  - 对类型中包含多个常量的值使用 “Go to Type Definition” 时，现在会为每个常量提供 “Go to Definition” 的结果。例如，对 `x : Array Nat` 中的 `x` 使用它，会得到 `Array` 和 `Nat`。

* [#9163](https://github.com/leanprover/lean4/pull/9163) 目前在服务器中禁用了由 `lake setup-file` 产生的头部。等到 Lake 在处理工作区模块时会考虑服务器给出的头部后，它会重新启用。否则，当磁盘上的文件与编辑器中的文件对该文件是否参与模块系统存在分歧时，`setup-file` 头部会产生奇怪的行为。

* [#9563](https://github.com/leanprover/lean4/pull/9563) 对模糊匹配做了一些微优化，带来约 `~20%` 的指令数收益。

* [#9784](https://github.com/leanprover/lean4/pull/9784) 确保编辑器进度条能更准确地反映并行精译的实际进度。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Lake"
%%%

````markdown

* [#9053](https://github.com/leanprover/lean4/pull/9053) 更新了 Lake，使 Lean 可以通过 `lean --setup` 的 `modules` 字段解析传递导入所需的 `.olean` 文件。这意味着 Lean 现在可以直接使用 Lake 缓存中的 `.olean` 文件，而不必再把它们定位到某个特定的层级路径。

* [#9101](https://github.com/leanprover/lean4/pull/9101) 修复了 #9081 引入的一个错误：它会让源文件从模块输入跟踪中丢失，并让模块作业日志中的一些条目消失。

* [#9162](https://github.com/leanprover/lean4/pull/9162) 将 Lake 在内容哈希数据结构里为 `,ir` 产物使用的键改成了 `r`，以保持“单字符键名”的约定。

* [#9165](https://github.com/leanprover/lean4/pull/9165) 修复了 Lake 创建静态归档文件过程中的两个问题。

* [#9332](https://github.com/leanprover/lean4/pull/9332) 修改了 Lake 中的依赖克隆机制，使得 “Lake 正在克隆某个依赖” 这一日志消息会在开始克隆时出现，而不是在克隆完成后才出现。这大大缓解了用户在新建项目时看到 Lake “无故卡住”的困惑；现在输出如下：
  ```
  λ lake +lean4 new math math
  info: downloading mathlib `lean-toolchain` file
  info: math: no previous manifest, creating one from scratch
  info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
  <hang>
  info: leanprover-community/mathlib: checking out revision 'cd11c28c6a0d514a41dd7be9a862a9c8815f8599'
  ```

* [#9434](https://github.com/leanprover/lean4/pull/9434) 修改了 Lake 的本地缓存基础设施，使其能够从缓存中恢复可执行文件、共享库和静态库。这意味着它们会保留预期名称，而某些用例仍然依赖这些名称。

* [#9435](https://github.com/leanprover/lean4/pull/9435) 添加了 `libPrefixOnWindows` 包与库配置选项。启用后，Lake 会在 Windows 上为静态库和共享库加上 `lib` 前缀（也就是与 Unix 上相同的方式）。

* [#9436](https://github.com/leanprover/lean4/pull/9436) 在 `lake build` 成功运行后的最终消息中加入了本次运行的作业数量。

* [#9478](https://github.com/leanprover/lean4/pull/9478) 为 `meta import` 增加了正确的 Lake 支持。模块 IR 现在会被记录到跟踪信息中，也会出现在 Lake 传给 `lean --setup` 的预解析模块里。

* [#9525](https://github.com/leanprover/lean4/pull/9525) 修复了 Lake 对模块系统 `import all` 的处理。此前，Lake 会像处理非模块化 `import` 一样处理 `import all`，从而把传递导入树中的所有私有数据都导入进来。现在 Lake 会区分这两者：`import all M` 只会导入 `M` 的私有数据。`M` 的直接私有导入会被跟随，但不会被提升。

* [#9559](https://github.com/leanprover/lean4/pull/9559) 修改了 `lake setup-file`，使其对工作区模块使用服务器提供的头部。

* [#9604](https://github.com/leanprover/lean4/pull/9604) 将 Lake 生成瘦归档的行为限制为仅用于 Windows 的核心构建（即 `bootstrap = true`）。macOS 上构建核心时通常使用的未捆绑 `ar` 不支持 `--thin`，因此除非必要我们会避免使用它。

* [#9677](https://github.com/leanprover/lean4/pull/9677) 为构建监视器的每个构建步骤加入了构建耗时（在 `-v` 或 CI 中显示），并让 `--no-build` 在构建监视器结束后才退出。因此，`--no-build` 失败现在会报告究竟是哪些目标因为需要重建而阻塞了 Lake。

* [#9697](https://github.com/leanprover/lean4/pull/9697) 修复了 `lake lean` 与 `lake setup-file` 对带多个点的库源文件（例如 `src/Foo.Bar.lean`）的处理。

* [#9698](https://github.com/leanprover/lean4/pull/9698) 调整了 `lake query` 的格式化类型类，使其不再要求同时具备文本和 JSON 两种形式，而是允许任意组合；这些类型类也被重命名了。此外，文本模块头的查询格式也被改进为只生成有效头部。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Other"
%%%

````markdown

* [#9106](https://github.com/leanprover/lean4/pull/9106) 修复了在不启用 `LEAN_USE_GMP` 构建时出现的 `undefined symbol: lean::mpz::divexact(lean::mpz const&, lean::mpz const&)`。

* [#9114](https://github.com/leanprover/lean4/pull/9114) 进一步改进了发布自动化，能在发往下游仓库的 bump PR 中自动纳入来自 `nightly-testing` 和 `bump/v4.X.0` 分支的内容。

* [#9659](https://github.com/leanprover/lean4/pull/9659) 修复了 `trace.profiler.output` 选项与新版 Firefox Profiler 的兼容性。

````
