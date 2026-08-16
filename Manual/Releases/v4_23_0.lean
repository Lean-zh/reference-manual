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
本次发布共合入 610 项改动。除下文列出的 95 项功能新增和 139 项修复外，还有 61 项重构、12 项文档改进、71 项性能改进，以及 232 项其他改动。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Highlights"
%%%

````markdown

Lean v4.23.0 带来了显著的性能改进、更好的错误消息，以及 `grind`、编译器和 Lean 其他组件中的大量错误修复、打磨与整合。

就用户体验而言，值得注意的新特性包括：

- 改进的 “Go to Definition” 导航（[#9040](https://github.com/leanprover/lean4/pull/9040)）

  - 在类型类投影上使用 “Go to Definition” 时，现在会提取参与其中的具体实例，并将它们也作为可跳转的位置提供。例如，在 `toString 0` 的 `toString` 上使用该功能，会返回 `ToString.toString` 和 `ToString Nat`。
  - 在会生成带有类型类投影语法的宏上使用 “Go to Definition” 时，现在也会提取参与其中的具体实例并提供跳转位置。例如，在 `1 + 1` 的 `+` 上使用该功能，会返回 `HAdd.hAdd`、`HAdd α α α` 和 `Add Nat`。
  - “Go to Declaration” 现在除了给出 elaborator 和 parser 外，也会提供 “Go to Definition” 的全部结果。例如，在 `1 + 1` 的 `+` 上使用它，会返回 `HAdd.hAdd`、`HAdd α α α`、`Add Nat`、`` macro_rules | `($x + $y) => ... `` 以及 `infixl:65 " + " => HAdd.hAdd`。
  - 对于类型中包含多个常量的值，“Go to Type Definition” 现在会为每个常量提供 “Go to Definition” 结果。例如，对 `x : Array Nat` 中的 `x` 使用它，会返回 `Array` 和 `Nat`。

- 面向错误的交互式代码动作提示：

  - 对于“无效命名参数”错误,建议有效的参数名称([#9315](https://github.com/leanprover/lean4/pull/9315))

  - 对于“无效案例名称”错误,建议有效的案例名称([#9316](https://github.com/leanprover/lean4/pull/9316))

  - 在结构实例中的“丢失字段”错误,建议插入所有缺失字段([#9317](https://github.com/leanprover/lean4/pull/9317))

你可以在 [Lean playground](https://live.lean-lang.org/#codez=PQWghAUAxABAEgSwHYBcDOMBmB7ATjZANwEMAbBAExiWIFsBTK43AcwFcHUNkYAHYlCnq4kaCCGAQIyCmwDGKBIXowAKjADuAC2H0IMGAB8YtANYBGGAAoAHjACeMAF4wAXDABC2bKQCUU+hs6XlIVKxQ3NV83AF59EwE5LRgIjQQULXjjADozSytHVxiU3DZ6aKsNWJKyipcirDI0cpgYgD5rfylQSFhELiw8GDliZuo6ejEJAKDaELCAI0ivH2j3ADkBaoX7eJHmjAW90ZUkbCRAhDQhVFa2+IM0UwRebvBoeGR0QfxaK7RkCwYNdSgo2LgVMhrsQkHIVJgEPRSBQppIICD5ChwSoAMqaHQQ+IIpEUSwbARExHIgBMkQAavQFENNhFicjzDNgqFIniivEAN4AXwgQA) 中尝试以上所有功能。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Highlights--Breaking-Changes"
%%%

````markdown

- [#9800](https://github.com/leanprover/lean4/pull/9800) 改进三角洲衍生处理器,使其有能力
与装有粘合器以及能够回溯
展开定义。 ** ** 退出变化**:
例名使用 `instance` 命令的名称生成器,
将新实例添加到当前命名空间中。

- [#9040](https://github.com/leanprover/lean4/pull/9040) 改进了“走向定义” UX。
**破坏性变更**：`InfoTree.hoverableInfoAt?` 已被泛化为 `InfoTree.hoverableInfoAtM?`，现在它接受一个通用的 `filter` 参数，而不再像以前那样携带若干布尔标志。

- [#9594](https://github.com/leanprover/lean4/pull/9594) 优化 `Lean.Name.toString` ,给10%的指令
受益。

关键的是,这是作为旧`Lean.Name.toString`的**突破性变化**。
用于支持标识符识别方法的方法。此方法
现作为`Lean.Name.toStringWithToken`现作为`Lean.Name.toStringWithToken`提供,以便
(高常见) `toString` 设置
3⁄4 ̄ ̧漯B

- [#9729](https://github.com/leanprover/lean4/pull/9729) 引入一种教条方式,向一种类型下订单
结构**** 空白变化:**

  - `lt_of_le_of_lt`/`le_trans`
`Vector`、`List`、`List`和`Array`已简化。
`IsLinearOrder`例。 新的要求在逻辑上等同
对旧的,但本例不是自动的,
从小类中推导出。
  - 替换类型`Std.Total (¬ · < · : α → α → Prop)`的假设
`Std.Asymm (· < · : α → α → Prop)`。
应加以限制,因为现在出现了一种产生
后一种情况。
  - 在 `Init.Data.List.MinMax` 中,多个定理签名被修改,
反对称、整数、`min_ex_or`
等,加上相应的实例参数。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Language"
%%%

````markdown

* [#6732](https://github.com/leanprover/lean4/pull/6732) 增加支持转换模式中的`clear` 战术。

* [#8666](https://github.com/leanprover/lean4/pull/8666)调整试验模块系统以不导入
非`meta` 声明。它这样做的方式是以不透明的方式替换这类IR
关于出口和调整新编译器的外国出口和调整申报
因此。

* [#8842](https://github.com/leanprover/lean4/pull/8842) 修补没有收集正则的错误
由其它正数引用。 此错误的一个结果就是
从`native_decide`所证明的定理中收集的轴轴值不得
包括`Lean.trustCompiler`。

* [#9015](https://github.com/leanprover/lean4/pull/9015) 使`isDefEq` 探测到更多卡卡定义等同
具体来说,如果`t =?= defn ?m`和`defn`
依据其论点,这种平等被卡在`?m`。
这一变化,我们不会看到这种依赖性,而会简单地返回`false`。

* [#9084](https://github.com/leanprover/lean4/pull/9084) 增加`binrel%` `!=`和`≠`中定义的`!=`和`≠`
`Init.Core` 。 这使精灵能够对两者都插入强制
而不是承诺左侧的类型
手边

* [#9090](https://github.com/leanprover/lean4/pull/9090)在`whnfCore` 中未减少错误的地方修正错误
反应器/辅助反射器的应用。

* [#9097](https://github.com/leanprover/lean4/pull/9097)确保`mspec`使用已配置的透明度设置
使`mvcgen`在调用`mspec`时使用默认透明度。

* [#9099](https://github.com/leanprover/lean4/pull/9099) 改进了“预期类型不匹配”错误信息：当类型的类型在定义上相等时省略它们；若不相等，则分成单独的行显示。

* [#9103](https://github.com/leanprover/lean4/pull/9103) 防止 `panic!` 中包含空字节时消息被截断。

* [#9108](https://github.com/leanprover/lean4/pull/9108) 修复了一个问题：它可能导致消息中的内联表达式被不必要地渲染到单独一行。

* [#9113](https://github.com/leanprover/lean4/pull/9113) 改进了 `grind` 的文档字符串，并尝试让它对新用户更有用。

* [#9130](https://github.com/leanprover/lean4/pull/9130) 修正 `Grind.offset` 装置的意外发生
地面模式。见新测试

* [#9131](https://github.com/leanprover/lean4/pull/9131) 将`usedLetOnly` 参数添加到`LocalContext.mkLambda` 和
`LocalContext.mkForall`,与`MetavarContext`版本平行。

* [#9133](https://github.com/leanprover/lean4/pull/9133)在`grind`正常化者中增加对`a^(m+n)`的支持。

* [#9143](https://github.com/leanprover/lean4/pull/9143)清除了模块系统中一个相当丑陋的黑客,暴露了
其类型提及`WellFounded`的定理体。

* [#9146](https://github.com/leanprover/lean4/pull/9146) 在 `grind ring` 中添加“安全”多边操作。使用
通常的组合:`withIncRecDepth`和`checkSystem`。

* [#9149](https://github.com/leanprover/lean4/pull/9149) 将`a^(m+n)` 研磨正常化器概括为任何半环。
示例:
  ```
  variable [Field R]

* [#9150](https://github.com/leanprover/lean4/pull/9150) 在 `grind` 使用的 `toPoly` 函数中补上了一个缺失分支。

* [#9153](https://github.com/leanprover/lean4/pull/9153) 改进了 linarith 的 `markVars`，并确保它不会产生伪造的问题消息。

* [#9168](https://github.com/leanprover/lean4/pull/9168) 解决了一个 defeq 菱形问题，它曾在 Mathlib 中引发问题：
  ```
import Mathlib

* [#9172](https://github.com/leanprover/lean4/pull/9172) 在 `matchEqBwdPat` 处修正错误。 类型可能包含模式
变量。

* [#9173](https://github.com/leanprover/lean4/pull/9173) 修正试验模块系统在下列条件下的不兼容性:
试图将有充分根据的复发与公开披露的定义结合起来。

* [#9176](https://github.com/leanprover/lean4/pull/9176) 进行`mvcgen` 拆分,不采用规格。
这样做可以修复Rish报告的一个错误。

* [#9182](https://github.com/leanprover/lean4/pull/9182) 试图改进`grind` 电子匹配模式的推论。
尽管如此,我们仍然需要更好的工具来说明和保持
库的注解。

* [#9184](https://github.com/leanprover/lean4/pull/9184)用新的总计符号来修正`⇓`语法的偷窃
通过将其降为非内建语法并将其范围扩大到
`Std.Do`。

* [#9191](https://github.com/leanprover/lean4/pull/9191)如果
否则,他们将隐匿循环电话。

这个修复了8939号

* [#9193](https://github.com/leanprover/lean4/pull/9193) 解决按问题报告的意外内核预测问题
#9187

* [#9194](https://github.com/leanprover/lean4/pull/9194) 让 `Std.Do` 的逻辑与策略在宇宙层面上实现多态化，其代价是失去了一些定义性质；这些定义性质原本来自把基例 `SPred []` 从 `Prop` 切换到 `ULift Prop`。

* [#9196](https://github.com/leanprover/lean4/pull/9196) 在 `grind` 中使用 simproc 而不是重写规则来实现 `forall` 归一化。这只是该 PR 的第一部分；待 stage0 更新后，我们必须移除那些归一化定理。

* [#9200](https://github.com/leanprover/lean4/pull/9200) 在 `grind` 中使用 simproc 而不是重写规则来实现 `exists` 归一化。这只是该 PR 的第一部分；待 stage0 更新后，我们必须移除那些归一化定理。

* [#9202](https://github.com/leanprover/lean4/pull/9202) 扩展了 `grind` 所使用的 `Eq` simproc。它现在覆盖更多情况，并在要展开的声明列表中新增了 3 个可约声明。

* [#9214](https://github.com/leanprover/lean4/pull/9214) 实现了对局部和 scoped `grind_pattern` 命令的支持。

* [#9225](https://github.com/leanprover/lean4/pull/9225) 改进了 `congr` 策略，使它能够处理参数个数少于头函数元数的函数应用。这也修复了 `congr` 在 Mathlib 中面对取值于 `Set` 的函数时无法推进的问题，因为 `Set` 会被展开，从而让这类函数看起来像具有更高元数。

* [#9228](https://github.com/leanprover/lean4/pull/9228) 通过按需生成所需类型类，改进了 `grind ring` 的启动时间。这项优化对会数百次调用 `grind` 的文件尤其相关，例如 `tests/lean/run/grind_bitvec2.lean`。例如，在这项改动之前，`grind` 在合成类型类上会花 6.87 秒；在这个 PR 之后则为 3.92 秒。

* [#9241](https://github.com/leanprover/lean4/pull/9241) 确保用于实现 `ToInt` 适配器（在 `grind cutsat` 中）的类型类实例会按需生成。

* [#9244](https://github.com/leanprover/lean4/pull/9244) 改进`grind linarith` 模块中的实例生成。

* [#9251](https://github.com/leanprover/lean4/pull/9251) 将`Std.Do.PostCond.total` 和
`Std.Do.Triple` 进入宏,继9015年的DefEq改进之后。

* [#9267](https://github.com/leanprover/lean4/pull/9267) 优化`grind` 中`Decidable` 实例的`Decidable`支助。
`Decidable`是一个子子集,罐体不再浪费时间
使这种情况正常化,在
基准,例如`grind_bitvec2.lean`。
一致性-封闭模块模块现在处理 `Decidable` 实例,并可以
解答示例,例如:
  ```lean
  example (p q : Prop) (h₁ : Decidable p) (h₂ : Decidable (p ∧ q)) : (p ↔ q) → h₁ ≍ h₂ := by
    grind
  ```

* [#9271](https://github.com/leanprover/lean4/pull/9271) 改进了 `grind` 所使用公式归一化器的性能。

* [#9287](https://github.com/leanprover/lean4/pull/9287) 重写了 “application type mismatch” 错误消息，使参数及其类型出现在应用表达式之前。

* [#9293](https://github.com/leanprover/lean4/pull/9293) 用一个高效得多的版本替换了 `grind` 中使用的 `reduceCtorEq` simproc。`simp` 中默认使用的那个版本在这里纯属额外开销，因为 `grind` 的归一化器已经会做算术归一化。后续我们会在单独的 PR 中把这些性能改进推回默认的 `reduceCtorEq`。

* [#9305](https://github.com/leanprover/lean4/pull/9305) 在 `simp` 中使用 `mkCongrSimpForConst?` API，以减少重复生成同一 congruence 引理的次数。在这个 PR 之前，
`grind`将花费`1.5`在
`grind_bitvec2.lean`基准的正常化。
`0.6`s]. 应该在我们合并后作出更大的改变
#9300。

* [#9315](https://github.com/leanprover/lean4/pull/9315) 改进了函数应用与匹配模式中的 “invalid named argument” 错误消息：它会给出包含合法参数名的可点击提示。同时，它还修复了一个问题：这条错误消息此前会错误地把合法的匹配模式参数名标记为错误。

* [#9316](https://github.com/leanprover/lean4/pull/9316) 添加可点击的代码动作提示到“ 无效的大小写名称 ”
错误消息 。

* [#9317](https://github.com/leanprover/lean4/pull/9317) 在“丢失字段”中添加结构错误信息
实例表示一个代码动作提示,该提示插入所有缺失字段。

* [#9324](https://github.com/leanprover/lean4/pull/9324) 改进了检查两个任期是否
`grind`中的不平等

* [#9325](https://github.com/leanprover/lean4/pull/9325) 优化`grind` 中使用的布尔不平等宣传器。

* [#9326](https://github.com/leanprover/lean4/pull/9326) 优化`grind` 所使用的`propagateEqUp`。

* [#9340](https://github.com/leanprover/lean4/pull/9340) 修改了 `grind cutsat` 中使用的从 `Nat` 到 `Int` 的编码。它更简单、更可扩展，也与通用的 `ToInt` 相似。在更新 stage0 后，我们将能删除遗留部分。

* [#9351](https://github.com/leanprover/lean4/pull/9351) 优化`grind` 预处理步骤,在下列时间跳过步骤以优化`grind`预处理步骤:
该词已在散列状态表格中存在。

* [#9358](https://github.com/leanprover/lean4/pull/9358) 增加了对生成格论（协）归纳证明原理的支持，适用于通过 `mutual` 块并使用 `inductive_fixpoint`/`coinductive_fixpoint` 构造定义的谓词。

* [#9367](https://github.com/leanprover/lean4/pull/9367)对`grind` 预处理器实施微小的优化。

* [#9369](https://github.com/leanprover/lean4/pull/9369)通过跳过不必要的步骤优化`grind`预处理器
在可能的情况下。

* [#9371](https://github.com/leanprover/lean4/pull/9371) 确定一个问题,该问题造成某些`deriving` 处理人当
申报类型的名称与申报类型的名称与申报类型的名称相符。
打开命名空间 。

* [#9372](https://github.com/leanprover/lean4/pull/9372) 确定产生等式时产生的性能问题
使用含有多个
字面文字。 这个问题被 # 9322 曝光, 是由一个组合产生的 。
因素:

1. 将文学价值编集成一个依附当时值的链条
表达式。
2. 依赖如果达到后电子值的表达式费用要高得多
简化比常规简化更简单。
3. `split` 战术选择目标,将其分割,然后援引
此外,`simp` 贯穿了整个`simp`
目标是自下而上,在达到目标后不会停止。

* [#9385](https://github.com/leanprover/lean4/pull/9385) 替换了 `grind` 中 `simpEq` simproc 使用的 `isDefEq` 测试。它的开销太大了。

* [#9386](https://github.com/leanprover/lean4/pull/9386) 改进了试图从零字段结构中做投影时产生的一条令人困惑的错误消息。

* [#9387](https://github.com/leanprover/lean4/pull/9387) 在 “invalid projection” 消息中加入了一个提示：对于形如 `t.n` 的表达式，如果 `t` 是元组且 `n > 2`，会建议正确的嵌套投影写法。

* [#9395](https://github.com/leanprover/lean4/pull/9395) 修复了 `mkCongrSimpCore?` 中的一个错误，也就是 @joehendrix 在 #9388 中报告的问题。实际修复只有提交 `afc4ba617fe2ca5828e0e252558d893d7791d56b`；该 PR 的其余部分只是清理文件。

* [#9398](https://github.com/leanprover/lean4/pull/9398) 避免昂贵的`inferType`调用`simpArith`。
清理一些代码 并清除反模式。

* [#9408](https://github.com/leanprover/lean4/pull/9408) 实施简单优化:从属影响无
在 `grind` 中被长期作为电子匹配定理处理。 in
`grind_bitvec2.lean`,这一变化节省了大约3秒左右,尽可能多的
产生自足影响。例如:
  ```lean
   ∀ (h : i + 1 ≤ w), x.abs.getLsbD i = x.abs[i]
   ```

* [#9414](https://github.com/leanprover/lean4/pull/9414) 增加`isArrowProposition` 返回的个案数量
`.undef`之外的结果。本函数用于执行`.undef`
`isProof` 前提`isProof`,在《公约》
`simp`。

* [#9421](https://github.com/leanprover/lean4/pull/9421))修正导致错误解释错误的错误解释错误到“偷”
Infoview的容器在Lean网络编辑器中。

* [#9423](https://github.com/leanprover/lean4/pull/9423) 更新了“未知”
粘合器的“ 识别符号错误” 和“ 无法推断类型” 错误
以及定义。

* [#9424](https://github.com/leanprover/lean4/pull/9424) 改进了`split` 战术产生的错误信息,
包括建议采用哪些语法修正法和相关战术
可能会被混淆。

* [#9443](https://github.com/leanprover/lean4/pull/9443) 让 cdot 函数扩展把 hygiene 信息考虑在内，修复了 “parenthesis capturing” 错误；这类错误会使错误的 cdot 与宏结合时触发 cdot 扩展。例如，给定
  ```lean
  macro "baz% " t:term : term => `(1 + ($t))
  ```
`baz% ·` 过去会展开为 `1 + fun x => x`，但现在 `($t)` 中的括号不会再捕获 cdot。我们还修复了另一个疏漏：cdot 函数扩展此前忽略了类型标注和元组本应界定扩展边界这一事实；同时，引号预检查器现在也会忽略 `hygieneInfo` 中的标识符。（#9491 向括号与 cdot 语法加入了 hygiene 信息。）

* [#9447](https://github.com/leanprover/lean4/pull/9447) 确保`mvcgen` 不仅试图关闭有状况的次级目标
和纯粹的利恩目标。

* [#9448](https://github.com/leanprover/lean4/pull/9448))用嵌套感应处理倾斜崩溃(堆积溢出)
和`SizeOf` 色雷斯的生成,在#9018中报告。

* [#9451](https://github.com/leanprover/lean4/pull/9451)在采用`let`/`have`的`mintro`战略中增加支持]
类似`intro`的定点目标。
技术规格引入了这种装订装置。

* [#9454](https://github.com/leanprover/lean4/pull/9454)引入战术`mleave`,使`SPred` 证明模式
通过其抽象概念并应用一些轻度的
简化。这有益于应用自动化,例如`grind`
之后。

* [#9464](https://github.com/leanprover/lean4/pull/9464) 让 `PProdN.reduceProjs` 也去查找投影函数。此前，所有可约 redex 都由 `PProdN` 中的函数创建，它们使用原始投影；但使用 `mkAdmProj` 时，投影函数会通过 `admissible_pprod_fst` 定理的类型渗入。因此我们干脆把这两类都约化掉。

* [#9472](https://github.com/leanprover/lean4/pull/9472)将另一个问题固定在`congr_simp`
多亏约翰·科姆林创造了Mwe

* [#9476](https://github.com/leanprover/lean4/pull/9476) 在`grind cutsat` 中修补`Nat`和`Int`之间的桥梁。

* [#9479](https://github.com/leanprover/lean4/pull/9479) 改进用于评价的`evalInt?`功能
从 `ToInt` 类型类中添加的配置参数。另添加
用于处理`IsCharP`型类的新`evalNat?`函数,以及
引入配置选项 :
  ```
  grind (exp := <num>)
  ```
此选项控制了在
以前,`evalInt?`使用`whnf`,可以
当减少诸如 `2^1024` 等条件时,堆叠空间已用完 。

* [#9480](https://github.com/leanprover/lean4/pull/9480) 增加了一项功能：`structure` 构造器可以覆盖类型参数推断出的 binder kind。下面这个例子中，`toLp` 上的 `(p)` binder 会让 `p` 成为 `WithLp.toLp` 的显式参数：
  ```lean
  structure WithLp (p : Nat) (V : Type) where toLp (p) ::
    ofLp : V
  ```
这反映了 #7742 中为覆盖结构投影 binder kind 而添加的语法。类似地，只有 `structure` 头部中的参数可以更新；尝试更新通过 `variable` 引入的参数的 binder kind 会报错。

* [#9481](https://github.com/leanprover/lean4/pull/9481) 修正使用 `grind` 时发生的内核类型不匹配
含有非标准`OfNat.ofNat`术语的目标。
#9477,定理中的`0`有:
  ```lean
  (@OfNat.ofNat
    (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.closed Std.PRange.BoundShape.open)) Nat)
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```
而不是比较标准的表格:
  ```lean
  (@OfNat.ofNat
    Nat
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```

* [#9487](https://github.com/leanprover/lean4/pull/9487) 修正了`grind linarith` 所构建的不正确的证明术语,
如#9485报告的那样。

* [#9491](https://github.com/leanprover/lean4/pull/9491) 将卫生信息添加到派/图/类型
用于在#9443实施卫生点功能扩展。

* [#9496](https://github.com/leanprover/lean4/pull/9496) 改进`set_option` 生成的错误信息
命令。

* [#9500](https://github.com/leanprover/lean4/pull/9500) 在`Lean.Grind.Field` 中添加一个`HPow \a Int \a`字段,并
足以将它与行动联系起来,以便今后我们
在 `grind` 中,为避免碰撞,我们还移动
`HPow \a Nat \a` 中`Semiring`的`HPow \a Nat \a`字段,从扩展条款到`Semiring`
最后,我们添加一些失败的测试,以测试指数的正常化。

* [#9505](https://github.com/leanprover/lean4/pull/9505)删除
`Lean.Elab.Tactic.Do.VCGen` 进口时`mvcgen`
现在应该可以导入 Mathlib 并仍然使用
`mvcgen`。

* [#9506](https://github.com/leanprover/lean4/pull/9506)在`mleave` 中加上一些缺失的简化物。

* [#9507](https://github.com/leanprover/lean4/pull/9507) 使`mvcgen` `mintro` 具有拘束力。

* [#9509](https://github.com/leanprover/lean4/pull/9509) 表面内核诊断,甚至在`example` 中也是如此。

* [#9512](https://github.com/leanprover/lean4/pull/9512) 使`mframe`、`mspec`和`mvcgen`尊重卫生。
无法获取的状态假设现在可以用新的策略命名
`mrename_i` 类似`rename_i`。

* [#9516](https://github.com/leanprover/lean4/pull/9516) 确保当模块系统使私有声明变得不可访问时，相关错误消息会注明这一点。

* [#9518](https://github.com/leanprover/lean4/pull/9518) 确保先前那些 “is marked as private” 消息在模块系统下仍然会被触发。

* [#9520](https://github.com/leanprover/lean4/pull/9520)纠正9500年对`Lean.Grind.Field`的修改。

* [#9522](https://github.com/leanprover/lean4/pull/9522) 使用`withAbstractAtoms` 防止内核意外发生
键盘检查时, 减少 arith 调制器中的原子。 此 PR
在 `grind` 中还设置了 `implicitDefEqProofs := false` 归和器

* [#9532](https://github.com/leanprover/lean4/pull/9532) 概括`Process.output`和`Process.run`
`String` 论点可以划入`stdin`。

* [#9551](https://github.com/leanprover/lean4/pull/9551) 修正“ 独立消除失败” 的错误位置
用于 `cases` 策略的错误。

* [#9553](https://github.com/leanprover/lean4/pull/9553) 修正# 7830 中引入的错误, 如果光标在
说明职位
  ```lean
  example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
    induction as with
    | nil => -- 光标
    | cons b bs ih =>
  ```
然后,Infoview将显示“无目标”,而不是目标。
PPR 还修正一个单独的错误, 将光标放置在下一行
在`induction`/`cases`战术之后
  ```lean
    induction as with
    | nil => sorry
    | cons b bs ih => sorry
    I -- < 光标
  ```
将报告目标清单中的最初目标。
多次改进错误回收(包括`allGoals`型逻辑)
以及出现错误时可见的战术状态。
添加`Tactic.throwOrLogErrorAt`/`Tactic.throwOrLogError`,用于投掷或
取决于恢复状态, 记录错误 。

* [#9571](https://github.com/leanprover/lean4/pull/9571) 恢复`induction` /`cases`中`Nat`的`induction` /`cases`中`Nat` 的特征,
`zero`和`succ`标签是可悬浮的。这是在#1660中添加的,但
在#3629和#3655中,当添加自定义除尘器时断裂。 in
一般,如果感应型号`T` 的自定义除尘器`T.elim`具有
替代 `foo`,且`T.foo`是一个常数,然后是`foo` 标签
将具有`T.foo` 盘旋信息。

* [#9574](https://github.com/leanprover/lean4/pull/9574)增加备选案文`abstractProof`,以控制是否`grind`
自动为生成的证明创建辅助性定理, 或
不,没有。

* [#9575](https://github.com/leanprover/lean4/pull/9575) 优化`grind ring` 产生的证明条件。
例如,在本 PR 之前,内核用2.22秒(在M4 Max上)到
在基准`grind_ring_5.lean`中检查证明;它现在需要
仅0.63秒。

* [#9578](https://github.com/leanprover/lean4/pull/9578) 解决了`grind` 不平等证明解释中的一个问题。
当平等与`False`等同合并时出现问题
类,但它不是 其一致性等级的根, 和它的
一致性根尚未并入等值 `False`
班级尚未结束 。

* [#9579](https://github.com/leanprover/lean4/pull/9579) 确保`ite`和`dite`被选定为电子匹配模式。
它们是坏模式 因为当时的/门的树枝只是
`grind` 确定该条件是否为
`True`/`False`。

* [#9592](https://github.com/leanprover/lean4/pull/9592) 更新了归纳类型声明与匿名构造子记号产生的错误消息的样式和措辞，包括关于可推断构造子可见性更新的提示。

* [#9595](https://github.com/leanprover/lean4/pull/9595) 改进写入无效时显示的错误消息
在函数类型的自由变量上投影。

* [#9606](https://github.com/leanprover/lean4/pull/9606)在替换时在折旧警告上加注
常量具有不同的类型、可见度和/或命名空间。

* [#9625](https://github.com/leanprover/lean4/pull/9625) 改进 wf_ preprocess 周围的跟踪信息 。

* [#9628](https://github.com/leanprover/lean4/pull/9628) 引入所生成的`mutual_induct`变式
(co) 相互界定的(co)引上证明原则
与标准(co)上上上(原则)不同(该原则是项目项目)
`mutual_induct` 产生
结合所有结论。

* [#9633](https://github.com/leanprover/lean4/pull/9633) 更新由
内置战术,使其格式适应现行公约。

* [#9634](https://github.com/leanprover/lean4/pull/9634)修改点识别符号,以便`(.a : T)`解决
`T.a` 关于根命名空间,如通用域
缩写 。 这让符号指私人名称, 跟随别名,
并使用开放式命名空间。 LSP 完成后将进行改进
点识别符号是如何解决的, 但它还没有考虑到
别名或开放命名空间 。

* [#9637](https://github.com/leanprover/lean4/pull/9637) 提高了“最大宇宙水平抵消”的可读性
超过错误消息 。

* [#9646](https://github.com/leanprover/lean4/pull/9646) 使用更为简单的方法证明正在展开的理论
由有充分根据的循环来定义的函数。
(尝试)完全取消
在 `WF.Fix` 中所做的修改,使用一个专用的定理来推动
每个匹配者(或`casesOn`)的附加参数。

* [#9649](https://github.com/leanprover/lean4/pull/9649) 确定宏向多个命令展开的宏的问题
在`mutual` 内不予接受

* [#9653](https://github.com/leanprover/lean4/pull/9653)为大型造成的两个常见错误添加错误解释
删除 `Prop`。为了支持此功能,命名“已取消”
子战术投出错误后, 现在可以显示错误代码
和解释。

* [#9666](https://github.com/leanprover/lean4/pull/9666))处理模块系统中的一个突出特点,以便
自定义标记 `let rec` 和 `where` 助手声明为私有
除非这些定义是在`@[expose]`所述等公共背景下界定的。

* [#9670](https://github.com/leanprover/lean4/pull/9670) 为 `CommRing.Expr` 添加了构造子 `.intCast k` 和 `.natCast k`。我们需要它们，因为诸如 `Nat.cast (R := α) 1` 与 `(1 : α)` 这样的项在定义上并不相等。这在 Mathlib 中对数字 `0` 和 `1` 的情况非常常见。

* [#9671](https://github.com/leanprover/lean4/pull/9671) 确定`grind ring` `SMul.smul` 中`SMul.smul` 的支持。
应用程序现已正常化。例如:
  ```lean
  example (x : BitVec 2) : x - 2 • x + x = 0 := by
    grind
  ```

* [#9675](https://github.com/leanprover/lean4/pull/9675) 在 `grind cutsat` 中增加了对 `Fin.val` 的支持。示例：
  ```lean
  example (a b : Fin 2) (n : Nat) : n = 1 → ↑(a + b) ≠ n → a ≠ 0 → b = 0 → False := by
    grind

* [#9676](https://github.com/leanprover/lean4/pull/9676) 为非标准算术实例添加了规范化器。`Nat` 和 `Int` 在 `grind` 中有内建支持，它会使用这些类型的标准实例，并假定当前使用的就是这些实例。不过，用户也可能定义与标准实例在定义上相等的替代实例。该 PR 使用 simproc 来规范化这类实例。Mathlib 中确实会出现这种情况。示例：

  ```lean
  class Distrib (R : Type _) extends Mul R where

* [#9679](https://github.com/leanprover/lean4/pull/9679)对多余的`grind` 论点提出警告。

* [#9682](https://github.com/leanprover/lean4/pull/9682) 修正以优化方式引入的回归
`grind` 正常化者使用的`unfoldReducible`步,它还确保
投影功能不会减少,因为投影功能会折叠在后面
步骤。

* [#9686](https://github.com/leanprover/lean4/pull/9686) 将`clear` 适用于详细的当地宣言
预处理步骤期间。

* [#9699](https://github.com/leanprover/lean4/pull/9699) 增加关于单吨型功能的传播规则。
这一特性有助于履行所产生的核查条件
`mvcgen`,例如:

  ```lean
  example (h : (fun (_ : Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
    grind
  ```

* [#9700](https://github.com/leanprover/lean4/pull/9700)当`checkInvariants` 能够处理`checkInvariants` 违反`checkInvariants`
`grind`

* [#9701](https://github.com/leanprover/lean4/pull/9701) 开关改为非以本地 `Std.Do.Triple` `Std.Do.Triple` 符号
SpecLemmas.lean 围绕第2阶段工作 建筑故障。

* [#9702](https://github.com/leanprover/lean4/pull/9702) 将问题固定在`match` 外观变量的`match`
似乎`__x` 在当地情况下不会有这种`implDetail`。
`kindOfBinderName`现在是`LocalDeclKind.ofBinderName`。

* [#9704](https://github.com/leanprover/lean4/pull/9704) 优化`grind cutsat` 产生的证明条件。
绩效改进将在以后合并。

* [#9706](https://github.com/leanprover/lean4/pull/9706) 结合了`Poly.combine_k`和`Poly.mul_k`
`grind cutsat` 证明条款。

* [#9710](https://github.com/leanprover/lean4/pull/9710) 改进了`grind ring` 和`grind ring` 提出的某些证明条件;
`grind cutsat`。

* [#9714](https://github.com/leanprover/lean4/pull/9714)增加一个`CommRing.Expr.toPoly` 优化的`CommRing.Expr.toPoly` 版本,用于内核
我们使用此函数不仅是为了执行`grind ring`,而且是为了执行`grind ring`
将环形模块与 `grind cutsat` 接口。

* [#9716](https://github.com/leanprover/lean4/pull/9716) 将跨包装`import all` 的验证转移到Lake和
进口关键字的语法验证(`public`、`meta`和`all`)
和两个进口采样器。

* [#9728](https://github.com/leanprover/lean4/pull/9728) 固定 #9724

* [#9735](https://github.com/leanprover/lean4/pull/9735) 将9699年实施的传播规则扩大至恒定
功能。

* [#9736](https://github.com/leanprover/lean4/pull/9736) 实施选择`mvcgen +jp`,采用略微亏损的《维也纳公约》
用来防止 VC 指数爆炸的联点编码
在控制流动方面发生分裂。

* [#9754](https://github.com/leanprover/lean4/pull/9754)使`mleave`适用`at *`,并改进为下列目的而设的简化
(#9581)。

* [#9755](https://github.com/leanprover/lean4/pull/9755)实施`mrevert ∀n`战术,“eta
并且与`mintro ∀x1 ... ∀xn`目标一致。

* [#9767](https://github.com/leanprover/lean4/pull/9767) 确定`grind` 所构建的平等一致性证明条件。

* [#9772](https://github.com/leanprover/lean4/pull/9772)在投影中修正一个错误,用于对已使用的建构或推进器的投影
`grind`。 当等同时,它可以构建类型错误的术语
类中包含各种等同。

* [#9776](https://github.com/leanprover/lean4/pull/9776) 将简化和展 - 展 - 降 - 延缓这两个步骤结合起来
`grind` 以确保不错过任何可能的正常化步骤。

* [#9780](https://github.com/leanprover/lean4/pull/9780)将`grind`工作类别理论的测试套套套件扩展至`grind`
帮助调试 Mathlib 的未决问题 。

* [#9781](https://github.com/leanprover/lean4/pull/9781) 确保`mvcgen` 卫生。
现在,所有当地人都无法无障碍地介绍。

* [#9785](https://github.com/leanprover/lean4/pull/9785) 将 `MVarId.getMVarDependencies` 的一个实现细节拆分成了顶层函数。Aesop 依赖此前在 `where` 子句中定义的那个函数，而在 #9759 之后这已不再可行。

* [#9798](https://github.com/leanprover/lean4/pull/9798) 介绍`Lean.realizeValue`,新的`Lean.realizeValue`
`MetaM`计算结果的累积

* [#9800](https://github.com/leanprover/lean4/pull/9800) 改进三角洲衍生处理器,使其有能力
与装有粘合器以及能够回溯
此外,从三角洲中衍生的三角洲现在尝试所有明确的
类中的非参数参数参数, 它可以处理“ 混合” 实例
参数。`deriving` 语法已修改,以接受一般
由此可以得出具体实例,以便:
示例`deriving OfNat _ 1`或`deriving Module R`。
被允许为 pi 类型, 以添加额外的假设; 这里有一个 Mathlib
例如:
  ```lean
  def Sym (α : Type*) (n : ℕ) :=
    { s : Multiset α // Multiset.card s = n }
  deriving [DecidableEq α] → DecidableEq _
  ```
这里的下划线表示可以插入 `Sym α n` 的位置；当使用 `→` 时这是必要的。`deriving instance` 命令在进行 delta deriving 时也可以引用带作用域的变量。
例名使用 `instance` 命令的名称生成器,
将新实例添加到当前命名空间中。

* [#9804](https://github.com/leanprover/lean4/pull/9804) 允许`simp?` 、`dsimp?` 和`simp?`的引号列表中的后期逗号,
`simpa`,等等......以前,只有在非`?`变式中才允许这样做。
`simp`、`dsimp`、`simp_all`。

* [#9807](https://github.com/leanprover/lean4/pull/9807) 将`Std.List.Zipper.pref` 添加到一套`mleave`。

* [#9809](https://github.com/leanprover/lean4/pull/9809) 添加一个用于分析`grind` 电子匹配注释的脚本。
用于检测匹配循环的脚本。我们计划添加
未来运行脚本的用户定位命令 。

* [#9813](https://github.com/leanprover/lean4/pull/9813) 在 `unfoldReducible` 中修正意外的捆绑变量恐慌
`grind`。

* [#9814](https://github.com/leanprover/lean4/pull/9814)当`grind`
这一点是不需要的。

* [#9818](https://github.com/leanprover/lean4/pull/9818)在`DecidableEq`衍生处理器未在 `DecidableEq`衍生处理器中设置错误
计数时的宇宙水平考虑到宇宙水平(缩略语类型)
其建造者都无田地。关闭#9541。

* [#9819](https://github.com/leanprover/lean4/pull/9819) 使`unsafe t`术语产生一个不透明的辅助词
而不是不透明的辅助定义
减少信号。

* [#9831](https://github.com/leanprover/lean4/pull/9831) 为`Std.Range` 标记增加一个除法器。

* [#9832](https://github.com/leanprover/lean4/pull/9832) 添加了 simp 引理 `SPred.entails_<n>`，用来替代 `SPred.entails_cons`；后者由于 #8074 而不适合作为 simp 引理。

* [#9833](https://github.com/leanprover/lean4/pull/9833) 规避了 `mspec` 中一个涉及延迟赋值的 DefEq 错误。

* [#9834](https://github.com/leanprover/lean4/pull/9834) 修复了 `mvcgen` 中一个由 `wp` 应用接收到过多状态参数触发的错误；这种情况会在处理 `StateT` 原语时出现。

* [#9841](https://github.com/leanprover/lean4/pull/9841) 将嵌入纯 `p : Prop` 的p符号迁移到
`SPred σs` 扩展成简单、一阶表达式`SPred.pure p`
可在`grind`中以电子比对加以支持。

* [#9843](https://github.com/leanprover/lean4/pull/9843) 使 `mvcgen` 为生成的 VC 产生确定性的 case 标签。不变式会命名为 `inv<n>`，其余每个 VC 会命名为 `vc<n>.*`，其中 `*` 部分会粗略指示其来源。

* [#9852](https://github.com/leanprover/lean4/pull/9852) 删除 `inShareCommon` `grind`中使用的快速过滤器
`shareCommon`不再仅用于全部前处理步骤。
预处理条款。

* [#9853](https://github.com/leanprover/lean4/pull/9853) 在`grind`中增加`Nat`和`Int`数字正常化。

* [#9857](https://github.com/leanprover/lean4/pull/9857) 确保`grind` 包含宇宙的E-相配式`grind`
多晶地地面亚模式。例如,给定
  ```
  set_option pp.universes true in
  attribute [grind?] Id.run_pure
  ```
模式模式
  ```
  Id.run_pure.{u_1}: [@Id.run.{u_1} #1 (@pure.{u_1, u_1} `[Id.{u_1}] `[Applicative.toPure.{u_1, u_1}] _ #0)]
  ```
包含两个嵌套的宇宙多形态地面模式
  - `Id.{u_1}`
  - `Applicative.toPure.{u_1, u_1}`

* [#9860](https://github.com/leanprover/lean4/pull/9860) 修正 `grind` 中的 E-匹配定理激活。

* [#9865](https://github.com/leanprover/lean4/pull/9865) 进一步支持对内核型号的校对和反省
。 它处理 # 9854 所暴露的性能问题 。
PR, 每当内核类型核对表格“ eagerReduce” 的参数时
,它进入了“缩小”模式。在这个模式中,内核更多
急切要缩短用词。 新的 `eagerReduce _` 提示通常用于
以 `Eq.refl true` 换行 `Eq.refl true`。新提示不应对任何
现有的利恩包包 。

* [#9867](https://github.com/leanprover/lean4/pull/9867) 在`grind ring` 中确定一种非决定性行为。

* [#9880](https://github.com/leanprover/lean4/pull/9880)确保每个模式最多一次激活一个本地全量
`grind`。

* [#9883](https://github.com/leanprover/lean4/pull/9883) 改进多余`grind` 参数的警告信息。
并非基于实际推断模式,而是提供种类。

* [#9885](https://github.com/leanprover/lean4/pull/9885) 最初的动机是注意到 `Lean.Grind.Preorder.toLE` 会出现在冗长的 Mathlib 类型类搜索中；这项改动将阻止这些搜索。这些修改也为未来可能移除自定义 `Lean.Grind.*` 类型类、并与 #9729 引入的新类型类统一做好了准备。
9729年推出的新类型班级。
````

````markdown
````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Library"
%%%

````markdown

* [#7450](https://github.com/leanprover/lean4/pull/7450) 执行`Nat.dfold`,一个附属类似`Nat.fold`的`Nat.dfold`。

* [#9096](https://github.com/leanprover/lean4/pull/9096)删除一些不必要的`Decidable*`实例参数
`Classical`名称空间而不是`Decidable`的名称空间中使用 Lemmas
命名空间 。

* [#9121](https://github.com/leanprover/lean4/pull/9121) 允许`grind` 以`Prod` 的宇宙变体为例。

* [#9129](https://github.com/leanprover/lean4/pull/9129) 修正关于布丁等式的修饰品 , 以表示 `(!x) = y`
`(!decide (x = y)) = true`改为`(!decide (x = y)) = true`

* [#9135](https://github.com/leanprover/lean4/pull/9135) 允许将`forIn`、`foldM`和`fold`的纯`forIn`、`foldM`和`fold`结果类型
迭代器(`Iter`)在与迭代器不同的宇宙中。

* [#9142](https://github.com/leanprover/lean4/pull/9142) 使用有充分依据的重复使用修改 `Fin.reverseInduction`
使用`let rec`,从而使其定义上更平等。
@digama0合著。

  ```lean
  namespace Fin

* [#9145](https://github.com/leanprover/lean4/pull/9145) 修正了两处拼写错误。

* [#9176](https://github.com/leanprover/lean4/pull/9176) 让 `mvcgen` 对 `if` 进行拆分，而不是应用规格；这样修复了 Rish 报告的一个错误。

* [#9194](https://github.com/leanprover/lean4/pull/9194) 使 `Std.Do` 的逻辑和策略具有宇宙多态性，代价是基础情形 `SPred []` 从 `Prop` 切换到 `ULift Prop` 后，会失去一些定义性性质。

* [#9249](https://github.com/leanprover/lean4/pull/9249) 添加了定理 `BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false`，它比 `BitVec.clzAuxRec_eq_clzAuxRec_of_le` 更一般，并在 bitblaster 中取代了后者。

* [#9260](https://github.com/leanprover/lean4/pull/9260) removes uses of `Lean.RBMap` in Lean itself.

* [#9263](https://github.com/leanprover/lean4/pull/9263) 修复了 `toISO8601String`，使其生成符合 ISO 8601 格式规范的字符串。先前的实现会用 `.` 而不是 `:` 分隔分钟和秒钟部分，并且在时区偏移中没有用 `:` 分隔小时和分钟部分。

* [#9285](https://github.com/leanprover/lean4/pull/9285) removes the unnecessary requirement of `BEq α` for
  `Array.any_push`, `Array.any_push'`, `Array.all_push`, `Array.all_push'`
  as well as `Vector.any_push` and `Vector.all_push`.

* [#9301](https://github.com/leanprover/lean4/pull/9301) 为与 `Zipper` 相关的定理添加了 `simp` 和 `grind` 标注，以改进对 `Std.Do` 不变式的推理。

* [#9391](https://github.com/leanprover/lean4/pull/9391) replaces the proof of the simplification lemma `Nat.zero_mod`
  with
  `rfl` since it is, by design, a definitional equality. This solves an
  issue
  whereby the lemma could not be used by the simplifier when in 'dsimp'
  mode.

* [#9441](https://github.com/leanprover/lean4/pull/9441) 修复了 `String.prev` 的行为，使运行时实现与参考实现保持一致。具体来说，现在以下陈述成立：
  - `(s.prev p).byteIdx` is at least `p.byteIdx - 4` and at most
  `p.byteIdx - 1`
  - `s.prev 0 = 0`
  - `s.prev` is monotone

* [#9449](https://github.com/leanprover/lean4/pull/9449) fix the behavior of `String.next` on the scalar boundary (`2 ^
  63 - 1` on 64-bit platforms).

* [#9451](https://github.com/leanprover/lean4/pull/9451) 让 `mintro` 策略支持像 `intro` 一样在带状态的目标中引入 `let`/`have` binder。当规格引入此类 `let` 绑定时，这很有用。

* [#9454](https://github.com/leanprover/lean4/pull/9454) 引入了策略 `mleave`，它会通过对抽象做 eta 展开并应用一些温和的化简来退出 `SPred` 证明模式。这有助于在之后应用诸如 `grind` 之类的自动化。

* [#9504](https://github.com/leanprover/lean4/pull/9504) 又添加了一些 `*.by_wp`“充分性定理”，从而可以使用 `Std.Do` 框架证明关于 `ReaderM` 和 `ExceptM` 中程序的性质。

* [#9528](https://github.com/leanprover/lean4/pull/9528) 添加了 `List.zipWithM` 和 `Array.zipWithM`。

* [#9529](https://github.com/leanprover/lean4/pull/9529) upstreams some helper instances for `NameSet` from Batteries.

* [#9538](https://github.com/leanprover/lean4/pull/9538) 添加了两个与 `Iter.toArray` 相关的引理。

* [#9577](https://github.com/leanprover/lean4/pull/9577) 添加了关于 `UIntX.toBitVec`、`UIntX.ofBitVec` 和 `^` 的引理。

* [#9586](https://github.com/leanprover/lean4/pull/9586) 为 `Vector α n` 添加了按分量进行的代数运算以及相关实例。

* [#9594](https://github.com/leanprover/lean4/pull/9594) optimizes `Lean.Name.toString`, giving a 10% instruction
  benefit.

* [#9609](https://github.com/leanprover/lean4/pull/9609) 为 `Prod.lex_def` 添加了 `@[grind =]`。注意，`omega` 对 `Prod.Lex` 有特殊处理，而 `grind` 的 cutsat 模块要实现同等能力就需要它。

* [#9616](https://github.com/leanprover/lean4/pull/9616) 引入了检查，以确保当输入包含 NUL 字节时，IO 函数会报错（而不是忽略第一个 NUL 字节之后的所有内容）。

* [#9620](https://github.com/leanprover/lean4/pull/9620) 将 `List.pairwise_iff_forall_sublist` 的两个方向分别作为具名引理加入。

* [#9621](https://github.com/leanprover/lean4/pull/9621) renames `Xor` to `XorOp`, to match `AndOp`, etc.

* [#9622](https://github.com/leanprover/lean4/pull/9622) 补上了一个关于 `List.sum` 的缺失引理，并添加了一个 grind 标注。

* [#9701](https://github.com/leanprover/lean4/pull/9701) switches to a non-verloading local `Std.Do.Triple` notation in
  SpecLemmas.lean to work around a stage2 build failure.

* [#9721](https://github.com/leanprover/lean4/pull/9721) tags more `SInt` and `UInt` lemmas with `int_toBitVec` so
  `bv_decide`
  can handle casts between them and negation.

* [#9729](https://github.com/leanprover/lean4/pull/9729) 引入了一种为类型赋予序结构的规范方式。基础运算（`LE`、`LT`、`Min`、`Max`，以及后续 PR 中的 `BEq`、`Ord` 等）与任何更高层次的性质（预序、偏序、线序等）都按需要与 `LE` 关联起来。该 PR 为许多核心类型提供了 `IsLinearOrder` 实例，并更新了若干引理的签名。

* [#9732](https://github.com/leanprover/lean4/pull/9732) 用 Lean 而不是 C++ 重新实现了 `IO.waitAny`。这样可以减小 `task_manager` 的体积和复杂度，从而便于未来重构。

* [#9736](https://github.com/leanprover/lean4/pull/9736) implements the option `mvcgen +jp` to employ a slightly lossy VC
  encoding for join points that prevents exponential VC blowup incurred by
  naïve splitting on control flow.

* [#9739](https://github.com/leanprover/lean4/pull/9739) removes the `instance` attribute from `lexOrd` that was
  accidentally applied in `Std.Classes.Ord.Basic`.

* [#9757](https://github.com/leanprover/lean4/pull/9757) 为关键的 `Std.Do.SPred` 引理添加了 `grind` 标注。

* [#9782](https://github.com/leanprover/lean4/pull/9782) 修正了 `StdGen` 的 `Inhabited` 实例，使其为伪随机数生成器使用一个有效的初始状态。此前 `default` 生成器满足 `Prod.snd (stdNext default) = default`，因此它只会产生常量序列。

* [#9787](https://github.com/leanprover/lean4/pull/9787) 添加了 simp 引理 `PostCond.const_apply`。

* [#9792](https://github.com/leanprover/lean4/pull/9792) 为两个带 `where` 子句且 Batteries 会为其证明定理的定义添加了 `@[expose]`。

* [#9799](https://github.com/leanprover/lean4/pull/9799) 修复了 #9410 中的问题。

* [#9805](https://github.com/leanprover/lean4/pull/9805) 改进了不变式和后置条件的 API，因此对现有的 `Std.Do` 预发布 API 引入了一些破坏性变更。它还把 Markus Himmel 的 `pairsSumToZero` 示例加入为测试用例。

* [#9832](https://github.com/leanprover/lean4/pull/9832) adds simp lemmas `SPred.entails_<n>` to replace
  `SPred.entails_cons` which was dysfunctional as a simp lemma due to
  #8074.

* [#9841](https://github.com/leanprover/lean4/pull/9841) migrates the ⌜p⌝ notation for embedding pure `p : Prop` into
  `SPred σs` to expand into a simple, first-order expression `SPred.pure p`
  that can be supported by E-matching in `grind`.

* [#9848](https://github.com/leanprover/lean4/pull/9848) 为 `Std.PRange` 中的 `forIn` 和 `forIn'` 添加了 `@[spec]` 引理。

* [#9850](https://github.com/leanprover/lean4/pull/9850) 为 `Std.PRange` 记号添加了反精译器。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Compiler"
%%%

````markdown

* [#8691](https://github.com/leanprover/lean4/pull/8691) 确保当使用新编译器进行编译失败时，状态会被回滚。这对于不可计算的 section 尤其重要，因为编译器可能会生成半编译的函数，而这些函数随后可能在编译其他函数时被错误地使用。

* [#9134](https://github.com/leanprover/lean4/pull/9134) 更改 ToIR 将 `lowerEnumToScalarType?`调 `lowerEnumToScalarType?`
`ConstructorVal.induct` 而不是建造者本身的名称。
这是对新编译器中代码的某些重新设置的监督
它不应影响编译代码的运行时间(由于
LLLLDM 优化的附加标签/贴贴标签), 但它确实使
口译员的IR为口译员,效率略高。

* [#9144](https://github.com/leanprover/lean4/pull/9144) 增加支持,以更诱人的方式代表昆虫,
被归纳为向那些未能成为主要对象的国家提供支助
因为参数或无关的字段。虽然这是很好的,
它实际上的动机是希望的未来的正确性。
优化优化。 如果我们
`object`/`tobject` 保证在`object`/`tobject`
一种物体的指针,和可以贴有标记的弧弧线的指针。
特别是,在本PR测试中增加的种类,如本PR测试中增加的种类,将具有所有
以标记值编码,但按自然
扩大现有代表类型规则的范围
`object` 而不是`tobject`。

* [#9154](https://github.com/leanprover/lean4/pull/9154) 收紧了IR在申请关闭方面的打字规则。
当重读一些代码时,我意识到代码在 `mkPartialApp`中
有明确的打字牌--`.object`和`type`应互换。然而,它却被互换。
无关紧要,因为IR会过后 平息这里的不匹配。
更合理的是,必须先严格前端,要求申请
总是返回 `.object`。

* [#9159](https://github.com/leanprover/lean4/pull/9159) 在基准阶段执行不内插_覆盖内插的不内衬
目前的情况允许建造者/案件
将不匹配暴露于简单化,这引发了一种断言
失败的失败。没有早于 Expr 出现的原因是 Expr
定制的场外获取器外部操作 。

* [#9177](https://github.com/leanprover/lean4/pull/9177) 使`pullInstances` 过号避免引任何实例
含有被删除的参数的表达式, 因为我们不正确
表示在消除后继续存在的相互依存关系。

* [#9198](https://github.com/leanprover/lean4/pull/9198) 修改编译器的专业分析,以便考虑
以只会改变其特性的方式拆散的较高顺序参数
`Prop` 参数有待确定。
a 仅仅是`@[specialize]`,而不是编译器必须选择加入
更具攻击性的特定参数专业化。

* [#9207](https://github.com/leanprover/lean4/pull/9207) 让当某个对象应标记为 `noncomputable` 时所产生错误消息中的相关声明可点击跳转。

* [#9209](https://github.com/leanprover/lean4/pull/9209) 更改 `getLiteral` 的`elimDeadBranches` 的`getLiteral` 助手功能
来正确处理构造器的感带导管。此函数不是
尽可能经常使用,这使得这个问题很少被外界查问
目标测试案例。

* [#9218](https://github.com/leanprover/lean4/pull/9218) 使LCNF`elimDeadBranches` 接风器处理不安全
更小心。现在,如果不安全的排除作用的结果将只有在以下情况下才会成为_____________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________________
有循环呼叫的值流。

* [#9221](https://github.com/leanprover/lean4/pull/9221)删除有错误假设的代码,即LCNF本地 vars
`ElimDead.lean`中有其他评论意见。
声称这是不可能的,所以这一定是个改变
在开发新编译器的早期。

* [#9224](https://github.com/leanprover/lean4/pull/9224)修改`toMono` 通行证,以审议申请的类型
并删除所有与删除的参数对应的参数参数。
通过改变单体型(a)和(a)的单体型
我本想把这和
但我试图让建筑师 同样的行为
#9222(正准备编写本PR)有微小表现
后退其实是变化的附带因素。 尽管如此,我还是决定
今后,我们有望
此项延伸至构建器、外部偏差等 。

* [#9266](https://github.com/leanprover/lean4/pull/9266)对LCNF单型`.mdata`增加支持(然后将其丢弃)
在 IR 类型级别, 而不是在 IR 类型级别上 。 这更符合
旧编译器 C++ 代码中的 Excter Excter 编辑器的 C++ 代码
用于当前创建外部解码, 并将很快被替换 。

* [#9268](https://github.com/leanprover/lean4/pull/9268) 将`lean_add_extern`/`addExtern`的执行从`lean_add_extern``lean_add_extern`]`addExtern`
C++ 进入 Lean 。 我相信是最后一个 C++ 助手功能
新编译器所依赖的库库/ 编译器目录。 I put
复制一些代码,因为此函数
需要在 CORM 中执行, 而其他 IR 函数则在
C++ 编译器被删除后, 我们可以移动 IR
函数进入 CORM 。

* [#9275](https://github.com/leanprover/lean4/pull/9275) 删除以 C++ 写入的旧编译器 。

* [#9279](https://github.com/leanprover/lean4/pull/9279) 将`compiler.extract_closed`选项移到`compiler.extract_closed`
利昂(并添加一个试验,以便它在未来被抓住)。

* [#9310](https://github.com/leanprover/lean4/pull/9310) 修正 IR 构造器参数调低以正确处理
在所有情况下,相关参数的相关参数均被传递为不相关的论点。
之所以发生这种情况,是因为建筑商的论据降低(不完整)
将LCNF-I至IR的参数下调,确定
仅采用通用辅助者函数。这很可能是由于
当新编译器还在分支上时, 不完整的重构 。

* [#9336](https://github.com/leanprover/lean4/pull/9336) 修改`trace.Compiler.result` 的`trace.Compiler.result`执行,以使用[`trace.Compiler.result`
在LCNF单体中提供而不是搜索这些设备时,这些设备被提供,而不是在LCNF单体中查找。
环境的扩展,这似乎是为了 省去环境的麻烦
打印标记前重新规范fval 身份标识符。 这意味着
`._closed` 由`extractClosed` 通行证创建的`extractClosed`号]决定现在将是
包含在输出中的输出中, 如果您
我不知道发生了什么事情。

* [#9344](https://github.com/leanprover/lean4/pull/9344) 正确缩入 `IR.FnBody.case` 的`xType` 字段
构造器。 事实证明, 这一点没有明显的后果
不正确,因为它被`Boxing`保守地重新引用
过。

* [#9393](https://github.com/leanprover/lean4/pull/9393) 修补一个不安全的把戏, 在其中, 用于 Expresss 散列表的监控器
(由指针以指针为主)是通过构建运行时间的值来创建的 。
无法成为有效的 Expr Expr 。为此选择的值
违反Expr没有
我们改成新分配的单位
=单位价值。

* [#9411](https://github.com/leanprover/lean4/pull/9411) 增加支持编制`casesOn` 分录的`casesOn`。
取决于 Elaborator 的类型检查, 以将此项限制在
`Prop` 实际可消除为`Type n`的`Prop`。
或`Prop`中不在`Prop`
该事项)。

* [#9703](https://github.com/leanprover/lean4/pull/9703) 更改了 LCNF `elimDeadBranches` pass，使其把所有非 `Nat` 的字面量类型都视为 `⊤`。事实证明，要在当前抽象值表示下正确处理所有这些类型，复杂度出人意料地高，因此最好先把这个修复落地。

* [#9720](https://github.com/leanprover/lean4/pull/9720) 清除暗示假设该类型类型的错误
无法在正在添加的测试中显示的已删除类型之间的依赖关系
发生错误时,将很难精确错误。
以LCNF类型提供的信息,目前资料很少。
价值(我不记得它曾经发现一个实际问题)
更感性地删除它。

* [#9827](https://github.com/leanprover/lean4/pull/9827) 更改 `Quot.lcInv` (编译器内部格式)的下调
`Quot.lift`中`toMono`项,以支持过量申请。

* [#9847](https://github.com/leanprover/lean4/pull/9847) 添加一个检查,以检查在此直言的内衬路径中的腐蚀性分层,
来修正旧编译器的回归 。

* [#9864](https://github.com/leanprover/lean4/pull/9864) 添加`Array.getInternal` `Array.getInternal` 和
`Array.get!Internal` 退还他们借回的论据,即没有
用于编译器在
它可以确定数组将继续持有
有效引用返回值寿命的元素。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Pretty-Printing"
%%%

````markdown

* [#8391](https://github.com/leanprover/lean4/pull/8391) 为 `Vector.mk` 添加了一个 unexpander，它会把 `Vector.mk #[...] _` 反展开为 `#v[...]`。
  ```lean
  -- 之前：
  #check #v[1, 2, 3] -- { toArray := #[1, 2, 3], size_toArray := ⋯ } : Vector Nat 3
  -- 现在：
  #check #v[1, 2, 3] -- #v[1, 2, 3] : Vector Nat 3
  ```

* [#9475](https://github.com/leanprover/lean4/pull/9475) 修复了某些语法因缺失空白建议而导致的美观打印方式。

* [#9494](https://github.com/leanprover/lean4/pull/9494) 修复了一个问题：它会导致某些错误消息试图为不存在的标识符显示悬停信息。

* [#9555](https://github.com/leanprover/lean4/pull/9555) 允许信件数据中的提示提示指定自定义预览间隔
范围超出代码动作指定的编辑区域。

* [#9778](https://github.com/leanprover/lean4/pull/9778) 修改匿名可变元的漂亮印刷版,以便使用
索引而不是内部名称。这导致较小数字
`?m.123` 中的后缀,因为索引是在给定的
相对于整个文件,因此每个文件
命令获得它自己的编号。这还没有影响精美的打印
宇宙水平的可变变量。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Documentation"
%%%

````markdown

* [#9093](https://github.com/leanprover/lean4/pull/9093)为`ToFormat.toFormat`增加一个缺失的文档。

* [#9152](https://github.com/leanprover/lean4/pull/9152)为`registerDerivingHandler`修正一个过时的`registerDerivingHandler`

* [#9593](https://github.com/leanprover/lean4/pull/9593) 大大简化`propext` 的句号。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Server"
%%%

````markdown

* [#9040](https://github.com/leanprover/lean4/pull/9040) 改进了“转到定义”的用户体验，具体包括：
  - 对类型类投影使用“转到定义”时，现在会提取参与其中的具体实例，并将它们作为可跳转的位置。例如，对 `toString 0` 中的 `toString` 使用“转到定义”将得到 `ToString.toString` 和 `ToString Nat`。
  - 对会生成带有类型类投影语法的宏使用“转到定义”时，现在也会提取参与其中的具体实例并提供跳转位置。例如，对 `1 + 1` 中的 `+` 使用“转到定义”将得到 `HAdd.hAdd`、`HAdd α α α` 和 `Add Nat`。
  - 使用“转到声明”时，现在除了精化器和解析器外，还会给出“转到定义”的全部结果。例如，对 `1 + 1` 中的 `+` 使用“转到声明”将得到 `HAdd.hAdd`、`HAdd α α α`、`Add Nat`、``macro_rules | `($x + $y) => ...`` 和 `infixl:65 " + " => HAdd.hAdd` 的结果。
  - 对类型中包含多个常量的值使用“转到类型定义”时，现在会为每个常量提供“转到定义”的结果。例如，对 `x : Array Nat` 中的 `x` 使用“转到类型定义”将得到 `Array` 和 `Nat` 的结果。

* [#9163](https://github.com/leanprover/lean4/pull/9163) 目前在服务器中禁用了由 `lake setup-file` 产生的头部。等到 Lake 在处理工作区模块时会考虑服务器给出的头部后，它会重新启用。否则，当磁盘上的文件与编辑器中的文件对该文件是否参与模块系统存在分歧时，`setup-file` 头部会产生奇怪的行为。

* [#9563](https://github.com/leanprover/lean4/pull/9563)在模糊匹配时对 `~20%` 进行某些微优化
指令获胜 。

* [#9784](https://github.com/leanprover/lean4/pull/9784)确保编辑器进度栏更好地反映实际
平行拟订的进展。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Lake"
%%%

````markdown

* [#9053](https://github.com/leanprover/lean4/pull/9053)更新Lake,以解决供过渡用的`.olean`文件
通过`modules`字段`lean --setup` 中`modules`项]的倾销进口。
表示利恩现在可以直接使用来自
湖缓藏地,无需将其定位于特定的等级
路径。

* [#9101](https://github.com/leanprover/lean4/pull/9101) 修正源文件被丢弃的# 9081 所引入的臭虫
从模块输入跟踪中取出模块输入跟踪,并且从
模块工作日志 。

* [#9162](https://github.com/leanprover/lean4/pull/9162) 修改`,ir` 文物`,ir` 内容中的关键湖用途
(h) 数据结构`r`,维持单项公约的数据结构`r`,
字符关键字名称。

* [#9165](https://github.com/leanprover/lean4/pull/9165) 修复了 Lake 创建静态归档文件过程中的两个问题。

* [#9332](https://github.com/leanprover/lean4/pull/9332)改变湖中依赖性克隆机制,以便记录
有关湖泊是克隆的信息a
在完成前(而不是在完成前)发生
开始 。 这是
对于不理解为什么湖看起来的用户来说,
被困在无
设置新工程时, 输出为 :
  ```
  λ lake +lean4 new math math
  info: downloading mathlib `lean-toolchain` file
  info: math: no previous manifest, creating one from scratch
  info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
  <hang>
  info: leanprover-community/mathlib: checking out revision 'cd11c28c6a0d514a41dd7be9a862a9c8815f8599'
  ```

* [#9434](https://github.com/leanprover/lean4/pull/9434) 改变湖中地方缓存基础设施,以恢复
缓存中的可执行文件以及共享和静态库。 这意味着
他们保留其预期姓名,有些使用案件仍然依赖这些名字。

* [#9435](https://github.com/leanprover/lean4/pull/9435) 添加了 `libPrefixOnWindows` 包与库配置选项。启用后，Lake 会在 Windows 上为静态库和共享库加上 `lib` 前缀（也就是与 Unix 上相同的方式）。

* [#9436](https://github.com/leanprover/lean4/pull/9436) 增加工作数量,直至湖生产的最终信息
在一个成功运行的 `lake build` 上。

* [#9478](https://github.com/leanprover/lean4/pull/9478)为`meta import`增加适当的湖湖支持。
湖传到`Lean'
设置。

* [#9525](https://github.com/leanprover/lean4/pull/9525) 修复湖对模块系统的处理`import all`。
以前,湖处理`import all` 同样的非模块`import`,
在过境进口树上进口所有私人数据。
两者有区别,而`import all M`只是进口私人
`M`数据的数据。 `M`的直接私人进口`M` 得到遵循,但`M`的直接私人进口
不升级。

* [#9559](https://github.com/leanprover/lean4/pull/9559)更改 `lake setup-file`,以使用服务器提供的页眉
工作空间模块。

* [#9604](https://github.com/leanprover/lean4/pull/9604) 将 Lake 生成 thin archive 的行为限制为仅用于 Windows core build（即 `bootstrap = true`）。macOS 上构建 core 时通常使用的未捆绑 `ar` 不支持 `--thin`，因此除非必要我们会避免使用它。

* [#9677](https://github.com/leanprover/lean4/pull/9677) 建筑物监测器的每个建造步骤增加建造时间(以下)
`-v` 或在[CI]中)和`--no-build` 上出现的延迟,直至`--no-build`
构建监视器完成 。 因此, [`--no-build` 失败现在将报告
其目标因需要重建而封锁了湖。

* [#9697](https://github.com/leanprover/lean4/pull/9697) 将处理固定在a`lake lean`和`lake setup-file`
多点( 如 `src/Foo.Bar.lean` ) 的库源文件 。

* [#9698](https://github.com/leanprover/lean4/pull/9698)调整 `lake query` 至无
需要文本和JSON表格,而与任何
类别也已经重新命名。此外,
仅将文本模块标题的查询格式改进为
产生有效页眉。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___23___0-_LPAR_2025-09-15_RPAR_--Other"
%%%

````markdown

* [#9106](https://github.com/leanprover/lean4/pull/9106) 修复了在不启用 `LEAN_USE_GMP` 构建时出现的 `undefined symbol: lean::mpz::divexact(lean::mpz const&, lean::mpz const&)`。

* [#9114](https://github.com/leanprover/lean4/pull/9114) 进一步改进了发布自动化，能在发往下游仓库的 bump PR 中自动纳入来自 `nightly-testing` 和 `bump/v4.X.0` 分支的内容。

* [#9659](https://github.com/leanprover/lean4/pull/9659) 确定`trace.profiler.output`选项与`trace.profiler.output`选项的兼容性
Firefox 配置文件器的新版本

````
