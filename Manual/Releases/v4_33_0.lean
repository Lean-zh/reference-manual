/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Lean.MessageSeverity

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "精益4.33.0 (2026-08-10)" =>
%%%
tag := "release-v4.33.0"
file := "v4.33.0"
%%%

此版本有 208 项更改。
除了新增的 53 项功能外，
以及下面列出的 50 个修复，
有 12 处重构更改，
11 项文档改进，
21 项性能改进，
对测试套件的 6 项改进，
以及 55 个其他变化。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights"
%%%

Lean 4.33.0 专注于响应能力和整合：编辑器在您打字时保留更多工作，`try?` 可以自行提出证明，`lia` 和 `grind` 策略得到改进，`Float` 不再是不透明的类型。继续 v4.31.0 的透明工作，它还默认启用 `backward.isDefEq.respectTransparency.types` — 这是移植时最可能需要注意的更改。

_此亮点部分由 Juanjo Madrigal 贡献。_

## 响应速度更快的编辑器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--A-More-Responsive-Editor"
%%%

几项独立的更改使交互式编辑明显更加流畅：

当只有*后面*的空格发生变化时，- [#11958](https://github.com/leanprover/lean4/pull/11958) 会阻止精译器重新运行策略。在准备下一行的策略后按回车键不再放弃其后所有内容所取得的进度。

- [#13712](https://github.com/leanprover/lean4/pull/13712) 使 `exact?`、`apply?`、`rw?` 和 `grind +locals` 停止等待同一文件中的早期定理来完成内核检查。在编辑器会话中，这通常显示为 `try?` 和 `exact?` ，似乎挂在长文件的顶部附近。

- [#14234](https://github.com/leanprover/lean4/pull/14234) 使完成、悬停和交互式术语目标看到术语级 `open … in` 或 `set_option … in` 范围的开放命名空间和选项，而不是封闭命令的开放命名空间和选项。

- [#14296](https://github.com/leanprover/lean4/pull/14296) 恢复在 `for` 循环之后引用的 `let mut` 变量上的转到定义和查找引用。

诊断也变得更加可行。 `unusedVariables` linter 现在提供下划线重命名作为适用的提示 ([#14259](https://github.com/leanprover/lean4/pull/14259))：

```lean (name := unusedVar)
def constantly (n : Nat) : Nat := 0
```
```leanOutput unusedVar (severity := warning)
Variable name `n` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _n

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```

新的 linter 会警告 `open` 实际上不会打开以给定名称 ([#14325](https://github.com/leanprover/lean4/pull/14325)) 结尾的每个命名空间：在 `namespace A` 内部，一旦上游 `A.B` 出现，`open B` 就会停止到达 `_root_.B`，这解释了随后出现的令人费解的 `unknown identifier` 错误。最后，[#14196](https://github.com/leanprover/lean4/pull/14196) 澄清了有关可还原性属性的警告。

## 自动 `try?` 建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Automatic--try___--Suggestions"
%%%

[#13830](https://github.com/leanprover/lean4/pull/13830) 让 `try?` 在缺少证明的情况下自行运行，由三个默认关闭的选项控制：

- `autoTry.onEmptyProof` — 一个空的 `by`、一个空的 `· `、一个空的 `case h => `，依此类推。
- `autoTry.onUnsolvedGoal` — 与上面类似，但也会在已经包含战术并留下目标的证据上触发；该建议被附加到已写的内容中。
- `autoTry.onSorry` — `sorry`，建议将其替换。

```lean +error (name := autoTry)
set_option autoTry.onEmptyProof true in
example (a b : Nat) : a + b = b + a := by
```
```leanOutput autoTry (severity := error)
unsolved goals
a b : Nat
⊢ a + b = b + a
```
```leanOutput autoTry (severity := information)
Try these:
  [apply] simp +arith
  [apply] simp +arith only
  [apply] grind
  [apply] grind only
```

## 战术改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Tactic-Improvements"
%%%

`lia` 在禁用电子匹配的情况下运行，因此它看不到定义引理。 [#14098](https://github.com/leanprover/lean4/pull/14098) 给它自己的 `@[lia]` 集——远小于 `@[grind]`，它保持禁用状态——并且 [#14107](https://github.com/leanprover/lean4/pull/14107) 标记 `min`/`max` 定义，结束了 {tactic}`omega` 不能简单地被 `lia` 替换的最常见情况：

```lean
example (a b : Nat) : min a b ≤ max a b := by lia
example (a b : Int) : max a b = max b a := by lia
```

{tactic}`grind` 获得传播器，用于评估 {name}`BitVec` 对文字的操作，包括通过电子图中记录的等式 ([#14393](https://github.com/leanprover/lean4/pull/14393))：

```lean
example {x : BitVec 64} (h : x = 0#64 + 42#64) :
    BitVec.extractLsb' 63 32 x = 0#32 := by grind
```

它还收集了一批正确性修复：

未标准化为 {tactic}`grind` 预期形式的 -  位向量文字可以被视为两个不同的值，在一种情况下会产生内核拒绝的证明（[#14371](https://github.com/leanprover/lean4/pull/14371) / [#14370](https://github.com/leanprover/lean4/pull/14370) / [#14379](https://github.com/leanprover/lean4/pull/14379)）；
`0 ∣ p` 形式的 -  约束可以将搜索发送到循环 ([#14373](https://github.com/leanprover/lean4/pull/14373))；
-  如果没有 `NoNatZeroDivisors` ([#14390](https://github.com/leanprover/lean4/pull/14390))，环求解器可能会丢失环中的信息；
现在可以检测并修复用户 simprocs 可能默默破坏的 - `SymM` 术语不变量 ([#14299](https://github.com/leanprover/lean4/pull/14299))。

新的 `liaSteps` 选项限制了硬线性整数算术 ([#14392](https://github.com/leanprover/lean4/pull/14392)) 的搜索。最后，仅当两个理论都已在电子图中时，才重新调整容器操作的电子匹配注释以连接两个理论，而不是一个拖入另一个。更多信息请参见 [#14177](https://github.com/leanprover/lean4/pull/14177) / [#14194](https://github.com/leanprover/lean4/pull/14194) / [#14192](https://github.com/leanprover/lean4/pull/14192) / [#14182](https://github.com/leanprover/lean4/pull/14182) / [#14178](https://github.com/leanprover/lean4/pull/14178)。

## `Float` 不再不透明
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Float--Is-No-Longer-Opaque"
%%%

{name}`Float` 和 {name}`Float32` 是没有逻辑内容的不透明类型。 [#14079](https://github.com/leanprover/lean4/pull/14079) 添加了 `Float.Model` 和 `Float32.Model`，针对 Berkeley TestFloat 案例的本机实现进行了验证，[#14091](https://github.com/leanprover/lean4/pull/14091) 重新定义了包装它们的类型，并将算术、比较和转换委托给模型。编译后的代码不受影响。这不是一个完整的浮点库 - 重点是让下游连接到 {name}`Float` 以便传输其定理。

两个后果是显而易见的。 [#14180](https://github.com/leanprover/lean4/pull/14180) 添加了一个 {name}`DecidableEq` 实例来比较位模式，这*不是* `==` 实现的 IEEE 754 关系。并且 [#14110](https://github.com/leanprover/lean4/pull/14110) 重写了 `Float.ofScientific` ，以便它正确舍入 - 它通过了 `parse-number-fxx-test-data` 套件的五百万次测试，但代价是回退路径慢得多 - 现在在内核中减少了：

```lean
def nan : Float := 0.0 / 0.0

/-- info: false -/
#guard_msgs in
#eval nan == nan

example : nan = nan := by decide
example : (0.0 : Float) ≠ -0.0 := by decide
example : 0.1 + 0.2 != 0.3 := rfl
```

该实例还支持浮点文字作为 `match` 模式 ([#14181](https://github.com/leanprover/lean4/pull/14181))，因此 `0.0` 和 `-0.0` 选择不同的分支：

```lean
def describe (x : Float) : String :=
  match x with
  | 0.0 => "zero" | -0.0 => "negative zero" | _ => "other"

/-- info: "negative zero" -/
#guard_msgs in
#eval describe (-0.0)
```

## 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Lake"
%%%

[#14235](https://github.com/leanprover/lean4/pull/14235) 使模块存档 (`.ltar`) 内容稳定：无论输入、检出路径或构建机器如何，字节相同的模块输出现在都会生成字节相同的存档，因此仅输入更改不会上传新字节，并且相同的输出会在缓存服务的各个修订版中进行重复数据删除。 [#13646](https://github.com/leanprover/lean4/pull/13646) 添加了 `requiresModuleSystem` 包选项，当没有 `module` 标头的文件导入包时发出警告； `allowNonModules` 选择退出。

两个修复消除了一类 `compiled configuration is invalid; run with '-R' to reconfigure` 故障：[#14284](https://github.com/leanprover/lean4/pull/14284) 使中断的配置留下有效跟踪，而 [#14285](https://github.com/leanprover/lean4/pull/14285) 在根本无法读取跟踪时重新配置。还有用于依赖项和链接信息的新模块方面 ([#14300](https://github.com/leanprover/lean4/pull/14300) / [#14254](https://github.com/leanprover/lean4/pull/14254))，以及带有 `exe` 模板的 `lake new`/`lake init` 不再发出库文件 ([#14366](https://github.com/leanprover/lean4/pull/14366))。

## 内核健全性修复和进一步改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Kernel-soundness-fixes-and-further-improvements"
%%%

此版本修复了 Lean 内核中的错误并提高了其稳健性。一些健全性错误只能从同一进程中运行的恶意元程序中利用（已知这是不安全的）。其他的在导出格式中仍然存在并影响 {ref "validating-comparator"}[也通过 `comparator` 进行校对]，除非也使用像 `nanoda` 这样的外部检查器。

* [PR #14498](https://github.com/leanprover/lean4/pull/14498) 防止不透明值中的自由变量。健全性错误，但不影响 `comparator` 的用户。
* [PR #14577](https://github.com/leanprover/lean4/pull/14577) 对嵌套归纳式的幻像参数的参数进行类型检查。健全性错误，影响 `comparator` 的用户。
* [PR #14607](https://github.com/leanprover/lean4/pull/14607) 添加了更多针对自由变量的检查。可能存在健全性问题，不影响 `comparator`。
* [PR #14608](https://github.com/leanprover/lean4/pull/14608) 检查递归定义中的级别参数一致性。不是已知的健全性问题，因为它只影响标记为 `partial` 或 `unsafe` 的声明。
* [PR #14609](https://github.com/leanprover/lean4/pull/14609) 修复了模块系统中的健全性问题。不影响 `comparator` 的用户。
* [PR #14613](https://github.com/leanprover/lean4/pull/14613) 识别可以标准化为 `Prop` 的级别表达式。健全性错误，影响 `comparator` 的用户。
* [PR #14615](https://github.com/leanprover/lean4/pull/14615) 为归纳处理添加了更多级别标准化。不是健全性错误。
* [PR #14616](https://github.com/leanprover/lean4/pull/14616) 拒绝在名称中使用 `_nested` 的名称，以防止与内核的嵌套归纳式内部结构发生冲突。健全性错误，但不影响 `comparator` 的用户。
* [PR #14621](https://github.com/leanprover/lean4/pull/14621) 为嵌套归纳的处理添加了更多强化。
* [PR #14631](https://github.com/leanprover/lean4/pull/14631) 在比较投影表达式时检查投影表达式的名称字段。这会使内核变硬。
* [PR #14632](https://github.com/leanprover/lean4/pull/14632) 通过显式检查更多不变量来强化内核。
* [PR #14633](https://github.com/leanprover/lean4/pull/14633) 通过更快地检查本地上下文声明的类型来强化内核。

另请参阅 [Postmortem for Kernel Soundness Bug #14576](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)。

## 重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Breaking-Changes"
%%%

### 透明度
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Breaking-Changes--Transparency"
%%%

[#13895](https://github.com/leanprover/lean4/pull/13895) 默认启用 `backward.isDefEq.respectTransparency.types`：在可约化、实例或隐式透明度处分配的元变量现在将其类型与 *隐式* 处的值类型进行比较，而不是默认透明度，并且许多现有声明被标记为隐式可约化以进行补偿。回报是对所展开的事情有更多的控制，以及更好地扩展大型项目。

破坏的症状是 {tactic}`simp`、{tactic}`grind` 或其他策略停止应用的引理，因为参数的类型在定义上不等于隐式透明时的预期类型。

*迁移：*

- `set_option backward.isDefEq.respectTransparency.types false` 恢复旧行为。尽可能缩小范围。
- 持久修复是找出为什么引理语句或目标在隐式透明度下类型不正确并解决这个问题，或者标记涉及的定义`@[implicit_reducible]`。
- 要进行诊断，请先找到 `set_option linter.tacticCheckInstances true`，然后找到 `trace.Meta.isDefEq`、`trace.Meta.isDefEq.printTransparency` 和 `trace.Meta.Tactic.simp`。在旧工具链上运行 `simp?` 显示哪个引理“应该”触发。
-  对于其语句为 {tactic}`simp` 规范化的自动生成引理（在 Mathlib 中，来自 `@[simps]` 和 `@[reassoc]`），修复通常属于生成引理的位置，而不是出现错误的位置。

相关地，[#13637](https://github.com/leanprover/lean4/pull/13637) 将旧的 `instances` 透明度一分为二，得到 `none < reducible < instances < implicit < default < all`。 `@[implicit_reducible]` 不再带有 `@[instance_reducible]` 的副作用，例如让类型类搜索看透声明；为此使用 `@[instance_reducible]` 。 `with_implicit` 策略加入 `with_reducible_and_instances`。

### 其他重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Highlights--Breaking-Changes--Other-Breaking-Changes"
%%%

- [#13956](https://github.com/leanprover/lean4/pull/13956) 通过 `maxRecDepth` 而不是物理堆栈来限制内核类型检查，从而使 `(kernel) deep recursion detected` 跨平台和构建具有确定性。深度递归代码可能需要 `set_option maxRecDepth` 碰撞。

- [#14372](https://github.com/leanprover/lean4/pull/14372) 将 `Lean.initializing`、`enableInitializersExecution` 和 `isInitializerExecutionEnabled` 从 `IO` 移动到 `BaseIO`。 `lean_enable_initializer_execution` 现在返回一个标量，因此 C FFI 调用者必须停止使用 `lean_io_result_*` 函数或 `lean_dec_ref` 处理其结果；无法适应可能会出现段错误。

- [#13679](https://github.com/leanprover/lean4/pull/13679) 阻止代码生成检查公共类型的私有构造函数。在极少数情况下，这会改变结构的 FFI 表示；该手册不再建议直接从 C 访问此类字段。

- [#14241](https://github.com/leanprover/lean4/pull/14241) 使 {tactic}`bv_decide` 使用 `ext_iff` 引理来实现结构相等，否则不对其进行推理，因此结构可能需要 `@[ext]` 或手写的外延性引理。

- [#14091](https://github.com/leanprover/lean4/pull/14091) 将 `Float.lt` 和 `Float.le` 从 `Float → Float → Prop` 更改为 `Float → Float → Bool`； {name}`LE` 和 {name}`LT` 实例不受影响。

- [#14290](https://github.com/leanprover/lean4/pull/14290) 将 `int_toBitVec` 拆分为 `SymM` 和 `MetaM` 简化集； {tactic}`simp` 调用现在应使用 `int_toBitVec_meta`。

- [#14206](https://github.com/leanprover/lean4/pull/14206) 将 Lake 的延迟文档字符串检查移动到 `linter.doc.deferred` 选项下的 linter 框架上；自定义 Verso 文档字符串元素成为双构造函数类型。

- 一轮命名空间和模块卫生重定位位于错误位置的声明 - `Int.Linear` 到 `Int.Internal.Linear` ([#14255](https://github.com/leanprover/lean4/pull/14255))，`IO.AsyncList` 到 `Lean.AsyncList` ([#14263](https://github.com/leanprover/lean4/pull/14263))，以及 [#14265](https://github.com/leanprover/lean4/pull/14265) / [#14260](https://github.com/leanprover/lean4/pull/14260) / [#14258](https://github.com/leanprover/lean4/pull/14258) / 中的更多内容[#14256](https://github.com/leanprover/lean4/pull/14256) / [#14303](https://github.com/leanprover/lean4/pull/14303) / [#14302](https://github.com/leanprover/lean4/pull/14302) / [#14293](https://github.com/leanprover/lean4/pull/14293)。 {name}`Nat.ne_of_gt` 现在是 `protected` ([#14216](https://github.com/leanprover/lean4/pull/14216))。

- Lake 的 `setup` 方面不再可从 CLI 构建，因为它生成 JSON 而不是工件 ([#14300](https://github.com/leanprover/lean4/pull/14300))。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Language"
%%%

````markdown

- [#14498](https://github.com/leanprover/lean4/pull/14498)
  修复内核不健全性：就像定义和定理一样， `opaque` 声明的值不得包含 fvar。

- [#14352](https://github.com/leanprover/lean4/pull/14352)
提供实验性 `postprocess_traces tracePostprocessor in cmd` 命令，该命令对于处理大型跟踪节点树非常有用。它运行命令 `cmd`，然后使用函数 `tracePostprocessor` 转换迹线。转换可以影响默认展开或折叠哪些节点，可以更改跟踪节点的消息，还可以添加或删除节点。
  示例：
  ```lean
  module
  meta import Lean.PostprocessTraces
  -- 展开 `synthInstance` 跟踪节点的所有祖先
  -- 为了更好地发现大型跟踪树
  postprocess_traces exposeSubtrees (ofClass `Meta.synthInstance) in
  set_option trace.Meta.isDefEq true in
  set_option trace.Meta.synthInstance true in
  def x ...
  ```

- [#14375](https://github.com/leanprover/lean4/pull/14375)
  向 `Syntax.structEq` 添加适当的借用注释。它们是必需的，因为它处于引导过程的早期，它通过 `Substring` 的引导包装器进行路由而无需借用注释。它们是相关的，因为 `Syntax.structEq` 最终会从 `alphaEq` 传递调用。

- [#14196](https://github.com/leanprover/lean4/pull/14196)
  改进了有关可还原性属性的警告和错误。部分解决#13351。

- [#14361](https://github.com/leanprover/lean4/pull/14361)
  通过尝试跳过用于传播 Universe 约束的 `check` 调用来优化 `applyAbstractResult?`。优化非常简单：它检查结果是否包含任何可以分配的元变量。

- [#14333](https://github.com/leanprover/lean4/pull/14333)
  当弃用有利于自身的声明时，会导致 `@[deprecated]` 属性错误。

- [#14325](https://github.com/leanprover/lean4/pull/14325)
  添加一个 linter，对 `open` 语句发出警告，这些语句实际上不会打开以给定名称结尾的所有命名空间。

- [#14335](https://github.com/leanprover/lean4/pull/14335)
  当非单子定义使用嵌套递归调用（例如 `f (f x)`）时，使 `partial_fixpoint` 报告有用的单调性错误，而不是令人困惑的 `Unknown constant` 错误，这要求函数是尾递归的。

- [#14330](https://github.com/leanprover/lean4/pull/14330)
  使 `tryResolve` 在成功统一目标类型与候选实例类型后直接分配目标元变量，而不是使用 `isDefEq` 重新检查类型。对于无元变量的目标来说，重新检查是多余的，而且成本可能很高。

- [#14259](https://github.com/leanprover/lean4/pull/14259)
  向 `unusedVariables` linter 添加提示，建议使用下划线重命名未引用的名称。

- [#14153](https://github.com/leanprover/lean4/pull/14153)
  为 `NameMap` 和 `NameSet` 添加 `Insert` 实例。

- [#13956](https://github.com/leanprover/lean4/pull/13956)
  通过使用现有的 `maxRecDepth` 选项而不是物理堆栈大小来限制内核类型检查，使内核的 `(kernel) deep recursion detected` 错误具有确定性。以前的限制取决于本机堆栈，因此它会因平台、构建和优化级别而异，并且无法可靠地重现；它现在是 `maxRecDepth` 单独的函数，并通过 `set_option maxRecDepth <num>` 以通常的方式引发。

- [#14297](https://github.com/leanprover/lean4/pull/14297)
  使 `do` 块的 `match (dependent := true)` 分支内的裸 `return` 目标为依赖细化的分支类型，因此像 `__FIX000__ 0 => return 0` 这样的分支会针对细化的 `do` 块结果类型进行类型检查，而不将其包装在嵌套的 `(do …)` 中。

- [#13895](https://github.com/leanprover/lean4/pull/13895)
  默认情况下启用 `backward.isDefEq.respectTransparency.types` 选项。当以可简化、实例或隐式透明度分配元变量时，这意味着元变量及其分配值的类型以隐式、先前默认的透明度进行比较。它还使许多现有的声明可以隐式简化。这一变化增强了用户对正在展开的内容的控制，从而提高了大型项目的可扩展性。

- [#14249](https://github.com/leanprover/lean4/pull/14249)
扩展 `dupNamespace` linter 以允许用户选择通过 `linter.extra.dupNamespace.consecutiveOnly` 选项来检查命名空间组件的非连续重复使用。默认情况下，仅检查连续的。选择非连续检查与 [mathlib4#39793](https://github.com/leanprover-community/mathlib4/pull/39793) 中引入的行为相匹配。

- [#14247](https://github.com/leanprover/lean4/pull/14247)
  修复了当文档字符串附加到 `coinductive` 谓词并且启用 `doc.verso` 时出现的错误（“无法解释活页夹”）。

- [#14234](https://github.com/leanprover/lean4/pull/14234)
  修复了自动完成功能（以及其他 InfoTree 驱动的使用者，例如交互式术语目标和悬停弹出窗口），以在光标位于术语级别 `open ... in <term>` 或 `set_option ... in <term>` 范围下时查看增强的 `openDecls` 和 `options` 。此前，两位精译器仅通过 `withTheReader` / `withOptions` 更新了运行时 `Core.Context`，但没有将相应的 `PartialContextInfo.commandCtx` 节点推送到 InfoTree 中；因此，消费者会看到外部命令的 `openDecls` / `options` ，并且，例如，即使在匹配的 `open` 下也提供完全限定的名称，或者忽略本地 `set_option pp.fullNames true` 渲染漂亮的目标。

- [#14214](https://github.com/leanprover/lean4/pull/14214)
  恢复leanprover/lean4#14193。它所引起的基准测试问题几乎肯定不是由它引起的，而是噪音；与用户更复杂的心智模型的负面影响相比，实际收益是微不足道的。

- [#14200](https://github.com/leanprover/lean4/pull/14200)
  导致宏中的文档字符串遵循宏定义站点（而不是其使用站点）的 `doc.verso` 选项的值。之前，使用了 use-site 选项，因此无法在选项值不一致的上下文中使用宏，因为解析的格式不正确。现在，无论选项的本地设置如何，都会使用语法中的解析格式。

- [#14198](https://github.com/leanprover/lean4/pull/14198)
  修复了以下错误：在存在 `_` 参数的情况下以及在宏生成的声明中，对于不带括号的绑定程序，按名称引用参数失败。

- [#14191](https://github.com/leanprover/lean4/pull/14191)
  修复了 Verso 内容中有效块打开位置中的行开头的转义内容被跳过的问题，就好像它是空格一样。

- [#14193](https://github.com/leanprover/lean4/pull/14193)
  将传播到解析器的选项限制为以 `doc.verso` 开头的选项，以提高性能超过 #14189。

- [#14189](https://github.com/leanprover/lean4/pull/14189)
  将命令、术语和策略中使用的 set_option ... 形式的选项值传播到正文的解析中。这意味着可以更方便地启用或禁用 Verso 语法，并使 `set_option ... in ...` 在语义上与 `open ... in ...` 保持一致。

- [#14115](https://github.com/leanprover/lean4/pull/14115)
  添加了对 Verso 文档字符串的可扩展 Markdown 渲染的支持。

- [#14181](https://github.com/leanprover/lean4/pull/14181)
  让 `match` 使用 `Float` 和 `Float32` 文字作为模式，就像 `String`、`UInt64` 和其他文字类型一样。编译器使用类型的 `DecidableEq` 实例（位模式相等）将审查者与每个文字进行比较，因此例如`0.0` 和 `-0.0` 是不同的模式。支持负文字，例如 `-1.5`。

- [#14114](https://github.com/leanprover/lean4/pull/14114)
  更改了霍尔三重表示法，因此 `;` 将异常后置条件引入为单个 `EPred` 项，而不是包装在 `epost⟨…⟩` 中的异常情况列表。这让符号表示 `epost` 变量或任何 `EPred` ，并使 `epost⟨…⟩` 成为在该槽中编写的普通显式构造函数。

- [#13637](https://github.com/leanprover/lean4/pull/13637)
将 `TransparencyMode.instances` 和 `ReducibilityStatus.implicitReducible` 拆分为两个透明度级别，以便 `@[implicit_reducible]` 注释不再具有 `@[instance_reducible]` 的副作用，例如允许类型类搜索查看标记的声明。

- [#14120](https://github.com/leanprover/lean4/pull/14120)
  修复了面向语言服务器的 API，例如 `findDocString?`，它从模块系统下的 `.olean.server` 获取其信息，如果相关模块是使用 `all` 导入的，则也可以在 cmdline 上工作。

- [#14112](https://github.com/leanprover/lean4/pull/14112)
  添加 `wait_for_expected_type%` 术语阐述器，它详细阐述了针对预期类型的参数，但当该类型是未分配的元变量时会推迟。这使得符号可以推迟断言，直到通过实例综合解析 `outParam` 为止，因此裸露的 lambda 检查折叠载体，而不是将其展开为点状函数格。

````

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Library"
%%%

````markdown

- [#14303](https://github.com/leanprover/lean4/pull/14303)
  从相应的命名空间中删除内置 simprocs 用于基本类型的帮助器定义。

- [#14302](https://github.com/leanprover/lean4/pull/14302)
  将关于 `ExceptT` 的三个公共引理从 `Std.Internal.Do.WP.Lemmas` （内部模块）移至 `Init.Control.Lawful.Instances`，其中其余 `ExceptT` 引理所在。

- [#14293](https://github.com/leanprover/lean4/pull/14293)
  将公共声明 `Function.Injective.leftInverse` 从 `Init.Grind` 移出并移入 `Init.Data.Function`。

- [#14255](https://github.com/leanprover/lean4/pull/14255)
  将 `Int.Linear` 重命名为 `Int.Internal.Linear`，以更清楚地表明这些是 `omega`/`grind`/`simp +arith` 的内部实现细节，用户不应直接依赖。

- [#14265](https://github.com/leanprover/lean4/pull/14265)
  将污染公共命名空间的各种声明移至内部命名空间（如 `Lean`）。

- [#14269](https://github.com/leanprover/lean4/pull/14269)
  使 Windows 转换时间在转换秒数时使用 ceil，这可以避免丢弃小数秒并导致相差一行为。

- [#14231](https://github.com/leanprover/lean4/pull/14231)
  将 `Array.back`、`Array.back!` 和 `Array.back?` 标记为 `@[expose]`，以便在下游模块中它们的主体可用于定义缩减。以前 `decide` 无法评估来自另一个模块的 `#[1, 2, 3].back? = some 3` 等目标，即使这些函数定义的 `getElem?`/`size` 访问器已经公开。

- [#14267](https://github.com/leanprover/lean4/pull/14267)
  通过标记其内部 `loop` `semireducible` （默认情况下有根据的定义是 `irreducible` ）并公开 `foldl` ，使 `Fin.foldl` 在内核中减少，因此内核对 `Nat` 上有根据的递归的特殊支持适用。之前 `Fin.foldl` 被困在 `decide`/`#reduce`/`Decidable` 下，与已经减少的 `Fin.foldr` 不同：

  ```lean
  example : Fin.foldl 8 (fun a i => a + i.val) 0 = 28 := by decide  -- now succeeds
  ```

- [#13804](https://github.com/leanprover/lean4/pull/13804)
  在 TzIf V2 和 V3 页脚中添加 Posix TZ 字符串（生成 `RecurringRule` 类型）的解析，以便在时间戳未被 `ZoneRules` 中的转换数组覆盖的情况下，lean 可以生成时区转换。

- [#14263](https://github.com/leanprover/lean4/pull/14263)
  将 `IO.AsyncList` 重命名为 `Lean.AsyncList` 以避免污染公共 `IO` 命名空间。

- [#14260](https://github.com/leanprover/lean4/pull/14260)
  将 `Lean.Data.Lsp.Communication` 中污染全局 `IO.FS.Stream` 命名空间的一些声明移至内部命名空间。

- [#14258](https://github.com/leanprover/lean4/pull/14258)
  将 `Lean.Data.Lsp.Utf16` 中的声明从 `Char` 移动到 `Char.Internal`，从 `String` 移动到 `String.Internal`，以便 `String` 命名空间在此实现模块中不会被污染。

- [#14256](https://github.com/leanprover/lean4/pull/14256)
  将 `LLVM` 命名空间重命名为 `Lean.LLVM` 以减少对全局命名空间的污染。

- [#14252](https://github.com/leanprover/lean4/pull/14252)
通过使用廉价的随机源而不是每次调用 `getRandomBytes` 来加速 `Selectable.one`、`Selectable.combine` 和 `Selectable.tryOne`。

- [#14244](https://github.com/leanprover/lean4/pull/14244)
  将 `Quot` 文档中的“可以看到”替换为“可以看到”，并重新包装该段落以适合 100 列，而不拆分短片段。

- [#14212](https://github.com/leanprover/lean4/pull/14212)
  添加 `List.Nodup.length_le_of_subset`：作为另一个列表的子集的无重复列表不长于该列表。目前仅在电池中可用（通过 `Subperm` API）；这里直接用归纳法证明。

- [#14211](https://github.com/leanprover/lean4/pull/14211)
  添加 `List.perm_ext_iff_of_nodup`：两个无重复列表当且仅当它们具有相同的元素时才是彼此的排列。目前仅在电池中可用（通过 `Subperm` 证明）；这里直接从`perm_iff_count`证明。

- [#14210](https://github.com/leanprover/lean4/pull/14210)
  在 `List.idxOf` 和索引之间添加往返引理：`List.getElem_idxOf`（`xs[xs.idxOf x] = x`，当 `x` 出现在 `xs` 中时）和 `List.Nodup.idxOf_getElem`（`idxOf xs[i] xs = i` 对于无重复的 `xs`）。这些目前仅适用于电池。

- [#14216](https://github.com/leanprover/lean4/pull/14216)
  将 `Nat.ne_of_gt` 标记为 `protected`，以便必须通过其完全限定名称来引用它，与周围的 `Nat` 顺序引理一致。命名空间内引用相应地更新为限定名称。

- [#14209](https://github.com/leanprover/lean4/pull/14209)
  添加 `List.pairwise_lt_finRange`、`List.pairwise_le_finRange` 和 `List.nodup_finRange`，说明 `List.finRange n` 严格递增、递增且无重复。这些是有关 `finRange` 的基本事实，目前仅适用于电池。

- [#14177](https://github.com/leanprover/lean4/pull/14177)
  降低 `List.count` 和 `Array.count` 电子匹配的攻击性。以前，任何对 count 的调用都会直接触发有关过滤器的理论。但是，鉴于 `count` 有自己的一组 `grind` 注释，我们认为 `count` 应该仅在电子图中已可以调用 `filter` 时才开始与 `filter` 连接。这样我们就不会不必要地从 `count` 触发 `filter` 理论。

- [#14194](https://github.com/leanprover/lean4/pull/14194)
  通过不再每次有机会自动转换为 `drop`/`take` ，降低了 `eraseIdx` 电子匹配的攻击性。

- [#14192](https://github.com/leanprover/lean4/pull/14192)
  降低了电子匹配注释的侵略性，以根据容器的大小来限制上述 `count` 操作的结果。现在，只有当大小和计数操作都已在电子图中时才会触发它们。与 find 的注释工作方式类似。

- [#14190](https://github.com/leanprover/lean4/pull/14190)
  添加了 `Std.Internal.Do` 验证框架使用的两个小型独立的 `Lean.Order.CompleteLattice` 基础设施。

- [#14182](https://github.com/leanprover/lean4/pull/14182)
  只要 `findIdx` 可用，就会停止通过电子匹配自动将 `findIdx` 连接到 `findIdx?`，而仅在 `findIdx` 和 `findIdx?` 可用时才这样做。

- [#13799](https://github.com/leanprover/lean4/pull/13799)
  修复了 `aligned` 类型和名称顺序，因此 `Week.Ordinal.OfMonth` 现在是 `Week.OfMonth.Ordinal` 并且我们有 `Week.OfMonth.Aligned.Ordinal` 这是一个非常大的类型，但它表明我们可以有 1 到 5 对齐的周。

- [#14180](https://github.com/leanprover/lean4/pull/14180)
  实现一个 `DecidableEq Float` 实例，它检查底层位模式的相等性。

- [#14178](https://github.com/leanprover/lean4/pull/14178)
  教导grind这样一个事实：一旦`count a xs`和`a ∈ xs`出现在电子图中，使用`count a xs = 0 ↔ a ∉ xs`可能会很有趣。

- [#14116](https://github.com/leanprover/lean4/pull/14116)
使用 `Selectable.combine` 修复了死锁，还修复了 `Selectable.one` 中递归互斥锁的一个简单问题。此 PR 修复了 #14090

- [#14174](https://github.com/leanprover/lean4/pull/14174)
  更新 `Std.Time.GenericFormat.parse` 和 `Std.Time.GenericFormat.parse!` 的文档字符串，说明它们解析为 `DateTime`，匹配它们的返回类型。

- [#14110](https://github.com/leanprover/lean4/pull/14110)
  完全重写了 `Float.ofScientific` 的实现。

- [#14091](https://github.com/leanprover/lean4/pull/14091)
  更改 `Float` 和 `Float32` 类型的定义以包装 #14079 中引入的 `Float.Model` 类型。

- [#14079](https://github.com/leanprover/lean4/pull/14079)
  添加类型 `Float.Model` 和 `Float32.Model` ，它们将用作 `Float` 和 `Float32` 类型的逻辑模型。

- [#14034](https://github.com/leanprover/lean4/pull/14034)
  将霍尔三重引理 `Triple.observe` 添加到 `Std.Do` 中。它从无状态程序 `obs` 的规范中证明了 `prog` 的三元组：观察 `obs` 的后置条件 `Q` （通过 `h`）并使用 `Q` 建立 `wp⟦prog⟧ Post` （通过 `hgoal`）产生 `⦃Pre⦄ prog ⦃Post⦄`。前提 `hp` 要求 `obs` 是无状态的：它的成功运行使状态保持不变，这适用于无状态 monad 的每个程序，例如 `Except`。

- [#14067](https://github.com/leanprover/lean4/pull/14067)
  添加最弱前提条件规范引理 `Spec.monadLift_Id` ，以便 `mvcgen`/`mvcgen'` 可以释放将 `Id` 值提升到 `Pure`/`WPMonad` 变压器堆栈中的 do-bind（例如 `StateT Nat Id` 内的 `let x ← (pure 5 : Id Nat)`）。

- [#14078](https://github.com/leanprover/lean4/pull/14078)
  修复了 `IntX.ofIntClamp` 系列函数中的错误。

````

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Tactics"
%%%

````markdown

- [#14618](https://github.com/leanprover/lean4/pull/14618)
  修复使用在量词下使用 `#` 语法编写的位向量文字的目标的 `grind` 回归，例如 `example (f g : Nat → BitVec 2) (h : ∀ n, f n = g n __FIX000____FIX001____FIX002__ 1#2) : f 0 = g 0 __FIX003____FIX004____FIX005__ 1#2 := by grind`。该战术因内核错误而失败，而不是关闭目标。

- [#14393](https://github.com/leanprover/lean4/pull/14393)
  实现 `grind` 传播器，用于评估文字上的 `BitVec` 操作

- [#14392](https://github.com/leanprover/lean4/pull/14392)
  向 `grind` 添加了新的 `liaSteps` 配置选项。其动机是快速中断对硬线性整数算术问题的搜索。

- [#14390](https://github.com/leanprover/lean4/pull/14390)
  修复了 `grind` 环解算器中的问题。当环 `R` 不满足 `[NoNatZeroDivisors R]` 时，多项式简化可能会丢失信息，影响完整性。

- [#14195](https://github.com/leanprover/lean4/pull/14195)
  使用自动帧推断扩展 `vcgen`：`@[frameproc]` 属性允许程序类型注册它如何构建资源，然后 `vcgen` 在调用中携带该资源，而无需用户指定显式 `frames` 子句。成帧不再与晶格相遇相关，而是适用于任何保留连接的帧运算符，因此成本预算、分离逻辑足迹和跟踪不变量通过相同的机制进行帧处理。

- [#14379](https://github.com/leanprover/lean4/pull/14379)
  修复了 `grind` 规范化器中的引导问题。 **在**我们处理 `Init/Data/BitVec/Lemmas.lean` 之前，必须将 `BitVec.ofNatLT` 归一化定理添加到 `grind` 归一化集中。否则，模式不会正确标准化。

- [#14373](https://github.com/leanprover/lean4/pull/14373)
  修复了 `grind` 中由 `0 ∣ p` 形式的约束触发的非终止问题。

- [#14371](https://github.com/leanprover/lean4/pull/14371)
  修复了 `grind` 中由非标准化位向量文字引起的两个错误。 `BitVec.ofNatLT` 文字和超出范围的 `OfNat.ofNat` 文字（例如 `(17 : BitVec 4)`）不会简化为 `grind` 使用的 `OfNat.ofNat` 正常形式，因此同一值的两个表示形式被视为不同的值，并且 `grind` 产生被内核拒绝的无效证明：

  ```lean
  example (x : BitVec 4) (_h1 : x = BitVec.ofNatLT 1 (by decide)) (_h2 : x = 1#4) : True := by
    grind -- kernel error before this PR
  ```

- [#14370](https://github.com/leanprover/lean4/pull/14370)
修复了 `bitVecOfNat := false` 时 `BitVec` simproc 中的错误。这个错误
  影响 `grind`，因为它使用 `bitVecOfNat := false`。这是 Henrik 报告的一个例子
  这暴露了问题。

- [#14358](https://github.com/leanprover/lean4/pull/14358)
  为 `grind` 的内部信封类型 `Ring.OfSemiring.Q type` 实现快速路径。

- [#14346](https://github.com/leanprover/lean4/pull/14346)
  优化辅助 `grind` 类型 `IntModule.OfNatModule.Q` 的 `grind` 相关实例的构造。这是 Mathlib 的一个主要瓶颈。

- [#14314](https://github.com/leanprover/lean4/pull/14314)
  确保 `shareCommon` 内部缓存在 `repairAndShare` 处重用。

- [#14299](https://github.com/leanprover/lean4/pull/14299)
  使 `shareCommon` 保持 `grind` 和 `Sym.simp` 使用的 `SymM` 表示不变量：可约常量被急切地展开，并且内核投影被折叠到投影函数应用程序中。这些不变量以前仅由 `grind` 预处理器建立，并且很容易从用户 simproc 和内部代码路径中违反（例如， `Sym.inferType` 从从未预处理的环境签名返回类型），从而产生静默 E 匹配和索引失败。现在，当术语进入最大共享术语表时会检测到违规行为并自动修复。

- [#14295](https://github.com/leanprover/lean4/pull/14295)
  让 `vcgen` 处理包装在 `mdata` 节点中的程序，例如规范阐述留下的 `save_info` 注释，而不是因内部错误而失败。

- [#14290](https://github.com/leanprover/lean4/pull/14290)
  通过将 `int_toBitVec` SymM 拆分为 SymM 和 MetaM simp 集来使其兼容。 `int_toBitVec` 的现有用户现在应该在其 `simp` 调用中使用 `int_toBitVec_meta` 。

- [#14289](https://github.com/leanprover/lean4/pull/14289)
  确保 `finish?` 在需要时将 `intros` 和 `by_contra` 添加到生成的策略脚本中作为预处理步骤。

- [#14287](https://github.com/leanprover/lean4/pull/14287)
  为 `sym =>` 模式实现 `rw` 策略。
  它还将 `Lean/Elab/Tatic/Grind/Sym.lean` 分解为更小的文件。

- [#14137](https://github.com/leanprover/lean4/pull/14137)
  向 `Sym` 模式匹配器添加指针相等快速路径：当模式子项指针等于目标时，它是一个等于目标的封闭项，没有要绑定的变量，因此匹配立即成功，无需遍历子项。

- [#14281](https://github.com/leanprover/lean4/pull/14281)
  确保方程定理的 RHS 在预处理期间不会减少 zeta。此问题影响 vcgen（请参阅 @sgraf812 的新测试）。

- [#14280](https://github.com/leanprover/lean4/pull/14280)
  修复了 `sym => apply <rule>` 可以使用包含松散实例元变量的证明项来关闭目标的错误。

- [#14279](https://github.com/leanprover/lean4/pull/14279)
  在 `SymM` 中向类似 `intro` 的函数添加了新的 `hygienic` 参数。

- [#14278](https://github.com/leanprover/lean4/pull/14278)
  在 `sym =>` 模式下实现 `case => ..` 策略。它与 `vcgen` 相关（请参阅新测试）。新功能尝试在常规战术模式下模拟`case => ..`战术。

- [#14277](https://github.com/leanprover/lean4/pull/14277)
  修复了 `SymM` 中虚假的 `apply` 故障。

- [#14241](https://github.com/leanprover/lean4/pull/14241)
改变了 `bv_decide` 处理结构的方式。以前 `bv_decide` 中对结构相等的支持是有限的。现在它将使用 `ext_iff` 引理（如果可用），否则不会推理结构的相等性。这一变化应该会增加 `bv_decide` 对结构的推理能力。然而，这是一个重大更改，可能需要用户使用 `@[ext]` 注释以前存在的结构，或者以其他方式为它们定义和标记外延引理。

- [#14227](https://github.com/leanprover/lean4/pull/14227)
  重构 `bv_decide` 处理 `USize` 和 `ISize` 的方式。这对于 `bv_decide` 中的 `SymM` 支持是必需的，因为在 `SymM` 中调用 `revert` 是非法的。

- [#13830](https://github.com/leanprover/lean4/pull/13830)
  在常见的证明站点添加自动 `try?` 建议，由三个选项控制
  默认关闭：

  * `autoTry.onEmptyProof` — 建议空证明和空子证明：空 `by`，
    空 `· `、空 `case h => ` 等等。
  * `autoTry.onUnsolvedGoal` — 与 `autoTry.onEmptyProof` 类似，但也会在校样上触发
    子证明已经包含一些策略并且留下了未解决的目标。建议
    附加到现有序列（例如 `by skip` → `by skip; <found>`）。
  * `autoTry.onSorry` — 建议 `sorry` 策略；该建议*替换* `sorry`。

- [#14205](https://github.com/leanprover/lean4/pull/14205)
  停止 `impossible` 策略组合器以在
  否定之前的目标，因为这会破坏这一点。

- [#13712](https://github.com/leanprover/lean4/pull/13712)
  使 `exact?`、`apply?`、`rw?` 和 `grind +locals` 不再等待先前的异步
  定理体位于同一文件中，以在迭代当前模块时完成内核检查
  声明。之前，这些策略走`env.constants.map₂`，这迫使`env.checked`和
  因此会阻塞每个待处理的异步分支；在编辑器会话中，这表现为 `try?` 和
  `exact?` 似乎挂在长文件的顶部附近。

- [#14167](https://github.com/leanprover/lean4/pull/14167)
  在 `vcgen` 策略中添加一个 `frames` 子句，该策略将状态断言（框架）附加到匹配的程序，因此有关程序的状态的事实保持不变，即使在注册规范删除它们的调用中仍然存在。

- [#14146](https://github.com/leanprover/lean4/pull/14146)
将实验性的基于 Sym 的 `mvcgen'` 策略重命名为 `vcgen`，包括其研磨模式步骤、`with` 放电子句和 `simplifying_assumptions`/`until`/`invariants` 语法。原来的 `mvcgen` 策略没有改变。

- [#14142](https://github.com/leanprover/lean4/pull/14142)
  通过在第一次查找时将每个匹配的规范模式内部化到 `SymM` 共享表中来加速 `mvcgen'` 规范查找，因此其实例参数变得与程序的指针相等，并且不需要在以后的每次查找时重新内部化。

- [#14138](https://github.com/leanprover/lean4/pull/14138)
  修复了 `mvcegn' ... with <tac>` 的错误消息。这样做的主要动机是，当我们编写 `mvcgen' with grind` 时，用户看到的错误消息是 `unexpected identifier; expected grind`，这非常令人困惑。发生这种情况是因为我们排除了 `grind` 序列，其语法类别称为 `grind`。
  我正在为放电者策略定义一个单独的语法类别，称为 `mvcgenWith`，如果它是一种策略，则抛出更有意义的异常。

- [#14134](https://github.com/leanprover/lean4/pull/14134)
  当规则被缓存时，通过将每个向后规则的模式内部化到 `SymM` 共享表中一次，而不是在每次匹配时重新内部化其实例参数，来加速 `mvcgen'` 匹配。

- [#14080](https://github.com/leanprover/lean4/pull/14080)
  从 `WPMonad` 中提取 `WP` 类型类，以便最弱前置条件推理和 `mvcgen'` 适用于任何程序类型，而不仅仅是 monad。这可以验证深度嵌入的语言：具有 `WP` 实例但没有 `WPMonad` 实例的程序类型（例如具有自己的操作语义的归纳命令语法）现在可以使用 `Triple` 指定并由 `mvcgen'` 分解。

- [#14119](https://github.com/leanprover/lean4/pull/14119)
  修复了 `mvcgen`/`mvcgen'` 无法分割判别式望远镜相关的 `match` ，即当后面的判别式的类型提到了前面的判别式时（例如 `match n, h with` ，其中 `h : 0 < n` ）。抽象这样的匹配器之前会产生类型错误的预分割动机。

- [#14107](https://github.com/leanprover/lean4/pull/14107)
  `Nat.min_def`、`Nat.max_def`、`Int.min_def` 和 `Int.max_def` 带有 `@[lia]` 属性，因此 `lia` 策略通过电子匹配实例化它们，并且可以开箱即用地证明涉及 `min`/`max` 的目标。这解决了最常见的情况，其中 `omega` 以前可以被 `lia` 替换，但 `lia` 无法看到 `min`/`max` 定义，需要回退到完整的 `grind` 策略。

- [#14098](https://github.com/leanprover/lean4/pull/14098)
  添加了一个内置的 `@[lia]` 属性，该属性为 `lia` 策略提供了一个小的 E 匹配引理集。以前，`lia`（仅限 `cutsat` 的 `grind` 配置）在禁用 E 匹配的情况下运行，因此无法看到定义引理，例如 `Nat.max_def`。现在 `lia` 仅实例化标记为 `@[lia]` 的引理，而禁用更大的 `@[grind]` 集。

- [#14102](https://github.com/leanprover/lean4/pull/14102)
  将名称 `WhileInvariant` 从 `Std/Internal/SpecLemmas` 更改为 `RepeatInvariant`，因为在大多数情况下，在验证 `forIn` -repeat 循环时会调用它。此外，我们添加了一个新的缩写来构造 `RepeatInvarinat`s。该缩写指定了一个条件 `inv` ，它应该在每个循环迭代（甚至是中断循环）的末尾保持，以及一个条件 `onDone` ，除了 `inv`* 之外，它还应该在循环结束时保持。
  在正常的 `while` 循环的情况下，后一个总是可以被视为循环条件的否定。

- [#14099](https://github.com/leanprover/lean4/pull/14099)
在 `mvcgen'` 中添加 `⊤` 规范化。
  在 `mvcgen` 运行期间，特别是在引入额外的状态参数时，`⊤` 可能会变成 `⊤ s₁ s₂ ⋯ sₙ`。
  我正在添加一个过程，它可以动态构建 `⊤ s₁ s₂ ⋯ sₙ = ⊤` 的证明并替换它。

- [#14095](https://github.com/leanprover/lean4/pull/14095)
  当蕴含的断言格是诸如 `(a : α) → β a → Prop` 之类的依赖函数类型时，使 `mvcgen'` 报告明确的错误，而不是循环直到心跳耗尽。阶数是普通的逐点函数阶数；限制是 `mvcgen'` 的剥离规则 `Lean.Order.le_of_forall_le` 当前无法应用于从属函数晶格。

- [#14081](https://github.com/leanprover/lean4/pull/14081)
  统一 `mvcgen'` 如何将 `@[spec]` 注释转换为后向规则，使注释的优先级对方程规范生效，并拒绝既不是霍尔三元组、方程也不是要展开的定义的 `@[spec]` 注释。

- [#14089](https://github.com/leanprover/lean4/pull/14089)
  让 `mvcgen` 和 `mvcgen'` 应用 `@[spec]` 定理，其陈述是包装霍尔三元组的可简化缩写，例如 `abbrev foo.spec := ⦃P⦄ foo ⦃Q⦄`。以前，程序一直卡住，因为规范虽然已注册，但在查找时被丢弃。

- [#14015](https://github.com/leanprover/lean4/pull/14015)
  将实验性的 `mvcgen'` 策略移植到新的 `Std.Internal.Do` 元理论中，其中验证条件生成基于晶格蕴涵 `pre ⊑ wp x post epost`。在证明表面上可以看到两个变化： `mvcgen'` 现在急切地将所有状态组件引入为局部假设，因此更多事实到达 `grind`；循环不变量不再需要重述异常后置条件。

````

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Compiler"
%%%

```markdown

- [#14372](https://github.com/leanprover/lean4/pull/14372)
  moves `Lean.initializing`, `enableInitializersExecution`, and `isInitializerExecutionEnabled` to `BaseIO` from `IO`.

- [#14365](https://github.com/leanprover/lean4/pull/14365)
  ensures that `unsafe` terms get properly inlined. Previously having some unsafe term `t` occurring inline as `unsafe t` would create a separate auxiliary declaration that might not end up getting inlined.

- [#14343](https://github.com/leanprover/lean4/pull/14343)
  fixes the new 1GB stack size not being used for the main `lean` thread itself, e.g. for serialization or `--run`.

- [#14139](https://github.com/leanprover/lean4/pull/14139)
  disables symbol stripping of our libleanshared.so in release mode again. As it turns out `--strip-unneeded` doesn't only strip symbols that we do not care about.

- [#14272](https://github.com/leanprover/lean4/pull/14272)
  changes `dbgTraceIfShared` to take its message borrowed (`s : @& String`), with the matching `b_obj_arg`/`b_lean_obj_arg` adjustments in the runtime and header. The C implementation only reads the string and never consumed it, so the owned argument leaked on every call; the leak goes unnoticed in typical use because string literals are compiled to persistent constants, which are exempt from reference counting. A dynamically constructed message leaks once per call. Borrowing matches what the implementation actually does and spares callers a reference-count operation. Found while auditing the runtime for the pattern fixed in #14271.

- [#13679](https://github.com/leanprover/lean4/pull/13679)
  fixes an issue where code generation broke when using structures with private fields and types inaccessible in the current scope.

- [#14127](https://github.com/leanprover/lean4/pull/14127)
  fixes a theoretical but not practical race condition on `lean_task_imp.m_canceled` by making it atomic.

- [#14108](https://github.com/leanprover/lean4/pull/14108)
  changes the `m_imp` field of `lean_task` to an atomic. This is necessary because  in `get_task_state_core` we access the `m_imp` to see if the task is finished *before* taking the mutex. Thus the memory access as it is done currently is UB.

```

# FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--FFI"
%%%

```markdown

- [#14184](https://github.com/leanprover/lean4/pull/14184)
  exports a `lean_set_initializing` symbol for users of Lean that need to emulate multiple `withImporting` calls from a C FFI.

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Documentation"
%%%

```markdown

- [#14222](https://github.com/leanprover/lean4/pull/14222)
  converts a number of comments that seem to have been clearly intended as docstrings into docstrings, avoiding those already converted in #13006.

```

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Server"
%%%

```markdown

- [#11958](https://github.com/leanprover/lean4/pull/11958)
  adjusts the elaborator and snapshot tree system so as not to rerun tactics when whitespace directly following them is changed, preventing loss of progress when preparing to type the next tactic.

- [#14296](https://github.com/leanprover/lean4/pull/14296)
  makes go-to-definition and find-references work on a `let mut` variable that is referenced after a `for` loop (or any construct that threads mutable state through a tuple).

```

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Lake"
%%%

```markdown

- [#14366](https://github.com/leanprover/lean4/pull/14366)
  fixes `lake new` and `lake init` to not emit library files on the `exe` template. It also fixes a related bug where the commands could sometimes overwrite library files for existing packages.

- [#14300](https://github.com/leanprover/lean4/pull/14300)
  adds the `presetup`, `depTrace`, and `depHash` facets, which provide different views of a module's full set of dependencies. Also, the `setup` facet is no longer buildable on the CLI (as it produces JSON and not artifacts) and now includes full set of transitive import artifacts, fixing their absence from `lake lean`'s `setup.json`.

- [#14364](https://github.com/leanprover/lean4/pull/14364)
  adds `getLakeSharedDynlib` to the Lake API. It is a simple monadic convenience function that retrieves `LakeInstall.sharedDynlib` for the detected Lake installation.

- [#14285](https://github.com/leanprover/lean4/pull/14285)
  makes Lake reconfigure when it cannot read the configuration trace, instead of aborting with `error: compiled configuration is invalid; run with '-R' to reconfigure`. `importConfigFile` already reconfigures automatically for a stale, wrong-toolchain, or partially-malformed trace; an unparsable trace is no more informative than a missing one, so it is now handled the same way — routed into the same `elabConfig (← acquireTrace h) …` path — recovering on its own rather than requiring a manual `-R`. When the trace has no usable `options` field it falls back to `cfg.lakeOpts`, the same options value the fresh-configure branch uses when no trace exists.

- [#14284](https://github.com/leanprover/lean4/pull/14284)
  makes an interrupted Lake configuration recoverable. `importConfigFile` writes the compiled-configuration trace to a buffered handle and then calls `IO.FS.Handle.truncate` — which sets the file size but does not flush buffered writes, as its own docstring notes — before the potentially slow configuration elaboration. A `lake` process killed in that window (an interrupted or cancelled build) leaves the trace on disk as a NUL-byte size placeholder with no `.olean`, so later invocations fail with `error: compiled configuration is invalid; run with '-R' to reconfigure`. Flushing the complete trace before truncating and elaborating means an interruption instead leaves a valid trace and no `.olean`, which Lake's existing up-to-date check already treats as a trigger to reconfigure automatically.

- [#14254](https://github.com/leanprover/lean4/pull/14254)
  adds two new module facets: `linkInfoExport` and `linkInfoNoExport`. They provide information on how to link a module. It also provides `Sync` variants for `buildSharedLib`, `buildLeanSharedLib`, and `buildLeanExe` that work from within a `Job` rather than across them.

- [#14235](https://github.com/leanprover/lean4/pull/14235)
  makes Lake's module archives (`.ltar`) content-stable: byte-identical module outputs now produce a byte-identical archive regardless of the inputs, checkout path, or machine that built them, so input-only changes (e.g. a comment edit in an imported module) upload no new archive bytes and identical outputs deduplicate across revisions on cache services.

- [#14206](https://github.com/leanprover/lean4/pull/14206)
  adapts the deferred docstring check mechanism to use the linter mechanism, presenting an interface akin to that of environment linters. This replaces custom CI setup with an already-used interface. Deferred checks are governed by the option `linter.doc.deferred`.

- [#14240](https://github.com/leanprover/lean4/pull/14240)
  ensures executables are executable when restored from the Lake cache even if they were not originally executable in the cache (e.g., because they were downloaded through `lake cache get`).

- [#14219](https://github.com/leanprover/lean4/pull/14219)
  adds API for retrieving the complete set of core dynamic libraries. In current terms, these are `libleanshared`, `libleanshared_1`, and `libleanshared_2`. and `libInit_shared`. These libraries have different interdependencies on Windows and Unix, so they are modelled with `Dynlib` in order to track this information.

- [#14220](https://github.com/leanprover/lean4/pull/14220)
  adds `Dynlib.runtimeOnlyDeps`. It specifies transitive dependencies that should not be linked, but need to be preloaded for `lean` elaboration when precompiling (e.g., libraries dynamically loaded at runtime via `dlopen`).

- [#14156](https://github.com/leanprover/lean4/pull/14156)
  allows modules which do not depend on any dynamic libraries to toggle `platformIndependent` between `true` and unset without a rebuild.

- [#14130](https://github.com/leanprover/lean4/pull/14130)
  fixes `Package.remoteUrl?` so an empty `remoteUrl` returns `none` and a non-empty `remoteUrl` returns `some remoteUrl`.

- [#13646](https://github.com/leanprover/lean4/pull/13646)
  adds a new Lake package option `requiresModuleSystem`. When a package sets it to `true`, Lake emits a warning whenever a non-module-system file (one without a `module` header) imports a module of the package, both from downstream consumers and from non-module files within the package itself. This signals that the package's API expects the visibility and elaboration semantics of the module system. A companion option `allowNonModules` lets an importing package opt out of these warnings, declaring that it knowingly mixes non-module-system files with module-system dependencies.

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___33___0-_LPAR_2026-08-10_RPAR_--Other"
%%%

```markdown

- [#14633](https://github.com/leanprover/lean4/pull/14633)
  makes `infer_lambda` and `infer_let` check a binder's type, and for `let` also its value, before adding the corresponding declaration to the local context, which is what `infer_pi` already did. No valid declaration changes behavior.

- [#14632](https://github.com/leanprover/lean4/pull/14632)
  is a hardening pass over the kernel. None of these commits fixes a bug reachable from ordinary Lean code: each one takes an invariant the kernel already depends on and checks it locally instead of assuming it holds elsewhere. The intent is that a future mistake in a neighbouring part of the kernel surfaces as a clean error rather than being amplified.

- [#14631](https://github.com/leanprover/lean4/pull/14631)
  makes the kernel compare the structure name when deciding whether two projection expressions are definitionally equal. Both `type_checker::is_def_eq_core` and `equiv_manager::is_equiv_core` compared only the projection index and the projected expression, ignoring `proj_sname`.

- [#14621](https://github.com/leanprover/lean4/pull/14621)
  makes the kernel recheck the declarations it adds to the environment after eliminating a nested inductive type.

- [#14616](https://github.com/leanprover/lean4/pull/14616)
  fixes a kernel bug: an inductive declaration could reference one of the auxiliary types the kernel generates when eliminating nested inductives, and end up with a stored constructor type that is ill typed. Such a declaration can only be produced with metaprogramming.

- [#14615](https://github.com/leanprover/lean4/pull/14615)
  makes the inductive checker test a resulting universe for zero up to normalization, so that `Sort (imax 1 0)` and `Sort 0` describe the same inductive type. The two spellings previously disagreed on whether a constructor field may carry data, on whether the recursor eliminates only into `Prop`, and on whether the type is a K-like reduction target. Only declarations produced with metaprogramming are affected, since the elaborator normalizes levels before the kernel sees them.

- [#14613](https://github.com/leanprover/lean4/pull/14613)
  fixes a kernel bug: a type whose sort is `Prop` only after universe normalization, such as `Sort (imax 1 0)`, was not recognized as a proposition, so the kernel allowed a non-proof field to be projected out of a proof. Such a declaration cannot be written in surface syntax and can only be produced with metaprogramming, and `nanoda` rejects it.

- [#14609](https://github.com/leanprover/lean4/pull/14609)
  fixes a soundness bug in the module system. A `partial` definition lost its `partial` marking when it crossed a module boundary, so downstream modules could use it from safe declarations. This issue can only be exploited using meta-programming.

- [#14608](https://github.com/leanprover/lean4/pull/14608)
  checks that declarations in a mutual block use the same universe parameters. The elaborator already enforces this invariant, but meta-programming can bypass it.

- [#14607](https://github.com/leanprover/lean4/pull/14607)
  adds a missing `check_no_metavar_no_fvar` checks to the kernel inductive type module. Without it, users could use metaprogramming to sneak in nested inductive declarations containing free variables or metavariables. Note that Comparator would catch this exploit, since lean4export refuses to export declarations containing free variables or metavariables.

- [#14577](https://github.com/leanprover/lean4/pull/14577)
  fixes a kernel bug where a nested inductive datatype whose parametric arguments are ill typed could be accepted.

- [#14354](https://github.com/leanprover/lean4/pull/14354)
  implements a minor optimization at `withExporting/withoutExporting`. When they call `modifyEnv` to toggle `Environment.isExporting`, and `MonadEnv` `MetaM`'s `modifyEnv` wipes all `Core` and `Meta` caches.

- [#14131](https://github.com/leanprover/lean4/pull/14131)
  fixes `finishCommentBlock` so it does not skip a `-` when it is not followed by `/`.

```
