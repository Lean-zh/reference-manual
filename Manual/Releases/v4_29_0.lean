/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.typography.quotes false

#doc (Manual) "Lean4.29.0 (2026-03-27)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

此版本有 453 项更改。除了下面列出的 112 项功能添加和 107 项修复之外，还有 30 项重构更改、21 项文档改进、29 项性能改进、26 项测试套件改进和 115 项其他更改。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights"
%%%

_Violetta Sim 帮助编写了 4.16 到 4.29 的发布亮点，Lean开发人员衷心感谢她的贡献。_


## 性能改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Performance-Improvements"
%%%

[#12082](https://github.com/leanprover/lean4/pull/12082) 和
[#12044](https://github.com/leanprover/lean4/pull/12044) 减少
通过直接在二进制文件中存储封闭项来启动时间，其中
可能，并延迟初始化剩余的而不是 at
启动。

[#12406](https://github.com/leanprover/lean4/pull/12406) 显着
减少 `bv_decide` 中 LRAT 验证检查所消耗的内存。

## 新的可扩展`do`精译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--New-Extensible--do--Elaborator"
%%%

[#12459](https://github.com/leanprover/lean4/pull/12459) 添加了一个新的，
可扩展的 `do` 精译器。用户可以通过以下方式选择加入新的精译器
取消设置选项 `backward.do.legacy`。

内置 `doElem` 语法类别的新精译器可以是
使用属性 `doElem_elab` 注册。对于新语法，另外
控制信息处理程序必须使用属性注册
`doElem_control_info` 指定新语法是否 `return`s
早期，`break`s、`continue`s 以及它重新分配的 `mut` 变量。

精译器有类型吗
``TSyntax `doElem → DoElemCont → DoElabM Expr``，其中 `DoElabM` 是
本质上 `TermElabM` 和 `DoElemCont` 代表其余部分如何
`do` 块的内容有待详细说明。请参阅文档字符串了解更多信息
详细信息。

*重大变更：*

- `let pat := rhs | otherwise` 的语法和类似的现在范围
  在随后的 `doSeq` 之上。此外，`otherwise` 和
接下来的序列现在是 `doSeqIndented` 为了不被窃取
  来自记录语法的语法。

通过取消设置选择新的 `do` 精译器时的*重大更改*
`backward.do.legacy`:

- `do` 表示法现在始终需要 `Pure`。
- `do match` 现在始终是非依赖的。有
  `do match (dependent := true)` 扩展为术语匹配
  一些相关用途的解决方法。

## mvcgen：本地上下文中的规范
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--mvcgen___-Specifications-in-the-Local-Context"
%%%

[#12395](https://github.com/leanprover/lean4/pull/12395) 添加 mvcgen
支持本地环境中的规范。示例：

```
import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

def foo (x : Id Nat → Id Nat) : Id Nat := do
  let r₁ ← x (pure 42)
  let r₂ ← x (pure 26)
  pure (r₁ + r₂)

theorem foo_spec
    (x : Id Nat → Id Nat)
    (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
    ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo, x_spec] <;> grind

def bar (k : Id Nat) : Id Nat := do
  let r ← k
  if r > 30 then return 12 else return r

example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
```

## grind：电子匹配中的高阶米勒模式支持
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--grind___-Higher-Order-Miller-Pattern-Support-in-E-matching"
%%%

[#12483](https://github.com/leanprover/lean4/pull/12483) 添加支持
用于 `grind` 电子匹配引擎中的高阶米勒模式。
以前，电子匹配模式中的 λ 参数始终是
被视为 `dontCare`，这意味着它们无法有助于匹配
或绑定模式变量。这是一个重大限制
λ 参数带有基本结构的定理，例如
`List.foldl`、`List.foldrM` 或任何采用函数的组合器
争论。

通过此更改，当模式参数是 λ 时，其主体
满足*米勒模式条件* — 即模式变量
仅适用于不同的 λ 绑定变量 - λ 是
保留为 `ho[...]` 模式。在实例化时，这些
在所有一阶之后，高阶模式通过 `isDefEq` 进行匹配
模式变量已由电子图分配。

*示例*

```
@[grind =] theorem applyFlip_spec (f : Nat → Nat → Nat) (a b : Nat)
    : applyFlip (fun x y => f y x) a b = f b a := sorry
```

模式 `applyFlip ho[fun x => fun y => #2 y x] #1 #0` 捕获
结构上的 λ 参数： `#2` （`f` 的模式变量）
应用于不同的 λ 绑定变量 `y` 和 `x`。当
`grind` 遇到 `applyFlip (fun x y => Nat.add y x) 3 4`，它绑定
`f := Nat.add` 通过 `isDefEq` 并触发重写。

## 每个本机计算一个公理
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--One-Axiom-per-Native-Computation"
%%%

[#12217](https://github.com/leanprover/lean4/pull/12217) 实现
RFC [#12216](https://github.com/leanprover/lean4/issues/12216)：本机
计算 ({tactic}`native_decide`, {tactic}`bv_decide`) 在逻辑中表示
作为每次计算的一个公理，断言所获得的相等性
来自本机计算。 `#print axiom` 将不再显示
`Lean.trustCompiler`，而是这些的自动生成的名称
公理（例如，名称中包含 `._native.bv_decide.`）。请参阅
RFC 了解更多信息。

##  `inductive`/`structure` 命令中更可靠的宇宙级别推断
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--More-Reliable-Universe-Level-Inference-in--inductive-___-structure--Commands"
%%%

[#12514](https://github.com/leanprover/lean4/pull/12514) 改进
`inductive` 和 `structure` 命令的宇宙级别推断
更加可靠并产生更好的错误消息。查看公关
描述以获取更多信息。

*重大变化。*宇宙级元变量仅存在于
构造函数字段不再提升为宇宙级别
参数：使用显式的宇宙级别参数。此次促销活动是
不一致的完成取决于归纳类型的宇宙是否
level 有一个元变量，也给用户带来了困惑，
因为这些宇宙层次不受前一种类型的限制
参数。

*重大更改。*现在递归类型不算“明显的”
`Prop` 候选人”。使用显式 `Prop` 类型前注释
递归归纳谓词。

## 更简单 `noncomputable` 语义
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Simpler--noncomputable--Semantics"
%%%

[#12028](https://github.com/leanprover/lean4/pull/12028) 给出
`noncomputable` 的语义更简单，也提高了可预测性
准备将代码生成移动到单独的构建步骤中，而无需
打破错误消息的立即生成。

具体而言，只要某个定义使用了公理或另一个 `noncomputable` 定义，现在就需要将其标记为 `noncomputable`，但以下特殊情况除外：

- 使用内部证明、类型、类型形成器和构造函数参数
  对应于（固定）感应参数被忽略
-  标记为 `@[extern]/@[implemented_by]/@[csimp]` 的函数的用途是
  被忽略
-  用于标记为 `@[macro_inline]` 的函数的应用程序，
  相反，检查内联的不可计算性

*重大更改*：此更改后，更多 `noncomputable`
可能需要比以前更多的注释来换取改进
未来的稳定。

## 实例和还原性处理的更改
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Changes-to-Instance-and-Reducibility-Handling"
%%%

v4.29.0 对还原性设置的处理带来了重大且突破性的变化。
我们解决了一个长期存在的问题：在 v4.29.0 之前，`isDefEq` 算法会影响
透明度级别高达 `.default` （即愿意展开默认透明度定义）
比较隐式参数时。

这是一个严重的问题，导致立即出现不可预测的性能问题
`isDefEq`，并隐藏了下游库中发生定义滥用的许多地方。

为了确保可扩展性并解决这些定义滥用问题，我们有
在 [#12179](https://github.com/leanprover/lean4/pull/12179) 中做出了相当颠覆性的改变，
删除此透明度级别凹凸作为默认路径。

比较隐式参数时透明度凹凸的变化可以通过两种方式控制：
* 定义可以使用新的 `@[implicit_reducible]` 属性进行标记。
  这是 `@[reducible]` 和 `@[semireducible]` 之间的中间值（即默认设置），
  因为该定义大多被视为半可简化的，除非 `isDefEq` 正在处理
  隐式参数或匹配判别式。
  请参阅 [#12247](https://github.com/leanprover/lean4/pull/12247) 和 [#12567](https://github.com/leanprover/lean4/pull/12567)。
* 选项 `set_option backward.isDefEq.respectTransparency false` 恢复 `v4.29.0` 之前的行为
  （等效地，所有半可约定义都被视为 `implicit_reducible`）。
作为向后兼容选项，这最终可能会被删除，但考虑到这一变化的破坏性，我们预计会在中期保留该选项。


由于透明度处理的这些变化，下游库中现有的定义滥用问题现在在某些地方浮现出来
以前他们没有。为了帮助解决这些问题，主要但不限于：
是由错误实现的类型类实例引起的，我们在 [#12897](https://github.com/leanprover/lean4/pull/12897) 中进行了更改
到 `inferInstanceAs` 和默认的 `deriving` 处理程序。
这些确保使用它们创建的实例不会泄漏所涉及类型的定义，
当实例以低于半可缩减的透明度缩减时。

`inferInstanceAs α` 合成 `α` 类型的实例，但现在对其进行调整以符合
预期类型 `β`，必须可以从上下文推断。

示例：
```
def D := Nat
instance : Inhabited D := inferInstanceAs (Inhabited Nat)
```

调整将确保生成的实例在以下情况下不会泄漏右侧 `Nat`
在透明度级别低于 `semireducible` 时减少，即 `D` 也不会展开。

更具体地说，给定源类型（参数）和目标类型（预期类型），
`inferInstanceAs` 合成源类型的实例，然后展开并重新包装其
根据需要添加组件（字段、嵌套实例）以使它们与目标类型兼容。的
各个步骤由以下选项表示，这些选项均默认启用并且可以
禁用以帮助移植：

* `backward.inferInstanceAs.wrap`： `inferInstanceAs` 中实例调整的主开关
和默认的派生处理程序
* `backward.inferInstanceAs.wrap.reuseSubInstances`：重用目标类型的现有实例
  对于子实例字段以避免非定义相等实例菱形
* `backward.inferInstanceAs.wrap.instances`：将不可约实例包装在辅助定义中
* `backward.inferInstanceAs.wrap.data`：将数据字段包装在辅助定义中（证明字段是
  总是包裹着）

如果您只需要合成一个实例而不需要在类型之间进行传输，请使用 `inferInstance`
相反，可能带有预期类型的类型注释。

`v4.29.0` 中的第三个重大变化是 `simp` 和 `dsimp` 不再处理类型类实例。
此行为会产生非标准实例，并导致 Mathlib 中出现问题。
请参阅 [#12244](https://github.com/leanprover/lean4/pull/12244) 和 [#12195](https://github.com/leanprover/lean4/pull/12195)。
可以恢复旧的行为

```
set_option backward.dsimp.instances true
```

或 `simp +instances` 表示 `simp`。然而，到目前为止，我们的经验是，这并不经常需要。

最后我们在 [#12172](https://github.com/leanprover/lean4/pull/12172) 中解决了一个问题
我们确定函数参数是否是实例，这对依赖于该分类的多种算法具有后续影响。
这可能会导致潜在的回归：自动化现在可能表现不同
在以前错误识别实例参数的情况下。
例如，`simp` 中的重写规则由于以下原因而未触发
现在可能会触发不正确的索引。

### 迁移指南
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Changes-to-Instance-and-Reducibility-Handling--Migration-guide"
%%%

任何想要推迟处理透明度级别变化所需的调整的项目都可以
只需使用 `set_option backward.isDefEq.respectTransparency false` 即可。

这可以在 `lakefile.toml` 中的项目范围级别上设置：
```
[leanOptions]
backward.isDefEq.respectTransparency = false
```

但是，我们鼓励您在需要它的文件中本地化该选项，
甚至在使用 `set_option backward.isDefEq.respectTransparency false in ...` 的单独声明上。
这使得开始识别代码中定义的滥用问题变得更加容易。

如果您的项目位于 Mathlib 的下游，您可能会发现以下两个脚本很有用：
* `scripts/add_set_option.py` （如果您有 Mathlib 作为依赖项，则可在 `.lake/packages/mathlib/scripts/add_set_option.py` 中使用）
  它尝试编译您的项目，并自动用 `set_option backward.isDefEq.respectTransparency false in ...` 包装任何失败的声明，
  在这种情况下，这样做可以解决失败。
* `scripts/rm_set_option.py`，它编译您的项目并标识所有出现的 `set_option backward.isDefEq.respectTransparency false in ...` ，可以将其删除而不会导致失败（在同一声明中）。
  发生这种情况可能是因为之前的更改解决了定义滥用问题。

这些脚本也可以从 Mathlib 中复制出来并在任何项目上运行。

同样，当 Mathlib 下游时，您还可以使用实验性 `#defeq_abuse in ...` 命令，
它试图识别和解释，或者至少提供线索，潜在的定义滥用问题
可以解释为什么声明当前需要 `set_option backward.isDefEq.respectTransparency false in ...`。
我们鼓励用户在 [Zulip](https://leanprover.zulipchat.com/) 上报告此命令的问题，
我们希望，随着该诊断命令的稳定，我们将能够将其作为未来Lean工具链的一部分。

我们鼓励您检查项目中所有默认透明度类型同义词的实例构造。
如果可能，您应该使用 `deriving` 处理程序，或新的 `inferInstanceAs` 精译器，
而不是编写需要展开类型同义词才能进行类型检查的术语模式结构。
`inferInstanceAs` 命令现在 *需要* 一个预期的类型。
如果您遇到错误，其中 `inferInstanceAs` 现在因未提供预期类型而给出错误，
您可能会发现您应该简单地使用 `inferInstance` 来代替。

## 宇宙级别作为输出参数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Universe-Levels-as-Output-Parameters"
%%%

[#12423](https://github.com/leanprover/lean4/pull/12423) 添加了
属性 `@[univ_out_params]` 用于指定哪些宇宙级别
应被视为输出参数。默认情况下，任何宇宙级别
任何输入参数中都没有出现的被视为输出
参数。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--Library-Highlights"
%%%

此版本包括一个新的字符串搜索基础架构，使用
对字符统一工作的多态模式系统，
谓词和字符串。参见：

- [#12333](https://github.com/leanprover/lean4/pull/12333) 添加了
将用于验证我们的基本类型类
  字符串搜索基础设施。

- [#12424](https://github.com/leanprover/lean4/pull/12424) 给出
  `LawfulToForwardSearcherModel` 的 `Slice` 模式的证明，其中
  等于证明我们实施的KMP是正确的。

该库还添加了各种内容，包括：

- [#11938](https://github.com/leanprover/lean4/pull/11938)介绍
  投影最小值和最大值，也称为“argmin/argmax”，用于
  列出在名称 `List.minOn` 和 `List.maxOn` 下。还介绍了
  `List.minIdxOn` 和 `List.maxIdxOn`，返回索引
  最小或最大元素。

- [#11994](https://github.com/leanprover/lean4/pull/11994) 提供
  更多关于列表/数组/向量之和的引理，尤其是
  `Nat` 或 `Int` 列表/数组/向量。

- [#12363](https://github.com/leanprover/lean4/pull/12363)介绍
  通过 `Vector.iter` 和 `Vector.iterM` 一起进行向量的迭代器
  与通常的引理。

- [#12452](https://github.com/leanprover/lean4/pull/12452) 上游
  `List.scanl`、`List.scanr` 及其引理从电池到
标准库。

## Lake 的新功能
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Highlights--New-Features-in-Lake"
%%%

- [#12203](https://github.com/leanprover/lean4/pull/12203) 更改
  从本地缓存传输工件，优先选择硬链接
  副本，当硬链接失败时（例如，在
  不同的文件系统）。缓存工件现在标记为只读
  防止通过硬链接路径意外损坏。

- [#12444](https://github.com/leanprover/lean4/pull/12444) 添加了
  Lake 命令行界面命令 `lake cache clean`，删除 Lake 缓存
  目录。

- [#12490](https://github.com/leanprover/lean4/pull/12490) 添加了一个
  系统范围的 Lake 配置文件并使用它来配置
  `lake cache` 使用的远程缓存服务。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Language"
%%%

* [#11963](https://github.com/leanprover/lean4/pull/11963) 更积极地激活 `getElem?_pos`，由 `c[i]` 触发。

* [#12028](https://github.com/leanprover/lean4/pull/12028) 为 `noncomputable` 提供了更简单的语义，改进了
  可预测性以及准备将代码生成移至单独的
  构建步骤不会中断错误消息的立即生成。

* [#12110](https://github.com/leanprover/lean4/pull/12110) 修复了在 `x86_64` 上求值 `(ISize.minValue
  / -1 : ISize)` 时发生的 SIGFPE 崩溃，补上了 #11624 中遗漏的情况。

* [#12159](https://github.com/leanprover/lean4/pull/12159) 使 Std.Do 的 `post` 宏宇宙通过扩展为多态
  `PUnit.unit` 而不是 `()`。

* [#12160](https://github.com/leanprover/lean4/pull/12160) 删除了对 `check` 的调用，我们希望在正常情况下传递该调用
  情况。稍后可以通过 `debug` 选项重新添加它。

* [#12164](https://github.com/leanprover/lean4/pull/12164) 在证明一个方向时使用 `.inj` 定理
  `.injEq` 定理。

* [#12179](https://github.com/leanprover/lean4/pull/12179) 确保 `isDefEq` 不会将透明度模式增加到
  `.default` 检查隐式参数是否定义时
  平等。以前的行为造成了可扩展性问题
  数学库。也就是说，这是一个非常具有颠覆性的变化。上一个
  可以使用命令恢复行为
  ```
  set_option backward.isDefEq.respectTransparency false
  ```

* [#12184](https://github.com/leanprover/lean4/pull/12184) 确保 `mspec` 策略不会分配合成不透明
  MVar 发生在目标中，就像 `apply` 策略一样。

* [#12190](https://github.com/leanprover/lean4/pull/12190) 添加了 `introSubstEq` MetaM 策略，作为对
  `intro h; subst h` 避免引入 `h : a = b`（如果可以的话）
  避免,
  在这种情况下，可以恢复 `b` 而无需恢复任何内容
  否则。加速 `injEq` 定理的生成。

* [#12217](https://github.com/leanprover/lean4/pull/12217) 实现 RFC #12216：本机计算 (`native_decide`,
  `bv_decide`) 在逻辑中表示为每次计算一个公理，
  断言从本机计算获得的相等性。
  `#print axiom` 将不再显示 `Lean.trustCompiler`，而是显示
  这些公理的自动生成的名称（例如，
  名称中的 `._native.bv_decide.`）。请参阅 RFC 了解更多信息。

* [#12219](https://github.com/leanprover/lean4/pull/12219) 修复了出现在
  `Lean.Meta.MkIffOfInductiveProp` 上游机械
  数学库。在 `toInductive` 内部，传递了错误的自由变量，
  这使得在某些情况下无法进行统一。

* [#12236](https://github.com/leanprover/lean4/pull/12236) 将 `orElse` 组合器添加到 `Sym.Simp` 的简化过程中。

* [#12243](https://github.com/leanprover/lean4/pull/12243) 修复了 #12240，其中 `deriving Ord` 因诊断信息 `Unknown identifier a✝` 而失败。

* [#12247](https://github.com/leanprover/lean4/pull/12247) 添加了新的透明度设置 `@[instance_reducible]`。我们
  用于检查声明是否具有 `instance` 可还原性，方法是使用
  `isInstance` 谓词。然而，这并不是一个可靠的解决方案
  因为：

  - 我们有作用域实例，并且 `isInstance` 仅在以下情况下返回 `true`
范围处于活动状态。

* [#12263](https://github.com/leanprover/lean4/pull/12263) 实现#12247 的第二部分。

* [#12269](https://github.com/leanprover/lean4/pull/12269) 通过设置 `isRecursive` 环境扩展来改进 #12106
  添加声明之后，但在处理属性之前，例如
  `macro_inline` 想要查看标志。修复#12268。

* [#12283](https://github.com/leanprover/lean4/pull/12283) 引入了 `cbv_opaque` 属性，允许标记
  定义不会被 `cbv` 策略展开。

* [#12285](https://github.com/leanprover/lean4/pull/12285) 实现类宇宙级别位置的缓存
  仅出现在输出参数类型中的参数。

* [#12286](https://github.com/leanprover/lean4/pull/12286) 确保类型解析缓存正确缓存结果
  包含输出参数的类型类。

* [#12324](https://github.com/leanprover/lean4/pull/12324) 将默认的 `Inhabited` 实例添加到 `Theorem` 类型。

* [#12325](https://github.com/leanprover/lean4/pull/12325) 向任何不包含警告的类类型的 `def` 添加警告
  声明适当的还原性。

* [#12329](https://github.com/leanprover/lean4/pull/12329) 添加选项 `doc.verso.module`。如果设置，它控制是否
  模块文档字符串使用 Verso 语法。如果未设置，则默认为该值
  `doc.verso` 选项。

* [#12338](https://github.com/leanprover/lean4/pull/12338) 实施 #12179 的准备工作。它实现了一个新的
`isDefEq` 中的功能确保它不会增加透明度
  检查隐式的定义相等性时将级别设置为 `.default`
  论据。这种透明度级别的提升是在Lean 3 中引入的，但它
  不是性能问题，而是影响 Mathlib。添加了
  新功能，但默认情况下处于禁用状态。

* [#12339](https://github.com/leanprover/lean4/pull/12339) 修复了 delta 导出中的钻石问题，其中
  派生实例类型中的实例隐式类参数为
  使用为基础类型而不是别名类型合成的实例。

* [#12340](https://github.com/leanprover/lean4/pull/12340) 实现了对标记为的展开类字段的更好支持
  `reducible`。例如，我们想要标记以下类型的字段
  ```
  MonadControlT.stM : Type u -> Type u
  ```
  动机类似于我们的启发式，类型定义应该
  是缩写。
  现在，假设我们想使用以下方法展开 `stM m (ExceptT ε m) α`
  `.reducible` 透明度设置，我们希望结果是`stM m m
  (MonadControl.stM m (ExceptT ε m) α)` 而不是
  `(instMonadControlTOfMonadControl m m (ExceptT ε m)).1 α`。后者
  将破坏将该字段标记为可约的意图，因为
  实例 `instMonadControlTOfMonadControl` 是 `[instance_reducible]` 并且
使用 `.reducible` 透明度时，结果项将被卡住
  模式。

* [#12353](https://github.com/leanprover/lean4/pull/12353) 通过重定向死跟踪类 `Elab.resume`
  不存在 `Elab.resuming` 。

* [#12355](https://github.com/leanprover/lean4/pull/12355) 将 `isBoolTrueExpr` 和 `isBoolFalseExpr` 函数添加到 `SymM`

* [#12391](https://github.com/leanprover/lean4/pull/12391) 使 `simpCond` 公开。需要避免代码重复
  在 #12361

* [#12395](https://github.com/leanprover/lean4/pull/12395) 添加了 `mvcgen` 对本地上下文中规范的支持。
  示例：

  ```
  import Std.Tactic.Do

  open Std.Do

  set_option mvcgen.warning false

  def foo (x : Id Nat → Id Nat) : Id Nat := do
    let r₁ ← x (pure 42)
    let r₂ ← x (pure 26)
    pure (r₁ + r₂)

  theorem foo_spec
      (x : Id Nat → Id Nat)
      (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
      ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo, x_spec] <;> grind

  def bar (k : Id Nat) : Id Nat := do
    let r ← k
    if r > 30 then return 12 else return r

  example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
  ```

* [#12407](https://github.com/leanprover/lean4/pull/12407) 与#12403 类似。

* [#12416](https://github.com/leanprover/lean4/pull/12416) 使 `Sym.Simp.toBetaApp` 公开。这是必要的
  重构 #12417 中的主要 `cbv` 简化过程。

* [#12425](https://github.com/leanprover/lean4/pull/12425) 修复了 `mvcgen` 中因 `match` 拆分不完整而导致的错误。

* [#12427](https://github.com/leanprover/lean4/pull/12427) 使 `mvcgen` 建议使用 `-trivial` ，这样做可以避免
  递归深度错误。

* [#12429](https://github.com/leanprover/lean4/pull/12429) 在生成方程之前设置 `irreducible` 属性
  用于递归定义。这可以防止这些方程被标记为
  `defeq`，这可能导致 `simp` 生成不键入的证明
  检查默认透明度。

* [#12451](https://github.com/leanprover/lean4/pull/12451) 为新的 do 精译器调用提供必要的钩子
  进入 let 和 match 精译器。

* [#12459](https://github.com/leanprover/lean4/pull/12459) 添加了一个新的、可扩展的 `do` 精译器。用户可以选择加入
  通过取消选项 `backward.do.legacy` 来创建新的精译器。

* [#12460](https://github.com/leanprover/lean4/pull/12460) 修复了 `cbv` 策略中的 `AppBuilder` 异常
  简化投影函数相关的投影（关闭
  #12457).

* [#12507](https://github.com/leanprover/lean4/pull/12507) 修复了方程定理生成失败的 #12495
  使用类似 Box 的包装器进行结构递归定义
  嵌套归纳法。

* [#12514](https://github.com/leanprover/lean4/pull/12514) 改进了 `inductive` 的宇宙级别推断，并且
  `structure` 命令更可靠并产生更好的错误
  消息。回想一下，归纳类型的主要约束是，如果
  `u` 是类型和 `u > 0` 的宇宙级别，然后每个
  构造函数字段的宇宙级别 `v` 满足 `v ≤ u`，其中
  *构造函数字段*是一个不是该类型的参数之一
  *参数*（回想一下：类型的参数是
  类型前者和所有构造函数共享的参数）。给定
  对于这个约束，`inductive` 精译器试图找到合理的
对可能存在的元变量的赋值：
  - 对于宇宙级别 `u`，选择一个作业以实现此目的
  最低级别是合理的，只要它是唯一的。
  - 对于构造函数字段，选择唯一的赋值通常是
  合理。
  - 对于类型的参数，将级别元变量提升为新的
  宇宙级参数合理。

* [#12524](https://github.com/leanprover/lean4/pull/12524) 添加了 `Std.Iter.toHashSet` 和变体。

* [#12525](https://github.com/leanprover/lean4/pull/12525) 将声明名称添加到leanchecker错误消息中以使得
  当内核拒绝声明时调试更容易。

* [#12530](https://github.com/leanprover/lean4/pull/12530) 改进了 `mvcgen` 无法解析名称时的错误消息
  规范定理。

* [#12538](https://github.com/leanprover/lean4/pull/12538) 为 v4.29 启用 `backward.whnf.reducibleClassField`。

* [#12558](https://github.com/leanprover/lean4/pull/12558) 修复了 `(kernel) declaration has metavariables` 错误
  当在依赖归纳类型索引中使用 `by` 策略时发生
  引用先前的索引：

  ```
  axiom P : Prop
  axiom Q : P → Prop
  -- 先前给出：（内核）声明具有元变量“Foo”
  inductive Foo : (h : P) → (Q (by exact h)) → Prop
  ```

* [#12564](https://github.com/leanprover/lean4/pull/12564) 修复 `getStuckMVar?` 以通过以下方式检测卡住的元变量
为钻石继承创建的辅助父投影。这些
  强制转换（例如 `AddMonoid'.toAddZero'`）未注册为常规
  预测，因为它们根据个体构建父值
  字段而不是提取单个字段。此前，
  `getStuckMVar?`遇到就会放弃，防止TC
  合成被触发。

* [#12567](https://github.com/leanprover/lean4/pull/12567) 将 `instance_reducible` 重命名为 `implicit_reducible` 并添加
  新的
  `backward.isDefEq.implicitBump` 选项准备治疗所有
  隐含的
  在定义相等性检查期间统一参数。

* [#12572](https://github.com/leanprover/lean4/pull/12572) 是 `implicit_reducible` 重构的第 2 部分（第 1 部分：
  #12567).

* [#12574](https://github.com/leanprover/lean4/pull/12574) 将 `SpecTheorems.add` 重命名为 `SpecTheorems.insert`

* [#12576](https://github.com/leanprover/lean4/pull/12576) 将 `Sym.mkPatternFromDeclWithKey` 添加到 Sym 接口中以进行泛化
  并实施`Sym.mkEqPatternFromDecl`。这对于实施很有用
  自定义类似重写的策略，想要使用 `Pattern`s
  判别树查找。

* [#12621](https://github.com/leanprover/lean4/pull/12621) 修复了 `reduceRecMatcher?` 和 `reduceProj?` 绕过的错误
`@[cbv_opaque]` 属性。这些内核级归约函数
  内部使用`whnf`，它不知道`@[cbv_opaque]`。这个
  意味着 `@[cbv_opaque]` 值在显示为匹配时展开
  判别式、递归主前提或投影目标。修复
  引入 `withCbvOpaqueGuard`，它将这些调用包装为
  `withCanUnfoldPred` 防止 `whnf` 展开 `@[cbv_opaque]`
  定义。

* [#12633](https://github.com/leanprover/lean4/pull/12633) 使 `isDefEqProj` 凹凸透明度到 `.instances` （通过
  `withInstanceConfig`) 比较类的结构参数时
  预测。这使得行为与 `isDefEqArgs` 一致，
  它已经对实例隐式参数应用了相同的凹凸
  在比较功能应用程序时。

* [#12639](https://github.com/leanprover/lean4/pull/12639) 修复了之间的交互
  `backward.whnf.reducibleClassField` 和 `isDefEqDelta` 的
  论证比较启发式。

* [#12650](https://github.com/leanprover/lean4/pull/12650) 修复了通过启用
  `backward.whnf.reducibleClassField`
  （https://github.com/leanprover/lean4/pull/12538 ）。
  `ExprDefEq` 中的 `isNonTrivialRegular` 函数正在对类进行分类
在所有透明度级别上的预测都是不平凡的，但额外的
  `.instances` 减少 `unfoldDefault` 激发了这一点
  分类仅适用于 `.reducible` 透明度。在较高的
  透明度级别，不平凡的分类导致不必要的
  `isDefEqDelta` 中级联的启发式比较尝试
  BitVec 减少，导致 `Lean.Data.Json.Parser` 的详细说明
  从 ~3.6G 指令翻倍到 ~7.2G。

* [#12698](https://github.com/leanprover/lean4/pull/12698) 将 `result? : Option TraceResult` 字段添加到 `TraceData` 并
  将其填充到 `withTraceNode` 和 `withTraceNodeBefore` 中，以便
  元程序行走跟踪树可以决定成功/失败
  在结构上而不是表情符号上的字符串匹配。

* [#12699](https://github.com/leanprover/lean4/pull/12699) 给出 `generate` 函数的“将 @Foo 应用到目标”跟踪节点
  他们自己的跟踪子类 `Meta.synthInstance.apply` 而不是共享
  父 `Meta.synthInstance` 类。

* [#12701](https://github.com/leanprover/lean4/pull/12701) 修复了 `@[implicit_reducible]` 分配给父级的方式上的差距
  结构细化期间的预测。

* [#12719](https://github.com/leanprover/lean4/pull/12719) 将 `levelZero`、`levelOne` 和 `Level.ofNat` 标记为
  `@[implicit_reducible]` 以便 `Level.ofNat 0 =?= Level.zero` 在以下情况下成功
定义相等检查器尊重透明度注释。

* [#12756](https://github.com/leanprover/lean4/pull/12756) 添加 `deriving noncomputable instance` 语法，以便
  增量派生实例可以标记为不可计算。

* [#12789](https://github.com/leanprover/lean4/pull/12789) 跳过 `deriving instance` 中不可计算的预检查，当
  实例类型是 `Prop`，因为编译器会删除证明并且
  可计算性是无关紧要的。

* [#12778](https://github.com/leanprover/lean4/pull/12778) 修复了 `getStuckMVar?` 中实例的不一致问题
  类投影函数和辅助父投影的参数
  在检查卡住的元变量之前未进行 whnf 标准化。每个
  `getStuckMVar?` 中的其他情况（递归器、商递归器、`.proj`
  节点）在递归之前通过 `whnf` 规范主要参数 — 类
  投影函数和辅助父投影是例外。

* [#12897](https://github.com/leanprover/lean4/pull/12897) 调整 `inferInstanceAs` 和 `def` `deriving` 的结果
  处理程序以符合最近加强的可还原性限制。
  当派生或推断半可简化类型定义的实例时，
  当实例减少时，定义的右侧不再泄漏
  低于半还原透明度。合成实例的组件
  （字段、嵌套实例）根据需要展开和重新包装。

* [#13043](https://github.com/leanprover/lean4/pull/13043) 修复了 `inferInstanceAs` 和默认 `deriving` 的错误
  处理程序，当在 `meta section` 内部使用时，将创建辅助
  未标记为 `meta` 的定义（通过 `normalizeInstance`）。
  这导致编译器拒绝父 `meta` 定义：

  ```
  Invalid `meta` definition `instEmptyCollectionNamePrefixRel`, `instEmptyCollectionNamePrefixRel._aux_1` not marked `meta`
  ```

* [#13059](https://github.com/leanprover/lean4/pull/13059) 切换由以下命令创建的辅助定义的元标记
  `normalizeInstance` 从使用 `isMetaSection` 到 `declName?` 模式，
  修复元部分中的 `deriving` 由于辅助定义而失败的错误
  被错误地标记为 `meta` 而实例本身却没有。

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Library"
%%%

* [#11811](https://github.com/leanprover/lean4/pull/11811) 证明成员资格是由eraseDups 保留的：一个元素
  存在于重复数据删除列表中，前提是它存在于原始列表中。

* [#11832](https://github.com/leanprover/lean4/pull/11832) 使用 `Array` 而不是 `List` 将子句存储在
  `Std.CNF`。这减少了内存占用和分配器压力
  分配器，导致巨大的 CNF 出现显着的性能变化。

* [#11936](https://github.com/leanprover/lean4/pull/11936) 提供类似于 `List.min(?)` 的 `Array` 操作
  `List.max(?)`.

* [#11938](https://github.com/leanprover/lean4/pull/11938) 引入投影最小值和最大值，也称为
  “argmin/argmax”，用于名称 `List.minOn` 下的列表和
  `List.maxOn`。它还引入了 `List.minIdxOn` 和 `List.maxIdxOn`，
  返回最小或最大元素的索引。而且，
有一些带有 `?` 后缀的变体返回 `Option`。改变
  进一步引入了相反顺序的新实例，例如
  `LE.opposite`、`IsLinearOrder.opposite` 等。此更改还添加了
  缺少 `Std.lt_irrefl` 引理。

* [#11943](https://github.com/leanprover/lean4/pull/11943) 介绍定理
  `BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend` 定理，证明
  `x.sshiftRight n` 相当于先符号扩展 `x`，提取
  适当的最低有效位，然后设置宽度
  至 `w`。

* [#11994](https://github.com/leanprover/lean4/pull/11994) 提供了更多关于列表/数组/向量之和的引理，
  特别是 `Nat` 或 `Int` 列表/数组/向量的总和。

* [#12017](https://github.com/leanprover/lean4/pull/12017) 对列表/数组/向量接口进行了一些小改进：
  * 它修复了`Init.Core`中的拼写错误。
  * 它添加了`List.isSome_min_iff`和`List.isSome_max_iff`。
  * 它将 `grind` 和 `simp` 注释添加到以前的各种注释中
  未注释的引理。
  * 它添加了用索引刻画 `∃ x ∈ xs, P x` 的引理，即 `∃
  (i : Nat), ∃ hi, P (xs[i])`，以及类似的全称量化引理：
`exists_mem_iff_exists_getElem` 和 `forall_mem_iff_forall_getElem`。
  * 它添加了`Vector.toList_zip`。
  * 它为列表/数组/向量添加了 `map_ofFn` 和 `ofFn_getElem` 。

* [#12019](https://github.com/leanprover/lean4/pull/12019) 提供 `Nat`/`Int` 引理 `x ≤ y * z ↔ (x + z - 1) / z ≤
  y`, `x ≤ y * z ↔ (x + y - 1) / y ≤ z` and `x / z + y / z ≤ (x + y) / z`。

* [#12108](https://github.com/leanprover/lean4/pull/12108) 添加 `prefix_map_iff_of_injective` 和
  Init.Data.List.Nat.Sublist 的 `suffix_map_iff_of_injective` 引理。

* [#12161](https://github.com/leanprover/lean4/pull/12161) 增加了 `Option.of_wp_eq` 和 `Except.of_wp_eq`，类似于
  现有 `Except.of_wp`。 `Except.of_wp` 已弃用，因为应用
  需要先进行泛化，此时比较方便
  使用`Except.of_wp_eq`。

* [#12162](https://github.com/leanprover/lean4/pull/12162) 添加函数 `Std.Iter.first?` 并证明规范
  引理 `Std.Iter.first?_eq_match_step` 如果迭代器是高效的。

* [#12170](https://github.com/leanprover/lean4/pull/12170) 调整了List.take/drop的研磨注释，并添加了两个
  定理。

* [#12181](https://github.com/leanprover/lean4/pull/12181) 为 `Int` 添加两个缺失的订单实例。

* [#12193](https://github.com/leanprover/lean4/pull/12193) 为 `Sigma` 和 `PSigma` 添加 `DecidableEq` 实例。

* [#12204](https://github.com/leanprover/lean4/pull/12204) 添加了显示 `find?` 和
各种索引查找功能。定理建立双向
  查找元素和查找其索引之间的关系。

* [#12212](https://github.com/leanprover/lean4/pull/12212) 添加函数 `Std.Iter.isEmpty` 并证明
  规范引理 `Std.Iter.isEmpty_eq_match_step` 和
  `Std.Iter.isEmpty_toList` 如果迭代器有效。

* [#12220](https://github.com/leanprover/lean4/pull/12220) 使用 `IO.Process.spawn` 修复了 Windows 上的错误，其中设置
  环境变量为空字符串不会设置环境
  子进程上的变量。

* [#12234](https://github.com/leanprover/lean4/pull/12234) 引入了一个 `Iter.step_eq` 引理，它完全展开了
  `Iter.step` 调用，绕过层层展开。

* [#12249](https://github.com/leanprover/lean4/pull/12249) 添加了一些关于 `sum`、`min` 和 `max` 相互作用的引理
  关于列表中已经存在的数组。

* [#12250](https://github.com/leanprover/lean4/pull/12250) 引入了定义等式 `Triple.iff` 并将其用于
  证明而不是依赖定义等式。还介绍了
  `Triple.iff_conseq` 对于向后推理很有用并引入
  验证条件。类似地， `Triple.entails_wp_*` 定理是
  引入用于向后推理，其中目标是有状态的
  蕴涵而不是三元组。

* [#12258](https://github.com/leanprover/lean4/pull/12258) 添加了直接说明 div 和 mod 形成的定理
  单射对：如果 `a / n = b / n` 和 `a % n = b % n` 那么 `a = b`。
  这些补充了现有的 div/mod 引理并且对于扩展很有用
  论据。

* [#12277](https://github.com/leanprover/lean4/pull/12277) 添加 `IO.FS.Metadata.numLinks`，其中包含
  到文件的硬链接。

* [#12281](https://github.com/leanprover/lean4/pull/12281) 将 `Squash` 的定义更改为使用 `Quotient`
  上游
  [`true_equivalence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#true_equivalence)
  （现在 `equivalence_true`）和
  [`trueSetoid`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#trueSetoid)
  （现在是`Setoid.trivial`）。新定义相对于旧定义来说是 def-eq，但是
  确保只要有 `Quotient` 参数，就可以使用 `Squash`
  无需显式提供 setoid 即可实现预期效果。

* [#12282](https://github.com/leanprover/lean4/pull/12282) 修复了 `IO.FS.removeFile` 中的平台不一致问题
  无法删除 Windows 上的只读文件。

* [#12290](https://github.com/leanprover/lean4/pull/12290) 将 `PredTrans.apply` 结构体字段移动到一个单独的
  `def`。这样做可以提高内核规约速度，因为内核
  与结构域相比，不太可能展开定义
  预测。这会导致 `simp` 正常形式发生微小变化。

* [#12301](https://github.com/leanprover/lean4/pull/12301) 介绍了函数 `(String|Slice).posGE` 和
  `(String|Slice).posGT` 将进行全面验证并弃用
  `Slice.findNextPos` 支持 `Slice.posGT`。

* [#12305](https://github.com/leanprover/lean4/pull/12305) 添加了有关基本类型的各种无趣引理，提取
  从KMP验证。

* [#12311](https://github.com/leanprover/lean4/pull/12311) 公开链和 `is_sup` 定义，以便其他模块
  可以声明自定义 CCPO 实例。

* [#12312](https://github.com/leanprover/lean4/pull/12312) 颠倒了 `ForwardPattern` 与
  `ToForwardSearcher` 类之间的关系。

* [#12318](https://github.com/leanprover/lean4/pull/12318) 避免 `String.Slice.hash` 中未对齐时的未定义行为
  子串。
  这可能会在某些 Arm 平台上产生 SIGILL。

* [#12322](https://github.com/leanprover/lean4/pull/12322) 添加了 `String.Slice.Subslice`，它是
  `String.Slice` 的非捆绑版本。

* [#12333](https://github.com/leanprover/lean4/pull/12333) 添加将在验证中使用的基本类型类
  我们的字符串搜索基础设施。

* [#12341](https://github.com/leanprover/lean4/pull/12341) 添加了一些我们之后需要的统一提示
  `backward.isDefEq.respectTransparency` 默认为 `true`。

* [#12346](https://github.com/leanprover/lean4/pull/12346) 显示 `s t : String.Slice` 的 `s == t ↔ s.copy = t.copy` 和
将右侧建立为 simpl 范式。

* [#12349](https://github.com/leanprover/lean4/pull/12349) 建立在 #12333 之上并证明 `Char` 和 `Char -> Bool`
  模式是合法的。

* [#12352](https://github.com/leanprover/lean4/pull/12352) 使用 `drop`/`take` 操作的引理改进了切片接口
  关于 `Subarray` 以及更多关于 `Std.Slice.fold`、`Std.Slice.foldM` 的引理
  和`Std.Slice.forIn`。它还更改了 `simp` 和 `grind`
  `Slice` 相关引理的注释。切片之间转换的引理
  不同形状的不再被 `simp`/`grind`-注释，因为它们
  通常引理很复杂并且阻碍了自动化。

* [#12358](https://github.com/leanprover/lean4/pull/12358) 改进了 `simp` 和 `grind` 规则框架
  `PredTrans.apply` 并根据以下内容重命名相应的引理
  公约。

* [#12359](https://github.com/leanprover/lean4/pull/12359) 弃用 `extract_eq_drop_take` 以支持更正确的方法
  name `extract_eq_take_drop`，这样我们就可以使用旧名称
  对于引理 `xs.extract start stop = (xs.take stop).drop start`。直到
  弃用截止日期已过，这个新引理将被称为
  `extract_eq_drop_take'`.

* [#12360](https://github.com/leanprover/lean4/pull/12360) 为字符串提供 `LawfulForwardPatternModel` 实例
  模式，即它证明 `dropPrefix?` 的正确性和
用于字符串模式的 `startsWith` 函数。

* [#12363](https://github.com/leanprover/lean4/pull/12363) 通过 `Vector.iter` 引入向量的迭代器
  `Vector.iterM`，以及通常的引理。

* [#12371](https://github.com/leanprover/lean4/pull/12371) 添加引理以简化涉及 `Bool` 和
  `ite`/`dite`.

* [#12412](https://github.com/leanprover/lean4/pull/12412) 引入 `Rat.abs` 并添加关于 `Int` 的缺失引理和
  `Rat`.

* [#12419](https://github.com/leanprover/lean4/pull/12419) 为 `Nat`、`Int` 和所有添加 `LawfulOrderOrd` 实例
  固定宽度整数类型（`Int8`、`Int16`、`Int32`、`Int64`、`ISize`、
  `UInt8`、`UInt16`、`UInt32`、`UInt64`、`USize`）。这些实例
  确定这些类型的 `Ord` 实例与
  他们的 `LE` 实例。此外，此 PR 添加了一些缺失的引理
  和 `grind` 模式。

* [#12424](https://github.com/leanprover/lean4/pull/12424) 给出 `Slice` 的 `LawfulToForwardSearcherModel` 的证明
  模式，这相当于证明我们的 KMP 实施是
  正确。

* [#12426](https://github.com/leanprover/lean4/pull/12426) 添加了引理 `Acc.inv_of_transGen`，它是
  `Acc.inv`。`Acc.inv` 表明给定 `r y x` 时，`Acc r x` 蕴含 `Acc r y`；新引理表明，如果 `y` 仅是，则这也成立
  *传递*与 `x` 相关。

* [#12432](https://github.com/leanprover/lean4/pull/12432) 将引理 `isSome_find?` 和 `isSome_findSome?` 添加到接口
  列表、数组和向量。

* [#12437](https://github.com/leanprover/lean4/pull/12437) 通过关联来验证 `String.Slice.splitToSubslice` 函数
  它基于一个模型实现 `Model.split`
  `ForwardPatternModel`.

* [#12438](https://github.com/leanprover/lean4/pull/12438) 提供 (1) 引理，表明从范围获得的列表具有
  切片上没有重复项和 (2) 关于 `forIn` 和 `foldl` 的引理。

* [#12441](https://github.com/leanprover/lean4/pull/12441) 删除 `Subarray.foldl(M)`、`Subarray.toArray` 和
  `Subarray.size` 支持 `Std.Slice` 命名空间操作。点
  符号将继续起作用。比如说，如果 `Subarray.size` 是明确的
  参考，会出现一条错误建议使用 `Std.Slice.size` 。

* [#12442](https://github.com/leanprover/lean4/pull/12442) 派生 `DecidableEq` 范围类型的实例，例如
  `a...b`（在本例中为 `Std.Rco`）。

* [#12445](https://github.com/leanprover/lean4/pull/12445) 提供表征 `Nat.toDigits`、`Nat.repr` 和
  `ToString Nat`.

* [#12449](https://github.com/leanprover/lean4/pull/12449) 将 `String.toString_eq_singleton` 标记为 `simp` 引理。

* [#12450](https://github.com/leanprover/lean4/pull/12450) 将 `String.Slice`/`String` 迭代器移出到自己的迭代器中
  文件，准备审核。

* [#12452](https://github.com/leanprover/lean4/pull/12452) 上游 `List.scanl`、`List.scanr` 及其引理
  电池放入标准库。

* [#12456](https://github.com/leanprover/lean4/pull/12456) 验证除字节之外的所有 `String` 迭代器
  迭代器，将它们与 `String.toList` 相关联。

* [#12504](https://github.com/leanprover/lean4/pull/12504) 产生 `Rat.abs_*` 引理 (`abs_zero`, `abs_nonneg`,
  `abs_of_nonneg`, `abs_of_nonpos`, `abs_neg`, `abs_sub_comm`,
  `abs_eq_zero_iff`、`abs_pos_iff`) 受保护，因此它们不会遮蔽
  当 `Rat` 命名空间在下游打开时，通用 `abs_*` 引理
  项目。

* [#12521](https://github.com/leanprover/lean4/pull/12521) 显示 `HashSet.ofList l ~m l.foldl (init := ∅) fun acc a =>
  acc.insert a`（“只是”定义）。

* [#12531](https://github.com/leanprover/lean4/pull/12531) 将一些关于哈希映射的引理捆绑到等价中以便更容易
  重写。

* [#12582](https://github.com/leanprover/lean4/pull/12582) 对 `Name.quickCmp` 使用 `ptrEq` 快速路径。它特别是
  有效加速
  `quickCmp` 调用由 `FVarId` 索引的 `TreeMap`，通常是这样
  每个 `FVarId` 只有一个指针
  因此，始终会立即检测到相等性，而无需遍历链接
  `Name` 组件列表。

* [#12583](https://github.com/leanprover/lean4/pull/12583) 内联 `Name` 的计算哈希字段的访问器。这个
  确保访问
值基本上总是只是一次加载，而不是执行完整的加载
  函数调用。

* [#12596](https://github.com/leanprover/lean4/pull/12596) 在字符串上为 `ForIn` 添加了 `Std.Do` 规范引理。

* [#12641](https://github.com/leanprover/lean4/pull/12641) 导出字符串位置上的线性顺序 (`String.Pos.Raw`,
  `String.Pos`、`String.Slice.Pos`) 通过 `Std.LinearOrderPackage`，其中
  确保所有数据承载和命题实例都存在。

* [#12642](https://github.com/leanprover/lean4/pull/12642) 添加了 dsimprocs 以减少 `String.toList` 和 `String.push`。

* [#12651](https://github.com/leanprover/lean4/pull/12651) 添加了一些关于 `min`、`minOn`、`List.min` 的缺失引理，
  `List.minOn`.

* [#12757](https://github.com/leanprover/lean4/pull/12757) 将 `Id.run` 标记为 `[implicit_reducible]` 以确保
  `Id.instMonadLiftTOfPure` 和 `instMonadLiftT Id` 定义为
  使用 `.implicitReducible` 透明度设置时相等。

* [#12821](https://github.com/leanprover/lean4/pull/12821) 删除 `@[grind →]` 属性
  `List.getElem_of_getElem?` 和 `Vector.getElem_of_getElem?`。这些是
  在 Mathlib 中被识别为有问题的
  https://github.com/leanprover/lean4/issues/12805.

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Tactics"
%%%

* [#11744](https://github.com/leanprover/lean4/pull/11744) 修复了 `lia` 错误地解决涉及的目标的错误
  它不应该处理像 `Rat` 这样的有序类型。 `lia` 策略是
  仅用于线性整数算术。

* [#12152](https://github.com/leanprover/lean4/pull/12152) 添加了 `simpArrowTelescope`，一个简化望远镜的简化过程
非相关箭头 (p₁ → p2 → ... → q)，同时避免二次
  证明增长。

* [#12153](https://github.com/leanprover/lean4/pull/12153) 改进了 `simpArrowTelescope` 简化过程，简化了
  非相关箭头望远镜：`p₁ → p₂ → ... → q`。

* [#12154](https://github.com/leanprover/lean4/pull/12154) 添加了 `simpTelescope`，一个简化望远镜的简化过程
  粘合剂（`have`-表达式值和箭头假设），但不是
  最终的身体。这对于在引入之前简化目标很有用
  假设。

* [#12168](https://github.com/leanprover/lean4/pull/12168) 在 `SymM` 中添加了对 η 缩减的支持。

* [#12172](https://github.com/leanprover/lean4/pull/12172) 修复了我们如何确定函数参数是否为
  实例。
  以前，我们依赖绑定器注解（例如 `[Ring A]` 与 `{_ : Ring A}`）
  做出这个决定。这并不可靠，因为用户
  合法使用
  当实例已经可用时，类类型的 `{..}` 绑定器
  来自
  上下文。例如：
  ```
  structure OrdSet (α : Type) [Hashable α] [BEq α] where
    ...

  def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α :=
    ...
  ```

这里， `Hashable` 和 `BEq` 是类，但 `{..}` 绑定器是故意的，
  实例来自 `OrdSet` 的参数，因此类型类解析是不必要的。

  该修复使用 `isClass?` 而不是其语法来检查参数的*类型*，并且
  将此信息缓存在 `FunInfo` 中。这会影响多个子系统：
  判别树、同余引理生成和 `grind` 规范化器。

* [#12176](https://github.com/leanprover/lean4/pull/12176) 修复了延迟 E 匹配定理实例可能导致的错误
  实例跟踪映射中的 uniqueId 冲突。

* [#12195](https://github.com/leanprover/lean4/pull/12195) 确保 `dsimp` 默认情况下不会“简化”实例。的
  可以通过使用来检索旧行为
  ```
  set_option backward.dsimp.instances true
  ```
  将 `dsimp` 应用于实例会创建非标准实例，这
  在 Mathlib 中产生各种各样的问题。
  这个修改类似于
  ```
  set_option backward.dsimp.proofs true
  ```

* [#12205](https://github.com/leanprover/lean4/pull/12205) 添加 `mkBackwardRuleFromExpr` 以创建向后规则
  表达式，补充现有的 `mkBackwardRuleFromDecl` 其中
  仅适用于声明名称。

* [#12224](https://github.com/leanprover/lean4/pull/12224) 修复了 `grind?` 建议不包括的错误
  使用局部变量点表示法的参数（例如，
  `cs.getD_rightInvSeq` 其中 `cs` 是局部变量）。这些参数
被错误地过滤掉，因为代码假定了所有 ident 参数
  决心全球声明。事实上，局部变量点表示法
  生成需要在重播期间加载原始术语的锚点，
  因此它们必须保留在建议中。

* [#12226](https://github.com/leanprover/lean4/pull/12226) 修复了当定理 `foo` 有时 `grind [foo]` 失败的错误
  与目标不同的宇宙变量名称，即使宇宙
  多态性应该允许宇宙统一。

* [#12244](https://github.com/leanprover/lean4/pull/12244) 确保 `simp` 默认情况下不会“简化”实例。旧的
  可以使用 `simp +instances` 检索行为。是相似的
  到#12195，但对于`dsimp`。
  `dsimp` 的向后兼容性标志也会停用此新功能
  功能。

* [#12259](https://github.com/leanprover/lean4/pull/12259) 确保我们将 `unfold_definition` 定义的结果缓存在
  内核类型检查器。我们曾经将这些信息缓存在线程中
  本地存储，但在Lean 3 到Lean 4 期间被删除
  过渡。

* [#12260](https://github.com/leanprover/lean4/pull/12260) 修复了 `Sym` 中函数 `instantiateRangeS'` 中的错误
  框架。

* [#12279](https://github.com/leanprover/lean4/pull/12279) 添加了一个实验性 `cbv` 策略，可以从
  `conv` 模式。该策略不适合生产使用，并且
  显示适当的警告。

* [#12280](https://github.com/leanprover/lean4/pull/12280) 添加了基于 Xavier Leroy 编译器验证的基准
  测试按值调用策略的课程。

* [#12287](https://github.com/leanprover/lean4/pull/12287) 修复了 `attribute [local simp]` 不正确的问题
  私人导入的定理被拒绝

* [#12296](https://github.com/leanprover/lean4/pull/12296) 添加了 `cbv_eval` 属性，允许计算以下函数
  使用预先注册的定理的 `cbv` 策略。

* [#12319](https://github.com/leanprover/lean4/pull/12319) 利用 `grind` 中表达式类型正确的事实
  外延定理的结论的形式为`?a = ?b`。

* [#12345](https://github.com/leanprover/lean4/pull/12345) 添加了两个基准（埃拉托色尼筛选、删除重复项
  从列表中）和一个测试（具有次线性复杂度的函数
  通过对大自然数进行评估的有充分依据的递归来定义
  到 `60` 数字）。

* [#12361](https://github.com/leanprover/lean4/pull/12361) 开发自定义简化过程来处理 `ite`/`dite`
  `cbv` 策略中的表达式，基于等效的简化过程
  `Sym.simp`，区别在于如果条件没有简化为
`True`/`False`，我们利用可判定实例并计算
  条件减少到什么程度。

* [#12370](https://github.com/leanprover/lean4/pull/12370) 修复了 `Sym.simp` 中的证明构造错误。

* [#12399](https://github.com/leanprover/lean4/pull/12399) 添加了一个自定义简化过程来处理 `Decidable.rec`，我们强制
  重写 `Decidable` 类型的参数，通常是
  由于是子单例而没有重写。

* [#12406](https://github.com/leanprover/lean4/pull/12406) 对 `bv_decide` 中的 LRAT 检查进行了两项更改：
  1. LRAT 修剪器以前用于删除删除指令，因为我们
  没有以有意义的方式对它们采取行动（如2中所述）。现在它
  找出最早可以删除条款的时间点
  修剪后的 LRAT 证明并在那里插入删除内容。
  2. LRAT 检查器接收 `Array IntAction` 并将其分解为
  在将其传递到检查循环之前先添加 `Array DefaultClauseAction` 。
  与相比，`DefaultClauseAction` 的内存占用要大得多
  `IntAction`。因此，预先将整个证明具体化为
  `DefaultClauseAction` 前期会消耗大量内存。在改编的
  LRAT 检查器我们接受 `Array IntAction` 并且只转换
  我们目前正在努力实现 `DefaultClauseAction`。在
结合我们现在插入删除指令的事实
  可以大大减少内存消耗。

* [#12408](https://github.com/leanprover/lean4/pull/12408) 添加了一个面向用户的 `cbv` 策略，可以在
  `conv` 模式。

* [#12411](https://github.com/leanprover/lean4/pull/12411) 添加了终结 `decide_cbv` 策略，适用
  `of_decide_eq_true` 然后尝试使用以下方法实现剩余目标
  `cbv`.

* [#12415](https://github.com/leanprover/lean4/pull/12415) 改进了对 `grind` 模式中 η 扩展项的支持。

* [#12417](https://github.com/leanprover/lean4/pull/12417) 重构了 `cbv` 策略的主循环。而不是使用
  多个简化过程，引入了中央预简化过程。此外，让
  由于性能原因，表达式不再立即 ζ 缩减
  基准之一 (`leroy.lean`)。

* [#12423](https://github.com/leanprover/lean4/pull/12423) 添加属性 `@[univ_out_params]` 用于指定哪个
  宇宙级别应被视为输出参数。默认情况下，任何
  考虑任何输入参数中未出现的宇宙级别
  一个输出参数。

* [#12467](https://github.com/leanprover/lean4/pull/12467) 为 `cbv` 策略添加了评估基准
  `Decidable.decide` 用于检查问题的 `Decidable` 实例
  如果一个数不是素数幂。

* [#12473](https://github.com/leanprover/lean4/pull/12473) 修复了 #12246 报告的 `grind` 中的断言冲突
  在包含异质等式的示例中，断言失败
  附加到不同类型的元素（例如 `Fin n` 和 `Fin m`）
  相同的理论求解器。

* [#12474](https://github.com/leanprover/lean4/pull/12474) 修复了 `grind` 中 `sreifyCore?` 可能遇到的恐慌
  嵌套期间尚未在 E 图中内化的幂子项
  传播。环形强化器（`reifyCore?`）已经具有防御能力
  `alreadyInternalized` 在创建变量之前检查，但半环
  reifier (`sreifyCore?`) 缺少这个守卫。当`propagatePower`时
  将 `a ^ (b₁ + b₂)` 分解为 `a^b₁ * a^b₂` 以及所得项
  触发进一步传播，可以调用半环放大器
  子项尚未出现在 E 图中，导致 `markTerm` 失败。

* [#12475](https://github.com/leanprover/lean4/pull/12475) 修复了假设包含元变量时 `grind` 失败的问题
  （例如，在 `refine` 之后）。根本原因是 `abstractMVars` 在
  `withProtectedMCtx` 仅抽象目标中的元变量，而不是
  假设，在grind的电子图中造成了脱节。

* [#12476](https://github.com/leanprover/lean4/pull/12476) 修复了 #12245，其中 `grind` 在 `Fin n` 上工作，但在 `Fin (n
  + 1)`.

* [#12477](https://github.com/leanprover/lean4/pull/12477) 修复了调用 `mkEqProof` 的内部 `grind` 错误
具有不同类型的术语。当等价类包含
  异构平等（例如， `0 : Fin 3` 和 `0 : Fin 2` 通过合并
  `HEq`), `closeGoalWithValuesEq` 会根据以下条件调用 `mkEqProof`
  不兼容的类型，触发内部错误。

* [#12480](https://github.com/leanprover/lean4/pull/12480) 在 AIG 到 CNF 转换期间跳过重新标记步骤，减少
  内存压力。

* [#12483](https://github.com/leanprover/lean4/pull/12483) 在 `grind` 中添加了对高阶米勒模式的支持
  电子匹配引擎。

* [#12486](https://github.com/leanprover/lean4/pull/12486) 将 `isDefEqI` 结果缓存在 `Sym` 中。符号计算期间
  （例如，VC 生成器），我们一遍又一遍地找到相同的实例。

* [#12500](https://github.com/leanprover/lean4/pull/12500) 改进了 `decide_cbv` 策略产生的错误消息
  通过仅减少引入的等式的左侧
  `of_decide_eq_true`，而不是尝试通过
  `cbvGoal`.

* [#12506](https://github.com/leanprover/lean4/pull/12506) 添加了使用 `cbv_eval` 注册定理的功能
  使用 `←` 修饰符反向设置属性，镜像
  现有的 `simp` 属性行为。当使用 `@[cbv_eval ←]` 时，
  方程 `lhs = rhs` 反转为 `rhs = lhs`，允许 `cbv`
  将出现的 `rhs` 重写为 `lhs`。

* [#12562](https://github.com/leanprover/lean4/pull/12562) 修复了 `cbv` 策略抛出“意外内核”的#12554
  结构定义相等期间的投影项”重写时
  定理的模式包含一个 λ 并且匹配的表达式有
  相应位置处的 `.proj` （内核投影）。

* [#12568](https://github.com/leanprover/lean4/pull/12568) 从中删除 `tryMatchEquations` 和 `tryMatcher`
  `Lean.Meta.Tactic.Cbv.Main`，因为两者都已在中定义和使用
  `Lean.Meta.Tactic.Cbv.ControlFlow`。`Main.lean` 中的副本是
  无法访问的死代码。

* [#12585](https://github.com/leanprover/lean4/pull/12585) 删除 `ite` 和 `dite` 中不必要的 `trySynthInstance `
  `cbv` 使用的简化过程之前导致了太多
  该策略不必要地展开。

* [#12588](https://github.com/leanprover/lean4/pull/12588) 为 `cbv` 策略添加了一个基准，其中涉及评估
  `List.mergeSort` 在自然数的反转列表上。

* [#12601](https://github.com/leanprover/lean4/pull/12601) 在策略模式下使用 `cbv` 或 `decide_cbv` 时添加警告，
  与转换模式下的现有警告相匹配
  （`src/Lean/Elab/Tactic/Conv/Cbv.lean`）。该警告告知用户
  这些策略是实验性的，仍在开发中。它可以是
  使用 `set_option cbv.warning false` 禁用。

* [#12612](https://github.com/leanprover/lean4/pull/12612) 修复了 `cbv` 策略的 `handleProj` 简化过程中的崩溃问题
  处理依赖投影（例如 `Sigma.snd`），其结构为
  通过 `@[cbv_eval]` 重写为非定义相等的术语
  无法进一步减少。

* [#12615](https://github.com/leanprover/lean4/pull/12615) 修复了 `handleConst` 中阻止 `cbv` 的翻转条件
  从展开无效（非函数）常量定义，例如
  `def myVal : Nat := 42`。检查 `unless eType matches .forallE` 的本意是
  旨在跳过裸函数常量（其展开定理期望
  参数），而是跳过值常量。该修复更改了
  防护到 `if eType matches .forallE`，匹配中使用的逻辑
  标准 `simp` 地面评估器。

* [#12622](https://github.com/leanprover/lean4/pull/12622) 修复了 `simp` 在类投影上没有取得进展的错误
  当 `backward.whnf.reducibleClassField` 为 `true` 时减少。

* [#12627](https://github.com/leanprover/lean4/pull/12627) 恢复 #12615，这意外地破坏了 Leroy 的编译器
  验证课程基准。

* [#12646](https://github.com/leanprover/lean4/pull/12646) 使 `cbv` 策略能够展开无效（非功能）
  常数
  诸如 `def myNat : Nat := 42` 之类的定义，允许地面术语
评价
  （例如 `evalEq`、`evalLT`）将它们的值识别为文字。

* [#12782](https://github.com/leanprover/lean4/pull/12782) 为 `OfSemiring.Q` 的实例添加高优先级
  环形信封。当Mathlib导入时，类型的实例合成
  像 `OfSemiring.Q Nat` 变得非常昂贵，因为求解器
  在找到正确的实例之前探索许多不相关的路径。由
  将这些实例标记为高优先级并添加快捷方式实例
  用于基本操作（`Add`、`Sub`、`Mul`、`Neg`、`OfNat`、`NatCast`、
  `IntCast`, `HPow`)，实例合成快速解析。

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Compiler"
%%%

* [#12044](https://github.com/leanprover/lean4/pull/12044) 实现封闭项的延迟初始化。以前的工作
  已经确保约 70% 的封闭术语出现在核心中
  可以从二进制文件静态初始化。这样剩下的
  它们是延迟初始化的，而不是在启动时初始化的。

* [#12052](https://github.com/leanprover/lean4/pull/12052) 避免了Lean程序关闭时潜在的死锁
  池线程数已暂时推至高于
  限制。

* [#12060](https://github.com/leanprover/lean4/pull/12060) 从 Linux 上的 libleanshared.so 中删除不需要的符号名称。它
  似乎在其他平台上我们感兴趣的符号名称
这里已经被链接器删除了。

* [#12082](https://github.com/leanprover/lean4/pull/12082) 使编译器生成静态初始化的 C 代码
  尽可能接近条款。此更改减少了启动时间，因为条款
  直接存储在二进制文件中，而不是在
  启动。

* [#12117](https://github.com/leanprover/lean4/pull/12117) 升级 Lean 的内部工具链以使用 C++20 作为准备
  步骤#12044。

* [#12214](https://github.com/leanprover/lean4/pull/12214) 向 LCNF 中间表示引入相分离。这是一个
  为合并做准备
  旧的 `Lean.Compiler.IR` 和新的 `Lean.Compiler.LCNF` 框架。

* [#12239](https://github.com/leanprover/lean4/pull/12239) 恢复#8308 中所做的许多更改。我们实际上
  遇到过这样的情况：
  ```
  fun y (z) :=
    let x := inst
    mkInst x z
  f y
  ```
  实例拉取器将其变成：
  ```
  let x := inst
  fun y (z) :=
    mkInst x z
  f y
  ```
  当前的启发式现在发现 `x` 在调用站点的范围内
  `f` 并在 `y` 中的活页夹下使用，从而阻止拉入
  `x` 到专业化，对实例进行抽象。

* [#12272](https://github.com/leanprover/lean4/pull/12272) 将 LCNF mono 到 λ pure 的转换转移到
  LCNF 不纯相。这是为即将进行的重构做的准备工作
中间表示转化为不纯的LCNF。

* [#12284](https://github.com/leanprover/lean4/pull/12284) 更改了对过度应用案例表达式的处理
  `ToLCNF` 以避免生成被调用的函数声明
  立即。例如，`ToLCNF` 之前生成了这个：
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 4
      def test x y : Bool :=
        fun _y.1 _y.2 : Bool :=
          cases x : Bool
          | PUnit.unit =>
            fun _f.3 a : Bool :=
              return a;
            let _x.4 := _f.3 _y.2;
            return _x.4;
        let _x.5 := _y.1 y;
        return _x.5
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  现在简化为
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 3
      def test x y : Bool :=
        cases x : Bool
        | PUnit.unit =>
          let a := y;
          return a
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  这与 #8309 尤其相关，因为 `dite` 定义为
  过度应用 `Bool.casesOn`。

* [#12294](https://github.com/leanprover/lean4/pull/12294) 将 `push_proj` 通道从中间表示移植到 LCNF。值得注意的是它不能
  将其从中间表示中删除，因为稍后仍会使用该通行证。

* [#12315](https://github.com/leanprover/lean4/pull/12315) 将中间表示 ResetReuse 传递迁移到 LCNF。

* [#12344](https://github.com/leanprover/lean4/pull/12344) 更改编译器中 `inline` 注释的语义。
  原始 `@[inline]` 属性的行为保持不变，但是
  函数 `inline` 现在有一个限制，它只能使用
  当前模块的本地声明。这是作为
  准备将编译器拉出到一个单独的进程中。

* [#12356](https://github.com/leanprover/lean4/pull/12356) 将中间表示 `elim_dead_vars` 通道移至 LCNF。它无法删除
  尚未通过，因为仍在使用
  在后来的中间表示通行证中。

* [#12384](https://github.com/leanprover/lean4/pull/12384) 将中间表示 SimpCase 传递移植到 LCNF。

* [#12387](https://github.com/leanprover/lean4/pull/12387) 修复了 LCNF simp 中尝试采取行动的问题
  输入错误 `cases`
  语句并寻找分支，否则会出现恐慌。这个问题没有
  但在生产中表现为
  LCNF simp 所支持的各种其他不变量有助于掩盖它，但会开始
  成为一个问题
  即将发生的变化。

* [#12413](https://github.com/leanprover/lean4/pull/12413) 将中间表示借用通行证移植到 LCNF。

* [#12434](https://github.com/leanprover/lean4/pull/12434) 删除了引入的 `shared_timed_mutex` 的使用
  因为我们被困在 C++14 上
  与 C++17 及更高版本中提供的 `shared_mutex` 一起使用。

* [#12446](https://github.com/leanprover/lean4/pull/12446) 添加了 `Task.get (Task.pure x) = x` 的简化规则
  LCNF 简化器。这个
  确保我们避免立即触及 `Task` 的运行时
  无论如何都会被破坏。

* [#12458](https://github.com/leanprover/lean4/pull/12458) 将用于装箱/拆箱插入的中间表示通道移植到 LCNF。

* [#12465](https://github.com/leanprover/lean4/pull/12465) 将 `uint64` 的装箱类型从 `tobject` 更改为 `object`
允许更精确的引用计数。

* [#12466](https://github.com/leanprover/lean4/pull/12466) 通过返回正确处理句柄上的零大小读取
  系统调用之前的空数组
  甚至尝试过。

* [#12472](https://github.com/leanprover/lean4/pull/12472) 内联 `mix_hash` 来自 C++，它提供了一般加速
  哈希函数。

* [#12548](https://github.com/leanprover/lean4/pull/12548) 将 RC 插入从中间表示移植到 LCNF。

* [#12580](https://github.com/leanprover/lean4/pull/12580) 使 `computed_field` 尊重
  计算函数
  场。这意味着我们可以内联字段的访问器，从而允许
  更快的访问。

* [#12604](https://github.com/leanprover/lean4/pull/12604)使RC插入中的导出值分析识别
  `Array.uget` 作为另一种
  “类投影”操作。这使得它可以减少引用计数
  访问元素的压力
  通过uget。

* [#12625](https://github.com/leanprover/lean4/pull/12625) 确保初始编译失败标记相关
  定义标记为 `noncomputable`，无论位于 `noncomputable
  section` 内部还是外部，以便检测后续错误或不可计算标记
  在初始编译中，而不是在管道的某个地方。

* [#12644](https://github.com/leanprover/lean4/pull/12644) 将拓扑排序过程从中间表示移植到 LCNF。

* [#12759](https://github.com/leanprover/lean4/pull/12759) 将 `isImplicitReducible` 检查替换为 `Meta.isInstance`
  在 `inlineCandidate?` 内的 `shouldInline` 函数中。

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Pretty-Printing"
%%%

* [#12688](https://github.com/leanprover/lean4/pull/12688) 添加 `pp.fvars.anonymous` 选项（默认 `true`）
  控制松散自由变量的显示（fvars 不在本地
  上下文）。当 `false` 时，它们显示为 `_fvar._` 而不是其内部
  名字。这对于稳定 `#guard_msgs` 中的输出很有用。
  [#12745](https://github.com/leanprover/lean4/pull/12745) 修复
  该选项设置为 `false` 时的行为。

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Documentation"
%%%

* [#12157](https://github.com/leanprover/lean4/pull/12157) 更新了#12137，并提供了Lean参考手册的链接。

* [#12174](https://github.com/leanprover/lean4/pull/12174) 修复了 `ExtractLetsConfig.merge` 文档注释中的拼写错误。

* [#12253](https://github.com/leanprover/lean4/pull/12253) 在 `#guard_msgs` 中添加了“稳定输出”部分
  文档字符串，解释如何使用 `pp.mvars.anonymous` 和 `pp.mvars`
  用于稳定包含自动生成的元变量名称的输出的选项
  像`?m.47`。

* [#12271](https://github.com/leanprover/lean4/pull/12271) 添加和更新语法文档字符串（以及范围文档字符串）。

* [#12439](https://github.com/leanprover/lean4/pull/12439) 改进了 `cbv` 和 `decide_cbv` 策略的文档字符串

* [#12487](https://github.com/leanprover/lean4/pull/12487) 扩展了 `@[univ_out_params]` 的文档字符串来解释：

  - 宇宙输出参数如何影响类型类解析缓存
  （它们从缓存键中删除，因此查询仅在输出上有所不同
  宇宙共享条目）
  - 何时应将宇宙参数视为输出（确定
  通过输入）与不（所提出问题的一部分）

* [#12616](https://github.com/leanprover/lean4/pull/12616) 将文档添加到下面的 Cbv 评估器文件中
  `Meta/Tactic/Cbv/`。模块文档字符串描述了求值策略，
  限制、属性和展开顺序。函数文档字符串覆盖
  公共接口和关键的内部简化过程。

* [#13115](https://github.com/leanprover/lean4/pull/13115) 更新 `inferInstanceAs` 文档字符串以反映当前
  行为：它需要一个
  上下文中的预期类型，不应用作简单的
  `inferInstance` 同义词。的
  旧示例（`#check inferInstanceAs (Inhabited Nat)`）不再有效，
  所以它被替换了
  其中一个演示了预期的运输用例。

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Server"
%%%

* [#12197](https://github.com/leanprover/lean4/pull/12197) 修复了 `System.Uri.fileUriToPath?` 中无法使用的错误
  它生成的路径中的默认 Windows 路径分隔符。

* [#12332](https://github.com/leanprover/lean4/pull/12332) 修复了新 NeoVim 版本上的一个问题，该问题会导致
  语言服务器在使用某些代码操作时显示错误。

* [#12553](https://github.com/leanprover/lean4/pull/12553) 修复了不支持增量的命令的问题
  当进行相关编辑时，他们的精译没有被打断
  由用户。由于 def/theorem 的所有内置变体都有一个共同点
  增量精译器，这可能对标准的影响可以忽略不计
  精简文件，但可能会影响严重依赖自定义的其他用例
  命令，例如 Verso。

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Lake"
%%%

* [#12113](https://github.com/leanprover/lean4/pull/12113) 更改存储在中的输出的文件格式
  本地 Lake 缓存包含指示服务的标识符（如果
  任何）输出来自。这将用于延迟启用
  在构建期间按需下载工件。

* [#12178](https://github.com/leanprover/lean4/pull/12178) 将 `FamilyOut.fam_eq` 上的 `simp` 属性范围限定为 `Lake`
  命名空间。引理有一个非常宽松的判别树键
  (`_`)，因此当 `Lake.Util.Family` 被传递导入到
  下游项目，它会导致 `simp` 在每个项目上尝试这个引理
进球，导致暂停。

* [#12203](https://github.com/leanprover/lean4/pull/12203) 改变了从当地湖泊转移文物的方式
  缓存到本地构建路径。现在，Lake 将首先尝试硬链接
  缓存中工件的本地构建路径。如果失败（例如，
  因为缓存位于不同的文件系统或驱动器上），它将
  回退到复制工件的现有方法。现在湖也
  将缓存工件标记为只读，以避免通过以下方式损坏缓存
  写入硬链接工件。

* [#12261](https://github.com/leanprover/lean4/pull/12261) 修复了 Lake 中以未知方式打印方面名称的错误
  构面错误将包含内部构面类型。

* [#12300](https://github.com/leanprover/lean4/pull/12300) 禁用工件缓存（例如，通过
  `LAKE_ARTIFACT_CACHE=false` 或 `enableArtifactCache = false`) 现在停止
  Lake 不再从缓存中获取数据（而之前它只是停止了
  写信给它）。

* [#12377](https://github.com/leanprover/lean4/pull/12377) 添加有关可用于 `lean` 的模块的标识信息
  （例如，其名称和包标识符）到模块的依赖关系
  踪迹。这保证了不同标识的模块有不同的
  输入哈希，即使它们的源文件和导入相同。

* [#12444](https://github.com/leanprover/lean4/pull/12444) 添加 Lake 命令行界面命令 `lake cache clean`，该命令删除
  湖缓存目录。

* [#12461](https://github.com/leanprover/lean4/pull/12461) 添加了对构建时手动重新发布 nightly 的支持
  问题或关键修复需要它。当 `workflow_dispatch` 触发时
  每晚发布作业和 `nightly-YYYY-MM-DD` 标签已经存在，
  CI 现在创建 `nightly-YYYY-MM-DD-rev1` （然后创建 `-rev2` 等）
  而不是默默地跳过。

* [#12490](https://github.com/leanprover/lean4/pull/12490) 添加系统范围的 Lake 配置文件并使用它
  配置 `lake cache` 使用的远程缓存服务。

* [#12532](https://github.com/leanprover/lean4/pull/12532) 修复了 `cache clean` 的一个错误，如果缓存
  目录不存在。

* [#12537](https://github.com/leanprover/lean4/pull/12537) 修复了 Lake 重新缓存的工件已存在于其中的错误
  缓存。因此，Lake 会尝试覆盖只读的
  工件，导致权限被拒绝错误。

* [#12835](https://github.com/leanprover/lean4/pull/12835) 将 Lake 更改为仅发出 `.nobuild` 痕迹（在
  #12076) 如果正常跟踪文件已经存在。这解决了一个问题
  其中 `lake build --no-build` 将创建构建目录并
  从而防止在未来的构建中进行云发布获取。

* [#13141](https://github.com/leanprover/lean4/pull/13141) 将 Lake 更改为在更新依赖项时运行 `git clean -xf`
  存储库，确保旧的未跟踪文件（例如 `.hash` 文件）
  源树已被删除。陈旧的 `.hash` 文件可能会导致错误的跟踪
  计算和中断构建。

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___29___0-_LPAR_2026-03-27_RPAR_--Other"
%%%

* [#12351](https://github.com/leanprover/lean4/pull/12351) 扩展了 `@[csimp]` 属性以正确跟踪
  `lake shake`

* [#12375](https://github.com/leanprover/lean4/pull/12375) 通过跟踪传递给的属性名称来扩展 shake
  `simp`/`grind`.

* [#12463](https://github.com/leanprover/lean4/pull/12463) 修复了修订版第一次测试中发现的两个问题
  每晚发布工作流程
  (https://github.com/leanprover/lean4/pull/12461):

  *1.日期逻辑：* 使用的 `workflow_dispatch` 路径 `date -u +%F`
  （当前 UTC 日期）每晚查找基准进行修改。如果最
  最近每晚是从昨天开始的（例如 `nightly-2026-02-12`），但 UTC
  已转至 2 月 13 日，代码将查找 `nightly-2026-02-13`，
  找不到它，并创建一个新的每晚而不是修订版。现在发现
  通过 `sort -rV` 最新的 `nightly-*` 标签并创建
  那个。

* [#12517](https://github.com/leanprover/lean4/pull/12517) 添加了用于以人类可读方式分析Lean程序的工具
  Firefox Profiler 中的函数名称：

  - *`script/lean_profile.sh`* — 单命令管道：记录
在 Firefox Profiler 中采样、符号化、分解和打开
  - *`script/profiler/lean_demangle.py`* — 忠实端口
  `Name.demangleAux` 来自 `NameMangling.lean`，带有一个后处理器
  将编译器后缀折叠成紧凑的注解（`[λ, arity↓]`、`spec at context[flags]`）
  - *`script/profiler/symbolicate_profile.py`* — 解析原始地址
  通过 samply 的符号接口
  - *`script/profiler/serve_profile.py`* — 将分解的配置文件提供给
  无需重新符号化的 Firefox Profiler
  - *`PROFILER_README.md`* — 文档，包括阅读指南
  分解的名字

* [#12533](https://github.com/leanprover/lean4/pull/12533) 在运行时添加了人性化的Lean符号名称整理
  回溯。当Lean程序出现恐慌时，堆栈跟踪现在显示可读
  名称而不是损坏的 C 标识符。
