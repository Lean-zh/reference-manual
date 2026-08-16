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

#doc (Manual) "精益4.28.0 (2026-02-17)" =>
%%%
tag := "release-v4.28.0"
file := "v4.28.0"
%%%

此版本有 309 项更改。除了下面列出的 94 项功能添加和 65 项修复之外，还有 19 项重构更改、8 项文档改进、34 项性能改进、12 项测试套件改进和 77 项其他更改。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights"
%%%

Lean v4.28 版本包含模块系统修复、性能
改进，特别是在 `bv_decide` 中，并持续扩展
标准库中的 `grind` 注释。主要新功能
下面介绍。

## 符号仿真框架
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Symbolic-Simulation-Framework"
%%%

新的轻量级符号模拟框架与 `grind` 集成
并启用验证条件生成器的实现
和符号执行引擎。
[#12143](https://github.com/leanprover/lean4/pull/12143) 定义
该框架的核心API。

有关设计说明和实现细节，请参阅：

- [#11788](https://github.com/leanprover/lean4/pull/11788) — 介绍和
  概述
- [#11825](https://github.com/leanprover/lean4/pull/11825) — 高效
  模式匹配和统一
- [#11837](https://github.com/leanprover/lean4/pull/11837) — 目标
  通过向后链接进行转换
- [#11860](https://github.com/leanprover/lean4/pull/11860) —
高效子项重写的同余分析
- [#11884](https://github.com/leanprover/lean4/pull/11884) —
  用于快速模式检索的判别树
- [#11909](https://github.com/leanprover/lean4/pull/11909) — 单子
  符号计算的层次结构
- [#11898](https://github.com/leanprover/lean4/pull/11898),
  [#11967](https://github.com/leanprover/lean4/pull/11967),
  [#11974](https://github.com/leanprover/lean4/pull/11974) —
  优化

## 用户定义的研磨属性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--User-Defined-Grind-Attributes"
%%%

[#11765](https://github.com/leanprover/lean4/pull/11765) 实现
用户定义的 `grind` 属性。它们对于想要的用户很有用
使用 `grind` 基础设施实施策略（例如，
`progress*` 埃涅阿斯）。新的 `grind` 属性使用
命令

```lean
register_grind_attr my_grind
```

该命令类似于 `register_simp_attr`。回想一下，类似于
`register_simp_attr`，新属性不能在同一个属性中使用
文件已声明。

```
opaque f : Nat → Nat
opaque g : Nat → Nat

@[my_grind] theorem fax : f (f x) = f x := sorry

example theorem fax2 : f (f (f x)) = f x := by
  fail_if_success grind
  grind [my_grind]
```

[#11770](https://github.com/leanprover/lean4/pull/11770) 实现
支持 `grind_pattern` 处的用户定义属性。之后
使用 `register_grind_attr my_grind` 声明 `grind` 属性，一
可以写：

```
opaque f : Nat → Nat
opaque g : Nat → Nat
axiom fg : g (f x) = x

grind_pattern [my_grind] fg => g (f x)
```

## Grind 中可配置的标准化和预处理
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Configurable-Normalization-and-Preprocessing-in-Grind"
%%%

[#11776](https://github.com/leanprover/lean4/pull/11776) 添加了
属性 `[grind norm]` 和 `[grind unfold]` 用于控制
`grind` 标准化器和预处理器。

`norm` 修饰符指示 `grind` 使用定理作为
规范化规则。也就是说，该定理适用于
预处理步骤。此功能适用于高级用户
了解预处理器和 `grind` 的搜索过程
彼此互动。新用户仍然可以从中受益
通过限制其使用完全消除了定理的功能
来自目标的符号。示例：

```
theorem max_def : max n m = if n ≤ m then m else n
```

`unfold` 修饰符指示 `grind` 展开给定的定义
在预处理步骤中。示例：

```lean
@[grind unfold] def h (x : Nat) := 2 * x
example : 6 ∣ 3*h x := by grind
```

请参阅 PR 描述以获取完整的讨论。

## Grind 和 Simp 中的局部定义
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Local-Definitions-in-Grind-and-Simp"
%%%

[#11946](https://github.com/leanprover/lean4/pull/11946) 添加了一个
`grind` 策略的 `+locals` 配置选项
自动将当前文件中的所有定义添加为电子匹配
定理。这提供了手动添加的便捷替代方法
每个定义的 `[local grind]` 属性。在形式上
`grind? +locals`，对于发现哪个本地也有帮助
添加 `[local grind]` 属性可能有用的声明。

[#11947](https://github.com/leanprover/lean4/pull/11947) 添加了一个
`+locals` 配置选项到 `simp`、`simp_all` 和 `dsimp`
战术。

##  `bv_decide` 中的解算器模式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Solver-Mode-in--bv_decide"
%%%

[#11847](https://github.com/leanprover/lean4/pull/11847) 添加了一个新的
`solverMode` 字段添加到 `bv_decide` 的配置中，允许用户
为不同类型的工作负载配置 SAT 求解器。解算器模式
可以设置为：

- `proof`，改进证明搜索；
- `counterexample`，改进反例搜索；
- `default`，其中没有额外的 SAT 求解器标志。

## 并行战术组合器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Parallel-Tactic-Combinator"
%%%

[#11949](https://github.com/leanprover/lean4/pull/11949) 添加了一个新的
`first_par` 并行运行多个策略的策略组合器
并返回第一个成功的结果（取消其他结果）。

`try?` 策略的 `atomicSuggestions` 步骤现在使用 `first_par` 来
并行尝试三种研磨变体：

- `grind? +suggestions` ̵ 使用库建议引擎
- `grind? +locals` ̵ 从当前文件展开本地定义
- `grind? +locals +suggestions` ̵ 结合了两者

## 依赖管理工具
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Dependency-Management-Tools"
%%%

- [#11726](https://github.com/leanprover/lean4/pull/11726) 上游
  Mathlib 的依赖管理命令：
    - `#import_path Foo` 打印传递导入链
      将 `Foo` 纳入范围
如果声明 `Foo` 存在，则     - `assert_not_exists Foo` 出错（对于
      依赖管理）
如果 `Module` 是可传递的，    - `assert_not_imported Module` 会发出警告
      进口的
    - `#check_assertions` 验证所有未决断言
      最终满意

- [#11921](https://github.com/leanprover/lean4/pull/11921) 添加
  `lake shake` 作为内置 Lake 命令，移动抖动
  功能从 `script/Shake.lean` 到 Lake CLI。

## 外部检查器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--External-Checker"
%%%

[#11887](https://github.com/leanprover/lean4/pull/11887) 使
外部检查器 Lean4checker 可用作现有的 `leanchecker`
elan 已知的二进制文件，允许开箱即用地访问
它。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Library-Highlights"
%%%

### 范围
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Library-Highlights--Ranges"
%%%

- [#11438](https://github.com/leanprover/lean4/pull/11438) 重命名
  namespace `Std.Range` to `Std.Legacy.Range`. Instead of using
  `Std.Range` 和 `[a:b]` 表示法，新范围类型 `Std.Rco` 和
  应使用其相应的 `a...b` 符号。

### 迭代器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Library-Highlights--Iterators"
%%%

- [#11446](https://github.com/leanprover/lean4/pull/11446) 移动很多
  迭代器 API 的常量从 `Std.Iterators` 到 `Std`
  namespace in order to make them more convenient to use. These
  常量包括但不限于 `Iter`、`IterM` 和
  __修复000__。这是一个*重大变化*。如果有什么东西坏了，
  尝试添加 `open Std` 以使这些常量可用
  再次。如果 `Std.Iterators` 命名空间中的某些常量不能
  找到了，现在可以直接在`Std`中找到了。

- [#11789](https://github.com/leanprover/lean4/pull/11789) 使
  `FinitenessRelation` 结构，这在证明时很有帮助
  迭代器的有限性，公共 API 的一部分。

### 位向量
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Library-Highlights--Bitvectors"
%%%

- [#11257](https://github.com/leanprover/lean4/pull/11257) 添加了
  `BitVec.cpop` 的定义，又名 popcount。

- [#11767](https://github.com/leanprover/lean4/pull/11767)介绍
位向量的两个归纳原理，基于 concat 和
  缺点操作。

### 异步框架
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--Library-Highlights--Async-Framework"
%%%

- [#11499](https://github.com/leanprover/lean4/pull/11499) 添加了
  `Context` 类型用于通过上下文传播取消。它有效
  通过存储主上下文的分叉树，提供了一种方法
  控制取消。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Language"
%%%

* [#11553](https://github.com/leanprover/lean4/pull/11553) 使匹配方程生成器中使用的 `simpH` 产生一个
  证明术语。这是为了在 #11512 中进行更大的重构做准备。

* [#11666](https://github.com/leanprover/lean4/pull/11666) 确保当使用稀疏情况编译匹配器时，
  该方程生成还使用稀疏情况进行分割。
  这修复了#11665。

* [#11669](https://github.com/leanprover/lean4/pull/11669) 确保关于 `ctorIdx` 的证明传递给 `grind` 通过
  尽管减少了 `semireducible` 定义，但 `debug.grind` 检查。

* [#11670](https://github.com/leanprover/lean4/pull/11670) 修复了 `grind` 对 `Nat.ctorIdx` 的支持。 Nat 构造函数
  出现在 `grind` 作为偏移量或文字，而不是作为标记的节点
  `.constr`，所以也处理这种情况。

* [#11673](https://github.com/leanprover/lean4/pull/11673) 修复了公共范围内的 `by` 可能会创建一个问题
  类型与预期不匹配的证明的辅助定理
输入公共范围。

* [#11698](https://github.com/leanprover/lean4/pull/11698) 在简化判别式后使 `mvcgen` 提前返回，
  避免重写格式错误的 `match`。

当用户尝试命名某个名称时，* [#11714](https://github.com/leanprover/lean4/pull/11714) 会给出一条重点错误消息
  示例，并调整尝试定义多个的错误消息
  立即不透明的名称。

* [#11718](https://github.com/leanprover/lean4/pull/11718) 添加了针对问题 #11655 的测试，该问题似乎已由 #11695 修复

* [#11721](https://github.com/leanprover/lean4/pull/11721) 提高了生成函数的性能
  同余引理，由 `simp` 使用
  和一些其他组件。

* [#11726](https://github.com/leanprover/lean4/pull/11726) 来自 Mathlib 的上游依赖管理命令：

  - `#import_path Foo` 打印传递导入链
  `Foo` 进入范围
如果声明 `Foo` 存在，则   - `assert_not_exists Foo` 出错（对于
  依赖管理）
如果 `Module` 是可传递的，  - `assert_not_imported Module` 会发出警告
  进口的
  - `#check_assertions` 验证所有未决断言最终是否
  满意

* [#11731](https://github.com/leanprover/lean4/pull/11731) 使 expr_eq_fn 中的缓存使用 mimalloc 进行小
性能全面获胜。

* [#11748](https://github.com/leanprover/lean4/pull/11748) 修复了某些策略不允许访问的边缘情况
  模块系统下私有证明内的私有声明

* [#11756](https://github.com/leanprover/lean4/pull/11756) 修复了 `grind` 尝试展开时失败的问题
  通过 `import all` 导入的模式匹配定义（或从
  非 `module`)。

* [#11780](https://github.com/leanprover/lean4/pull/11780) 确保统一提示的漂亮打印插入一个
  |- 后的空格。 ⊢。

如果 `tac` 在其中一个 VC 上失败，则 * [#11871](https://github.com/leanprover/lean4/pull/11871) 会使 `mvcgen with tac` 失败，
  就像 `induction ... with tac` 失败，如果 `tac` 在其中之一失败
  目标。可以通过使用 try 编写 `mvcgen 来恢复旧的行为
  tac` 代替。

* [#11875](https://github.com/leanprover/lean4/pull/11875) 添加目录 `Meta/DiscrTree` 并重新组织代码
  到不同的文件中。动机：我们将为
  检索新结构简化器的简化定理。

* [#11882](https://github.com/leanprover/lean4/pull/11882) 在 `TagDeclarationExtension.tag` 上添加一个防护来检查是否
  声明名称是匿名的，如果是的话，请提前返回。这可以防止
  当像 `meta` 或 `noncomputable` 这样的修饰符被使用时可能会发生恐慌
与语法错误结合使用。

* [#11896](https://github.com/leanprover/lean4/pull/11896) 修复了当定理具有文档字符串时发生的恐慌
  `where` 子句中的辅助定义。

* [#11908](https://github.com/leanprover/lean4/pull/11908) 在消息测试命令中添加了两个功能：
  如果嵌套命令产生，则新的 `#guard_panic` 命令会成功
  一条恐慌消息（对于测试预期会出现恐慌的命令很有用），以及
  `#guard_msgs` 的 `substring := true` 选项检查文档字符串是否
  显示为输出的子字符串，而不需要精确匹配。

* [#11919](https://github.com/leanprover/lean4/pull/11919) 改进了 `initialize` （或 `opaque`）失败时的错误消息
  查找 `Inhabited` 或 `Nonempty` 实例。

* [#11926](https://github.com/leanprover/lean4/pull/11926) 向现有辅助函数用户添加 `unsafe` 修饰符
  `unsafeEIO`，并且还将该函数保留为私有。

* [#11933](https://github.com/leanprover/lean4/pull/11933) 添加了用于在期间管理消息日志的实用程序函数
  战术
  评估，并重构现有代码以使用它们。

* [#11940](https://github.com/leanprover/lean4/pull/11940) 修复了尝试声明模块时的模块系统可见性问题
  共同块内的公共感应。

* [#11991](https://github.com/leanprover/lean4/pull/11991) 修复 `declare_syntax_cat` 声明本地类别导致
  import errors when used in `module` without `public section`.

* [#12026](https://github.com/leanprover/lean4/pull/12026) 修复了 `@[irreducible]` 之类的属性不会出现的问题
  除非与 `@[exposed]` 结合使用，否则在模块系统下是允许的，
  但如果没有后者，前者可能会有所帮助，以确保下游
  非 `module` 也会受到影响。

* [#12045](https://github.com/leanprover/lean4/pull/12045) 禁用跨包边界的 `import all` 检查。现在
  任何模块都可以 `import all` 任何其他模块。

* [#12048](https://github.com/leanprover/lean4/pull/12048) 修复了 `mvcgen` 丢失 VC 导致未分配的错误
  元变量。通过将所有发出的 VC 设为合成不透明来修复此问题。

* [#12122](https://github.com/leanprover/lean4/pull/12122) 在 `where` 子句中添加了对 Verso 文档字符串的支持。

* [#12148](https://github.com/leanprover/lean4/pull/12148) 恢复 #12000，这引入了回归，其中 `simp`
  错误地拒绝对 perm 引理的有效重写。

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Library"
%%%

* [#11257](https://github.com/leanprover/lean4/pull/11257) 增加了 `BitVec.cpop` 的定义，它依赖于更多
  一般 `BitVec.cpopNatRec`，并围绕它建立一些理论。名称
  `cpop` 与 [RISCV ISA 一致
  命名法](https://msyksphinz-self.github.io/riscv-isadoc/#_cpop)。

* [#11438](https://github.com/leanprover/lean4/pull/11438) 将命名空间 `Std.Range` 重命名为 `Std.Legacy.Range`。相反
  使用 `Std.Range` 和 `[a:b]` 表示法，新范围类型 `Std.Rco`
  并应使用其相应的 `a...b` 符号。还有
其他具有开放/封闭/无限边界形状的范围
  `Std.Data.Range.Polymorphic` 和新的范围表示法也适用于
  `Int`、`Int8`、`UInt8`、`Fin` 等。

* [#11446](https://github.com/leanprover/lean4/pull/11446) 将迭代器 API 的许多常量从 `Std.Iterators` 移动到
  `Std` 命名空间，以便使它们更方便使用。这些
  常量包括但不限于 `Iter`、`IterM` 和
  __修复000__。这是一个突破性的改变。如果出现问题，请尝试
  添加 `open Std` 以使这些常量再次可用。如果
  无法找到 `Std.Iterators` 命名空间中的某些常量，它们
  现在可以直接在`Std`中找到。

* [#11499](https://github.com/leanprover/lean4/pull/11499) 添加 `Context` 类型以通过上下文取消
  传播。它的工作原理是存储主上下文的分叉树，
  提供一种控制取消的方法。

* [#11532](https://github.com/leanprover/lean4/pull/11532) 添加新操作 `MonadAttach.attach` 附加一个
  证明后置条件保持一元函数的返回值
  操作。标准库中的大多数非 CPS monad 都支持此功能
  以一种不平凡的方式进行操作。 PR 还更改了 `filterMapM`，
  `mapM` 和 `flatMapM` 组合器，以便它们将后置条件附加到
  用户提供的一元函数传递给他们。这使得
可以证明其中一些未终止的终止
  以前可能。此外，PR 添加了许多缺失的引理
  本 PR 过程中需要 `filterMap(M)` 和 `map(M)`。

* [#11693](https://github.com/leanprover/lean4/pull/11693) 可以验证迭代器上的循环。它提供
  关于 `for` 在纯迭代器上循环的 MPL 规范引理。它还提供
  重写 `mapM`、`filterMapM` 或 `filterM` 循环的规范引理
  迭代器组合器进入其基本迭代器的循环中。

* [#11705](https://github.com/leanprover/lean4/pull/11705) 提供了许多关于 `Int` 范围的引理，类似于那些
  大约 `Nat` 范围。添加了一些必要的基本 `Int` 引理。公关
  还删除 `Rcc.toList_eq_toList_rco` 上的 `simp` 注释，
  `Nat.toList_rcc_eq_toList_rco` 和配偶。

* [#11706](https://github.com/leanprover/lean4/pull/11706) 删除 `IteratorCollect` 类型类并由此简化
  迭代器 API。其有限的优势并不能证明其复杂性是合理的
  成本。

* [#11710](https://github.com/leanprover/lean4/pull/11710) 扩展了范围的 get-elem 策略，以便它支持
  子数组。示例：
  ```
  example {a : Array Nat} (h : a.size = 28) : Id Unit := do
    let mut x := 0
    for h : i in *...(3 : Nat) do
      x := a[1...4][i]
  ```

* [#11716](https://github.com/leanprover/lean4/pull/11716) 为 `for` 循环的所有组合添加更多 MPL 规范引理，
  `fold(M)` 和 `filter(M)/filterMap(M)/map(M)` 迭代器组合器。
这些组合器上的这些类型的循环（例如 `it.mapM`）是首先
  转换为对其基本迭代器 (`it`) 的循环，并且如果基本迭代器
  迭代器的类型为 `Iter _` 或 `IterM Id _`，然后是另一个规范引理
  存在用于使用不变量证明霍尔三元组，并且
  底层列表 (`it.toList`)。 PR 还修复了 MPL 始终存在的错误
  如果 `Std.Tactic.Do.Syntax` 为，则将默认优先级分配给规范引理
  未导入并且优先考虑低优先级引理的错误
  高优先级的。

* [#11724](https://github.com/leanprover/lean4/pull/11724) 添加了更多 `event_loop_lock` 来修复竞争条件。

* [#11728](https://github.com/leanprover/lean4/pull/11728) 引入了一些围绕 `BitVec.extractLsb'` 的附加引理
  和`BitVec.extractLsb`。

* [#11760](https://github.com/leanprover/lean4/pull/11760) 允许 `grind` 使用 `List.eq_nil_of_length_eq_zero` （并且
  `Array.eq_empty_of_size_eq_zero`)，但仅当它已经被证明时
  长度为零。

* [#11761](https://github.com/leanprover/lean4/pull/11761) 添加了一些 `grind_pattern` `guard` 条件
  昂贵的定理。

* [#11762](https://github.com/leanprover/lean4/pull/11762) 将研磨图案从 `Sublist.eq_of_length` 移动到
  稍微更通用 `Sublist.eq_of_length_le`，并增加了磨砺
模式保护，因此只有当我们有假设的证明时它才会激活。

* [#11767](https://github.com/leanprover/lean4/pull/11767) 介绍了位向量的两个归纳原理，基于
  concat 和 cons 操作。我们展示了这一原则如何有用
  通过重构两个人口计数引理来推理位向量
  （`cpopNatRec_zero_le` 和 `toNat_cpop_append`）并引入新的
  引理 (`toNat_cpop_not`)。
  为了使用归纳原理，我们还移动 `cpopNatRec_cons_of_le` 和
  `cpopNatRec_cons_of_lt` 位于 popcount 部分的前面（它们是
  构建模块使我们能够利用新的归纳
  原则）。

* [#11772](https://github.com/leanprover/lean4/pull/11772) 修复了优化和不安全实现中的错误
  `Array.foldlM`.

* [#11774](https://github.com/leanprover/lean4/pull/11774) 修复了 `foldlM` 和 `foldlM` 的行为之间的不匹配
  三个数组中的`foldlMUnsafe`
  类型。仅当手动指定 `stop` 时才会暴露这种不匹配
  值大于尺寸
  数组的并且只能通过 `native_decide` 来利用。

* [#11779](https://github.com/leanprover/lean4/pull/11779) 修复了最初的 #11772 PR 中的一个疏忽。

* [#11784](https://github.com/leanprover/lean4/pull/11784) 只是添加一个可选的起始位置参数
  `PersistentArray.forM`

* [#11789](https://github.com/leanprover/lean4/pull/11789) 生成 `FinitenessRelation` 结构，这在以下情况下很有帮助：
  证明迭代器的有限性，公共 API 的一部分。此前，
  它被标记为内部和实验性的。

* [#11794](https://github.com/leanprover/lean4/pull/11794) 实现函数 `getMaxFVar?` 来实现 `SymM`
  基元。

* [#11834](https://github.com/leanprover/lean4/pull/11834) 将 `num?` 参数添加到 `mkPatternFromTheorem` 来控制如何
  创建模式时，许多前导量词都会被删除。这个
  允许匹配定理，其中只有一些量词应该是
  转换为模式变量。

* [#11848](https://github.com/leanprover/lean4/pull/11848) 修复了 `Name.beq` 报告的错误
  加油站codemanager@gmail.com

* [#11852](https://github.com/leanprover/lean4/pull/11852) 更改迭代器组合器的定义 `takeWhileM`
  和 `dropWhileM` 以便他们使用 `MonadAttach`。这只是相关的
  在极少数情况下，但有时可以证明这样的组合子
  当有限性取决于一元的属性时是有限的
  谓词。

* [#11901](https://github.com/leanprover/lean4/pull/11901) 为 `Nat` 和 `Int` 添加 `gcd_left_comm` 引理：

  - `Nat.gcd_left_comm`: `gcd m (gcd n k) = gcd n (gcd m k)`
  - `Int.gcd_left_comm`: `gcd a (gcd b c) = gcd b (gcd a c)`

* [#11905](https://github.com/leanprover/lean4/pull/11905) 为 `Nat.isPowerOfTwo` 提供了一个 `Decidable` 实例，基于
公式 `(n ≠ 0) ∧ (n &&& (n - 1)) = 0`。

* [#11907](https://github.com/leanprover/lean4/pull/11907) 实现 `PersistentHashMap.findKeyD` 和
  __修复000__。动机是避免两次记忆
  当集合包含时的分配（`Prod.mk` 和 `Option.some`）
  关键。

* [#11945](https://github.com/leanprover/lean4/pull/11945) 更改 `Decidable (xs = #[])` 的运行时实现
  和 `Decidable (#[] = xs)` 实例来使用 `Array.isEmpty`。此前，
  `decide (xs = #[])` 首先将 `xs` 转换为列表，然后
  将其与 `List.nil` 进行比较。

* [#11979](https://github.com/leanprover/lean4/pull/11979) 添加 `suggest_for` 注释，使得 `Int*.toNatClamp` 是
  建议用于 `Int*.toNat`。

* [#11989](https://github.com/leanprover/lean4/pull/11989) 删除剩余的 `example`
  `src/Std/Tactic/BVDecide/Bitblast/BVExpr/Circuit/Lemmas/Operations/Clz.lean`.

* [#11993](https://github.com/leanprover/lean4/pull/11993) 将 `grind` 注释添加到有关 `Subarray` 的引理中，并且
  `ListSlice`.

* [#12058](https://github.com/leanprover/lean4/pull/12058) 实现 `Fin` 和 `Char` 范围内的迭代。

* [#12139](https://github.com/leanprover/lean4/pull/12139) 将 `«term_⁻¹»` 添加到 `inv` 的 `recommended_spelling` 中，
  匹配
  包括该函数的所有其他运算符使用的模式
  以及拼写列表中的语法。

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Tactics"
%%%

* [#11664](https://github.com/leanprover/lean4/pull/11664) 在 `grind linarith` 中添加了对 `Nat.cast` 的支持。现在它使用
  __修复000__。示例：
  ```
  open Lean Grind Std
  attribute [instance] Semiring.natCast

  variable [Lean.Grind.CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

  example (a : Nat) : 0 ≤ (a : R) := by grind
  example (a b : Nat) : 0 ≤ (a : R) + (b : R) := by grind
  ```

* [#11677](https://github.com/leanprover/lean4/pull/11677) 在 `grind linarith` 中添加了对相等传播的基本支持
  对于 `IntModule` 情况。这仅涵盖基本情况。请参阅注释
  代码。
  我们注意到此功能与 `CommRing` 无关，因为 `grind ring`
  已经对平等传播有了更好的支持。

* [#11678](https://github.com/leanprover/lean4/pull/11678) 修复了用于实现的 `registerNonlinearOccsAt` 中的错误
  __修复000__。此问题最初报告于：
  https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Weirdness.20with.20cutsat/near/562099515

* [#11691](https://github.com/leanprover/lean4/pull/11691) 修复 `grind` 以支持声明中的点符号
  引理列表。

* [#11700](https://github.com/leanprover/lean4/pull/11700) 添加指向 `grind` 文档字符串的链接。该链接将用户引导至
  参考手册中描述 `grind` 的部分。

* [#11712](https://github.com/leanprover/lean4/pull/11712) 避免调用 TC 合成和其他推理机制
  `bv_decide` 的 simprocs。这可以显着加速
  给这些模拟过程带来压力的问题。

* [#11717](https://github.com/leanprover/lean4/pull/11717) 提高了 `bv_decide` 重写器在大型机上的性能
  问题。

* [#11736](https://github.com/leanprover/lean4/pull/11736) 修复了 `exact?` 不建议私有的问题
  当前模块中定义的声明。

* [#11739](https://github.com/leanprover/lean4/pull/11739) 变成了更常用的 `bv_decide` 定理，需要
  统一为快速 simprocs
  使用句法相等。这推动了整体性能
  sage/app7 至 <= 1min10s
  每个问题。

* [#11749](https://github.com/leanprover/lean4/pull/11749) 修复了 `grind` 中使用的函数 `selectNextSplit?` 中的错误。
  它错误地计算了每个候选人的代数。

* [#11758](https://github.com/leanprover/lean4/pull/11758) 改进了对非标准 `Int`/`Nat` 实例的支持
`grind` 和 `simp +arith`。

* [#11765](https://github.com/leanprover/lean4/pull/11765) 实现用户定义的 `grind` 属性。它们对于
  想要使用 `grind` 基础设施实施策略的用户
  （例如，《埃涅阿斯记》中的 `progress*`）。新的 `grind` 属性使用以下方式声明
  命令
  ```
  register_grind_attr my_grind
  ```
  该命令类似于 `register_simp_attr`。回想一下，类似于
  `register_simp_attr`，新属性不能在同一文件中使用
  它被宣布了。
  ```
  opaque f : Nat → Nat
  opaque g : Nat → Nat

  @[my_grind] theorem fax : f (f x) = f x := sorry

  example theorem fax2 : f (f (f x)) = f x := by
    fail_if_success grind
    grind [my_grind]
  ```

* [#11769](https://github.com/leanprover/lean4/pull/11769) 使用对用户定义 `grind` 属性的新支持
实现默认的 `[grind]` 属性。

* [#11770](https://github.com/leanprover/lean4/pull/11770) 实现对用户定义属性的支持
  __修复000__。声明 `grind` 属性后
  `register_grind_attr my_grind`，可以写：
  ```
  grind_pattern [my_grind] fg => g (f x)
  ```

* [#11776](https://github.com/leanprover/lean4/pull/11776) 添加属性 `[grind norm]` 和 `[grind unfold]`
  控制 `grind` 标准化器/预处理器。

* [#11785](https://github.com/leanprover/lean4/pull/11785) 禁用反射项中使用的封闭项提取
  __修复000__。这些条款做
  封闭式提取根本不会带来任何好处，但实际上可能会导致
  数千个新的封闭学期
  声明反过来又会减慢编译器的速度。

* [#11787](https://github.com/leanprover/lean4/pull/11787) 添加了对增量处理本地声明的支持
  __修复000__。而不是在目标过程中一次处理所有假设
  初始化， `grind` 现在跟踪哪些本地声明已被
  通过 `Goal.nextDeclIdx` 处理并提供 API 来处理新的
  逐步提出假设。
  新的 `SymM` monad 将使用此功能来实现高效的符号
  模拟。

* [#11788](https://github.com/leanprover/lean4/pull/11788) 引入了 `SymM`，一个用于实现符号的新 monad
  精益中的模拟器（例如验证条件生成器）。单子
  解决了在顶部构建的符号模拟器中发现的性能问题
  面向用户的策略，如 `apply` 和 `intros`。

* [#11792](https://github.com/leanprover/lean4/pull/11792) 添加 `isDebugEnabled` 用于检查 `grind.debug` 是否设置
  当 `grind` 初始化时，到 `true`。

* [#11793](https://github.com/leanprover/lean4/pull/11793) 添加了用于创建最大共享术语的功能
  最大限度地共享条款。它比创建表达式更有效
  然后调用 `shareCommon`。我们将使用这些函数
  实现符号模拟原语。

* [#11797](https://github.com/leanprover/lean4/pull/11797) 通过分离持久性来简化 `AlphaShareCommon.State`
  和状态的瞬态部分。

* [#11800](https://github.com/leanprover/lean4/pull/11800) 增加了函数 `Sym.replaceS`，类似于
  `replace_fn` 在内核中可用，但假设输入最大
  共享并确保输出也得到最大程度的共享。公关还
  概括了 `AlphaShareBuilder` API。

* [#11802](https://github.com/leanprover/lean4/pull/11802) 添加了函数 `Sym.instantiateS` 及其变体，它们是
  类似于 `Expr.instantiate` 但假设输入最大限度地共享
并确保输出也得到最大程度的共享。

* [#11803](https://github.com/leanprover/lean4/pull/11803) 为 `SymM` 实现 `intro` （及其变体）。这些版本
  不要使用归约或推断类型，并确保表达式是
  最大限度地共享。

* [#11806](https://github.com/leanprover/lean4/pull/11806) 重构了 `grind` 中使用的 `Goal` 类型。新的
  表示允许具有不同元变量的多个目标
  共享相同的 `GoalState`。这对于自动化很有用，例如
  符号模拟器，应用定理创建多个目标
  继承相同的 E-graph、同余闭包和求解器状态，并且
  其他积累的事实。

* [#11810](https://github.com/leanprover/lean4/pull/11810) 添加了新的透明模式 `.none`，其中没有定义
  展开。

* [#11813](https://github.com/leanprover/lean4/pull/11813) 引入了快速模式匹配和统一模块
  符号模拟框架（`Sym`）。设计优先考虑
  使用两阶段方法来提高性能：

  *阶段 1（语法匹配）*
  - Patterns 使用 de Bruijn 索引作为表达式变量并重命名
  Universe 变量的级别参数 (`_uvar.0`, `_uvar.1`, ...)
  - 展开可简化定义后匹配纯粹是结构性的
  预处理期间
  - Universe 级别将 `max` 和 `imax` 视为未解释的函数（无
  交流推理）
  - 绑定器和术语元变量被推迟到第 2 阶段

  *第 2 阶段（待定限制）*
  - 处理绑定器（米勒模式）和元变量统一
  - 将剩余的 de Bruijn 变量转换为元变量
必要时   -  回退到 `isDefEq`

* [#11814](https://github.com/leanprover/lean4/pull/11814) 实现 `instantiateRevBetaS`，类似于
  `instantiateRevS` 但 beta 减少了其功能的嵌套应用程序
  替换后变为 lambda。

* [#11815](https://github.com/leanprover/lean4/pull/11815) 通过跳过证明和实例来优化模式匹配
  第一阶段（语法匹配）期间的参数。

* [#11819](https://github.com/leanprover/lean4/pull/11819) 为结构添加了一些基本基础设施（并且更便宜）
  `isDefEq` 谓词用于 `Sym` 中的模式匹配和统一。

* [#11820](https://github.com/leanprover/lean4/pull/11820) 添加了优化的 `abstractFVars` 和 `abstractFVarsRange`
  在模式期间将自由变量转换为 de Bruijn 索引
匹配/统一。

* [#11824](https://github.com/leanprover/lean4/pull/11824) 实现 `isDefEqS`，一个轻量级结构定义
  符号模拟框架的平等性。与完整的不同
  `isDefEq`，它避免了昂贵的操作，同时仍然支持 Miller
  模式统一。

* [#11825](https://github.com/leanprover/lean4/pull/11825) 完成新的模式匹配和统一程序
  使用两阶段方法的符号模拟框架。

* [#11833](https://github.com/leanprover/lean4/pull/11833) 修复了一些拼写错误，添加了缺少的文档字符串，并添加了（简单的）
  缺少优化。

* [#11837](https://github.com/leanprover/lean4/pull/11837) 添加 `BackwardRule` 通过以下方式进行有效的目标转换
  `SymM` 中的向后链接。

* [#11847](https://github.com/leanprover/lean4/pull/11847) 在 `bv_decide` 的配置中添加了一个新的 `solverMode` 字段，
  允许用户配置
  适用于不同类型工作负载的 SAT 求解器。

* [#11849](https://github.com/leanprover/lean4/pull/11849) 修复了模式中缺失的 zetaDelta 支持
  新 Sym 框架中的匹配/统一过程。

* [#11850](https://github.com/leanprover/lean4/pull/11850) 修复了 Sym 的新模式匹配过程中的错误
  框架。在期间它没有正确处理分配的元变量
模式匹配。

* [#11851](https://github.com/leanprover/lean4/pull/11851) 修复了 `Sym/Intro.lean` 对 `have` 声明的支持。

* [#11856](https://github.com/leanprover/lean4/pull/11856) 添加了所用结构简化器的基础设施
  通过符号模拟（`Sym`）框架。

* [#11857](https://github.com/leanprover/lean4/pull/11857) 为表达式添加 `shareCommon` 的增量变体
  由已经共享的子项构建。当表达式
  `e` 由精益 API（例如 `inferType`、`mkApp4`）生成，该 API
  不保留最大共享，但该 API 的输入已经
  最大限度地共享。与 `shareCommon` 不同，该函数不使用
  local `Std.HashMap ExprPtr Expr` 来跟踪访问过的节点。这更
  当新（非共享）节点数量较少时，效率较高，即
  包装构建一些构造函数节点的 API 调用时的常见情况
  围绕共享输入。

* [#11858](https://github.com/leanprover/lean4/pull/11858) 更改了 `bv_decide` 对于要使用哪种结构的启发式
  拆分也允许
  在字段具有独立类型宽度的结构上进行拆分。
  例如：
  ```
  structure Byte (w : Nat) where
    /-- A two's complement integer value of width `w`. -/
    val : BitVec w
    /-- A per-bit poison mask of width `w`. -/
    poison : BitVec w
  ```
  这是为了允许处理诸如 `(x : Byte 8)` 之类的情况，其中
宽度变为混凝土后
  分割完成。

* [#11860](https://github.com/leanprover/lean4/pull/11860) 增加了 `CongrInfo` 中函数应用的分析
  符号模拟器框架。 `CongrInfo` 决定如何构建
  有效重写子项的同余证明，分类
  函数为：

  - `none`：没有参数可以重写（例如，证明）
  - `fixedPrefix`：隐式/实例参数形成的常见情况
  固定前缀和显式参数可以重写（例如 `HAdd.hAdd`、
  `Eq`)
  - `interlaced`：可重写和不可重写参数交替（例如，
  `HEq`)
  - `congrTheorem`：使用自动生成的函数同余定理
  具有依赖证明参数（例如 `Array.eraseIdx`）

* [#11866](https://github.com/leanprover/lean4/pull/11866) 实现 `Sym` 框架的核心简化循环，
  通过有效的基于同余的参数重写。

* [#11868](https://github.com/leanprover/lean4/pull/11868) 实现 `Sym.Simp.Theorem.rewrite?` 用于重写术语
  `Sym` 中的方程定理。

* [#11869](https://github.com/leanprover/lean4/pull/11869) 添加配置标志 `Meta.Context.cacheInferType`。你可以
  使用它禁用 `MetaM` 处的 `inferType` 缓存。我们使用这个标志来
实现 `SymM` 因为它有自己的基于指针相等的缓存。

* [#11878](https://github.com/leanprover/lean4/pull/11878) 记录符号模拟框架所做的假设
  关于结构匹配和定义平等。

* [#11880](https://github.com/leanprover/lean4/pull/11880) 添加了 `with_unfolding_none` 策略来设置透明度
  模式为 `.none`，其中不展开任何定义。这补充了
  现有的 `with_unfolding_all` 策略并提供策略级别
  访问添加的 `TransparencyMode.none`
  https://github.com/leanprover/lean4/pull/11810.

* [#11881](https://github.com/leanprover/lean4/pull/11881) 修复了 `grind` 无法从 `f * r 证明 `f ≠ 0` 的问题
  ≠ 0` when using `Lean.Grind.CommSemiring`，但成功了
  `Lean.Grind.Semiring`.

* [#11884](https://github.com/leanprover/lean4/pull/11884) 添加了对符号模拟的判别树支持
  框架。
  新的 `DiscrTree.lean` 模块将 `Pattern` 值转换为
  歧视
  树键，将证明/实例参数和模式变量视为
  通配符
  （`Key.star`）。动机：重写期间有效的模式检索。

* [#11886](https://github.com/leanprover/lean4/pull/11886) 添加 `getMatch` 和 `getMatchWithExtra` 用于检索模式
  来自
  符号模拟框架中的判别树。
  PR 还添加了使用 `DiscrTree` 来实现 `Sym.simp` 中的索引。

* [#11888](https://github.com/leanprover/lean4/pull/11888) 重构了 `Sym.simp` 以使其更加通用和可定制。
  它还移动了代码
  到它自己的子目录 `Meta/Sym/Simp`。

* [#11889](https://github.com/leanprover/lean4/pull/11889) 提高了使用的判别树检索性能
  `Sym.simp`.

* [#11890](https://github.com/leanprover/lean4/pull/11890) 确保 `Sym.simp` 检查最大递归的阈值
  深度和最大步数。它还调用 `checkSystem`。
  此外，此 PR 还简化了主循环。分配的元变量
  和 `zetaDelta` 减少现在通过安装 `pre`/`post` 来处理
  方法。

* [#11892](https://github.com/leanprover/lean4/pull/11892) 优化了 `simp` 中同余证明的构造。
  它使用了 `Sym.simp` 中使用的一些想法。

* [#11898](https://github.com/leanprover/lean4/pull/11898) 添加了对简化 `Sym.simp` 中的 lambda 表达式的支持。
  对于非常大的 lambda 来说，它比标准 simpl 更有效
  具有许多活页夹的表达式。关键思想是生成一个自定义的
  lambda 类型的函数外延定理
  简化。

* [#11900](https://github.com/leanprover/lean4/pull/11900) 将 `done` 标志添加到 `Simproc`s 返回的结果中
  `Sym.simp`.

* [#11906](https://github.com/leanprover/lean4/pull/11906) 尝试最小化创建的表达式数量
  `AlphaShareCommon`.

* [#11909](https://github.com/leanprover/lean4/pull/11909) 重新组织 monad 层次结构以进行符号计算
  精益。

* [#11911](https://github.com/leanprover/lean4/pull/11911) 最小化执行的表达式分配数量
`replaceS` 和 `instantiateRevBetaS`。

* [#11914](https://github.com/leanprover/lean4/pull/11914) 分解出 `simp` 中使用的 `have` 望远镜支撑，并且
  使用 `MonadSimp` 接口实现它。目标是
  对 `Meta.simp` 和 `Sym.simp` 使用这个良好的基础设施。

* [#11918](https://github.com/leanprover/lean4/pull/11918) 从 `exact?` 和 `rw?` 建议中过滤已弃用的引理。

* [#11920](https://github.com/leanprover/lean4/pull/11920) 实现了对简化 `have` 望远镜的支持
  `Sym.simp`.

* [#11923](https://github.com/leanprover/lean4/pull/11923) 向函数 `simpHaveTelescope` 添加了一个新选项，其中
  `have` 望远镜被简化为两遍：

  * 在第一遍中，仅简化值和主体。
  * 在第二遍中，未使用的声明被消除。

* [#11932](https://github.com/leanprover/lean4/pull/11932) 消除了超线性内核类型检查开销
  简化 lambda 表达式。我改进了产生的证明项
  __修复000__。该函数在 `Sym.simp` 中简化 lambda 时使用
  表达式。

* [#11946](https://github.com/leanprover/lean4/pull/11946) 在 `grind` 策略中添加了 `+locals` 配置选项，
  自动将当前文件中的所有定义添加为电子匹配
定理。这提供了手动添加的便捷替代方法
  每个定义的 `[local grind]` 属性。以“磨？”的形式
  +locals`，它也有助于发现它的本地声明
  添加 `[local grind]` 属性可能很有用。

* [#11947](https://github.com/leanprover/lean4/pull/11947) 在 `simp`、`simp_all` 的基础上添加了 `+locals` 配置选项，
  和 `dsimp` 策略，自动添加来自
  要展开的当前文件。

* [#11949](https://github.com/leanprover/lean4/pull/11949) 添加了一个新的 `first_par` 策略组合器，可运行多个
  并行策略并返回第一个成功的结果（取消
  其他人）。

* [#11950](https://github.com/leanprover/lean4/pull/11950) 在 `Sym.simp` 中实现 `simpForall` 和 `simpArrow`。

* [#11962](https://github.com/leanprover/lean4/pull/11962) 修复库建议以包含私有证明值
  结构字段。

* [#11967](https://github.com/leanprover/lean4/pull/11967) 实施了简化 `have` 望远镜的新策略
  `Sym.simp` 实现线性内核类型检查时间而不是
  二次的。

* [#11974](https://github.com/leanprover/lean4/pull/11974) 通过以下方式优化 `Sym.simp` 中的同余证明结构
  回避
`inferType` 调用不太可能被缓存的表达式。
  而不是
  推断表达式的类型，例如 `@HAdd.hAdd Nat Nat Nat instAdd 5`，
  我们推断
  函数前缀 `@HAdd.hAdd Nat Nat Nat instAdd` 的类型和
  遍历
  福尔望远镜。

* [#11976](https://github.com/leanprover/lean4/pull/11976) 在模式期间添加了对模式变量的缺失类型检查
  匹配/统一以防止错误匹配。

* [#11985](https://github.com/leanprover/lean4/pull/11985) 实现对自动生成同余定理的支持
  `Sym.simp`，可以简化具有复杂参数的函数
  依赖项，例如证明参数和 `Decidable` 实例。

* [#11999](https://github.com/leanprover/lean4/pull/11999) 添加了对简化过度应用和
  `Sym.simp` 中未应用的功能应用术语，完成
  所有三种同余策略的实现（固定前缀，
  交错定理和同余定理）。

* [#12006](https://github.com/leanprover/lean4/pull/12006) 修复了 `extract_lets` 策略的漂亮打印。
  以前，漂亮的打印机会期望在
`extract_lets` 策略，当它后面跟着另一个策略时
  同一行：例如，
  `extract_lets; exact foo`
  将更改为
  `extract_lets ; exact foo`.

* [#12012](https://github.com/leanprover/lean4/pull/12012) 实现了对过度应用术语重写的支持
  __修复000__。示例：使用 `id_eq` 重写 `id f a`。

* [#12031](https://github.com/leanprover/lean4/pull/12031) 添加了 `Sym.Simp.evalGround`，这是一个简化过程
  评估内置数字类型的基本术语。它是专为
  `Sym.simp`.

* [#12032](https://github.com/leanprover/lean4/pull/12032) 将 `Discharger`s 添加到 `Sym.simp`，并确保缓存结果
  是一致的。

* [#12033](https://github.com/leanprover/lean4/pull/12033) 向 `Sym.simp` 添加了对条件重写规则的支持。

* [#12035](https://github.com/leanprover/lean4/pull/12035) 添加了 `simpControl`，一个处理控制流的 simproc
  诸如 `if-then-else` 之类的表达式。它简化了条件，同时
  避免在不会被采用的分支上进行不必要的工作。

* [#12039](https://github.com/leanprover/lean4/pull/12039) 实现 `Sym.simp` 的 `match` 表达式简化。

* [#12040](https://github.com/leanprover/lean4/pull/12040) 添加了 simprocs 以简化 `cond` 和依赖项
  `if-then-else` 在 `Sym.simp` 中。

* [#12053](https://github.com/leanprover/lean4/pull/12053) 在 `SymM` 中添加了对偏移项的支持。这对于
  处理自然模式匹配函数的方程定理
`Sym.simp` 中的数字。如果没有这个，它就无法处理简单的例子
  例如 `pw (a + 2)` ，其中 `pw` 模式与 `n+1` 匹配。

* [#12077](https://github.com/leanprover/lean4/pull/12077) 为 `String` 和 `Char` 实现 simprocs。它还确保
  可简化的定义在 `SymM` 中展开

* [#12096](https://github.com/leanprover/lean4/pull/12096) 清理应用时生成的临时元变量
  重写 `Sym.simp` 中的规则。

* [#12099](https://github.com/leanprover/lean4/pull/12099) 确保 `Sym.simpGoal` 不使用 `mkAppM`。也增加了
  `Sym.simp` 中的默认最大步数。

* [#12100](https://github.com/leanprover/lean4/pull/12100) 添加了 `MetaM` 和 `SymM` 之间的比较，基准测试为
  在 Lean@Google 黑客马拉松期间提出。

* [#12101](https://github.com/leanprover/lean4/pull/12101) 改进了 `Sym.simp` API。现在更容易重用
  不同简化步骤之间的简化器缓存。我们使用 API
  将基准提高到#12100。

* [#12134](https://github.com/leanprover/lean4/pull/12134) 添加了一个新的基准 `shallow_add_sub_cancel.lean`
  演示使用浅嵌入到单子中的符号模拟
  `do` 表示法，而不是深度嵌入方法
  `add_sub_cancel.lean`.

* [#12143](https://github.com/leanprover/lean4/pull/12143) 添加了用于构建符号模拟引擎的 API
  验证
利用 `grind` 的条件生成器。 API 包装 `Sym`
  操作到
  使用 `grind` 的 `Goal` 类型，实现轻量级符号执行
  同时
  携带 `grind` 状态用于放电步骤。

* [#12145](https://github.com/leanprover/lean4/pull/12145) 将预共享常用表达式从 `GrindM` 移至
  `SymM`.

* [#12147](https://github.com/leanprover/lean4/pull/12147) 添加了一个新的 API，用于帮助用户编写有针对性的重写。

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Compiler"
%%%

* [#11479](https://github.com/leanprover/lean4/pull/11479) 使专门化器也能够递归地专门化于某些
  非平凡的高阶情况。

* [#11729](https://github.com/leanprover/lean4/pull/11729) 在 LCNF 转换期间内化 Quot.lift 的所有参数，
  防止某些地区出现恐慌
  使用商的重要程序。

* [#11874](https://github.com/leanprover/lean4/pull/11874) 通过合并锁定来提高 `getLine` 的性能
  底层 `FILE*` 的。

* [#11916](https://github.com/leanprover/lean4/pull/11916) 在运行时添加一个符号用于标记 `Array`
  非线性。这应该允许用户
  在配置文件中更轻松地发现它们或使用调试器捕获它们。

* [#11983](https://github.com/leanprover/lean4/pull/11983) 修复 `floatLetIn` 传递，使其不移动变量
可能会破坏线性（拥有的变量通过 RC 1 传递）。这个
  主要改善了解析器中的情况，以前有很多
  就 `ParserState` 而言应该是线性的函数，但是
  编译器使它们成为非线性的。有关这如何影响的示例
  解析器：
  ```
  def optionalFn (p : ParserFn) : ParserFn := fun c s =>
    let iniSz  := s.stackSize
    let iniPos := s.pos
    let s      := p c s
    let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s
    s.mkNode nullKind iniSz
  ```
  之前将 `let iniSz := ...` 声明移至 `hasError` 中
  分支。然而，这意味着在调用内部时
  解析器（`p c s`），原始状态 `s` 需要 RC>1，因为它
  稍后在 `hasError` 分支中使用，破坏线性。这个修复
  防止此类移动，在 `p c s` 调用之前保留 `iniSz` 。

* [#12003](https://github.com/leanprover/lean4/pull/12003) 将编译器管理的 SCC 拆分为（可能）
  之后有多个
  执行 lambda 提升。这有助于封闭术语提取器和
  elimDeadBranches 传递为
  当申报数量超过要求时，它们都会受到负面影响
  位于一个 SCC 内。

* [#12008](https://github.com/leanprover/lean4/pull/12008) 确保 LCNF 简化器已经常数折叠决策
  程序（`Decidable`
操作）在基础阶段。

* [#12010](https://github.com/leanprover/lean4/pull/12010) 修复封闭子项提取器中的超线性行为。

* [#12123](https://github.com/leanprover/lean4/pull/12123) 修复了可能偶尔触发 ASAN 进入的问题
  通过 `IO.Process.spawn` 运行子进程时出现死锁
  框架。

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Documentation"
%%%

* [#11737](https://github.com/leanprover/lean4/pull/11737) 用指向相应部分的链接替换 `ffi.md`
  手册，因此我们不必使两份文档保持最新。

* [#11912](https://github.com/leanprover/lean4/pull/11912) 为迭代器库的某些部分添加了缺失的文档字符串，其中
  删除手册中的警告和空内容。

* [#12047](https://github.com/leanprover/lean4/pull/12047) 使策略文档中的自动第一个标记检测更加有效
  除了使其在模块和其他上下文中工作之外，更加健壮
  环境中没有内置策略。它还添加了
  能够覆盖策略的第一个标记作为用户可见的名称。

* [#12072](https://github.com/leanprover/lean4/pull/12072) 启用 `let rec` 策略的策略完成和文档，
  在 #12047 之后需要进行 stage0 更新。

* [#12093](https://github.com/leanprover/lean4/pull/12093) 使 Verso 模块文档字符串 API 更像 Markdown
  模块文档字符串API，使下游消费者能够相同地使用它们
  方式。

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Server"
%%%

* [#11536](https://github.com/leanprover/lean4/pull/11536) 更正 JSON 架构
`src/lake/schemas/lakefile-toml-schema.json` 以允许表变体
  `lakefile.toml` 中的 `require.git` 字段的
  [reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#Lake___Dependency-git).

* [#11630](https://github.com/leanprover/lean4/pull/11630) 通过以下方式提高了自动完成和模糊匹配的性能
  将 ASCII 快速路径引入其核心循环之一并使得
  Char.toLower/toUpper 更高效。

* [#12000](https://github.com/leanprover/lean4/pull/12000) 修复了转到定义会跳转到错误的问题
  存在异步定理时的位置。

* [#12004](https://github.com/leanprover/lean4/pull/12004) 允许“转到定义”查看可简化定义
  当寻找类型类实例投影时。

* [#12046](https://github.com/leanprover/lean4/pull/12046) 修复了未知标识符代码操作的错误
  NeoVim 中由于语言服务器未正确设置而损坏
  它生成的所有代码操作项的 `data?` 字段。

* [#12119](https://github.com/leanprover/lean4/pull/12119) 修复了 `where` 声明的调用层次结构
  模块系统

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Lake"
%%%

* [#11683](https://github.com/leanprover/lean4/pull/11683) 修复了 Lake 和 Lean 看待问题的方式不一致的问题
  `meta import` 的传递性。 Lake 现在按照 Lean 的预期工作，并且
  包括 `meta import` 的所有传递导入的元段
  在其传递轨迹中。

* [#11859](https://github.com/leanprover/lean4/pull/11859) 无需为数字选项编写 `.ofNat`
  __修复000__。请注意 `lake translate-config` 错误地假设
  这在早期的修订中已经是合法的。

* [#11921](https://github.com/leanprover/lean4/pull/11921) 添加 `lake shake` 作为内置 Lake 命令，移动抖动
  功能从 `script/Shake.lean` 到 Lake CLI。

* [#12034](https://github.com/leanprover/lean4/pull/12034) 更改 `enableArtifactCache` 的默认值以使用
  如果包是依赖项，则工作区的 `enableArtifactCache` 设置
  并且 `LAKE_ARTIFACT_CACHE` 未设置。这意味着a的依赖关系
  默认情况下，设置了 `enableArtifactCache` 的项目也将使用 Lake 的
  本地工件缓存。

* [#12037](https://github.com/leanprover/lean4/pull/12037) 修复了两个 Lake 缓存问题：上传失败的错误
  不会产生错误和缓存的 `--wfail` 检查中的错误
  命令。

* [#12076](https://github.com/leanprover/lean4/pull/12076) 将额外的调试信息添加到 `lake build 的运行中
  --no-build` via a `.nobuild` 跟踪文件。当构建由于以下原因失败时
  需要重建，Lake 接下来发出新的预期跟踪作为 `.nobuild`
  文件位于构建的旧 `.trace` 旁边。这些输入记录在
  然后可以比较文件以调试导致不匹配的原因。

* [#12086](https://github.com/leanprover/lean4/pull/12086) 修复了 `lake build --no-build` 将退出并带有代码的错误
`3` 如果是获取 GitHub 或 Reservoir 版本的可选作业
  包失败（即使没有其他需要重建的东西）。

* [#12105](https://github.com/leanprover/lean4/pull/12105) 修复产生 `lake query` 目标的输出
  具有自定义 `QueryText` 或 `QueryJson` 的值的 `Array` 或 `List`
  实例（例如 `deps` 和 `transDeps`）。

* [#12112](https://github.com/leanprover/lean4/pull/12112) 恢复了通过以下方式在依赖项中指定模块的能力
  基本 `+mod` 目标键。

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Other"
%%%

* [#11727](https://github.com/leanprover/lean4/pull/11727) 添加了一个 Python 脚本，帮助查找哪个提交引入了
  精益中的行为改变。它支持多种二分模式和
  当可用时自动下载 CI 工件。

* [#11735](https://github.com/leanprover/lean4/pull/11735) 添加了一个独立脚本来下载预构建的 CI 工件
  GitHub 操作。这使我们能够快速切换提交，而无需
  重建。

* [#11887](https://github.com/leanprover/lean4/pull/11887) 使外部检查器lean4checker 可用作为
  elan 已知现有的 `leanchecker` 二进制文件，允许
  开箱即用地访问它。

* [#12121](https://github.com/leanprover/lean4/pull/12121) 包装由 `lean` Verso 文档字符串生成的信息树
  上下文信息节点中的代码块。

# Ffi
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Ffi"
%%%

* [#12098](https://github.com/leanprover/lean4/pull/12098) 删除了针对精益编译库的要求
  标头必须使用 `-fwrapv`。
