/-
版权 (c) 2025 Lean FRO LLC。保留所有权利。
根据 LICENSE 文件所述，按 Apache 2.0 许可证发布。
作者：Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.26.0 (2025-12-13)" =>
%%%
tag := "release-v4.26.0"
file := "v4.26.0"
%%%

本次发布共合入 264 项变更。除下方列出的 84 项功能新增和 73 项修复外，还有 10 项重构、7 项文档改进、13 项性能改进、8 项测试套件改进，以及 69 项其他变更。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights"
%%%

## 按语义版本指定依赖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Dependencies-by-Semantic-Version"
%%%

[#10959](https://github.com/leanprover/lean4/pull/10959) 让 Lake 用户能够按语义版本范围声明 Reservoir 依赖。在执行 `lake update` 时，Lake 会从 Reservoir 获取该包的版本信息，并选择满足该范围的最新版本。

## `grind`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Grind"
%%%

### `grind_pattern` 约束
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Grind--Grind-Pattern"
%%%

[#11189](https://github.com/leanprover/lean4/pull/11189) 实现了 `grind_pattern` 约束。它们可用于控制 `grind` 中的定理实例化。举例来说，考虑下面两个定理：

```
theorem extract_empty {start stop : Nat} :
    (#[] : Array α).extract start stop = #[] := …

theorem extract_extract {as : Array α} {i j k l : Nat} :
    (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := …
```

如果这两个定理都用于定理实例化，那么一旦把项 `#[].extract i j` 加入 `grind` 上下文，就会生成无界数量的实例。

现在可以通过为 `extract_extract` 添加 `grind_pattern` 约束来防止这种情况：

```
grind_pattern extract_extract => (as.extract i j).extract k l where
  as =/= #[]
```

有了这个约束，就会如预期那样只生成一个实例：

```
/-- trace: [grind.ematch.instance] extract_empty: #[].extract i j = #[] -/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (as : Array Nat) (h : #[].extract i j = as) : False := by
  grind only [= extract_empty, usr extract_extract]
```

### `#grind_lint` 命令
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Grind--Grind-Lint"
%%%

[#11157](https://github.com/leanprover/lean4/pull/11157) 实现了 `#grind_lint` 命令，这是一个用于分析被标注为可进行定理实例化之定理行为的诊断工具。该命令有助于识别那些在 E-matching 期间会产生过多或无界实例生成的问题定理，而这可能导致性能问题。
主要入口是：

```
#grind_lint check
```

它会分析所有带有 `@[grind]` 属性的定理。对于每个定理，它都会创建一个人工目标并运行 `grind`，收集所产生实例数量的统计信息。结果会通过信息类消息汇总显示；对于超过可配置阈值的引理，还会展示详细分解。
此外还提供了若干子命令，用于定向检查与控制：

- `#grind_lint inspect thm`：详细分析一个或多个特定定理
- `#grind_lint mute thm`：在分析期间将某个定理排除在实例化之外
- `#grind_lint skip thm`：让 `#grind_lint check` 跳过对某个定理的分析

[#11167](https://github.com/leanprover/lean4/pull/11167) 为 `#grind_lint check in module <module>` 添加了支持。

### `grind` 交互模式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Grind--Grind-Interactive-Mode"
%%%

`grind` 交互模式新增了若干特性：

- 策略组合子 ` · t_1 ... t_n`，使 `finish?` 生成的脚本更简洁（[#10975](https://github.com/leanprover/lean4/pull/10975)）；

- 可在 `grind` 交互模式中通过 `set_config` 策略进行配置（[#10990](https://github.com/leanprover/lean4/pull/10990)）；

- 可用配置选项（[#10997](https://github.com/leanprover/lean4/pull/10997)）和参数（[#11012](https://github.com/leanprover/lean4/pull/11012)）控制 `finish` 与 `finish?`；

- 为 `grind only` 添加了 anchor 支持，以限制搜索空间（[#11003](https://github.com/leanprover/lean4/pull/11003)）；

- `cases_next`：一个执行下一次 case split 的策略（[#11148](https://github.com/leanprover/lean4/pull/11148)）；

- 策略 `have <ident>? : <prop>`，其中命题会使用默认的 `grind` 搜索策略来证明；这对检查或查询当前 `grind` 状态很有用（[#10919](https://github.com/leanprover/lean4/pull/10919)）。

## `try?` 中的用户扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--User-Extensions-in-try___"
%%%

[#11149](https://github.com/leanprover/lean4/pull/11149) 为 `try?` 策略添加了用户扩展机制。你既可以在签名为 `` MVarId -> Try.Info -> MetaM (Array (TSyntax `tactic)) `` 的声明上使用 `@[try_suggestion]` 属性来生成建议，也可以使用 `register_try?_tactic <stx>` 命令注册一段固定语法。只有在内建的尝试策略都已尝试且失败之后，才会尝试这些用户扩展。

## 模式匹配编译
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Match-Compilation"
%%%

本次发布包含若干针对大型 `match` 语句之模式匹配编译的性能优化（PR [#10763](https://github.com/leanprover/lean4/pull/10763)、[#11072](https://github.com/leanprover/lean4/pull/11072) 和 [#10823](https://github.com/leanprover/lean4/pull/10823)）。

## 库建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Library-Suggestions"
%%%

- [#10920](https://github.com/leanprover/lean4/pull/10920)/[#11029](https://github.com/leanprover/lean4/pull/11029) 添加了对 `grind +suggestions` 的支持：它会调用当前配置的前提选择算法，并将结果作为参数传给 `grind`。

- [#11032](https://github.com/leanprover/lean4/pull/11032) 实现了 `simp? +suggestions`，它会使用配置好的库建议引擎，将相关定理加入 `simp` 调用。

- [#11030](https://github.com/leanprover/lean4/pull/11030) 为局部定理添加了库建议引擎。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Library-Highlights"
%%%

- [#11019](https://github.com/leanprover/lean4/pull/11019) 引入了列表切片，并可通过切片记法使用（例如 `xs[1...5]`）。

- [#10933](https://github.com/leanprover/lean4/pull/10933) 添加了关于 `String.ValidPos` 和 `String.Slice.Pos` 进行终止性证明所需的基础设施。

## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Highlights--Breaking-Changes"
%%%

- [#10625](https://github.com/leanprover/lean4/pull/10625) 通过从参数列表和结构中擦除 `IO.RealWorld` 参数，实现了零成本 `BaseIO`。这对 FFI 是一项*重大破坏性变更*。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Language"
%%%

* [#10763](https://github.com/leanprover/lean4/pull/10763) 改进了模式匹配编译：按第一个剩余备选项建议的顺序对变量分支；如果第一个剩余备选项不需要分支，就不要分支。这修复了 https://github.com/leanprover/lean4/issues/10749. 通过 `set_option backwards.match.rowMajor false` 可以重新启用旧行为。

* [#10823](https://github.com/leanprover/lean4/pull/10823) 允许在模式只匹配某个归纳类型的部分而非全部构造子时，模式匹配编译过程使用稀疏 case 分析。这样会生成更少的代码。此前，会先为其余各个分支生成处理代码，再由后续编译流水线进行优化与公共化，但这样做很浪费。

* [#10826](https://github.com/leanprover/lean4/pull/10826) 修复了在字段记法（`e.f`、`(e).f`、`e |>. f`）上，“deprecated constant” 及类似错误消息的位置。修复 #10821。

* [#10851](https://github.com/leanprover/lean4/pull/10851) 使得一旦没有剩余备选项，模式匹配编译就会立即使用 `exfalso`。这样编译器无需再查看后续的 case split。

* [#10865](https://github.com/leanprover/lean4/pull/10865) 让规约 `Std.Do.Spec.forIn'_list` 及相关项在 universe 上更具多态性。

* [#10872](https://github.com/leanprover/lean4/pull/10872) 通过为 `try (mpure_intro; trivial)` 提供优化实现，提升了 `mvcgen` 的性能。这一策略序列会用于积极消解 VC，并在过程中实例化 schematic variables。

* [#10926](https://github.com/leanprover/lean4/pull/10926) 如果正在抽象 MVar，则在 `Meta.Closure.mkValueTypeClosure` 中按拓扑顺序排列被抽象的变量。修复 #10705。

* [#10931](https://github.com/leanprover/lean4/pull/10931) 从展示给策略的目标中，去除了 `WF.Fix` 用来把目标与递归调用关联起来的 `Expr.mdata`。修复 #10895。

* [#10944](https://github.com/leanprover/lean4/pull/10944) 在 `sizeOf` 声明上运行 `enableRealizationsForConst`。修复 #10573。

* [#10980](https://github.com/leanprover/lean4/pull/10980) 在 `decreasing_by` 中尽量保留 `match` 各分支里模式变量的名称：做法是对具体分支做望远镜展开，而不是对匹配器的分支类型做望远镜展开。修复 #10976。

* [#11011](https://github.com/leanprover/lean4/pull/11011) 从 #10763 中抽出了一些重构，包括删除死代码，并让 `inaccessibleAsCtor` 不再失败；这会带来（略微）更好的错误消息，也因为失败的分支实际上可能根本不可达。

* [#11024](https://github.com/leanprover/lean4/pull/11024) 让 `Bool` 像其他归纳类型一样具有 `.ctorIdx`。

* [#11068](https://github.com/leanprover/lean4/pull/11068) 从 `bv_decide` 前端移除了 `verifyEnum` 函数。这些函数会查看 matcher 的实现，以确认它们确实执行了所声称的匹配。这打破了那层抽象边界，而且本不该有此必要，因为这里只有带 `MatcherInfo` 环境条目的函数才会被纳入考虑，而它们本应都能正常工作。

* [#11072](https://github.com/leanprover/lean4/pull/11072) 添加了“稀疏 `casesOn`”构造。它们与 `.casesOn` 类似，但只为部分构造子提供分支，并带有一个 catch-all（提供 `t.ctorIdx ≠ 42` 假设）。编译器原生支持这些构造，现在也（由于它们的相似性）原生支持逐构造子的消去原理。

* [#11094](https://github.com/leanprover/lean4/pull/11094) 将 workspaceSymbol 基准测试改成 `module`，从而降低它们对标准库新增私有符号的敏感度。

* [#11095](https://github.com/leanprover/lean4/pull/11095) 开始使用 `hasIndepIndices`。该函数自 commit 54f6517ca36b237b40e02aac62ea36dbd4179758 以来一直未被使用，但看起来本就应该用到它。

* [#11107](https://github.com/leanprover/lean4/pull/11107) 为遗漏分支错误添加了测试。

* [#11122](https://github.com/leanprover/lean4/pull/11122) 修复了带菱形继承的结构上的一个问题：不再复制 docstring（除非加载 `.server.olean`，否则它们不可用），而是改为链接到它们。并添加了测试。

* [#11125](https://github.com/leanprover/lean4/pull/11125) 为前提选择器添加了过滤器，以确保不会返回已弃用的定理。

* [#11132](https://github.com/leanprover/lean4/pull/11132) 为 `try?` 添加了对 `grind +suggestions` 和 `simp_all? +suggestions` 的支持。它会输出 `grind only [X, Y, Z]` 或 `simp_all only [X, Y, Z]` 建议，而不是仅仅输出 `+suggestions`。

* [#11146](https://github.com/leanprover/lean4/pull/11146) 修复了 #11125 中的一个问题。这次还添加了测试……

* [#11150](https://github.com/leanprover/lean4/pull/11150) 新增了一个目前未激活也未使用的 `doElem_elab` 属性，未来允许用户以新类型 `DoElab` 的形式为 `doElem` 注册自定义 elaborator。旧 `do` elaborator 默认仍启用，但可通过关闭新选项 `backward.do.legacy` 来停用。

* [#11161](https://github.com/leanprover/lean4/pull/11161) 为 DTreeMap 添加了 `getEntry`/`getEntry?`/`getEntry!`/`getEntryD` 操作。

* [#11184](https://github.com/leanprover/lean4/pull/11184) 修改了当多个合成元变量无法解析时返回的错误消息。

* [#11190](https://github.com/leanprover/lean4/pull/11190) 避免在打印 “Failed to compile pattern matching” 错误时又触发 “unknown free variable”。修复 #11186。

* [#11191](https://github.com/leanprover/lean4/pull/11191) 确保在 `realizeConst` 内部 `maxHeartbeat` 选项能够生效。

# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Library"
%%%

* [#9515](https://github.com/leanprover/lean4/pull/9515) 为 `List` API 补上了一个缺失的引理。

* [#10739](https://github.com/leanprover/lean4/pull/10739) 为 `n^0` 增加了两个缺失的 `NeZero` 实例，其中 `n : Nat` 与 `n : Int`。

* [#10743](https://github.com/leanprover/lean4/pull/10743) 将名称中使用 `sorted` 的定理重命名为改用 `pairwise`。

* [#10765](https://github.com/leanprover/lean4/pull/10765) 将 `all`/`any` 函数从哈希集合扩展到哈希表和依赖哈希表，并对其进行了验证。

* [#10769](https://github.com/leanprover/lean4/pull/10769) 参照 `List.find?` 及其变体，新增了一个 `find?` consumer。

* [#10776](https://github.com/leanprover/lean4/pull/10776) 基于 zipper 为 `DTreeMap`/`TreeMap`/`TreeSet` 添加了迭代器和切片，并给出了相关的基础引理。

* [#10820](https://github.com/leanprover/lean4/pull/10820) 证明了：只要模式的 前向匹配迭代器是有限的（对我们所有模式都已知如此），`String.Slice.split` 和 `String.Slice.splitInclusive` 返回的迭代器就是有限的。

* [#10852](https://github.com/leanprover/lean4/pull/10852) 将 `String.Range` 重命名为 `Lean.Syntax.Range`，以反映它并非标准库的一部分。

* [#10853](https://github.com/leanprover/lean4/pull/10853) 将 `String.endPos` 重命名为 `String.rawEndPos`，因为未来版本中，名称 `String.endPos` 将改用于当前名为 `String.endValidPos` 的函数。

* [#10854](https://github.com/leanprover/lean4/pull/10854) 修复了从 libuv 到 lean 的 IPv4 地址编码。

* [#10865](https://github.com/leanprover/lean4/pull/10865) 让规约 `Std.Do.Spec.forIn'_list` 及相关项在 universe 上更具多态性。

* [#10896](https://github.com/leanprover/lean4/pull/10896) 为 DTreeMap/TreeMap/TreeSet 及其原始变体添加了并集操作，并提供了有关并集操作的引理。

* [#10933](https://github.com/leanprover/lean4/pull/10933) 添加了关于 `String.ValidPos` 和 `String.Slice.Pos` 进行终止性证明所需的基础设施。

* [#10941](https://github.com/leanprover/lean4/pull/10941) 从 `Std.instIrreflLtOfIsPreorderOfLawfulOrderLT` 中移除了一个冗余的实例要求。

* [#10946](https://github.com/leanprover/lean4/pull/10946) 为 ExtDHashMap/ExtHashMap/ExtHashSet 添加了并集操作，并提供了有关并集操作的引理。

* [#10952](https://github.com/leanprover/lean4/pull/10952) 用 `Iter(M).count` 取代了 `Iter(M).size`。前者使用专门的 `IteratorSize` 类型类，而后者依赖 `IteratorLoop`。`IteratorSize` 类现已弃用。该 PR 还通过将名称中的 `_Rcc` 改为 `_rcc`、`_Rco` 改为 `_roo`（等等），重命名了若干关于范围的引理，以与命名约定保持更一致。

* [#10966](https://github.com/leanprover/lean4/pull/10966) 修复了一些表述错误的引理；它们本应针对 map 的 `.Raw` 变体。

* [#10986](https://github.com/leanprover/lean4/pull/10986) 定义了 `String.Slice.replace`，并将 `String.replace` 重新定义为使用 `Slice` 版本。

* [#10993](https://github.com/leanprover/lean4/pull/10993) 允许 `grind` 在外延映射/集合上按外延方式工作。

* [#11006](https://github.com/leanprover/lean4/pull/11006) 移除了重复的引理 `Std.Do.SPred.{and_pure,or_pure,imp_pure,entails_pure_intro}`。

* [#11008](https://github.com/leanprover/lean4/pull/11008) 出于性能原因，将若干 Decidable 实例内联。

* [#11017](https://github.com/leanprover/lean4/pull/11017) 将 `String.ofList` 与 `String.toList` 确立为字符串与字符列表之间转换的首选方式，并弃用了替代方案 `String.mk`、`List.asString` 与 `String.data`。

* [#11019](https://github.com/leanprover/lean4/pull/11019) 引入了列表切片，并可通过切片记法使用（例如 `xs[1...5]`）。

* [#11021](https://github.com/leanprover/lean4/pull/11021) 为字符串上的 `Splits` 添加了更多理论，并推导出了首个面向用户的 `String` 引理 `String.toList_map`。

* [#11058](https://github.com/leanprover/lean4/pull/11058) 修改了 `Nat.ble`，将两个 `Nat.ble Nat.zero _` 分支合并为一个，从而让 `decide (0 <= x) = true` 与 `decide (0 < succ x) = true` 可以通过 `rfl` 解决。

* [#11060](https://github.com/leanprover/lean4/pull/11060) 为列表添加了 `min` 和 `max` 操作，以对应 `min?` 和 `max?`，其关系类似于 `head?` 与 `head`。

* [#11070](https://github.com/leanprover/lean4/pull/11070) 为 ExtDHashMap/ExtHashMap/ExtHashSet 添加了并集操作，并提供了有关并集操作的引理。

* [#11076](https://github.com/leanprover/lean4/pull/11076) 为 DHashMap 添加了 `getEntry`/`getEntry?`/`getEntry!`/`getEntryD` 操作。

* [#11100](https://github.com/leanprover/lean4/pull/11100) 添加了 `theorem Int.ediv_pow {a b : Int} {n : Nat} (hab : b ∣ a) : (a / b) ^ n = a ^ n / b ^ n` 及相关引理。

* [#11102](https://github.com/leanprover/lean4/pull/11102) 为 Array 引导文件补上了一些缺失的注解。

* [#11113](https://github.com/leanprover/lean4/pull/11113) 添加了一些缺失的小引理。

* [#11123](https://github.com/leanprover/lean4/pull/11123) 为 `List`/`Array`/`Vector` 添加了关于 `flatMap` 上 fold 的定理。

* [#11127](https://github.com/leanprover/lean4/pull/11127) 从 core 中移除了对 `String.Iterator` 的全部使用，改为优先使用 `String.ValidPos`。

* [#11138](https://github.com/leanprover/lean4/pull/11138) 添加了一条 `csimp` 引理，以便用 `Nat.pow` 更快地在运行时求值 `Int.pow`。

* [#11139](https://github.com/leanprover/lean4/pull/11139) 取代了 #11138。#11138 只是为 `Int.pow` 添加了 `@[csimp]` 引理，而这次则真正替换了其定义。这意味着我们不仅获得更快的运行时行为，也能利用内核对 `Nat.pow` 的特殊支持。

* [#11150](https://github.com/leanprover/lean4/pull/11150) 新增了一个目前未激活也未使用的 `doElem_elab` 属性，未来允许用户以新类型 `DoElab` 的形式为 `doElem` 注册自定义 elaborator。旧 `do` elaborator 默认仍启用，但可通过关闭新选项 `backward.do.legacy` 来停用。

* [#11152](https://github.com/leanprover/lean4/pull/11152) 将 `String.Iterator` 重命名为 `String.Legacy.Iterator`。

* [#11154](https://github.com/leanprover/lean4/pull/11154) 将 `Substring` 重命名为 `Substring.Raw`。

* [#11159](https://github.com/leanprover/lean4/pull/11159) 添加了关于 Int 范围大小的引理，对应于 `Init.Data.Range.Polymorphic.NatLemmas` 中关于 Nat 的引理。另见 https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Reasonning.20about.20PRange.20sizes.20.28with.20.60Int.60.29/with/546466339.

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Tactics"
%%%

* [#10848](https://github.com/leanprover/lean4/pull/10848) 修复了这样一个问题：在 `induction` 中于竖线后补上缺失的 case 名称时，不会移除现在已经过时的错误消息。

* [#10858](https://github.com/leanprover/lean4/pull/10858) 改进了 `grind` 交互模式中的 `done` 策略。它现在会显示所有未解子目标的 `grind` 状态诊断信息。

* [#10859](https://github.com/leanprover/lean4/pull/10859) 修复了 `grind` 交互模式中 `set_option` 的自动补全。

* [#10862](https://github.com/leanprover/lean4/pull/10862) 在 `grind` 交互模式中实现了 `show_term` 组合子。

* [#10874](https://github.com/leanprover/lean4/pull/10874) 在精化 `grind` 状态过滤器时使用了正确的上下文。

* [#10877](https://github.com/leanprover/lean4/pull/10877) 修复了 `grind order` 中的理论传播问题。

* [#10881](https://github.com/leanprover/lean4/pull/10881) 修复了 `grind` 中一个导致证明不稳定的来源。

* [#10887](https://github.com/leanprover/lean4/pull/10887) 在 `grind` 交互模式中悬停查看 `cases` 策略 anchor 时，使用新的 `TermInfo.isDisplayableTerm`。

* [#10890](https://github.com/leanprover/lean4/pull/10890) 为 `grind` 添加了 `+lax` 配置选项，使其忽略那些引用了不存在定理、或无法为其生成 pattern 的参数。这允许把大批定理（例如来自前提选择引擎）直接丢给 `grind` 看看会发生什么。

* [#10899](https://github.com/leanprover/lean4/pull/10899) 确保生成出的 `instantiate` 策略会按 `finish?` 使用的同一顺序实例化这些定理。

* [#10916](https://github.com/leanprover/lean4/pull/10916) 为 `finish?` 生成的 `instantiate` 策略实现了参数优化。
  我们使用一个简单的参数优化器，它接收两个集合作为输入：下界和上界。
  下界由证明项中实际用到的定理构成，而上界则包含某一步定理实例化中被实例化的全部定理。
  下界通常已足以重放证明，但在某些情况下，还必须包含额外定理，因为某次定理实例化可能通过提供项来参与证明，而这些项未必会出现在最终证明项中。

* [#10919](https://github.com/leanprover/lean4/pull/10919) 为 `grind` 交互模式实现了 `have <ident>? : <prop>` 策略。该命题会使用默认的 `grind` 搜索策略来证明。此策略也有助于检查或查询当前 `grind` 状态。

* [#10920](https://github.com/leanprover/lean4/pull/10920) 添加了对 `grind +premises` 的支持：它会调用当前配置的前提选择算法，并将结果作为参数传给 `grind`。（请注意 Lean4 目前并未提供默认的 premise selector：你需要下游前提选择器 才能使用这一功能。）

* [#10936](https://github.com/leanprover/lean4/pull/10936) 修复了 `grind => finish?` 中的问题；这些问题此前会导致生成的 `grind` 策略脚本无法成功重放。

* [#10937](https://github.com/leanprover/lean4/pull/10937) 修复了 `grind` 交互模式里 `cases` 策略缺少计数器重置的问题。

* [#10938](https://github.com/leanprover/lean4/pull/10938) 确保求解器 `grind` 策略（例如 `ac`、`ring`、`lia` 等）在取得进展后会处理待处理事实。

* [#10939](https://github.com/leanprover/lean4/pull/10939) 修复了另一处“构造子中的默认参数值”陷阱，它会影响 `grind` 交互模式中的 `cases` 策略。

* [#10948](https://github.com/leanprover/lean4/pull/10948) 确保 `finish?` 会生成包含 `sorry` 的部分策略脚本。
  将来我们可能会添加一个选项来禁用这一功能。
  它默认启用，因为这为调试 `grind` 失败提供了有用手段。

* [#10949](https://github.com/leanprover/lean4/pull/10949) 确保生成的策略脚本中包含关闭目标所必需的求解器传播步骤。

* [#10950](https://github.com/leanprover/lean4/pull/10950) 为 `grind` 交互模式添加了 `mbtc` 策略。它实现了基于模型的理论组合，也确保 `finish?` 能够生成它。

* [#10951](https://github.com/leanprover/lean4/pull/10951) 修复了 `cutsat` 增量模型构造中的一个问题：在断言新的（未满足）等式时，模型没有被重置。

* [#10955](https://github.com/leanprover/lean4/pull/10955) 修复了 `grind order` 模块中引入的一处回归。

* [#10956](https://github.com/leanprover/lean4/pull/10956) 修复了 `grind.order` 中相等传播过程的一个问题。具体来说，它影响的是这样一道过程：把由 `grind.order` 模块中的（ring）不等式所蕴含的等式断言到 `grind` 核心状态中。

* [#10960](https://github.com/leanprover/lean4/pull/10960) 修复了 `grind linarith` 在模型/反例构造中的一个问题。

* [#10961](https://github.com/leanprover/lean4/pull/10961) 为 `grind` 添加了对 `Rat` 科学计数法字面量的支持。`grind` 目前尚未为任意域中的此类字面量添加支持。

* [#10962](https://github.com/leanprover/lean4/pull/10962) 修复了 `grind` 中一条虚假的警告消息。

* [#10964](https://github.com/leanprover/lean4/pull/10964) 为 `a^(n+m)` 添加了一个传播器，并移除了它的规范化器。此变更的动机来自问题 #10661。

* [#10965](https://github.com/leanprover/lean4/pull/10965) 确保 `grind cutsat` 中的基于模型理论组合会考虑非线性项。诸如 `x * y` 这样的非线性乘法在 `cutsat` 中会被当作未解释符号处理。

* [#10971](https://github.com/leanprover/lean4/pull/10971) 添加了 `LawfulOfScientific` 类，以提供与 `Lean.Grind.Field` 结构的兼容性。

* [#10975](https://github.com/leanprover/lean4/pull/10975) 为 `grind` 交互模式添加了组合子 ` · t_1 ... t_n`。`finish?` 策略现在会使用该组合子生成脚本，以符合 Mathlib 编码规范。新格式也更紧凑。示例：
  ```
  /--
  info: Try this:
    [apply] ⏎
      instantiate only [= mem_indices_of_mem, insert, = getElem_def]
      instantiate only [= getElem?_neg, = getElem?_pos]
      cases #f590
      · cases #ffdf
        · instantiate only
          instantiate only [= Array.getElem_set]
        · instantiate only
          instantiate only [size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
      · instantiate only [= mem_indices_of_mem, = getElem_def]
        instantiate only [usr getElem_indices_lt]
        instantiate only [size]
        cases #ffdf
        · instantiate only [=_ WF]
          instantiate only [= getElem?_neg, = getElem?_pos, = Array.getElem_set]
          instantiate only [WF']
        · instantiate only
          instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
  -/
  #guard_msgs in
  example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
      (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
    grind => finish?
  ```

* [#10978](https://github.com/leanprover/lean4/pull/10978) 实现了以下 `grind` 改进：
  1. `set_option` 现在可用于在交互模式中设置 `grind` 配置选项。
  2. 修复了重复定理实例化检测中的一个问题。
  3. 添加宏 `use [...]`，作为 `instantiate only [...]` 的简写。

* [#10990](https://github.com/leanprover/lean4/pull/10990) 添加了用于设置 `grind` 配置选项的 `set_config` 策略。它使用与在 `grind` 主策略中设置配置选项相同的语法。

* [#10991](https://github.com/leanprover/lean4/pull/10991) 在配置选项和 trace 消息中，将 `cutsat` 重命名为 `lia`。

* [#10992](https://github.com/leanprover/lean4/pull/10992) 确保 `grind +premises` 会静默丢弃关于坏建议的警告和错误。

* [#10997](https://github.com/leanprover/lean4/pull/10997) 为 `finish` 和 `finish?` 添加了配置选项支持。

* [#11003](https://github.com/leanprover/lean4/pull/11003) 添加了在使用 `grind only` 时指定 anchor 以限制 `grind` 搜索空间的支持。Anchor 可以限制执行哪些 case split，以及实例化哪些局部引理。

* [#11012](https://github.com/leanprover/lean4/pull/11012) 确保 `grind` 策略 `finish` 和 `finish?` 可以接受参数。

* [#11026](https://github.com/leanprover/lean4/pull/11026) 修复了 `grind order` 中一个不终止问题和一个传播缺失问题。它还为算术注册了相关的 case split。

* [#11028](https://github.com/leanprover/lean4/pull/11028) 确保 `grind? +premises` 会从 “Try this” 建议中移除 `+premises`。

* [#11029](https://github.com/leanprover/lean4/pull/11029) 将所用术语从 “premise selection” 改为 “library suggestions”。这对用户更易理解（我们不假定所有人都熟悉 premise selection 文献），也避免了与 Lean 术语中既有的 “premise” 用法发生冲突（例如归纳中的 “major premise”，以及更一般地作为 “hypothesis”/“argument” 的同义词）。

* [#11030](https://github.com/leanprover/lean4/pull/11030) 为局部定理添加了库建议引擎。要让它真正有用，我仍需要编写更多组合子，以便对来自多个引擎的建议重新排序并进行合并。

* [#11032](https://github.com/leanprover/lean4/pull/11032) 实现了 `simp? +suggestions`，它会使用配置好的库建议引擎，将相关定理加入 `simp` 调用。不带 `?` 的 `simp +suggestions` 会打印一条消息，要求加上 `?`。

* [#11034](https://github.com/leanprover/lean4/pull/11034) 为 `finish?` 添加了一条新建议。它现在会像以前一样生成 `grind` 策略脚本，并额外生成一个 `finish only` 策略。示例：
  ```
  /--
  info: Try these:
    [apply] ⏎
      instantiate only [findIdx, insert, = mem_indices_of_mem]
      instantiate only [= getElem?_neg, = getElem?_pos]
      cases #1bba
      · instantiate only [findIdx]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]
    [apply] finish only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
      = HashMap.getElem_insert, #1bba]
  -/
  example (m : IndexMap α β) (a : α) (b : β) :
      (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
    grind => finish?
  ```

* [#11039](https://github.com/leanprover/lean4/pull/11039) 修复了 #11036 报告的 `grind` 无效 universe level 回归。

* [#11040](https://github.com/leanprover/lean4/pull/11040) 修复了在 `grind` 中处理广义 E-matching 模式时发生的一次崩溃。

* [#11047](https://github.com/leanprover/lean4/pull/11047) 在 `grind order` 中实现了（嵌套项的）相等传播。也就是说，它会把 `grind order` 蕴含的等式传播回 `grind` 核心。示例：
  ```
  open Lean Grind Std

  ```

* [#11049](https://github.com/leanprover/lean4/pull/11049) 在 `grind order` 中为 `Nat` 实现了相等传播。`grind order` 为 ring 支持 offset equality，但它为 `Nat` 提供了一个适配器。示例：
  ```
  example (a b : Nat) (f : Nat → Int) : a ≤ b + 1 → b + 1 ≤ a → f (1 + a) = f (1 + b + 1) := by
    grind -offset -mbtc -lia -linarith (splits := 0)
  ```

* [#11050](https://github.com/leanprover/lean4/pull/11050) 修复了 `grind order` 中对 `Nat` 的相等传播。

* [#11051](https://github.com/leanprover/lean4/pull/11051) 移除了 `grind offset` 模块，因为它如今已被 `grind order` 吸收。

* [#11057](https://github.com/leanprover/lean4/pull/11057) 使用新的 `grind => finish?` 基础设施实现了 `grind?`。

* [#11061](https://github.com/leanprover/lean4/pull/11061) 修复了内核在对 `grind` 产生的证明项做类型检查时发生的深递归问题。

* [#11071](https://github.com/leanprover/lean4/pull/11071) 确保 `grind` 中用于实现反射式证明项的 `denote` 函数都是缩写。这一变更消除了对 `withAbstractAtoms` 小工具的需求。

* [#11075](https://github.com/leanprover/lean4/pull/11075) 更新了 `simp? +suggestions`：如果名称存在歧义（因为命名空间），就使用全部候选项，而不是报错。

* [#11077](https://github.com/leanprover/lean4/pull/11077) 修复了 `grind?` 生成的 anchor 值。

* [#11080](https://github.com/leanprover/lean4/pull/11080) 修复了 `grind ring` 模块在相等传播期间的一次 panic。如果已达到最大步数，多项式可能不会被完全化简。

* [#11084](https://github.com/leanprover/lean4/pull/11084) 修复了在 `grind` 中构造证明项时发生的栈溢出。

* [#11087](https://github.com/leanprover/lean4/pull/11087) 使 `grind` 能够对 `Sum` 和 `PSum` 进行 case bash。

* [#11092](https://github.com/leanprover/lean4/pull/11092) 确保 `grind ac` 中用于反射式证明的 denotation 函数被标记为 `abbrev`。

* [#11098](https://github.com/leanprover/lean4/pull/11098) 更新了 `suggestions` 策略，使打印出的消息包含可悬停查看的类型信息（并在相关时显示分数和标志）。

* [#11099](https://github.com/leanprover/lean4/pull/11099) 改进了 `grind` 对 universe metavariable 的支持。

* [#11101](https://github.com/leanprover/lean4/pull/11101) 修复了局部 `Function.Injective f` 假设的初始化问题。

* [#11126](https://github.com/leanprover/lean4/pull/11126) 确保 `grind` 在对因前向依赖而无法清除的假设应用 `injection` 时不会失败。

* [#11133](https://github.com/leanprover/lean4/pull/11133) 修复了 `grind` 中构造子应用的非等传播问题。等价类代表元可能是不同的构造子应用，但我们必须确保它们具有相同的类型。下面这些示例在此 PR 之前会 panic：
  ```
  example (a b : List Nat)
      : a ≍ ([] : List Int) → b ≍ ([1] : List Int) → a = b ∨ p → p := by
    grind

  ```

* [#11135](https://github.com/leanprover/lean4/pull/11135) 确保在 `grind lia`（此前称为 `grind cutsat`）和 `grind ring` 中使用 `checkExp`，以防止栈溢出。

* [#11136](https://github.com/leanprover/lean4/pull/11136) 为 `try?` 添加了使用归纳的支持；它只会对当前命名空间和/或模块中定义的归纳类型执行归纳；因此目前特别不会对 `Nat` 或 `List` 这样的内建归纳类型做归纳。

* [#11137](https://github.com/leanprover/lean4/pull/11137) 修复了 `grind` 在构造证明期间的一次栈溢出。

* [#11145](https://github.com/leanprover/lean4/pull/11145) 修复了 `grind` 中 `isMatchCondCandidate` 的一个问题。缺失的条件会导致一条 “not internalized term” 的 `grind` 内部错误。

* [#11147](https://github.com/leanprover/lean4/pull/11147) 重构了 `grind` 所用对称相等同余规则的实现。

* [#11148](https://github.com/leanprover/lean4/pull/11148) 在 `grind` 交互模式中添加了 `cases_next` 策略。

* [#11149](https://github.com/leanprover/lean4/pull/11149) 为 `try?` 策略添加了用户扩展机制。你既可以在签名为 ``MVarId -> Try.Info -> MetaM (Array (TSyntax `tactic))`` 的声明上使用 `@[try_suggestion]` 属性来生成建议，也可以使用 `register_try?_tactic <stx>` 命令注册一段固定语法。只有在内建的尝试策略都已尝试且失败之后，才会尝试这些用户扩展。

* [#11157](https://github.com/leanprover/lean4/pull/11157) 实现了 `#grind_lint` 命令，这是一个用于分析被标注为可进行定理实例化之定理行为的诊断工具。该命令有助于识别那些在 E-matching 期间会产生过多或无界实例生成的问题定理，而这可能导致性能问题。
  主要入口是：
  ```
  #grind_lint check
  ```
  它会分析所有带有 `@[grind]` 属性的定理。对于每个定理，它都会创建一个人工目标并运行 `grind`，收集所产生实例数量的统计信息。结果会通过信息类消息汇总显示；对于超过可配置阈值的引理，还会展示详细分解。
  此外还提供了若干子命令，用于定向检查与控制：

  * `#grind_lint inspect thm`：详细分析一个或多个特定定理
  * `#grind_lint mute thm`：在分析期间将某个定理排除在实例化之外
  * `#grind_lint skip thm`：让 `#grind_lint check` 跳过对某个定理的分析

* [#11166](https://github.com/leanprover/lean4/pull/11166) 为 `#grind_lint` 命令实现了以下改进：
  1. 当实例数超过最小阈值时，消息会提供更多信息。
  2. 为 `#grind_lint inspect` 添加了代码操作：只要实例数超过最小阈值，就会插入 `set_option trace.grind.ematch.instance true`。
  3. 在 `#grind_lint` 中显示 `grind` 配置选项的文档字符串。
  4. 改进 `#grind_lint inspect` 与 `#grind_lint check` 的文档字符串。

* [#11167](https://github.com/leanprover/lean4/pull/11167) 为 `#grind_lint check in module <module>` 添加了支持。Mathlib 不使用命名空间，因此我们需要用模块（前缀）名来限制 `#grind_lint` 的搜索空间。示例：

  ```
  /--
  info: instantiating `Array.filterMap_some` triggers more than 100 additional `grind` theorem instantiations
  ---
  info: Array.filterMap_some
  [thm] instances
    [thm] Array.filterMap_filterMap ↦ 94
    [thm] Array.size_filterMap_le ↦ 5
    [thm] Array.filterMap_some ↦ 1
  ---
  info: instantiating `Array.range_succ` triggers 22 additional `grind` theorem instantiations
  -/
  #guard_msgs in
  #grind_lint check (min := 20) in module Init.Data.Array
  ```

* [#11168](https://github.com/leanprover/lean4/pull/11168) 修改了默认的库建议（例如用于 `grind +suggestions` 或 `simp_all? +suggestions` 的那些），使其除 Sine Qua Non 的输出外，还包含当前文件中的定理。

* [#11170](https://github.com/leanprover/lean4/pull/11170) 为 `∎`（输入 `\qed`）添加了策略模式与项模式宏，它们会展开为 `try?`。项模式版本会捕获生成出的建议，并在前面加上 `by`。

* [#11171](https://github.com/leanprover/lean4/pull/11171) 确保使用库建议的策略会设置调用者字段，以便前提选择引擎能够访问它。稍后我们会利用这一点为 `grind` 过滤掉某些模块，因为我们知道这些模块已经被完整标注过。

* [#11172](https://github.com/leanprover/lean4/pull/11172) 暂时把 `simp_all? +suggestions` 从 `try?` 中移除。它在 Mathlib 里实在太慢；建议经常会让 `simp` 陷入循环。在 `try?` 具备跳过超时策略的能力之前（或者甚至要等到有并行之后），它都需要被移除。

* [#11174](https://github.com/leanprover/lean4/pull/11174) 修改了 `try?` 框架，使每个附属策略都在独立的 `maxHeartbeats` 预算下运行。

* [#11187](https://github.com/leanprover/lean4/pull/11187) 添加了用于指定 `grind_pattern` 约束的语法，并扩展了 `EMatchTheorem` 对象。

* [#11189](https://github.com/leanprover/lean4/pull/11189) 实现了 `grind_pattern` 约束。它们可用于控制 `grind` 中的定理实例化。举例来说，考虑下面两个定理：
  ```
  theorem extract_empty {start stop : Nat} :
      (#[] : Array α).extract start stop = #[] := …

  ```

* [#11193](https://github.com/leanprover/lean4/pull/11193) 使用新的 `grind_pattern` 约束，修复了标准库中某些定理会生成无界数量定理实例化的情形。

* [#11194](https://github.com/leanprover/lean4/pull/11194) 调整了冗余 `grind` 参数的警告消息。它现在也会检查 `grind` 的定理实例化约束。

* [#11197](https://github.com/leanprover/lean4/pull/11197) 使用新的 `finish?` 基础设施实现了 `try?`。它还移除了旧的 tracing 基础设施，因为那部分现在已经过时。示例：

  ```
  /--
  info: Try these:
    [apply] grind
    [apply] grind only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
      = HashMap.getElem_insert, #1bba]
    [apply] grind only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
      = HashMap.getElem_insert]
    [apply] grind =>
      instantiate only [findIdx, insert, = mem_indices_of_mem]
      instantiate only [= getElem?_neg, = getElem?_pos]
      cases #1bba
      · instantiate only [findIdx]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]
  -/
  #guard_msgs in
  example (m : IndexMap α β) (a : α) (b : β) :
      (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
    try?
  ```

* [#11203](https://github.com/leanprover/lean4/pull/11203) 修复了 `grind` 所用新 `Action` 框架中的几个小问题。目标最终是删除旧的 `SearchM` 基础设施。`grind` 使用的主 `solve` 函数现在已基于 `Action` 框架实现。该 PR 还删除了 `SearchM` 中的死代码。

* [#11204](https://github.com/leanprover/lean4/pull/11204) 让 `#grind_list check` 生成包含 `#grind_list inspect` 命令的 “Try this:” 建议，因为这通常是处理问题案例的下一步。我们还顺手修复了一个定理的模式约束，以测试这条工作流。后续还会继续。

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Compiler"
%%%

* [#10625](https://github.com/leanprover/lean4/pull/10625) 通过从参数列表和结构中擦除 `IO.RealWorld` 参数，实现了零成本 `BaseIO`。这对 FFI 是一项*重大破坏性变更*。

* [#10727](https://github.com/leanprover/lean4/pull/10727) 通过在必要时添加 `00` 进行消歧，使名称改写变得无歧义且可注入。此外还添加了逆函数 `Lean.Name.unmangle`，可用于还原被改写的标识符。这个反改写器的加入既是为了展示该过程的单射性，也可用于例如调试时还原标识符。

* [#10856](https://github.com/leanprover/lean4/pull/10856) 在 ElimDeadBranches 中做了更多加宽，试图改善局部精度信息很多时的性能。

* [#10864](https://github.com/leanprover/lean4/pull/10864) 通过切断如下形状的一个链接环，减少了 DLL 中的符号数量：

  `Environment -> Compiler -> Meta -> Environment`

* [#10982](https://github.com/leanprover/lean4/pull/10982) 将闭包分配器改为使用通用分配器，而不是小对象分配器。
  这是因为用户可能创建携带巨量闭包变量的闭包，从而使闭包大小超过小对象阈值。

* [#11000](https://github.com/leanprover/lean4/pull/11000) 通过回退基于 Lean 的 `IO.waitAny` 实现，修复了它导致的内存泄漏。

* [#11010](https://github.com/leanprover/lean4/pull/11010) 使急切 λ 提升启发式的行为更可预测：它现在会阻止从任何可内联函数中提升，而不只是 `@[inline]`。它还调整了文档字符串，以描述实际发生的事情。

* [#11020](https://github.com/leanprover/lean4/pull/11020) 改进了代码生成器对“在同一值上多次分支”情形的检测。此前只考虑对函数参数的重复分支，现在会考虑任意值。

* [#11042](https://github.com/leanprover/lean4/pull/11042) 修复了 UInt 上一次过于激进的常量折叠：编译器会误以为 `0 - x = x`。

* [#11043](https://github.com/leanprover/lean4/pull/11043) 修复了 Nat 上一次过于激进的常量折叠：编译器会误以为 `0 - x = x`（另见 #11042，其中修复了 UInt 上的同一问题）。

* [#11044](https://github.com/leanprover/lean4/pull/11044) 强制常量折叠器 API 的使用者提供其代数性质的证明，希望能避免未来再出现 #11042 和 #11043 这样的错误。

* [#11056](https://github.com/leanprover/lean4/pull/11056) 修复了 `ST.Ref.ptrEq`，使其行为与文档描述一致。这修复了两个问题：
  1. 最近的 `IO.RealWorld` 消除 PR 忽略了这个函数（据我所知这是唯一一个），导致其返回值通常错误。
  2. 先前 `ptrEq` 的实现总会把两个不同单元中“指针等价”的值视为指针相等。然而该函数本应检查两个 `Ref` 是否是同一个单元，而不是它们包含的元素是否相同。

* [#11151](https://github.com/leanprover/lean4/pull/11151) 修复了 Verso 文档字符串的 Markdown 渲染中的一些细节，并添加测试以保证其正确性。同时还为 Verso 文档字符串元数据添加了测试。

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Documentation"
%%%

* [#11179](https://github.com/leanprover/lean4/pull/11179) 移除了多数“可能是由元变量导致”的错误消息说明，转而提供更多解释和提示。

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Server"
%%%

* [#10787](https://github.com/leanprover/lean4/pull/10787) 彻底改造了服务器日志机制，使日志输出可以按 LSP 方法过滤。

* [#10805](https://github.com/leanprover/lean4/pull/10805) 为 `TermInfo` 以及所有创建 `TermInfo` 的工具函数新增了字段 `isDisplayableTerm`，可通过设置该字段强制语言服务器在悬停弹窗中渲染该项。

# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Lake"
%%%

* [#10861](https://github.com/leanprover/lean4/pull/10861) 修复了 `input_dir` 跟踪，使其也会递归遍历子目录。`input_dir` 的 `filter` 会应用到目录树中的每个文件（不会检查目录本身的路径名）。

* [#10883](https://github.com/leanprover/lean4/pull/10883) 修复了 Lake 缓存中的一个问题：修订版本被存到了错误路径。此前它们存于 `<rev>/<pkg>.jsonl`，而正确路径应为 `<pkg>/<rev>.jsonl`。

* [#10959](https://github.com/leanprover/lean4/pull/10959) 让 Lake 用户能够按语义版本范围声明 Reservoir 依赖。在执行 `lake update` 时，Lake 会从 Reservoir 获取该包的版本信息，并选择满足该范围的最新版本。

* [#11062](https://github.com/leanprover/lean4/pull/11062) 修改了 Lake 的调试构建类型，使其在编译 C 代码时使用 `-O0` 而非 `-Og`。事实证明 `-Og` 对调试编译后的 Lean 代码并不充分——相关代码仍会被优化掉。

* [#11063](https://github.com/leanprover/lean4/pull/11063) 修改了 `lake new` 和 `lake init` 的 `math` 与 `math-lax` 模板，使其使用与当前 Lean 工具链对应版本的 Mathlib。因此，`lake +x.y.z new <pkg> math` 会使用适用于 Lean `x.y.z` 的 Mathlib。另一方面，对此类包执行 `lake update` 将不再自动更新 Mathlib。用户需要先在配置文件中修改 Mathlib 修订版本，再进行更新。

* [#11117](https://github.com/leanprover/lean4/pull/11117) 修复了 Lake 在 `lean_exe` 上忽略 `moreLinkObjs` 和 `moreLinkLibs` 的问题。

* [#11118](https://github.com/leanprover/lean4/pull/11118) 添加了 `Job.sync`，作为声明同步作业的标准方式。

* [#11169](https://github.com/leanprover/lean4/pull/11169) 将 Lake 中所有模块构建键改为按所属包进行作用域限定。这使得构建不同包中同名模块成为可能（此前只有可执行文件根在这方面支持得较好）。

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___26___0-_LPAR_2025-12-13_RPAR_--Other"
%%%

* [#11074](https://github.com/leanprover/lean4/pull/11074) 新增了 `.claude/claude.md`，其中包含 Claude Code 在此仓库中工作的基本开发说明。
