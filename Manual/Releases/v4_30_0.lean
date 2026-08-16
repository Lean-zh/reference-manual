/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "精益4.30.0 (2026-05-26)" =>
%%%
tag := "release-v4.30.0"
file := "v4.30.0"
%%%

此版本共进行了 306 项更改。
除了新增的 123 项功能外，
以及下面列出的 73 个修复，
有 17 处重构更改，
8 项文档改进，
19 项性能改进，
对测试套件进行 12 项改进，
以及 54 个其他变化。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights"
%%%

Lean 4.30.0 带来了新的交互式 `sym =>` 策略、显着扩展的 `cbv` 策略、带有用户可控借用注释的新 LCNF 编译器后端的完成，以及 Lake 缓存基础设施的重大检修。

_此亮点部分由 Juanjo Madrigal 贡献。_

## 新`sym =>`互动策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--New--sym-____GT_--Interactive-Tactic"
%%%

[#12970](https://github.com/leanprover/lean4/pull/12970) 增加了 `sym =>`，这是一种基于 {tactic}`grind` 构建的新交互战术模式。与 `grind =>` 急切地引入假设并应用反证法不同，`sym =>` 为用户提供了对每个步骤的明确控制。因此，用户可以使用 `grind` 提供的所有基础设施，但采用自定义策略：

```lean  (name := sym)
example (f : Nat → Nat) (a b : Nat)
    (hinj : ∀ x y, f x = f y → x = y) (h : f a = f b) : a = b := by
  sym => instantiate ; show_eqcs ; finish
```
```leanOutput sym
[eqc] Equivalence classes
  [eqc] {a, b}
  [eqc] {f a, f b}
```

可用策略包括 `intro`/`intros`、`apply`、`internalize`、`by_contra` 和 `simp`。像 `lia` 和 `ring` 这样的求解器会自动引入剩余的绑定器并根据需要应用矛盾。

相关开发可参见PR：[#12996](https://github.com/leanprover/lean4/pull/12996) / [#13018](https://github.com/leanprover/lean4/pull/13018) / [#13034](https://github.com/leanprover/lean4/pull/13034) / [#13039](https://github.com/leanprover/lean4/pull/13039) / [#13040](https://github.com/leanprover/lean4/pull/13040) / [#13041](https://github.com/leanprover/lean4/pull/13041) / [#13042](https://github.com/leanprover/lean4/pull/13042) / [#13046](https://github.com/leanprover/lean4/pull/13046) / [#13048](https://github.com/leanprover/lean4/pull/13048) / [#13080](https://github.com/leanprover/lean4/pull/13080)。

## `cbv` 战术扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--cbv--Tactic-Expansion"
%%%

v4.29.0 中引入的 {tactic}`cbv` 策略不再是实验性的，并在此版本中获得了主要的新功能。

{tactic}`cbv` 执行类似于按值调用评估的过程，以简化或关闭目标。

```lean
def fact : Nat → Nat
| 0 => 1
| n+1 => (n+1) * fact n

def pow2 : Nat → Nat
| 0 => 1
| n+1 => 2 * pow2 n

-- `simp` requires providing functions
example : fact 5 < pow2 7 := by simp [fact, pow2]
-- `cbv` just executes directly
example : fact 5 < pow2 7 := by cbv
```

v4.30.0 引入了以下改进：

- [#12597](https://github.com/leanprover/lean4/pull/12597)：`cbv_simproc` 系统镜像 {tactic}`simp` 的 `simproc` 基础设施。

- [#12773](https://github.com/leanprover/lean4/pull/12773)：`at` 位置语法（`cbv at h`、`cbv at h __FIX001__-` 和 `cbv at *`）。

- [#12788](https://github.com/leanprover/lean4/pull/12788)：`set_option cbv.maxSteps N` 用于用户可配置的步数限制。

- [#12763](https://github.com/leanprover/lean4/pull/12763)：`Or`/`And` 的短路评估：对于像 `decide (m < n ∨ expensive)` 这样的表达式

- 其他改进：[#12851](https://github.com/leanprover/lean4/pull/12851) / [#12944](https://github.com/leanprover/lean4/pull/12944) / [#12875](https://github.com/leanprover/lean4/pull/12875) / [#12888](https://github.com/leanprover/lean4/pull/12888)。

## 编译器：用户借用注释和新的 LCNF 后端
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Compiler___-User-Borrow-Annotations-and-New-LCNF-Backend"
%%%

### 用户借用注释
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Compiler___-User-Borrow-Annotations-and-New-LCNF-Backend--User-Borrow-Annotations"
%%%

[#12830](https://github.com/leanprover/lean4/pull/12830) 支持用户提供的借用注释。用户现在可以使用 `(x : @&Ty)` 标记函数参数，并让借用推理保留这些注释，从而减少引用计数压力：

```
def process (ctx : @& Context) (data : Array Nat) : Result :=
  ...  -- `ctx` will not be reference counted
```

编译器优先考虑保留尾部调用而不是借用注释。使用 `trace.Compiler.inferBorrow` 查看编译器推理决策的详细推理。 [#12810](https://github.com/leanprover/lean4/pull/12810) 添加了此跟踪基础设施。

[#12942](https://github.com/leanprover/lean4/pull/12942) 将 {lean}`ReaderT` 的上下文参数标记为借用 (`(a : @&ρ) → m α`)，从而导致整个元编程堆栈中的 RC 压力广泛减少。

### 新 LCNF 后端完成
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Compiler___-User-Borrow-Annotations-and-New-LCNF-Backend--New-LCNF-Backend-Complete"
%%%

[#12781](https://github.com/leanprover/lean4/pull/12781) 将 C 发射通道从 IR 移植到 LCNF，标志着 IR/LCNF 转换的最后一步，并通过新的编译基础设施实现端到端代码生成。

[#12665](https://github.com/leanprover/lean4/pull/12665) 将扩展重置/重用传递移植到 LCNF，并改进了指数代码预防，从而导致*二进制大小减少约 15%*，并全面提升速度。

### 其他编译器改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Compiler___-User-Borrow-Annotations-and-New-LCNF-Backend--Other-Compiler-Improvements"
%%%

- [#12971](https://github.com/leanprover/lean4/pull/12971) 将 Lean 的默认堆栈大小增加到 1GB（页面是动态分配的，因此这不会增加内存使用量）。堆栈大小可以通过 `LEAN_STACK_SIZE_KB` 自定义。
- [#12539](https://github.com/leanprover/lean4/pull/12539) 用 `Lean.Compiler.NameDemangling` 中的单一事实来源替换了三个独立的名称重组实现（Lean、C++、Python），删除了约 1,400 行重复代码。
- [#12724](https://github.com/leanprover/lean4/pull/12724)、[#12727](https://github.com/leanprover/lean4/pull/12727) 将地面数组和装箱标量文字提取到静态初始化数据中。

## Lake 缓存大修
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Lake-Cache-Overhaul"
%%%

此版本对 Lake 的缓存基础设施进行了全面检修：

- [#12634](https://github.com/leanprover/lean4/pull/12634)：使 Lake 能够按需从远程缓存服务下载工件，作为 `lake build` 的一部分。

- [#12927](https://github.com/leanprover/lean4/pull/12927)：`lake cache get` 更改为默认下载工件。可以使用新的 `--mappings-only` 选项按需下载工件。

- [#12974](https://github.com/leanprover/lean4/pull/12974)：使用 `curl --parallel` 进行上传和下载并行工件传输。

- [#13164](https://github.com/leanprover/lean4/pull/13164)：通过在单个批量 POST 请求中从 Reservoir 获取所有工件 URL（而不是每个工件重定向）来进行下载优化。

- [#12914](https://github.com/leanprover/lean4/pull/12914)：`.ltar` 通过 `leantar` 进行存档打包/解包。

- [#13144](https://github.com/leanprover/lean4/pull/13144)：用于分阶段缓存上传的新 `lake cache` 子命令：`stage`、`unstage` 和 `put-staged`，与 Mathlib 的 `lake exe cache` 中的同名命令并行运行。

- [#12935](https://github.com/leanprover/lean4/pull/12935)：新的 `fixedToolchain` 选项适用于仅预期在单个工具链（如 Mathlib）上运行的包。

## 其他语言改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Other-Language-Improvements"
%%%

- [#13011](https://github.com/leanprover/lean4/pull/13011) 添加了 `@[deprecated_arg]`，这是一个用于弃用单个函数参数的新属性。当调用者使用旧的参数名称时，阐述器会发出带有代码操作提示的弃用警告。
- [#12756](https://github.com/leanprover/lean4/pull/12756) 添加了 `deriving noncomputable instance Foo for Bar` 语法，以便可以将增量派生实例标记为不可计算。
- [#13117](https://github.com/leanprover/lean4/pull/13117) 通过在 olean 序列化时计算公理依赖关系来重新启用模块系统下的 `#print axioms`。
- [#12866](https://github.com/leanprover/lean4/pull/12866) 向 `doPatDecl` 解析器添加 `optType` 支持，允许在 do 表示法中使用 `let ⟨width, height⟩ : Nat × Nat ← action`。
当类类型的 `def` 未声明适当的可归约性（例如 `@[reducible]` 或 `@[implicit_reducible]`）时，- [#12325](https://github.com/leanprover/lean4/pull/12325) 添加警告。
- [#12233](https://github.com/leanprover/lean4/pull/12233) 使用两遍实现替换 `instantiateMVars`，该实现将二次复杂度从延迟分配元变量的长链降低为线性。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Library-Highlights"
%%%

### HTTP 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Library-Highlights--HTTP-Library"
%%%

[#12126](https://github.com/leanprover/lean4/pull/12126)、[#12127](https://github.com/leanprover/lean4/pull/12127)、[#12128](https://github.com/leanprover/lean4/pull/12128) 和 [#12144](https://github.com/leanprover/lean4/pull/12144) 介绍了核心 HTTP 数据类型：`Request`、`Response`、`Status`、`Version`、`Method`、`Headers`、`URI` 和流式 `Body`。这是 Lean 标准 HTTP 库的基础。

### 其他库添加
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Library-Highlights--Other-Library-Additions"
%%%

- 字符串验证从 v4.29.0 开始继续进行，并提供 `startsWith`、`skipPrefix?`、`dropPrefix?`、`endsWith`、`dropSuffix?`、`split`、`intercalate`、`isNat`、`toNat?`、`isInt`、 `toInt?`、`drop`、`take` 等。
- [#12852](https://github.com/leanprover/lean4/pull/12852) 添加一个 `PersistentHashMap` 迭代器，[#12844](https://github.com/leanprover/lean4/pull/12844) 添加一个 `append` 组合器用于迭代器串联。
- [#12385](https://github.com/leanprover/lean4/pull/12385) 添加了 `Array.mergeSort`，这是一种稳定的 O(n log n) 最坏情况排序，对于大型随机数组，测量速度大约是 `List.mergeSort` 的两倍。
- [#12430](https://github.com/leanprover/lean4/pull/12430) 提供 `WellFounded.partialExtrinsicFix` 用于实现和验证部分终止函数。
- [#12702](https://github.com/leanprover/lean4/pull/12702) 位于 Batteries/Mathlib 的 `List.splitOn` 和 `List.splitOnP` 上游。
- [#12433](https://github.com/leanprover/lean4/pull/12433) 为 `BitVec.cpop` 添加了高效的并行前缀和位爆破电路。

## 实验：使用 `idbg` 进行实时调试
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Experimental___-Live-Debugging-with--idbg"
%%%

[#12648](https://github.com/leanprover/lean4/pull/12648) 添加了实验性 `idbg e` 语法，用于语言服务器和正在运行的已编译精益程序之间的实时调试。当放置在 `do` 块中时，`idbg` 捕获作用域和表达式 `e` 中的局部变量，然后通过 TCP 将正在运行的程序连接到语言服务器，以使用实际运行时值计算 `e` 。可以在程序运行时编辑表达式 - 每次编辑都会触发重新评估，并将更新的结果显示为信息诊断。这是实验性的，有已知的限制（一次单个 `idbg`，必须设置 `LEAN_PATH`，在 Windows/macOS 上未经测试）。

## 重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Highlights--Breaking-Changes"
%%%

- [#12897](https://github.com/leanprover/lean4/pull/12897)：依赖于这些实例之前的“defeq滥用”或依赖于其特定结构的证明可能需要调整。由于 `inferInstanceAs A` 现在需要在继续之前准确地知道源和目标类型，因此它不能再用作 `(inferInstance : A)` 的同义词，当源和目标类型相同时，请使用后者。
- [#13005](https://github.com/leanprover/lean4/pull/13005)：直接调用 `compileDecl` 的元程序现在可能需要在适当的情况下首先调用 `markMeta`，可能基于现有声明的 `isMarkedMeta` 的值。为此，`addAndCompile` 应拆分为 `addDecl` 和 `compileDecl`，以便在其间插入调用。
- [#12749](https://github.com/leanprover/lean4/pull/12749) 重命名元编程 API：`isStructureLike` → `isNonRecStructure`、`matchConstStructLike` → `matchConstNonRecStructure`、`getStructureLikeCtor?` → `getNonRecStructureCtor?`、`getStructureLikeNumFields` → `getNonRecStructureNumFields`。
- [#12771](https://github.com/leanprover/lean4/pull/12771) 将 `String.Slice.Pos.cast` 的签名更改为需要 `s.copy = t.copy` 而不是 `s = t`。如果需要，可以通过将 `proof` 替换为 `congrArg Slice.copy proof` 来轻松调整它的使用。
- [#12435](https://github.com/leanprover/lean4/pull/12435) 更改 `Option.getElem?_inj` 的签名。
- [#12708](https://github.com/leanprover/lean4/pull/12708) 更改 `PostCond.noThrow`、`PostCond.mayThrow`、`PostCond.entails`、`PostCond.and`、`PostCond.imp` 中隐式参数的顺序，以便 `α` 始终位于 `ps` 之前。
- [#12603](https://github.com/leanprover/lean4/pull/12603)：具有以无类型绑定程序开头的构造函数的归纳类型可能需要重写，例如如果存在具有该名称的 `variable` 或者如果它旨在隐藏归纳类型的参数之一，则将 `(x)` 更改为 `(x : _)`。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Language"
%%%

````markdown

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  修复 `processDefDeriving` 以将 `meta` 属性传播到通过增量派生派生的实例，以便 `public meta section` 内的 `deriving BEq` 生成元实例。以前，派生的 `instBEqFoo` 未标记元，并且 LCNF 可见性检查器拒绝在别名上使用 `==` 的元定义 - 这是在将 verso 升级到 v4.30.0-rc1 时出现的。

- [#13311](https://github.com/leanprover/lean4/pull/13311)
  向 `addAndCompile` 添加一个可选的 `markMeta : Bool := false` 参数，以便调用者可以传播 `meta` 标记，而无需手动拆分为 `addDecl` + `markMeta` + `compileDecl`。

- [#13304](https://github.com/leanprover/lean4/pull/13304)
  当实例类型为 `Prop` 时，使增量派生处理程序创建 `theorem` 声明而不是 `def` 声明。以前，`deriving instance Nonempty for Foo` 总是会创建 `def`，这与手写的 `instance` 声明的行为不一致。

- [#13188](https://github.com/leanprover/lean4/pull/13188)
  扩展 `missingDocs` linter 来检测和警告空文档字符串（例如 `/---/` 或 `/-- -/`）以及丢失的文档字符串。以前，空的文档注释会使 linter 静音，即使它不提供任何文档价值。现在，空文档字符串会产生明显的“空文档字符串...”警告，而 `@[inherit_doc]` 仍然像以前一样抑制警告。

- [#13192](https://github.com/leanprover/lean4/pull/13192)
修复了使用新的 do elaborator 时 `do` 块内匿名相关 `if` (`if _ : cond then ... else ...`) 的处理。

- [#13011](https://github.com/leanprover/lean4/pull/13011)
  添加 `@[deprecated_arg]` 属性，将各个函数参数标记为已弃用。当调用者使用旧的参数名称时，阐述器会发出弃用警告，并带有代码操作提示以重命名或删除参数，并以静默方式将值转发到正确的绑定器。

- [#13153](https://github.com/leanprover/lean4/pull/13153)
  将新的 `spec_invariant_type` 属性与旧属性一起注册
  `mvcgen_invariant_type`，重命名内部标识符，并替换
  硬编码 `Invariant` 使用 `isSpecInvariantType` 签入 `Spec.lean`。

- [#13117](https://github.com/leanprover/lean4/pull/13117)
  通过在 olean 序列化时计算公理依赖关系，重新启用模块系统下的 `#print axioms`。它恢复#8174 并用正确的修复程序替换它。

- [#13142](https://github.com/leanprover/lean4/pull/13142)
  将 `exportEntriesFnEx` 的每级 `OLeanLevel → Array α` 返回类型替换为新的 `OLeanEntries (Array α)` 结构，该结构将导出的、服务器和私有条目捆绑在一起。这允许扩展在所有三个 olean 级别之间共享昂贵的计算，而不是被调用三次。

- [#13120](https://github.com/leanprover/lean4/pull/13120)
  恢复 `mvcgen witnesses` 语法添加并撤消 `elabMVCGen` 中的向后兼容 hack。

- [#13111](https://github.com/leanprover/lean4/pull/13111)
  恢复 #12882，将 `@[mvcgen_witness_type]` 标记属性和 `witnesses` 部分添加到 `mvcgen`。 Théophile Wallez 确认他不需要此功能，并且可以使用 `invariants` 来实现，因此拥有它没有任何用处。

- [#13059](https://github.com/leanprover/lean4/pull/13059)
  将 `normalizeInstance` 从使用 `isMetaSection` 切换到现有的 `declName?` 模式（已由 `BuiltinNotation.lean` 中的 `unsafe` 和 `BuiltinTerm.lean` 中的 `private_decl%` 使用）来确定辅助定义是否应标记为 `meta`。

- [#12973](https://github.com/leanprover/lean4/pull/12973)
  使定理在几乎所有方面都变得不透明，包括在内核中。

- [#12987](https://github.com/leanprover/lean4/pull/12987)
  提取传递给结构中的 `brecOn` 的函数 (lambda)
  递归到命名的 `_f` 辅助定义（例如 `foo._f`），类似于
  有根据的递归如何使用 `._unary`。这样函数就显示出来了
  在内核诊断中使用有用的名称，而不是作为匿名 lambda。

- [#13043](https://github.com/leanprover/lean4/pull/13043)
  修复了一个错误，其中 `inferInstanceAs` 和默认的 `deriving` 处理程序在 `meta section` 内部使用时，会创建未标记为 `meta` 的辅助定义（通过 `normalizeInstance`）。这导致编译器拒绝父 `meta` 定义：

  ```
  Invalid `meta` definition `instEmptyCollectionNamePrefixRel`, `instEmptyCollectionNamePrefixRel._aux_1` not marked `meta`
  ```

- [#13029](https://github.com/leanprover/lean4/pull/13029)
  删除未使用的 `change ... with` 策略语法。

- [#12897](https://github.com/leanprover/lean4/pull/12897)
  调整 `inferInstanceAs` 和 `def` `deriving` 处理程序的结果，以符合最近加强的可简化性限制。此更改可确保在派生或推断半可约类型定义的实例时，当实例以低于半可约透明度的方式约简时，定义的 RHS 不会泄漏。

- [#13005](https://github.com/leanprover/lean4/pull/13005)
进一步强制编译时执行中使用的所有模块都必须进行元导入，以准备启用 https://github.com/leanprover/lean4/pull/10291

- [#12840](https://github.com/leanprover/lean4/pull/12840)
  修复了使用私有导入导致下游模块中出现未知命名空间的问题。

- [#12953](https://github.com/leanprover/lean4/pull/12953)
  修复了当 `using` 子句包含嵌套策略时 `induction` 和 `cases` 策略会吞噬诊断（例如未解决的目标错误）的问题。

- [#12979](https://github.com/leanprover/lean4/pull/12979)
  使 `#print` 显示完整的内部私有名称（包括
  当 `pp.privateNames` 为时，声明签名中包含模块前缀）
  设置为 true。以前，`pp.privateNames` 仅影响
  主体但签名总是去掉私有前缀。

- [#12964](https://github.com/leanprover/lean4/pull/12964)
  修复了 `realizeConst` 会生成辅助声明的问题
  （如 `_sparseCasesOn`）使用原始定义模块的私有名称前缀
  而不是实现模块的前缀。当两个模块独立实现时
  相同的导入常量，它们产生相同名称的辅助声明，
  导致钻石导入时出现“环境已包含”错误。

- [#12881](https://github.com/leanprover/lean4/pull/12881)
  添加 `Invariant.withEarlyReturnNewDo`、`StringInvariant.withEarlyReturnNewDo` 和 `StringSliceInvariant.withEarlyReturnNewDo`，它们使用 `Prod` 而不是 `MProd` 作为状态元组，匹配新的 do elaborator 的输出。现有的 `withEarlyReturn` 定义将恢复为 `MProd` 以向后兼容旧版 do elaborator。测试和不变建议已更新为使用 `NewDo` 变体。

- [#12880](https://github.com/leanprover/lean4/pull/12880)
  将 `@[mvcgen_invariant_type]` 应用到 `Std.Do.Invariant` 并删除 `isMVCGenInvariantType` 中引导所需的硬编码回退（参见#12874）。它还提取 `StringInvariant` 和 `StringSliceInvariant` 作为用 `@[mvcgen_invariant_type]` 标记的命名缩写，以便 `mvcgen` 正确分类字符串和字符串切片循环不变量。

- [#12874](https://github.com/leanprover/lean4/pull/12874)
  添加 `@[mvcgen_invariant_type]` 标签属性，以便用户可以标记
  自定义类型作为 `mvcgen` 策略的不变类型。目标类型为
  标记类型的应用被归类为不变量而不是验证
  条件。保留 `Std.Do.Invariant` 的硬编码检查作为后备
直到 stage0 更新允许直接应用该属性。

- [#12767](https://github.com/leanprover/lean4/pull/12767)
  确保名称中带有 `Meta` 或 `Simproc` 的标识符不会出现在库搜索结果中。

- [#12866](https://github.com/leanprover/lean4/pull/12866)
  向 `doPatDecl` 解析器添加 `optType` 支持，允许
  do 符号中的 `let ⟨width, height⟩ : Nat × Nat ← action`。此前，仅
  不太符合人体工程学的 `let ⟨width, height⟩ : Nat × Nat := ← action` 解决方法
  可用。类型注释作为
  预期类型，匹配 `doIdDecl` 的现有行为。

- [#12698](https://github.com/leanprover/lean4/pull/12698)
  将 `result? : Option TraceResult` 字段添加到 `TraceData` 并将其填充到 `withTraceNode` 和 `withTraceNodeBefore` 中，以便行走跟踪树的元程序可以在结构上确定成功/失败，而不是在表情符号上进行字符串匹配。

- [#12233](https://github.com/leanprover/lean4/pull/12233)
  用两遍变体替换默认的 `instantiateMVars` 实现，该变体将 fvar 替换融合到遍历中，避免对延迟分配的 MVar 进行单独的 `replace_fvars` 调用并保留共享。旧的单遍实现被完全删除。

- [#12560](https://github.com/leanprover/lean4/pull/12560)
  改变 `linter.unusedSimpArgs` 的 linting 从环境中获取值的方式。这是通过使用 `Lean.Linter.Basic` 中定义的适当辅助函数来实现的。

- [#11427](https://github.com/leanprover/lean4/pull/11427)
  修改 `#eval e` 以使用范围内的节变量详细说明 `e`。虽然不可能使用自由变量评估表达式，但这可以让 `#eval` 给出比“未知标识符”更好的错误消息。

- [#12841](https://github.com/leanprover/lean4/pull/12841)
  更改了 `structure`/`class` 命令的详细说明，以便默认值在上下文中也具有后续字段。这允许字段默认值取决于它们之前和之后的字段。虽然继承字段在某种程度上已经是这种情况，但现在它统一适用于所有字段。此外，在详细说明字段的默认值时，将从上下文中清除依赖于该字段的所有字段，以避免默认值依赖于其自身的情况。

- [#12749](https://github.com/leanprover/lean4/pull/12749)
  将内部文档、错误消息、元编程 API 和内核中的“类似结构”术语更改为“非递归结构”，以阐明 Lean 的类型理论。 *结构* 是一种没有索引的单构造函数归纳类型 - 这些可以通过 `structure` 或 `inductive` 命令创建 - 并且受原始 `Expr.proj` 投影支持。只有*非递归*结构才有 eta 转换规则。 PR 描述包含已重命名的 API。

- [#12662](https://github.com/leanprover/lean4/pull/12662)
  调整模块解析器，将第一个标记的前导空白设置为该标记之前的空白。如果文件中没有实际令牌，则在最终（空）EOI 令牌上设置前导空格。这确保我们不会丢失 `Syntax` 中文件的初始空白（例如注释）。

- [#12325](https://github.com/leanprover/lean4/pull/12325)
  向任何未声明适当可归约性的类类型的 `def` 添加警告。

- [#12817](https://github.com/leanprover/lean4/pull/12817)
将全域级别计数检查从 `unfold_definition_core` 移至 `is_delta`，建立不变式：如果 `is_delta` 成功，则 `unfold_definition` 也会成功。这可以防止当 `lazy_delta_reduction_step` 中的调用站点无条件取消引用 `unfold_definition` 的结果时发生崩溃（SIGSEGV 或乱码错误），即使在级别参数计数不匹配的情况下也是如此。

- [#12802](https://github.com/leanprover/lean4/pull/12802)
  将 https://github.com/leanprover/lean4/pull/12757（在 https://github.com/leanprover/lean4/pull/12801 中恢复）与 `release-ci` 标签重新应用，以测试它是否会导致 v4.29.0-rc5 标记 CI 中出现的异步扩展 PANIC。

- [#12789](https://github.com/leanprover/lean4/pull/12789)
  当实例类型为 `Prop` 时，跳过 `processDefDeriving` 中的不可计算预检查。由于编译器会删除证明，因此可计算性与 `Prop` 值实例无关。

- [#12776](https://github.com/leanprover/lean4/pull/12776)
  修复了有根据的递归定义上的 `@[implicit_reducible]` 。

- [#12778](https://github.com/leanprover/lean4/pull/12778)
  修复了 `getStuckMVar?` 中的不一致问题，其中类投影函数和辅助父投影的实例参数在检查卡住的元变量之前未进行 whnf 标准化。 `getStuckMVar?` 中的所有其他情况（递归器、商递归器、`.proj` 节点）在递归之前通过 `whnf` 规范化主要参数 — 类投影函数和辅助父投影是例外。

- [#12756](https://github.com/leanprover/lean4/pull/12756)
  添加 `deriving noncomputable instance Foo for Bar` 语法，以便可以将增量派生实例标记为不可计算。以前，当底层实例不可计算时，`deriving instance` 将失败并出现不透明的异步编译错误。

- [#12699](https://github.com/leanprover/lean4/pull/12699)
  为 `generate` 函数的“将 @Foo 应用到目标”跟踪节点提供自己的跟踪子类 `Meta.synthInstance.apply`，而不是共享父类 `Meta.synthInstance` 。

- [#12701](https://github.com/leanprover/lean4/pull/12701)
  修复了结构精译过程中如何将 `@[implicit_reducible]` 分配给父投影的差距。

- [#12719](https://github.com/leanprover/lean4/pull/12719)
  将 `levelZero` 和 `Level.ofNat` 标记为 `@[implicit_reducible]`，以便当定义相等性检查器尊重透明度注释时 `Level.ofNat 0 =?= Level.zero` 成功。如果没有这个，带有隐式 `Level` 参数的结构之间的强制转换就会失败，正如 @FLDutchmann 在 [Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/576131374) 上所报告的那样。

- [#12695](https://github.com/leanprover/lean4/pull/12695)
  修复了 `Meta.zetaReduce` 中的错误，其中 `have` 表达式没有被减少 zeta。它还添加了一个功能，可以减少局部函数的应用程序的 beta 减少，以及另一个可以禁用 zeta-delta 减少的功能。这些都可以通过标志来控制：
  - `zetaDelta` （默认值：true）启用展开局部定义
  - `zetaHave` （默认值：true）启用 zeta 减少 `have` 表达式
  - `beta`（默认值：true）启用本地定义的 beta 减少应用程序

- [#12696](https://github.com/leanprover/lean4/pull/12696)
  修复了 Alexander Bentkamp 报告的一个测试用例，由于在 `mvcgen` 中大胆使用 `withDefault` `rfl`，该测试用例遇到了心跳限制。

- [#12680](https://github.com/leanprover/lean4/pull/12680)
  修复了 `mutual public structure` 有私有构造函数的问题。该修复复制了 #11940 中的修复。

- [#12602](https://github.com/leanprover/lean4/pull/12602)
  限制并特别简化了 `evalConst` 与 `(checkMeta := true)` 的语义（这是默认值）：如果传递的常量名称不是 `meta` （并且我们位于 `module` 下），它现在会失败。

- [#12603](https://github.com/leanprover/lean4/pull/12603)
添加了一个功能，其中 `inductive` 构造函数可以覆盖类型参数的绑定类型，如 #9480 中的 `structure` 。例如，可以在构造函数 `Eq.refl` 中显式设置 `x`，而不是隐式：
  ```lean
  inductive Eq {α : Type u} (x : α) : α → Prop where
    | refl (x) : Eq x x
  ```

- [#12647](https://github.com/leanprover/lean4/pull/12647)
  将缺少的 `popScopes` 调用添加到 `withNamespace`，之前的
  只从 elaborator 的 `Command.State` 中删除了范围，但没有弹出
  环境的 `ScopedEnvExtension` 状态堆栈。这导致了作用域语法
  当 `withNamespace` 有时声明将关键字泄漏到其名称空间之外
  被召唤。

- [#12673](https://github.com/leanprover/lean4/pull/12673)
  允许在新的 `do` 阐述器中使用依赖 `match` 的轻量级版本：判别式类型比以前的判别式更抽象。匹配结果类型和本地上下文仍然不考虑抽象。例如，如果 `i : Nat` 和 `h : i < len` 都是判别式，那么如果替代项将 `i` 与 `0` 匹配，我们也有 `h : 0 < len`：

  ```lean
  example {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
    let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
      match i, h with
      | 0,   _ => pure b
      | i+1, h =>
        have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
        have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
        have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
        match (← f as[as.size - 1 - i] (Array.getElem_mem this) b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => loop i (Nat.le_of_lt h') b
    loop as.size (Nat.le_refl _) b
  ```

- [#12608](https://github.com/leanprover/lean4/pull/12608)
  继续#9674，清理 `let rec` 和 `where` 定义体内的绑定器注释。

- [#12666](https://github.com/leanprover/lean4/pull/12666)
  修复了以 `do` 表示法表示的非原子匹配判别式中使用的变量的虚假未使用变量警告。例如，在 `match Json.parse s >>= fromJson? with` 中，变量 `s` 将被报告为未使用。

- [#12661](https://github.com/leanprover/lean4/pull/12661)
  使用新的 do elaborator 修复了在 `try`/`catch` 块内重新分配的可变变量的误报“未使用变量”警告。

````

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Library"
%%%

```markdown

- [#13175](https://github.com/leanprover/lean4/pull/13175)
  fixes the wrong behavior of a stream in http_body.

- [#12144](https://github.com/leanprover/lean4/pull/12144)
  introduces the `Body` type class, the `ChunkStream` and `Full` types that are used to represent streaming bodies of Requests and Responses.

- [#13129](https://github.com/leanprover/lean4/pull/13129)
  implements verification infrastructure for backwards patterns that is analogous to the existing infrastructure for forward patterns. Based on this it adds verification for the `skipSuffix?`, `endsWith` and `dropSuffix?` functions on strings.

- [#12912](https://github.com/leanprover/lean4/pull/12912)
  adds trivial lemmas about `ExceptCpsT.runK` to match the existing lemmas about `.run`.

- [#13109](https://github.com/leanprover/lean4/pull/13109)
  adds lemmas about the `String` operations `drop`, `dropEnd`, `take`, `takeEnd`.

- [#13106](https://github.com/leanprover/lean4/pull/13106)
  verifies `String.Pos.nextn` by providing the low-level API `nextn_zero`/`nextn_add_one` as well as a `Splits` lemma.

- [#13105](https://github.com/leanprover/lean4/pull/13105)
  proves `theorem front?_eq {s : String} : s.front? = s.toList.head?` and related results.

- [#13098](https://github.com/leanprover/lean4/pull/13098)
  generalizes some theorems about `Nat.ofDigitChars` which were needlessly restricted to base 10.

- [#13096](https://github.com/leanprover/lean4/pull/13096)
  show the trivial result that given `c : l.Cursor`, we have that `c.pos ≤ l.length`.

- [#13092](https://github.com/leanprover/lean4/pull/13092)
  fixes an issue where `Std.Iter.joinString` had an extra universe parameter because of an `IteratorLoop` instance which was actually unnecessary.

- [#13091](https://github.com/leanprover/lean4/pull/13091)
  adds the function `String.Slice.join` and adds lemmas about `String.join` and `String.Slice.join`.

- [#13090](https://github.com/leanprover/lean4/pull/13090)
  adds the single lemma `Char.toNat_mk`.

- [#13061](https://github.com/leanprover/lean4/pull/13061)
  adds lemmas about `BEq` on `List String.Slice`.

- [#13058](https://github.com/leanprover/lean4/pull/13058)
  adds `EquivBEq` and `LawfulHashable` instances to `String.Slice`.

- [#13057](https://github.com/leanprover/lean4/pull/13057)
  adds some variants of existing lemmas about `String.toNat?` and friends.

- [#13056](https://github.com/leanprover/lean4/pull/13056)
  adds the functions `Std.Iter.joinString` and `Std.Iter.intercalateString`.

- [#13054](https://github.com/leanprover/lean4/pull/13054)
  adds the simproc String.reduceToSingleton`, which is disabled by default and turns `"c"` into `String.singleton 'c'`.

- [#13003](https://github.com/leanprover/lean4/pull/13003)
  reorganizes the instances `ToString Int` and `Repr Int` so that they both point at a common definition `Int.repr` (the same setup is used for `Nat`). It then verifies the functions `Int.repr`, `String.isInt` and `String.toInt`.

- [#12999](https://github.com/leanprover/lean4/pull/12999)
  verifies the `String.dropPrefix?` function for our various patterns.

- [#12469](https://github.com/leanprover/lean4/pull/12469)
  adds the `Inhabited` instance for `Thunk`.

- [#12128](https://github.com/leanprover/lean4/pull/12128)
  introduces the `URI` data type.

- [#12990](https://github.com/leanprover/lean4/pull/12990)
  verifies the `String.startsWith` and `String.skipPrefix?` functions for our various pattern types.

- [#12988](https://github.com/leanprover/lean4/pull/12988)
  introduces the functions `String.Slice.skipPrefix?`, `String.Slice.Pos.skip?`, `String.Slice.skipPrefixWhile`, `String.Slice.Pos.skipWhile` and redefines `String.Slice.takeWhile` and `String.Slice.dropWhile` to use these new functions.

- [#12984](https://github.com/leanprover/lean4/pull/12984)
  renames the function `ForwardPattern.dropPrefix?` to `ForwardPattern.skipPrefix`?

- [#12828](https://github.com/leanprover/lean4/pull/12828)
  redefines the `String.isNat` function to use less state and perform short-circuiting. It then verifies the `String.isNat` and `String.toNat?` functions.

- [#12980](https://github.com/leanprover/lean4/pull/12980)
  adds theorems about `Char`, `Nat` and `List`.

- [#12977](https://github.com/leanprover/lean4/pull/12977)
  removes most of the `simp` annotations added in #12945, to mitigate the performance impact. The lemmas remain.

- [#12966](https://github.com/leanprover/lean4/pull/12966)
  adds simp lemmas that simplify `n.digitChar = '0'` to `n = 0` and a simproc that simplifies `n.digitChar = '!'` to `False`.

- [#12924](https://github.com/leanprover/lean4/pull/12924)
  fixes a regression introduced in Lean 4.29.0-rc2 where `simp` no longer simplifies inside type class instance arguments due to the `backward.isDefEq.respectTransparency` change. This breaks proofs where a term like `(a :: l).length` appears both in the main expression and inside implicit instance arguments (e.g., determining a `BitVec` width).

- [#12950](https://github.com/leanprover/lean4/pull/12950)
  adds simp lemmas equating kernel-friendly function names with their operator notation equivalents: `Nat.land_eq`, `Nat.lor_eq`, `Nat.xor_eq`, `Nat.shiftLeft_eq'`, `Nat.shiftRight_eq'`, and `Bool.rec_eq`. These are useful when proofs involve reflection and need to simplify kernel-reduced terms back to operator notation.

- [#12955](https://github.com/leanprover/lean4/pull/12955)
  fixes the windows build with signal handlers.

- [#12945](https://github.com/leanprover/lean4/pull/12945)
  adds a few `forall` lemmas to the `simp` set.

- [#12900](https://github.com/leanprover/lean4/pull/12900)
  fixes some process signals that were incorrectly numbered.

- [#12127](https://github.com/leanprover/lean4/pull/12127)
  introduces the `Headers` data type, that provides a good and convenient abstraction for parsing, querying, and encoding HTTP/1.1 headers.

- [#12936](https://github.com/leanprover/lean4/pull/12936)
  fixes `Id.run_seqLeft` and `Id.run_seqRight` to apply when the two monad results are different.

- [#12909](https://github.com/leanprover/lean4/pull/12909)
  fixes the typo in `Int.sq_nonnneg`.

- [#12919](https://github.com/leanprover/lean4/pull/12919)
  fixes the `HSub PlainTime Duration` instance, which had its operands reversed: it computed `duration - time` instead of `time - duration`. For example, subtracting 2 minutes from `time("13:02:01")` would give `time("10:57:59")` rather than the expected `time("13:00:01")`. We also noticed that `HSub PlainDateTime Millisecond.Offset` is similarly affected.

- [#12885](https://github.com/leanprover/lean4/pull/12885)
  shifts some material in `Init` to make sure that the `ToString` instances of basic types don't rely on `String.Internal.append`.

- [#12857](https://github.com/leanprover/lean4/pull/12857)
  removes the use of `native_decide` in the HTTP library and adds proofs to remove the `panic!`.

- [#12852](https://github.com/leanprover/lean4/pull/12852)
  implements an iterator for `PersistentHashMap`.

- [#12844](https://github.com/leanprover/lean4/pull/12844)
  provides the iterator combinator `append` that permits the concatenation of two iterators.

- [#12481](https://github.com/leanprover/lean4/pull/12481)
  provides lemmas about `toArray` and `keysArray` on tree maps and tree sets that are analogous to the existing `toList` and `keys` lemmas.

- [#12385](https://github.com/leanprover/lean4/pull/12385)
  implements a merge sort algorithm on arrays. It has been measured to be about twice as fast as `List.mergeSort` for large arrays with random elements, but for small or almost sorted ones, the list implementation is faster. Compared to `Array.qsort`, it is stable and has O(n log n) worst-case cost. Note: There is still a lot of potential for optimization. The current implementation allocates O(n log n) arrays, one per recursive call.

- [#12821](https://github.com/leanprover/lean4/pull/12821)
  removes the `@[grind →]` attribute from `List.getElem_of_getElem?` and `Vector.getElem_of_getElem?`. These were identified as problematic in Mathlib by https://github.com/leanprover/lean4/issues/12805.

- [#12807](https://github.com/leanprover/lean4/pull/12807)
  makes the lemmas about `String.find?` and `String.contains` that were added recently into public declarations.

- [#12757](https://github.com/leanprover/lean4/pull/12757)
  marks `Id.run` as `[implicit_reducible]` to ensure that `Id.instMonadLiftTOfPure` and `instMonadLiftT Id` are definitionally equal when using `.implicitReducible` transparency setting.

- [#12793](https://github.com/leanprover/lean4/pull/12793)
  takes a more principled approach in deriving `String` pattern lemmas by reducing to simpler cases similar to how the instances are defined.

- [#12126](https://github.com/leanprover/lean4/pull/12126)
  introduces the core HTTP data types: `Request`, `Response`, `Status`, `Version`, and `Method`. Currently, URIs are represented as `String` and headers as `HashMap String (Array String)`. These are placeholders, future PRs will replace them with strict implementations.

- [#12783](https://github.com/leanprover/lean4/pull/12783)
  adds user-facing API lemmas for `s.contains t`, where `s` and `t` are both a string or a slice.

- [#12760](https://github.com/leanprover/lean4/pull/12760)
  adds general projection lemmas for `ExceptConds` conjunction:

  - `ExceptConds.and_elim_left`: `(x ∧ₑ y) ⊢ₑ x`
  - `ExceptConds.and_elim_right`: `(x ∧ₑ y) ⊢ₑ y`

- [#12779](https://github.com/leanprover/lean4/pull/12779)
  provides a `ForwardPatternModel` for string patterns and deduces theorems and lawfulness instances from the corresponding results for slice patterns.

- [#12777](https://github.com/leanprover/lean4/pull/12777)
  adds lemmas about `String.find?` and `String.contains`.

- [#12771](https://github.com/leanprover/lean4/pull/12771)
  generalizes `String.Slice.Pos.cast`, which turns an `s.Pos` into a `t.Pos`, to no longer require `s = t`, but merely `s.copy = t.copy`.

- [#12433](https://github.com/leanprover/lean4/pull/12433)
  adds a bitblasting circuit for `BitVec.cpop` with a divide-and-conquer for a parallel-prefix-sum.

- [#12435](https://github.com/leanprover/lean4/pull/12435)
  provides injectivity lemmas for `List.getElem`, `List.getElem?`, `List.getElem!` and `List.getD` as well as for `Option`. Note: This introduces a breaking change, changing the signature of `Option.getElem?_inj`.

- [#12725](https://github.com/leanprover/lean4/pull/12725)
  shows that lawful searchers split the empty string to `[""]`.

- [#12723](https://github.com/leanprover/lean4/pull/12723)
  relates `String.split` to `List.splitOn` and `List.splitOnP`, provided that we are splitting by a character or character predicate.

- [#12710](https://github.com/leanprover/lean4/pull/12710)
  deprecated the handful of names in core involving the component `cons₂` in favor of `cons_cons`.

- [#12709](https://github.com/leanprover/lean4/pull/12709)
  adds various `String` lemmas that will be useful for deriving high-level theorems about `String.split`.

- [#12708](https://github.com/leanprover/lean4/pull/12708)
  changes the order of implicit parameters `α` and `ps` such that `α` consistently comes before `ps` in `PostCond.noThrow`, `PostCond.mayThrow`, `PostCond.entails`, `PostCond.and`, `PostCond.imp` and theorems.

- [#12707](https://github.com/leanprover/lean4/pull/12707)
  adds lemmas about `String.intercalate` and `String.Slice.intercalate`.

- [#12706](https://github.com/leanprover/lean4/pull/12706)
  adds a dsimproc which evaluates `String.singleton ' '` to `" "`.

- [#12697](https://github.com/leanprover/lean4/pull/12697)
  adds two new unfolding theorems to Std.Do: `PostCond.entails.mk` and `Triple.of_entails_wp`.

- [#12702](https://github.com/leanprover/lean4/pull/12702)
  upstreams `List.splitOn` and `List.splitOnP` from Batteries/mathlib.

- [#12405](https://github.com/leanprover/lean4/pull/12405)
  adds several useful lemmas for `List`, `Array` and `Vector` whenever they were missing, improving API coverage and consistency among these types.
  - `size_singleton`/`sum_singleton`/`sum_push`
  - `foldlM_toArray`/`foldlM_toList`/`foldl_toArray`/`foldl_toList`/`foldrM_toArray`/`foldrM_toList`/`foldr_toList`
  - `toArray_toList`
  - `foldl_eq_apply_foldr`/`foldr_eq_apply_foldl`, `foldr_eq_foldl`: relates `foldl` and `foldr` for associative operations with identity
  - `sum_eq_foldl`: relates sum to `foldl` for associative operations with identity
  - `Perm.pairwise_iff`/`Perm.pairwise`: pairwise properties are preserved under permutations of arrays

- [#12430](https://github.com/leanprover/lean4/pull/12430)
  provides `WellFounded.partialExtrinsicFix`, which makes it possible to implement and verify partially terminating functions, safely building on top of the seemingly less general `extrinsicFix` (which is now called `totalExtrinsicFix`). A proof of termination is only necessary in order to formally verify the behavior of `partialExtrinsicFix`.

- [#12685](https://github.com/leanprover/lean4/pull/12685)
  adds some missing material about transferring positions across the subslicing operations `slice`, `sliceFrom`, `sliceTo`.

- [#12678](https://github.com/leanprover/lean4/pull/12678)
  marks `List.flatten`, `List.flatMap`, `List.intercalate` as noncomputable to ensure that their `csimp` variants are used everywhere.

- [#12668](https://github.com/leanprover/lean4/pull/12668)
  adds lemmas about string positions and patterns that will be useful for providing high-level API lemmas for `String.split` and friends.

```

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Tactics"
%%%

```markdown

- [#13177](https://github.com/leanprover/lean4/pull/13177)
  adds `@[expose]` to `Lean.Grind.abstractFn` and
  `Lean.Grind.simpMatchDiscrsOnly` so that the kernel can unfold them when
  type-checking `grind`-produced proofs inside `module` blocks. Other
  similar gadgets (`nestedDecidable`, `PreMatchCond`, `alreadyNorm`) were
  already exposed; these two were simply missed.

- [#13166](https://github.com/leanprover/lean4/pull/13166)
  replaces the `grind` canonicalizer with a new type-directed normalizer (`Sym.canon`) that goes inside binders and applies targeted reductions in type positions, eliminating the O(n^2) `isDefEq`-based approach.

- [#13149](https://github.com/leanprover/lean4/pull/13149)
  simplifies the `grind` canonicalizer by removing dead state and unnecessary
  complexity, and fixes two bugs discovered during the cleanup.

- [#13080](https://github.com/leanprover/lean4/pull/13080)
  adds `SymExtension`, a typed extensible state mechanism for `SymM`,
  following the same pattern as `Grind.SolverExtension`. Extensions are
  registered at initialization time via `registerSymExtension` and provide
  typed `getState`/`modifyState` accessors. Extension state persists across
  `simp` invocations within a `sym =>` block and is re-initialized on each
  `SymM.run`.

- [#13048](https://github.com/leanprover/lean4/pull/13048)
  adds two new `sym_simproc` DSL primitives and helper grind-mode
  tactics.

- [#13046](https://github.com/leanprover/lean4/pull/13046)
  prevents `Sym.simp` from looping on permutation theorems like
  `∀ x y, x + y = y + x`.

- [#13042](https://github.com/leanprover/lean4/pull/13042)
  extends the `simp` tactic in `sym =>` mode to support local
  hypotheses in the extra theorem list.

- [#13041](https://github.com/leanprover/lean4/pull/13041)
  extends `mkTheoremFromDecl` and `mkTheoremFromExpr` to handle
  theorems whose conclusion is not an equality, enabling `Sym.simp` to use
  a broader class of lemmas as rewrite rules.

- [#13040](https://github.com/leanprover/lean4/pull/13040)
  adds validation to the `register_sym_simp` command:

  - Reject duplicate variant names
  - Validate `pre`/`post` syntax by elaborating them via `elabSymSimproc`
    in a minimal `GrindTacticM` context, catching unknown theorem names
    and unknown theorem set references at registration time

- [#13039](https://github.com/leanprover/lean4/pull/13039)
  adds the `simp` tactic to the `sym =>` interactive mode, completing
  the `Sym.simp` interactive infrastructure.

- [#13034](https://github.com/leanprover/lean4/pull/13034)
  adds the `register_sym_simp` command for declaring named `Sym.simp`
  variants with `pre`/`post` simproc chains and optional config overrides.

- [#13033](https://github.com/leanprover/lean4/pull/13033)
  adds `r == e` guards to the `norm_eq_var` and `norm_eq_var_const` branches of `Int.Linear.simpEq?`. Without these guards, `simpEq?` returns a non-trivial proof for already-normalized equations like `x = -1`, causing `exists_prop_congr` to fire repeatedly and build an infinitely growing term.

- [#13032](https://github.com/leanprover/lean4/pull/13032)
  fixes #12842 where `grind` exhausts memory on goals involving high-degree polynomials such as `(x + y)^2 = x^128 + y^2` over `Fin 2`.

- [#13031](https://github.com/leanprover/lean4/pull/13031)
  adds the built-in elaborators for the `sym_simproc` and `sym_discharger` DSL syntax categories introduced in #13026.

- [#13027](https://github.com/leanprover/lean4/pull/13027)
  fixes a nondeterministic crash in `grind` caused by a `BEq`/`Hashable` invariant
  violation in the congruence table. `congrHash` uses each expression's own `funCC` flag to
  compute its hash (one-level decomposition for `funCC = true`, full recursive decomposition
  for `funCC = false`), but `isCongruent` only checked the stored expression's flag. When two
  expressions with mismatched `funCC` flags accidentally hash-collided (via pointer-based
  `ptrAddrUnsafe` hashing), `isCongruent` could declare them congruent despite different
  argument counts, leading to an assertion failure in `mkCongrProof`.

- [#13026](https://github.com/leanprover/lean4/pull/13026)
  adds the infrastructure for simproc and discharger DSLs used to specify `pre`/`post` simproc chains and conditional rewrite dischargers in `Sym.simp` variants.

- [#13024](https://github.com/leanprover/lean4/pull/13024)
  fixes an issue where `grind` could prove each conjunct individually but failed on the conjunction. The root cause: `solverAction`'s `.propagated` path calls `processNewFacts` which drains the `newFacts` queue, but the resulting propagation cascade (congruence closure, or-propagation, `propagateForallPropDown`) can call `addNewRawFact`, enqueuing to the separate `newRawFacts` queue. These raw facts were never drained.

- [#13018](https://github.com/leanprover/lean4/pull/13018)
  adds named theorem sets for `Sym.simp` with associated attributes, following the same pattern as `Meta.simp`'s `register_simp_attr`.

- [#12996](https://github.com/leanprover/lean4/pull/12996)
  adds per-result `contextDependent` tracking to `Sym.Simp.Result` and splits the simplifier cache into persistent (context-independent) and transient (context-dependent, cleared on binder entry). This replaces the coarse `wellBehavedMethods` flag.

- [#12970](https://github.com/leanprover/lean4/pull/12970)
  adds a `sym =>` tactic that enters an interactive symbolic simulation
  mode built on `grind`. Unlike `grind =>`, it does not eagerly introduce
  hypotheses or apply by-contradiction, giving users explicit control over
  `intro`, `apply`, and `internalize` steps.

- [#12944](https://github.com/leanprover/lean4/pull/12944)
  changes the interaction between `@[cbv_opaque]` and `@[cbv_eval]`
  attributes in the `cbv` tactic. Previously, `@[cbv_opaque]` completely blocked
  all reduction including `@[cbv_eval]` rewrite rules. Now, `@[cbv_eval]` rules
  can fire on `@[cbv_opaque]` constants, allowing users to provide custom rewrite
  rules without exposing the full definition. Equation theorems, unfold theorems,
  and kernel reduction remain suppressed for opaque constants.

- [#12923](https://github.com/leanprover/lean4/pull/12923)
  fixes a bug where `max u v` and `max v u` fail to match in SymM's pattern matching. Both `processLevel` (Phase 1) and `isLevelDefEqS` (Phase 2) treated `max` positionally, so `max u v ≠ max v u` structurally even though they are semantically equal.

- [#12920](https://github.com/leanprover/lean4/pull/12920)
  adds eta reduction to the sym discrimination tree lookup functions (`getMatch`, `getMatchWithExtra`, `getMatchLoop`). Without this, expressions like `StateM Nat` that unfold to eta-expanded forms `(fun α => StateT Nat Id α)` fail to match discrimination tree entries for the eta-reduced form `(StateT Nat Id)`.

- [#12887](https://github.com/leanprover/lean4/pull/12887)
  optimizes the `String.reduceEq`, `String.reduceNe`, and `Sym.Simp` string equality simprocs to produce kernel-efficient proofs. Previously, these used `String.decEq` which forced the kernel to run UTF-8 encoding/decoding and byte array comparison, causing 86+ kernel unfoldings on short strings.

- [#12908](https://github.com/leanprover/lean4/pull/12908)
  makes `@[cbv_opaque]` unconditionally block all evaluation of a constant
  by `cbv`, including `@[cbv_eval]` rewrite rules. Previously, `@[cbv_eval]` could
  bypass `@[cbv_opaque]`, and for bare constants (not applications), `isOpaqueConst`
  could fall through to `handleConst` which would unfold the definition body.

- [#12888](https://github.com/leanprover/lean4/pull/12888)
  adds `String`-specific simprocs to `cbv` tactic.

- [#12882](https://github.com/leanprover/lean4/pull/12882)
  adds an `@[mvcgen_witness_type]` tag attribute, analogous to `@[mvcgen_invariant_type]`, that allows users to mark types as witness types. Goals whose type is an application of a tagged type are classified as witnesses rather than verification conditions, and appear in a new `witnesses` section in the `mvcgen` tactic syntax (before `invariants`).

- [#12875](https://github.com/leanprover/lean4/pull/12875)
  adds `cbv` simprocs for getting elements out of arrays.

- [#12597](https://github.com/leanprover/lean4/pull/12597)
  adds a `cbv_simproc` system for the `cbv` tactic, mirroring simp's `simproc` infrastructure but tailored to cbv's three-phase pipeline (`↓` pre, `cbv_eval` eval, `↑` post). User-defined simplification procedures are indexed by discrimination tree patterns and dispatched during cbv normalization.

- [#12851](https://github.com/leanprover/lean4/pull/12851)
  add support for erasing `@[cbv_eval]` annotations using `attribute [-cbv_eval]`, mirroring the existing `@[-simp]` mechanism for simp lemmas.

- [#12805](https://github.com/leanprover/lean4/pull/12805)
  adds a `set_option grind.unusedLemmaThreshold` that, when set to N > 0
  and `grind` succeeds, reports E-matching lemmas that were activated at least N
  times but do not appear in the final proof term. This helps identify `@[grind]`
  annotations that fire frequently without contributing to proofs.

- [#12563](https://github.com/leanprover/lean4/pull/12563)
  makes the `omit`, `unusedSectionVars` and `loopingSimpArgs` linters respect the `linter.all` option:
  when `linter.all` is set to false (and the respective linter option is unset), the linter should not report errors.

- [#12816](https://github.com/leanprover/lean4/pull/12816)
  solves three distinct issues with the handling of `ite`/`dite`,`decide`.

- [#12788](https://github.com/leanprover/lean4/pull/12788)
  adds a `set_option cbv.maxSteps N` option that controls the maximum
  number of simplification steps the `cbv` tactic performs. Previously the limit
  was hardcoded to the `Sym.Simp.Config` default of 100,000 with no way for
  users to override it. The option is threaded through `cbvCore`, `cbvEntry`,
  `cbvGoal`, and `cbvDecideGoal`.

- [#12782](https://github.com/leanprover/lean4/pull/12782)
  adds high priority to instances for `OfSemiring.Q` in the grind ring envelope. When Mathlib is imported, instance synthesis for types like `OfSemiring.Q Nat` becomes very expensive because the solver explores many irrelevant paths before finding the correct instances. By marking these instances as high priority and adding shortcut instances for basic operations (`Add`, `Sub`, `Mul`, `Neg`, `OfNat`, `NatCast`, `IntCast`, `HPow`), instance synthesis resolves quickly.

- [#12773](https://github.com/leanprover/lean4/pull/12773)
  adds `at` location syntax to the `cbv` tactic, matching the interface of `simp at`. Previously `cbv` could only reduce the goal target; now it supports `cbv at h`, `cbv at h |-`, and `cbv at *`.

- [#12766](https://github.com/leanprover/lean4/pull/12766)
  adds a dedicated cbv simproc for `Decidable.decide` that directly matches on `isTrue`/`isFalse` instances, producing simpler proof terms and avoiding unnecessary unfolding through `Decidable.rec`.

- [#12677](https://github.com/leanprover/lean4/pull/12677)
  changes the  approach in `simpIteCbv` and `simpDIteCbv`, by replacing call to `Decidable.decide`
  with reducing and direct pattern matching on the `Decidable` instance for `isTrue`/`isFalse`. This produces simpler proof terms.

- [#12763](https://github.com/leanprover/lean4/pull/12763)
  adds pre-pass simprocs `simpOr` and `simpAnd` to the `cbv` tactic that evaluate only the left argument of `Or`/`And` first, short-circuiting when the result is determined without evaluating the right side. Previously, `cbv` processed `Or`/`And` via congruence, which always evaluated both arguments. For expressions like `decide (m < n ∨ expensive)`, when `m < n` is true, the expensive right side is now skipped entirely.

- [#12607](https://github.com/leanprover/lean4/pull/12607)
  fixes an issue where `withLocation` wasn't saving the info context, which meant that tactics that use `at *` location syntax and do term elaboration would save infotrees but revert the metacontext, leading to Infoview messages like "Error updating: Error fetching goals: Rpc error: InternalError: unknown metavariable" if the tactic failed at some locations but succeeded at others.

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Compiler"
%%%

```markdown

- [#13270](https://github.com/leanprover/lean4/pull/13270)
  adds `Runtime.hold`, which ensures its argument remains alive until the callsite by holding a reference to it. This can be useful for unsafe code (such as an FFI) that relies on a Lean object not being freed until after some point in the program.

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  fixes a heap buffer overflow in `lean_io_prim_handle_read` that was triggered through an
  integer overflow in the size computation of an allocation. In addition it places several checked
  arithmetic operations on all relevant allocation paths to have potential future overflows be turned
  into crashes instead. The offending code now throws an out of memory error instead.

- [#13152](https://github.com/leanprover/lean4/pull/13152)
  informs the RC optimizer that tagged values can also be considered as "borrowed" in the sense that we do not need to consider them as owned values for the borrow analysis (they do of course not have an allocation they actually borrow from).

- [#13136](https://github.com/leanprover/lean4/pull/13136)
  introduces coalescing of RC operations to the RC optimizer. Whenever we perform multiple `inc`s for a single value within one basic block it is legal to instead perform all of these `inc`s at once at the first `inc` side. This is the case because the value will stay alive until at least the last `inc` and was thus never observable with `RC=1`. Hence, this change of `inc` location never destroys reuse opportunities.

- [#13147](https://github.com/leanprover/lean4/pull/13147)
  fixes theoretical leaks in the handling of `Array.get!Internal` in the code generator.
  Currently, the code generator assumes that the value returned by `get!Internal` is derived from the
  `Array` argument. However, this does not generally hold up as we might also return the `Inhabited`
  value in case of an out of bounds access (recall that we continue execution after panics by
  default). This means that we sometimes convert an `Array.get!Internal` to
  `Array.get!InternalBorrowed` when we are not allowed to do so because in the panic case the
  `Inhabited` instance can be returned and if it is an owned value it is going to leak.

- [#13138](https://github.com/leanprover/lean4/pull/13138)
  introduces the `weak_specialize` attribute. Unlike the `nospecialize` attribute it does not
  block specialization for parameters marked with this type completely. Instead, `weak_specialize`
  parameters are only specialized for if another parameter provokes specialization. If no such
  parameter exists, they are treated like `nospecialize`.

- [#13118](https://github.com/leanprover/lean4/pull/13118)
  fixes an incompatibility of `--load-dynlib` with the module system.

- [#13116](https://github.com/leanprover/lean4/pull/13116)
  ensures that reads from constants count as borrows in the eyes of the borrow inference analysis. This reduces RC pressure in the presence of constant reads.

- [#13094](https://github.com/leanprover/lean4/pull/13094)
  marks the `Inhabited` arguments of all functions in core marked as `extern` as borrowed
  (panicking array accessors and `panic!` itself). This in turn causes a transitive effect throughout
  the codebase and promotes most, if not all, `Inhabited` arguments to functions to borrowed.

- [#13097](https://github.com/leanprover/lean4/pull/13097)
  makes the compiler traces contain more information about the kind of `inc`/`dec` that are
  being conducted (`persistent`, `checked` etc.)

- [#13066](https://github.com/leanprover/lean4/pull/13066)
  changes the behavior of forward and backward projection propagation in the context of user defined borrows. The reason to have them be "forced" override (i.e. override user annotations as well) was that a user annotated borrowed value can potentially flow into a reset-reuse transitively through a projection and must thus have accurate reference count. The reasons that this is no longer necessary are:
  1. Forward never had to be forced anyways, it can only affect the `z` in `let z := oproj x i` which can't be annotated by a user
  2. Backward is no longer necessary as the forward propagator for user annotations prevents the reset-reuse insertion from working with values that have user defined borrow annotations entirely.

- [#13064](https://github.com/leanprover/lean4/pull/13064)
  informs the borrow inference that if an `Array` is borrowed and we index into it, the value we obtain is effectively a borrowed value as well. This helps improve the ABI of operations that recurse on linked structures containing arrays such as tries or persistent hash maps.

- [#12942](https://github.com/leanprover/lean4/pull/12942)
  marks the context argument of `ReaderT` as borrowed, causing a wide spread of useful borrow annotations throughout the entire meta stack which reduces RC pressure. This introduces a crucial new behavior: When modifying `ReaderT` context, e.g. through `withReader` this will almost always cause an allocation. Given that the `ReaderT` context is frequently used in a non-linear fashion anyways we think this is an acceptable behavior.

- [#13052](https://github.com/leanprover/lean4/pull/13052)
  fixes a bug in the borrow inference in connection with `export` annotations.

- [#13017](https://github.com/leanprover/lean4/pull/13017)
  ensures that when a declaration is marked with `@[export]`, the compiler throws an error if
  any of its arguments are marked as borrowed.

- [#12971](https://github.com/leanprover/lean4/pull/12971)
  increases Lean's default stack size, including for the main thread of Lean executables, to 1GB.

- [#12830](https://github.com/leanprover/lean4/pull/12830)
  enables support for respecting user provided borrow annotations. This allows user to mark arguments of their definitions or local functions with `(x : @&Ty)` and have the borrow inference try its best to preserve this annotation, thus potentially reducing RC pressure. Note that in some cases this might not be possible. For example, the compiler prioritizes preserving tail calls over preserving borrow annotations. A precise reasoning of why the compiler chose to make its inference decisions can be obtained with `trace.Compiler.inferBorrow`.

- [#12952](https://github.com/leanprover/lean4/pull/12952)
  ensures that when a function is marked `export` its borrow annotations (if present) are always ignored.

- [#12930](https://github.com/leanprover/lean4/pull/12930)
  places `set_option compiler.ignoreBorrowAnnotation true in` on to all `export`/`extern`
  pairs. This is necessary because `export` forces all arguments to be passed as owned while `extern`
  respects borrow annotations. The current approach to the `export`/`extern` trick was always broken
  but never surfaced. However, with upcoming changes many `export`/`extern` pairs are going to be
  affected by borrow annotations and would've broken without this.

- [#12886](https://github.com/leanprover/lean4/pull/12886)
  adds support for ignoring user defined borrow annotations. This can be useful when defining
  `extern`/`export` pairs as the `extern` might be infected by borrow annotations while in `export`
  they are already ignored.

- [#12781](https://github.com/leanprover/lean4/pull/12781)
  ports the C emission pass from IR to LCNF, marking the last step of the IR/LCNF conversion and thus enabling end-to-end code generation through the new compilation infrastructure.

- [#12850](https://github.com/leanprover/lean4/pull/12850)
  optimizes the handling of `match_same_ctor.het` to make it emit nice match trees as opposed to unoptimized CPS style code.

- [#12539](https://github.com/leanprover/lean4/pull/12539)
  replaces three independent name demangling implementations (Lean, C++, Python) with a single source of truth in `Lean.Compiler.NameDemangling`. The new module handles the full pipeline: prefix parsing (`l_`, `lp_`, `_init_`, `initialize_`, `lean_apply_N`, `_lean_main`), postprocessing (suffix flags, private name stripping, hygienic suffix stripping, specialization contexts), backtrace line parsing, and C exports via `@[export]`.

- [#12810](https://github.com/leanprover/lean4/pull/12810)
  adds tracing to the borrow inference to explain to the user why it got to its conclusions.

- [#12796](https://github.com/leanprover/lean4/pull/12796)
  fixes a deadlock when `uv_tcp_accept` is under contention from multiple threads.

- [#12795](https://github.com/leanprover/lean4/pull/12795)
  fixes a memory leak that gets triggered on the error path of `lean_uv_dns_get_name`

- [#12790](https://github.com/leanprover/lean4/pull/12790)
  makes the compiler removes arguments to join points that are void, avoiding a bunch of dead
  stores in the bytecode and the initial C (though LLVM was surely able to optimize these away further
  down the line already).

- [#12759](https://github.com/leanprover/lean4/pull/12759)
  replaces the `isImplicitReducible` check with `Meta.isInstance` in the `shouldInline` function within `inlineCandidate?`.

- [#12724](https://github.com/leanprover/lean4/pull/12724)
  implements support for extracting simple ground array literals into statically initialized data.

- [#12727](https://github.com/leanprover/lean4/pull/12727)
  implements simple ground literal extraction for boxed scalar values.

- [#12715](https://github.com/leanprover/lean4/pull/12715)
  ensures the compiler extracts `Array`/`ByteArray`/`FloatArray` literals as one big closed term to avoid quadratic overhead at closed term initialization time.

- [#12705](https://github.com/leanprover/lean4/pull/12705)
  ports the simple ground expression extraction pass from IR to LCNF.

- [#12665](https://github.com/leanprover/lean4/pull/12665)
  ports the expand reset/reuse pass from IR to LCNF. In addition it prevents exponential code generation unlike the old one. This results in a ~15% decrease in binary size and slight speedups across the board.

- [#12687](https://github.com/leanprover/lean4/pull/12687)
  implements the LCNF instructions required for the expand reset reuse pass.

- [#12663](https://github.com/leanprover/lean4/pull/12663)
  avoids false-positive error messages on specialization restrictions under the module system when the declaration is explicitly marked as not specializable. It could also provide some minor public size and rebuild savings.

```

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Pretty-Printing"
%%%

````markdown

- [#10384](https://github.com/leanprover/lean4/pull/10384)
  当 `pp.unicode` 为 false 时，使用 ASCII 版本使 `∨`、`∧`、`≤` 和 `≥` 等符号打印得漂亮。

- [#12745](https://github.com/leanprover/lean4/pull/12745)
  当选项设置为 `false` 时，修复 `pp.fvars.anonymous` 将松散的自由变量显示为 `_fvar._` 而不是 `_`。这是 https://github.com/leanprover/lean4/pull/12688 中的预期行为，但修复是在本地提交的，并且在 PR 合并之前没有推送。

- [#12688](https://github.com/leanprover/lean4/pull/12688)
  添加一个 `pp.fvars.anonymous` 选项（默认 `true`）来控制松散自由变量（fvars 不在本地上下文中）的显示。

- [#12654](https://github.com/leanprover/lean4/pull/12654)
  修复了私人姓名打印美观的两个方面。
  1. 名称未解析。现在私有名称不是特殊大小写的：私有前缀被剥离并添加 `_root_` 前缀，然后它尝试解析结果的所有后缀。这足以处理新模块系统中导入的私有名称。 （此外，未解析现在考虑了宏观范围。）
  2. 详细阐述。不可访问的私有名称使用确定性算法将私有前缀转换为宏范围。其效果是，在同一精心设计的表达式中多次出现的同一私有名称现在每次都具有相同的 `✝` 后缀。它曾经在每次出现时使用新的宏范围。

- [#12606](https://github.com/leanprover/lean4/pull/12606)
  添加漂亮打印机选项 `pp.mdata`，这会导致漂亮打印机使用存在的任何元数据来注释术语。例如，
  ```lean
  set_option pp.mdata true
  /-- info: [mdata noindex:true] 2 : Nat -/
  #guard_msgs in #check no_index 2
  ```

````

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Documentation"
%%%

```markdown

- [#13115](https://github.com/leanprover/lean4/pull/13115)
  updates the `inferInstanceAs` docstring to reflect current behavior: it requires an
  expected type from context and should not be used as a simple `inferInstance` synonym. The
  old example (`#check inferInstanceAs (Inhabited Nat)`) no longer works, so it's replaced
  with one demonstrating the intended transport use case.

- [#13065](https://github.com/leanprover/lean4/pull/13065)
  rewrites the docstring on `Lean.ReducibilityHints` to accurately describe the
  kernel's lazy delta reduction strategy: which side gets unfolded when comparing two
  definitions, how definitional height is computed, and how hints relate to the
  `@[reducible]`/`@[irreducible]` elaborator attributes.

- [#12959](https://github.com/leanprover/lean4/pull/12959)
  fixes a series of errors in docstrings.

```

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Server"
%%%

```markdown

- [#12948](https://github.com/leanprover/lean4/pull/12948)
  moves `RequestCancellationToken` from `IO.Ref` to `IO.CancelToken`.

- [#12905](https://github.com/leanprover/lean4/pull/12905)
  adjusts the JSON encoding of RPC references from `{"p": "n"}` to `{"__rpcref": "n"}`. Existing clients will continue to work unchanged, but should eventually move to the new format by advertising the `rpcWireFormat` client capability.

```

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Lake"
%%%

```markdown

- [#13683](https://github.com/leanprover/lean4/pull/13683)
  moves the compiled Lake configurations (e.g., `lakefile.olean`) from the package's `.lake/config` directory to the workspace's `.lake/config`. This removes a potential source contention between workspaces sharing a dependency.

- [#13600](https://github.com/leanprover/lean4/pull/13600)
  fixes a Lake issue where the IR for a `meta import`'s transitive imports was not included in the import artifacts Lake provided to Lean (e.g., via `--setup`). When using the Lake artifact cache, this could produce "missing data file" errors due to absent IR.

- [#13164](https://github.com/leanprover/lean4/pull/13164)
  changes `lake cache get` to fetch artifact cloud storage URLs from Reservoir in a single bulk POST request rather than relying on per-artifact HTTP redirects. When downloading many artifacts, the redirect-based approach sends one request per artifact to the Reservoir web host (Netlify), which can be slow and risks hitting rate limits. The bulk endpoint returns all URLs at once, so curl only talks to the CDN after that.

- [#13151](https://github.com/leanprover/lean4/pull/13151)
  changes `Lake.proc` to always log process output as `info` if the process exits with a nonzero return code. This way it behaves the same as `captureProc` on errors.

- [#13144](https://github.com/leanprover/lean4/pull/13144)
  adds three new `lake cache` subcommands for staged cache uploads: `stage`, `unstage`, and `put-staged`. These are designed to function as parallels for the commands of the same name in Mathlib's `lake exe cache`.

- [#13141](https://github.com/leanprover/lean4/pull/13141)
  changes Lake's materialization process to run remove untracked files in tracked directories (via `git clean -xf`) when updating dependency repositories. This ensures stale leftovers in the source tree are removed.

- [#13110](https://github.com/leanprover/lean4/pull/13110)
  fixes a race condition in `Cache.saveArtifact` that caused intermittent "permission denied" errors when two library facets (e.g., `static` and `static.export`) produce artifacts with the same content hash and attempt to cache them concurrently.

- [#13028](https://github.com/leanprover/lean4/pull/13028)
  adds a check that rejects Lake configurations where multiple executables share the same root module name. Previously, Lake would silently compile the root module once and link it into all executables, producing identical binaries regardless of differing `srcDir` settings.

- [#13014](https://github.com/leanprover/lean4/pull/13014)
  makes errors in `lake cache get` / `lake cache put` artifact transfers more verbose, which helps with debugging. It also fixes an issue with error reporting when downloading artifacts on demand.

- [#12993](https://github.com/leanprover/lean4/pull/12993)
  fixes a bug with Lake where caching an `ltar` produced via `lake build -o` would fail if `restoreAllArtifacts` was also `true`.

- [#12974](https://github.com/leanprover/lean4/pull/12974)
  changes `lake cache get` and `lake cache put` to transfer artifacts in parallel (using `curl --parallel`) when uploading or eagerly downloading artifacts. Transfers are still recorded one-by-one in the output -- no progress meter yet.

- [#12957](https://github.com/leanprover/lean4/pull/12957)
  fixes a build failure on macOS introduced by #12540. macOS BSD `ar` does not support the `@file` response file syntax that #12540 enabled unconditionally. On macOS, when building core (i.e., `bootsrap := true`), `recBuildStatic` now uses `libtool -static -filelist`, which handles long argument lists natively.

- [#12954](https://github.com/leanprover/lean4/pull/12954)
  changes the Lake `CacheMap` data structure to track the platform-dependence of outputs. Platform-independent packages will no longer include platform-dependent mappings in the output files produced by `lake build -o`.

- [#12540](https://github.com/leanprover/lean4/pull/12540)
  extends Lake's use of response files (`@file`) from Windows-only to all platforms, avoiding `ARG_MAX` limits when invoking `clang`/`ar` with many object files.

- [#12935](https://github.com/leanprover/lean4/pull/12935)
  adds the `fixedToolchain` Lake package configuration option. Setting this to `true` informs Lake that the package is only expected to function on a single toolchain (like Mathlib). This causes Lake's toolchain update procedure to prioritize its toolchain and avoids the need to separate input-to-output mappings for the package by toolchain version in the Lake cache.

- [#12914](https://github.com/leanprover/lean4/pull/12914)
  adds packing and unpacking of module artifacts into `.ltar` archives using `leantar`.

- [#12927](https://github.com/leanprover/lean4/pull/12927)
  changes `lake cache get` to download artifacts by default. Artifacts can be downloaded on demand with the new `--mappings-only` option (`--download-arts` is now obsolete).

- [#12837](https://github.com/leanprover/lean4/pull/12837)
  changes the default behavior of the `restoreAllArtifacts` package configuration to mirror that of the workspace. If the workspace also has it unset, the default remains the same (`false`).

- [#12835](https://github.com/leanprover/lean4/pull/12835)
  changes Lake to only emit `.nobuild` traces (introduced in #12076) if the normal trace file already exists. This fixes an issue where a  `lake build --no-build` would create the build directory and thereby prevent a cloud release fetch in a future build.

- [#12799](https://github.com/leanprover/lean4/pull/12799)
  changes Lake to use the modification times of traces (where available) for artifact modification times.

- [#12634](https://github.com/leanprover/lean4/pull/12634)
  enables Lake to download artifacts from a remote cache service on demand as part of a `lake build`. It also refactors much of the cache API to be more type safe.

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___30___0-_LPAR_2026-05-26_RPAR_--Other"
%%%

```markdown

- [#13499](https://github.com/leanprover/lean4/pull/13499)
  fixes the architecture detection for `leantar` on Linux aarch64, ensuring it is properly bundled with Lean.

- [#12865](https://github.com/leanprover/lean4/pull/12865)
  fixes a crash in release_checklist.py when a repository uses the
  `leanprover/lean4-nightly:` toolchain prefix (e.g. leansqlite). The
  `is_version_gte` function only checked for `leanprover/lean4:nightly-` but
  not `leanprover/lean4-nightly:`, causing a `ValueError: invalid literal for
  int() with base 10: 'nightly'` when trying to parse the version.

- [#12963](https://github.com/leanprover/lean4/pull/12963)
  fixes a panic in `lake shake` when applied to a header-only file without trailing newline

- [#12836](https://github.com/leanprover/lean4/pull/12836)
  adds a `lake-ci` label that enables the full Lake test suite in CI,
  avoiding the need to temporarily commit and revert changes to
  `tests/CMakeLists.txt`. The `lake-ci` label implies `release-ci` (check level
  3), so all release platforms are also tested.

- [#12822](https://github.com/leanprover/lean4/pull/12822)
  downloads a prebuilt release of `leantar` and bundles it with Lean as part of the core build.

- [#12700](https://github.com/leanprover/lean4/pull/12700)
  fixes a CMake scoping bug that made `-DLEAN_VERSION_*` overrides ineffective.

- [#12638](https://github.com/leanprover/lean4/pull/12638)
  switches four lightweight workflows from `pull_request` to
  `pull_request_target` to stop GitHub from requiring manual approval when the
  `mathlib-lean-pr-testing[bot]` app triggers label events (e.g. adding
  `builds-mathlib`). Since the bot never lands commits on master, it is
  perpetually treated as a "first-time contributor" and every `pull_request`
  event it triggers requires approval. `pull_request_target` events always run
  without approval because they execute trusted code from the base branch.

- [#12682](https://github.com/leanprover/lean4/pull/12682)
  extends `lake shake` with a flag for minimizing only a specific module

- [#12648](https://github.com/leanprover/lean4/pull/12648)
  adds the experimental `idbg e`, a new do-element (and term) syntax for live debugging between the language server and a running compiled Lean program.

```
