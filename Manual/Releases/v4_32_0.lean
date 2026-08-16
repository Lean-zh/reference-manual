/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown
import Std.Tactic.Do

open Manual
open Std.Do
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "精益4.32.0 (2026-07-13)" =>
%%%
tag := "release-v4.32.0"
file := "v4.32.0"
%%%

此版本有 102 项更改。
除了 35 项新增功能外，
以及下面列出的 20 个修复，
有 7 个重构更改，
2 文档改进，
9 项性能改进，
对测试套件的 2 项改进，
以及其他 27 项变更。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights"
%%%

Lean 4.32.0 使新的 {ref "do-notation"}`do` 阐述器成为默认值，使用 `do←` 标记扩展 `do` 表示法以进行效果转发，并带来显着的性能改进，包括 `import Mathlib` 时间减少约 10%。 Lake 的 linting 框架获得了基于选项的控制和模块级 linters，并且实验性增量编译模式支持 CLI 标志。

_此亮点部分由 Juanjo Madrigal 贡献。_

## 新 `do` Elaborator 现在是默认值
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--New--do--Elaborator-is-Now-the-Default"
%%%

[#13305](https://github.com/leanprover/lean4/pull/13305) 通过将 {option}`backward.do.legacy` 翻转为 `false`，使新的 {ref "do-notation"}`do` 精译器（在 v4.31.0 中作为实验引入）成为默认值。旧版 elaborator 仍可通过 `set_option backward.do.legacy true` 使用。 [#13912](https://github.com/leanprover/lean4/pull/13912) 和 [#13931](https://github.com/leanprover/lean4/pull/13931) 添加了重要的新功能：

### `do←` — 效果转发
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--New--do--Elaborator-is-Now-the-Default--do___--___-Effect-Forwarding"
%%%

[#13931](https://github.com/leanprover/lean4/pull/13931) 引入了 `do← body` 标记（ASCII `do<- body`），它允许普通的连续获取包装器（如 `withReader` 或 `Meta.withLocalDecl`）参与周围 `do` 块的控制流。当 `do← body` 作为 `do` 块内应用程序的最后一个参数出现时，主体的 `return`、`break`、`continue` 和 `mut` 变量重新分配将通过包装器转发到封闭块。例如，让

```lean
def withLogging [Monad m] [MonadLiftT IO m] (act : m α) : m α := do
  IO.print "log!"
  act
```

内部 `do← body` 可以改变外部变量：

```lean
def mutForward : IO Nat := do
  let mut x := 0
  withLogging (do← x := x + 1)
  return x

/--
info: log!
---
info: 1
-/
#guard_msgs in
#eval mutForward
```

它还可以触发提前返回：

```lean
def retForward : IO Nat := do
  let x <- withLogging (do← return 5)
  IO.println "unreachable"
  return x + 100

/--
info: log!
---
info: 5
-/
#guard_msgs in
#eval retForward
```

或者打破外部循环（并且 `do← body` 可以执行多次）：

```lean
def brkForward : IO Nat := do
  let mut total := 0
  for i in [1, 2, 3, 4, 5] do
    total := total + (← withLogging (do←
      if i > 3 then break
      pure i))
  return total

/--
info: log!log!log!log!
---
info: 6
-/
#guard_msgs in
#eval brkForward
```

该语法让人想起嵌套操作 `(← body)`，但与嵌套操作不同，`body` 在调用包装函数之前不会立即运行。包装函数决定何时运行 `body`，并插入代码以将 `body` 的效果转发到外部 `do` 块。

嵌套操作中的 ### 任意 `doElem`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--New--do--Elaborator-is-Now-the-Default--Arbitrary--doElem-s-in-Nested-Actions"
%%%

[#13912](https://github.com/leanprover/lean4/pull/13912) 扩展了 `nestedAction` 解析器（`do` 块内的 `←`）以接受 `←` 之后的任意 `doElem` 而不仅仅是术语。

```lean
def bumpAndUse : IO Nat := do
  let mut y := 1
  let x ← pure (← if y < 3 then
    y := y + 1
    pure y
  else
    pure 0)
  return x + y     -- x = 2 and y = 2

/-- info: 4 -/
#guard_msgs in
#eval bumpAndUse
```

`(← do …)` 或 `(← try … catch …)` 内的 `return e` 现在从 _enending_ `do` 块提前返回，而不是从嵌套操作中返回。这是一个*重大更改*：当打算从嵌套块返回值时替换为 `pure e`，或者将 `do` 块括在括号中 (`(← (do …))`)。

### 其他 `do` 精译器改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--New--do--Elaborator-is-Now-the-Default--Other--do--Elaborator-Improvements"
%%%

- [#13970](https://github.com/leanprover/lean4/pull/13970) 使错误消息中 `mut` 变量的打印名称携带悬停信息，以便信息视图显示其类型。
- [#13910](https://github.com/leanprover/lean4/pull/13910) 将 `liftMethod` 解析器重命名为 `nestedAction`，反映文档中已使用的术语。

## 性能
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Performance"
%%%

通过消除插入算法中的非线性，对 DiscrTree 插入 ([#13928](https://github.com/leanprover/lean4/pull/13928)) 的修复将 `import Mathlib` 的时间减少了约 10%。

其他值得注意的表演作品：

- [#13123](https://github.com/leanprover/lean4/pull/13123) 使任务线程池在 5 秒不活动后回收空闲工作线程，从而减少每个线程 1GB 默认堆栈大小的内存浪费。
- [#13938](https://github.com/leanprover/lean4/pull/13938) 添加了有界量词 `Decidable` 实例（`Nat.decidableBallLT`、`Nat.decidableExistsLT`、`Nat.decidableExistsLT'`）的尾递归 `@[csimp]` 运行时替换，因此运行如下示例

  ```lean (name := ex)
  #eval decide (∀ k, k < 2000000 → 0 ≤ k)
  #eval decide (∃ k, k < 50000000 ∧ k + 1 = 0)
  ```

  不再花费二次时间或溢出堆栈。
- [#13991](https://github.com/leanprover/lean4/pull/13991) 为 `USize` 操作和常见的按位操作添加常量折叠，[#13974](https://github.com/leanprover/lean4/pull/13974) 将其扩展为 `USize` 关系。 [#14044](https://github.com/leanprover/lean4/pull/14044) 为 `Nat.reprFast` 添加常量折叠。

## Monadic 验证：`mvcgen'` 和 `grind` 改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Monadic-Verification___--mvcgen___--and--grind--Improvements"
%%%

`mvcgen'` 和 {tactic}`grind` 生态系统不断成熟：

- [#13983](https://github.com/leanprover/lean4/pull/13983) 添加 `mvcgen' until $t`，其中 `$t` 是一个 conv 样式模式；一旦程序与模式匹配，验证条件生成就会停止。例如，比较这两个示例中的迹线：

  ```lean -show
  set_option mvcgen.warning false

  def increaseBy (n m : Nat) : Id Nat := pure (n + m)

  @[spec]
  theorem increaseBy_spec (n : Nat) : ⦃⌜True⌝⦄ increaseBy n m ⦃⇓ r => ⌜r = n + m⌝⦄ := by
    mvcgen [increaseBy]
  ```

  ```
  def inc (n : Nat) : Id Nat := do
    let a ← increaseBy n 1
    let b ← increaseBy a 2
    let c ← increaseBy b 3
    let d ← increaseBy c 4
    increaseBy d 5

  example (n : Nat) : ⦃⌜True⌝⦄ inc n ⦃⇓ r => ⌜r = n + 15⌝⦄ := by
    mvcgen' [inc]
    trace_state
    omega

  example (n : Nat) : ⦃⌜True⌝⦄ inc n ⦃⇓ r => ⌜r = n + 15⌝⦄ := by
    mvcgen' [inc] until increaseBy _ 4
    case vc1 a =>
      trace_state
      mvcgen'    -- resume: run the remaining program to completion
      omega
  ```

- [#13925](https://github.com/leanprover/lean4/pull/13925) 跨策略和 {tactic}`grind` (`sym =>`) 模式整合 `mvcgen'` 语法：

  ```
  example (n : Nat) : ⦃⌜True⌝⦄ inc n ⦃⇓ r => ⌜r = n + 15⌝⦄ := by
    sym =>
      mvcgen' [inc] <;> (show_asserted; finish)
  ```

  `mvcgen' invariants?`（建议模式）也可以在 sym => … 块内工作。

- [#13881](https://github.com/leanprover/lean4/pull/13881) 让 `mvcgen'` 分解其头部是类型类方法投影的程序（例如 `Add.add inst a b`）。
- [#13888](https://github.com/leanprover/lean4/pull/13888) 教导 `mvcgen'` 在 VC 生成期间将 `Triple` 形状的局部假设注册为规范。
- [#13971](https://github.com/leanprover/lean4/pull/13971) 使 {tactic}`cbv` 策略在 {tactic}`grind` 的交互式 `sym =>` 模式中可用。

## Lake：Linter 检修和缓存改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Lake___-Linter-Overhaul-and-Cache-Improvements"
%%%

### 通过选项进行环境检查
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Lake___-Linter-Overhaul-and-Cache-Improvements--Environment-Linters-via-Options"
%%%

[#13893](https://github.com/leanprover/lean4/pull/13893)（基于 [#13852](https://github.com/leanprover/lean4/pull/13852) 的内置 linter 集构建）使环境 linter 由精益选项 ({name}`Lean.Option`) 控制，就像普通的 linter 一样。每个环境 linter 都与一个布尔选项相关联，因此您可以使用 `set_option linter.X false in ...` 启用或禁用每个声明，并使用新的 `lake lint --linters=linter.X,-linter.Y` 标志跨 lint 运行。使用具有相同语法的 `--lint-only` 仅从指定的 linter 收集信息。 *重大更改：*之前的 `lake lint` 标志 `--extra`、`--lint-all` 和 `builtin_nolint` 属性已被删除，以支持此基于选项的控制。 `linter.extra` 成为一个 linter 集，其成员是现有的额外 linter。

### 模块检查器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Lake___-Linter-Overhaul-and-Cache-Improvements--Module-Linters"
%%%

[#13917](https://github.com/leanprover/lean4/pull/13917) 添加了模块 linter，它在详细说明模块结束时运行一次，而不是在每个命令之后运行。模块 linter 接收模块的完整顶级命令语法数组，使其适合需要整个模块视图的检查（例如强制执行模块范围的语法约定）。

### 其他湖改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Lake___-Linter-Overhaul-and-Cache-Improvements--Other-Lake-Improvements"
%%%

- [#13961](https://github.com/leanprover/lean4/pull/13961) 将 `--record-exceptions` 标志添加到 `lake lint`，其中插入 `set_option` 标志以消除触发警告的定义上的警告。
- [#14060](https://github.com/leanprover/lean4/pull/14060) 通过哈希对缓存工件进行重复数据删除，而 [#14036](https://github.com/leanprover/lean4/pull/14036) 使用新的 `--no-overwrite` 和 `--force-overwrite` 选项改进了 Lake 覆盖缓存数据的时间和方式。 [#13949](https://github.com/leanprover/lean4/pull/13949) 添加 `LAKE_RESTORE_ARTIFACTS` 环境变量来覆盖工作区的 `restoreAllArtifacts` 配置。

## 实验：增量编译缓存
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Experimental___-Incremental-Compilation-Caching"
%%%

[#13965](https://github.com/leanprover/lean4/pull/13965) 添加*实验性* CLI 标志，用于跨调用缓存 `lean` 的导入后详细状态：`--incr-save FILE` 在运行结束时写入完整快照，`--incr-load FILE` 在启动时重用一个快照，`--incr-header-save FILE` 写入仅标头快照（导入后 `Environment`，无命令体）。只要语法允许，加载的快照将被重复使用。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Library-Highlights"
%%%

- [#3727](https://github.com/leanprover/lean4/pull/3727) 添加了 `BitVec.flattenList` 用于连接位向量列表，具有特征引理和 `@[csimp]` 驱动的分而治之实现，比简单的左折叠快约 900 倍。
- [#12030](https://github.com/leanprover/lean4/pull/12030) 将 OpenSSL 链接到 Lean 的运行时，并使用 [#13988](https://github.com/leanprover/lean4/pull/13988) 使其可延迟加载。
- [#14054](https://github.com/leanprover/lean4/pull/14054) 位于电池的 `Nat.sqrt` 上游，具有避免暴露内部结构的特征引理。
- [#13798](https://github.com/leanprover/lean4/pull/13798) 简化了 `Std.Time` API：删除了 `DateTime (tz : TimeZone)`，并将之前的 `ZonedDateTime` 重命名为 `DateTime`。 *重大更改：*直接使用 `DateTime` 或 `ZonedDateTime` 的代码需要更新。
- [#13908](https://github.com/leanprover/lean4/pull/13908) 弃用 `Lean.RBMap` 和 `Lean.RBTree`，转而使用 `Std.TreeMap` 和 `Std.TreeSet`。进口商现在通过 {keywordOf Lean.Parser.Command.deprecated_module}`deprecated_module` 收到弃用警告。
- [#13891](https://github.com/leanprover/lean4/pull/13891) 添加了对通过 `CompactedRegion.save (allowClosures := true)` 将闭包序列化到 `.olean` 文件的选择支持。

## 重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Breaking-Changes"
%%%

除了上述 `do` elaborator 和 linter 更改之外：

- [#13305](https://github.com/leanprover/lean4/pull/13305)（新的 `do` 阐述器默认值）：`do` 表示法现在需要 `Pure` 实例，而不仅仅是 `Bind`。默认情况下，`do match` 的臂是非相关的 - 写入 `do match (dependent := true)` 以恢复旧的术语匹配扩展。 `try`/`catch` 不再接受结果类型仅通过强制与周围预期类型匹配的主体。无法访问的代码现在会触发警告而不是错误。语法 `let pat := rhs __FIX001__ otherwise` 现在的范围涵盖后面的 `doSeq`。
- [#13912](https://github.com/leanprover/lean4/pull/13912)（嵌套操作）：`(← do …)` 或 `(← try … catch …)` 内的 `return e` 现在从*封闭* `do` 块提前返回。 *迁移：* 当需要从嵌套块返回值时替换为 `pure e`，或者用括号 `(← (do …))` 括起来。
- [#13893](https://github.com/leanprover/lean4/pull/13893)（Lake lint）：删除 `--extra`、`--lint-all` 标志和 `@[builtin_nolint]` 属性。请改用 `lake lint --linters=linter.X,-linter.Y` 和 `set_option linter.X false in ...`。
- [#13798](https://github.com/leanprover/lean4/pull/13798)（标准时间）：`DateTime (tz : TimeZone)` 已删除；使用 `DateTime` （以前的 `ZonedDateTime`）。 *迁移：*用新的 `DateTime` 替换带有显式时区参数的 `DateTime` 的使用，并将对旧 `ZonedDateTime` 的引用重命名为 `DateTime` 。
- [#13908](https://github.com/leanprover/lean4/pull/13908)：`Lean.RBMap` 和 `Lean.RBTree` 已弃用。 *迁移：*切换到`Std.TreeMap`和`Std.TreeSet`。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Language"
%%%

```markdown

- [#14039](https://github.com/leanprover/lean4/pull/14039)
  fixes a bug where the builting docstring roles for asserting equalities did not properly highlight their contents for downstream consumers of rich docstring info, and exposes a structure that was mistakenly made private.

- [#14030](https://github.com/leanprover/lean4/pull/14030)
  removes the hypothesis rewriting functionality of `cbv` (introduced using `cbv at` syntax) in the `Sym` mode. Additionally, this PR fixes the transparency level when dealing with projections in `cbv`.

- [#14025](https://github.com/leanprover/lean4/pull/14025)
  adds `Lean.DoElem` and `Lean.DoSeq` as abbreviations for ``TSyntax `doElem`` and ``TSyntax `Lean.Parser.Term.doSeq``, mirroring `Lean.Term`, and uses them throughout the `do` elaborator.

- [#13961](https://github.com/leanprover/lean4/pull/13961)
  adds a a `--record-exceptions` flag to `lake lint`, such that the definitions triggering builtin linting framework warnings will be silenced, by putting an appropriate `set_option` flag.

- [#13072](https://github.com/leanprover/lean4/pull/13072)
  moves the status emoji from the stored trace header to the rendering layer. `withTraceNode`/`withTraceNodeBefore` no longer prepend `TraceResult.toEmoji` to the header `MessageData`; instead, `formatAux` and `InteractiveDiagnostic` prepend it when rendering. `TraceResult.toEmoji` is moved from `Lean.Util.Trace` to `Lean.Message` (next to the `TraceResult` definition) so that both rendering paths can use it.

- [#13868](https://github.com/leanprover/lean4/pull/13868)
  adds `Lean.Environment.hasExposedBody` — a small helper that asks "does `env` export a body for `n` to downstream modules?". The idiom

- [#13981](https://github.com/leanprover/lean4/pull/13981)
  fixes a private inductive type not being usable as a namespace immediately after its definition.

- [#13970](https://github.com/leanprover/lean4/pull/13970)
  makes the printed name of a variable in a `do`-elaborator error message carry hover info so the infoview surfaces its type. The bulk of the change is a small refactor that introduces a `MutVar` structure (declaration identifier + initial `FVarId`) and threads it through the do-elaborator helpers.

- [#13954](https://github.com/leanprover/lean4/pull/13954)
  prepares the `@[spec]` attribute used by `mvcgen` to support both specifications theorems for both new and old `mvcgen'` meta theories.

- [#13912](https://github.com/leanprover/lean4/pull/13912)
  extends the `nestedAction` parser (`←` inside `do` blocks) to accept arbitrary `doElem`s after `←` instead of just terms. The new `do` elaborator handles any `doElem`; the legacy elaborator (`set_option backward.do.legacy true`) keeps the old restriction to terms and rejects more general `doElem`s with an explicit error.

- [#13931](https://github.com/leanprover/lean4/pull/13931)
  introduces the `do← body` marker (ASCII `do<- body`), which lets ordinary continuation-taking wrappers like `withReader` or `Meta.withLocalDecl` participate in the surrounding `do` block's control flow. When `do← body` appears as the last argument of an application inside a `do` block, the body's `return`, `break`, `continue`, and `mut`-variable reassignments are forwarded out through the wrapper to the enclosing block.

- [#13852](https://github.com/leanprover/lean4/pull/13852)
  adds builtin linter sets — linter sets registered from core Lean code during initialization, complementing the user-facing `register_linter_set` command — and makes `linter.extra` one of them. Enabling `linter.extra` (e.g. via `set_option linter.extra true` or `lake lint --extra`) now activates the extra linters through the same set-membership mechanism as any other linter set.

- [#13917](https://github.com/leanprover/lean4/pull/13917)
  adds module linters, which run once at the end of elaborating a module rather than after every command. A module linter receives the full array of top-level command syntaxes for the module, making it suitable for checks that need a whole-module view (e.g. enforcing module-wide syntactic conventions) rather than per-command checks.

- [#13928](https://github.com/leanprover/lean4/pull/13928)
  fixes a non-linearity in DiscrTree insertion, reducing the time it takes to `import Mathlib` by ~10%

- [#13916](https://github.com/leanprover/lean4/pull/13916)
  fixes the silencing of `deprecated` warnings inside of definitions that are themselves deprecated and use `grind` with a `deprecated` theorem.

- [#13911](https://github.com/leanprover/lean4/pull/13911)
  removes the `Lean.Parser.Term.liftMethod` alias for `Lean.Parser.Term.nestedAction` that was kept for bootstrapping during the rename in #13910. Now that stage0 has been updated, the alias is no longer needed.

- [#13910](https://github.com/leanprover/lean4/pull/13910)
  renames the `liftMethod` parser (the `← <action>` syntax inside `do` blocks) and all of its associated helpers to use the more descriptive "nested action" terminology that the documentation already adopted.

- [#13305](https://github.com/leanprover/lean4/pull/13305)
  makes the new `do` elaborator (#12459) the default by flipping `backward.do.legacy` to `false`. Legacy behavior remains available via `set_option backward.do.legacy true`.

```

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Library"
%%%

```markdown

- [#14054](https://github.com/leanprover/lean4/pull/14054)
  upstreams `Nat.sqrt` from Batteries and just enough theory from mathlib to characterize the function without having to expose its internals.

- [#14051](https://github.com/leanprover/lean4/pull/14051)
  cleans up the internal `Std.Internal.Do` weakest-precondition library: the wp application lemmas and the `Triple` entailment field are renamed to follow the naming convention, the loop-invariant types are curried, and the monad spec lemmas reuse the `Triple` rules.

- [#14048](https://github.com/leanprover/lean4/pull/14048)
  adds a few lemmas about the way that `cpop` and `setWidth` interact on `BitVec`.

- [#3727](https://github.com/leanprover/lean4/pull/3727)
  adds `BitVec.flattenList`, which concatenates a list of bitvectors of a common width into a single bitvector, together with lemmas describing its bits: `getLsbD_flattenList` and `getMsbD_flattenList` compute an individual bit in terms of the corresponding element of the list, and `extractLsb_flattenList` describes extracting a contiguous range that falls within a single element. For efficient execution, `flattenList` is replaced at runtime via `@[csimp]` with a divide-and-conquer implementation costing `O(n * L * log L)` rather than the `O(n * L²)` of a naive left fold (≈900x faster at a million elements), while keeping `O(log L)` recursion depth so it remains stack-safe.

- [#13458](https://github.com/leanprover/lean4/pull/13458)
  adds `Nat.or_two_pow_eq_add_of_lt`, a small missing bitwise lemma.

- [#13459](https://github.com/leanprover/lean4/pull/13459)
  adds some missing `Array` and `Vector` `set!` convenience lemmas.

- [#13865](https://github.com/leanprover/lean4/pull/13865)
  adds lemmas to simplify sequencing with `pure` in `LawfulApplicative`.

- [#13988](https://github.com/leanprover/lean4/pull/13988)
  removes `OPENSSL_init_ssl` from `initialize_openssl` so it helps with loading OpenSSL lazily.

- [#13798](https://github.com/leanprover/lean4/pull/13798)
  simplifies the `Std.Time` API by removing the `DateTime (tz : TimeZone)` and replacing it with `ZonedDateTime` that got renamed to `DateTime`.

- [#12030](https://github.com/leanprover/lean4/pull/12030)
  links OpenSSL

- [#13960](https://github.com/leanprover/lean4/pull/13960)
  renames the `WPAdequate` typeclass to `WPSound` to reflect that it encodes the directional soundness arrow `wp x P → Internal.Ensures P x` (not a bidirectional adequacy correspondence), and replaces the `Id`-only `*.of_wp_run_eq` family with a uniform per-transformer soundness framework that works over any base monad with `WPSound`.

- [#13908](https://github.com/leanprover/lean4/pull/13908)
  deprecates the `Lean.RBMap` and `Lean.RBTree` containers in favour of `Std.TreeMap` and `Std.TreeSet`, which offer a more complete and consistent API. Nothing in the Lean repository uses these types any longer, and downstream code should migrate to the `Std` containers.

- [#13942](https://github.com/leanprover/lean4/pull/13942)
  introduces `PersistentHashMap.alter` in the same spirit as `Std.HashMap.alter`.

- [#13938](https://github.com/leanprover/lean4/pull/13938)
  adds tail-recursive `@[csimp]` runtime replacements for the bounded-quantifier `Decidable` instances `Nat.decidableBallLT`, `Nat.decidableExistsLT`, and `Nat.decidableExistsLT'`, so that *running* them no longer takes quadratic time or overflows the stack for large `n`.

- [#13891](https://github.com/leanprover/lean4/pull/13891)
  adds opt-in support for serializing closures (functions with captured values) to `.olean` files via `CompactedRegion.save (allowClosures := true)`, so a saved function can be loaded back and called, including from a separate process. Regular module data is unaffected and continues to reject closures.

```

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Tactics"
%%%

```markdown

- [#14031](https://github.com/leanprover/lean4/pull/14031)
  implements `SymM` simprocs for reducing bit-vector conversion operations.

- [#14029](https://github.com/leanprover/lean4/pull/14029)
  fixes a `Sym.dsimp` bug that could produce an ill-typed term, causing the kernel to reject the resulting goal with errors such as `application type mismatch` or `function expected`. It triggered when a `let`/`λ`/`∀` binder's type or value referenced an earlier binder in the same telescope.

- [#14022](https://github.com/leanprover/lean4/pull/14022)
  fixes `grind?` for goals containing hypotheses with inaccessible names. Distinct terms that differ only in inaccessible variables have identical anchors, so anchor references in generated tactic scripts could resolve to the wrong term during replay, producing empty `grind only` suggestions and scripts that could not close the goal. The `cases` tactic now supports anchor ordinal references (e.g., `cases #a56e/2` selects the second candidate matching the anchor), and `grind?` uses them to disambiguate colliding anchors.

- [#14021](https://github.com/leanprover/lean4/pull/14021)
  fixes an `unknown metavariable` error in `grind` that occurred when instantiating `match`-congruence equations whose generalized-pattern equalities mention theorem parameters that cannot be determined by E-matching.

- [#14020](https://github.com/leanprover/lean4/pull/14020)
  fixes two bugs that made `grind` construct proofs that are rejected by the kernel for goals involving `match`-expressions with overlapping patterns and proof discriminants (#13773).

- [#13971](https://github.com/leanprover/lean4/pull/13971)
  makes the `cbv` tactic available inside `grind`'s interactive `sym =>` mode. It reduces the goal target using call-by-value evaluation and supports the standard `at` location syntax (`cbv at h`, `cbv at h ⊢`, `cbv at *`) to reduce selected hypotheses, automatically closing equation goals via `refl` when reduction finishes the proof.

- [#13983](https://github.com/leanprover/lean4/pull/13983)
  adds `mvcgen' until $t`, where `$t` is a conv-style pattern (holes `_` allowed); verification-condition generation stops as soon as the program matches the pattern, leaving it as a VC instead of applying a spec, similar to the existing `stepLimit` option.

- [#13925](https://github.com/leanprover/lean4/pull/13925)
  consolidates `mvcgen'`'s syntax across tactic and grind (`sym =>`) modes. The grind-mode `with` clause is removed (use `<;>` instead), and the tactic-level `with` now takes a single grind step that shares an E-graph with `mvcgen'`. `mvcgen' invariants?` (suggest mode) also works inside `sym => …` blocks.

- [#13944](https://github.com/leanprover/lean4/pull/13944)
  changes a `filterMap` to a `map` in `CNF.convertLRAT'` so that tautological clauses become `none` in the array rather then being deleted.

- [#13932](https://github.com/leanprover/lean4/pull/13932)
  implements the `evalGround` `dsimproc` for `Sym.dsimp`.

- [#13621](https://github.com/leanprover/lean4/pull/13621)
  fixes a bug in the `rcases`-family tactics where the InfoView could give "unknown free variable" errors when the cursor was inside the pattern. It hoists applying the fvar substitution to give `addTermInfo'` and `addLocalVarInfo` the correct expression. Previously, the substitution only happened in `rfl`/typed/tuple/alternative branches, which caused stale free variables to be recorded in the info tree. Repeated applications in recursive cases like `.paren` should be fine, because the domain of `fs` should be old fvars and replacement exprs should only refer current-goal fvars, not old-domain fvars. Proof elaboration shouldn't be affected by this PR.

- [#13909](https://github.com/leanprover/lean4/pull/13909)
  makes the `intersperse` library suggestion combinator honor `ratio` at the endpoints, so `ratio = 0` draws entirely from `selector₂` and `ratio = 1` entirely from `selector₁` while both selectors still have results. Previously each element was chosen by comparing the achieved fraction of `selector₁` contributions against `ratio` with a strict `<` (seeded to `0` when empty), which left `ratio = 1` drawing one stray element from `selector₂` before settling. The combinator now picks whichever candidate next state keeps the running fraction closest to `ratio`, with ties going to `selector₁`.

- [#13907](https://github.com/leanprover/lean4/pull/13907)
  makes the `intersperse` library suggestion combinator request `maxSuggestions` results from each of its two selectors instead of splitting the budget by `ratio`, so that if one selector returns fewer suggestions than its allocation the other can compensate to still fill the request. The interspersing ratio and the final `maxSuggestions` cap on the combined result are unchanged.

- [#13896](https://github.com/leanprover/lean4/pull/13896)
  improves the support for universe constraints in the `SymM` pattern matcher/unifier. Two new cases are supported

- [#13887](https://github.com/leanprover/lean4/pull/13887)
  factors the whnf-based projection step used inside `mvcgen'`'s head reducer into a new `reduceProjAndUnfold?` helper that `unfoldReducible`s the projected field only when whnf reduced the structure. The outer `Sym.unfoldReducible` call in `tryHeadReduceProg` is no longer needed, so the per-step cost of normalizing abbrevs is proportional to the small unfolded instance body rather than the whole program expression.

- [#13888](https://github.com/leanprover/lean4/pull/13888)
  teaches `mvcgen'` to register Triple-shaped local hypotheses as specs as they come into scope during VC generation. This is an existing feature of `mvcgen`.

- [#13883](https://github.com/leanprover/lean4/pull/13883)
  teaches `mvcgen'` to register Triple-shaped local hypotheses as specs as they come into scope during VC generation. This is an existing feature of `mvcgen`.

- [#13881](https://github.com/leanprover/lean4/pull/13881)
  lets `mvcgen'` decompose programs whose head is a typeclass method projection (e.g. `Add.add inst a b`) by reducing through the kernel projection to the instance body.

- [#13880](https://github.com/leanprover/lean4/pull/13880)
  reverts #13870 due to large performance regressions visible on [radar](https://radar.lean-lang.org/repos/lean4/commits/3757160ab7625097a69757bd1dce8c28f6af9f09) that were not caught by benchmarking before merge.

- [#13878](https://github.com/leanprover/lean4/pull/13878)
  fixes a bug when reducing `match`-expressions in the `Sym.dsimp` tactic.

- [#13870](https://github.com/leanprover/lean4/pull/13870)
  lets `mvcgen'` decompose programs whose head is a typeclass method projection (e.g. `Add.add inst a b`) by reducing through the kernel projection to the instance body.

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Compiler"
%%%

```markdown

- [#14044](https://github.com/leanprover/lean4/pull/14044)
  introduces constant folding for `Nat.reprFast`.

- [#13123](https://github.com/leanprover/lean4/pull/13123)
  makes the task thread pool reclaim idle worker threads after 5 seconds of inactivity. Previously, pool threads were allocated on demand but never freed, which could waste significant memory given the new default 1GB stack size per thread.

- [#13991](https://github.com/leanprover/lean4/pull/13991)
  adds constant folding for `USize` operations that are already supported in other datatypes. It does so by checking whether the result of applying the operation is equivalent in both `UInt32` and `UInt64`. Furthermore, it also adds constant folding operations for the most common bitwise operations.

- [#13989](https://github.com/leanprover/lean4/pull/13989)
  fixes a bug in the constant folding for `Bool` wherein the compiler incorrectly determined
  0-ary functions that participate in constant folding to be equal to `false`.

- [#13974](https://github.com/leanprover/lean4/pull/13974)
  adds constant folding for `USize` relation by evaluating them both in the `UInt32` and
  `UInt64` world and applying the fold if both worlds agree.

- [#13926](https://github.com/leanprover/lean4/pull/13926)
  makes `dbgTraceIfShared` print the shared message in all non-linear situations. Previously
  it would only trigger if `RC > 1`. However, `RC = 0` and `RC < 0` are also non-linearity triggers.

- [#13924](https://github.com/leanprover/lean4/pull/13924)
  fixes a code generator panic that occurred when a recursive definition (well-founded or structural) was marked by a `noncomputable section` and then referenced from computable code. The compiler now reports a clean error, or accepts the second definition when everything occurs in a `noncomputable section`.

```

# FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--FFI"
%%%

```markdown

- [#13952](https://github.com/leanprover/lean4/pull/13952)
  declares the `extern "C"` parameter of `lean_mk_bool_data_value` as `uint8` to match its `@[export]`ed Lean definition (where a `Bool` argument lowers to `uint8_t` at the C ABI), fixing a `wasm32`-emscripten/LTO ABI mismatch that trapped during module initialization.

```

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Lake"
%%%

```markdown

- [#14060](https://github.com/leanprover/lean4/pull/14060)
  has Lake deduplicate artifacts by their hash when uploading or downloading to the cache (e.g., in `lake cache put` or `lake cache get`). This fixes possible errors when `curl` was asked to transfer to the same file and/or URL multiple times.

- [#14036](https://github.com/leanprover/lean4/pull/14036)
  refines when and how Lake decides to overwrite data while caching, and has Lake prefer outputs in a local trace file over those stored in the cache.

- [#13893](https://github.com/leanprover/lean4/pull/13893)
  makes environment linters (the declaration-level checks run by `lake lint --builtin-lint`) controlled by `Lean.Option`s, just like ordinary linters. Each environment linter is tied to a boolean option, so you enable or disable it per declaration with `set_option linter.X false in ...` and across a lint run with the new `lake lint --linters=linter.X,-linter.Y` flag.  Using `--lint-only` with the same syntax will only collect information from the specified linters and will not run the default on linters. The previous `lake lint` flags `--extra`, `--lint-all`, and the `builtin_nolint` attribute, are removed in favour of this option-based control.

- [#13949](https://github.com/leanprover/lean4/pull/13949)
  adds a `LAKE_RESTORE_ARTIFACTS` environment variable that overrides the workspace's default `restoreAllArtifacts` configuration, mirroring how `LAKE_ARTIFACT_CACHE` overrides `enableArtifactCache`.

- [#13936](https://github.com/leanprover/lean4/pull/13936)
  fixes an issue where `depPkgs` was not properly set for a transitive dependency that was overriden by a package at a higher level in the dependency graph.

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Other"
%%%

```markdown

- [#14028](https://github.com/leanprover/lean4/pull/14028)
  fixes an issue where existence of potential stray files could influence whether a module is loaded under the module system, resulting in unexpected behavior

- [#14019](https://github.com/leanprover/lean4/pull/14019)
  fixes `mkSimpleThunkType` to use `_` instead of `Name.anonymous` as its binder name. A local declaration whose user name is `Name.anonymous` matches every identifier in `resolveLocalName`, shadowing all global constants and making the pretty printer render every constant in the local context as inaccessible (e.g., `True✝`). The `match` compiler uses `mkSimpleThunkType` to create the minor premises of parameterless alternatives, and tactics that introduce these binders using their binder name verbatim (e.g., `grind`) ended up with a corrupted local context. Found while investigating #13773.

- [#13965](https://github.com/leanprover/lean4/pull/13965)
  adds **experimental** CLI flags that cache `lean`'s elaboration state used for in-process incrementality across invocations:
  * `--incr-save FILE` writes a full snapshot including the states after import and after each command at the end of the run
  * `--incr-load FILE` reuses such a snapshot at startup, up to the first point of syntactic difference just like incrementality in the language server
    *  `--incr-header-save FILE` writes a cheaper and smaller import-only snapshot

```
