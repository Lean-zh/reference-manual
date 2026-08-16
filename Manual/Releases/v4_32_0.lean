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

#doc (Manual) "Lean4.32.0 (2026-07-13)" =>
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

Lean 4.32.0 使新的 {ref "do-notation"}`do` 精译器成为默认值，使用 `do←` 标记扩展 `do` 表示法以进行效果转发，并带来显着的性能改进，包括 `import Mathlib` 时间减少约 10%。 Lake 的检查框架获得了基于选项的控制和模块级检查器，并且实验性增量编译模式支持命令行界面标志。

_此亮点部分由 Juanjo Madrigal 贡献。_

## 新 `do` Elaborator 现在是默认值
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--New--do--Elaborator-is-Now-the-Default"
%%%

[#13305](https://github.com/leanprover/lean4/pull/13305) 通过将 {option}`backward.do.legacy` 翻转为 `false`，使新的 {ref "do-notation"}`do` 精译器（在 v4.31.0 中作为实验引入）成为默认值。旧版精译器仍可通过 `set_option backward.do.legacy true` 使用。 [#13912](https://github.com/leanprover/lean4/pull/13912) 和 [#13931](https://github.com/leanprover/lean4/pull/13931) 添加了重要的新功能：

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

### 嵌套操作中的任意 `doElem`
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

`(← do …)` 或 `(← try … catch …)` 内的 `return e` 现在从封闭 `do` 块提前返回，而不是从嵌套操作中返回。这是一个*重大更改*：当打算从嵌套块返回值时替换为 `pure e`，或者将 `do` 块括在括号中 (`(← (do …))`)。

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

## 单子程序验证：`mvcgen'` 和 `grind` 改进
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

[#13893](https://github.com/leanprover/lean4/pull/13893)（基于 [#13852](https://github.com/leanprover/lean4/pull/13852) 的内置检查器集构建）使环境检查器由Lean选项 ({name}`Lean.Option`) 控制，就像普通的检查器一样。每个环境检查器都与一个布尔选项相关联，因此您可以使用 `set_option linter.X false in ...` 启用或禁用每个声明，并使用新的 `lake lint --linters=linter.X,-linter.Y` 标志跨 lint 运行。使用具有相同语法的 `--lint-only` 仅从指定的检查器收集信息。 *重大更改：*之前的 `lake lint` 标志 `--extra`、`--lint-all` 和 `builtin_nolint` 属性已被删除，以支持此基于选项的控制。 `linter.extra` 成为一个检查器集，其成员是现有的额外检查器。

### 模块检查器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Lake___-Linter-Overhaul-and-Cache-Improvements--Module-Linters"
%%%

[#13917](https://github.com/leanprover/lean4/pull/13917) 添加了模块检查器，它在精译模块结束时运行一次，而不是在每个命令之后运行。模块检查器接收模块的完整顶级命令语法数组，使其适合需要整个模块视图的检查（例如强制执行模块范围的语法约定）。

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

[#13965](https://github.com/leanprover/lean4/pull/13965) 添加*实验性* 命令行界面标志，用于跨调用缓存 `lean` 的导入后详细状态：`--incr-save FILE` 在运行结束时写入完整快照，`--incr-load FILE` 在启动时重用一个快照，`--incr-header-save FILE` 写入仅标头快照（导入后 `Environment`，无命令体）。只要语法允许，加载的快照将被重复使用。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Library-Highlights"
%%%

- [#3727](https://github.com/leanprover/lean4/pull/3727) 添加了 `BitVec.flattenList` 用于连接位向量列表，具有特征引理和 `@[csimp]` 驱动的分而治之实现，比简单的左折叠快约 900 倍。
- [#12030](https://github.com/leanprover/lean4/pull/12030) 将 OpenSSL 链接到 Lean 的运行时，并使用 [#13988](https://github.com/leanprover/lean4/pull/13988) 使其可延迟加载。
- [#14054](https://github.com/leanprover/lean4/pull/14054) 位于电池的 `Nat.sqrt` 上游，具有避免暴露内部结构的特征引理。
- [#13798](https://github.com/leanprover/lean4/pull/13798) 简化了 `Std.Time` 接口：删除了 `DateTime (tz : TimeZone)`，并将之前的 `ZonedDateTime` 重命名为 `DateTime`。 *重大更改：*直接使用 `DateTime` 或 `ZonedDateTime` 的代码需要更新。
- [#13908](https://github.com/leanprover/lean4/pull/13908) 弃用 `Lean.RBMap` 和 `Lean.RBTree`，转而使用 `Std.TreeMap` 和 `Std.TreeSet`。导入方现在通过 {keywordOf Lean.Parser.Command.deprecated_module}`deprecated_module` 收到弃用警告。
- [#13891](https://github.com/leanprover/lean4/pull/13891) 添加了对通过 `CompactedRegion.save (allowClosures := true)` 将闭包序列化到 `.olean` 文件的选择支持。

## 重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Highlights--Breaking-Changes"
%%%

除了上述 `do` 精译器和 检查器更改之外：

- [#13305](https://github.com/leanprover/lean4/pull/13305)（新的 `do` 精译器默认值）：`do` 表示法现在需要 `Pure` 实例，而不仅仅是 `Bind`。默认情况下，`do match` 的臂是非相关的 - 写入 `do match (dependent := true)` 以恢复旧的术语匹配扩展。 `try`/`catch` 不再接受结果类型仅通过强制与周围预期类型匹配的主体。无法访问的代码现在会触发警告而不是错误。语法 `let pat := rhs | otherwise` 现在的范围涵盖后面的 `doSeq`。
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
修复了一个错误，即用于断言平等的构建文档字符串角色没有为丰富文档字符串信息的下游消费者正确突出显示其内容，并公开了错误地设为私有的结构。

- [#14030](https://github.com/leanprover/lean4/pull/14030)
删除`Sym`模式下`cbv`的假设重写功能（使用`cbv at`语法引入）。此外，此 PR 修复了处理 `cbv` 中的投影时的透明度级别。

- [#14025](https://github.com/leanprover/lean4/pull/14025)
添加 `Lean.DoElem` 和 `Lean.DoSeq` 作为 ``TSyntax `doElem`` and ``TSyntax `Lean.Parser.Term.doSeq`` 的缩写，镜像 `Lean.Term`，并在整个 `do` 精译器中使用它们。

- [#13961](https://github.com/leanprover/lean4/pull/13961)
向 `lake lint` 添加一个 `--record-exceptions` 标志，这样通过放置适当的 `set_option` 标志，触发内置检查框架警告的定义将被静音。

- [#13072](https://github.com/leanprover/lean4/pull/13072)
将状态表情符号从存储的跟踪标头移动到渲染层。 `withTraceNode`/`withTraceNodeBefore`不再将`TraceResult.toEmoji`添加到标头`MessageData`；相反，`formatAux`和`InteractiveDiagnostic`在渲染时将其添加到前面。 `TraceResult.toEmoji`从`Lean.Util.Trace`移动到`Lean.Message`（位于`TraceResult`定义旁边），以便两个渲染路径都可以使用它。

- [#13868](https://github.com/leanprover/lean4/pull/13868)
添加 `Lean.Environment.hasExposedBody` — 一个小助手，询问“`env` 是否将 `n` 的主体导出到下游模块？”。成语

- [#13981](https://github.com/leanprover/lean4/pull/13981)
修复了私有归纳类型在定义后不能立即用作命名空间的问题。

- [#13970](https://github.com/leanprover/lean4/pull/13970)
使 `do`-精译器错误消息中变量的打印名称携带悬停信息，以便信息视图显示其类型。大部分更改是一个小的重构，引入了 `MutVar` 结构（声明标识符 + 初始 `FVarId`）并将其通过 do-精译器帮助程序进行线程化。

- [#13954](https://github.com/leanprover/lean4/pull/13954)
准备`mvcgen`使用的`@[spec]`属性来支持新旧`mvcgen'`元理论的规范定理。

- [#13912](https://github.com/leanprover/lean4/pull/13912)
扩展`nestedAction`解析器（`do`块内的`←`）以接受`←`之后的任意`doElem`，而不仅仅是术语。新的`do`精译器可处理任何`doElem`；遗留的精译器（`set_option backward.do.legacy true`）保留了旧的术语限制，并拒绝了更一般的`doElem`，并出现了明确的错误。

- [#13931](https://github.com/leanprover/lean4/pull/13931)
引入了 `do← body` 标记（ASCII `do<- body`），它让普通的连续获取包装器（如 `withReader` 或 `Meta.withLocalDecl`）参与周围的 `do` 块的控制流。当 `do← body` 作为应用程序的最后一个参数出现在 `do` 块内时，主体的 `return`、`break`、`continue` 和 `mut` 变量重新分配将通过包装器转发到封闭块。

- [#13852](https://github.com/leanprover/lean4/pull/13852)
添加内置检查器集 - 在初始化期间从核心 Lean 代码注册的检查器集，补充面向用户的 `register_linter_set` 命令 - 并使 `linter.extra` 其中之一。启用 `linter.extra` （例如，通过 `set_option linter.extra true` 或 `lake lint --extra`）现在可以通过与任何其他检查器集相同的集成员机制激活额外的检查器。

- [#13917](https://github.com/leanprover/lean4/pull/13917)
添加了模块检查器，它在精译模块结束时运行一次，而不是在每个命令之后运行。模块检查器接收模块的完整顶级命令语法数组，使其适合需要整个模块视图的检查（例如强制执行模块范围的语法约定）而不是每个命令检查。

- [#13928](https://github.com/leanprover/lean4/pull/13928)
修复了 DiscrTree 插入中的非线性问题，将 `import Mathlib` 所需的时间减少了约 10%

- [#13916](https://github.com/leanprover/lean4/pull/13916)
修复了本身已弃用的定义内`deprecated`警告的沉默，并将`grind`与`deprecated`定理一起使用。

- [#13911](https://github.com/leanprover/lean4/pull/13911)
删除了 `Lean.Parser.Term.nestedAction` 的 `Lean.Parser.Term.liftMethod` 别名，该别名在 #13910 重命名期间保留用于引导。现在 stage0 已更新，不再需要别名。

- [#13910](https://github.com/leanprover/lean4/pull/13910)
重命名 `liftMethod` 解析器（`do` 块内的 `← <action>` 语法）及其所有相关帮助程序，以使用文档已采用的更具描述性的“嵌套操作”术语。

- [#13305](https://github.com/leanprover/lean4/pull/13305)
通过将 `backward.do.legacy` 翻转为 `false`，使新的 `do` 精译器 (#12459) 成为默认值。旧版行为仍然可以通过 `set_option backward.do.legacy true` 获得。

```

# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Library"
%%%

```markdown

- [#14054](https://github.com/leanprover/lean4/pull/14054)
来自电池的上游 `Nat.sqrt` 以及来自 mathlib 的足够理论来描述该函数，而无需暴露其内部结构。

- [#14051](https://github.com/leanprover/lean4/pull/14051)
清理内部 `Std.Internal.Do` 最弱前置条件库：wp 应用程序引理和 `Triple` 蕴涵字段被重命名以遵循命名约定，循环不变类型被柯里化，并且单子规范引理重用 `Triple` 规则。

- [#14048](https://github.com/leanprover/lean4/pull/14048)
添加了一些关于 `cpop` 和 `setWidth` 在 `BitVec` 上交互的方式的引理。

- [#3727](https://github.com/leanprover/lean4/pull/3727)
添加`BitVec.flattenList`，它将公共宽度的位向量列表连接成单个位向量，以及描述其位的引理：`getLsbD_flattenList`和`getMsbD_flattenList`根据列表的相应元素计算单个位，`extractLsb_flattenList`描述提取落在单个元素内的连续范围。为了高效执行，`flattenList`在运行时通过`@[csimp]`替换为分而治之的实现，成本为`O(n * L * log L)`，而不是朴素左折叠的`O(n * L²)`（在一百万个元素上快约900倍），同时保持`O(log L)`递归深度，因此它保持堆栈安全。

- [#13458](https://github.com/leanprover/lean4/pull/13458)
添加了`Nat.or_two_pow_eq_add_of_lt`，一个小的缺失的按位引理。

- [#13459](https://github.com/leanprover/lean4/pull/13459)
添加了一些缺失的 `Array` 和 `Vector` `set!` 便利引理。

- [#13865](https://github.com/leanprover/lean4/pull/13865)
添加引理以简化 `pure` 中的`LawfulApplicative` 的排序。

- [#13988](https://github.com/leanprover/lean4/pull/13988)
从 `initialize_openssl` 中删除 `OPENSSL_init_ssl`，因此有助于延迟加载 OpenSSL。

- [#13798](https://github.com/leanprover/lean4/pull/13798)
通过删除 `DateTime (tz : TimeZone)` 并将其替换为已重命名为 `DateTime` 的 `ZonedDateTime` 来简化 `Std.Time` 接口。

- [#12030](https://github.com/leanprover/lean4/pull/12030)
链接 OpenSSL

- [#13960](https://github.com/leanprover/lean4/pull/13960)
将 `WPAdequate` 类型类重命名为 `WPSound`，以反映它对方向健全性箭头 `wp x P → Internal.Ensures P x` 进行编码（不是双向充分性对应），并用可在任何基本单子上工作的统一的每变压器健全性框架替换 `Id`-only `*.of_wp_run_eq` 系列与`WPSound`。

- [#13908](https://github.com/leanprover/lean4/pull/13908)
弃用 `Lean.RBMap` 和 `Lean.RBTree` 容器，转而使用 `Std.TreeMap` 和 `Std.TreeSet`，它们提供更完整和一致的接口。 Lean 存储库中的任何内容都不再使用这些类型，下游代码应迁移到 `Std` 容器。

- [#13942](https://github.com/leanprover/lean4/pull/13942)
本着与`Std.HashMap.alter`相同的精神介绍`PersistentHashMap.alter`。

- [#13938](https://github.com/leanprover/lean4/pull/13938)
为有界量词 `Decidable` 实例 `Nat.decidableBallLT`、`Nat.decidableExistsLT` 和 `Nat.decidableExistsLT'` 添加尾递归 `@[csimp]` 运行时替换，以便*运行*它们不再需要二次时间或溢出大型 `n` 的堆栈。

- [#13891](https://github.com/leanprover/lean4/pull/13891)
添加了对通过 `CompactedRegion.save (allowClosures := true)` 将闭包（具有捕获值的函数）序列化到 `.olean` 文件的选择性支持，因此可以加载回并调用已保存的函数，包括从单独的进程中加载​​和调用。常规模块数据不受影响并继续拒绝关闭。

```

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Tactics"
%%%

```markdown

- [#14031](https://github.com/leanprover/lean4/pull/14031)
实现 `SymM` 简化过程以减少位向量转换操作。

- [#14029](https://github.com/leanprover/lean4/pull/14029)
修复了一个 `Sym.dsimp` 错误，该错误可能会产生错误类型的术语，导致内核拒绝生成的目标，并出现诸如 `application type mismatch` 或 `function expected` 之类的错误。当`let`/`λ`/`∀`绑定器的类型或值引用同一望远镜中较早的绑定器时触发。

- [#14022](https://github.com/leanprover/lean4/pull/14022)
修复了包含名称无法访问的假设的目标的`grind?`。仅在不可访问变量中不同的不同术语具有相同的锚点，因此生成的策略脚本中的锚点引用可能会在重播期间解析为错误的术语，从而产生空的`grind only`建议和无法关闭目标的脚本。 `cases`策略现在支持锚点序数引用（例如，`cases #a56e/2`选择与锚点匹配的第二个候选者），并且`grind?`使用它们来消除冲突锚点的歧义。

- [#14021](https://github.com/leanprover/lean4/pull/14021)
修复了在实例化 `match` 同余方程时发生的 `grind` 中的 `unknown metavariable` 错误，其广义模式等式提到了无法通过电子匹配确定的定理参数。

- [#14020](https://github.com/leanprover/lean4/pull/14020)
修复了导致 `grind` 构造证明被内核拒绝的两个错误，这些错误涉及具有重叠模式和证明判别式的 `match` 表达式 (#13773)。

- [#13971](https://github.com/leanprover/lean4/pull/13971)
使`cbv`策略在`grind`的交互式`sym =>`模式中可用。它使用按值调用评估来减少目标，并支持标准 `at` 位置语法（`cbv at h`、`cbv at h ⊢`、`cbv at *`）来减少选定的假设，当减少完成证明时，通过 `refl` 自动关闭方程目标。

- [#13983](https://github.com/leanprover/lean4/pull/13983)
添加`mvcgen' until $t`，其中`$t`是一个转换样式模式（允许有孔`_`）；一旦程序匹配模式，验证条件生成就会停止，将其保留为 VC 而不是应用规范，类似于现有的 `stepLimit` 选项。

- [#13925](https://github.com/leanprover/lean4/pull/13925)
统一了 `mvcgen'` 在策略模式和研磨（`sym =>`）模式中的语法。研磨模式的 `with` 子句已删除（改用 `<;>`），而策略级 `with` 现在接受一个与 `mvcgen'` 共享 E 图的研磨步骤。`mvcgen' invariants?`（建议模式）也适用于 `sym => …` 块。

- [#13944](https://github.com/leanprover/lean4/pull/13944)
将`CNF.convertLRAT'`中的`filterMap`更改为`map`，以便同义反复子句在数组中变为`none`而不是被删除。

- [#13932](https://github.com/leanprover/lean4/pull/13932)
为 `Sym.dsimp` 实现 `evalGround` `dsimproc`。

- [#13621](https://github.com/leanprover/lean4/pull/13621)
修复了 `rcases` 系列策略中的一个错误，当光标位于模式内时，InfoView 可能会给出“未知的自由变量”错误。它提升应用 fvar 替换来为 `addTermInfo'` 和 `addLocalVarInfo` 提供正确的表达式。以前，替换仅发生在 `rfl`/typed/tuple/alternative 分支中，这导致过时的自由变量被记录在信息树中。在像`.paren`这样的递归情况下重复应用应该没问题，因为`fs`的域应该是旧的fvar，并且替换表达式应该仅引用当前目标fvar，而不是旧域fvar。证明的精译不应受到此 PR 的影响。

- [#13909](https://github.com/leanprover/lean4/pull/13909)
使`intersperse`库建议组合器在端点尊重`ratio`，因此`ratio = 0`完全从`selector₂`提取，`ratio = 1`完全从`selector₁`提取，而两个选择器仍然有结果。以前，每个元素的选择都是通过将`selector₁`贡献与`ratio`的贡献分数与严格的`<`（空时播种到`0`）进行比较，这使得`ratio = 1`在稳定之前从`selector₂`提取一个杂散元素。组合器现在选择下一个状态中保持运行分数最接近`ratio`的候选者，并与`selector₁`保持联系。

- [#13907](https://github.com/leanprover/lean4/pull/13907)
使 `intersperse` 库建议组合器从两个选择器各请求 `maxSuggestions` 条结果，而不是按 `ratio` 分割预算。这样，如果一个选择器返回的建议少于其配额，另一个选择器便可补足，仍然满足请求。交错比例和最终组合结果的 `maxSuggestions` 上限不变。

- [#13896](https://github.com/leanprover/lean4/pull/13896)
改进了对 `SymM` 模式匹配器/统一器中的宇宙约束的支持。支持两个新案例

- [#13887](https://github.com/leanprover/lean4/pull/13887)
将`mvcgen'`头部减速器中使用的基于whnf的投影步骤分解为新的`reduceProjAndUnfold?`助手，仅当whnf缩减结构时，`unfoldReducible`才是投影场。不再需要`tryHeadReduceProg`中的外部`Sym.unfoldReducible`调用，因此规范化缩写的每步成本与展开的小实例主体成正比，而不是与整个程序表达式成正比。

- [#13888](https://github.com/leanprover/lean4/pull/13888)
教导`mvcgen'`将三重形状局部假设注册为规范，因为它们在 VC 生成期间进入范围。这是`mvcgen`现有的功能。

- [#13883](https://github.com/leanprover/lean4/pull/13883)
教导`mvcgen'`将三重形状局部假设注册为规范，因为它们在 VC 生成期间进入范围。这是`mvcgen`现有的功能。

- [#13881](https://github.com/leanprover/lean4/pull/13881)
让 `mvcgen'` 通过减少内核投影到实例主体来分解其头部是类型类方法投影（例如 `Add.add inst a b`）的程序。

- [#13880](https://github.com/leanprover/lean4/pull/13880)
恢复#13870，因为[雷达](https://radar.lean-lang.org/repos/lean4/commits/3757160ab7625097a69757bd1dce8c28f6af9f09) 上可见性能大幅下降，但合并前的基准测试未发现这些下降。

- [#13878](https://github.com/leanprover/lean4/pull/13878)
修复了减少 `Sym.dsimp` 策略中的 `match` 表达式时的错误。

- [#13870](https://github.com/leanprover/lean4/pull/13870)
让 `mvcgen'` 通过减少内核投影到实例主体来分解其头部是类型类方法投影（例如 `Add.add inst a b`）的程序。

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Compiler"
%%%

```markdown

- [#14044](https://github.com/leanprover/lean4/pull/14044)
引入了`Nat.reprFast`的常量折叠。

- [#13123](https://github.com/leanprover/lean4/pull/13123)
使任务线程池在 5 秒不活动后回收空闲工作线程。以前，池线程是按需分配的，但从未释放，鉴于每个线程新的默认 1GB 堆栈大小，这可能会浪费大量内存。

- [#13991](https://github.com/leanprover/lean4/pull/13991)
为其他数据类型已支持的`USize`操作添加常量折叠。它通过检查应用操作的结果在`UInt32`和`UInt64`中是否相等来实现这一点。此外，它还为最常见的按位操作添加了常量折叠操作。

- [#13989](https://github.com/leanprover/lean4/pull/13989)
修复了 `Bool` 常量折叠中的错误，其中编译器错误地确定
参与常量折叠的 0 元函数等于`false`。

- [#13974](https://github.com/leanprover/lean4/pull/13974)
通过在 `UInt32` 和中评估它们来为 `USize` 关系添加常量折叠
`UInt64` 世界并在两个世界都同意的情况下应用折叠。

- [#13926](https://github.com/leanprover/lean4/pull/13926)
使`dbgTraceIfShared`在所有非线性情况下打印共享消息。之前
仅当`RC > 1`时才会触发。然而，`RC = 0`和`RC < 0`也是非线性触发器。

- [#13924](https://github.com/leanprover/lean4/pull/13924)
修复了当递归定义（有充分依据的或结构性的）由 `noncomputable section` 标记然后从可计算代码中引用时发生的代码生成器崩溃。现在，编译器会报告一个干净的错误，或者当所有内容都发生在 `noncomputable section` 中时接受第二个定义。

```

# 外部函数接口
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--FFI"
%%%

```markdown

- [#13952](https://github.com/leanprover/lean4/pull/13952)
将 `lean_mk_bool_data_value` 的 `extern "C"` 参数声明为 `uint8` 以匹配其 `@[export]`ed Lean 定义（其中 `Bool` 参数在 C ABI 处降低为 `uint8_t`），修复模块初始化期间捕获的`wasm32`-emscripten/LTO ABI 不匹配。

```

# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Lake"
%%%

```markdown

- [#14060](https://github.com/leanprover/lean4/pull/14060)
Lake 在上传或下载到缓存时（例如，在 `lake cache put` 或 `lake cache get` 中）根据哈希值对工件进行重复数据删除。这修复了当 `curl` 被要求多次传输到同一文件和/或 URL 时可能出现的错误。

- [#14036](https://github.com/leanprover/lean4/pull/14036)
改进了 Lake 在缓存时决定覆盖数据的时间和方式，并且使 Lake 更喜欢本地跟踪文件中的输出而不是存储在缓存中的输出。

- [#13893](https://github.com/leanprover/lean4/pull/13893)
使环境检查器（由 `lake lint --builtin-lint` 运行的声明级检查）由 `Lean.Option` 控制，就像普通的检查器一样。每个环境检查器都与一个布尔选项相关联，因此您可以使用 `set_option linter.X false in ...` 每个声明启用或禁用它，并使用新的 `lake lint --linters=linter.X,-linter.Y` 标志运行 lint。  使用相同语法的 `--lint-only` 只会从指定的检查器中收集信息，而不会在检查器上运行默认值。之前的 `lake lint` 标志 `--extra`、`--lint-all` 和 `builtin_nolint` 属性已被删除，以支持此基于选项的控制。

- [#13949](https://github.com/leanprover/lean4/pull/13949)
添加一个 `LAKE_RESTORE_ARTIFACTS` 环境变量，该变量覆盖工作区的默认 `restoreAllArtifacts` 配置，镜像 `LAKE_ARTIFACT_CACHE` 覆盖 `enableArtifactCache` 的方式。

- [#13936](https://github.com/leanprover/lean4/pull/13936)
修复了未正确设置 `depPkgs` 的传递依赖关系的问题，该传递依赖关系被依赖关系图中更高级别的包覆盖。

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___32___0-_LPAR_2026-07-13_RPAR_--Other"
%%%

```markdown

- [#14028](https://github.com/leanprover/lean4/pull/14028)
修复了潜在杂散文件的存在可能影响模块是否加载到模块系统下的问题，从而导致意外行为

- [#14019](https://github.com/leanprover/lean4/pull/14019)
修复 `mkSimpleThunkType` 使用 `_` 而不是 `Name.anonymous` 作为绑定器名称的问题。名称为 `Name.anonymous` 的局部声明会在 `resolveLocalName` 中匹配每个标识符，从而遮蔽所有全局常量，并使美化打印器把局部上下文中的每个常量都渲染为不可访问的名称（例如 `True✝`）。`match` 编译器使用 `mkSimpleThunkType` 为无参数分支创建次要前提；按原样使用绑定器名称引入这些绑定器的策略（如 `grind`）最终会破坏局部上下文。此问题在调查 #13773 时发现。

- [#13965](https://github.com/leanprover/lean4/pull/13965)
添加了**实验性** 命令行界面标志，用于缓存 `lean` 的详细状态，用于跨调用的进程内增量：
* `--incr-save FILE` 写入完整快照，包括导入后和运行结束时每个命令后的状态
* `--incr-load FILE` 在启动时重用这样的快照，直到第一个语法差异点，就像语言服务器中的增量一样
* `--incr-header-save FILE` 编写更便宜且更小的仅导入快照

```
