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
open Lean.MessageSeverity

#doc (Manual) "精益4.31.0 (2026-06-13)" =>
%%%
tag := "release-v4.31.0"
file := "v4.31.0"
%%%

在此版本中，发生了 305 项更改。
除了新增的 105 项功能外，
以及下面列出的 102 个修复，
有 17 处重构更改，
5 项文档改进，
13 项性能改进，
对测试套件进行 15 项改进，
以及 48 个其他变化。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights"
%%%

Lean 4.31.0 是一个整合性很强的版本：除了一些新的面向用户的功能（`do` 块细化、Lake 内置 linting 和更丰富的编辑器悬停）之外，它还付出了巨大的协调努力，使定义平等检查正确尊重透明度级别、更快和重新实现的 `mvcgen'`、包括 HTTP 在内的库的重大开发，以及包括 LLVM 22 升级在内的广泛性能工作。

_此亮点部分由 Juanjo Madrigal 贡献。_

## `do` 符号：新循环形式和新阐述器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--do--Notation___-New-Loop-Forms-and-New-Elaborator"
%%%

`do` 块中的 `while` 条件现在接受 `if` ([#13534](https://github.com/leanprover/lean4/pull/13534)) 已允许的任何条件形式。除了 `while c do …` 和 `while h : c do …` 之外，您现在还可以匹配模式，与 `:=` 或 `←` 绑定：

```
while let some x := stack.pop? do
  process x

while let .ok line ← readLine? do
  handle line
```

`repeat`/`while` 循环也变得*可验证*（[#13209](https://github.com/leanprover/lean4/pull/13209)）。 `whileM` 是 `Lean.Loop.forIn` 的对应项，它承认一步展开引理 `whileM_eq`。现有的 `repeat`/`while` 循环现在可以在不更改源的情况下通过 `whileM` 进行扩展，并且随附的 `@[spec]` 定理允许 `mvcgen`/`mvcgen'` 在给定终止措施和不变量的情况下释放循环体。另请参见 [#13689](https://github.com/leanprover/lean4/pull/13689) / [#13442](https://github.com/leanprover/lean4/pull/13442) / [#13447](https://github.com/leanprover/lean4/pull/13447)。

与此同时，新的 `do` 阐述器（可通过 `set_option backward.do.legacy false` 访问）也在开发中：除了可扩展性之外，它已经产生了更精确、更可操作的诊断：

```lean (name := newDo)
set_option backward.do.legacy false in
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput newDo (severity := warning)
This `do` element and its control-flow region are dead code. Consider removing it.
```

相反，遗留的阐述器拒绝了相同的程序，但有一个更粗略的、纯粹的结构错误：

```lean +error (name := oldDo)
set_option backward.do.legacy true in
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput oldDo (severity := error)
must be last element in a `do` sequence
```

相关开发在[#13404](https://github.com/leanprover/lean4/pull/13404) / [#13542](https://github.com/leanprover/lean4/pull/13542) / [#13491](https://github.com/leanprover/lean4/pull/13491) / [#13494](https://github.com/leanprover/lean4/pull/13494) / [#13502](https://github.com/leanprover/lean4/pull/13502) / [#13506](https://github.com/leanprover/lean4/pull/13506) / [#13486](https://github.com/leanprover/lean4/pull/13486) / [#13397](https://github.com/leanprover/lean4/pull/13397) / [#13396](https://github.com/leanprover/lean4/pull/13396) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13413](https://github.com/leanprover/lean4/pull/13413) / [#13434](https://github.com/leanprover/lean4/pull/13434) / [#13437](https://github.com/leanprover/lean4/pull/13437) / [#13507](https://github.com/leanprover/lean4/pull/13507) / [#13255](https://github.com/leanprover/lean4/pull/13255) / [#13250](https://github.com/leanprover/lean4/pull/13250)。

## Monadic 程序验证：`mvcgen'`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Monadic-Program-Verification___--mvcgen___"
%%%

单元验证框架的工作仍在继续。 [#12965](https://github.com/leanprover/lean4/pull/12965) 引入了推理一元精益代码的新基础，将一元霍尔三元组的前置/后置条件的断言语言从 `SPred` 推广到任何 `CompleteLattice`，分离终止路径和突然路径的后置条件，并解决了几个全域多态性问题。

在此基础上，[#13644](https://github.com/leanprover/lean4/pull/13644) 添加了实验性 `mvcgen'` 策略，这是在新的基于 `SymM` 的符号评估框架上从头开始重新实现 `mvcgen`。在某些综合基准测试中，它的性能比 {tactic}`mvcgen` 强 100 倍以上，并且渴望实现功能完整。 `mvcgen'` 也可以用作交互式 `sym => …` 块内的步骤，其中剩余的验证条件成为后续 `grind` 步骤 ([#13680](https://github.com/leanprover/lean4/pull/13680)) 的子目标。

## 透明度和 Defeq 纪律
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Transparency-and-Defeq-Discipline"
%%%

此版本的一个跨领域主题是使定义相等检查正确尊重“透明度”：在决定两个术语是否“定义相等”时，精益如何积极地展开定义。普通的 `def` 在 `.default` 透明度下对其主体进行 defeq，但 `simp`/`dsimp` 在较低的 `.reducible` 级别上运行，在那里它不会展开：

```lean +error
def x : Nat := 5

-- `rfl` checks defeq at `.default` transparency, so it closes the goal:
example : x = 5 := rfl

-- 但 `with_reducible` （其中 `simp`/`dsimp` 运行）不会展开它：
example : x = 5 := by with_reducible refl

-- 并且 `simp`/`dsimp` 也不起作用：
example : x = 5 := by simp
```

以前，这种透明度不匹配的情况很常见，而且很难诊断。通常的解决方法是通过将常量标记为 `@[reducible]` 来让常量在较低透明度下展开：

```lean (name := defeqFix)
@[reducible] def y : Nat := 5
example : y = 5 := by with_reducible rfl
example : y = 5 := by simp
```

*迁移：*如果证明在更严格的制度下被破坏，最常见的修复是将 `set_option backward.defeqAttrib.useBackward true in` 范围扩展到受影响的声明上，将 `simpa using` 切换到 `simpa using!`，标记相关常量 `@[implicit_reducible]`，或将现在需要的投影显式添加到 `simp`/`dsimp` 调用中。上述诊断（以及 `set_option diagnostics true` 和 `set_option trace.diagnostics true`）有助于找到受影响的点。

相关开发：[#13492](https://github.com/leanprover/lean4/pull/13492) / [#13363](https://github.com/leanprover/lean4/pull/13363) / [#13281](https://github.com/leanprover/lean4/pull/13281) / [#13512](https://github.com/leanprover/lean4/pull/13512) / [#13636](https://github.com/leanprover/lean4/pull/13636) / [#13833](https://github.com/leanprover/lean4/pull/13833) / [#13317](https://github.com/leanprover/lean4/pull/13317) / [#13368](https://github.com/leanprover/lean4/pull/13368) / [#13793](https://github.com/leanprover/lean4/pull/13793) / [#13280](https://github.com/leanprover/lean4/pull/13280) / [#13768](https://github.com/leanprover/lean4/pull/13768) / [#13772](https://github.com/leanprover/lean4/pull/13772)。

## 弃用模块、语法和选项
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Deprecating-Modules___-Syntax___-and-Options"
%%%

此版本为库作者添加了一系列工具来管理弃用：

- [#13002](https://github.com/leanprover/lean4/pull/13002) 添加了 `deprecated_module` 命令，将当前模块标记为已弃用；进口商收到建议更换的警告。 `#show_deprecated_modules` 命令列出环境中已弃用的模块。

  ```
  deprecated_module "use NewModule instead" (since := "2026-03-30")
  ```

- [#13108](https://github.com/leanprover/lean4/pull/13108) 添加了一个 `deprecated_syntax` 命令，该命令将语法类型标记为已弃用，并在详细说明已弃用的语法（包括通过宏扩展）时发出 linter 警告。
- [#13195](https://github.com/leanprover/lean4/pull/13195) 允许将选项标记为已弃用，并在 `set_option` 使用时发出警告（由 `linter.deprecated.options` 控制）。

一组相关的新 linter 会警告冗余修饰符：`linter.redundantVisibility` 表示与默认值 ([#13132](https://github.com/leanprover/lean4/pull/13132)) 匹配的 `private`/`public`，`linter.redundantExpose` 表示无操作 `@[expose]`/`@[no_expose]` ([#13359](https://github.com/leanprover/lean4/pull/13359))，以及针对带有变量或无法识别的 `@[simp]` 定理的警告头部符号 ([#13325](https://github.com/leanprover/lean4/pull/13325))。

## Lake：内置 Linting
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Lake___-Built-in-Linting"
%%%

Lake 获得了内置的 linting 框架，可通过 `lake lint` 标志（[#13393](https://github.com/leanprover/lean4/pull/13393)、[#13431](https://github.com/leanprover/lean4/pull/13431)）访问。它附带了来自 Batteries/Mathlib 上游的环境 linter（`defLemma`/`defProp`、`checkUnivs`） - 另请参阅 [#13356](https://github.com/leanprover/lean4/pull/13356) 中的核心上游 - 以及 `builtinLint` 包配置选项。标志包括 `--builtin-lint`、`--builtin-only`、`--clippy`、`--lint-all` 和 `--lint-only <name>`，并且 `@[builtin_nolint]` 属性抑制每个声明的特定 linter。

[#13513](https://github.com/leanprover/lean4/pull/13513) 通过将警告保留到每个模块的 `.olean` 中，将其扩展到 *text* linter，而 [#13843](https://github.com/leanprover/lean4/pull/13843) 使模块系统目标检查其公共表面，与下游消费者所看到的相匹配。

## 性能
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Performance"
%%%

此版本包括广泛的性能工作：

- [#13545](https://github.com/leanprover/lean4/pull/13545) 将捆绑编译器工具链从 LLVM 19 升级到 LLVM 22，根据基准测试，指令总体改进高达 5%。
- [#13788](https://github.com/leanprover/lean4/pull/13788) 为已知形状的值生成专门的 `dec` 代码，[#13669](https://github.com/leanprover/lean4/pull/13669) 优化 `lean_dec_ref_cold` 冷路径。
- [#13796](https://github.com/leanprover/lean4/pull/13796) 将 `String.compare` 简化为单个 `memcmp`，并且 [#13235](https://github.com/leanprover/lean4/pull/13235) 使用 `memcmp` 来实现 {name}`ByteArray` 相等。
- [#13651](https://github.com/leanprover/lean4/pull/13651) 将战术配置阐述系统替换为直接构造配置对象并可以完全跳过术语阐述的系统；配置评估现在花费的时间大约是以前的 6.2%。新系统还支持 {tactic}`simp` （例如 `(user.optionName := …)`）的自定义配置语法和用户配置选项。
- Elaboration 本身对于具有许多字段的结构实例表示法 ([#13760](https://github.com/leanprover/lean4/pull/13760)) 和常见情况下的 `Expr.instantiateBetaRevRange` ([#13758](https://github.com/leanprover/lean4/pull/13758)) 来说更快。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Library-Highlights"
%%%

上一个版本引入的标准 HTTP 库成长为工作服务器：[#12146](https://github.com/leanprover/lean4/pull/12146) 添加了 `H1` 纯 HTTP/1.1 状态机，[#12151](https://github.com/leanprover/lean4/pull/12151) 添加了异步 HTTP/1.1 `Server`。重要的是，[#13511](https://github.com/leanprover/lean4/pull/13511) 将 `Async` 和 `Http` 模块从 `Internal` 升级到 `Std`。

其他值得注意的库添加：

- 日期/时间获得本地时间点的 `WallTime` 类型和简化的 `Timestamp` API ([#13675](https://github.com/leanprover/lean4/pull/13675))，以及用于可配置格式的 `Locale`/`LocaleSymbols` ([#13567](https://github.com/leanprover/lean4/pull/13567))。
- `List.prod`/`Array.prod`/`Vector.prod` 镜像现有的 `sum` API，具有简化和磨削引理 ([#13200](https://github.com/leanprover/lean4/pull/13200))。
- 更多 {name}`ByteArray` `push`/`set!` 引理 ([#13457](https://github.com/leanprover/lean4/pull/13457)) 和 `Vector` 附加引理推广到不同大小的向量 ([#13693](https://github.com/leanprover/lean4/pull/13693))。
- 验证 `String.dropWhile`/`String.takeWhile` 继续字符串验证工作 ([#13155](https://github.com/leanprover/lean4/pull/13155))。

许多运行时稳健性修复还将以前无声的内存耗尽故障转变为正确的错误或恐慌，而不是段错误和损坏（[#13392](https://github.com/leanprover/lean4/pull/13392)、[#13546](https://github.com/leanprover/lean4/pull/13546)、[#13547](https://github.com/leanprover/lean4/pull/13547)、[#13548](https://github.com/leanprover/lean4/pull/13548)、[#13549](https://github.com/leanprover/lean4/pull/13549)、[#13521](https://github.com/leanprover/lean4/pull/13521)）。对于安全敏感的部署，[#13401](https://github.com/leanprover/lean4/pull/13401) 添加了 `LEAN_MI_SECURE` 构建选项，可实现额外的 mimalloc 内存安全缓解。

## 编辑器和用户体验改进
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Editor-and-UX-Improvements"
%%%

[#13260](https://github.com/leanprover/lean4/pull/13260) 添加了对*增量诊断*的服务器端支持。以前，在处理文件时报告诊断需要每次重新发送全套数据，这是文件处理过程中工作量的二次方。宣传 `incrementalDiagnosticSupport` 的客户现在会收到 `PublishDiagnosticsParams.isIncremental` 标志，告诉他们追加而不是替换，从而消除了二次报告。 VS Code 扩展的客户端实现在 [vscode-lean4#752](https://github.com/leanprover/vscode-lean4/pull/752) 中跟踪。

元变量 ([#13446](https://github.com/leanprover/lean4/pull/13446)) 和悬停 ([#13728](https://github.com/leanprover/lean4/pull/13728) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13678](https://github.com/leanprover/lean4/pull/13678) / [#13715](https://github.com/leanprover/lean4/pull/13715)) 的显示也有重大发展。

## 重大变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Breaking-Changes"
%%%

除了上述与透明度相关的更改外，请注意以下事项：

- [#13807](https://github.com/leanprover/lean4/pull/13807) 使应用程序精译器 beta-reduce 参数，同时将它们替换为以后预期的类型，与 `inferType` 和 `instantiateMVars` 一致。 *重大更改：*一些策略证明可能需要删除不必要的步骤，例如`dsimp only` 以前仅存在的步骤用于执行这些 beta 减少。相关地， [#13528](https://github.com/leanprover/lean4/pull/13528) 更改元变量簿记，以便元程序不再仅仅因为分配了元变量而假设 `MVarId` 发生更改（例如，当 `change` 的唯一效果是偶然分配时，`change` 不再更改 `MVarId` ）；它还揭示了许多 `dsimp` 没有执行任何操作并且可以删除。
在*以模式*阐述结构实例符号时，- [#13243](https://github.com/leanprover/lean4/pull/13243)不再应用结构的默认值（例如`s matches { x := 1 }`）。 *重大更改：*此类模式现在可能会报告“字段缺失”错误，并且需要提供缺失的字段或添加 `..` 。
- [#13476](https://github.com/leanprover/lean4/pull/13476) 在计算 `apply`/`rewrite` 子目标标签之前过滤分配的元变量，因此单个剩余目标现在继承输入目标的标签。 *重大更改：*依赖先前标签名称的脚本（例如 `funext` 之后的 `case h => …`）可能需要更新。
- [#13030](https://github.com/leanprover/lean4/pull/13030) 更改级别元变量漂亮打印以使用每个定义索引。 *破坏性元编程更改：*级别漂亮打印应使用 `delabLevel` 或 `MessageData.ofLevel`； `format`/`toString` 无法访问索引，并将原始内部标识符打印为 `?_mvar.nnn`。由于索引记录分配，一些测试需要 `maxHeartbeats` 提高 20-50%。
- [#13627](https://github.com/leanprover/lean4/pull/13627) 将 `UInt8.ofNatTruncate` 重命名为 `UInt8.ofNatClamp` （以及其他宽度变体），以便与 `UIntX` API 的其余部分保持一致。
- [#13516](https://github.com/leanprover/lean4/pull/13516) 将缺少的 `namespace Lake` 添加到 `Lake.Util.Opaque` 中；必须更新引用 `Opaque` 而没有 `open Lake` 的代码。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Language"
%%%

````markdown

- [#13803](https://github.com/leanprover/lean4/pull/13803)
  将 `defLemma` linter 重命名为 `defProp` 并澄清
  它的警告消息。

- [#13862](https://github.com/leanprover/lean4/pull/13862)
  将错误消息改进从 #10488 更新为在提供改进的消息时还检查标识符转义字符。之前，它仅检查标识符起始字符。

- [#13853](https://github.com/leanprover/lean4/pull/13853)
  通过模块使 `lake lint --builtin-lint` 组保存文本 linter 诊断
  产生它们的，而不是在
  顶级模块被检查。每个贡献子模块现在都有自己的
  `-- Text linter diagnostics in <module>:` 标头，镜像如何
  环境 linter 方面已经对结果进行了分组。

- [#13844](https://github.com/leanprover/lean4/pull/13844)
  使 `Lean.Linter.logLint` 将内部标签附加到每个
  linter 警告，以便 `Lean.Linter.recordLints` 能够可靠地区分
  linter 从其他标记消息生成的消息（命名错误，
  未知标识符消息、`hasSorry` 标记等）。之前，
`recordLints` 捕获了顶级类型为非匿名的每条消息，
  它将非 linter 诊断过度记录到持久 lint 日志中。

- [#13752](https://github.com/leanprover/lean4/pull/13752)
  使得投影符号错误总是在适用时提及父结构上的私有声明作为原因。以前，对于通过结构继承解决的投影，提示会被默默地忽略，使用户无法得知实际原因。

- [#13813](https://github.com/leanprover/lean4/pull/13813)
  修复了 `beforeElaboration` 属性未在 `inductive`/`structure`/`coinductive` 命令上运行的问题。关闭#13433。

- [#13811](https://github.com/leanprover/lean4/pull/13811)
  更新 `#where` 命令以便能够报告 `module` 相关范围状态，例如输出中的 `@[expose] public meta section` 行。

- [#13760](https://github.com/leanprover/lean4/pull/13760)
  提高了具有大量字段的结构实例表示法的精细化性能。它还使用结构参数的 beta 减少替换，这已经是结构字段的情况。

- [#13807](https://github.com/leanprover/lean4/pull/13807)
  将应用程序阐述器修改为 beta 减少参数，同时将它们替换为后续参数的预期类型。这使得它与 `inferType` 和 `instantiateMVars` 一致，这两个测试版都减少了替换。特别是，此更改可确保应用程序阐述器的行为就像为每个参数创建元变量并将详细参数分配给元变量一样。 **重大变化：**可能需要修改策略证明以删除不必要的步骤，例如`dsimp only` 之前用于减少 beta 的步骤。

- [#13808](https://github.com/leanprover/lean4/pull/13808)
  强制 Verso 文档字符串扩展在属性应用程序时应始终是元的，从而提供更好的错误消息，并确保生成的参数解析器帮助程序也是元的并且具有相同的可见性。

- [#13801](https://github.com/leanprover/lean4/pull/13801)
  向 `DoOps`、`splitMonadApp?` 和 `mkMonadApp` 添加两个新字段，以便 `elabDoWith` 的调用者可以使用默认 `m α` 分解无法处理的索引 monad（其中 `Measure : (α : Type u) → [MeasureSpace α] → Type u` 携带实例参数）。现有行为移至 `DoOps.default`。

- [#13800](https://github.com/leanprover/lean4/pull/13800)
  将 `do` 阐述器的 `mkMonadicType` 重命名为 `mkMonadApp`，使其与 `DoOps` 中现有的 `mkPureApp` / `mkBindApp` 命名约定保持一致。

- [#13780](https://github.com/leanprover/lean4/pull/13780)
  是 #13779 的第 2 部分。它完成了配置评估元程序到内置阐述器的转变。

- [#13779](https://github.com/leanprover/lean4/pull/13779)
  使用于配置评估元编程的命令阐述器成为内置的，以避免由于解释器在运行所有内置初始化程序之前评估阐述器的大部分而导致核心 Lean 中的引导 ABI 问题。 （这是第 1 部分；#13780 将在 stage0 更新后应用。）

- [#13762](https://github.com/leanprover/lean4/pull/13762)
  对函数应用程序阐述器进行了一些重构，并改进了 `trace.Elab.app` 跟踪。它还通过更仔细地将参数替换为函数的类型以及更改命名参数依赖抑制的实现方式来提高渐近复杂性。对于点表示法，它现在直接构建基本投影，而不是使用应用程序阐述器。它修复了 eta args 功能中的一个错误，即比预期更显式的参数将转换为隐式参数，并且它通过遵循主应用程序阐述器的规则来改进预期的类型传播。

- [#13772](https://github.com/leanprover/lean4/pull/13772)
通过在 `Config.toKey` 中包含 `Config.zetaUnused` 来关闭 https://github.com/leanprover/lean4/issues/13770。如果没有这个，两个仅在 `zetaUnused` 方面不同的配置共享 `WHNF`/`isDefEq` 缓存键，因此可以为另一种设置返回在一种设置下执行的减少。新位位于位置 22，紧邻 `zetaHave` 上方。

- [#13768](https://github.com/leanprover/lean4/pull/13768)
  修复了 `Meta.Config.toKey` 和 `Context.setTransparency` 中长期存在的错误，其中 `TransparencyMode` 仅打包到缓存键的 2 位中，即使它有 5 个构造函数（`.all`、`.default`、`.reducible`、`.instances`、`.none`）。 `.none` 情况（值 `4`，即 `0b100`）与 `foApprox` 位重叠，因此仅透明度与 `foApprox` 不同的配置可能会在 `isDefEq`/`WHNF` 缓存中发生冲突，并且在切换到 `.none` 或从 `.none` 切换时，`Context.setTransparency` 会损坏相邻位。

- [#13763](https://github.com/leanprover/lean4/pull/13763)
  添加 `MessageData.withExprHover`，用于创建在鼠标悬停时显示有关表达式的信息的消息。 `withExprHoverM` 变体捕获当前本地上下文。

- [#13758](https://github.com/leanprover/lean4/pull/13758)
  改进了 `Expr.instantiateBetaRevRange` 在 lambda 函数未实例化的常见情况下更加高效，并且增加了应用程序中的表达式共享。

- [#13737](https://github.com/leanprover/lean4/pull/13737)
  将 `--plugin` 中插件文件名和初始化函数之间的分隔符从 `:` 更改为 `=`。这可以防止与 Windows 上驱动器前缀中的 `:` 发生冲突。

- [#13651](https://github.com/leanprover/lean4/pull/13651)
  用一种更高效、支持自定义配置语法和处理的系统取代了以前的策略配置系统。在简单的基准测试中，配置评估所需的时间是以前的 6.2%。 `declare_config_elab` 命令生成一个配置阐述器，现在可以直接构造配置对象；以前它依赖于 `Meta.evalExpr'`，它涉及通过完整的术语阐述、编译和评估过程来运行配置。生成的配置阐述器现在还能够在常见情况下进行直接 `Syntax` 评估，跳过术语阐述。此外，阐述器更自由地接受配置：接受具有 `optConfig` 样式配置或配置项（包括例如 `namedArgument`s）形式的任何用户定义语法。导入`Lean.Elab.ConfigEval`即可使用系统；除了 `Lean.Elab.ConfigEval.Commands` 中的文档字符串之外，请参阅此模块以获取一些文档。此外，`simp` 策略现在还具有 `(user.optionName := ...)` 用户配置选项，可以使用全局 `tactic.simp.user.optionName` 选项进行声明；使用 `getUserConfigOption` 和 `withUserConfig` 在元程序中访问和设置它们。

- [#13550](https://github.com/leanprover/lean4/pull/13550)
  改进了 `checkImpossibleInstance` 函数的逻辑和性能，以检测更多不可能的参数
  推断类型类合成。它还改进了 `checkImpossibleInstance` 和 `checkNonClassInstance` 的错误消息的格式，使其更具可读性。

- [#13730](https://github.com/leanprover/lean4/pull/13730)
  修复了 #7166 中引入的回归，其中在固定和变化之后
  参数被允许重新排序，三个地方
  `Lean.Elab.Structural.FindRecArg` 仍然索引连接 `xs ++ ys`
  与 `recArgInfo.recArgPos` 即使 `recArgPos` 指的是原始
  参数顺序。固定参数与结构交错
参数，这选择了错误的元素：错误消息命名错误
  参数，而 `argsInGroup` 的嵌套归纳识别被默默拒绝
  否则有效的相互定义。

- [#13728](https://github.com/leanprover/lean4/pull/13728)
  改进了结构实例符号中复合字段名称的悬停和完成。以前，像 `x.fst` 这样的字段只有与附加到整个语法的 `x` 相关的信息，但现在 `x` 和 `fst` 是分开处理的。

- [#13715](https://github.com/leanprover/lean4/pull/13715)
  通过将可能令人困惑的“未使用的变量 `x`”消息替换为“未显式引用变量名称 `x`。可以删除绑定（如果未使用）或命名为 `_`（如果隐式使用）”，改进了 `unusedVariables` linter 的消息。

- [#13710](https://github.com/leanprover/lean4/pull/13710)
  使仅测试的 `waitForMessage` 帮助程序立即中止
  当精益语言服务器报告 fatalError 时，而不是
  阻塞直到外部测试框架超时终止进程。

- [#11313](https://github.com/leanprover/lean4/pull/11313)
  确保 `withSetOptionIn` 不会修改信息树或错误选项值的错误，从而避免使用 `visitM` 遍历信息树的 linter 中出现恐慌。

- [#13595](https://github.com/leanprover/lean4/pull/13595)
  消除本身已弃用的定义内的 `Linter.deprecated` 警告。

- [#13209](https://github.com/leanprover/lean4/pull/13209)
  添加 `whileM`，与 `Lean.Loop.forIn` 相对应，承认一步展开引理 `whileM_eq`（无法证明原始 `partial def`）。 `Lean.Loop.forIn` 现在扩展为 `whileM`，因此 `repeat`/`while` 无需更改源代码即可继续工作，并且 `Spec.whileM`/`Spec.forIn_loop` `@[spec]` 定理让 `mvcgen` 在给定 Nat 变体和 `α ⊕ β` 不变量的情况下释放其身体。

- [#13670](https://github.com/leanprover/lean4/pull/13670)
  向 Verso 文档字符串添加了对块引用的支持，这在之前是缺失的。它还大大提高了文档字符串的 Verso->Markdown 渲染的稳健性，尤其是块引用行前缀的处理。

- [#13663](https://github.com/leanprover/lean4/pull/13663)
  取代了使用的 `check_cancel` 双向协调协议
  `tests/server_interactive/cancellation_par.lean` 使用单一策略
  __修复000__。标签寄存器的第一次调用
  一个承诺，打印 `<label>: blocked`，并在 `Core.checkInterrupted` 上循环
  直到取消令牌触发（然后 `finally` 解决承诺）。稍后
  对同一标签的调用等待该承诺 - 因此仅测试
如果第一次调用实际上退出了循环，则终止。如果取消
  无法传播，第二次调用的 `IO.wait` 永远阻塞，并且
  测试挂起（超时=失败），没有错误的成功路径。

- [#13548](https://github.com/leanprover/lean4/pull/13548)
  修复了从内存耗尽中恢复时可能出现的损坏。

- [#13613](https://github.com/leanprover/lean4/pull/13613)
  当注册 `foo` 的模块没有明显导入到当前文件中而只是作为 IR 加载时，使精译器拒绝 `@[foo]`。以前，此类使用默默地进行了阐述，但导致了 cmdline 和服务器行为的分歧，并导致 `lake shake --fix` 在连续运行时发生翻转 (#13599)。

- [#13510](https://github.com/leanprover/lean4/pull/13510)
  添加了在加载时为 Lean 插件的初始化函数指定名称的功能。

- [#13645](https://github.com/leanprover/lean4/pull/13645)
  修复了终止检查器报告错误的错误
  当函数包含结构相同时的递归调用站点
  不同源位置的递归调用。

- [#13547](https://github.com/leanprover/lean4/pull/13547)
  防止在不使用 GMP 时导致内存损坏的静默分配失败。

- [#13596](https://github.com/leanprover/lean4/pull/13596)
  修复了私有（导入的）默认实例在公共签名中意外使用而导致后续错误的问题。

- [#13574](https://github.com/leanprover/lean4/pull/13574)
  通过在详细者之间共享更多代码，确保 Verso 文档字符串和 Verso 模块文档之间元变量行为的一致性。它还改进了防止元变量泄漏时的错误消息。

- [#13528](https://github.com/leanprover/lean4/pull/13528)
  赋予 `specialize` 策略实例化通用量词的能力，而不是使用 `specialize h (y := v)` 语法的第一个量词。它还修复了 `MVarId.assertAfter` 未记录变量别名信息的问题，以及 `MVarId.replace` 和 `MVarId.replaceLocalDecl` 在计算依赖项时未考虑元变量的问题。此外，它还修复了一些未实例化的元变量错误，包括 Infoview 策略状态假设差异中的错误。

- [#13428](https://github.com/leanprover/lean4/pull/13428)
  修复了当服务器取消重新阐述时并行策略组合器（`attempt_all_par`、`first_par`）泄漏其子任务的问题。通过 `CoreM.asTask` （及其 `MetaM`/`TermElabM`/`TacticM` 变体）生成的子任务会获得一个新的 `IO.CancelToken`，它以前没有到父令牌的链接； `cancelRec` 将设置命令级令牌，但子级继续运行。

- [#13569](https://github.com/leanprover/lean4/pull/13569)
  解决了 `IO.CancelToken` 上的两个审查点：

  * `set` 现在*在*编写 `Bool` 之前解决了底层承诺
    快速路径标志，因此观察 `isSet = true` 意味着任何同步
    链式 `onSet` 回调已经运行。前一个顺序（首先标记，
然后解决）是一个微妙的枪：代码看到 `isSet = true` 不能
    依赖已触发的取消任务。
  * 底层承诺及其产生的任务是保密的。的
    先前的 `task : Task (Option Unit)` 访问器被删除；消费者应该
    使用 `onSet` 对取消做出反应。对结构记录的评论
    将来重新公开该任务需要重新审核订单
    在 `set` 中，用于承诺和 `Bool` 标志之间的竞争。

- [#13303](https://github.com/leanprover/lean4/pull/13303)
  将 `IO.CancelToken` 从 `Init.System.IO` 移动到其自己的文件 `Init.System.CancelToken`，由 `IO.Promise Unit` 而不是 `IO.Ref Bool` 支持。这可以实现非轮询取消传播：令牌的底层承诺可以直接与 `IO.waitAny` 一起使用，并且可以注册回调以在请求取消时触发。

- [#13542](https://github.com/leanprover/lean4/pull/13542)
  将新的 `do` 阐述器针对典型模式错误（#2215、#8304、#10393）产生的包罗万象的“语法匹配中不支持的模式”错误替换为来自常规模式变量收集器的正确诊断（例如“无效模式：需要用 `[match_pattern]` 标记的构造函数或常量”、“不明确的模式，使用完全限定名称”），指向有问题的模式。

- [#13359](https://github.com/leanprover/lean4/pull/13359)
  添加 `linter.redundantExpose` 选项（默认 `true`），当 `@[expose]` 或 `@[no_expose]` 属性无效时发出警告：

`abbrev` 上的   - `@[expose]` （始终暴露）或非 Prop `instance` （始终暴露）
  - `@[expose]` 位于 `@[expose] section` 内的 `def` 上（已由该部分公开）
非 `module` 文件中的   - `@[expose]`/`@[no_expose]` （无模块系统）
  - `@[no_expose]` 位于默认情况下不会公开的声明上

- [#13492](https://github.com/leanprover/lean4/pull/13492)
  引入了对 `@[defeq]` 属性的更严格的推断和
  保留 PR 前行为的同伴 `@[backward_defeq]` 属性
  作为选择加入。

- [#13534](https://github.com/leanprover/lean4/pull/13534)
  概括了 `do` 块中的 `while` 语法，以便条件可以是任何 `doIfCond`，与 `if` 已接受的条件形式相同。因此，除了 `while cond do …` 和 `while h : cond do …` 之外，现在还支持 `while let pat := e do …` 和 `while let pat ← e do …`。之前单独的 `doWhile` 和 `doWhileH` 解析器及其附带的宏被统一为一个 `doWhile` 解析器，其宏委托给现有的 `doIf` 脱糖。

- [#13523](https://github.com/leanprover/lean4/pull/13523)
允许策略宏和详细说明者选择在失败时不自动回退到以前的宏/elab。 `throwUnsupportedSyntax` 不受影响。

- [#13363](https://github.com/leanprover/lean4/pull/13363)
  将 `whnfMatcher` 中从 `.reducible` 到 `.instances` 的透明度凹凸替换为 `canUnfoldAtMatcher` 中的显式允许列表。以前，在减少匹配判别式时，`whnfMatcher` 将展开所有 `implicitReducible` 定义和所有 `fromClass` 投影。这使得不可能在不默默影响匹配减少行为的情况下将定义标记为 `implicit_reducible` 。

- [#13512](https://github.com/leanprover/lean4/pull/13512)
  更改方程定理生成机制中要使用的 `whnfAux`
  可简化透明度 (`whnfR`) 而不是实例透明度 (`whnfI`)。
  以前，`Eqns.go` 中的循环会在 LHS 上展开实例，这
  与将 `dite`/`ite` 标记为 `implicit_reducible` 的用户交互不良：
  方程生成会减少超过 `dite` 并陷入困境而不是
  致力于分支。 `whnfI` 的最初动机（减少
  数字文字上 `match` 的 `Nat.rec ... (OfNat.ofNat 0)` 残差）是
  已经被周围的 `simpMatch?`/`simpIf?`/`simpTargetStar` 覆盖
  `Eqns.go` 中的步骤，因此完整的测试套件继续通过。

- [#13506](https://github.com/leanprover/lean4/pull/13506)
  当预期结果类型与 `PUnit` 不统一时，将 `unreachable!` 追加到 `break`-less `repeat` 的扩展中。然后，延续具有多态值，因此无需用户编写填充符即可推断出封闭的 do 块的结果类型，并且 `ControlInfo` 表示无中断 `repeat` 可以诚实地报告 `noFallthrough` — 后续元素上的死代码警告现在是可操作的。

- [#13507](https://github.com/leanprover/lean4/pull/13507)
  将 `do` 阐述器发出的 `Pure.pure` / `Bind.bind` 应用程序公开为可插入闭包，因此外部表面语法（例如索引单子的 `ido` 表示法）可以在发出备用常量时重用完整的 `do` 机制。

- [#13491](https://github.com/leanprover/lean4/pull/13491)
  修复了 do-block `match` 的 `ControlInfo` 推论：匹配臂的折叠从 `ControlInfo.pure` 开始（默认为 `numRegularExits := 1`、`noFallthrough := false`），但 `alternative` 与 `numRegularExits` 和 `noFallthrough` 相加，因此折叠标识为 `{ numRegularExits := 0, noFallthrough := true }`。由于基地错误，一个手臂全部为 `break`/`continue`/`return` 的 `match` 报告了 `numRegularExits = 1` 和 `noFallthrough = false`，抑制了比赛后继续的死代码警告。该修复更正了 `InferControlInfo.lean` 中的推理处理程序和 `elabDoMatchCore` 中的折叠。

- [#13502](https://github.com/leanprover/lean4/pull/13502)
  将 `ControlInfo` 的死码信号一分为二。 `numRegularExits` 现在纯粹是语法上的：块将其延续连接到详细表达式中的次数，由 `withDuplicableCont` 作为连接点复制触发器 (`> 1`) 使用。新的 `noFallthrough : Bool` 断言封闭序列中的下一个 doElem 在语义上是不相关的； `false` 没有断言。不变式：`numRegularExits = 0 → noFallthrough`；反之则不成立。 `sequence` 派生 `noFallthrough := a.noFallthrough __FIX000____FIX001__ b.noFallthrough` （并无条件聚合语法字段）； `alternative` 将其派生为 `a.noFallthrough && b.noFallthrough`。 `withDuplicableCont` 和 `ControlLifter.ofCont` 中的死代码警告门现在读取 `noFallthrough`。

- [#13494](https://github.com/leanprover/lean4/pull/13494)
阻止 `repeat` 推理处理程序报告 `numRegularExits := 0` 对于无中断主体。对于无中断的 `repeat` ，循环永远不会正常终止，因此 `0` 在语义上看起来更准确，但循环表达式仍然具有类型 `m Unit` ，并且循环后的 do 块的延续是携带该类型的。报告 `0` 会使精译器将该延续标记为死代码，但用户无法删除类型正确的它 — 除非封闭的 do 块的单子结果类型恰好是 `Unit`。将 `numRegularExits` 固定在 `1` （匹配 `for ... in`）可以消除这些虚假警告。

- [#13489](https://github.com/leanprover/lean4/pull/13489)
  修复了当存在没有标题的文档注释时 Verso Docstrings 中的嵌套级别被遗忘的错误。

- [#13486](https://github.com/leanprover/lean4/pull/13486)
  修复 `inferControlInfoSeq` 和 `ControlInfo.sequence` 以继续聚合 `breaks`/`continues`/`returnsEarly`/`reassigns` 过去的 `ControlInfo` 报告 `numRegularExits := 0` 的元素。以前，分析在这些元素处短路，因此推断信息中缺少任何尾随 `return`/`break`/`continue` 。精化框架仅在语法上跳过顶级 `return`/`break`/`continue` 的后续 doElem；对于每个其他 `numRegularExits == 0` 情况（例如，分支全部终止的 `match`/`if`/`try`，或没有 `break` 的 `repeat`），阐述器会继续访问延续，然后 for/match 阐述器会使用 `Early returning ... but the info said there is no early return` 触发其不变检查。通过此更改，推断的信息与精译器实际看到的内容相匹配，这也消除了对 #13479 中引入的 `repeat` 上的 `numRegularExits := 1` 解决方法的需要。

- [#13477](https://github.com/leanprover/lean4/pull/13477)
  修复了 #13475 中引入的基准回归：`eqnOptionsExt`
  正在使用 `.async .asyncEnv` asyncMode，它会在
  `checked` 环境并且可以阻止。切换到 `.local` — 一致
  与相邻的 `eqnsExt` 和其他声明缓存
  `src/Lean/Meta` — 恢复性能（
  `build/profile/blocked (unaccounted) wall-clock` 板凳移动 +33%
  回到基线）。 `.local` 在这里是安全的，因为 `saveEqnAffectingOptions`
  仅在顶级 `def` 阐述和下游读者期间调用
  查看导入状态；合并非主分支上的修改
  完成后进入主分支。

- [#13475](https://github.com/leanprover/lean4/pull/13475)
  取代了由以下触发的急切方程实现
  影响方程的选项的非默认值（例如
  `backward.eqns.nonrecursive`) 与 `MapDeclarationExtension`
  在定义时存储非默认选项值。这些值是
  然后当方程被延迟实现时恢复，所以相同的方程
无论何时发生，都会产生。

- [#13367](https://github.com/leanprover/lean4/pull/13367)
  消除了 `simp` 会严重超出超时的一些情况。

- [#13447](https://github.com/leanprover/lean4/pull/13447)
  从 `Init.While` 中删除 `repeat`、`while` 和 `repeat ... until` 的过渡 `syntax` 声明，并将 `Lean.Parser.Do` 中相应的 `@[builtin_doElem_parser]` def 从 `low` 提升到默认优先级，使它们成为规范解析器。

- [#13442](https://github.com/leanprover/lean4/pull/13442)
  将 `repeat`、`while` 和 `repeat ... until` 解析器与其他 do 元素解析器一起从 `Init.While` 中的 `syntax` 声明提升到 `Lean.Parser.Do` 中的 `@[builtin_doElem_parser]` 定义。 `while` 变体和 `repeat ... until` 获得 `@[builtin_macro]` 扩展； `repeat` 本身获得一个 `@[builtin_doElem_elab]`，因此后续操作可以通过在 `Loop.mk` 和有根据的 `Repeat.mk` 之间进行选项驱动的选择来扩展它。

- [#13437](https://github.com/leanprover/lean4/pull/13437)
  为 `doRepeat` 添加内置 `doElem_control_info` 处理程序。只要我们有`repeat`的宏，它就无效。

- [#13434](https://github.com/leanprover/lean4/pull/13434)
  命名 `repeat` 语法 (`doRepeat`) 并在旧版和新版 do-elaborators 中为其安装专用的 elaborators。目前，两者都扩展为 `for _ in Loop.mk do ...`，与 `Init.While` 中现有的后备宏相同。

- [#13389](https://github.com/leanprover/lean4/pull/13389)
  向 `addInstance` 添加了两项验证检查，为实例声明中的常见错误提供早期反馈：

  1. **非类实例检查**：当实例目标类型不是类型类时出错。这捕获了为普通结构编写 `instance` 的常见错误。以前由电池 (`Batteries.Tactic.Lint.TypeClass`) 中的 `nonClassInstance` linter 处理，现在直接在声明时检查。

  2. **不可能的参数检查**：当实例具有无法通过实例合成推断的参数时出现错误。具体来说，它标记非实例隐式参数，并且不会出现在任何后续实例隐式参数或返回类型中。以前，此类实例会被默默接受，但永远无法综合。

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  修复 `processDefDeriving` 以将 `meta` 属性传播到通过增量派生派生的实例，以便 `public meta section` 内的 `deriving BEq` 生成元实例。以前，派生的 `instBEqFoo` 未标记元，并且 LCNF 可见性检查器拒绝在别名上使用 `==` 的元定义 - 这是在将 verso 升级到 v4.30.0-rc1 时出现的。

- [#13404](https://github.com/leanprover/lean4/pull/13404)
  修复了 #12846，当 do 元素的延续具有不匹配的单子结果类型时，新的 do 阐述器会产生令人困惑的错误。这些错误在位置（例如，指向 `let x ← value` 的值而不是 `let` 关键字）和内容（例如，提及用户从未编写过的 `PUnit.unit` ）上都具有误导性。

- [#13420](https://github.com/leanprover/lean4/pull/13420)
  修复了在构造函数名称带有宏作用域的宏作用域内定义 `coinductive` 谓词时出现的恐慌。现有的防护仅检查宏作用域的声明名称，缺少在宏引用内生成构造函数标识符并因此携带宏作用域的情况。这导致 `removeFunctorPostfixInCtor` 在宏范围编码的 `Name.num` 组件上出现恐慌。

- [#13413](https://github.com/leanprover/lean4/pull/13413)
为 do 块添加内部 `skip` 语法，供 `if` 和 `unless` 精译器使用，以替换隐式 else 分支中的 `pure PUnit.unit` 。这为精译器提供了一个专用的语法节点来附加更好的错误消息和位置信息，而不是合成 `pure PUnit.unit` ，后者会将内部细节泄漏到面向用户的错误中。

- [#13391](https://github.com/leanprover/lean4/pull/13391)
  在调用 `decLevel` 之前，在 `getDecLevel` 和 `getDecLevel?` 中添加关卡实例化和规范化。

- [#13395](https://github.com/leanprover/lean4/pull/13395)
  使 `structure` 的 `deriving Inhabited` 处理程序能够从结构父级继承 `Inhabited` 实例，使用与类父级相同的机制。这修复了 #9815 引入的回归，该回归失去了为表示为子对象字段的父级应用 `Inhabited` 实例的能力。有了这个 PR，现在它适用于层次结构中的所有父母。

- [#13399](https://github.com/leanprover/lean4/pull/13399)
  修复了 #12827，将鼠标悬停在 `for h : x in xs do` 中的 `for` 循环变量 `x` 和 `h` 上，在新的 do 阐述器中没有显示类型信息。该修复在 `elabDoFor` 中的 `withLocalDeclsD` 引入循环变量和成员身份证明绑定器后添加了 `Term.addLocalVarInfo` 调用。

- [#13397](https://github.com/leanprover/lean4/pull/13397)
  改进了当 `do` 阐述器生成在 `withDuplicableCont` 中失败 `checkedAssign` 的格式不正确的表达式时的错误报告。以前，失败被默默地丢弃，使得诊断 `do` 阐述器中的错误变得困难。现在抛出一个描述性错误，显示连接点 RHS 及其未能分配到的元变量。

- [#13396](https://github.com/leanprover/lean4/pull/13396)
  修复了#12768，当绑定延续的结果类型在定义上但在语法上不独立于绑定变量时，新的 `do` 阐述器产生了“声明有自由变量”内核错误。该修复将结果类型元变量的创建移至 `withLocalDecl` 之前，因此统一器必须减少依赖性。

- [#13325](https://github.com/leanprover/lean4/pull/13325)
  在注册 `@[simp]` 定理时添加警告，该定理的左侧在判别树中具有有问题的头符号：

  - **变量头**（`.star` key）：该定理将在每个 `simp` 步骤上进行尝试，这可能会很昂贵。警告指出这对于 `local` 或 `scoped` simpl 引理来说可能是可以接受的。由 `warning.simp.varHead` 控制（默认值：`true`）。
  - **无法识别的头**（`.other` 键，例如 lambda 表达式）：该定理不太可能被 `simp` 应用。由 `warning.simp.otherHead` 控制（默认值：`true`）。

- [#13390](https://github.com/leanprover/lean4/pull/13390)
  更改线性 BEq 推导策略，在比较构造函数索引时使用 `Nat.decEq` 而不是 `decEq`。由于构造函数索引始终为 `Nat`，因此直接使用 `Nat.decEq` 更合适，因为它是 `@[reducible]`，而通用 `decEq` 仅是半可约的，并且不会以 `.reducible` 透明度展开。这使得生成的代码更加透明友好。

- [#13356](https://github.com/leanprover/lean4/pull/13356)
  上游环境从电池到核心精益。

- [#13360](https://github.com/leanprover/lean4/pull/13360)
  修复了 #13268，其中深度 ≥ 3 的复合名称的 `local macro` （和其他本地声明）会默默地丢失其本地条目。

- [#13374](https://github.com/leanprover/lean4/pull/13374)
  修复了具有公共归纳类型的 `SizeOf` 实例生成
私有构造函数。规格定理证明构造需要展开
  `_sizeOf` 辅助函数可能不会在公共视图中公开，因此
  我们使用 `withoutExporting` 进行证明构造和类型检查。

- [#13239](https://github.com/leanprover/lean4/pull/13239)
  修复了 `module` 内的 `(builtin_)initialize` 不允许引用其类型中的私有定义的问题，除非显式使用 `private` 前缀。

- [#9815](https://github.com/leanprover/lean4/pull/9815)
  将 `structure` 类型的 `Inhabited` 派生处理程序更改为使用默认字段值（如果存在）；这确保当所有字段都有默认值时 `{}` 和 `default` 可以互换。处理程序有效地使用 `by refine' {..} <;> exact default` 来构造居民。 （注意：当无法解析默认字段值时，它们将被忽略，就像省略号模式一样。）

- [#13318](https://github.com/leanprover/lean4/pull/13318)
  添加了对模块名称中操作系统禁止的名称和字符的检查。  这实现了 mathlib 的 `modulesOSForbidden` linter 的功能。

- [#13262](https://github.com/leanprover/lean4/pull/13262)
  扩展了 Lean 的语法，允许在表达式中使用显式的 Universe 级别，例如 `e.f.{u,v}`、`(f e).g.{u}` 和 `e __FIX000__>.f.{u,v} x y z`。它修复了宇宙级别会被归因于错误表达式的错误；例如 `x.f.{u}` 将被解释为 `x.{u}.f`。它还更改了顶级声明的语法，不允许标识符和 Universe 级别列表之间存在空格，并且修复了 `checkWsBefore` 解析器中的一个错误，该错误不会检测 `optional` 解析器中的空格。

- [#13332](https://github.com/leanprover/lean4/pull/13332)
  使用类型跨越多个隐式 Universe 的 `mut` 变量修复 `for` 循环的 Universe 统一。旧方法对每个变量使用 `ensureHasType (mkSort mi.u.succ)`，这会生成像 `max (?u+1) (?v+1) =?= ?u+1` 这样的约束，Universe 求解器无法分解。新方法在递减级别上使用 `getDecLevel`/`isLevelDefEq` ，生成 `max ?u ?v =?= ?u` ，由 `solveSelfMax` 直接处理。

- [#13229](https://github.com/leanprover/lean4/pull/13229)
  使用 `withPosition` 包装顶级命令解析器，以强制 `by` 块中的缩进，并结合使用empty-by后备以获得更好的错误消息。

- [#13320](https://github.com/leanprover/lean4/pull/13320)
  将自动生成的 `sizeOf` 定义更改为不
  暴露并且 `sizeOf_spec` 定理不标记 `[defeq]`。

- [#13311](https://github.com/leanprover/lean4/pull/13311)
  向 `addAndCompile` 添加一个可选的 `markMeta : Bool := false` 参数，以便调用者可以传播 `meta` 标记，而无需手动拆分为 `addDecl` + `markMeta` + `compileDecl`。

- [#13319](https://github.com/leanprover/lean4/pull/13319)
  修改 #13317 以建议 `:= (rfl)` 作为避免定理自动标记为 `[defeq]` 的推荐方法，以与现有文档保持一致。理由：`:= rfl` 的特殊处理是基于语法，而不是证明项，因此使用不同的语法是合适的。我也喜欢它读起来像“`rfl` 的无声耳语”的方式。

- [#13223](https://github.com/leanprover/lean4/pull/13223)
  添加警告，防止用户使用 `... in ...` 应用全局属性，例如
  ```lean4
  theorem a : True := trivial
  attribute [simp] a in
  def b : True := a
  ```

- [#13317](https://github.com/leanprover/lean4/pull/13317)
添加一个选择加入的 linter (`set_option simp.rfl.checkTransparency true`)，当 `rfl` simp 定理的 LHS 和 RHS 在 `.instances` 透明度下定义不相等时发出警告。糟糕的 rfl-simp 定理（那些仅在较高透明度下成立的定理）会在整个系统中产生问题，因为 `simp` 和 `dsimp` 在有限的透明度下运行。 linter 建议两个修复：使用 `id rfl` 作为证明（以删除 `rfl` 状态），或将相关常量标记为 `[implicit_reducible]`。

- [#13304](https://github.com/leanprover/lean4/pull/13304)
  当实例类型为 `Prop` 时，使增量派生处理程序创建 `theorem` 声明而不是 `def` 声明。以前，`deriving instance Nonempty for Foo` 总是会创建 `def`，这与手写的 `instance` 声明的行为不一致。

- [#13281](https://github.com/leanprover/lean4/pull/13281)
  将任何公开的（非私有）辅助匹配声明标记为 `[implicit_reducible]`。当外部声明被标记为 `instance_reducible` 时，这一点至关重要——如果没有它，还原将在匹配辅助中被阻止。我们不会从父声明继承该属性，因为匹配辅助声明在定义之间重用，并且父声明的可归约性设置可以独立更改。此更改为在 `ExprDefEq.lean:465` 处实现 TODO 做准备，否则会导致太多失败，需要在名称不一定源自外部函数的匹配声明上手动添加 `[implicit_reducible]` 注释。

- [#13280](https://github.com/leanprover/lean4/pull/13280)
  添加了一个新选项 `backward.isDefEq.respectTransparency.types` ，用于控制在检查元变量的类型是否与在 `checkTypesAndAssign` 期间分配给它的术语类型匹配时使用的透明度。以前，此检查总是将透明度提高到 `.default` （通过 `withInferTypeConfig`），这过于宽松。新选项使用 `.instances` 透明度代替（通过 `withImplicitConfig`），与已用于隐式参数的行为相匹配。

- [#13266](https://github.com/leanprover/lean4/pull/13266)
  将匹配编译器中的反例累加器从
  一个 `List` （用缺点构建，产生相反的顺序）到 `Array` （构建
  使用推送，保留声明顺序）。失踪案件现已报告
  构造函数出现在归纳类型定义中的顺序。

- [#13243](https://github.com/leanprover/lean4/pull/13243)
  更改在模式中使用时结构实例符号的详细说明（例如 `s matches { x := 1, y := [] }`），以便结构的默认值不用于详细说明模式。其动机是默认值经常导致令人惊讶的过于特定的模式。现在它会报告“字段丢失”错误。可以使用 `{ x := 1, .. }` 省略号表示法来抑制该错误，其行为与以前相同。漂亮的打印机也经过修改以与此功能保持同步。 **重大更改：** 使用结构实例表示法的模式可能需要缺少字段或添加 `..`（视情况而定）。

- [#13195](https://github.com/leanprover/lean4/pull/13195)
  添加了对将选项标记为已弃用的支持。当通过 `set_option` 使用已弃用的选项时，会发出警告（由 `linter.deprecated.options` 控制）。

- [#13255](https://github.com/leanprover/lean4/pull/13255)
在 `do` 块 `let` 和 `have` 声明中添加了对 let 配置选项（`(eq := h)`、`+nondep`、`+usedOnly`、`+zeta`）的支持，与术语级别 `let`/`have` 中可用的行为相匹配。配置选项被 `let mut` 拒绝，因为它们与可变绑定不兼容。 `+postponeValue` 和 `+generalize` 也在 `do` 块中被拒绝。

- [#13250](https://github.com/leanprover/lean4/pull/13250)
  扩展 `doLet`、`doLetElse`、`doLetArrow` 和 `doHave` 解析器以接受 `letConfig`（例如 `(eq := h)`、`+nondep`、`+usedOnly`、`+zeta`），匹配术语级别 `let`/`have` 的语法。阐述器被调整以处理移位的语法索引，但尚未处理配置；这将在 stage0 更新后的后续 PR 中完成，允许使用正确的引用模式。

- [#13245](https://github.com/leanprover/lean4/pull/13245)
  扩展了点函数表示法 (`.f`) 的精益语法，以添加对显式模式 (`@.f`)、显式宇宙 (`.f.{u,v}`) 以及两者同时 (`@.f.{u,v}`) 的支持。这还包括对涉及重载函数的错误的修复，该错误用于对函数未详细说明的声明发出错误的弃用警告。

- [#13232](https://github.com/leanprover/lean4/pull/13232)
  修复了编译在索引归纳类型上使用 `casesOn` 的相互递归定义时出现的恐慌（例如 `Vect`）。 `WF.Unfold` 中的 `splitMatchOrCasesOn` 函数断言 `matcherInfo.numDiscrs = 1`，但对于索引类型，casesOn 递归器具有多个判别式（索引 + 大前提）。该修复使用最后一个判别式（大前提）并让 `cases` 策略自动处理索引判别式。

- [#13002](https://github.com/leanprover/lean4/pull/13002)
  添加 `deprecated_module` 命令，将当前模块标记为已弃用。当另一个模块导入已弃用的模块时，在详细说明期间会发出警告，建议替换导入。

- [#13205](https://github.com/leanprover/lean4/pull/13205)
  修复 `FirstTokens.seq (.optTokens s) .unknown` 以返回 `.unknown`。这种情况会发生，例如当可选（第一个标记为 `.optTokens s`）后跟解析器类别（第一个标记为 `.unknown`）时。以前 `FirstTokens.seq` 返回 `.optTokens s`，忽略了可选值可能为空并且解析器类别可能具有任何第一个标记的事实。这里正确的行为是返回 `.unknown`，这表明第一个标记可以是任何东西。

- [#13220](https://github.com/leanprover/lean4/pull/13220)
  添加 `checkSystem` 调用到几个可以运行的代码路径
  延长时间而不检查取消、心跳限制或
  堆栈溢出。这提高了取消机制的响应能力
  在语言服务器中。

- [#13108](https://github.com/leanprover/lean4/pull/13108)
  添加 `deprecated_syntax` 命令，将语法类型标记为已弃用。当详细说明已弃用的语法（术语、策略或命令）时，会发出 linter 警告。当宏定义在其扩展中使用不推荐使用的语法时，在引用预检查期间也会发出警告。

- [#13219](https://github.com/leanprover/lean4/pull/13219)
  将 `hasAssignableMVar`、`hasAssignableLevelMVar` 和 `isLevelMVarAssignable` 从 `MetavarContext.lean` 移动到新的 `Lean.Meta.HasAssignableMVar` 模块，将它们从通用 `[Monad m] [MonadMCtx m]` 函数更改为 `MetaM` 函数。这使得可以在递归遍历中添加 `checkSystem` 调用，从而确保在非常昂贵的计算过程中进行取消和心跳检查。

````

# 图书馆
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Library"
%%%

```markdown

- [#13863](https://github.com/leanprover/lean4/pull/13863)
  changes the e-matching annotations on `BitVec` to avoid automatically going from `getMsbD` theory to `getLsbD` theory. The key reason being that all lemmas are already duplicated between `getMsbD` and `getLsbD` anyways. Thus, whenever we connect them all lemmas fire in both variants even though usually one is already sufficient. In order to make this possible without reducing proof strength noticeably we introduce two changes:
  1. Write or annotate a few additional `BitVec.getMsbD` lemmas to match the reasoning power of `BitVec.getLsbD`. Most notably `getMsbD_eq_getElem` so `getMsbD` can attempt to convert into `getElem` on its own.
  2. Introduce `grind_pattern getMsbD_eq_getLsbD => x.getMsbD i, x.getLsbD _` such that whenever we have both `getMsbD` and `getLsbD` on the same value in scope we attempt to match them up. We expect that this annotation should *usually* not fire much as most `get*D` can probably be converted into `getElem` and be worked from there.

- [#13850](https://github.com/leanprover/lean4/pull/13850)
  removes the grind annotation that makes `getElem?_pos` trigger whenever `c[i]` is in the e-graph. We do this to avoid reasoning about `c[i]?` just because `c[i]` is available. The trigger for instantiating `getElem?_pos` whenever `c[i]?` is in scope remains in order to nudge grind towards proving or disproving the bounds check.

- [#13689](https://github.com/leanprover/lean4/pull/13689)
  makes the unfolding lemma for `whileM` derivable from a `Lean.Order.MonadTail` instance. The public entry point is `whileM_eq_of_monadTail` in `Init.Internal.Order.While`; the underlying pinning predicate `whileM.Pred` and the conditional `whileM_eq` lemma in `Init.While` are kept module-internal.

- [#13787](https://github.com/leanprover/lean4/pull/13787)
  fixes a small docsting error for `String.split`.

- [#13748](https://github.com/leanprover/lean4/pull/13748)
  fixes premise selection silently dropping relevant premises when the goal was reached via `induction`.

- [#13750](https://github.com/leanprover/lean4/pull/13750)
  refines MePo premise selection so that (1) candidates are restricted to theorems, matching the convention already used by `SineQuaNon` and `SymbolFrequency`, and (2) the result is ordered lexicographically by `(iteration, score)` rather than by score alone.

- [#13747](https://github.com/leanprover/lean4/pull/13747)
  fixes the MePo premise selector returning its lowest-scoring premises instead of its best ones.

- [#13457](https://github.com/leanprover/lean4/pull/13457)
  adds the missing `ByteArray` push and `set!` lemmas that are still carried locally in `ZipForStd.ByteArray` downstream.

- [#13654](https://github.com/leanprover/lean4/pull/13654)
  adds `Dyadic.divAtPrec a b prec`, returning the greatest dyadic with precision at most `prec` which is less than or equal to `a/b` (and `0` when `b = 0`). Mirroring the existing `invAtPrec`, the characterising lemmas `divAtPrec_mul_le` and `lt_divAtPrec_add_inc_mul` are also provided.

- [#13718](https://github.com/leanprover/lean4/pull/13718)
  fixes tests in context_async.lean by removing all the issues with Async.sleep and IO.sleep and improving how ContextAsync.race works.

- [#13567](https://github.com/leanprover/lean4/pull/13567)
  adds Locale and LocaleSymbols for configurable date/time formatting. It also modifies alignedWeekOfMonth and weekOfYear so it contains a parameter to the first of the week.

- [#13565](https://github.com/leanprover/lean4/pull/13565)
  fixes an issue where the missing /etc/localtime caused a failure even when TZ and TZDIR were present.

- [#13675](https://github.com/leanprover/lean4/pull/13675)
  adds a `WallTime` type representing a point in time as nanoseconds since `1970-01-01T00:00:00` local time. It also removes the `sinceUNIXEpoch` and `AssumingUTC` suffixes because `Timestamp` implies UTC, and `WallTime` implies it is based on the WallTime epoch (defined in the comment as `1970-01-01T00:00:00`).

- [#13693](https://github.com/leanprover/lean4/pull/13693)
  generalizes a number of `Vector` lemmas about `++` so that the two appended vectors no longer need to share the same size index: `sum_append`, `prod_append`, their `_nat` / `_int` variants, `flatMap_append`, `unattach_append`, `eraseIdx_append_of_lt_size`, and `eraseIdx_append_of_length_le`.

- [#13521](https://github.com/leanprover/lean4/pull/13521)
  prevents undefined behavior in `readModuleDataParts #[]` on configurations without `LEAN_MMAP`. Previously this would lead to out-of-bounds indexing.

- [#13549](https://github.com/leanprover/lean4/pull/13549)
  makes `readModuleDataParts` report a clearer error if there is insufficient memory to load a module.

- [#13627](https://github.com/leanprover/lean4/pull/13627)
  renames `UInt8.ofNatTruncate` to `UInt8.ofNatClamp`.

- [#13583](https://github.com/leanprover/lean4/pull/13583)
  changes `Invariant`, `StringInvariant`, and `StringSliceInvariant` from `abbrev` to `@[spec_invariant_type, simp, grind =] def`, so that they remain visible as applications of a named constant in proof states (where `SymM` does not unfold `def`s) and can be detected as invariant types by `isSpecInvariantType`. The `@[simp, grind =]` annotations ensure they still unfold on demand under `simp` and `grind`.

- [#13582](https://github.com/leanprover/lean4/pull/13582)
  adds several entailment-related lemmas to `Std.Do.SPred` and `Std.Do.PostCond`, intended for goal-decomposition during program verification proof automation.

- [#12965](https://github.com/leanprover/lean4/pull/12965)
  Introduces new foundations for reasoning about monadic Lean code. Eventually we will port `mvcgen` on top of these new foundations, to make the framework more general and robust.

- [#13546](https://github.com/leanprover/lean4/pull/13546)
  prevents memory exhaustion turning into segfaults when using Lean functions which call into libuv

- [#13511](https://github.com/leanprover/lean4/pull/13511)
  moves Async and Http from Internal to Std

- [#12151](https://github.com/leanprover/lean4/pull/12151)
  introduces the Server module, an Async HTTP/1.1 server.

- [#13400](https://github.com/leanprover/lean4/pull/13400)
  fixes the incorrect name `String.Pos.skipWhile_le` to be `String.Pos.le_skipWhile`.

- [#13398](https://github.com/leanprover/lean4/pull/13398)
  removes private from H1.lean

- [#12146](https://github.com/leanprover/lean4/pull/12146)
  introduces the H1 module, a pure HTTP/1.1 state machine that incrementally parses incoming byte streams and emits response bytes without side effects.

- [#13357](https://github.com/leanprover/lean4/pull/13357)
  is based on a systematic review of all read-only operations on the default containers in core. Where sensible it applies specialize annotations on higher order operations that lack them or borrow annotations on parameters that should morally be borrowed (e.g. the container when iterating over it).

- [#13200](https://github.com/leanprover/lean4/pull/13200)
  adds `prod` (multiplicative fold) for `List`, `Array`, and `Vector`, mirroring the existing `sum` API. Includes basic simp lemmas (`prod_nil`, `prod_cons`, `prod_append`, `prod_singleton`, `prod_reverse`, `prod_push`, `prod_eq_foldl`), Nat-specialized lemmas (`prod_pos_iff_forall_pos_nat`, `prod_eq_zero_iff_exists_zero_nat`, `prod_replicate_nat`), Int-specialized lemmas (`prod_replicate_int`), cross-type lemmas (`prod_toArray`, `prod_toList`), and `Perm.prod_nat` with grind patterns.

- [#13273](https://github.com/leanprover/lean4/pull/13273)
  adds a comprehensive public API for constructing maximally shared
  expression applications and performing beta reduction in the `Sym` framework.
  These functions were previously defined locally in the VC generator and cbv
  tactic, and are needed by downstream `SymM`-based tools.

- [#13155](https://github.com/leanprover/lean4/pull/13155)
  verifies the `String.dropWhile` and `String.takeWhile` functions.

- [#13235](https://github.com/leanprover/lean4/pull/13235)
  uses `std::memcmp` for `ByteArray` `BEq` and `DecidableEq`.

- [#13172](https://github.com/leanprover/lean4/pull/13172)
  adds borrow annotations in `Std.Internal.UV.System`.

```

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Tactics"
%%%

```markdown

- [#13859](https://github.com/leanprover/lean4/pull/13859)
  fixes a kernel rejection when a user-supplied pre-tactic like `clear` in `sym => mvcgen' with (clear h)` rewrites the local context.

- [#13857](https://github.com/leanprover/lean4/pull/13857)
  implements the `dsimp` tactic for interactive `sym =>` mode. It also adds DSL for declaring `dsimp` variants.

- [#13680](https://github.com/leanprover/lean4/pull/13680)
  makes `mvcgen'` usable as a step inside `sym => …` blocks. Leftover VCs become subgoals for subsequent grind steps; `mvcgen' invariants` works inline, `mvcgen' invariants?` is rejected.

- [#13854](https://github.com/leanprover/lean4/pull/13854)
  implements the syntax for declaring `dsimp` variants for `SymM`.

- [#13793](https://github.com/leanprover/lean4/pull/13793)
  extends the new tactic hints about type-incorrect goals at `instances` transparency with the type checking error message to assist with cases that are more complex than "inadvisable `unfold`".

- [#13636](https://github.com/leanprover/lean4/pull/13636)
  makes `simpa using h` close at **reducible** transparency rather than the ambient (default/semireducible) transparency used previously, making `simpa using h` more predictable under changes to the simp set. The previous behaviour is available as `simpa using! h` (introduced in #13833).

- [#13833](https://github.com/leanprover/lean4/pull/13833)
  adds the `simpa ... using! e` syntax as a parallel form of
  `simpa ... using e`. At present `using!` behaves identically to `using` — both
  close the goal at the ambient (default/semireducible) transparency.

- [#13771](https://github.com/leanprover/lean4/pull/13771)
  adds a new `impossible by t` tactic combinator and wires it into the
  default suggestion set of `try?`.

- [#13825](https://github.com/leanprover/lean4/pull/13825)
  implements a collection of reusable reduction `DSimproc`s (`beta`, `zeta`, `zetaAll`, `dsimpProj`, `dsimpMatch`), exposing them as public so callers can compose them into their own `Methods`, and fixing a few bugs.

- [#13824](https://github.com/leanprover/lean4/pull/13824)
  adds functions for simplifying binders in `Sym.dsimp`.

- [#13823](https://github.com/leanprover/lean4/pull/13823)
  adds the basic infrastructure for a `dsimp` in `SymM`.

- [#13812](https://github.com/leanprover/lean4/pull/13812)
  fixes `mconstructor`, `mleft`, and `mright` failing inside `mhave` blocks (#13691), and `mspecialize` failing after a `mrevert; mintro` round trip. Both cases stem from hypothesis-naming `Expr.mdata` leaking from hypothesis-conjunction leaves into non-leaf positions (an inner target, or the antecedent of an `SPred.imp` target), where downstream pattern matches did not see through it.

- [#13766](https://github.com/leanprover/lean4/pull/13766)
  moves the `evalSuggest` combinator and trace-handler dispatch
  from a hardcoded `match` on syntax kinds to the existing
  `tryTacticElabAttribute` registration mechanism, bringing `try?`'s
  extensibility model in line with normal tactics and interactive `grind`.

- [#13774](https://github.com/leanprover/lean4/pull/13774)
  makes `try?`'s `expandUserTactic` walk the info tree for `TryThisInfo`
  nodes (introduced in #10524) instead of parsing the rendered `Try this:` message
  text. The previous approach scraped lines prefixed with `  [apply] ` from the
  message log, which would break the moment that wire format changed.

- [#13430](https://github.com/leanprover/lean4/pull/13430)
  makes an empty `by` block run `try?` in the background and surface its suggestions, while still producing the usual unsolved-goals diagnostic. The implicit `try?` is informational only — it does not change elaboration behavior beyond emitting messages. Behaviour is controlled by a new option `tactic.tryOnEmptyBy`, disabled by default for now; set it to `true` to opt in. The default may flip in a future release.

- [#13699](https://github.com/leanprover/lean4/pull/13699)
  adds a new `grind` configuration option, `genLocal`, that controls the
  maximum term generation for local theorems (e.g., hypotheses). It defaults to
  `8`, same value as `gen` and applies whenever
  `grind` instantiates a theorem whose origin is local rather than a declaration
  or user-provided term. Since users have little control over the patterns used
  for local theorems, a tighter generation bound is a reasonable default.

- [#13698](https://github.com/leanprover/lean4/pull/13698)
  improves the `grind` diagnostics output so that local hypotheses used
  as E-matching theorems show up with their user-facing names and instantiation
  counters, instead of being silently dropped or reported under an anonymous
  `local.<idx>` identifier.

- [#13644](https://github.com/leanprover/lean4/pull/13644)
  adds an experimental tactic `mvcgen'` that will soon replace `mvcgen`. It has been reimplemented from the ground up using the new `SymM`-based framework for efficient symbolic evaluation and can outperform `mvcgen` by a factor of >100x for some synthetic benchmarks. `mvcgen'` aspires to be feature-complete with `mvcgen`. Known exceptions currently are join point sharing, introduction of local specs and smaller bugs.

- [#13678](https://github.com/leanprover/lean4/pull/13678)
  ensures that one can hover over the function name in fun_induction. Fixes #13673

- [#13665](https://github.com/leanprover/lean4/pull/13665)
  replaces `Meta.mkCongrArg` call sites in `handleProj` and `simplifyAppFn` are replaced with direct `congrArg` constructions that reuse types already in the `Sym` pointer cache. A few stray unqualified `inferType` / `getLevel` / `isDefEq` calls in the same file are also routed through the cached `Sym` equivalents.

- [#13640](https://github.com/leanprover/lean4/pull/13640)
  adds a trace event emitted whenever a `dsimp` (or rfl-only `simp`) rewrite fires
  because of a `[backward_defeq]`-tagged theorem (i.e., one that would not
  have applied without `set_option backward.defeqAttrib.useBackward true`).

- [#13635](https://github.com/leanprover/lean4/pull/13635)
  fixes a `Sym.simp` panic ("unexpected kernel projection term
  during simplification") that triggered when matcher iota-reduction
  exposed kernel `Expr.proj` terms via struct-eta. For example, a `do`
  block with a `for` loop whose state is a tuple, where `Sym.simp`
  unfolds the equational lemma and then descends into a destructuring
  match.

- [#13624](https://github.com/leanprover/lean4/pull/13624)
  fixes a `grind` congruence-table invariant violation that could panic
  when an `ite` branch was internalized lazily (after the condition became `True`
  or `False`) and that branch's equivalence class was later merged with another.

- [#13625](https://github.com/leanprover/lean4/pull/13625)
  fixes a `grind` internal error triggered when `cast` (or `Eq.rec`, `Eq.ndrec`, `Eq.recOn`) is applied to an argument that has not yet been internalized. `pushCastHEqs` was emitting `e ≍ a` before internalizing the args of `e`, so the `rhs` of the heq had no enode and the debug sanity check tripped. The call now runs after the args are internalized.

- [#13623](https://github.com/leanprover/lean4/pull/13623)
  fixes proof construction issues in the `grind` projection propagators.

- [#13622](https://github.com/leanprover/lean4/pull/13622)
  fixes another issue in the `grind` AC invariant checker.

- [#13614](https://github.com/leanprover/lean4/pull/13614)
  fixes the invariant in `grind` AC. equations in the todo queue are not fully simplified.

- [#13612](https://github.com/leanprover/lean4/pull/13612)
  improves the universe unifier used by `SymM`.

- [#13611](https://github.com/leanprover/lean4/pull/13611)
  fixes an assertion failure in `Sym.simp` when simplifying a `have`-expression whose binder type depends on a preceding binder in the telescope.

- [#13368](https://github.com/leanprover/lean4/pull/13368)
  adds infrastructure to help diagnose cases where tactics like `unfold`
  leave the goal in a state that is type-correct only at `.default` transparency,
  causing `rw`/`simp` to fail at `.instances` transparency.

- [#13593](https://github.com/leanprover/lean4/pull/13593)
  disables model-based theory combination (`mbtc`) in `grind`'s `NoopConfig`, which is the base configuration used by the derived tactics `lia`, `linarith`, `cutsat`, `order`, and `ring`. Without this fix, these tactics could engage in wasteful reasoning via theory combination, causing them to run for a long time (or hit the deterministic timeout) on problems they are not designed to solve. With this fix, these tactics fail quickly on out-of-scope problems, as expected.

- [#13590](https://github.com/leanprover/lean4/pull/13590)
  makes `lia` (and `grind`'s arithmetic case-split heuristic) recognize
  implications whose antecedent is an `And` or `Or` of arithmetic predicates as
  relevant case-split candidates. Previously, `Arith.isRelevantPred` only matched
  `Not`, `LE`, `LT`, `Eq`, and `Dvd`. With `splitImp := false` (the default),
  implications `p → q` are added as split candidates only when `p` is
  arith-relevant, so a hypothesis like `(b ≤ e ∧ e < b + c → a ≤ e ∧ e < a + d)`
  was never registered as a candidate. cutsat/lia would then find a satisfying
  assignment for the constraints it had been told about, but that assignment
  would not necessarily satisfy the original implication, yielding the bad
  counterexample reported in #13575.

- [#13585](https://github.com/leanprover/lean4/pull/13585)
  adds a `ringMaxDegree` configuration option (default `1024`) that bounds the maximum degree of polynomials processed by the `grind` ring solver. Equality constraints whose polynomial exceeds this threshold are discarded (with an issue reported once per goal), preventing pathological degree explosion on inputs such as `r ^ (2 ^ 250 - 1)`.

- [#13558](https://github.com/leanprover/lean4/pull/13558)
  adds the option `grind.ematch.diagnostics`, which tracks how E-matching theorem instances depend on each other. When enabled, `grind` records, for every new theorem instance, the set of previous instances whose generated terms participated in the match. This produces a hyper-graph `{thm_1, ..., thm_n} => thm` describing the provenance of each instantiation.

- [#13560](https://github.com/leanprover/lean4/pull/13560)
  fixes a bug in `propagateBetaEqs` (in `Lean.Meta.Tactic.Grind.Beta`)
  where new equalities/terms introduced by beta reduction were added to the goal
  without checking the generation threshold. The generation of the new fact
  is the maximum generation of the lambda, the function `f`, and its
  arguments, plus one. Without the threshold check, beta reduction can
  cascade indefinitely on self-similar lambdas such as
  `(fun b => f (b + 1)) = fun b => f b`, which kept producing
  `f n = f (n + 1)` for every `n`. The fix aggregates argument generations
  before the threshold check and bails out when the resulting generation
  reaches `maxGeneration`.

- [#13301](https://github.com/leanprover/lean4/pull/13301)
  adds a `try? => tac` syntax that runs `evalSuggest` directly on a given tactic, useful for testing the `try?` machinery in isolation. It also adds a server_interactive test (`cancellation_par.lean`) that demonstrates a cancellation bug with parallel tactic combinators.

- [#13532](https://github.com/leanprover/lean4/pull/13532)
  notifies satellite solvers about asserted equalities `lhs = rhs` even though `lhs = rhs` is not internalized in the E-graph (an existing optimization). The notification lets solvers that do not inspect equivalence classes (such as the homomorphism extension) react to asserted equalities directly. It fires before the equivalence-class merge so that solvers that mark `lhs` and `rhs` as their internal terms have them registered before `Solvers.mergeTerms` fires `processNewEq`.

- [#13476](https://github.com/leanprover/lean4/pull/13476)
  refines how the `apply` tactic (and related tactics like `rewrite`) name and tag the remaining subgoals. Assigned metavariables are now filtered out *before* computing subgoal tags. As a consequence, when only one unassigned subgoal remains, it inherits the tag of the input goal instead of being given a fresh suffixed tag.

- [#13474](https://github.com/leanprover/lean4/pull/13474)
  fixes a bug in `sym =>` interactive mode where goals whose metavariable was assigned by `isDefEq` (e.g. via `apply Eq.refl`) were not pruned. `pruneSolvedGoals` previously only filtered out goals flagged as inconsistent, so an already-assigned goal would linger as an unsolved goal. It now also removes goals whose metavariable is already assigned.

- [#13472](https://github.com/leanprover/lean4/pull/13472)
  fixes a bug in `sym =>` interactive mode where satellite solvers (`lia`, `ring`, `linarith`) would throw an internal error if their automatic `intros + assertAll` preprocessing step already closed the goal. Previously, `evalCheck` used `liftAction` which discarded the closure result, so the subsequent `liftGoalM` call failed due to the absence of a main goal. `liftAction` is now split so the caller can distinguish the closed and subgoals cases and skip the solver body when preprocessing already finished the job.

- [#13453](https://github.com/leanprover/lean4/pull/13453)
  fixes a kernel error in `grind` when propagating a `Nat` equality to an order structure whose carrier type is not `Int` (e.g. `Rat`). The auxiliary `Lean.Grind.Order.of_nat_eq` lemma was specialized to `Int`, so the kernel rejected the application when the cast destination differed.

- [#13451](https://github.com/leanprover/lean4/pull/13451)
  fixes a bug in `Sym.introCore.finalize` where the original metavariable was unconditionally assigned via a delayed assignment, even when no binders were introduced. As a result, `Sym.intros` would return `.failed` while the goal metavariable had already been silently assigned, confusing downstream code that relies on `isAssigned` (e.g. VC filters in `mvcgen'`).

- [#13448](https://github.com/leanprover/lean4/pull/13448)
  fixes a regression in `Sym.simp` where rewrite rules whose LHS contains a lambda over a pattern variable (e.g. `∃ x, a = x`) failed to match targets with semantically equivalent structure.

- [#13088](https://github.com/leanprover/lean4/pull/13088)
  wires the `PowIdentity` typeclass (from https://github.com/leanprover/lean4/pull/13086) into the `grind` ring solver's Groebner basis engine.

- [#13086](https://github.com/leanprover/lean4/pull/13086)
  adds a `Lean.Grind.PowIdentity` typeclass stating that `x ^ p = x` for all elements of a commutative semiring, with `p` as an `outParam`.

- [#13289](https://github.com/leanprover/lean4/pull/13289)
  adds the shared infrastructure for arithmetic normalization in `Sym.Arith/`,
  laying the groundwork for both `Sym.simp`'s arith pre-simproc and the eventual
  unification of grind's `CommRing` module.

- [#13272](https://github.com/leanprover/lean4/pull/13272)
  extends the sym canonicalizer to apply reductions (projection, match/ite/cond, Nat
  arithmetic) in all positions, not just inside types. Previously, a value `v` appearing in a
  type `T(v)` could remain unreduced while `T(v)` was normalized, breaking the invariant that
  definitionally equal types are structurally identical after canonicalization.

- [#13271](https://github.com/leanprover/lean4/pull/13271)
  refactors instance canonicalization in the sym canonicalizer to properly handle
  \`Grind.nestedProof\` and \`Grind.nestedDecidable\` markers. Previously, the canonicalizer
  would report an issue when it failed to resynthesize propositional instances that were
  provided by \`grind\` itself or by the user via \`haveI\`. Now, resynthesis failure gracefully
  falls back to the original instance in value positions, while remaining strict inside types.

- [#13202](https://github.com/leanprover/lean4/pull/13202)
  fixes a heartbeat timeout from an environment extension at the end of the file that cannot be avoided by raising the limit.

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Compiler"
%%%

```markdown

- [#13796](https://github.com/leanprover/lean4/pull/13796)
  optimizes `String.compare` to turn it into 1 instead of 2 `memcmp` calls.

- [#13788](https://github.com/leanprover/lean4/pull/13788)
  generates specialized code for invoking `dec` on values whose shape is known. This puts branch prediction pressure off `lean_dec_ref_cold` as the shape of the constructor should now be compiled into the executable.

- [#13669](https://github.com/leanprover/lean4/pull/13669)
  optimizes `lean_dec_ref_cold` by outlining the "freezing cold" path and performing a small microarchitecural optimization. The latter is better as it makes clear to LLVM that we believe the pointer to only use 48 bits.

- [#13545](https://github.com/leanprover/lean4/pull/13545)
  upgrades LLVM from version 19 to version 22. This brings general performance improvements of up to 5% instructions depending on benchmark.

- [#13493](https://github.com/leanprover/lean4/pull/13493)
  ensures that `import` gracefully processes `EINTR` errors from the filesystem.

- [#13464](https://github.com/leanprover/lean4/pull/13464)
  replaces `exit(-1)` with `_exit(-1)` in the forked child branches of `lean_io_process_spawn` (the `chdir` failure and `execvp` failure paths). `exit` flushes inherited C stdio buffers, which share underlying file descriptors with the parent. If the parent had a file handle open with unflushed data, that data would be written to the file in the child and then again when the parent later flushes, resulting in duplicated output. `_exit` skips the stdio flush, so the parent's buffered writes are no longer duplicated into inherited files.

- [#13435](https://github.com/leanprover/lean4/pull/13435)
  fixes a bug in EmitC that can be caused by working with the string literal `"\x01abc"` in
  Lean and causes a C compiler error.

- [#13427](https://github.com/leanprover/lean4/pull/13427)
  fixes two minor bugs in `io.cpp`:
  1. A resource leak in a Windows error path of `Std.Time.Database.Windows.getNextTransition`
  2. A buffer overrun in `IO.appPath` on linux when the executable is a symlink at max path length.

- [#13421](https://github.com/leanprover/lean4/pull/13421)
  fixes an issue in the expand reset reuse pass that causes segfaults in very rare situations.

- [#13409](https://github.com/leanprover/lean4/pull/13409)
   specialize qsort properly onto the lt function

- [#13401](https://github.com/leanprover/lean4/pull/13401)
  adds the option `LEAN_MI_SECURE` to our CMake build. It can be configured with values `0`
  through `4`. Every increment enables additional memory safety mitigations in mimalloc, at the cost
  of 2%-20% instruction count, depending on the benchmark. The option is disabled by default in our
  release builds as most of our users do not use the Lean runtime in security sensitive situations.
  Distributors and organization deploying production Lean code should consider enabling the option as
  a hardening measure. The effects of the various levels can be found at  https://github.com/microsoft/mimalloc/blob/v2.2.7/include/mimalloc/types.h#L56-L60.

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  fixes a heap buffer overflow in `lean_io_prim_handle_read` that was triggered through an
  integer overflow in the size computation of an allocation. In addition it places several checked
  arithmetic operations on all relevant allocation paths to have potential future overflows be turned
  into crashes instead. The offending code now throws an out of memory error instead.

- [#13384](https://github.com/leanprover/lean4/pull/13384)
  fixes a compiler panic when a structure constructor receives a noncomputable instance as an instance-implicit argument.

- [#13234](https://github.com/leanprover/lean4/pull/13234)
  fixes a build issue when Lean is not linked against libuv.

- [#13233](https://github.com/leanprover/lean4/pull/13233)
  fixes runtime build issues when `LEAN_MULTI_THREAD` is not set.

- [#13270](https://github.com/leanprover/lean4/pull/13270)
  adds `Runtime.hold`, which ensures its argument remains alive until the callsite by holding a reference to it. This can be useful for unsafe code (such as an FFI) that relies on a Lean object not being freed until after some point in the program.

- [#13258](https://github.com/leanprover/lean4/pull/13258)
  adds a `Core.checkInterrupted` call in `checkInferTypeCache` on cache miss, allowing cancellation to be detected during large type inference traversals. Previously, `inferTypeImp` could run for >100ms without any interruption check when processing large expressions (e.g. BVDecide proof terms), making IDE cancellation unresponsive.

- [#13242](https://github.com/leanprover/lean4/pull/13242)
  fixes the compiler handling of pattern matching on the `String` constructor to conform to the new `String` representation.

- [#13128](https://github.com/leanprover/lean4/pull/13128)
  fixes the Windows dev build by using `CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY` instead of the hardcoded `lib/lean` path for the Lake plugin. On Windows, DLLs must be placed next to executables in `bin/`, but the plugin path was hardcoded to `lib/lean`, causing stage0 DLLs to not be found.

```

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Pretty-Printing"
%%%

```markdown

- [#13761](https://github.com/leanprover/lean4/pull/13761)
  fixes an issue where the `pp.universes` option would cause constants with no universes to not use unexpanders or dot notation. For example, `p ↔ q` would pretty print as `Iff p q` even though `Iff` has no universe levels.

- [#13446](https://github.com/leanprover/lean4/pull/13446)
  improves metavariable pretty printing and their hovers in the InfoView. The hovers in the InfoView now include information about specific metavariables — it includes information such as the kind of the metavariable, whether it is a blocked delayed assignment and which metavariables it is blocked on, and the differences in what variables exist the metavariable's local context. Additionally, named metavariables now pretty print with tombstones if they are inaccessible. Delayed assignment pretty printing now more reliably follows chains of assignments to find the pending metavariable.

- [#13438](https://github.com/leanprover/lean4/pull/13438)
  makes the universe level pretty printer instantiate level metavariables when `pp.instantiateMVars` is true.

- [#13030](https://github.com/leanprover/lean4/pull/13030)
  improves pretty printing of level metavariables: they now print with a per-definition index rather than their per-module internal identifiers. Furthermore, `+` is printed uniformly in level expressions with surrounding spaces. **Breaking metaprogramming change:** level pretty printing should use `delabLevel` or `MessageData.ofLevel`; functions such as `format` or `toString` do not have access to the indices, since they are stored in the current metacontext. Absent index information, metavariables print with the raw internal identifier as `?_mvar.nnn`. **Note:** The heartbeat counter also increases quicker due to counting allocations that record level metavariable indices. In some tests we needed to increase `maxHeartbeats` by 20–50% to compensate, without a corresponding slowdown.

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Documentation"
%%%

```markdown

- [#13864](https://github.com/leanprover/lean4/pull/13864)
  updates the pipe operator docstrings for accurracy and helpfulness. Such operators are not idiomatic Haskell, so the old text was incorrect, and it's better to explain the behavior than to reference other languages anyway.

- [#13656](https://github.com/leanprover/lean4/pull/13656)
  documents how to perform an LLVM upgrade.

```

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Server"
%%%

```markdown

- [#13525](https://github.com/leanprover/lean4/pull/13525)
  adds `FromJson`/`ToJson` instances for `Unit` - encoded as `{}` - and documentation for `FromJson`/`ToJson`.

- [#13260](https://github.com/leanprover/lean4/pull/13260)
  adds server-side support for incremental diagnostics via a new `isIncremental` field on `PublishDiagnosticsParams` that is only used by the language server when clients set `incrementalDiagnosticSupport` in `LeanClientCapabilities`.

- [#13348](https://github.com/leanprover/lean4/pull/13348)
  fixes a bug where tactic auto-completion would produce tactic completion items in the entire trailing whitespace of an empty tactic block. Since #13229 further restricted top-level `by` blocks to be indentation- sensitive, this PR adjusts the logic to only display completion items at a "proper" indentation level.

- [#13257](https://github.com/leanprover/lean4/pull/13257)
  adds test infrastructure and tests for tactic completion in empty `by` blocks.

```

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Lake"
%%%

```markdown

- [#13949](https://github.com/leanprover/lean4/pull/13949)
  adds a `LAKE_RESTORE_ARTIFACTS` environment variable that overrides the workspace's default `restoreAllArtifacts` configuration, mirroring how `LAKE_ARTIFACT_CACHE` overrides `enableArtifactCache`.

- [#13936](https://github.com/leanprover/lean4/pull/13936)
  fixes an issue where `depPkgs` was not properly set for a transitive dependency that was overriden by a package at a higher level in the dependency graph.

- [#13843](https://github.com/leanprover/lean4/pull/13843)
  makes `lake lint --builtin-lint` import module-system targets at the public (`OLeanLevel.exported`) level instead of `private`. Environment linters now lint the public surface of such modules, matching how downstream consumers see them. Non-module targets retain their previous behaviour (`private` level), and text-linter warnings recorded via `lintLogExt` are preserved across the level change because that extension stores uniform OLean entries.

- [#13563](https://github.com/leanprover/lean4/pull/13563)
  makes `Glob.ofString?` public, allowing removing the last use of `open private` from Mathlib.

- [#13683](https://github.com/leanprover/lean4/pull/13683)
  moves the compiled Lake configurations (e.g., `lakefile.olean`) from the package's `.lake/config` directory to the workspace's `.lake/config`. This removes a potential source contention between workspaces sharing a dependency.

- [#13601](https://github.com/leanprover/lean4/pull/13601)
  changes Lake's module import graph processing to await the completion of any `needs` targets or other extra dependencies (such as cloud releases). This both enables the `needs` targets to influence header processing and prevents them from racing with said processing.

- [#13600](https://github.com/leanprover/lean4/pull/13600)
  fixes a Lake issue where the IR for a `meta import`'s transitive imports was not included in the import artifacts Lake provided to Lean (e.g., via `--setup`). When using the Lake artifact cache, this could produce "missing data file" errors due to absent IR.

- [#13559](https://github.com/leanprover/lean4/pull/13559)
  fixes a race condition in the Lake build monitor's draining of the job queue.

- [#13513](https://github.com/leanprover/lean4/pull/13513)
  extends `lake lint --builtin-lint` to also support text linters (i.e. those using `logLint`/`logLintIf`), in addition to the environment linters added in #13431. Text-linter warnings emitted during the build are persisted into each module's `.olean` via a new `Lean.Linter.lintLogExt` environment extension; `lake lint` re-runs the build for the target modules and reads the entries back, reporting them alongside the environment linter output.

- [#13516](https://github.com/leanprover/lean4/pull/13516)
  adds `namespace Lake` to `Lake.Util.Opaque`, which was missing it. This is technically a breaking change for any code which used `Opaque` without `open Lake`, but hopefully no one was doing that.

- [#13500](https://github.com/leanprover/lean4/pull/13500)
  adds a check for empty `lake build` invocations (as an empty build usually indicates a misconfiguration). Builds with no jobs will now print "Nothing to build." and invocations of `lake build` with no default targets configured will produce a warning. This will be promoted to an error in the future. The warning (and future error) can be suppressed with the new `--allow-empty` CLI option.

- [#13431](https://github.com/leanprover/lean4/pull/13431)
  adds builtin environment linting support to Lake, accessible via `lake lint` flags. It also introduces two builtin linters upstreamed from Mathlib (`defLemma` and `checkUnivs`) and a `builtinLint` package configuration option.

- [#13456](https://github.com/leanprover/lean4/pull/13456)
  adds a type abbreviation `GitRev` to Lake, which is used for `String` values that signify Git revisions. Such revisions may be a SHA1 commit hash, a branch name, or one of Git's more complex specifiers.

- [#13423](https://github.com/leanprover/lean4/pull/13423)
  adds `JobAction.reuse` and `JobAction.unpack` which provide more information captions for what a job is doing for the build monitor. `reuse` is set when using an artifact from the Lake cache, `unpack` is set when unpacking module `.ltar` archives and release (Reservoir or GitHub) archives.

- [#13393](https://github.com/leanprover/lean4/pull/13393)
  adds a basic support for `lake builtin-lint` command that is used to run environment linters and in the future will be extend to deal with the core syntax linters.

- [#13340](https://github.com/leanprover/lean4/pull/13340)
  fixes a Lake issue where library builds would not produce informative errors about bad imports (unlike module builds).

- [#13282](https://github.com/leanprover/lean4/pull/13282)
  introduces `LakefileConfig`, which can be constructed from a Lake configuration file without all the information required to construct a full `Package`. Also, workspaces now have a well-formedness property attached which ensures the workspace indices of its packages match their index in the workspace. Finally, the facet configuration map now has its own type: `FacetConfigMap`.

- [#13277](https://github.com/leanprover/lean4/pull/13277)
  fixes a public-facing typo in a function name: `Module.checkArtifactsExsist` ->  `Module.checkArtifactsExist`.

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Other"
%%%

```markdown

- [#13185](https://github.com/leanprover/lean4/pull/13185)
  adds new incremental module serialization functions that save/load a single module at a time with explicit sharing via dep regions and compactor state, generalizing the existing batch saveModuleDataParts API.

- [#13740](https://github.com/leanprover/lean4/pull/13740)
  extends `lake shake --explain` to also cover reasons for keeping imports that go beyond direct references, such as shake annotations.

- [#13530](https://github.com/leanprover/lean4/pull/13530)
  adds a `trace.profiler.serve` option that, when enabled, serves the Firefox Profiler-compatible profile JSON on an ephemeral `127.0.0.1` port and opens `https://profiler.firefox.com/from-url/...` in the user's default browser, à la `samply`. The server shuts down once the profile has been fetched.

- [#13630](https://github.com/leanprover/lean4/pull/13630)
  fixes an "Unknown constant" error when `set_option diagnostics true` is enabled in module mode under a `public section`. Diagnostic output may reference private declarations such as `_match_*` and `_sparseCasesOn_*` that are recorded in unfold counters; constructing the message previously failed because the environment was in exporting mode and could not resolve those names. The diagnostic-printing paths in `Lean.Meta.Diagnostics.reportDiag` and `Lean.Meta.Tactic.Simp.Diagnostics.reportDiag` now run under `withoutExporting`.

- [#13589](https://github.com/leanprover/lean4/pull/13589)
  ensures that the `lean --error=tag` flag actually sets a non-zero exit code on promoted errors.

- [#13553](https://github.com/leanprover/lean4/pull/13553)
  fixes a typo in the error message thrown by `runInitAttrs` when initializer execution has not been enabled. The message previously referred to `enableInitializerExecution` (singular), but the actual function is `enableInitializersExecution` (plural).

- [#13520](https://github.com/leanprover/lean4/pull/13520)
  extends the `grind` homomorphism demo with predicates to be applied atoms.

- [#13499](https://github.com/leanprover/lean4/pull/13499)
  fixes the architecture detection for `leantar` on Linux aarch64, ensuring it is properly bundled with Lean.

- [#13497](https://github.com/leanprover/lean4/pull/13497)
  adds an example for the Lean hackathon in Paris. It demonstrates how users can implement https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#13132](https://github.com/leanprover/lean4/pull/13132)
  adds a `linter.redundantVisibility` option (default `true`) that warns
  when a visibility modifier has no effect because it matches the default for the
  current context:

  - `private` outside a `public section` in a `module` file, where declarations
    are already module-scoped by default
  - `public` in a non-`module` file or inside a `public section`, where
    declarations are already public by default

- [#13211](https://github.com/leanprover/lean4/pull/13211)
  adds an `unlock_limits` command that sets `maxHeartbeats`, `maxRecDepth`, and `synthInstance.maxHeartbeats` to 0, disabling all core resource limits. Also makes `maxRecDepth 0` mean "no limit" (matching the existing behavior of `maxHeartbeats 0`).

- [#13226](https://github.com/leanprover/lean4/pull/13226)
  updates `release_checklist.py` to handle the `CACHE STRING ""` suffix on CMake version variables. The `CACHE STRING` format was introduced in the `releases/v4.30.0` branch, but the script's parsing wasn't updated to match, causing false failures.

```
