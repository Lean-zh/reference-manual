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

#doc (Manual) "Lean4.31.0 (2026-06-13)" =>
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

Lean 4.31.0 是一个整合性很强的版本：除了一些新的面向用户的功能（`do` 块细化、Lake 内置检查和更丰富的编辑器悬停）之外，它还付出了巨大的协调努力，使定义相等检查正确尊重透明度级别、更快和重新实现的 `mvcgen'`、包括 HTTP 在内的库的重大开发，以及包括 LLVM 22 升级在内的广泛性能工作。

_此亮点部分由 Juanjo Madrigal 贡献。_

## `do` 符号：新循环形式和新精译器
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

与此同时，新的 `do` 精译器（可通过 `set_option backward.do.legacy false` 访问）也在开发中：除了可扩展性之外，它已经产生了更精确、更可操作的诊断：

```lean (name := newDo)
set_option backward.do.legacy false in
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput newDo (severity := warning)
This `do` element and its control-flow region are dead code. Consider removing it.
```

相反，遗留的精译器拒绝了相同的程序，但有一个更粗略的、纯粹的结构错误：

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

## 单子程序程序验证：`mvcgen'`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Monadic-Program-Verification___--mvcgen___"
%%%

单子程序验证框架的工作仍在继续。 [#12965](https://github.com/leanprover/lean4/pull/12965) 引入了推理单子 Lean 代码的新基础，将单子 Hoare 三元组的前置/后置条件的断言语言从 `SPred` 推广到任何 `CompleteLattice`，分离终止路径和突然路径的后置条件，并解决了几个宇宙多态性问题。

在此基础上，[#13644](https://github.com/leanprover/lean4/pull/13644) 添加了实验性 `mvcgen'` 策略，这是在新的基于 `SymM` 的符号评估框架上从头开始重新实现 `mvcgen`。在某些综合基准测试中，它的性能比 {tactic}`mvcgen` 强 100 倍以上，并且渴望实现功能完整。 `mvcgen'` 也可以用作交互式 `sym => …` 块内的步骤，其中剩余的验证条件成为后续 `grind` 步骤 ([#13680](https://github.com/leanprover/lean4/pull/13680)) 的子目标。

## 透明度和 Defeq 纪律
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Transparency-and-Defeq-Discipline"
%%%

此版本的一个跨领域主题是使定义相等检查正确尊重“透明度”：在决定两个术语是否“定义相等”时，Lean如何积极地展开定义。普通的 `def` 在 `.default` 透明度下对其主体进行定义相等，但 `simp`/`dsimp` 在较低的 `.reducible` 级别上运行，在那里它不会展开：

```lean +error
def x : Nat := 5

-- `rfl` checks defeq at `.default` transparency, so it closes the goal:
example : x = 5 := rfl

-- but `with_reducible` (where `simp`/`dsimp` run) won't unfold it:
example : x = 5 := by with_reducible refl

-- and `simp`/`dsimp` does not work either:
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

- [#13002](https://github.com/leanprover/lean4/pull/13002) 添加了 `deprecated_module` 命令，将当前模块标记为已弃用；导入方收到建议更换的警告。 `#show_deprecated_modules` 命令列出环境中已弃用的模块。

  ```
  deprecated_module "use NewModule instead" (since := "2026-03-30")
  ```

- [#13108](https://github.com/leanprover/lean4/pull/13108) 添加了一个 `deprecated_syntax` 命令，该命令将语法类型标记为已弃用，并在精译已弃用的语法（包括通过宏扩展）时发出检查器警告。
- [#13195](https://github.com/leanprover/lean4/pull/13195) 允许将选项标记为已弃用，并在 `set_option` 使用时发出警告（由 `linter.deprecated.options` 控制）。

一组相关的新检查器会警告冗余修饰符：`linter.redundantVisibility` 表示与默认值 ([#13132](https://github.com/leanprover/lean4/pull/13132)) 匹配的 `private`/`public`，`linter.redundantExpose` 表示无操作 `@[expose]`/`@[no_expose]` ([#13359](https://github.com/leanprover/lean4/pull/13359))，以及针对带有变量或无法识别的 `@[simp]` 定理的警告头部符号 ([#13325](https://github.com/leanprover/lean4/pull/13325))。

## Lake：内置 Linting
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Lake___-Built-in-Linting"
%%%

Lake 获得了内置的检查框架，可通过 `lake lint` 标志（[#13393](https://github.com/leanprover/lean4/pull/13393)、[#13431](https://github.com/leanprover/lean4/pull/13431)）访问。它附带了来自 Batteries/Mathlib 上游的环境检查器（`defLemma`/`defProp`、`checkUnivs`） - 另请参阅 [#13356](https://github.com/leanprover/lean4/pull/13356) 中的核心上游 - 以及 `builtinLint` 包配置选项。标志包括 `--builtin-lint`、`--builtin-only`、`--clippy`、`--lint-all` 和 `--lint-only <name>`，并且 `@[builtin_nolint]` 属性抑制每个声明的特定检查器。

[#13513](https://github.com/leanprover/lean4/pull/13513) 通过将警告保留到每个模块的 `.olean` 中，将其扩展到 *text* 检查器，而 [#13843](https://github.com/leanprover/lean4/pull/13843) 使模块系统目标检查其公共表面，与下游消费者所看到的相匹配。

## 性能
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Performance"
%%%

此版本包括广泛的性能工作：

- [#13545](https://github.com/leanprover/lean4/pull/13545) 将捆绑编译器工具链从 LLVM 19 升级到 LLVM 22，根据基准测试，指令总体改进高达 5%。
- [#13788](https://github.com/leanprover/lean4/pull/13788) 为已知形状的值生成专门的 `dec` 代码，[#13669](https://github.com/leanprover/lean4/pull/13669) 优化 `lean_dec_ref_cold` 冷路径。
- [#13796](https://github.com/leanprover/lean4/pull/13796) 将 `String.compare` 简化为单个 `memcmp`，并且 [#13235](https://github.com/leanprover/lean4/pull/13235) 使用 `memcmp` 来实现 {name}`ByteArray` 相等。
- [#13651](https://github.com/leanprover/lean4/pull/13651) 将策略配置精译系统替换为直接构造配置对象并可以完全跳过术语精译的系统；配置评估现在花费的时间大约是以前的 6.2%。新系统还支持 {tactic}`simp` （例如 `(user.optionName := …)`）的自定义配置语法和用户配置选项。
- Elaboration 本身对于具有许多字段的结构实例表示法 ([#13760](https://github.com/leanprover/lean4/pull/13760)) 和常见情况下的 `Expr.instantiateBetaRevRange` ([#13758](https://github.com/leanprover/lean4/pull/13758)) 来说更快。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Highlights--Library-Highlights"
%%%

上一个版本引入的标准 HTTP 库成长为工作服务器：[#12146](https://github.com/leanprover/lean4/pull/12146) 添加了 `H1` 纯 HTTP/1.1 状态机，[#12151](https://github.com/leanprover/lean4/pull/12151) 添加了异步 HTTP/1.1 `Server`。重要的是，[#13511](https://github.com/leanprover/lean4/pull/13511) 将 `Async` 和 `Http` 模块从 `Internal` 升级到 `Std`。

其他值得注意的库添加：

- 日期/时间获得本地时间点的 `WallTime` 类型和简化的 `Timestamp` 接口 ([#13675](https://github.com/leanprover/lean4/pull/13675))，以及用于可配置格式的 `Locale`/`LocaleSymbols` ([#13567](https://github.com/leanprover/lean4/pull/13567))。
- `List.prod`/`Array.prod`/`Vector.prod` 镜像现有的 `sum` 接口，具有简化和磨削引理 ([#13200](https://github.com/leanprover/lean4/pull/13200))。
- 更多 {name}`ByteArray` `push`/`set!` 引理 ([#13457](https://github.com/leanprover/lean4/pull/13457)) 和 `Vector` 附加引理推广到不同大小的向量 ([#13693](https://github.com/leanprover/lean4/pull/13693))。
- 验证 `String.dropWhile`/`String.takeWhile` 继续字符串验证工作 ([#13155](https://github.com/leanprover/lean4/pull/13155))。

许多运行时稳健性修复还将以前无声的内存耗尽故障转变为正确的错误或崩溃，而不是段错误和损坏（[#13392](https://github.com/leanprover/lean4/pull/13392)、[#13546](https://github.com/leanprover/lean4/pull/13546)、[#13547](https://github.com/leanprover/lean4/pull/13547)、[#13548](https://github.com/leanprover/lean4/pull/13548)、[#13549](https://github.com/leanprover/lean4/pull/13549)、[#13521](https://github.com/leanprover/lean4/pull/13521)）。对于安全敏感的部署，[#13401](https://github.com/leanprover/lean4/pull/13401) 添加了 `LEAN_MI_SECURE` 构建选项，可实现额外的 mimalloc 内存安全缓解。

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

- [#13807](https://github.com/leanprover/lean4/pull/13807) 使应用程序精译器 β-reduce 参数，同时将它们替换为以后预期的类型，与 `inferType` 和 `instantiateMVars` 一致。 *重大更改：*一些策略证明可能需要删除不必要的步骤，例如`dsimp only` 以前仅存在的步骤用于执行这些 β 减少。相关地， [#13528](https://github.com/leanprover/lean4/pull/13528) 更改元变量簿记，以便元程序不再仅仅因为分配了元变量而假设 `MVarId` 发生更改（例如，当 `change` 的唯一效果是附带赋值时，该命令不再更改 `MVarId`）；它还揭示了许多 `dsimp` 没有执行任何操作并且可以删除。
- [#13243](https://github.com/leanprover/lean4/pull/13243) 在*作为模式*精译结构实例表示法时，不再应用结构的默认值（例如 `s matches { x := 1 }`）。*重大变更：*此类模式现在可能报告“缺少字段”错误，需要提供缺失字段或添加 `..`。
- [#13476](https://github.com/leanprover/lean4/pull/13476) 在计算 `apply`/`rewrite` 子目标标签之前过滤分配的元变量，因此单个剩余目标现在继承输入目标的标签。 *重大更改：*依赖先前标签名称的脚本（例如 `funext` 之后的 `case h => …`）可能需要更新。
- [#13030](https://github.com/leanprover/lean4/pull/13030) 更改级别元变量漂亮打印以使用每个定义索引。 *破坏性元编程更改：*级别漂亮打印应使用 `delabLevel` 或 `MessageData.ofLevel`； `format`/`toString` 无法访问索引，并将原始内部标识符打印为 `?_mvar.nnn`。由于索引记录分配，一些测试需要 `maxHeartbeats` 提高 20-50%。
- [#13627](https://github.com/leanprover/lean4/pull/13627) 将 `UInt8.ofNatTruncate` 重命名为 `UInt8.ofNatClamp` （以及其他宽度变体），以便与 `UIntX` 接口的其余部分保持一致。
- [#13516](https://github.com/leanprover/lean4/pull/13516) 将缺少的 `namespace Lake` 添加到 `Lake.Util.Opaque` 中；必须更新引用 `Opaque` 而没有 `open Lake` 的代码。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Language"
%%%

````markdown

- [#13803](https://github.com/leanprover/lean4/pull/13803)
  将 `defLemma` 检查器重命名为 `defProp` 并澄清
  它的警告消息。

- [#13862](https://github.com/leanprover/lean4/pull/13862)
  将错误消息改进从 #10488 更新为在提供改进的消息时还检查标识符转义字符。之前，它仅检查标识符起始字符。

- [#13853](https://github.com/leanprover/lean4/pull/13853)
  通过模块使 `lake lint --builtin-lint` 组保存文本检查器诊断
  产生它们的，而不是在
  顶级模块被检查。每个贡献子模块现在都有自己的
  `-- Text linter diagnostics in <module>:` 标头，镜像如何
  环境检查器方面已经对结果进行了分组。

- [#13844](https://github.com/leanprover/lean4/pull/13844)
  使 `Lean.Linter.logLint` 将内部标签附加到每个
  检查器警告，以便 `Lean.Linter.recordLints` 能够可靠地区分
  检查器从其他标记消息生成的消息（命名错误，
  未知标识符消息、`hasSorry` 标记等）。之前，
`recordLints` 捕获了顶级类型为非匿名的每条消息，
  它将非检查器诊断过度记录到持久 lint 日志中。

- [#13752](https://github.com/leanprover/lean4/pull/13752)
  使得投影符号错误总是在适用时提及父结构上的私有声明作为原因。以前，对于通过结构继承解决的投影，提示会被默默地忽略，使用户无法得知实际原因。

- [#13813](https://github.com/leanprover/lean4/pull/13813)
  修复了 `beforeElaboration` 属性未在 `inductive`/`structure`/`coinductive` 命令上运行的问题。关闭#13433。

- [#13811](https://github.com/leanprover/lean4/pull/13811)
  更新 `#where` 命令以便能够报告 `module` 相关范围状态，例如输出中的 `@[expose] public meta section` 行。

- [#13760](https://github.com/leanprover/lean4/pull/13760)
  提高了具有大量字段的结构实例表示法的精细化性能。它还使用结构参数的 β 减少替换，这已经是结构字段的情况。

- [#13807](https://github.com/leanprover/lean4/pull/13807)
  将应用程序精译器修改为 β 减少参数，同时将它们替换为后续参数的预期类型。这使得它与 `inferType` 和 `instantiateMVars` 一致，这两个测试版都减少了替换。特别是，此更改可确保应用程序精译器的行为就像为每个参数创建元变量并将详细参数分配给元变量一样。 **重大变化：**可能需要修改策略证明以删除不必要的步骤，例如`dsimp only` 之前用于减少 β 的步骤。

- [#13808](https://github.com/leanprover/lean4/pull/13808)
  强制 Verso 文档字符串扩展在属性应用程序时应始终是元的，从而提供更好的错误消息，并确保生成的参数解析器帮助程序也是元的并且具有相同的可见性。

- [#13801](https://github.com/leanprover/lean4/pull/13801)
  向 `DoOps`、`splitMonadApp?` 和 `mkMonadApp` 添加两个新字段，以便 `elabDoWith` 的调用者可以使用默认 `m α` 分解无法处理的索引单子 `Measure α`（其中 `Measure : (α : Type u) → [MeasureSpace α] → Type u` 携带实例参数）。现有行为移至 `DoOps.default`。

- [#13800](https://github.com/leanprover/lean4/pull/13800)
  将 `do` 精译器的 `mkMonadicType` 重命名为 `mkMonadApp`，使其与 `DoOps` 中现有的 `mkPureApp` / `mkBindApp` 命名约定保持一致。

- [#13780](https://github.com/leanprover/lean4/pull/13780)
  是 #13779 的第 2 部分。它完成了配置评估元程序到内置精译器的转变。

- [#13779](https://github.com/leanprover/lean4/pull/13779)
  使用于配置评估元编程的命令精译器成为内置的，以避免由于解释器在运行所有内置初始化程序之前评估精译器的大部分而导致核心 Lean 中的引导 ABI 问题。 （这是第 1 部分；#13780 将在 stage0 更新后应用。）

- [#13762](https://github.com/leanprover/lean4/pull/13762)
  对函数应用程序精译器进行了一些重构，并改进了 `trace.Elab.app` 跟踪。它还通过更仔细地将参数替换为函数的类型以及更改命名参数依赖抑制的实现方式来提高渐近复杂性。对于点表示法，它现在直接构建基本投影，而不是使用应用程序精译器。它修复了 η args 功能中的一个错误，即比预期更显式的参数将转换为隐式参数，并且它通过遵循主应用程序精译器的规则来改进预期的类型传播。

- [#13772](https://github.com/leanprover/lean4/pull/13772)
通过在 `Config.toKey` 中包含 `Config.zetaUnused` 来关闭 https://github.com/leanprover/lean4/issues/13770 。此前，两个仅在 `zetaUnused` 方面不同的配置共享 `WHNF`/`isDefEq` 缓存键，因此可以为另一种设置返回在一种设置下执行的减少。新位位于位置 22，紧邻 `zetaHave` 上方。

- [#13768](https://github.com/leanprover/lean4/pull/13768)
  修复了 `Meta.Config.toKey` 和 `Context.setTransparency` 中长期存在的错误，其中 `TransparencyMode` 仅打包到缓存键的 2 位中，即使它有 5 个构造函数（`.all`、`.default`、`.reducible`、`.instances`、`.none`）。 `.none` 情况（值 `4`，即 `0b100`）与 `foApprox` 位重叠，因此仅透明度与 `foApprox` 不同的配置可能会在 `isDefEq`/`WHNF` 缓存中发生冲突，并且在切换到或离开 `.none` 时，`Context.setTransparency` 会损坏相邻位。

- [#13763](https://github.com/leanprover/lean4/pull/13763)
  添加 `MessageData.withExprHover`，用于创建在鼠标悬停时显示有关表达式的信息的消息。 `withExprHoverM` 变体捕获当前本地上下文。

- [#13758](https://github.com/leanprover/lean4/pull/13758)
  改进了 `Expr.instantiateBetaRevRange` 在 λ 函数未实例化的常见情况下更加高效，并且增加了应用程序中的表达式共享。

- [#13737](https://github.com/leanprover/lean4/pull/13737)
  将 `--plugin` 中插件文件名和初始化函数之间的分隔符从 `:` 更改为 `=`。这可以防止与 Windows 上驱动器前缀中的 `:` 发生冲突。

- [#13651](https://github.com/leanprover/lean4/pull/13651)
  用一种更高效、支持自定义配置语法和处理的系统取代了以前的策略配置系统。在简单的基准测试中，配置评估所需的时间是以前的 6.2%。 `declare_config_elab` 命令生成一个配置精译器，现在可以直接构造配置对象；以前它依赖于 `Meta.evalExpr'`，它涉及通过完整的术语精译、编译和评估过程来运行配置。生成的配置精译器现在还能够在常见情况下进行直接 `Syntax` 评估，跳过术语精译。此外，精译器更自由地接受配置：接受具有 `optConfig` 样式配置或配置项（包括例如 `namedArgument`s）形式的任何用户定义语法。导入`Lean.Elab.ConfigEval`即可使用系统；除了 `Lean.Elab.ConfigEval.Commands` 中的文档字符串之外，请参阅此模块以获取一些文档。此外，`simp` 策略现在还具有 `(user.optionName := ...)` 用户配置选项，可以使用全局 `tactic.simp.user.optionName` 选项进行声明；使用 `getUserConfigOption` 和 `withUserConfig` 在元程序中访问和设置它们。

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
  通过将可能令人困惑的“未使用的变量 `x`”消息替换为“未显式引用变量名称 `x`。可以删除绑定（如果未使用）或命名为 `_`（如果隐式使用）”，改进了 `unusedVariables` 检查器的消息。

- [#13710](https://github.com/leanprover/lean4/pull/13710)
  使仅测试的 `waitForMessage` 帮助程序立即中止
  当Lean语言服务器报告 fatalError 时，而不是
  阻塞直到外部测试框架超时终止进程。

- [#11313](https://github.com/leanprover/lean4/pull/11313)
  确保 `withSetOptionIn` 不会修改信息树或错误选项值的错误，从而避免使用 `visitM` 遍历信息树的检查器中出现崩溃。

- [#13595](https://github.com/leanprover/lean4/pull/13595)
  消除本身已弃用的定义内的 `Linter.deprecated` 警告。

- [#13209](https://github.com/leanprover/lean4/pull/13209)
  添加 `whileM`，与 `Lean.Loop.forIn` 相对应，承认一步展开引理 `whileM_eq`（无法证明原始 `partial def`）。 `Lean.Loop.forIn` 现在扩展为 `whileM`，因此 `repeat`/`while` 无需更改源代码即可继续工作，并且 `Spec.whileM`/`Spec.forIn_loop` `@[spec]` 定理让 `mvcgen` 在给定 Nat 变体和 `α ⊕ β` 不变量的情况下释放其身体。

- [#13670](https://github.com/leanprover/lean4/pull/13670)
  向 Verso 文档字符串添加了对块引用的支持，这在之前是缺失的。它还大大提高了文档字符串的 Verso->Markdown 渲染的稳健性，尤其是块引用行前缀的处理。

- [#13663](https://github.com/leanprover/lean4/pull/13663)
  取代了使用的 `check_cancel` 双向协调协议
  `tests/server_interactive/cancellation_par.lean` 使用单一策略
  `block_until_cancelled "<label>"`。标签的第一次调用
  一个承诺，打印 `<label>: blocked`，并在 `Core.checkInterrupted` 上循环
  直到取消令牌触发（然后 `finally` 解决承诺）。稍后
  对同一标签的调用等待该承诺 - 因此仅测试
如果第一次调用实际上退出了循环，则终止。如果取消
  无法传播，第二次调用的 `IO.wait` 永远阻塞，并且
  测试挂起（超时=失败），没有错误的成功路径。

- [#13548](https://github.com/leanprover/lean4/pull/13548)
  修复了从内存耗尽中恢复时可能出现的损坏。

- [#13613](https://github.com/leanprover/lean4/pull/13613)
  当注册 `foo` 的模块没有明显导入到当前文件中而只是作为中间表示加载时，使精译器拒绝 `@[foo]`。以前，此类使用默默地进行了精译，但导致了命令行和服务器行为的分歧，并导致 `lake shake --fix` 在连续运行时发生翻转 (#13599)。

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
  通过在精译器之间共享更多代码，确保 Verso 文档字符串和 Verso 模块文档之间元变量行为的一致性。它还改进了防止元变量泄漏时的错误消息。

- [#13528](https://github.com/leanprover/lean4/pull/13528)
  赋予 `specialize` 策略实例化通用量词的能力，而不是使用 `specialize h (y := v)` 语法的第一个量词。它还修复了 `MVarId.assertAfter` 未记录变量别名信息的问题，以及 `MVarId.replace` 和 `MVarId.replaceLocalDecl` 在计算依赖项时未考虑元变量的问题。此外，它还修复了一些未实例化的元变量错误，包括 Infoview 策略状态假设差异中的错误。

- [#13428](https://github.com/leanprover/lean4/pull/13428)
  修复了当服务器取消重新精译时并行策略组合器（`attempt_all_par`、`first_par`）泄漏其子任务的问题。通过 `CoreM.asTask` （及其 `MetaM`/`TermElabM`/`TacticM` 变体）生成的子任务会获得一个新的 `IO.CancelToken`，它以前没有到父令牌的链接； `cancelRec` 将设置命令级令牌，但子级继续运行。

- [#13569](https://github.com/leanprover/lean4/pull/13569)
  解决了 `IO.CancelToken` 上的两个审查点：

  * `set` 现在先解析底层 Promise，*然后*再写入 `Bool` 快速路径标志。因此，观察到 `isSet = true` 就意味着所有同步串联的 `onSet` 回调都已运行。此前的顺序是先写标志、再解析 Promise，这很容易埋下隐患：看到 `isSet = true` 的代码仍不能确信取消任务已经触发。
  * 底层 Promise 及其产生的任务现在保持私有。原有的 `task : Task (Option Unit)` 访问器已删除；调用方应使用 `onSet` 响应取消。结构体上的注释还说明：如果将来重新公开该任务，就必须重新审查 `set` 中 Promise 与 `Bool` 标志之间是否存在竞态。

- [#13303](https://github.com/leanprover/lean4/pull/13303)
  将 `IO.CancelToken` 从 `Init.System.IO` 移动到其自己的文件 `Init.System.CancelToken`，由 `IO.Promise Unit` 而不是 `IO.Ref Bool` 支持。这可以实现非轮询取消传播：令牌的底层承诺可以直接与 `IO.waitAny` 一起使用，并且可以注册回调以在请求取消时触发。

- [#13542](https://github.com/leanprover/lean4/pull/13542)
  将新的 `do` 精译器针对典型模式错误（#2215、#8304、#10393）产生的包罗万象的“语法匹配中不支持的模式”错误替换为来自常规模式变量收集器的正确诊断（例如“无效模式：需要用 `[match_pattern]` 标记的构造函数或常量”、“不明确的模式，使用完全限定名称”），指向有问题的模式。

- [#13359](https://github.com/leanprover/lean4/pull/13359)
  添加 `linter.redundantExpose` 选项（默认 `true`），当 `@[expose]` 或 `@[no_expose]` 属性无效时发出警告：

  - `@[expose]` 用于 `abbrev`（始终公开）或非 Prop 的 `instance`（始终公开）
  - `@[expose]` 用于 `@[expose] section` 内的 `def`（已由该 section 公开）
  - `@[expose]`/`@[no_expose]` 用于非 `module` 文件（没有模块系统）
  - `@[no_expose]` 位于默认情况下不会公开的声明上

- [#13492](https://github.com/leanprover/lean4/pull/13492)
  引入了对 `@[defeq]` 属性的更严格的推断和
  保留 PR 前行为的同伴 `@[backward_defeq]` 属性
  作为选择加入。

- [#13534](https://github.com/leanprover/lean4/pull/13534)
  概括了 `do` 块中的 `while` 语法，以便条件可以是任何 `doIfCond`，与 `if` 已接受的条件形式相同。因此，除了 `while cond do …` 和 `while h : cond do …` 之外，现在还支持 `while let pat := e do …` 和 `while let pat ← e do …`。之前单独的 `doWhile` 和 `doWhileH` 解析器及其附带的宏被统一为一个 `doWhile` 解析器，其宏委托给现有的 `doIf` 脱糖。

- [#13523](https://github.com/leanprover/lean4/pull/13523)
允许策略宏和精译器选择在失败时不自动回退到以前的宏/elab。 `throwUnsupportedSyntax` 不受影响。

- [#13363](https://github.com/leanprover/lean4/pull/13363)
  将 `whnfMatcher` 中从 `.reducible` 到 `.instances` 的透明度凹凸替换为 `canUnfoldAtMatcher` 中的显式允许列表。以前，在减少匹配判别式时，`whnfMatcher` 将展开所有 `implicitReducible` 定义和所有 `fromClass` 投影。这使得不可能在不默默影响匹配减少行为的情况下将定义标记为 `implicit_reducible` 。

- [#13512](https://github.com/leanprover/lean4/pull/13512)
  更改方程定理生成机制中要使用的 `whnfAux`
  可简化透明度 (`whnfR`) 而不是实例透明度 (`whnfI`)。
  以前，`Eqns.go` 中的循环会在左侧上展开实例，这
  与将 `dite`/`ite` 标记为 `implicit_reducible` 的用户交互不良：
  方程生成会减少超过 `dite` 并陷入困境而不是
  致力于分支。 `whnfI` 的最初动机（减少
  数字文字上 `match` 的 `Nat.rec ... (OfNat.ofNat 0)` 残差）是
  已经被周围的 `simpMatch?`/`simpIf?`/`simpTargetStar` 覆盖
  `Eqns.go` 中的步骤，因此完整的测试套件继续通过。

- [#13506](https://github.com/leanprover/lean4/pull/13506)
  当预期结果类型与 `PUnit` 不统一时，将 `unreachable!` 追加到 `break`-less `repeat` 的扩展中。然后，延续具有多态值，因此无需用户编写填充符即可推断出封闭的 do 块的结果类型，并且 `ControlInfo` 表示无中断 `repeat` 可以诚实地报告 `noFallthrough` — 后续元素上的死代码警告现在是可操作的。

- [#13507](https://github.com/leanprover/lean4/pull/13507)
  将 `do` 精译器发出的 `Pure.pure` / `Bind.bind` 应用程序公开为可插入闭包，因此外部表面语法（例如索引单子的 `ido` 表示法）可以在发出备用常量时重用完整的 `do` 机制。

- [#13491](https://github.com/leanprover/lean4/pull/13491)
  修复了 do-block `match` 的 `ControlInfo` 推论：匹配臂的折叠从 `ControlInfo.pure` 开始（默认为 `numRegularExits := 1`、`noFallthrough := false`），但 `alternative` 与 `numRegularExits` 和 `noFallthrough` 相加，因此折叠标识为 `{ numRegularExits := 0, noFallthrough := true }`。由于基地错误，一个手臂全部为 `break`/`continue`/`return` 的 `match` 报告了 `numRegularExits = 1` 和 `noFallthrough = false`，抑制了比赛后继续的死代码警告。该修复更正了 `InferControlInfo.lean` 中的推理处理程序和 `elabDoMatchCore` 中的折叠。

- [#13502](https://github.com/leanprover/lean4/pull/13502)
  将 `ControlInfo` 的死码信号一分为二。 `numRegularExits` 现在纯粹是语法上的：块将其延续连接到详细表达式中的次数，由 `withDuplicableCont` 作为连接点复制触发器 (`> 1`) 使用。新的 `noFallthrough : Bool` 断言封闭序列中的下一个 doElem 在语义上是不相关的； `false` 没有断言。不变式：`numRegularExits = 0 → noFallthrough`；反之则不成立。 `sequence` 派生 `noFallthrough := a.noFallthrough || b.noFallthrough` （并无条件聚合语法字段）； `alternative` 将其派生为 `a.noFallthrough && b.noFallthrough`。 `withDuplicableCont` 和 `ControlLifter.ofCont` 中的死代码警告门现在读取 `noFallthrough`。

- [#13494](https://github.com/leanprover/lean4/pull/13494)
阻止 `repeat` 推理处理程序报告 `numRegularExits := 0` 对于无中断主体。对于无中断的 `repeat` ，循环永远不会正常终止，因此 `0` 在语义上看起来更准确，但循环表达式仍然具有类型 `m Unit` ，并且循环后的 do 块的延续是携带该类型的。报告 `0` 会使精译器将该延续标记为死代码，但用户无法删除类型正确的它 — 除非封闭的 do 块的单子结果类型恰好是 `Unit`。将 `numRegularExits` 固定在 `1` （匹配 `for ... in`）可以消除这些虚假警告。

- [#13489](https://github.com/leanprover/lean4/pull/13489)
  修复了当存在没有标题的文档注释时 Verso Docstrings 中的嵌套级别被遗忘的错误。

- [#13486](https://github.com/leanprover/lean4/pull/13486)
  修复 `inferControlInfoSeq` 和 `ControlInfo.sequence` 以继续聚合 `breaks`/`continues`/`returnsEarly`/`reassigns` 过去的 `ControlInfo` 报告 `numRegularExits := 0` 的元素。以前，分析在这些元素处短路，因此推断信息中缺少任何尾随 `return`/`break`/`continue` 。精译框架仅在语法上跳过顶级 `return`/`break`/`continue` 的后续 doElem；对于每个其他 `numRegularExits == 0` 情况（例如，分支全部终止的 `match`/`if`/`try`，或没有 `break` 的 `repeat`），精译器会继续访问延续，然后 for/match 精译器会使用 `Early returning ... but the info said there is no early return` 触发其不变检查。通过此更改，推断的信息与精译器实际看到的内容相匹配，这也消除了对 #13479 中引入的 `repeat` 上的 `numRegularExits := 1` 解决方法的需要。

- [#13477](https://github.com/leanprover/lean4/pull/13477)
  修复了 #13475 中引入的基准回归：`eqnOptionsExt`
  正在使用 `.async .asyncEnv` asyncMode，它会在
  `checked` 环境并且可以阻止。切换到 `.local` — 一致
  与相邻的 `eqnsExt` 和其他声明缓存
  `src/Lean/Meta` — 恢复性能（
  `build/profile/blocked (unaccounted) wall-clock` 板凳移动 +33%
  回到基线）。 `.local` 在这里是安全的，因为 `saveEqnAffectingOptions`
  仅在顶级 `def` 精译和下游读者期间调用
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
  命名 `repeat` 语法 (`doRepeat`) 并在旧版和新版 do-精译器中为其安装专用的精译器。目前，两者都扩展为 `for _ in Loop.mk do ...`，与 `Init.While` 中现有的后备宏相同。

- [#13389](https://github.com/leanprover/lean4/pull/13389)
  向 `addInstance` 添加了两项验证检查，为实例声明中的常见错误提供早期反馈：

  1. **非类实例检查**：当实例目标类型不是类型类时出错。这捕获了为普通结构编写 `instance` 的常见错误。以前由电池 (`Batteries.Tactic.Lint.TypeClass`) 中的 `nonClassInstance` 检查器处理，现在直接在声明时检查。

  2. **不可能的参数检查**：当实例具有无法通过实例合成推断的参数时出现错误。具体来说，它标记非实例隐式参数，并且不会出现在任何后续实例隐式参数或返回类型中。以前，此类实例会被默默接受，但永远无法综合。

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  修复 `processDefDeriving` 以将 `meta` 属性传播到通过增量派生派生的实例，以便 `public meta section` 内的 `deriving BEq` 生成元实例。以前，派生的 `instBEqFoo` 未标记元，并且 LCNF 可见性检查器拒绝在别名上使用 `==` 的元定义 - 这是在将 verso 升级到 v4.30.0-rc1 时出现的。

- [#13404](https://github.com/leanprover/lean4/pull/13404)
  修复了 #12846，当 do 元素的延续具有不匹配的单子结果类型时，新的 do 精译器会产生令人困惑的错误。这些错误在位置（例如，指向 `let x ← value` 的值而不是 `let` 关键字）和内容（例如，提及用户从未编写过的 `PUnit.unit` ）上都具有误导性。

- [#13420](https://github.com/leanprover/lean4/pull/13420)
  修复了在构造函数名称带有宏作用域的宏作用域内定义 `coinductive` 谓词时出现的崩溃。现有的防护仅检查宏作用域的声明名称，缺少在宏引用内生成构造函数标识符并因此携带宏作用域的情况。这导致 `removeFunctorPostfixInCtor` 在宏范围编码的 `Name.num` 组件上出现崩溃。

- [#13413](https://github.com/leanprover/lean4/pull/13413)
为 do 块添加内部 `skip` 语法，供 `if` 和 `unless` 精译器使用，以替换隐式 else 分支中的 `pure PUnit.unit` 。这为精译器提供了一个专用的语法节点来附加更好的错误消息和位置信息，而不是合成 `pure PUnit.unit` ，后者会将内部细节泄漏到面向用户的错误中。

- [#13391](https://github.com/leanprover/lean4/pull/13391)
  在调用 `decLevel` 之前，在 `getDecLevel` 和 `getDecLevel?` 中添加关卡实例化和规范化。

- [#13395](https://github.com/leanprover/lean4/pull/13395)
  使 `structure` 的 `deriving Inhabited` 处理程序能够从结构父级继承 `Inhabited` 实例，使用与类父级相同的机制。这修复了 #9815 引入的回归，该回归失去了为表示为子对象字段的父级应用 `Inhabited` 实例的能力。有了这个 PR，现在它适用于层次结构中的所有父母。

- [#13399](https://github.com/leanprover/lean4/pull/13399)
  修复了 #12827，将鼠标悬停在 `for h : x in xs do` 中的 `for` 循环变量 `x` 和 `h` 上，在新的 do 精译器中没有显示类型信息。该修复在 `elabDoFor` 中的 `withLocalDeclsD` 引入循环变量和成员身份证明绑定器后添加了 `Term.addLocalVarInfo` 调用。

- [#13397](https://github.com/leanprover/lean4/pull/13397)
  改进了当 `do` 精译器生成在 `withDuplicableCont` 中失败 `checkedAssign` 的格式不正确的表达式时的错误报告。以前，失败被默默地丢弃，使得诊断 `do` 精译器中的错误变得困难。现在抛出一个描述性错误，显示连接点右侧及其未能分配到的元变量。

- [#13396](https://github.com/leanprover/lean4/pull/13396)
  修复了#12768，当绑定延续的结果类型在定义上但在语法上不独立于绑定变量时，新的 `do` 精译器产生了“声明有自由变量”内核错误。该修复将结果类型元变量的创建移至 `withLocalDecl` 之前，因此统一器必须减少依赖性。

- [#13325](https://github.com/leanprover/lean4/pull/13325)
  在注册 `@[simp]` 定理时添加警告，该定理的左侧在判别树中具有有问题的头符号：

  - **变量头**（`.star` key）：该定理将在每个 `simp` 步骤上进行尝试，这可能会很昂贵。警告指出这对于 `local` 或 `scoped` simpl 引理来说可能是可以接受的。由 `warning.simp.varHead` 控制（默认值：`true`）。
  - **无法识别的头**（`.other` 键，例如 λ 表达式）：该定理不太可能被 `simp` 应用。由 `warning.simp.otherHead` 控制（默认值：`true`）。

- [#13390](https://github.com/leanprover/lean4/pull/13390)
  更改线性 BEq 推导策略，在比较构造函数索引时使用 `Nat.decEq` 而不是 `decEq`。由于构造函数索引始终为 `Nat`，因此直接使用 `Nat.decEq` 更合适，因为它是 `@[reducible]`，而通用 `decEq` 仅是半可约的，并且不会以 `.reducible` 透明度展开。这使得生成的代码更加透明友好。

- [#13356](https://github.com/leanprover/lean4/pull/13356)
  将环境从 Batteries 上游移入 Lean 核心。

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
  添加了对模块名称中操作系统禁止的名称和字符的检查。  这实现了 mathlib 的 `modulesOSForbidden` 检查器的功能。

- [#13262](https://github.com/leanprover/lean4/pull/13262)
  扩展了 Lean 的语法，允许在表达式中使用显式的宇宙级别，例如 `e.f.{u,v}`、`(f e).g.{u}` 和 `e |>.f.{u,v} x y z`。它修复了宇宙级别会被归因于错误表达式的错误；例如 `x.f.{u}` 将被解释为 `x.{u}.f`。它还更改了顶级声明的语法，不允许标识符和宇宙级别列表之间存在空格，并且修复了 `checkWsBefore` 解析器中的一个错误，该错误不会检测 `optional` 解析器中的空格。

- [#13332](https://github.com/leanprover/lean4/pull/13332)
  使用类型跨越多个隐式宇宙的 `mut` 变量修复 `for` 循环的宇宙统一。旧方法对每个变量使用 `ensureHasType (mkSort mi.u.succ)`，这会生成像 `max (?u+1) (?v+1) =?= ?u+1` 这样的约束，宇宙求解器无法分解。新方法在递减级别上使用 `getDecLevel`/`isLevelDefEq` ，生成 `max ?u ?v =?= ?u` ，由 `solveSelfMax` 直接处理。

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
添加一个选择加入的检查器 (`set_option simp.rfl.checkTransparency true`)，当 `rfl` simp 定理的左侧和 右侧在 `.instances` 透明度下定义不相等时发出警告。糟糕的 rfl-simp 定理（那些仅在较高透明度下成立的定理）会在整个系统中产生问题，因为 `simp` 和 `dsimp` 在有限的透明度下运行。 检查器建议两个修复：使用 `id rfl` 作为证明（以删除 `rfl` 状态），或将相关常量标记为 `[implicit_reducible]`。

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
  更改在模式中使用时结构实例符号的精译（例如 `s matches { x := 1, y := [] }`），以便结构的默认值不用于精译模式。其动机是默认值经常导致令人惊讶的过于特定的模式。现在它会报告“字段丢失”错误。可以使用 `{ x := 1, .. }` 省略号表示法来抑制该错误，其行为与以前相同。漂亮的打印机也经过修改以与此功能保持同步。 **重大更改：** 使用结构实例表示法的模式可能需要缺少字段或添加 `..`（视情况而定）。

- [#13195](https://github.com/leanprover/lean4/pull/13195)
  添加了对将选项标记为已弃用的支持。当通过 `set_option` 使用已弃用的选项时，会发出警告（由 `linter.deprecated.options` 控制）。

- [#13255](https://github.com/leanprover/lean4/pull/13255)
在 `do` 块 `let` 和 `have` 声明中添加了对 let 配置选项（`(eq := h)`、`+nondep`、`+usedOnly`、`+zeta`）的支持，与术语级别 `let`/`have` 中可用的行为相匹配。配置选项被 `let mut` 拒绝，因为它们与可变绑定不兼容。 `+postponeValue` 和 `+generalize` 也在 `do` 块中被拒绝。

- [#13250](https://github.com/leanprover/lean4/pull/13250)
  扩展 `doLet`、`doLetElse`、`doLetArrow` 和 `doHave` 解析器以接受 `letConfig`（例如 `(eq := h)`、`+nondep`、`+usedOnly`、`+zeta`），匹配术语级别 `let`/`have` 的语法。精译器被调整以处理移位的语法索引，但尚未处理配置；这将在 stage0 更新后的后续 PR 中完成，允许使用正确的引用模式。

- [#13245](https://github.com/leanprover/lean4/pull/13245)
  扩展了点函数表示法 (`.f`) 的Lean语法，以添加对显式模式 (`@.f`)、显式宇宙 (`.f.{u,v}`) 以及两者同时 (`@.f.{u,v}`) 的支持。这还包括对涉及重载函数的错误的修复，该错误用于对函数未精译的声明发出错误的弃用警告。

- [#13232](https://github.com/leanprover/lean4/pull/13232)
  修复了编译在索引归纳类型上使用 `casesOn` 的相互递归定义时出现的崩溃（例如 `Vect`）。 `WF.Unfold` 中的 `splitMatchOrCasesOn` 函数断言 `matcherInfo.numDiscrs = 1`，但对于索引类型，casesOn 递归器具有多个判别式（索引 + 大前提）。该修复使用最后一个判别式（大前提）并让 `cases` 策略自动处理索引判别式。

- [#13002](https://github.com/leanprover/lean4/pull/13002)
  添加 `deprecated_module` 命令，将当前模块标记为已弃用。当另一个模块导入已弃用的模块时，在精译期间会发出警告，建议替换导入。

- [#13205](https://github.com/leanprover/lean4/pull/13205)
  修复 `FirstTokens.seq (.optTokens s) .unknown` 以返回 `.unknown`。这种情况会发生，例如当可选（第一个标记为 `.optTokens s`）后跟解析器类别（第一个标记为 `.unknown`）时。以前 `FirstTokens.seq` 返回 `.optTokens s`，忽略了可选值可能为空并且解析器类别可能具有任何第一个标记的事实。这里正确的行为是返回 `.unknown`，这表明第一个标记可以是任何东西。

- [#13220](https://github.com/leanprover/lean4/pull/13220)
  添加 `checkSystem` 调用到几个可以运行的代码路径
  延长时间而不检查取消、心跳限制或
  堆栈溢出。这提高了取消机制的响应能力
  在语言服务器中。

- [#13108](https://github.com/leanprover/lean4/pull/13108)
  添加 `deprecated_syntax` 命令，将语法类型标记为已弃用。当精译已弃用的语法（术语、策略或命令）时，会发出检查器警告。当宏定义在其扩展中使用不推荐使用的语法时，在引用预检查期间也会发出警告。

- [#13219](https://github.com/leanprover/lean4/pull/13219)
  将 `hasAssignableMVar`、`hasAssignableLevelMVar` 和 `isLevelMVarAssignable` 从 `MetavarContext.lean` 移动到新的 `Lean.Meta.HasAssignableMVar` 模块，将它们从通用 `[Monad m] [MonadMCtx m]` 函数更改为 `MetaM` 函数。这使得可以在递归遍历中添加 `checkSystem` 调用，从而确保在非常昂贵的计算过程中进行取消和心跳检查。

````

# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Library"
%%%

```markdown

- [#13863](https://github.com/leanprover/lean4/pull/13863)
更改`BitVec`上的电子匹配注释，以避免自动从`getMsbD`理论转到`getLsbD`理论。关键原因是所有引理都已经在 `getMsbD` 和 `getLsbD` 之间重复了。因此，每当我们连接它们时，所有引理都会在两种变体中触发，即使通常一个引理就已经足够了。为了在不显着降低证明强度的情况下实现这一点，我们引入了两项更改：
1. 编写或注释一些额外的`BitVec.getMsbD`引理以匹配`BitVec.getLsbD`的推理能力。最值得注意的是`getMsbD_eq_getElem`，因此`getMsbD`可以尝试自行转换为`getElem`。
2. 引入`grind_pattern getMsbD_eq_getLsbD => x.getMsbD i, x.getLsbD _`，这样每当我们在范围内的相同值上同时拥有`getMsbD`和`getLsbD`时，我们就会尝试将它们匹配。我们预计这个注释*通常*不会触发太多，因为大多数 `get*D` 可能可以转换为 `getElem` 并从那里开始工作。

- [#13850](https://github.com/leanprover/lean4/pull/13850)
删除了每当 `c[i]` 出现在 E 图中时就会触发 `getElem?_pos` 的 grind 注解。我们这样做是为了避免仅仅因为 `c[i]` 可用而对 `c[i]?` 进行推理。每当 `c[i]?` 在范围内时，实例化 `getElem?_pos` 的触发器仍然存在，以便推动 grind 证明或反驳边界检查。

- [#13689](https://github.com/leanprover/lean4/pull/13689)
使得 `whileM` 的展开引理可以从 `Lean.Order.MonadTail` 实例导出。公共入口点是`Init.Internal.Order.While`中的`whileM_eq_of_monadTail`；底层固定谓词`whileM.Pred`和`Init.While`中的条件`whileM_eq`引理保留在模块内部。

- [#13787](https://github.com/leanprover/lean4/pull/13787)
修复了 `String.split` 的一个小文档错误。

- [#13748](https://github.com/leanprover/lean4/pull/13748)
修复了当通过`induction`达到目标时，前提选择会默默地丢弃相关前提。

- [#13750](https://github.com/leanprover/lean4/pull/13750)
细化 MePo 前提选择，以便 (1) 候选对象仅限于定理，匹配 `SineQuaNon` 和 `SymbolFrequency` 已经使用的约定，以及 (2) 结果按 `(iteration, score)` 字典顺序排序，而不是单独按分数排序。

- [#13747](https://github.com/leanprover/lean4/pull/13747)
修复了 MePo 前提选择器返回得分最低的前提，而不是最好的前提。

- [#13457](https://github.com/leanprover/lean4/pull/13457)
添加了仍然在 `ZipForStd.ByteArray` 下游本地携带的缺失的 `ByteArray` 推送和 `set!` 引理。

- [#13654](https://github.com/leanprover/lean4/pull/13654)
添加 `Dyadic.divAtPrec a b prec`，返回最大二元，精度最多为 `prec`，小于或等于 `a/b`（当 `b = 0` 时，返回 `0`）。镜像现有的`invAtPrec`，还提供了特征引理`divAtPrec_mul_le`和`lt_divAtPrec_add_inc_mul`。

- [#13718](https://github.com/leanprover/lean4/pull/13718)
通过消除 Async.sleep 和 IO.sleep 的所有问题并改进 ContextAsync.race 的工作方式，修复了 context_async.lean 中的测试。

- [#13567](https://github.com/leanprover/lean4/pull/13567)
添加了 Locale 和 LocaleSymbols 以用于可配置的日期/时间格式。它还修改alignedWeekOfMonth 和weekOfYear，因此它包含一周第一天的参数。

- [#13565](https://github.com/leanprover/lean4/pull/13565)
修复了即使 TZ 和 TZDIR 存在，丢失 /etc/localtime 也会导致失败的问题。

- [#13675](https://github.com/leanprover/lean4/pull/13675)
添加一个 `WallTime` 类型，表示自 `1970-01-01T00:00:00` 本地时间以来的纳秒时间点。它还删除了 `sinceUNIXEpoch` 和 `AssumingUTC` 后缀，因为 `Timestamp` 暗示 UTC，而 `WallTime` 暗示它基于 WallTime 纪元（在注释中定义为 `1970-01-01T00:00:00`）。

- [#13693](https://github.com/leanprover/lean4/pull/13693)
概括了关于 `++` 的许多 `Vector` 引理，以便两个附加向量不再需要共享相同的大小索引：`sum_append`、`prod_append`、它们的 `_nat` / `_int` 变体、`flatMap_append`、 `unattach_append`、`eraseIdx_append_of_lt_size`、`eraseIdx_append_of_length_le`。

- [#13521](https://github.com/leanprover/lean4/pull/13521)
防止在没有 `LEAN_MMAP` 的配置上`readModuleDataParts #[]` 中未定义的行为。以前这会导致索引越界。

- [#13549](https://github.com/leanprover/lean4/pull/13549)
如果没有足够的内存来加载模块，则使`readModuleDataParts`报告更清晰的错误。

- [#13627](https://github.com/leanprover/lean4/pull/13627)
将 `UInt8.ofNatTruncate` 重命名为 `UInt8.ofNatClamp`。

- [#13583](https://github.com/leanprover/lean4/pull/13583)
将`Invariant`、`StringInvariant`和`StringSliceInvariant`从`abbrev`更改为`@[spec_invariant_type, simp, grind =] def`，以便它们在证明状态中作为命名常量的应用保持可见（其中`SymM`不展开`def`）并且可以被检测为`isSpecInvariantType` 的不变类型。 `@[simp, grind =]`注释确保它们仍然在`simp`和`grind`下按需展开。

- [#13582](https://github.com/leanprover/lean4/pull/13582)
向`Std.Do.SPred`和`Std.Do.PostCond`添加了几个与蕴涵相关的引理，用于程序验证证明自动化期间的目标分解。

- [#12965](https://github.com/leanprover/lean4/pull/12965)
引入了推理单子Lean代码的新基础。最终我们将在这些新基础之上移植`mvcgen`，以使框架更加通用和健壮。

- [#13546](https://github.com/leanprover/lean4/pull/13546)
当使用调用 libuv 的 Lean 函数时，防止内存耗尽变成段错误

- [#13511](https://github.com/leanprover/lean4/pull/13511)
将异步和 Http 从内部移动到标准

- [#12151](https://github.com/leanprover/lean4/pull/12151)
引入了 Server 模块，一个异步 HTTP/1.1 服务器。

- [#13400](https://github.com/leanprover/lean4/pull/13400)
将错误名称`String.Pos.skipWhile_le`修复为`String.Pos.le_skipWhile`。

- [#13398](https://github.com/leanprover/lean4/pull/13398)
从 H1.lean 中删除私有

- [#12146](https://github.com/leanprover/lean4/pull/12146)
引入了 H1 模块，这是一个纯 HTTP/1.1 状态机，可以增量解析传入字节流并发出响应字节，而不会产生副作用。

- [#13357](https://github.com/leanprover/lean4/pull/13357)
基于对 core 中默认容器上的所有只读操作的系统审查。在合理的情况下，它会对缺乏注释的高阶操作应用专门注释，或者在道德上应该借用的参数上借用注释（例如，迭代容器时的容器）。

- [#13200](https://github.com/leanprover/lean4/pull/13200)
为 `List`、`Array` 和 `Vector` 添加 `prod`（乘法折叠），镜像现有的 `sum` 接口。包括基本的 simp 引理（`prod_nil`、`prod_cons`、`prod_append`、`prod_singleton`、`prod_reverse`、`prod_push`、`prod_eq_foldl`）、Nat 专用引理（`prod_pos_iff_forall_pos_nat`、`prod_eq_zero_iff_exists_zero_nat`、`prod_replicate_nat`）、Int 专用引理（`prod_replicate_int`）、跨类型引理（`prod_toArray`、`prod_toList`），以及带有 grind 模式的 `Perm.prod_nat`。

- [#13273](https://github.com/leanprover/lean4/pull/13273)
添加了全面的公共接口，用于构建最大程度的共享
表达式应用程序并在 `Sym` 框架中执行 β 缩减。
这些函数之前是在 VC 生成器和 cbv 中本地定义的
策略，并且是下游基于`SymM`的工具所需要的。

- [#13155](https://github.com/leanprover/lean4/pull/13155)
验证`String.dropWhile`和`String.takeWhile`功能。

- [#13235](https://github.com/leanprover/lean4/pull/13235)
将 `std::memcmp` 用于 `ByteArray` `BEq` 和 `DecidableEq`。

- [#13172](https://github.com/leanprover/lean4/pull/13172)
在`Std.Internal.UV.System`中添加借用注释。

```

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Tactics"
%%%

```markdown

- [#13859](https://github.com/leanprover/lean4/pull/13859)
修复了当用户提供的预策略（例如`sym => mvcgen' with (clear h)`中的`clear`）重写本地上下文时内核拒绝的问题。

- [#13857](https://github.com/leanprover/lean4/pull/13857)
实现交互式`sym =>`模式的`dsimp`策略。它还添加了用于声明 `dsimp` 变体的 DSL。

- [#13680](https://github.com/leanprover/lean4/pull/13680)
使`mvcgen'`可用作`sym => …`块内的步骤。剩余的 VC 成为后续研磨步骤的子目标； `mvcgen' invariants` 内联工作，`mvcgen' invariants?` 被拒绝。

- [#13854](https://github.com/leanprover/lean4/pull/13854)
实现声明 `SymM` 的 `dsimp` 变体的语法。

- [#13793](https://github.com/leanprover/lean4/pull/13793)
通过类型检查错误消息将有关类型不正确目标的新策略提示扩展为`instances`透明度，以帮助处理比“不建议的`unfold`”更复杂的情况。

- [#13636](https://github.com/leanprover/lean4/pull/13636)
使 `simpa using h` 接近**可缩减**透明度，而不是之前使用的环境（默认/半可缩减）透明度，从而使 `simpa using h` 在 simp 集更改下更具可预测性。先前的行为可作为 `simpa using! h` 使用（在 #13833 中引入）。

- [#13833](https://github.com/leanprover/lean4/pull/13833)
添加 `simpa ... using! e` 语法作为并行形式
`simpa ... using e`。目前 `using!` 的行为与 `using` 相同 — 两者
以环境（默认/半可缩减）透明度关闭目标。

- [#13771](https://github.com/leanprover/lean4/pull/13771)
添加一个新的`impossible by t`策略组合器并将其连接到
默认建议集`try?`。

- [#13825](https://github.com/leanprover/lean4/pull/13825)
实现可重用归约`DSimproc`（`beta`、`zeta`、`zetaAll`、`dsimpProj`、`dsimpMatch`）的集合，将它们公开，以便调用者可以将它们组合成自己的`Methods`，并且修复一些错误。

- [#13824](https://github.com/leanprover/lean4/pull/13824)
在`Sym.dsimp`中添加了简化绑定器的功能。

- [#13823](https://github.com/leanprover/lean4/pull/13823)
在`SymM`中添加`dsimp`的基本基础设施。

- [#13812](https://github.com/leanprover/lean4/pull/13812)
修复了`mconstructor`、`mleft`和`mright`在`mhave`块内失败（#13691），以及`mspecialize`在`mrevert; mintro`往返后失败。这两种情况都源于假设命名`Expr.mdata`从假设连接叶子泄漏到非叶子位置（内部目标，或`SPred.imp`目标的先行词），其中下游模式匹配没有看穿它。

- [#13766](https://github.com/leanprover/lean4/pull/13766)
移动 `evalSuggest` 组合器和跟踪处理程序调度
从语法类型上的硬编码`match`到现有的
`tryTacticElabAttribute`注册机制，带来`try?`的
符合正常策略和交互的扩展模型`grind`。

- [#13774](https://github.com/leanprover/lean4/pull/13774)
使 `try?` 的 `expandUserTactic` 遍历 `TryThisInfo` 的信息树
节点（在 #10524 中引入）而不是解析渲染的 `Try this:` 消息
  文本。先前的方法会从消息日志中抓取以 `  [apply] ` 为前缀的行；
消息日志，当线路格式改变时，这会中断。

- [#13430](https://github.com/leanprover/lean4/pull/13430)
使一个空的`by`块在后台运行`try?`并显示其建议，同时仍然产生通常的未解决目标诊断。隐式的`try?`仅提供信息——除了发出消息之外，它不会改变精译行为。行为由新选项`tactic.tryOnEmptyBy`控制，目前默认禁用；将其设置为 `true` 以选择加入。默认值可能会在未来版本中翻转。

- [#13699](https://github.com/leanprover/lean4/pull/13699)
添加了新的 `grind` 配置选项 `genLocal`，用于控制
局部定理（例如假设）的最大项生成。它默认为
`8`，与`gen`相同的值并且适用于任何时候
`grind` 实例化一个定理，其起源是局部的而不是声明
或用户提供的术语。由于用户几乎无法控制所使用的模式
对于局部定理，更严格的生成界限是合理的默认值。

- [#13698](https://github.com/leanprover/lean4/pull/13698)
改进了`grind`诊断输出，以便使用局部假设
当电子匹配定理以其面向用户的名称和实例化出现时
柜台，而不是默默地删除或匿名举报
`local.<idx>` 标识符。

- [#13644](https://github.com/leanprover/lean4/pull/13644)
添加了一个实验性策略`mvcgen'`，它将很快取代`mvcgen`。它已使用基于 `SymM` 的新框架从头开始重新实现，以进行高效的符号评估，并且对于某些综合基准测试，其性能比 `mvcgen` 高出 100 倍以上。 `mvcgen'` 渴望与 `mvcgen` 一起实现功能完整。目前已知的例外情况包括连接点共享、本地规范的引入和较小的错误。

- [#13678](https://github.com/leanprover/lean4/pull/13678)
确保可以将鼠标悬停在 fun_induction 中的函数名称上。修复#13673

- [#13665](https://github.com/leanprover/lean4/pull/13665)
替换 `handleProj` 和 `simplifyAppFn` 中的 `Meta.mkCongrArg` 调用点被替换为直接重用 `Sym` 指针缓存中已有类型的 `congrArg` 结构。同一文件中的一些杂散不合格 `inferType` / `getLevel` / `isDefEq` 调用也会通过缓存的 `Sym` 等效项进行路由。

- [#13640](https://github.com/leanprover/lean4/pull/13640)
添加每当 `dsimp`（或仅 rfl `simp`）重写触发时发出的跟踪事件
因为 `[backward_defeq]` 标记定理（即，不会
已申请但没有`set_option backward.defeqAttrib.useBackward true`）。

- [#13635](https://github.com/leanprover/lean4/pull/13635)
修复了 `Sym.simp` 崩溃（“意外的内核投影项
在简化过程中”）当匹配器 iota-reduction 时触发
通过 struct-η 公开内核 `Expr.proj` 术语。例如，`do`
带有 `for` 循环的块，其状态是元组，其中 `Sym.simp`
展开等式引理，然后下降到解构
  模式匹配。

- [#13624](https://github.com/leanprover/lean4/pull/13624)
修复了可能导致崩溃的 `grind` 同余表不变违规
当`ite`分支被延迟内化时（在条件变为`True`之后）
或`False`），并且该分支的等价类后来与另一个分支合并。

- [#13625](https://github.com/leanprover/lean4/pull/13625)
修复了当`cast`（或`Eq.rec`、`Eq.ndrec`、`Eq.recOn`）应用于尚未内部化的参数时触发的`grind`内部错误。 `pushCastHEqs` 在内部化 `e` 的参数之前发出 `e ≍ a`，因此 heq 的 `rhs` 没有 enode，并且调试健全性检查被触发。现在，调用在参数内部化后运行。

- [#13623](https://github.com/leanprover/lean4/pull/13623)
修复了`grind`投影传播器中的证明构造问题。

- [#13622](https://github.com/leanprover/lean4/pull/13622)
修复了 `grind` AC 不变检查器中的另一个问题。

- [#13614](https://github.com/leanprover/lean4/pull/13614)
修复了`grind` AC 中的不变量。待办事项队列中的方程并未完全简化。

- [#13612](https://github.com/leanprover/lean4/pull/13612)
改进了`SymM`使用的宇宙统一符。

- [#13611](https://github.com/leanprover/lean4/pull/13611)
修复了简化 `have` 表达式时`Sym.simp` 中的断言失败，该表达式的绑定器类型取决于望远镜中先前的绑定器。

- [#13368](https://github.com/leanprover/lean4/pull/13368)
添加基础设施以帮助诊断采用 `unfold` 等策略的案例
仅在`.default`透明度下将目标保持在类型正确的状态，
导致`rw`/`simp`在`.instances`透明度下失败。

- [#13593](https://github.com/leanprover/lean4/pull/13593)
禁用`grind`的`NoopConfig`中基于模型的理论组合（`mbtc`），这是派生策略`lia`、`linarith`、`cutsat`、`order`使用的基本配置，以及`ring`。如果没有这个修复，这些策略可能会通过理论组合进行浪费性的推理，导致它们在并非旨在解决的问题上运行很长时间（或达到确定性超时）。通过此修复，正如预期的那样，这些策略在超出范围的问题上很快就会失败。

- [#13590](https://github.com/leanprover/lean4/pull/13590)
使`lia`（和`grind`的算术大小写启发式）识别
其先行词是算术谓词 `And` 或 `Or` 的蕴涵如下
相关的案例分割候选人。此前，`Arith.isRelevantPred`仅匹配
`Not`、`LE`、`LT`、`Eq`、`Dvd`。使用`splitImp := false`（默认），
仅当 `p` 为时，含义 `p → q` 才会添加为分割候选者
与算术相关，所以像 `(b ≤ e ∧ e < b + c → a ≤ e ∧ e < a + d)` 这样的假设
从未登记为候选人。 cutsat/lia 然后会找到令人满意的
分配给它已经被告知的约束，但是那个分配
不一定满足最初的含义，产生不好的结果
#13575 中报告了反例。

- [#13585](https://github.com/leanprover/lean4/pull/13585)
添加了 `ringMaxDegree` 配置选项（默认为 `1024`），该选项限制了 `grind` 环求解器处理的多项式的最大次数。多项式超过此阈值的等式约束将被丢弃（每个目标报告一次问题），从而防止`r ^ (2 ^ 250 - 1)`等输入的病理程度爆炸。

- [#13558](https://github.com/leanprover/lean4/pull/13558)
添加选项 `grind.ematch.diagnostics`，该选项跟踪 E 匹配定理实例如何相互依赖。启用后，`grind` 会为每个新定理实例记录其生成的术语参与匹配的先前实例的集合。这会生成一个超图`{thm_1, ..., thm_n} => thm`，描述每个实例化的来源。

- [#13560](https://github.com/leanprover/lean4/pull/13560)
修复了`propagateBetaEqs`（`Lean.Meta.Tactic.Grind.Beta`）中的错误
其中通过贝塔减少引入的新等式/项被添加到目标中
不检查生成阈值。新事实的产生
是 λ 的最大生成，函数`f`，及其
参数，加一。如果没有阈值检查，β 减少可以
在自相似的 λ 上无限级联，例如
`(fun b => f (b + 1)) = fun b => f b`，持续生产
`f n = f (n + 1)` 对于每个 `n`。该修复聚合了参数生成
在阈值检查之前并在生成的生成时退出
达到`maxGeneration`。

- [#13301](https://github.com/leanprover/lean4/pull/13301)
添加了直接在给定策略上运行 `evalSuggest` 的 `try? => tac` 语法，对于单独测试 `try?` 机器非常有用。它还添加了一个 server_interactive 测试 (`cancellation_par.lean`)，该测试演示了并行策略组合器的取消错误。

- [#13532](https://github.com/leanprover/lean4/pull/13532)
即使 `lhs = rhs` 未内化在 E 图中（现有的优化），也会通知卫星求解器有关断言的等式 `lhs = rhs`。该通知允许不检查等价类（例如同态扩展）的求解器直接对断言的等式做出反应。它在等价类合并之前触发，以便将 `lhs` 和 `rhs` 标记为其内部术语的求解器在 `Solvers.mergeTerms` 触发 `processNewEq` 之前注册它们。

- [#13476](https://github.com/leanprover/lean4/pull/13476)
改进了`apply`策略（以及`rewrite`等相关策略）命名和标记其余子目标的方式。现在*在*计算子目标标签之前过滤掉分配的元变量。因此，当只剩下一个未分配的子目标时，它会继承输入目标的标签，而不是被赋予新的后缀标签。

- [#13474](https://github.com/leanprover/lean4/pull/13474)
修复了 `sym =>` 交互模式中的错误，其中元变量由 `isDefEq` 分配的目标（例如通过 `apply Eq.refl`）未被修剪。 `pruneSolvedGoals` 之前仅过滤掉标记为不一致的目标，因此已分配的目标将作为未解决的目标徘徊。现在，它还删除已分配元变量的目标。

- [#13472](https://github.com/leanprover/lean4/pull/13472)
修复了 `sym =>` 交互模式中的错误，其中卫星解算器（`lia`、`ring`、`linarith`）如果其自动 `intros + assertAll` 预处理步骤已关闭目标，则会抛出内部错误。此前，`evalCheck`使用了`liftAction`，丢弃了闭包结果，因此后续的`liftGoalM`调用因缺乏主要目标而失败。 `liftAction` 现在已拆分，因此调用者可以区分封闭目标和子目标情况，并在预处理已完成工作时跳过求解器主体。

- [#13453](https://github.com/leanprover/lean4/pull/13453)
修复了将 `Nat` 等式传播到载体类型不是 `Int` 的有序结构时 `grind` 中的内核错误（例如 `Rat`）。辅助`Lean.Grind.Order.of_nat_eq`引理专门用于`Int`，因此当转换目的地不同时，内核会拒绝该应用程序。

- [#13451](https://github.com/leanprover/lean4/pull/13451)
修复了 `Sym.introCore.finalize` 中的错误，其中原始元变量通过延迟分配无条件分配，即使没有引入绑定器也是如此。结果，`Sym.intros`将返回`.failed`，而目标元变量已经被静默分配，从而混淆了依赖于`isAssigned`的下游代码（例如`mvcgen'`中的VC过滤器）。

- [#13448](https://github.com/leanprover/lean4/pull/13448)
修复了`Sym.simp`中的回归，其中左侧包含模式变量上的λ（例如`∃ x, a = x`）的重写规则无法匹配具有语义等效结构的目标。

- [#13088](https://github.com/leanprover/lean4/pull/13088)
将 `PowIdentity` 类型类（来自 https://github.com/leanprover/lean4/pull/13086) 连接到 `grind` 环求解器的 Groebner 基础引擎。

- [#13086](https://github.com/leanprover/lean4/pull/13086)
添加一个 `Lean.Grind.PowIdentity` 类型类，声明 `x ^ p = x` 对于可交换半环的所有元素，`p` 作为 `outParam`。

- [#13289](https://github.com/leanprover/lean4/pull/13289)
在`Sym.Arith/`中添加算术标准化的共享基础设施，
为 `Sym.simp` 的 arith pre-简化过程和最终的 arith 奠定基础
统一grind的`CommRing`模块。

- [#13272](https://github.com/leanprover/lean4/pull/13272)
扩展 sym 标准化器以应用缩减（投影、匹配/ite/cond、Nat
算术）在所有位置，而不仅仅是内部类型。之前，值 `v` 出现在
当 `T(v)` 被归一化时，类型 `T(v)` 可以保持不变，打破了以下不变量：
定义上相等的类型在规范化后结构上是相同的。

- [#13271](https://github.com/leanprover/lean4/pull/13271)
重构 sym 规范化器中的实例规范化以正确处理
\`Grind.nestedProof\` 和 \`Grind.nestedDecidable\` 标记。之前，规范化器
当它无法重新合成命题实例时，会报告问题
由\`grind\`本身提供或由用户通过\`haveI\`提供。现在，重新合成优雅地失败
在值位置上回退到原始实例，同时保持严格的内部类型。

- [#13202](https://github.com/leanprover/lean4/pull/13202)
修复了文件末尾环境扩展的心跳超时问题，该超时问题无法通过提高限制来避免。

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Compiler"
%%%

```markdown

- [#13796](https://github.com/leanprover/lean4/pull/13796)
优化 `String.compare` 将其变成 1 个而不是 2 个 `memcmp` 调用。

- [#13788](https://github.com/leanprover/lean4/pull/13788)
生成专门的代码，用于对形状已知的值调用`dec`。这减轻了分支预测压力`lean_dec_ref_cold`，因为构造函数的形状现在应该被编译到可执行文件中。

- [#13669](https://github.com/leanprover/lean4/pull/13669)
通过概述“冰冷”路径并执行小型微架构优化来优化`lean_dec_ref_cold`。后者更好，因为它向 LLVM 明确表明我们相信指针仅使用 48 位。

- [#13545](https://github.com/leanprover/lean4/pull/13545)
将 LLVM 从版本 19 升级到版本 22。这带来了高达 5% 指令的总体性能提升，具体取决于基准测试。

- [#13493](https://github.com/leanprover/lean4/pull/13493)
确保`import`优雅地处理来自文件系统的`EINTR`错误。

- [#13464](https://github.com/leanprover/lean4/pull/13464)
在`lean_io_process_spawn`的分叉子分支（`chdir`故障和`execvp`故障路径）中将`exit(-1)`替换为`_exit(-1)`。 `exit` 刷新继承的 C stdio 缓冲区，该缓冲区与父级共享底层文件描述符。如果父级打开了一个包含未刷新数据的文件句柄，则该数据将被写入子级中的文件，然后在父级稍后刷新时再次写入，从而导致重复输出。 `_exit` 跳过 stdio 刷新，因此父级的缓冲写入不再复制到继承的文件中。

- [#13435](https://github.com/leanprover/lean4/pull/13435)
修复了 EmitC 中的一个错误，该错误可能是由于使用字符串文字 `"\x01abc"` 引起的
Lean并导致 C 编译器错误。

- [#13427](https://github.com/leanprover/lean4/pull/13427)
修复了`io.cpp`中的两个小错误：
1. Windows错误路径`Std.Time.Database.Windows.getNextTransition`发生资源泄漏
2. 当可执行文件是最大路径长度的符号链接时，Linux 上的`IO.appPath` 会发生缓冲区溢出。

- [#13421](https://github.com/leanprover/lean4/pull/13421)
修复了扩展重置重用过程中的一个问题，该问题在极少数情况下会导致段错误。

- [#13409](https://github.com/leanprover/lean4/pull/13409)
将 qsort 正确地专门化到 lt 函数上

- [#13401](https://github.com/leanprover/lean4/pull/13401)
将选项 `LEAN_MI_SECURE` 添加到我们的 CMake 构建中。可以配置值`0`
通过`4`。每个增量都可以在 mimalloc 中实现额外的内存安全缓解，但代价是
2%-20% 的指令数，具体取决于基准测试。我们的系统中默认禁用该选项
发布版本是因为我们的大多数用户在安全敏感情况下不会使用Lean运行时。
部署生产Lean代码的分销商和组织应考虑启用该选项：
这是一项强化措施。各个级别的效果可在  https://github.com/microsoft/mimalloc/blob/v2.2.7/include/mimalloc/types.h#L56-L60. 查看。

- [#13392](https://github.com/leanprover/lean4/pull/13392)
修复了`lean_io_prim_handle_read`中的堆缓冲区溢出，该溢出是通过
分配大小计算中的整数溢出。此外，它还放置了几个检查的
对所有相关分配路径进行算术运算，以消除未来潜在的溢出
反而陷入崩溃。现在，有问题的代码会抛出内存不足错误。

- [#13384](https://github.com/leanprover/lean4/pull/13384)
修复了当结构构造函数接收不可计算实例作为实例隐式参数时出现的编译器崩溃。

- [#13234](https://github.com/leanprover/lean4/pull/13234)
修复了 Lean 未与 libuv 链接时的构建问题。

- [#13233](https://github.com/leanprover/lean4/pull/13233)
修复了未设置 `LEAN_MULTI_THREAD` 时的运行时构建问题。

- [#13270](https://github.com/leanprover/lean4/pull/13270)
添加了 `Runtime.hold`，这通过持有对它的引用来确保其参数在调用点之前保持活动状态。这对于不安全代码（例如 FFI）非常有用，这些代码依赖于Lean对象直到程序中的某个点之后才被释放。

- [#13258](https://github.com/leanprover/lean4/pull/13258)
在缓存未命中时在 `checkInferTypeCache` 中添加 `Core.checkInterrupted` 调用，允许在大型类型推理遍历期间检测取消。以前，在处理大型表达式（例如 BVDecide 证明项）时，`inferTypeImp` 可以运行 >100 毫秒，而不会进行任何中断检查，从而导致 IDE 取消无响应。

- [#13242](https://github.com/leanprover/lean4/pull/13242)
修复了编译器对 `String` 构造函数上模式匹配的处理，以符合新的 `String` 表示形式。

- [#13128](https://github.com/leanprover/lean4/pull/13128)
通过使用 `CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY` 而不是 Lake 插件的硬编码 `lib/lean` 路径来修复 Windows 开发版本。在 Windows 上，DLL 必须放置在`bin/` 中的可执行文件旁边，但插件路径被硬编码为`lib/lean`，导致无法找到 stage0 DLL。

```

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Pretty-Printing"
%%%

```markdown

- [#13761](https://github.com/leanprover/lean4/pull/13761)
修复了 `pp.universes` 选项会导致没有宇宙的常量不使用解展开器或点表示法的问题。例如，即使 `Iff` 没有宇宙级别，`p ↔ q` 也会打印为 `Iff p q`。

- [#13446](https://github.com/leanprover/lean4/pull/13446)
改进了元变量的漂亮打印及其在 InfoView 中的悬停。 InfoView 中的悬停现在包括有关特定元变量的信息 - 它包括诸如元变量的类型、是否是阻止的延迟赋值以及它被阻止的元变量以及元变量的本地上下文中存在哪些变量的差异等信息。此外，如果命名元变量无法访问，现在可以用墓碑漂亮地打印它们。延迟赋值漂亮的打印现在可以更可靠地遵循赋值链来查找待处理的元变量。

- [#13438](https://github.com/leanprover/lean4/pull/13438)
当`pp.instantiateMVars`为真时，使宇宙级别漂亮的打印机实例化级别元变量。

- [#13030](https://github.com/leanprover/lean4/pull/13030)
改进了级别元变量的漂亮打印：它们现在使用每个定义的索引而不是每个模块的内部标识符进行打印。此外，`+`与周围空间统一打印在水平表达式中。 **重大元编程更改：** 级别漂亮打印应使用 `delabLevel` 或 `MessageData.ofLevel`；诸如 `format` 或 `toString` 之类的函数无法访问索引，因为它们存储在当前元上下文中。如果没有索引信息，元变量将使用原始内部标识符打印为 `?_mvar.nnn`。 **注意：** 由于记录级别元变量索引的分配计数，心跳计数器也会增加得更快。在某些测试中，我们需要将 `maxHeartbeats` 增加 20-50% 进行补偿，但不会出现相应的减速。

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Documentation"
%%%

```markdown

- [#13864](https://github.com/leanprover/lean4/pull/13864)
更新管道运算符文档字符串以提高准确性和实用性。这些运算符不是 Haskell 惯用的，因此旧文本是不正确的，最好解释一下其行为，而不是引用其他语言。

- [#13656](https://github.com/leanprover/lean4/pull/13656)
记录如何执行 LLVM 升级。

```

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Server"
%%%

```markdown

- [#13525](https://github.com/leanprover/lean4/pull/13525)
添加 `Unit` 的 `FromJson`/`ToJson` 实例 - 编码为 `{}` - 以及 `FromJson`/`ToJson` 的文档。

- [#13260](https://github.com/leanprover/lean4/pull/13260)
通过 `PublishDiagnosticsParams` 上的新 `isIncremental` 字段添加对增量诊断的服务器端支持，该字段仅在客户端在 `LeanClientCapabilities` 中设置 `incrementalDiagnosticSupport` 时由语言服务器使用。

- [#13348](https://github.com/leanprover/lean4/pull/13348)
修复了策略自动完成会在空策略块的整个尾随空白中生成策略完成项的错误。由于 #13229 进一步限制顶级 `by` 块对缩进敏感，因此此 PR 调整逻辑以仅在“适当”缩进级别显示完成项。

- [#13257](https://github.com/leanprover/lean4/pull/13257)
在空的`by`块中添加测试基础设施和策略完成测试。

```

# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Lake"
%%%

```markdown

- [#13949](https://github.com/leanprover/lean4/pull/13949)
添加一个 `LAKE_RESTORE_ARTIFACTS` 环境变量，该变量覆盖工作区的默认 `restoreAllArtifacts` 配置，镜像 `LAKE_ARTIFACT_CACHE` 覆盖 `enableArtifactCache` 的方式。

- [#13936](https://github.com/leanprover/lean4/pull/13936)
修复了未正确设置 `depPkgs` 的传递依赖关系的问题，该传递依赖关系被依赖关系图中更高级别的包覆盖。

- [#13843](https://github.com/leanprover/lean4/pull/13843)
使`lake lint --builtin-lint`在公共（`OLeanLevel.exported`）级别导入模块系统目标，而不是`private`。环境检查现在会在此类模块的公共表面上进行检查，以匹配下游消费者对它们的看法。非模块目标保留其先前的行为（`private`级别），并且通过`lintLogExt`记录的文本检查器警告在级别更改期间保留，因为该扩展存储统一的OLean条目。

- [#13563](https://github.com/leanprover/lean4/pull/13563)
使`Glob.ofString?`公开，允许从Mathlib中删除最后一次使用的`open private`。

- [#13683](https://github.com/leanprover/lean4/pull/13683)
将已编译的 Lake 配置（例如，`lakefile.olean`）从包的 `.lake/config` 目录移动到工作区的 `.lake/config`。这消除了共享依赖项的工作区之间潜在的源争用。

- [#13601](https://github.com/leanprover/lean4/pull/13601)
更改 Lake 的模块导入图处理以等待任何 `needs` 目标或其他额外依赖项（例如云发布）的完成。这既使 `needs` 目标能够影响标头处理，并防止它们与所述处理竞争。

- [#13600](https://github.com/leanprover/lean4/pull/13600)
修复了 Lake 问题，即 `meta import` 的传递导入的中间表示未包含在 Lake 提供给 Lean 的导入工件中（例如，通过 `--setup`）。使用 Lake 工件缓存时，由于缺少中间表示，可能会产生“丢失数据文件”错误。

- [#13559](https://github.com/leanprover/lean4/pull/13559)
修复了 Lake 构建监视器排空作业队列中的竞争条件。

- [#13513](https://github.com/leanprover/lean4/pull/13513)
除了 #13431 中添加的环境检查器之外，还扩展了 `lake lint --builtin-lint` 来支持文本检查器（即使用 `logLint`/`logLintIf` 的文本检查器）。构建期间发出的 Text-检查器警告通过新的 `Lean.Linter.lintLogExt` 环境扩展保留到每个模块的 `.olean` 中； `lake lint` 重新运行目标模块的构建并读回条目，将它们与环境检查器输出一起报告。

- [#13516](https://github.com/leanprover/lean4/pull/13516)
将 `namespace Lake` 添加到 `Lake.Util.Opaque`，其中缺少它。从技术上讲，对于任何使用 `Opaque` 而不使用 `open Lake` 的代码来说，这是一个重大更改，但希望没有人这样做。

- [#13500](https://github.com/leanprover/lean4/pull/13500)
添加了对空 `lake build` 调用的检查（因为空构建通常表示配置错误）。没有作业的构建现在将打印“Nothing to build”。在没有配置默认目标的情况下调用`lake build`将产生警告。这将在未来升级为错误。可以使用新的 `--allow-empty` 命令行界面选项来抑制警告（以及未来的错误）。

- [#13431](https://github.com/leanprover/lean4/pull/13431)
向 Lake 添加内置环境检查支持，可通过 `lake lint` 标志访问。它还引入了两个来自 Mathlib 上游的内置检查器（`defLemma` 和 `checkUnivs`）和一个 `builtinLint` 包配置选项。

- [#13456](https://github.com/leanprover/lean4/pull/13456)
向 Lake 添加类型缩写 `GitRev`，用于表示 Git 修订版本的 `String` 值。此类修订可能是 SHA1 提交哈希、分支名称或 Git 更复杂的说明符之一。

- [#13423](https://github.com/leanprover/lean4/pull/13423)
添加了 `JobAction.reuse` 和 `JobAction.unpack`，它们为构建监视器的作业正在执行的操作提供更多信息标题。 `reuse` 在使用 Lake 缓存中的工件时设置，`unpack` 在解压模块 `.ltar` 档案并发布（Reservoir 或 GitHub）档案时设置。

- [#13393](https://github.com/leanprover/lean4/pull/13393)
添加了对 `lake builtin-lint` 命令的基本支持，该命令用于运行环境检查器，并且将来将扩展以处理核心语法检查器。

- [#13340](https://github.com/leanprover/lean4/pull/13340)
修复了 Lake 问题，即库构建不会产生有关错误导入的信息性错误（与模块构建不同）。

- [#13282](https://github.com/leanprover/lean4/pull/13282)
引入了 `LakefileConfig`，它可以从 Lake 配置文件构建，无需构建完整的 `Package` 所需的所有信息。此外，工作区现在附加了格式良好的属性，可确保其包的工作区索引与其在工作区中的索引相匹配。最后，构面配置图现在有自己的类型：`FacetConfigMap`。

- [#13277](https://github.com/leanprover/lean4/pull/13277)
修复了函数名称中面向公众的拼写错误：`Module.checkArtifactsExsist` -> `Module.checkArtifactsExist`。

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___31___0-_LPAR_2026-06-13_RPAR_--Other"
%%%

```markdown

- [#13185](https://github.com/leanprover/lean4/pull/13185)
添加了新的增量模块序列化函数，可一次保存/加载单个模块，并通过 dep 区域和压缩器状态显式共享，从而概括了现有的批量 saveModuleDataParts 接口。

- [#13740](https://github.com/leanprover/lean4/pull/13740)
扩展 `lake shake --explain` 还涵盖了保留超出直接引用范围的导入的原因，例如抖动注释。

- [#13530](https://github.com/leanprover/lean4/pull/13530)
添加一个 `trace.profiler.serve` 选项，启用后，将在临时 `127.0.0.1` 端口上提供与 Firefox Profiler 兼容的配置文件 JSON，并在用户的默认浏览器中打开
`https://profiler.firefox.com/from-url/...`
其行为类似于 `samply`。获取配置文件后，服务器将关闭。

- [#13630](https://github.com/leanprover/lean4/pull/13630)
修复了在 `public section` 下的模块模式下启用 `set_option diagnostics true` 时出现的“未知常量”错误。诊断输出可能会引用记录在展开计数器中的私有声明，例如`_match_*`和`_sparseCasesOn_*`；之前构建消息失败，因为环境处于导出模式并且无法解析这些名称。 `Lean.Meta.Diagnostics.reportDiag` 和 `Lean.Meta.Tactic.Simp.Diagnostics.reportDiag` 中的诊断打印路径现在在 `withoutExporting` 下运行。

- [#13589](https://github.com/leanprover/lean4/pull/13589)
确保 `lean --error=tag` 标志实际上在提升的错误上设置非零退出代码。

- [#13553](https://github.com/leanprover/lean4/pull/13553)
修复了未启用初始化程序执行时`runInitAttrs`抛出的错误消息中的拼写错误。该消息之前提到的是`enableInitializerExecution`（单数），但实际功能是`enableInitializersExecution`（复数）。

- [#13520](https://github.com/leanprover/lean4/pull/13520)
使用要应用原子的谓词扩展 `grind` 同态演示。

- [#13499](https://github.com/leanprover/lean4/pull/13499)
修复了 Linux aarch64 上`leantar`的架构检测，确保它与 Lean 正确捆绑。

- [#13497](https://github.com/leanprover/lean4/pull/13497)
添加了巴黎 Lean 黑客马拉松的示例。它演示了用户如何实现https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#13132](https://github.com/leanprover/lean4/pull/13132)
添加警告的`linter.redundantVisibility`选项（默认`true`）
当可见性修饰符无效时，因为它与默认值匹配
当前上下文：

- `module` 文件中 `public section` 之外的`private`，其中声明
默认情况下已经在模块范围内
- `public` 在非`module` 文件中或`public section` 内，其中
默认情况下声明已经公开

- [#13211](https://github.com/leanprover/lean4/pull/13211)
添加 `unlock_limits` 命令，将 `maxHeartbeats`、`maxRecDepth` 和 `synthInstance.maxHeartbeats` 设置为 0，禁用所有核心资源限制。也使得 `maxRecDepth 0` 意味着“无限制”（与 `maxHeartbeats 0` 的现有行为匹配）。

- [#13226](https://github.com/leanprover/lean4/pull/13226)
更新 `release_checklist.py` 以处理 CMake 版本变量上的 `CACHE STRING ""` 后缀。 `CACHE STRING`格式是在`releases/v4.30.0`分支中引入的，但脚本的解析未更新以匹配，导致错误失败。

```
