/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/
import VersoManual

import Manual.Meta

import Verso.Code.External

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Verso.Code.External (lit)

open Lean (Syntax SourceInfo)

#doc (Manual) "验证 Lean 证明" =>
%%%
file := "ValidatingProofs"
tag := "validating-proofs"
number := false
htmlSplit := .never
%%%

本节讨论如何验证用 Lean 表达的证明。

根据具体情况，可能需要额外步骤来排除误导性的证明。
尤其重要的是区分 {tech}[诚实]的证明尝试（只需防范无害错误）与可能的 {tech}[恶意]证明尝试（主动试图误导用户）。

特别地，当目标是创建有效证明时，我们使用 {deftech}_诚实_ 一词。
这允许证明和元代码（策略、属性、命令等）中存在错误和缺陷，但不允许明显只用于绕过系统的代码（例如使用 {option}`debug.skipKernelTC`）。
注意，API 函数上的 {keyword}`unsafe` 标记与该 API 是否可被不诚实地使用无关。

相反，我们用 {deftech}_恶意_ 描述刻意欺骗或误导用户、利用缺陷或破坏系统的代码。
这包括未经审查的 AI 生成证明和程序。

此外，区分“定理是否有有效证明”和“定理陈述是什么意思”这两个问题也很重要。

下面给出一系列逐步加强的检查，并说明如何执行、检查的含义，以及它们防范的错误或攻击。

# 蓝色双勾
%%%
tag := "validating-blue-check-marks"
%%%

在日常使用 Lean 时，只需检查定理陈述旁的蓝色双勾，即可确认定理已被证明。

## 操作说明

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--The-Blue-Double-Check-Marks--Instructions"
%%%
在 Lean 交互工作时，定理证明完成后，代码左侧的槽中会出现蓝色双勾。

:::figure "蓝色双勾"
![编辑器槽中显示蓝色双勾的定理](/static/screenshots/doublecheckmarks.png)
:::

## 含义

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--The-Blue-Double-Check-Marks--Significance"
%%%
蓝色勾号表示定理陈述已依据当前文件及其导入文件中定义的语法和类型类实例成功精译，并且 Lean 内核已接受一个由当前文件及其导入文件中声明的定义、定理和公理推出的该定理证明。

## 信任

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--The-Blue-Double-Check-Marks--Trust"
%%%
如果相信形式化定理陈述符合其预期的非形式含义，相信导入库的作者是{tech}[诚实]的、已检查库中定理表达了预期含义，且没有声明和使用不健全的公理，则此检查有意义。

## 防护

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--The-Blue-Double-Check-Marks--Protection"
%%%
:::listBullet "🛡️"
此检查可防范：

* 当前定理的未完成证明（缺少目标、策略错误）
* 当前定理中显式使用 {lean}`sorry`
* {tech}[诚实]的元程序和策略缺陷
* 仍在后台检查的证明
:::

## 备注

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--The-Blue-Double-Check-Marks--Comments"
%%%
可以在 Visual Studio Code 扩展设置中更改该符号。
非 VS Code 编辑器可能使用不同的指示方式。

运行 {lake}`build`{lit}` +Module`（其中 {lit}`Module` 指包含定理的文件），并确认成功且没有错误消息或警告，可提供相同保证。

# 打印公理
%%%
tag := "validating-printing-axioms"
%%%

即使定理依赖项中显式使用了 {lean}`sorry` 或存在未完成证明，蓝色双勾仍会出现。
由于 {lean}`sorry` 和未完成证明都会被精译为公理，可以列出证明所依赖的公理来检测它们。

## 操作说明

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Printing-Axioms--Instructions"
%%%
:::keepEnv
```lean -show
inductive TheoremStatement : Prop where | intro
theorem thmName : TheoremStatement := .intro
```

在定理声明后写入 {leanCommand}`#print axioms thmName`，将 {lean}`thmName` 替换为定理名称，并确认报告中只有内置公理 {name}`propext`、{name}`Classical.choice` 和 {name}`Quot.sound`。

:::

## 含义

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Printing-Axioms--Significance"
%%%
该命令打印定理及其依赖定理所使用的公理集合。
上面的三个公理是 Lean 逻辑的标准公理，没有危害。

* 如果报告 {name}`sorryAx`，则该定理或其某个依赖使用了 {lean}`sorry`，或以其他方式未完成。
* 如果报告 {name}`Lean.trustCompiler`，则使用了本地求值；说明见下文。
* 任何其他公理都表示声明并使用了自定义公理，此时定理只相对于这些公理的可靠性有效。

## 信任

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Printing-Axioms--Trust"
%%%
如果相信形式化定理陈述符合其预期的非形式含义，并相信导入库的作者是{tech}[诚实]的，则此检查有意义。

## 防护

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Printing-Axioms--Protection"
%%%
:::listBullet "🛡️"
（除上述列表外）

* 未完成的证明
* 显式使用 {lean}`sorry`
* 自定义公理
:::

# 使用 `lean4checker` 重新检查证明
%%%
tag := "validating-lean4checker"
%%%

重新检查构建项目时存储在 {tech}[`.olean` 文件]中的证明，可以捕获一小类缺陷以及某些不诚实的证明呈现方式。

## 操作说明

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Re-Checking-Proofs-with--lean4checker--Instructions"
%%%
使用 {lake}`build` 构建项目，在包含目标定理的模块上运行 `lean4checker --fresh`，并确认没有报告错误。

## 含义

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Re-Checking-Proofs-with--lean4checker--Significance"
%%%
`lean4checker` 工具读取 `lean` 构建时存储的声明和证明（即 {tech}[`.olean` 文件]），并通过内核重放它们。
它信任 {tech}[`.olean` 文件]在结构上是正确的。

## 信任

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Re-Checking-Proofs-with--lean4checker--Trust"
%%%
如果相信形式化定理陈述符合其预期的非形式含义，并相信导入库的作者不会非常狡猾地{tech}[恶意]行事、不会破坏用户系统，也不会利用 Lean 的可扩展性改变定理陈述的解释，则此检查有意义。

## 防护

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Re-Checking-Proofs-with--lean4checker--Protection"
%%%
:::listBullet "🛡️"
（除上述列表外）

* Lean 核心处理内核状态时的缺陷（例如并行处理证明或处理导入时的缺陷）
* 有意绕过该状态的元程序或策略（例如使用低级功能添加未经检查的定理）
:::

## 备注

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Re-Checking-Proofs-with--lean4checker--Comments"
%%%
由于 `lean4checker` 读取 {tech}[`.olean` 文件]时不验证格式，此检查容易受到攻击者制作无效 `.olean` 文件的影响（例如无效指针、字符串中的无效数据）。
Lean 策略和其他元代码运行时可以执行任意操作。
导入决意{tech}[恶意]攻击者创建的库并在没有进一步保护的情况下构建它们，可能危及用户系统，此后就不再有有意义的检查可做。
我们建议在 CI 中运行 `lean4checker`，以额外防范 Lean 处理声明时的缺陷，并遏制简单攻击。
[lean-action](https://github.com/leanprover/lean-action) GitHub Action 可通过设置 `lean4checker: true` 提供此功能。

不使用 `--fresh` 标志时，可以让工具只检查部分模块，并假定其他模块正确（例如受信任的库），以加快处理。

# 黄金标准：`comparator` 与外部检查器
%%%
tag := "validating-comparator"
%%%

为了防止极其{tech}[恶意]的证明破坏 Lean 对定理陈述的解释或用户系统，还需要额外步骤。
这只应在高风险场景（证明市场、高奖励证明竞赛、未对齐 AI）中必要。

## 操作说明

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Gold-Standard___--comparator--and-external-checkers--Instructions"
%%%
在受信任环境中写下定理*陈述*（即“挑战”），然后按其文档启用外部检查器，将挑战和拟议证明一并交给 [`comparator`](https://github.com/leanprover/comparator) 工具。

## 含义

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Gold-Standard___--comparator--and-external-checkers--Significance"
%%%
Comparator 会在沙箱环境中构建证明，以防范构建步骤中的{tech}[恶意]代码。
证明项会导出为序列化格式。
在沙箱外、远离可能的恶意代码时，它验证导出格式，使用 Lean 内核和/或外部检查器重放证明，并确保已证明的定理陈述与受信任挑战文件中的陈述一致。

## 信任

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Gold-Standard___--comparator--and-external-checkers--Trust"
%%%
如果受信任挑战文件中的定理陈述正确，且用于构建可能{tech}[恶意]代码的沙箱安全，则此检查有意义。

## 防护

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Gold-Standard___--comparator--and-external-checkers--Protection"
%%%
:::listBullet "🛡️"
（除上述列表外）

* 主动实施{tech}[恶意]行为的证明
* 某些所用检查器中存在、但并非同时存在于所有检查器中的实现缺陷。
:::

## 备注

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Gold-Standard___--comparator--and-external-checkers--Comments"
%%%
在本文撰写时，`comparator` 支持使用官方 Lean 内核和独立开发、以 Rust 实现的外部检查器 [`nanoda`](https://github.com/ammkrn/nanoda_lib)。[Lean Kernel Arena](https://arena.lean-lang.org/) 提供更多外部检查器，可手动使用以获得更高信心。

# 遗留问题

%%%
tag := "Lean-__________________--Validating-a-Lean-Proof--Remaining-Issues"
%%%
即使遵循使用 comparator 检查证明的黄金标准，仍有一些假设：

* Lean 逻辑是可靠的。
* `comparator` 工具提供的连接机制正确。
* `comparator` 使用的沙箱安全。
* 不存在同时影响所有所用检查器的实现缺陷。
* 受信任挑战文件中的定理陈述不存在人为错误或误导性呈现。

  如果怀疑定理的含义并非表面所示，就必须仔细调查其陈述和所有引用的定义，尤其要注意自定义记法和类型类。
  一些外部检查器提供原始美化打印能力，不受源文件中解析器或记法变化的影响。

# 关于 `Lean.trustCompiler`（截至 Lean 4.28.0）
%%%
tag := "validating-trustCompiler"
%%%

Lean 支持通过本地求值进行证明。
{tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native` 策略或特定策略（尤其是 {tactic}`bv_decide`）会使用此功能，生成调用已编译 Lean 代码进行计算的证明项，而内核信任该计算。

封装在{tech}[诚实]策略中的特定用法（例如 {tactic}`bv_decide`）通常值得信任。
受信任代码库更大（包括 Lean 的编译工具链和标准库中的库注解），但仍是固定且经过审查的。

一般使用（{tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native` 或直接使用 {name}`Lean.ofReduceBool`）时，只要项的本地求值与内核求值不一致，就可能创建无效证明。
特别地，对于库中的每个 {attr}`implemented_by`/{attr}`extern` 属性，替代实现与原实现语义等价这一点都会成为受信任代码库的一部分。

所有这些用法都会在 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` 中显示为公理 {name}`Lean.trustCompiler`。
外部检查器（`lean4checker`、`comparator`）无法检查此类证明，因为它们无法访问 Lean 编译器。
需要这种级别的检查时，证明必须避免使用本地求值。

从 Lean 4.29.0 起，{tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native` 和 {tactic}`bv_decide` 策略不再使用 {name}`Lean.trustCompiler`，而是为本地计算断言的每次计算引入一个专用公理。{name}`Lean.trustCompiler` 机制已弃用，最终会被移除。
