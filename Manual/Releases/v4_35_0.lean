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

#doc (Manual) "Lean 4.35.0 (2026-10-12)" =>
%%%
tag := "release-v4.35.0"
file := "v4.35.0"
%%%

此版本合入了 214 项更改。
除下面列出的 78 项新增功能
和 57 项修复外，
还有 18 项重构，
7 项文档改进，
23 项性能改进，
2 项测试套件改进，
以及 29 项其他更改。

# 亮点
%%%
file := "Highlights"
tag := "Manual-Releases-v4_35_0-Highlights"
%%%

Lean 4.35.0 最主要的新功能是 `vcgen`：它是 `mvcgen` 更快、更通用的后继。
此外新增 `lake check` 和 `lake comparator`，使用 Lean 内核检查项目；若用户要求，还可用现随工具链分发的多个独立内核检查。
策略方面重新设计了 `rwa`，`constructor` 在必须选择构造器时发出警告，{tactic}`grind` 则通过将 `BitVec` 与固定位宽整数转换为 `Nat`、`Int` 算术，证明更多目标。
{name}`Decidable` 改用基于 {name}`Bool` 的新定义，使更多等式可由 `rfl` 证明。

_本亮点一节由 Juanjo Madrigal 贡献。_

## `mvcgen` 的后继 `vcgen`
%%%
file := "vcgen-___-the-successor-of--mvcgen"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--vcgen-___-the-successor-of--mvcgen"
%%%

Lean 4.35 提供验证条件生成器 {tactic}`vcgen`，大多数情况下可直接替代 {tactic}`mvcgen`；后者现已弃用。改进包括：

1. *深度嵌入。* `vcgen` 基于 `Std.WP` 框架，其最弱前置条件解释适用于任意程序类型，而不局限于单子：除任意单子中的 `do` 程序外，也可验证能够定义最弱前置条件的深度嵌入语言，例如 [x64 汇编](https://github.com/sgraf812/kraken/blob/829c9468974ea0f725abc268baa6dbb9403ccd36/Kraken/X64/Examples/P3.lean#L85-L95) 或 [WebAssembly](https://github.com/sgraf812/talos/blob/9875d3b4f9a17f9e93211ba20062bd3f78f045aa/wp/WasmWP/Gcd.lean#L69-L82)。这种通用性正是更名的原因。

2. *更通用的断言语言。* 程序逻辑的断言可位于任意完备格，因此 `vcgen` 不仅支持状态谓词，也支持概率逻辑、分离逻辑等断言语言；推广的框架保持概念则能让断言中未改变的部分跨调用保留。

3. *性能。* `vcgen` 基于新的 `SymM` 框架，只将共享目标上下文内部化到 `grind` 的 E-图一次，因此 `vcgen … with finish` 可在全部验证条件间复用它。在 [AddSubCancel](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/tests/bench/vcgen/cases/Cases/AddSubCancel.lean) 基准中，有状态循环体重复 2200 次，`vcgen` 耗时 0.32 秒，而 `mvcgen` 为 66 秒；内核检查所得证明分别耗时 0.53 秒和 246 秒。`vcgen` 运行时间随程序大小线性增长，每次循环迭代约 0.14 毫秒。

:::figure "`mvcgen` 与 `vcgen` 对比"
![`mvcgen` 与 `vcgen` 对比](/static/screenshots/mvcgen_vs_vcgen.png)
:::

:::figure "`vcgen` 与内核对比"
![`vcgen` 与内核对比](/static/screenshots/vcgen_vs_kernel.png)
:::

`vcgen` 仍标记为实验性功能：`set_option experimental.vcgen true` 表示接受此状态并关闭对应警告。参考手册章节和{ref "vcgen-tactic-tutorial" (remote := "tutorials")}[使用 `vcgen` 验证命令式程序]教程介绍此策略。

## 使用 `lake check` 和 `lake comparator` 检查项目
%%%
file := "Checking-Projects-with--lake-check--and--lake-comparator"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Checking-Projects-with--lake-check--and--lake-comparator"
%%%

此前，用外部内核检查已完成的开发，或用 {ref "validating-comparator"}[comparator] 检查证明是否符合给定陈述，需要安装配置多个独立工具。
本版本将这些功能全部纳入 Lake。

[#14990](https://github.com/leanprover/lean4/pull/14990) 新增 {ref "lake-comparator"}[`lake check`]：构建当前项目默认目标、导出结果，再通过内核重放；若任何内容使用{ref "standard-axioms"}[标准公理]以外的公理，则失败。
[#14885](https://github.com/leanprover/lean4/pull/14885) 与 [#15146](https://github.com/leanprover/lean4/pull/15146) 添加 comparator 的前端 `lake comparator`：给定包含定理陈述的挑战模块和解答模块，检查解答中的各指定定理是否证明挑战中的相同陈述、是否仅用允许的公理，以及是否被内核接受。
默认从 `comparator.json` 读取配置（[#15147](https://github.com/leanprover/lean4/pull/15147)）：

```
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["imo2024_p1"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

两个命令都将项目视为不可信输入。
构建与导出在 `bubblewrap` 沙箱中完成：隐藏用户主目录，仅在解析依赖时允许网络访问（[#15005](https://github.com/leanprover/lean4/pull/15005)）；内核则在独立进程中运行（[#15055](https://github.com/leanprover/lean4/pull/15055)）。
沙箱目前仅适用于 Linux。

发行工具链现在还包含外部检查器 `lean4lean`（[#15048](https://github.com/leanprover/lean4/pull/15048)）、`nanoda`（[#15099](https://github.com/leanprover/lean4/pull/15099)）、`con-leche`（[#15130](https://github.com/leanprover/lean4/pull/15130)）、`con-ron`（[#15153](https://github.com/leanprover/lean4/pull/15153)），以及使用加固内存分配器构建的 `leanchecker` 版本 `leanchecker-paranoid`（[#14884](https://github.com/leanprover/lean4/pull/14884)）。
添加 `--paranoid` 后，两个命令除运行 Lean 自身内核外，还会运行上述全部检查器；只有每个检查器都接受时才接受项目（[#15145](https://github.com/leanprover/lean4/pull/15145)）：

```
lake check              # Lean's kernel, standard axioms only
lake check --paranoid   # ...and every bundled external checker
```

在其他地方（例如虚拟机或计算资源更丰富的第三方）产生的导出文件，可直接用 `lake check --from-export`、`lake comparator --solution-from-export` 或 `lake comparator --challenge-from-export` 检查（[#15157](https://github.com/leanprover/lean4/pull/15157)）；`leanchecker` 本身也新增 `--from-export` 标志（[#15050](https://github.com/leanprover/lean4/pull/15050)）。

相关地，[#14953](https://github.com/leanprover/lean4/pull/14953) 移除了自二月起已弃用的 `Lean.reduceBool`、`Lean.reduceNat` 与 `Lean.trustCompiler` 公理。
由于 `Lean.reduceBool` 和 `Lean.reduceNat` 的定义引用 `Lean.trustCompiler`，导入它们的每个环境看起来都使用此公理，使 `lake check` 之类的全环境公理检查意义减弱。
v4.34.0 的运行时引用计数工作也在继续，三项修复已同时回移到 v4.34.1。
[#15241](https://github.com/leanprover/lean4/pull/15241) 和 [#15289](https://github.com/leanprover/lean4/pull/15289) 封堵了极大输入导致官方内核释放后使用的另外两条路径；[#15288](https://github.com/leanprover/lean4/pull/15288) 修复线程共享对象的相关问题，官方内核默认配置不会这样共享，但其他基于 Lean 的检查器可能会。
不基于 Lean 运行时的内核不受影响。

## 策略变更
%%%
file := "Tactic-Changes"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Tactic-Changes"
%%%

### 重新设计的 `rwa`
%%%
file := "A-Redesigned--rwa"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Tactic-Changes--A-Redesigned--rwa"
%%%

{tactic}`rwa` 此前只是 `rw ...; assumption` 的简单宏，因此 {tactic}`assumption` 步骤可能关闭无关目标。
[#14937](https://github.com/leanprover/lean4/pull/14937) 将其改为仅操作调用时的目标和重写产生的旁目标：`rwa [rules]` 重写目标并用假设关闭它；`rwa [rules] at h` 则重写 `h`，再用 `h` 本身而非任意匹配假设关闭主目标。
若单靠重写就已关闭目标，它会建议改用 {tactic}`rw`：

```lean (name := rwaWarn)
example (a : Nat) : a + 0 = a := by
  rwa [Nat.add_zero]
```
```leanOutput rwaWarn (severity := warning)
`rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [Nat.add_zero]

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
```

`rwa [rules] at h₁ h₂` 和 `rwa [rules] at *` 已弃用；改用 `rw [rules] at h₁ h₂ <;> assumption`。

### `constructor` 在需要选择时发出警告
%%%
file := "constructor--Warns-When-It-Has-to-Choose"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Tactic-Changes--constructor--Warns-When-It-Has-to-Choose"
%%%

多个构造器匹配目标时，{tactic}`constructor` 此前静默选用第一个。
对于析取，这意味着总选左侧，而这往往不是用户意图。
[#14854](https://github.com/leanprover/lean4/pull/14854) 使这种情况产生警告：

```lean (name := ctorWarn)
example : 2 ≤ 3 ∨ 3 ≤ 2 := by
  constructor
  decide
```
```leanOutput ctorWarn (severity := warning)
Tactic `constructor` applied constructor `Or.inl`, but `Or.inr` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
```

新的 `constructor!` 保持此前行为，但不警告。

### 为 `lia` 与 `grobner` 提供额外事实
%%%
file := "Extra-Facts-for--lia--and--grobner"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Tactic-Changes--Extra-Facts-for--lia--and--grobner"
%%%

[#15116](https://github.com/leanprover/lean4/pull/15116) 允许 {tactic}`lia`、{tactic}`grobner` 像 {tactic}`grind` 一样接收事实和引理列表，不必先用 `have` 加入上下文：

```lean
def double (n : Nat) : Nat := 2 * n

theorem double_def (n : Nat) : double n = 2 * n := rfl

example (n : Nat) (h : double n ≤ 10) : n ≤ 5 := by
  lia [double_def n]
```

## `grind` 中的同态
%%%
file := "Homomorphisms-in--grind"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Homomorphisms-in--grind"
%%%

[#14727](https://github.com/leanprover/lean4/pull/14727) 在 v4.34.0 准备的 `[grind hom]`、`[grind hom_pred]` 属性基础上，完成 {tactic}`grind` 的{ref "grind-hom"}[同态]支持。
带这些属性的定理描述如何将一种类型的项转换到 {tactic}`grind` 已有求解器的其他类型。
Lean 自带 {name}`Fin`、{name}`BitVec` 和固定位宽整数 `UInt8`–`UInt64`、`USize`、`Int8`–`Int64`、`ISize` 等类型的转换，将它们映射到 {name}`Nat` 和 {name}`Int` 算术。
因此，混合机器算术和自然数界的以下目标现在可由 {tactic}`grind` 证明：

```lean
example (x : UInt8) (h : x.toNat < 100) :
    (x + 1).toNat = x.toNat + 1 := by
  grind

example (x : BitVec 8) (h : x.toNat < 10) :
    (x * 2).toNat < 20 := by
  grind
```

此转换默认启用，可用 `grind -hom` 关闭。
它取代此前基于 `Lean.Grind.ToInt` 类型类的机制。

## 可判定命题现在基于 `Bool`
%%%
file := "Decidable-Propositions-Are-Now-Based-on--Bool"
tag := "Lean-__________________--____________--Lean-4___35___0-_LPAR_2026-10-12_RPAR_--Highlights--Decidable-Propositions-Are-Now-Based-on--Bool"
%%%

[#8309](https://github.com/leanprover/lean4/pull/8309) 修改 {name}`Decidable` 的定义：不再是带 `isTrue`、`isFalse` 构造器的归纳类型，而是保存 {name}`Bool` 及其反映该命题的证明的结构体。

```lean (name := printDecidable)
#print Decidable
```
```leanOutput printDecidable
class Decidable (p : Prop) : Type
number of parameters: 1
fields:
  Decidable.decide : Bool
  Decidable.reflects_decide : (decide p).Reflects p
constructor:
  Decidable.intro {p : Prop} (decide : Bool) (reflects_decide : decide.Reflects p) : Decidable p
```

因此，对由 {name}`Bool` 等式构成的命题调用 `decide`，现在会归约为对应的 {name}`Bool` 运算，许多等式可直接用 `rfl` 证明：

```lean
variable (a b : Bool)

example : decide (a = true) = a := rfl
example : decide (a = true ∧ b = true) = (a && b) := rfl
example : decide (a = true ∨ b = true) = (a || b) := rfl
example : decide (¬a) = !a := rfl
```

{tactic}`decide` 也不再需要携带证明，对良好编写的实例更快。
现在推荐用 `decidable_of_bool` 或 `decidable_of_iff` 编写此类实例。
{name}`Decidable.isTrue` 与 {name}`Decidable.isFalse` 仍存在，也可继续用作 `match` 模式，因此大多数现有代码保持可用。

## 其他语言改进
%%%
file := "Other-Language-Improvements"
tag := "Manual-Releases-v4_35_0-Other-Language-Improvements"
%%%

[#14899](https://github.com/leanprover/lean4/pull/14899) 将 Mathlib 的 `recall` 命令加入 Lean 本身。
它重述已有声明，适合教学和说明性文件；Lean 会检查重述与原声明一致：

```lean (name := recallBad) +error
recall Nat.add_comm (n m : Nat) : n + m = m + n
recall Nat.add_comm (n m : Nat) : n + m = n + m
```
```leanOutput recallBad
Type mismatch
  Nat.add_comm
has type
  ∀ (n m : Nat), n + m = n + m
but is expected to have type
  ∀ (n m : Nat), n + m = m + n
```

`recall?` 为给定名称建议重述：

```lean (name := recallQ)
recall? Nat.add_comm
```
```leanOutput recallQ
Try this:
  [apply] recall Nat.add_comm (n m : Nat) : n + m = m + n
```

[#14960](https://github.com/leanprover/lean4/pull/14960) 使 `#print` 以可读形式显示递归器归约规则，而非内核使用的原始函数：

```lean (name := printRec)
#print Nat.rec
```
```leanOutput printRec
recursor Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) : motive t
number of parameters: 0
number of motives: 1 (position 1)
number of minor premises: 2 (positions 2–3)
number of indices: 0
major premise position: 4
rules:
  Nat.rec zero succ Nat.zero
    ==> zero
  Nat.rec zero succ n.succ
    ==> succ n (Nat.rec zero succ n)
```

[#14834](https://github.com/leanprover/lean4/pull/14834) 使“跳转到定义”适用于同一 `structure` 或 `class` 中后续字段定义内使用的先前字段。

弃用检查也有改进：`deprecated` 警告附带可点击替换旧名的修复（[#14705](https://github.com/leanprover/lean4/pull/14705)）；`@[deprecated]` 本身会在替代项也已弃用（[#14816](https://github.com/leanprover/lean4/pull/14816)）或类型不同（[#14600](https://github.com/leanprover/lean4/pull/14600)）时警告：

```lean
def addOne (n : Nat) : Int := n + 1
```
```lean (name := deprTypeWarn)
@[deprecated addOne (since := "2026-10-01")]
def plusOne (n : Nat) : Nat := n + 1
```
```leanOutput deprTypeWarn (severity := warning)
The updated constant has a different type:
  Nat → Int
instead of
  Nat → Nat

This suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.

If the type difference is intentional, use `+typeChanged` to silence this warning.

Hint: Add `+typeChanged`:
  [apply] +typeChanged
```

对（余）归纳谓词，[#14861](https://github.com/leanprover/lean4/pull/14861) 新增 `monotonicity_by` 子句，在自动证明失败时手动提供单调性证明；[#14855](https://github.com/leanprover/lean4/pull/14855) 生成强（余）归纳原理 `strong_coinduct` 与 `strong_induct`。

## Lake

除上述 `lake check`、`lake comparator` 外，本版本 Lake 新功能主要是面向特定情形的选项：

:::table -header
 * - 首次失败时停止构建
   - `lake build --fail-fast`：首次失败后停止调度新作业，允许运行中作业完成，并将跳过的作业标为 `⊘ Canceled`（[#14797](https://github.com/leanprover/lean4/pull/14797)、[#14835](https://github.com/leanprover/lean4/pull/14835)）。
 * - 通过副本而非原地依赖本地包
   - 在带 `path` 的 `[[require]]` 条目中设置 `copy = true`，或在 `lakefile.lean` 使用 `require pkg from copy "path"`；Lake 像克隆 Git 依赖一样，将包复制到工作区包目录并使用该副本（[#15142](https://github.com/leanprover/lean4/pull/15142)）。
 * - 只预编译部分代码，而不使用 `precompileModules`
   - `precompileImports` 编译模块导入而非模块本身；`precompileLibrary` 为导入该库的模块编译整个库（[#15015](https://github.com/leanprover/lean4/pull/15015)）。
 * - 将依赖包的构建输出上传缓存
   - 先运行 `lake build -o <file> --package <name>`，再运行 `lake cache put <file> --package=<name>`（[#15141](https://github.com/leanprover/lean4/pull/15141)）。
 * - 收集检查器与自定义检查的代码质量数据
   - `lake lint --code-quality` 现在也报告检查器在精译期间记录的度量（[#14748](https://github.com/leanprover/lean4/pull/14748)、[#14933](https://github.com/leanprover/lean4/pull/14933)），并运行以 `@[package_code_quality_check]` 注册的检查，包括由 `--checks` 传入的模块中的检查（[#14716](https://github.com/leanprover/lean4/pull/14716)）。
:::

另一项变更无需用户操作：依赖现在以单个修订版本的部分 Git 克隆获取，减少下载量（[#14782](https://github.com/leanprover/lean4/pull/14782)）。
因此，在依赖内运行 `git blame` 等 Git 命令时，可能需要按需获取数据。

## 库亮点
%%%
file := "Library-Highlights"
tag := "Manual-Releases-v4_35_0-Library-Highlights"
%%%

[#13490](https://github.com/leanprover/lean4/pull/13490) 新增 {name}`Nat.powMod`，无需先计算 `b ^ e` 就能计算 `b ^ e % m`。
Lean 使用 GMP 构建时，编译代码使用 GMP 模幂运算；定义本身使用平方乘法，因此内核也能高效求值。
`Fin n` 的幂运算现已使用它，因此即使很大的模幂也可用 {tactic}`decide` 检查：

```lean
example : (2 : Fin 1000000007) ^ 1000000006 = 1 := by decide
```

其他新增内容包括 {name}`Float`、{name}`Float32` 的融合乘加（[#15024](https://github.com/leanprover/lean4/pull/15024)），更完整的 CNF 公式公开 API 与重写的 LRAT 检查器（[#14842](https://github.com/leanprover/lean4/pull/14842)），以及 `Fin`、`Int`、`Nat` 和固定位宽整数缺失的序实例（[#15092](https://github.com/leanprover/lean4/pull/15092)、[#15088](https://github.com/leanprover/lean4/pull/15088)、[#15071](https://github.com/leanprover/lean4/pull/15071)、[#15122](https://github.com/leanprover/lean4/pull/15122)）。
{name}`Array`、{name}`Vector` 的 `map`、`ofFn`、`zipWith`、`modify` 等操作现在可跨模块边界在内核中归约，因此 {tactic}`decide` 和 `rfl` 能在使用模块系统的文件中对其求值（[#14270](https://github.com/leanprover/lean4/pull/14270)、[#14989](https://github.com/leanprover/lean4/pull/14989)、[#14996](https://github.com/leanprover/lean4/pull/14996)、[#15078](https://github.com/leanprover/lean4/pull/15078)、[#15079](https://github.com/leanprover/lean4/pull/15079)）。
向量现在使用 `#v[...]` 记法显示（[#14545](https://github.com/leanprover/lean4/pull/14545)）：

```lean (name := vecRepr)
#eval #v[1, 2, 3].map (· * 10)
```
```leanOutput vecRepr
#v[10, 20, 30]
```

为查找意外复制造成的性能问题，[#15052](https://github.com/leanprover/lean4/pull/15052) 给 {name}`String`、{name}`ByteArray`、{name}`FloatArray`、{name}`Array` 添加 `markLinear`；[#15069](https://github.com/leanprover/lean4/pull/15069)、[#15049](https://github.com/leanprover/lean4/pull/15049) 为向量和哈希映射添加它。
调用 `markLinear` 后，对该值的每次写入都必须在它未被共享时发生；设置环境变量 `LEAN_ABORT_ON_NONLINEAR` 后，首次不满足要求的写入会终止程序。

## 破坏性变更
%%%
file := "Breaking-Changes"
tag := "Manual-Releases-v4_35_0-Breaking-Changes"
%%%

- [#14624](https://github.com/leanprover/lean4/pull/14624) 修复[问题 #9077](https://github.com/leanprover/lean4/issues/9077)：实例合成原本可能穿透类型同义词。
  实例搜索期间，实例隐式参数的元变量现在只会被赋予在实例透明度意义下类型符合预期的值。
  相关变更 [#14583](https://github.com/leanprover/lean4/pull/14583) 使合一在因停滞异常放弃前，尝试剩余启发式方法。
  *迁移：* `set_option backward.isDefEq.respectTransparency.instanceSearchTypes false` 恢复旧实例搜索行为，`set_option backward.isDefEq.throwOnStuckAfterApp true` 恢复旧合一行为。
  Mathlib 中受影响的声明使用第一个选项，并附有正确修复方式的建议。

- [#8309](https://github.com/leanprover/lean4/pull/8309) 修改 {name}`Decidable` 定义，如前所述。
  由于 `isTrue` 与 `isFalse` 仍可用作模式，受影响代码较少，但依赖旧归纳定义的代码可能需要调整。

- [#14937](https://github.com/leanprover/lean4/pull/14937) 修改 `rwa` 行为，如前所述。
  特别地，若重写后的 `h` 无法关闭目标，`rwa [rules] at h` 现在会失败，即使其他假设能够关闭目标。
  *迁移：*使用 `rw [rules] at h; assumption` 保持旧行为；以 `rw [rules] at h₁ h₂ <;> assumption` 代替弃用的多位置形式。

- [#14854](https://github.com/leanprover/lean4/pull/14854) 多个构造器匹配时，让 `constructor` 发出警告。
  *迁移：*确实要用首个构造器时使用 `constructor!`，否则用 `left`、`right` 等更具体的策略。

- [#14727](https://github.com/leanprover/lean4/pull/14727) 移除此前供 {tactic}`grind` 算术求解器使用的 `Lean.Grind.ToInt` 类型类层次及其实例（仅留下也将移除的空占位类），从默认 {tactic}`grind` 集中移除现在由同态处理的许多 `BitVec`、`UIntN` E-匹配引理，并移除 `Fin.ext` 的 `[grind ext]`。

- [#14953](https://github.com/leanprover/lean4/pull/14953) 移除 `Lean.reduceBool`、`Lean.reduceNat`、`Lean.ofReduceBool`、`Lean.ofReduceNat`、`Lean.trustCompiler`。
  *迁移：*使用 {tactic}`native_decide`，或在元程序中使用 `Lean.Meta.nativeEqTrue`。

- [#14874](https://github.com/leanprover/lean4/pull/14874) 弃用 `mvcgen` 与 `mvcgen?`，改用 `vcgen`。

- [#15141](https://github.com/leanprover/lean4/pull/15141) 要求 `lake cache put-staged` 显式指定修订版本。
  *迁移：*通过 `--rev` 传入，例如 `--rev=$(git rev-parse HEAD)`。

- [#15054](https://github.com/leanprover/lean4/pull/15054) 修改范围记法优先级，使 `1 + 2...3` 表示 `(1 + 2)...3`，`a...b |>.toList` 表示 `(a...b).toList`。

- [#14350](https://github.com/leanprover/lean4/pull/14350) 要求 `{f x}` 等单元素集合记法中的元素若续写到下一行，续行的缩进必须深于元素起始位置，避免与结构体实例记法混淆。

- [#15019](https://github.com/leanprover/lean4/pull/15019) 移除 `macro`、`elab` 声明主体中带来意外对齐约束的 `withPosition` 标记；[#15020](https://github.com/leanprover/lean4/pull/15020) 将 `Array Syntax` 与 `SepArray` 间的强制转换，替换为保留分隔符源码信息的 `TSepArray` 到 `SepArray` 的强制转换。

- [#14890](https://github.com/leanprover/lean4/pull/14890) 交换 `Dyadic.not_lt` 和 `Dyadic.not_le` 的名称，使其与其他数值类型的引理一致。

# 语言
%%%
file := "Language"
tag := "Manual-Releases-v4_35_0-Language"
%%%

````markdown

- [#15020](https://github.com/leanprover/lean4/pull/15020)
  移除 `Array Syntax` 到 `SepArray sep` 及反向的强制转换，改为提供保留分隔符 `SourceInfo` 的 `TSepArray ks sep` 到 `SepArray sep` 转换，修复此前转换会丢失分隔符源码信息的问题。

- [#15133](https://github.com/leanprover/lean4/pull/15133)
  将 InfoTree 与 SnapshotTree 工具从服务器领域移到精译领域。

- [#15090](https://github.com/leanprover/lean4/pull/15090)
  为 `do` 记法添加擦除状态：`erased x := e`、`erased mut x := e` 和 `erased x ← act` 声明仅供验证的变量，循环 `invariant` 子句与断言可以读取它们，而编译代码中只保留占位值。

- [#15079](https://github.com/leanprover/lean4/pull/15079)
  使 `Array.modify` 与 `Array.modifyM` 可以跨模块边界在内核中归约。

- [#15078](https://github.com/leanprover/lean4/pull/15078)
  使 `Array.zipWith` 及对应的 `Vector.zipWith` 可以跨模块边界在内核中归约。

- [#14996](https://github.com/leanprover/lean4/pull/14996)
  使 `Array.map` 及调用它的 `Vector.map` 可以跨模块边界在内核中归约。

- [#14989](https://github.com/leanprover/lean4/pull/14989)
  使 `Array.ofFn` 及调用它的 `Vector.ofFn` 可以跨模块边界在内核中归约。

- [#14988](https://github.com/leanprover/lean4/pull/14988)
  使派生的 `Vector` `DecidableEq` 实例可以跨模块边界在内核中归约。

- [#14270](https://github.com/leanprover/lean4/pull/14270)
  使 `decide` 和 `rfl` 能够跨模块边界在内核中归约非空 `Array` 的相等性。

- [#15050](https://github.com/leanprover/lean4/pull/15050)
  为 `leanchecker` 添加 `--from-export file.ndjson` 标志，指示其加载指定的 ndjson 格式导出文件，并通过内核检查。

- [#15019](https://github.com/leanprover/lean4/pull/15019)
  从 `macro`、`elab` 声明主体中移除 `withPosition` 标记。

- [#14982](https://github.com/leanprover/lean4/pull/14982)
  新增 `mimalloc.cpp` 文件，包含对象分配逻辑并引入 mimalloc 实现。

- [#14912](https://github.com/leanprover/lean4/pull/14912)
  为 `TerminationHints` 添加禁用冗余提示警告的选项，便于通过 `addPreDefinitions` 生成带终止提示的声明，避免提示最终多余时产生警告。

- [#13815](https://github.com/leanprover/lean4/pull/13815)
  修复歧义语法缺少 terminfo 或上下文（如元变量上下文），从而导致信息视图报错的问题。关闭 #8108。

- [#14960](https://github.com/leanprover/lean4/pull/14960)
  改进 `#print` 描述递归器的方式，例如 `#print Nat.rec` 现在给出以下输出：
  ```
  recursor Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ)
    (t : Nat) : motive t
  number of parameters: 0
  number of motives: 1 (position 1)
  number of minor premises: 2 (positions 2–3)
  number of indices: 0
  major premise position: 4
  rules:
    Nat.rec zero succ Nat.zero
      ==> zero
    Nat.rec zero succ n.succ
      ==> succ n (Nat.rec zero succ n)
  ```

- [#14940](https://github.com/leanprover/lean4/pull/14940)
  修改宏展开生成内容的 `deprecated_syntax` 警告行为：若语法来自宏，但具有 `.original` 源码信息，则将警告定位到该语法。

- [#14937](https://github.com/leanprover/lean4/pull/14937)
  重新设计 `rwa` 策略，提高一致性和易用性。

- [#14554](https://github.com/leanprover/lean4/pull/14554)
  通过分离 `Fin.foldl` 的类型论实现与运行时实现修复 #14540。

- [#14925](https://github.com/leanprover/lean4/pull/14925)
  使命题的 `casesOn`、`recOn` 直接将次要前提应用于主要前提的投影，而不经过递归器。递归器仅在主要前提为构造器应用时归约，但证明可能永远不成为这种形式；因此 `And.casesOn` 等不再要求证明本身能归约。

- [#14855](https://github.com/leanprover/lean4/pull/14855)
  为格论中的（余）归纳谓词添加强（余）归纳证明原理。`coinductive_fixpoint` 生成的 `strong_coinduct` 加强 `coinduct`：假设中候选谓词的各次出现都与余归纳谓词自身作析取，使余归纳证明在重新进入该谓词时即可结束。对偶地，`inductive_fixpoint` 得到 `strong_induct`，其归纳假设额外提供属于该谓词的事实；相互定义（含混合定义）得到 `strong_mutual_induct`，按各分量选择联结词。生成原理的结论现在也会 β-归约，例如使用 `star_ind tr q₁ q₂ → pred q₁`，而非 `(fun q₁ => star_ind tr q₁ q₂) q₁ → pred q₁`。

- [#14909](https://github.com/leanprover/lean4/pull/14909)
  修复 `inductive T : Sort u | a | b` 等 sort 多态归纳类型的精译，此前会报 `` Unknown constant `T.ctorIdx` ``。同时修复 `set_option genCtorIdx false` 时的同类问题。

- [#14350](https://github.com/leanprover/lean4/pull/14350)
  强制单元素集合记法中的元素对嵌套应用实参等续行进行缩进，否则与结构体记法的重叠会令读者及即将提供的格式化器困惑，后者甚至必须等待精译才能判断。

- [#14861](https://github.com/leanprover/lean4/pull/14861)
  为 `coinductive`、`inductive` 谓词声明添加 `monotonicity_by` 子句，当自动 `monotonicity` 搜索失败时，可用显式策略块证明底层不动点函子的单调性。该子句像 `decreasing_by` 一样直接进入策略模式，可以附在相互定义组的单个成员上，包括混合 `inductive`/`coinductive` 定义：

  ```lean
  mutual
    coinductive tick : Prop where
      | mk : ¬tock → tick
    monotonicity_by repeat monotonicity

    inductive tock : Prop where
      | mk : ¬tick → tock
  end
  ```

- [#14899](https://github.com/leanprover/lean4/pull/14899)
  内置添加 `recall`、`recall?` 命令，用于经检查的说明性重述，无需导入任何模块。

- [#14834](https://github.com/leanprover/lean4/pull/14834)
  为 `structure`/`class` 字段添加 terminfo，使字段的依赖使用中的“跳转到定义”指向其定义，也帮助查找结构体定义中的字段使用。同时修复模块系统中公开结构体的私有字段未应用 terminfo 和文档字符串的问题。

- [#14844](https://github.com/leanprover/lean4/pull/14844)
  确保 `DiscrTree` 操作会折叠变为空的 trie 节点。

- [#14860](https://github.com/leanprover/lean4/pull/14860)
  使 `do` 块中的 `invariant`、`decreasing`、`assert` 无需 `open Std.WP` 即可精译，与契约的 `requires`、`ensures` 子句一致。

- [#14858](https://github.com/leanprover/lean4/pull/14858)
  移除 `ensures` 子句的匹配分支形式。除此以外，契约所有子句（`requires`、`ensures`、`assert`、`invariant`、`decreasign`）都按 `fun` 的参数列方式精译，包括 `ensures (lo, hi) => lo ≤ hi` 这样的元组模式。

- [#14854](https://github.com/leanprover/lean4/pull/14854)
  多个构造器匹配时让 `constructor` 发出警告，并添加保留旧行为、静默应用首个匹配构造器的 `constructor!`。

- [#14845](https://github.com/leanprover/lean4/pull/14845)
  为 `while`、`repeat` 循环不变式提供独立类型 `def Std.WP.WhileInvariant α Pred := Bool → α → Pred`，它是关于循环 `exit` 标志和状态的谓词。此前复用实际较难使用的 `Std.WP.RepeatInvariant α α Pred = α ⊕ α → Pred`。

- [#14590](https://github.com/leanprover/lean4/pull/14590)
  按程序变量命名验证条件中的变量，并使这些名称可访问。例如：

- [#14825](https://github.com/leanprover/lean4/pull/14825)
  为 `def` 契约添加写在 `requires` 前的 `given` 子句，绑定契约的逻辑变量，并使其在 `requires`、`ensures` 中可见。

- [#14748](https://github.com/leanprover/lean4/pull/14748)
  添加从检查器收集代码质量度量的基础设施。精译期间记录的条目保存在模块 `.olean` 文件中，构建工具随后无需重新精译即可收集各模块条目。

- [#14816](https://github.com/leanprover/lean4/pull/14816)
  当 `@[deprecated]` 指定的替代声明本身已弃用时发出警告；若替代项另有替代项，建议直接弃用为最终声明。可用 `set_option linter.deprecated.deprecatedTarget false` 禁用此检查。

- [#14826](https://github.com/leanprover/lean4/pull/14826)
  在各使用位置将内在验证语法报告为实验性：`def` 的 `requires`、`ensures`，`assert` 元素，以及循环的 `invariant`、`decreasing` 均在关键字处报告。设置 `experimental.intrinsic` 为 `true` 即表示接受实验状态并关闭报告。

- [#14821](https://github.com/leanprover/lean4/pull/14821)
  根据包装函数的签名推断 `do←` 实参中 `fun` 绑定的类型，使 `bs.extract` 等字段记法可在转发主体中解析。也接受带类型标注的绑定，并为模式绑定提供专门错误信息。

- [#14624](https://github.com/leanprover/lean4/pull/14624)
  修复 #9077：实例搜索中，所有实例隐式参数的元变量，只能在实例透明度意义下赋为预期类型的值。向后兼容选项 `set_option backward.isDefEq.respectTransparency.instanceSearchTypes false` 恢复旧行为。此破坏性变更影响 Mathlib 少量声明，均已用兼容选项修复，并经过分析和详细标注，给出建议操作。注意：此修复*不*在实例透明度下强制输出参数类型；若 `X` 为输出参数位置，合成 `Class X` 仍可得到 `Class Y`，只要在更高透明度下 `X =?= Y`。后者性质不同；虽然容易强制要求，但会破坏 Mathlib 约数千个声明，收益却不明确。

- [#14705](https://github.com/leanprover/lean4/pull/14705)
  为 `deprecated` 检查器添加可点击提示，从而也提供代码操作。

- [#14771](https://github.com/leanprover/lean4/pull/14771)
  修复在 `ofKernelEnv` 结果上使用 `Environment.find?` 及其变体的问题。

- [#14583](https://github.com/leanprover/lean4/pull/14583)
  修改定义相等性与合一启发式：`isDefEqApp` 的回退分支抛出停滞异常前，先尝试剩余几个启发式，仅全部失败后才抛出异常。这同时提高合一和实例搜索的性能与健壮性，为 #14624 做准备。兼容标志 `set_option backward.isDefEq.throwOnStuckAfterApp true` 恢复旧行为。

- [#14703](https://github.com/leanprover/lean4/pull/14703)
  允许 `repeat`、`while` 循环陈述 `vcgen` 所需的不变式与终止度量，使带契约 `def` 内的循环无需手动证明即可验证：

  ```lean
  def countDown (n : Nat) : Id Nat
      ensures r => r = 0 := do
    let mut i := n
    while i > 0
        invariant exit => if exit then i = 0 else True
        decreasing i
      do
      i := i - 1
    return i
  ```

- [#14600](https://github.com/leanprover/lean4/pull/14600)
  当弃用声明的替代项与它不在可约透明度下定义相等时，添加警告。

````

# 库
%%%
file := "Library"
tag := "Manual-Releases-v4_35_0-Library"
%%%

````markdown

- [#15430](https://github.com/leanprover/lean4/pull/15430)
  再次将 `And`、`Or` 的 `Decidable` 实例标为 `macro_inline`，使其在所有情形下正确短路。

- [#13490](https://github.com/leanprover/lean4/pull/13490)
  新增模幂函数 `Nat.powMod b e m`，证明等于 `b ^ e % m`，使非零模数下的大幂可无需构造完整幂值就能求值。同时使 `Fin n` 的幂使用此操作。

- [#15024](https://github.com/leanprover/lean4/pull/15024)
  公开 `Float`、`Float32` 的融合乘加及其逻辑模型。

- [#15144](https://github.com/leanprover/lean4/pull/15144)
  允许 LRAT 检查器的 RUP 部分接受本身冗余的提示子句。

- [#14796](https://github.com/leanprover/lean4/pull/14796)
  修复 libuv 模块中的引用计数、mark_mt 和错误消息。

- [#15122](https://github.com/leanprover/lean4/pull/15122)
  补齐 `UIntX` 与 `IntX` 的序实例。

- [#15114](https://github.com/leanprover/lean4/pull/15114)
  公开 `Fin.addNat?`，使其能跨模块边界归约。`Fin n` 上的范围通过 `UpwardEnumerable (Fin n)` 实例由它构造，因此此前在使用模块系统的文件中，`cbv` 与内核归约会卡在 `Fin.addNat?` 应用处。

- [#15092](https://github.com/leanprover/lean4/pull/15092)
  为 `Fin` 添加 `Min`、`Max`、`LawfulOrderOrd` 等一系列缺失的序实例。

- [#15088](https://github.com/leanprover/lean4/pull/15088)
  提供 `LinearOrderPackage Int`，继而提供缺失实例 `LawfulOrderBEq Int`。

- [#15080](https://github.com/leanprover/lean4/pull/15080)
  弃用 `Lean.MVarId.liftReflToEq` 和辅助定理 `Lean.Meta.Rfl.rel_of_eq_and_refl`；二者均未接入核心策略，下游用户应自行保留副本。

- [#15049](https://github.com/leanprover/lean4/pull/15049)
  为哈希映射引入类似 `Array.markLinear` 的 `markLinear` 函数。

- [#15071](https://github.com/leanprover/lean4/pull/15071)
  补齐实例 `LawfulOrderBEq Nat`。

- [#15069](https://github.com/leanprover/lean4/pull/15069)
  引入类似 `Array.markLinear` 的 `Vector.markLinear`。

- [#15062](https://github.com/leanprover/lean4/pull/15062)
  为 `ULift`、`PULift`、`PLift`、`MProd` 注册 `ext`、`ext_iff` 定理，使 `ext` 策略可用于这些结构体的等式。

- [#15043](https://github.com/leanprover/lean4/pull/15043)
  修复 `Std.Http.Server` 中空闲连接在配置的保活超时后仍占用连接槽导致的停滞。

- [#15059](https://github.com/leanprover/lean4/pull/15059)
  为一些 `ForIn`、`ForIn'` 实例添加 `default_instance` 标注。

- [#15054](https://github.com/leanprover/lean4/pull/15054)
  调整范围语法优先级，使 `1 + 2...3` 为 `(1+2)...3`，`a...b |>.toList` 为 `(a...b).toList`。

- [#15018](https://github.com/leanprover/lean4/pull/15018)
  为 `bif`（`cond`）表达式补齐 `Decidable` 实例，类似于现有 `if`（`ite`）实例。

- [#14794](https://github.com/leanprover/lean4/pull/14794)
  为一致的关联容器 API 添加 `isEmpty_inter_comm`，从关联列表开始，将结果提升到哈希映射、树映射及集合，使无需展开成员关系就能证明容器不相交的对称性。

- [#14995](https://github.com/leanprover/lean4/pull/14995)
  添加两个揭示 `List.mergeSort` 递归、但不引用 `MergeSort.Internal.splitInTwo` 的引理：

  - `mergeSort_append`：对任意平衡拆分（`l₂.length ≤ l₁.length ≤ l₂.length + 1`）的两半排序再归并，得到 `(l₁ ++ l₂).mergeSort`。这是主要陈述：无索引算术，适用于所有长度；中点 take/drop 或 cons-cons 形式等具体展开，都是两行可证的推论。
  - `@[simp] mergeSort_pair`：`[a, b].mergeSort le = if le a b then [a, b] else [b, a]`，补全 `mergeSort_nil`/`mergeSort_singleton` 序列。不同于 `mergeSort_append`，它确实能简化，因此标注 `@[simp]`。

- [#14890](https://github.com/leanprover/lean4/pull/14890)
  交换 `Dyadic.not_lt` 与 `Dyadic.not_le` 的名称，分别表述 `¬x < y ↔ y ≤ x` 和 `¬x ≤ y ↔ y < x`，与 `Nat`、`Int`、`Rat` 及 mathlib 中 `_root_.not_lt`、`_root_.not_le` 的对应引理一致。

- [#8204](https://github.com/leanprover/lean4/pull/8204)
  添加 `Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero`，表明 T-除法结果为零，当且仅当分子绝对值小于分母绝对值，或分母为零：

  ```lean
  @[simp] theorem tdiv_eq_zero_iff_natAbs_lt_or_eq_zero {a : Int} {b : Int} :
      a.tdiv b = 0 ↔ (a.natAbs < b.natAbs ∨ b = 0):= by
  ```

- [#14545](https://github.com/leanprover/lean4/pull/14545)
  使用 `#v[...]` 字面量记法显示 `Vector` 值，不再暴露底层结构体表示，使求值后的向量更简洁易读。它替换派生的 `Repr` 实例。

- [#14953](https://github.com/leanprover/lean4/pull/14953)
  移除 `Lean.reduceBool`、`Lean.reduceNat`、`Lean.ofReduceBool`、`Lean.ofReduceNat`、`Lean.trustCompiler`，以及内核通过运行编译器归约前两个函数应用的支持。它们自 2026-02-01 起已弃用，改为通过公理断言本地求值；`native_decide` 与 `bv_decide` 已通过 `Lean.Meta.nativeEqTrue` 采用此方式。工具链已无任何部分使用它们。

- [#14842](https://github.com/leanprover/lean4/pull/14842)
  重构 LRAT 检查器，同时大幅扩展公开 CNF API，具体包括：
  - 形式化蕴涵、否定、单位子句等基本 CNF 性质；
  - 形式化 RUP 和 RAT 性质；
  - 将子句数据结构改为更节省内存的实现，以更高效地存储巨大 CNF；
  - 基于新 API 从头重写 LRAT 检查器，新版本稍快，并支持有界变量添加。

- [#14916](https://github.com/leanprover/lean4/pull/14916)
  引入 `BitVec.ofNatClamp`，推广已有的 `UIntX.ofNatClamped` 系列函数。

- [#14915](https://github.com/leanprover/lean4/pull/14915)
  为 `Sym.simp`、`Meta.simp` 的闭项求值器添加 `Nat.log2` 支持。虽然函数递归，但它仅执行对数数量的内核加速操作，因此归约仍能高效求值。

- [#14905](https://github.com/leanprover/lean4/pull/14905)
  通过改为编码为依赖合取加 `getElem`，降低 `BitVec` 中会“意外”从 `getElem` 转为 `getLsbD` 的 E-匹配标注的激进程度。

- [#14903](https://github.com/leanprover/lean4/pull/14903)
  仅在已出现 `Nodup xs` 及对 `xs` 的索引访问时才触发 `List.Nodup.getElem_inj`。

- [#14895](https://github.com/leanprover/lean4/pull/14895)
  为 `Sum` 添加 `ReflBEq`、`LawfulBEq` 实例，并公开派生的 `BEq`，使和类型上的 `==` 能在定义模块之外归约。

- [#14872](https://github.com/leanprover/lean4/pull/14872)
  移除霍尔三元组记法 `⦃ P ⦄ c ⦃ v, Q ⦄`；其展开 `⦃ P ⦄ c ⦃ fun v => Q ⦄` 更易理解。

- [#14836](https://github.com/leanprover/lean4/pull/14836)
  用积类型取代异常后置条件类型 `EPost.Nil`、`EPost.Cons`。异常后置条件栈现在为 `(ε₁ → Pred) × (ε₂ → Pred) × EStack⟨⟩`，可使用 `Prod` API。基础单子使用直接的后置条件：`Except ε` 使用 `ε → Prop`，`Option` 使用 `Unit → Prop`。`EStack⟨A, B⟩` 表示栈类型，`estack⟨e₁, e₂⟩` 表示栈值，打印时均保持该记法。`vcgen` 使用与其他格联结词相同的缓存反向规则拆分 `⊥`、`⊤` 异常后置条件。

- [#8309](https://github.com/leanprover/lean4/pull/8309)
  将 `Decidable p` 改为包含一个 `Bool` 及 `p` 或 `¬p` 证明的结构体。

- [#14824](https://github.com/leanprover/lean4/pull/14824)
  为缺少 `apply` 等式的 `PredTrans` 运算添加这些等式，使 `simp` 像归约 `pure`、`bind` 等运算一样归约 `get`、`set`、`modifyGet`、`read`、`throw`、`tryCatch`。

- [#14813](https://github.com/leanprover/lean4/pull/14813)
  向 `Std.WP` 添加 `Triple.and`、`Triple.mp` 和 `Triple.observe`，每个都将同一程序的两个霍尔三元组规约合为一个。

- [#14801](https://github.com/leanprover/lean4/pull/14801)
  将可靠性类 `WPSound` 从 `Std.Do` 移到 `Std.WP`，更名为 `LawfulWPMonadAttach`。

- [#12330](https://github.com/leanprover/lean4/pull/12330)
  从两个数组相关陈述中移除与 True 的等价。这使它们更难使用，因为不能直接用来重写；此外，由于 `iff_true`，它们也不处于 simp 范式。

- [#14751](https://github.com/leanprover/lean4/pull/14751)
  按标注组合为 `repeat`、`while` 循环分别提供 `forInLoopWithInvariant`、`forInLoopWithVariant` 或 `forInLoopWithInvariantAndVariant` 辅助构造，取代同时以 `Option` 槽携带两种标注的单一构造。

- [#14744](https://github.com/leanprover/lean4/pull/14744)
  使 `grind` 可在带状态单子中解决陈述了终止度量的 `repeat`、`while` 循环验证条件；此前证明需先用 `simp_all` 对度量求值。`RepeatVariant.EvalsTo`、`RepeatVariant.EvalsBelow` 增加元数 1 至 5 的固定元数闭项实例，供 `grind` 索引。

- [#14711](https://github.com/leanprover/lean4/pull/14711)
  修正 `Std.ExtDHashMap` 的 `contains_empty`、`not_mem_empty`、`singleton_eq_insert` 三个误写成关于 `Std.DHashMap` 的引理。

````

# 策略
%%%
file := "Tactics"
tag := "Manual-Releases-v4_35_0-Tactics"
%%%

```markdown

- [#15391](https://github.com/leanprover/lean4/pull/15391)
  显著加速进程中的首次库建议查询。自 #15159 起，符号频率映射和 Sine Qua Non 触发索引在首次使用时计算，使文件中的首个 `grind +suggestions`、`simp? +suggestions` 或 `try?` 在 `import Lean` 下耗时 12 秒，`import Mathlib` 下则达数分钟。现在两份索引由同一次遍历导入定理陈述产生；遍历使用并行任务，每种应用头和元数仅分类一次实参。对 Lean 核心与 Mathlib 的每个定理，结果均与旧遍历一致。并发首次查询共享同次计算，取消查询时立即停止。

- [#15161](https://github.com/leanprover/lean4/pull/15161)
  共享 `grind` 修饰符的解析器，降低 Lean 核心构建的模块导入开销。

- [#15159](https://github.com/leanprover/lean4/pull/15159)
  避免在构建期间准备和序列化前提选择索引；保留选择器，在每个进程首次使用时计算并缓存索引。

- [#15124](https://github.com/leanprover/lean4/pull/15124)
  修复 LRAT 裁剪的非线性问题：原证明与裁剪后证明同时存活，而未复用内存。

- [#15116](https://github.com/leanprover/lean4/pull/15116)
  允许 `lia`、`grobner` 接受与 `grind` 相同的 `[...]` 参数列表，可内联提供额外事实和引理（如 `lia [foo n]`、`grobner [= sq_def]`），而不必先用 `have` 加入局部上下文。

- [#14688](https://github.com/leanprover/lean4/pull/14688)
  若程序头既不受任何策略步骤处理，也没有规约以它为索引，例如展开匿名状态变换器的 `liftM` 后留下的 `fun s => …`，让 `vcgen` 报告 `No spec found for program …`；此前会报 `Failed to decompose weakest precondition … This should not happen`。

- [#14956](https://github.com/leanprover/lean4/pull/14956)
  为 `BitVec` 引入 `min`/`max` 定义，并为 `bv_decide` 添加对 `BitVec` 和 `UIntX`/`IntX` 系列 `min`/`max` 的支持。

- [#14928](https://github.com/leanprover/lean4/pull/14928)
  支持符号化 `Nat` 移位及 `extractLsb'`：将 `x >>> n` 重新解释为 `x >>> BitVec.ofNatClamped (log2 w + 1) n`，将 `extractLsb'` 解释为移位加 `setWidth`。`bv_decide` 仍不推理 `n` 本身，但至少知道 `x >>> n` 的输出位为 `0` 或 `x` 的某个输入位；通过将 `BitVec.ofNatClamped` 视为未解释位向量原子实现。

- [#14921](https://github.com/leanprover/lean4/pull/14921)
  修复一个 simproc 将项重写为实参数量更少的项后，`simp`、`dsimp` 触发 `PANIC at Lean.Expr.appArg!` / `Lean.Expr.appFn!: application expected` 的问题。该 panic 以 `info` 级记录，因此即使输出了它，构建此前仍会成功退出。

- [#14922](https://github.com/leanprover/lean4/pull/14922)
  不再让 `Lean.Elab.WF.paramProj`、`paramMatcher`、`paramLet` 参与每次 `simp`、`dsimp` 调用；它们只实现良基递归定义预处理的一步，在其他地方没有用途。

- [#14883](https://github.com/leanprover/lean4/pull/14883)
  让 `vcgen` 规范化 `WP` 实例，使单子可以在从 `WPMonad.toWP` 合成的低优先级实例之外，注册菱形 `WP` 实例。

- [#14874](https://github.com/leanprover/lean4/pull/14874)
  通过 `deprecated_syntax` 弃用 `mvcgen`、`mvcgen?`，改用 `vcgen`，使每次使用都报告受 `linter.deprecated.syntax` 控制的弃用警告。

- [#14870](https://github.com/leanprover/lean4/pull/14870)
  添加 `experimental.vcgen` 选项，并让 `vcgen invariants?` 警告不变式建议尚未从 `mvcgen` 移植，且该功能计划移除。

- [#14857](https://github.com/leanprover/lean4/pull/14857)
  使 `vcgen` 在局部上下文不一致的目标上成功；此前会报 `No goals to be solved`。

- [#14856](https://github.com/leanprover/lean4/pull/14856)
  将 `vcgen frames` 子句查找从 `applySpec` 移到 `applySpecs`，使匹配子句按每个目标而非每个规约候选项消费。若候选项查找后因实例实参无法合成等原因应用失败，不再使子句失效，后续候选项仍可使用同一框架。

- [#14848](https://github.com/leanprover/lean4/pull/14848)
  修复 `sym =>` 初始化，正确处理预处理期间目标已关闭的情况。

- [#14828](https://github.com/leanprover/lean4/pull/14828)
  移除 `vcgen` 每次替换目标时在证明项中生成的 `@id` 提示，以加快所得证明的内核检查。

- [#14829](https://github.com/leanprover/lean4/pull/14829)
  修复 `grind` 的字面量规范化。

- [#14823](https://github.com/leanprover/lean4/pull/14823)
  对 `vcgen` 输出的每个验证条件进行头部归约，使两个可变变量循环的入口条件写成 `0 ≤ 0`，而非 `match (0, 0) with | (lo, hi) => lo ≤ hi`；可归约为 `rfl` 的条件当场关闭，不再交给用户。

- [#14819](https://github.com/leanprover/lean4/pull/14819)
  使 `@[spec]` 定理的合取前置条件分类能够穿透 `binderNameHint`。

- [#14820](https://github.com/leanprover/lean4/pull/14820)
  为 `Sym.simp` 添加在参数中提供函数符号时展开定义的支持。`sym => simp [f]` 现在像 `Meta.simp` 一样使用 `f` 的方程定理，而不再失败。

- [#14814](https://github.com/leanprover/lean4/pull/14814)
  修复将非命题声明用作 `Sym.simp` 定理时（如 `sym => simp [HAdd.hAdd]`）的内部错误 `unexpected bound variable #3`，现在给出适当错误消息。

- [#14802](https://github.com/leanprover/lean4/pull/14802)
  为交互式 `sym =>` 添加 `let_to_have` 策略，将目标中的非依赖 `let` 声明变为 `have`，得到定义相等的目标。这启用了 `Sym.simp` 的高效 `have` 参数列机制 `simpLet`，后者不处理依赖 `let`。

- [#14799](https://github.com/leanprover/lean4/pull/14799)
  消除两个导致含大项目标在 `grind`/`sym` 中情形拆分缓慢的开销来源。在对 6400 个 `BitVec` 运算链执行一次 `cases_next` 的新基准中，耗时从 5.9 秒降至 0.11 秒。

- [#14787](https://github.com/leanprover/lean4/pull/14787)
  使 `mvcgen`、`vcgen` 对以 `cond`（`bif c then t else e`）为头的程序按分支拆分验证条件，并在上下文中加入 `c = true` 或 `c = false`，与 `if`、`match` 一致。

- [#14118](https://github.com/leanprover/lean4/pull/14118)
  为 `grind` 的 E-匹配图引入新的开销度量，可通过 `set_option grind.ematch.diagnostics true` 在诊断中启用。现在能够检测：
  - 具有大量直接后继子实例的单个实例，通过 `grind.ematch.diagnostics.branchThreshold` 配置；
  - 参与大型后继实例传递闭包的实例。为此计算的开销度量近似于传递闭包大小，但在多个父项间公平分配，通过 `grind.ematch.diagnostics.costThreshold` 配置。度量基于 https://github.com/viperproject/smt-scope 的开销启发式。

- [#14785](https://github.com/leanprover/lean4/pull/14785)
  将等待 SAT 求解器的固定 50 毫秒延迟改为从 1 毫秒递增至 64 毫秒的指数退避，以降低批量求解小 SAT 问题的延迟。

- [#14770](https://github.com/leanprover/lean4/pull/14770)
  修复 `grind` 生成的证明项可能触发内核确定性超时的性能问题。`grind` 在恒等包装 `Grind.nestedDecidable` 下规范化嵌套 `Decidable` 实例，让内核检查 `t =?= Grind.nestedDecidable t`。内核看不到 `[reducible]` 属性，其惰性 δ 启发式会展开 `t` 而非包装器。若 `t` 是将 `UInt32.decLe` 等实例应用于符号实参和大字面量（例如来自 `Char`/`UInt32` 回绕的 `97 ≤ c.val + 4294967264`），检查会经过 `BitVec`、`Fin`，进入含自由变量的 `2^32` 量级字面量上的 `Nat.ble`；数值快速路径不适用，实际不会终止。将 `nestedDecidable` 标为缩写后，`abbrev` 可约性提示存入声明本身并被内核遵守，因此先展开包装器，立即检查成功。

- [#14769](https://github.com/leanprover/lean4/pull/14769)
  修复 `grind` 内部错误：`mkEqProof` 以不同类型的项调用。通过 `HEq` 合并时，一个等价类可能包含不同类型的项，例如通过 `cast` 关联的不同位宽 `BitVec` 项。`[grind hom]` 钩子的 `=` 单射转换仅适用于同类型相等，因此 `processNewEq`、`processNewDiseq` 现在跳过类型不同的项对。

- [#14768](https://github.com/leanprover/lean4/pull/14768)
  为 `sym =>` 添加 `lift_lets` 策略，在依赖允许的范围内将目标中的 `let`/`have` 声明尽量提升到根部，展平嵌套声明并合并定义在语法上相同的声明。新目标与原目标定义相等。不会提升 `fun`/`∀` 绑定下的声明，也不修改假设。

- [#14766](https://github.com/leanprover/lean4/pull/14766)
  使 `vcgen` 保留以 ``epost⟨E⟩``、且 `E` 为模式变量形式陈述的 `@[spec]` 定理的异常后置条件；此前应用时会将其弱化为 `⊥`，留下验证条件 `⊥`。

- [#14727](https://github.com/leanprover/lean4/pull/14727)
  为 `grind` 实现同态简化集。带新属性 `[grind hom]` 的定理将源类型的项转换到有专用求解器的目标类型（如将 `Fin`、`BitVec`、固定位宽整数转换到 `Nat`/`Int` 算术）；`[grind hom_pred]` 定理提供单射函数的值域事实（如 `Fin.isLt`）。内部化期间在 E-图外反复转换到不动点，仅内部化最终范式。默认启用，可用 `grind -hom` 禁用。

- [#14763](https://github.com/leanprover/lean4/pull/14763)
  引入新的 `grind`/`sym` 模式策略 `bv_decide_push`，可在证明任意位置对至今已内部化到 `grind` 状态的全部内容运行预处理，并将结果保存到目标状态，加快后续 `bv_decide` 或 `bv_decide_push` 调用。在许多子目标共享同样假设且预处理占比高的基准中，可提速两倍或更多。注意它**尚未**实现增量 SAT 求解。

- [#14765](https://github.com/leanprover/lean4/pull/14765)
  使文件中标注 `@[spec]` 的定理可以相互并行精译；此前每次这样的标注都会等待证明完成，阻塞精译。

- [#14757](https://github.com/leanprover/lean4/pull/14757)
  修改 `bv_decide` 在 grind 模式中收集事实的两点行为：
  1. 相应功能关闭时，不再考虑枚举、结构体或 UIntX 等价类。
  2. 不再自行立即内部化目标状态，因为这可能代价较高；因此不会使用 grind 内部化目标才能推出的事实，但目标本身仍用于 bv_decide 的反证证明。

- [#14747](https://github.com/leanprover/lean4/pull/14747)
  使 `vcgen` 能继续处理程序在绑定下应用续延变量的规约，例如 `Lang.bnd (fun x => Lang.add (k x) (Lang.nat 0))` 中的 `k`。一阶匹配保留 `k`，合一在处理待解约束时为其赋值；这发生在生成目标的类型构造后，因此目标中的程序是表示 `k` 的元变量应用于实参。此前 `vcgen` 会报 `Failed to decompose weakest precondition … This should not happen` 并放弃，现在在正确位置实例化。

- [#14745](https://github.com/leanprover/lean4/pull/14745)
  存在 `simplifying_assumptions` 时，`vcgen` 推进程序的同时立即简化 `wp` 目标的状态参数，使验证条件更清晰且避免重复简化。在 `tests/bench/vcgen/vcgen_get_throw_set_grind` 的 n=300 情况下，内核检查从 862 毫秒降至 291 毫秒，验证条件生成也略有加速。

- [#13968](https://github.com/leanprover/lean4/pull/13968)
  为 `bv_decide` 从 AIG 到 CNF 的转换添加 if-then-else/XOR/XNOR 门检测及优化。它识别 AIG 中形如 `(c → t) ∧ (¬c → f)` 的 `c ? t : f` 门，允许输入置换或取反；该模式也覆盖表示为 `a ? ¬b : b` / `a ? b : ¬b` 的 XOR/XNOR。匹配这些模式时，门改用 4 个子句编码，而非作为 AND 门转换时的 12 个。

```

# 编译器
%%%
file := "Compiler"
tag := "Manual-Releases-v4_35_0-Compiler"
%%%

```markdown

- [#15429](https://github.com/leanprover/lean4/pull/15429)
  支持 `macro_inline` 与 `csimp` 相互递归。例如，`macro_inline` 定义可包含经 `csimp` 替换的定义，其替代体再含 `macro_inline`，依此类推。编译器*不*检查此过程终止；用户未保证终止时，最终会报 maxRecDepth 错误。

- [#15288](https://github.com/leanprover/lean4/pull/15288)
  修复大量入引用的对象在线程间共享时可能出现的未定义行为。官方内核的默认配置（comparator 及 `lake check/compare` 所用配置）不使用多线程，但 con-leche 等基于 Lean 的检查器可能受影响。

- [#15289](https://github.com/leanprover/lean4/pull/15289)
  当共享子项的引用数超过 `INT_MAX` 时，让最大共享机制（包括内核对所检查每个定理的共享）触发 panic，而非最终在仍有引用时释放子项。在超过 100GB 的输入上，无法排除以此触发官方内核未定义行为、并进一步构造 False 证明的可能。不基于 Lean 运行时或不使用此特定函数的 nanoda、con-leche 等内核不受影响。

- [#15241](https://github.com/leanprover/lean4/pull/15241)
  防止删除级联释放因引用计数上溢或下溢而被冻结的对象。与 #14838 一样，在至少有 18GB 可用内存的机器上，此问题可能触发官方内核的释放后使用，并进一步构造 False 的证明。不依赖 Lean 运行时的 nanoda、con-ron 等内核不受影响。

- [#15107](https://github.com/leanprover/lean4/pull/15107)
  允许 `ReduceArity` 阶段移除函数的全部参数；若发生此情况，加入 `void` 参数，避免将值提升为常量。

- [#15089](https://github.com/leanprover/lean4/pull/15089)
  当 `cases` 操作 `EST.Out` 或 `ST.Out` 时，让 `floatLetIn` 保守决定是否将表达式浮入其中。这些情形暗示可能有副作用，通过 `ST.Ref` 导致静态分析难以预测的非线性。因此不再浮入这些 `cases`，以确保线性。

- [#15075](https://github.com/leanprover/lean4/pull/15075)
  修复对象最大尺寸计算中的差一错误。

- [#15052](https://github.com/leanprover/lean4/pull/15052)
  引入动态跟踪原语检测非线性问题。对 `String`、`ByteArray`、`FloatArray`、`Array` 调用 `markLinear` 有两个效果：若值不唯一，则强制复制使其唯一；此后所有写访问必须线性发生。若访问不线性且设置了 `LEAN_ABORT_ON_NONLINEAR`，程序终止。用户可在 `lean_internal_panic` 设置断点，定位终止位置并找出线性问题。后续 PR 将为其他内置线性数据结构添加 `markLinear`。

- [#14969](https://github.com/leanprover/lean4/pull/14969)
  修复对元数至多 16 的闭包一次应用超过 16 个实参时的崩溃。

- [#14948](https://github.com/leanprover/lean4/pull/14948)
  使用 `MI_MAX_ALIGN_SIZE=8` 构建 mimalloc，使 `List.cons` 等对象占用 24 而非 32 字节，改善内存与缓存效率。

- [#14531](https://github.com/leanprover/lean4/pull/14531)
  将 LLVM 升级到 23.1.0，略微改善各类 Lean 二进制性能，并缩短 C 编译时间。

- [#14888](https://github.com/leanprover/lean4/pull/14888)
  修复属性与 `extern "C"` 顺序影响某些 gcc 版本构建的问题。

- [#14811](https://github.com/leanprover/lean4/pull/14811)
  先创建临时文件，再原子移动到实际目标，以原子方式写入 Lean 的 C 输出文件。`clang` 通过 `mmap` 读取 C 文件，并发写同一文件可能出问题；尤其应解决此前观察到的偶发 clang 词法分析器段错误。

- [#12814](https://github.com/leanprover/lean4/pull/12814)
  修改 `ToLCNF` 对证明过度应用的 cases 表达式的处理，避免生成立即被调用的函数声明。这是较温和的 #12284 版本（后者已回退），仅影响证明过度应用而非所有过度应用；这也正是 #8309 等情形（如 `match h : _`）所需的唯一情况。

- [#14775](https://github.com/leanprover/lean4/pull/14775)
  修复 `ST.Ref` 剩余问题，通过两点变更确保它真正表现为自旋锁：
  1. `ST.Ref.set` 现在仅为 `discard <| ST.Ref.swap`，不再专门用于关闭 `ST.Ref.take` 打开的临界区。
  2. 新增 `unsafe` 函数 `ST.Ref.put`，仅可在用 `unsafe` 的 `ST.Ref.take` 打开临界区后调用；再用这些操作实现 `modify` 等函数。

- [#14773](https://github.com/leanprover/lean4/pull/14773)
  将解释器的实参传递路径恢复到 #14749 之前，后者使部分基准回退。标量参数上的借用标注不提供信息，`Lean.IR.ToIR.lowerParam` 现在去除它。因此解释器可假设借用参数均为引用，将 #14749 为每个实参加的测试改为 `lean_assert`。

- [#14749](https://github.com/leanprover/lean4/pull/14749)
  修复解释代码调用带 `@&` 标量参数的已编译函数时的内存泄漏。

- [#14585](https://github.com/leanprover/lean4/pull/14585)
  以防止与空指针交换的 CAS 取代有缺陷的原子交换，修复 `Ref.swap` 与 `Ref.get` 竞争时的引用计数损坏。

```

# 美化打印
%%%
file := "Pretty-Printing"
tag := "Manual-Releases-v4_35_0-Pretty-Printing"
%%%

```markdown

- [#14971](https://github.com/leanprover/lean4/pull/14971)
  为 `@[delab]` 属性的 `app` 表达式种类前缀添加补全。

```

# Lake

```markdown

- [#15142](https://github.com/leanprover/lean4/pull/15142)
  为路径依赖添加 `copy` 配置：TOML 使用 `[[require]] copy = true`，Lean 使用 `require <name> from copy <path>`。启用后，Lake 将相对路径中的包原样复制到工作区包目录（类似 Git 克隆），从副本加载而非直接从相对来源加载。

- [#15153](https://github.com/leanprover/lean4/pull/15153)
  在发行工具链中捆绑外部检查器 `con-ron`，无需单独安装即可作为独立检查器。

- [#14835](https://github.com/leanprover/lean4/pull/14835)
  将 `--fail-fast` 下的作业取消视为正式状态：取消作业报告为 `⊘ Canceled` 而非成功，取消的依赖也不再误报为 `bad import`。

- [#15157](https://github.com/leanprover/lean4/pull/15157)
  为 `lake check` 添加 `--from-export`，为 `lake comparator` 添加 `--solution-from-export`、`--challenge-from-export`，允许从现有 NDJSON 文件加载导出，而非即时构建。适用情况包括：
    - 使用虚拟机中构建的导出，提供额外隔离。
    - 使用第三方构建的导出，例如生成过程
      需要大量计算资源时。
    - 使用通过标准 `lake build` 之外方式
      生成的导出。

- [#15156](https://github.com/leanprover/lean4/pull/15156)
  为 comparator 添加供专家用户关闭沙箱的标志，不应在常规生产环境使用，仅适合确信形式化代码不会恶意攻击系统的情况。

- [#15145](https://github.com/leanprover/lean4/pull/15145)
  为 `lake check`、`lake comparator` 添加 `--paranoid`，除 Lean 自身内核外，对导出运行发行工具链内全部检查器（`leanchecker-paranoid`、`lean4lean`、`nanoda`、`con-leche`），仅在全部接受时接受。

- [#15141](https://github.com/leanprover/lean4/pull/15141)
  为 `lake build` 和 `lake cache put` 添加 `--package`。在 `lake build` 上，`-o` 配合 `--package` 跟踪指定包而非根包的输出，再通过 `lake cache put --package` 上传。同时为减少误上传，`lake cache put-staged` 现在要求手动设置 `--rev`。

- [#15147](https://github.com/leanprover/lean4/pull/15147)
  将 `comparator.json` 作为 `lake comparator` 默认配置文件位置。

- [#15146](https://github.com/leanprover/lean4/pull/15146)
  将 lake challenge 更名为 lake comparator。

- [#15096](https://github.com/leanprover/lean4/pull/15096)
  确保 comparator 永不完整物化 `lean4export` 输出，而是先写入文件，再仅用流式解析器读取。

- [#15005](https://github.com/leanprover/lean4/pull/15005)
  在限制更严格的 `bubblewrap` 而非 `landrun` 沙箱中构建和导出 `lake challenge` 评判的代码，禁止访问调用用户文件，并让禁止联网的步骤完全没有网络。

- [#14990](https://github.com/leanprover/lean4/pull/14990)
  新增无需挑战的 `lake challenge` 变体 `lake check`，构建当前项目默认目标、导出并通过内核重放结果，对任何非标准公理使用报错。

- [#15015](https://github.com/leanprover/lean4/pull/15015)
  新增两个属于 `precompileModules` 部分功能的配置选项：`lean_lib` 的 `precompileLibrary`，以及全部 Lean 配置（可在 `package`、`lean_lib`、`lean_exe` 设置）的 `precompileImports`。后者编译模块导入而非模块本身；前者为导入方编译整个库，但库模块精译时不编译自己的导入。

- [#15042](https://github.com/leanprover/lean4/pull/15042)
  修复 `moreServerOptions` 仅应用于包外模块（如编辑临时文件）而未应用于包内模块的 Lake 问题。

- [#14885](https://github.com/leanprover/lean4/pull/14885)
  将 `lake challenge` 作为 `comparator` 前端分发，大幅简化设置。`landrun` 仍是硬性要求，且无关闭沙箱模式，因此目前仅适用于 Linux。

- [#14933](https://github.com/leanprover/lean4/pull/14933)
  使 `lake lint --code-quality` 输出检查器精译期间记录的代码质量条目。通过 `Lean.Linter.logCodeQualityEntryIf` 记录的条目归属于对应检查器选项名，受 `--lint-only` 筛选；`Lean.Linter.logCodeQualityEntry` 条目不归属特定检查器，总会输出，检查器选择标志无法抑制。禁用记录检查器（如 `--linters=-linter.foo`）会在精译时抑制归属条目；多个检查目标共享的模块只贡献一次条目。

- [#14902](https://github.com/leanprover/lean4/pull/14902)
  修复某导入同时是 `import all` 又通过 `meta import` 传递到达时，Lake 从模块 setup 漏掉导入的问题。`import all` 抑制后续 `meta import`，使仅经后者可达的模块未包含在传给 lean 的 setup 中。

- [#14797](https://github.com/leanprover/lean4/pull/14797)
  为 `lake build` 添加 `--fail-fast`：首个必需目标失败时停止调度新作业，让运行中作业完成后报告失败并退出。此前总将所有已调度作业运行到底，即使早期出错也要承担整个工作区的开销。

- [#14853](https://github.com/leanprover/lean4/pull/14853)
  将覆盖的 Lean include 目录中的 `lean.h` 及传递包含头文件纳入目标文件构建追踪，确保头文件变化时重建，例如自举时。为避免未来影响公开 API，`leanIncludeDir?` 从公开 `buildLeanO` API 移除，移入内部 `buildLeanO`。

- [#14716](https://github.com/leanprover/lean4/pull/14716)
  使 `lake lint --code-quality` 运行通过 `@[package_code_quality_check]` 注册的包级检查。在每个检查目标的导入闭包发现检查，每个目标运行一次，并与检查器条目一起输出 JSON。可通过新命令行选项 `--checks`（隐含 `--code-quality`）或包配置选项 `checks` 提供额外模块；构建后与被检查模块一起导入，因此无需添加到包自身导入中。

- [#14782](https://github.com/leanprover/lean4/pull/14782)
  重做 Lake 克隆依赖的方式：现在获取单个修订版本的无树部分 Git 克隆，尽量减少下载；切换分支时，若新修订及其树和 blob 已存在，就避免 fetch。依赖 URL 改变时复用仓库目录，避免文件系统反复变动及 fetch 失败时丢失依赖。为进一步减少磁盘使用，获取新版本后清理远程引用并运行 Git 垃圾回收。

```

# 其他
%%%
file := "Other"
tag := "Manual-Releases-v4_35_0-Other"
%%%

```markdown

- [#15542](https://github.com/leanprover/lean4/pull/15542)
  使 `leanchecker --from-export` 和 `lake check` 使用的 `LeanExport` NDJSON 读取器拒绝此前静默接受的非法输入：行中 JSON 对象后的多余字节、重复键对象，以及重复绑定名称、层级、表达式或递归器规则索引的行，包括匿名名称与零层级的预定义索引 0。

- [#15130](https://github.com/leanprover/lean4/pull/15130)
  在发行工具链中捆绑 `con-leche`，无需单独安装即可作为独立检查器。

- [#15099](https://github.com/leanprover/lean4/pull/15099)
  在发行工具链中捆绑 `nanoda`，无需单独安装即可作为独立检查器。

- [#15048](https://github.com/leanprover/lean4/pull/15048)
  在发行工具链中捆绑 `lean4lean`，无需单独安装即可作为独立检查器。

- [#15055](https://github.com/leanprover/lean4/pull/15055)
  在 `lake check` 与 `lake challenge` 中将默认内核运行于权限隔离的进程。这并不修复特定安全问题，只是额外加固。

- [#14884](https://github.com/leanprover/lean4/pull/14884)
  添加 `bin/leanchecker-paranoid`，即采用加固分配器构建的 `leanchecker` 变体。

```
