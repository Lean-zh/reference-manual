/-
版权 (c) 2025 Lean FRO LLC。保留所有权利。
根据 LICENSE 文件所述，按 Apache 2.0 许可证发布。
作者：Anne Baanen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown
import Std.Data.Iterators
import Std.Data.TreeMap

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Std.Iterators
open Std (TreeMap)
open Std (Iterator Iter IterM IteratorLoop)
open Std (HashMap)
open Std (Iter IterM IteratorLoop)

#doc (Manual) "Lean 4.27.0 (2026-01-24)" =>
%%%
tag := "release-v4.27.0"
file := "v4.27.0"
%%%

本次发布共合入 372 项变更。除下方列出的 118 项功能新增和 71 项修复外，还有 28 项重构、13 项文档改进、25 项性能改进、6 项测试套件改进，以及 111 项其他变更。

# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights"
%%%

## 模块系统已稳定
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Module-System-Stabilized"
%%%

[#11637](https://github.com/leanprover/lean4/pull/11637) 宣布模块系统不再属于实验性功能，并将 {option}`experimental.module` 选项变为空操作。

相关文档见参考手册中的 {ref "module-scopes"}[模块与可见性] 一节。

## 向后兼容选项
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Backward-Compatibility-Options"
%%%

[#11304](https://github.com/leanprover/lean4/pull/11304) 说明 `backward.*` 选项只是临时的迁移辅助工具；自引入起 6 个月后，它们可能在不另行通知的情况下消失。若用户依赖这些选项，恳请反馈。

## 性能提升
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Performance-Gains"
%%%

本次发布包含许多性能改进，其中尤其值得一提的是：

- [#11162](https://github.com/leanprover/lean4/pull/11162) 降低了语言服务器的内存占用（尤其是监视进程）。在 Mathlib 中，内存占用大约减少了 1 GB。

- [#11507](https://github.com/leanprover/lean4/pull/11507) 优化了导入过程中的文件系统访问，在 Linux 上带来约 3% 的收益，在其他平台上可能更多。

## 错误消息
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Error-Messages"
%%%

本次发布对错误消息做了一系列修改，目标是让它们更有帮助、更便于采取行动。
具体来说，一些消息现在会附带提示、建议以及解释链接。

相关拉取请求：
[#11119](https://github.com/leanprover/lean4/pull/11119)、
[#11245](https://github.com/leanprover/lean4/pull/11245)、
[#11346](https://github.com/leanprover/lean4/pull/11346)、
[#11347](https://github.com/leanprover/lean4/pull/11347)、
[#11456](https://github.com/leanprover/lean4/pull/11456)、
[#11482](https://github.com/leanprover/lean4/pull/11482)、
[#11518](https://github.com/leanprover/lean4/pull/11518)、
[#11554](https://github.com/leanprover/lean4/pull/11554)、
[#11555](https://github.com/leanprover/lean4/pull/11555)、
[#11621](https://github.com/leanprover/lean4/pull/11621)。

## `grind` 的新特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind"
%%%

### 函数值同余闭包
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind--Function-Valued-Congruence-Closure"
%%%

[#11323](https://github.com/leanprover/lean4/pull/11323) 为 {tactic}`grind` 引入了一个新选项 `funCC`（默认启用），将同余闭包扩展到_函数值_相等式。启用 `funCC` 后，`grind` 会跟踪*部分应用函数*之间的相等式，因此可以进行如下推理：

```
a : Nat → Nat
f : (Nat → Nat) → (Nat → Nat)
h : f a = a
⊢ (f a) m = a m

g : Nat → Nat
f : Nat → Nat → Nat
h : f a = g
⊢ f a b = g b
```

这一特性显著增强了 `grind` 对高阶相等式和部分应用函数相等式的支持；而在禁用 `funCC` 时，仍保持与一阶 SMT 求解器行为的兼容性。

更多用法细节请参见该拉取请求的说明。

### 控制定理实例化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind--Controlling-Theorem-Instantiation"
%%%

[#11428](https://github.com/leanprover/lean4/pull/11428) 在 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 中加入了对 *guard* 的支持。这个新特性让用户能更细致地控制定理实例化。举例来说，考虑下面这个单调性定理：

```lean
opaque f : Nat → Nat
theorem fMono : x ≤ y → f x ≤ f y := sorry
```

借助新的 `guard` 特性，我们可以指示 {tactic}`grind` 仅在当前 `grind` 状态中已知 `x ≤ y` 为真时，才对该定理进行实例化：

```lean
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y
```

这能显著减少定理实例化的次数。

更详细的讨论和证明轨迹示例，请参见该拉取请求的说明。

### 提供任意参数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind--Supplying-Arbitrary-Parameters"
%%%

[#11268](https://github.com/leanprover/lean4/pull/11268) 实现了对任意 {tactic}`grind` 参数的支持。该特性与 {tactic}`simp` 中已有的机制类似：证明项会被视为局部的宇宙多态引理。此特性依赖于 `grind -revert`（见 [#11248](https://github.com/leanprover/lean4/pull/11248)）。例如，用户现在可以写出：

```lean
def snd (p : α × β) : β := p.2
theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

/--
trace: [grind.ematch.instance] snd_eq (a + 1): snd (a + 1, Type) = Type
[grind.ematch.instance] snd_eq (a + 1): snd (a + 1, true) = true
-/
#guard_msgs (trace) in
set_option trace.grind.ematch.instance true in
example (a : Nat) :
    (snd (a + 1, true), snd (a + 1, Type), snd (2, 2)) =
    (true, Type, snd (2, 2)) := by
  grind [snd_eq (a + 1)]
```

请注意，上面的例子里，`snd_eq` 只被实例化了两次，但使用了不同的宇宙参数。

### grind 的 revert 选项
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind--Grind-Revert"
%%%

[#11248](https://github.com/leanprover/lean4/pull/11248) 实现了 `revert` 选项，其默认值为 `false`。

这是一项与回退假设相关的内部变更。
采用新的默认值后，{tactic}`grind` 产生的跟踪信息、反例和证明项都会不同。
若要恢复旧的 `grind` 行为，请使用 `grind +revert`。

### `grind` 的其他新特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--New-Features-in-Grind--Other-New-Features-in-Grind"
%%%

- 在 `grind ring` 中加入 `BitVec` 支持（[#11639](https://github.com/leanprover/lean4/pull/11639)），并在 `grind lia` 中加入 `BitVec` 支持（[#11640](https://github.com/leanprover/lean4/pull/11640)）；

- 新增配置选项 `grind -reducible`，允许在定义相等性测试期间展开不可约声明（[#11480](https://github.com/leanprover/lean4/pull/11480)）；

- 支持异构构造子单射性（[#11491](https://github.com/leanprover/lean4/pull/11491)）；

- 支持 `LawfulOfScientific` 类（[#11331](https://github.com/leanprover/lean4/pull/11331)）；

- 在 `grind` 策略块中支持语法 `use [ns Foo]` 和 `instantiate only [ns Foo]`，其效果是激活该命名空间作用域下的全部 grind pattern（[#11335](https://github.com/leanprover/lean4/pull/11335)）；

- 新增 `grind_pattern` 约束（[#11405](https://github.com/leanprover/lean4/pull/11405) 和 [#11409](https://github.com/leanprover/lean4/pull/11409)）。

## `Nat` 上的良基递归
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Well-Founded-Recursion-on--Nat"
%%%

使用良基递归的定义通常都是不可约的。
借助 [#7965](https://github.com/leanprover/lean4/pull/7965)，当终止度量的类型为 {name}`Nat` 时，这类定义可以被归约，并且显式的 `@[semireducible]` 标注会被接受，而不会触发通常的警告。

## 库亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Library-Highlights"
%%%

本次发布完成了对 {name}`String` 接口的修订，包括依赖类型化的 {name}`String.Pos`、对 {name}`String.Slice` 的完整接口支持，以及采用新 `Iterator` 接口的迭代器。
此外，{name}`TreeMap`/{name}`HashMap` 接口也新增了许多内容，包括交集、差集与相等性。

这些更新还包含一些*破坏性变更*，即：

- [#11180](https://github.com/leanprover/lean4/pull/11180) 将 {name}`String.take` 及其变体重新定义为基于 {name}`String.Slice` 工作。此前，返回输入子串的函数有时返回 {name}`String`，有时返回 {name}`Substring.Raw`；现在它们统一返回 {name}`String.Slice`。

  这是一个破坏性变更，因为许多函数的返回类型现在不同了。例如，如果 `s` 是字符串而 `f` 是接受字符串的函数，那么 `f (s.drop 1)` 将不再编译，因为 `s.drop 1` 是一个 `String.Slice`。要修复这一点，请插入一次 `copy` 调用以恢复旧行为：`f (s.drop 1).copy`。

  当然，在很多情况下还有更高效的写法。例如，不要写 `f <| s.drop 1 |>.copy |>.dropEnd 1 |>.copy`，而应写 `f <| s.drop 1 |>.dropEnd 1 |>.copy`。同样，也不要写 `(s.drop 1).copy = "Hello"`，而应写 `s.drop 1 == "Hello".toSlice`。

## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Highlights--Breaking-Changes"
%%%

- [#11474](https://github.com/leanprover/lean4/pull/11474) 和 [11562](https://github.com/leanprover/lean4/pull/11562) 将 `noConfusion` 构造推广到异构相等式（假设参数和索引之间有命题相等性）。
  这对那些手动、显式地在带索引类型上使用 `noConfusion` 原理的用户来说是一个破坏性变更。
  请按需传入合适的 `rfl` 参数，并对得到的相等式使用 `eq_of_heq`。

- [#11490](https://github.com/leanprover/lean4/pull/11490) 防止 `try` 吞掉嵌套 `simp` 调用产生的心跳错误，更一般地说，它还确保 `isRuntime` 标志会被 `throwNestedTacticEx` 传播。
  这避免了证明的行为（尤其是使用 `aesop` 的证明）受当前递归深度或心跳上限影响。
  这会破坏 Mathlib 中一个调用点：那里 `simp` 使用了形如 `x = f (g x)` 的引理，并因此栈溢出；可以通过对 `g x` 做泛化来修复。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Language"
%%%

````markdown

* [#7965](https://github.com/leanprover/lean4/pull/7965) 允许通过良基递归定义的递归函数在终止度量类型为 `Nat` 时使用不同的 `fix` 函数。
  这个不动点算子会对由给定度量初始化的“燃料”做结构递归，因此可以合理地被归约，例如在 `by decide` 证明中。

* [#11196](https://github.com/leanprover/lean4/pull/11196) 在计算匹配器时跟踪可能的重叠、将信息存入 `MatcherInfo`，并在后续匹配器计算中复用这些信息，从而避免匹配分支器为了检测重叠而对所有备选分支进行二次复杂度的两两测试。

* [#11200](https://github.com/leanprover/lean4/pull/11200) 更改了稀疏 case 表达式表示“以上都不是”信息的方式。
  它不再引入许多 `x.ctorIdx ≠ i` 假设，而是引入单个 `Nat.hasNotBit mask x.ctorIdx` 假设，把这些信息压缩进一个位掩码中。
  这避免了分支器生成时的二次开销；原先对于分支器备选中的全部 n 个假设，都要通过 `.subst` 和 `.cases` 构造对这 n 个假设逐一精化。

* [#11221](https://github.com/leanprover/lean4/pull/11221) 让 `realizeConst` 使用 `withDeclNameForAuxNaming`，从而使其中创建的辅助定义获得不冲突的名字。

* [#11222](https://github.com/leanprover/lean4/pull/11222) 实现了 `elabToSyntax`，用于为任意精译器 `el : Option Expr -> TermElabM Expr` 创建带作用域的语法 `s : Syntax`，满足 `elabTerm s = el`。

* [#11236](https://github.com/leanprover/lean4/pull/11236) 从 `Match.MatchEqs` 中抽取出两个模块，为 #11220 做准备，并借助模块系统更清晰地划分这里的关注点边界。

* [#11239](https://github.com/leanprover/lean4/pull/11239) 为原本没有参数的分支器备选新增一个 `Unit` 假设。此改动修复了 #11211。

* [#11245](https://github.com/leanprover/lean4/pull/11245) 改进了类型类实例解析失败时的错误消息，并新增错误解释，讨论新手常见的二元运算重载场景，并指向 `trace.Meta.synthInstance` 选项以进行高级调试。

* [#11256](https://github.com/leanprover/lean4/pull/11256) 用更细致的数据结构替代 `MatcherInfo.numAltParams`。
  这样我们尤其能区分两种备选：一种来自带 `Unit` 字段的构造子，另一种来自无参构造子（此时会人为引入一个 `Unit` 参数）。

* [#11261](https://github.com/leanprover/lean4/pull/11261) 延续 #11256，继续统一匹配器与分支器。
  其中尤其移除了 `numParams` 是否包含 `discrEqns` 的歧义。

* [#11269](https://github.com/leanprover/lean4/pull/11269) 为空列表和空数组的可判定相等性提供支持。
  同时适当调整列表和数组的可判定相等性实现，使所有菱形在定义上相等。

* [#11292](https://github.com/leanprover/lean4/pull/11292) 为 `ExtDTreeMap`/`ExtTreeMap`/`ExtTreeSet` 添加交集操作，并证明若干相关引理。

* [#11301](https://github.com/leanprover/lean4/pull/11301) 允许在异步上下文中设置 reducibilityCoreExt（例如在可实现定义中使用 `mkSparseCasesOn` 时）。

* [#11302](https://github.com/leanprover/lean4/pull/11302) 将 CTests 的测试名改为使用文件名。
  因此，不再是
  ```
          2080 - leanruntest_issue5767.lean (Failed)
  ```
  而会变成
  ```
          2080 - tests/lean/run/issue5767.lean (Failed)
  ```
  这样就可以在 VSCode 终端里按住 Ctrl 单击这些路径。

* [#11303](https://github.com/leanprover/lean4/pull/11303) 将命名错误的 `backwards.` 选项重命名为 `backward.`。

* [#11304](https://github.com/leanprover/lean4/pull/11304) 记录了 `backward.*` 选项只是临时迁移辅助工具；自引入起 6 个月后，它们可能在不另行通知的情况下消失。
  若用户依赖这些选项，恳请反馈。

* [#11305](https://github.com/leanprover/lean4/pull/11305) 从选项描述中移除 `group` 字段。
  该字段未被使用、含义也不清晰，而且往往只是与选项名的第一部分重复。

* [#11307](https://github.com/leanprover/lean4/pull/11307) 移除了所有给 `Option.Decl.group` 字段赋值的代码；该字段既未使用，也没有清晰记录的含义。

* [#11325](https://github.com/leanprover/lean4/pull/11325) 新增 `CoreM.toIO'`，它是 `CoreM.toIO` 的对应版本，会从返回类型中去掉状态；`TermElabM.toIO'` 与 `MetaM.toIO'` 也同理。

* [#11333](https://github.com/leanprover/lean4/pull/11333) 为 Lean 的策略单子增加并行执行基础设施。

* [#11338](https://github.com/leanprover/lean4/pull/11338) 将来自 Mathlib 的 `with_weak_namespace` 命令上游化：
  `with_weak_namespace <id> <cmd>` 会在执行命令 `<cmd>` 期间把当前命名空间切换为 `<id>`，但不会让 scoped 事物超出作用域。
  这为把 Mathlib 的 `scoped[Foo.Bar]` 语法上游化做准备；既然我们正在给作用域添加 `grind` 标注，这会很有用。

* [#11346](https://github.com/leanprover/lean4/pull/11346) 修改了类型综合失败时的错误消息，适用于相关类型类可能通过 `deriving` 命令自动派生的场景。
  同时也修改了类型类实例综合失败的错误解释，并加入这一模式的示例说明。

* [#11347](https://github.com/leanprover/lean4/pull/11347) 针对有人试图在 Lean 中直接使用 Natural-Numbers-Game 风格 `induction` 证明、而这类证明在语法上并不合法的场景，新增了更聚焦的错误解释。

* [#11353](https://github.com/leanprover/lean4/pull/11353) 对特化键应用 β 归约，使我们能在更多场景下复用特化结果。

* [#11379](https://github.com/leanprover/lean4/pull/11379) 为单构造子的归纳类型上（平凡的）`.ctorIdx` 添加 `@[macro_inline]`，以减少编译器生成的符号数量。

* [#11385](https://github.com/leanprover/lean4/pull/11385) 让隐式实例名避免与 private 声明发生命名冲突。此改动修复了 #10329。

* [#11408](https://github.com/leanprover/lean4/pull/11408) 为 `ExtDTreeMap`/`ExtTreeMap`/`TreeSet` 添加差集操作，并证明若干相关引理。

* [#11422](https://github.com/leanprover/lean4/pull/11422) 在 `grind` 中使用 `Mon.mul` 的一种针对内核归约优化过的变体。

* [#11425](https://github.com/leanprover/lean4/pull/11425) 将 `Lean.Order.CCPO` 和 `.CompleteLattice` 调整为携带一个 Prop。
  这避免了 `CCPO IO` 实例成为 `noncomputable`。

* [#11432](https://github.com/leanprover/lean4/pull/11432) 修复了 `#guard_mgs` 的文档字符串中的一个拼写错误。

* [#11453](https://github.com/leanprover/lean4/pull/11453) 修复了一个未定义行为：对使用 `new[]` 分配的对象调用了 `delete`（而不是 `delete[]`）。

* [#11456](https://github.com/leanprover/lean4/pull/11456) 细化了若干错误消息，主要涉及字段记法、广义字段记法和数值投影的无效用法。
  同时还为字段记法提供了新的错误解释。

* [#11463](https://github.com/leanprover/lean4/pull/11463) 修复了 `getEqnsFor?` 在作用于从定理类型中的 `match` 表达式生成的匹配器时发生的崩溃。

* [#11474](https://github.com/leanprover/lean4/pull/11474) 将 `noConfusion` 构造推广到异构相等式（假设索引之间存在命题相等性）。
  这为 `grind` 更好地支持把 injection 应用于异构相等式打下基础。

* [#11476](https://github.com/leanprover/lean4/pull/11476) 新增 `` {givenInstance}`C` `` 文档 role，它会把 `C` 的一个实例加入文档的局部假设中。

* [#11482](https://github.com/leanprover/lean4/pull/11482) 在从未知类型进行投影时，根据当前可用常量给出建议。

* [#11485](https://github.com/leanprover/lean4/pull/11485) 确保在未设置 `LEAN_USE_GMP` 的情况下，`.olean` 文件中的 `Nat` 会使用确定性的序列化方式。

* [#11490](https://github.com/leanprover/lean4/pull/11490) 防止 `try` 吞掉嵌套 `simp` 调用产生的心跳错误，更一般地说，也确保 `isRuntime` 标志会被 `throwNestedTacticEx` 传播。
  这避免了证明的行为（尤其是使用 `aesop` 的证明）受当前递归深度或心跳限制影响。

* [#11492](https://github.com/leanprover/lean4/pull/11492) 在更多地方使用辅助函数 withImplicitBinderInfos 和 mkArrowN。

* [#11493](https://github.com/leanprover/lean4/pull/11493) 让 `Match.MatchEqs` 成为叶子模块，从而减少我们在其中能使用哪些特性的限制。

* [#11502](https://github.com/leanprover/lean4/pull/11502) 新增两个用于精译大量 `Nat` 字面量 match 语句的基准测试：一个不生成分支器，另一个生成分支器。

* [#11508](https://github.com/leanprover/lean4/pull/11508) 在对值做匹配时，若无需生成假设（例如存在兜底分支，因此不需要完备性检查），就避免生成这些假设。

  这一调整得益于 #11220。

* [#11510](https://github.com/leanprover/lean4/pull/11510) 避免在 caseValues 中运行两次 substCore。

* [#11511](https://github.com/leanprover/lean4/pull/11511) 实现了一个检查器，会在应用已弃用强制转换时发出警告。
  当 `Option` 强制转换或 `Subarray` 到 `Array` 的强制转换在 `Init` 或 `Std` 中使用时，它也会发出警告。
  当前这个检查器仅限于 `Coe` 实例；`CoeFun` 等实例不在考虑范围内。

* [#11518](https://github.com/leanprover/lean4/pull/11518) 在自动绑定的隐式参数被要求具有函数类型或相等式类型时，额外给出一条提示。
  此时综合会失败，而现有错误消息没有指出：错误源头其实是一个被自动绑定的未知标识符。

* [#11541](https://github.com/leanprover/lean4/pull/11541) 为 `String.toNat?`、`String.toInt?` 及相关解析函数添加了以下划线作为数字分隔符的支持。
  这让字符串解析函数与 Lean 的数字字面量语法保持一致；后者早已支持用下划线提升可读性（例如 `100_000_000`）。

* [#11554](https://github.com/leanprover/lean4/pull/11554) 为 Lean 添加 `@[suggest_for]` 标注，使其能为多数默认导入类型（数组、列表、字符串、子串、子数组以及向量）把 `.all` 或 `.any` 方法纠正为 `.every` 或 `.some` 方法。

* [#11555](https://github.com/leanprover/lean4/pull/11555) 扫描环境，为点式标识符（如 `.zero`）寻找可行替代项，并给出具体建议。

* [#11562](https://github.com/leanprover/lean4/pull/11562) 让 `noConfusion` 原理变得更加异构，不仅允许索引不同，也允许参数不同。

* [#11566](https://github.com/leanprover/lean4/pull/11566) 让编译器像处理通用 `noConfusion` 一样处理每个构造子的 `noConfusion`，并把更多逻辑移到 no confusion 生成附近。

* [#11571](https://github.com/leanprover/lean4/pull/11571) 让 `whnf` 不再查询 `isNoConfusion`，以稍微加快这条热点路径。

* [#11587](https://github.com/leanprover/lean4/pull/11587) 调整实验性模块系统中新引入的 `meta` 关键字，使其不再隐含 `partial`，以保持整体一致性。

* [#11607](https://github.com/leanprover/lean4/pull/11607) 让无参数调用的 `Std.Do` 策略（如 `mintro`）给出正确的错误消息：“`mintro` expects at least one pattern”，而不是声称需要导入 `Std.Tactic.Do`。

* [#11611](https://github.com/leanprover/lean4/pull/11611) 修复了由 #11562 引入的一个 `noConfusion` 编译问题。

* [#11619](https://github.com/leanprover/lean4/pull/11619) 允许 Lean 在遇到不含内部点号的未知标识符时，也能基于 `@[suggest_for]` 标注给出建议。
  （#11554 中的标注此前只能为点式标识符提供建议，例如 `Array.every` -> `Array.all`，而不能为裸标识符提供建议，例如 `Result` -> `Except` 或 `ℕ` -> `Nat`。）

* [#11620](https://github.com/leanprover/lean4/pull/11620) 将 Batteries.WF 迁移到 Init.WFC，用于可执行的良基不动点。
  它引入 `csimp` 定理，用可执行定义替代递归器和不可执行定义。

* [#11621](https://github.com/leanprover/lean4/pull/11621) 让 Lean 在某些看起来像是未知标识符被错误自动绑定的错误场景下，也会搜索 `@[suggest_for]` 标注。
  这样就能正确识别：类型为 `Maybe String` 的声明其实应写成 `Option String`。

* [#11624](https://github.com/leanprover/lean4/pull/11624) 修复了在 `x86_64` 上求值有符号整数类型的 `INT_MIN / -1` 或 `INT_MIN % -1` 时发生的 SIGFPE 崩溃。

* [#11637](https://github.com/leanprover/lean4/pull/11637) 宣布模块系统不再是实验性功能，并把 `experimental.module` 选项变成待删除的空操作。

* [#11644](https://github.com/leanprover/lean4/pull/11644) 让 `.ctorIdx` 不再是 abbrev；我们不希望 `grind` 展开它。

* [#11645](https://github.com/leanprover/lean4/pull/11645) 修复了 `propagateForallPropUp` 的文档字符串；此前只是复制粘贴产物。

* [#11652](https://github.com/leanprover/lean4/pull/11652) 教会 `grind` 归约施加到构造子上的 `.ctorIdx`。
  它还可以处理如下任务
  ```
  xs ≍ Vec.cons x xs' → xs.ctorIdx = 1
  ```
  这得益于按需生成的 `.ctorIdx.hinj` 定理。

* [#11657](https://github.com/leanprover/lean4/pull/11657) 在 #11652 的基础上进一步改进，同时保留了针对内核归约优化过的定义。

````

# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Library"
%%%

```markdown

* [#8406](https://github.com/leanprover/lean4/pull/8406) 添加了形如 `getElem_swapIfInBounds*` 的引理，并弃用 `getElem_swap'`。

* [#9302](https://github.com/leanprover/lean4/pull/9302) 修改了 `Option.instDecidableEq` 和 `Option.decidableEqNone`，使后者可以被设为全局实例而不会产生菱形依赖。
  同时还新增了 `Option.decidableNoneEq`。

* [#10204](https://github.com/leanprover/lean4/pull/10204) 修改了 `ForIn`、`ForIn'` 和 `ForM` 类型类的接口，不再接收 `Monad m` 参数。
  这对大多数下游 `instance` 来说是破坏性变更；它们现在需要假定 `[Monad m]`。

* [#10945](https://github.com/leanprover/lean4/pull/10945) 添加了 `Std.Tricho r`，这是一个把关系标记为三歧的类型类。
  在所有场合，它都优于 `Std.Antisymm (¬ r · ·)`（两者等价）。

* [#11038](https://github.com/leanprover/lean4/pull/11038) 引入了新的不动点组合子 `WellFounded.extrinsicFix`。
  终止性证明若需要给出，也可以以外延方式给出，也就是从项的外部观察它；只有在想形式化验证该不动点行为时才需要。
  新组合子随后被应用到迭代器接口上。
  `toList` 或 `ForIn` 之类的消费者不再需要证明底层迭代器是有限的。
  若想以内在方式确保终止性，也提供了严格终止的变体，例如用 `it.ensureTermination.toList` 代替 `it.toList`。

* [#11112](https://github.com/leanprover/lean4/pull/11112) 为 `DHashMap`/`HashMap`/`HashSet` 添加交集操作，并提供若干关于其行为的引理。

* [#11141](https://github.com/leanprover/lean4/pull/11141) 为切片提供多态的 `ForIn` 实例，并为使用 `for ... in` 遍历切片提供一个 MPL `spec` 引理。
  同时还提供了专门针对 `Subarray` 的版本。

* [#11165](https://github.com/leanprover/lean4/pull/11165) 为 `DTreeMap`/`TreeMap`/`TreeSet` 提供交集操作，并给出若干相关引理。

* [#11178](https://github.com/leanprover/lean4/pull/11178) 为 `Subarray` 和 `ListSlice` 增补更多引理，并为这两种切片类型的子切片提供支持。

* [#11180](https://github.com/leanprover/lean4/pull/11180) 将 `String.take` 及其变体重新定义为基于 `String.Slice` 工作。
  以前返回输入子串的函数有时返回 `String`，有时返回 `Substring.Raw`；现在统一返回 `String.Slice`。

* [#11212](https://github.com/leanprover/lean4/pull/11212) 为 `DHashMap`/`HashMap`/`HashSet` 添加差集操作支持，并证明若干相关引理。

* [#11218](https://github.com/leanprover/lean4/pull/11218) 将 `String.offsetOfPos` 重命名为 `String.Pos.Raw.offsetOfPos`，以与其他 `String.Pos.Raw` 操作保持一致。

* [#11222](https://github.com/leanprover/lean4/pull/11222) 实现了 `elabToSyntax`，用于为任意精译器 `el : Option Expr -> TermElabM Expr` 创建带作用域的语法 `s : Syntax`，满足 `elabTerm s = el`。

* [#11223](https://github.com/leanprover/lean4/pull/11223) 为 `DHashMap`/`HashMap`/`HashSet` 补充了 `emptyWithCapacity`/`empty` 与 `toList`/`keys`/`values` 之间缺失的引理。

* [#11231](https://github.com/leanprover/lean4/pull/11231) 添加了若干引理，把 `getMin`/`getMin?`/`getMin!`/`getMinD` 与向空的 (D)TreeMap/TreeSet 及其外延变体插入元素关联起来。

* [#11232](https://github.com/leanprover/lean4/pull/11232) 弃用 `String.toSubstring`，推荐改用 `String.toRawSubstring`（参见 #11154）。

* [#11235](https://github.com/leanprover/lean4/pull/11235) 为 `Lean.Parser.Term.elabToSyntax` 注册了一种节点种类，以支持 `Lean.Elab.Term.elabToSyntax` 的功能，而无需为用户可访问语法单独注册解析器。

* [#11237](https://github.com/leanprover/lean4/pull/11237) 修复了 `UInt64.fromJson?` 和 `USize.fromJson?` 抛出的错误，使其使用缺失的 `s!`。

* [#11240](https://github.com/leanprover/lean4/pull/11240) 将 `String.ValidPos` 重命名为 `String.Pos`，将 `String.endValidPos` 重命名为 `String.endPos`，并将 `String.startValidPos` 重命名为 `String.startPos`。

* [#11241](https://github.com/leanprover/lean4/pull/11241) 为 `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` 提供交集操作，并证明若干相关引理。

* [#11242](https://github.com/leanprover/lean4/pull/11242) 大幅修改了 `ToIterator` 类型类的签名。
  得到的迭代器状态不再是依赖类型，也不再打包在类内部，而改为一个 `outParam`。
  诸多好处之一是，`simp` 现在可以在 `Slice.toList` 和 `Slice.toArray` 内部重写。
  代价是我们失去了一些灵活性；例如，之前基于组合子的 `Subarray` 迭代器实现不再可行，因为它的状态是依赖类型的。
  因此，这个拉取请求为 `Subarray` 提供了手写迭代器，不需要依赖类型状态，而且比之前更快。

* [#11243](https://github.com/leanprover/lean4/pull/11243) 为 `DHashMap`/`HashMap`/`HashSet` 添加 `ofArray`，并证明一个可将 `ofArray` 重写为 `ofList` 的 simp 引理。

* [#11250](https://github.com/leanprover/lean4/pull/11250) 引入了函数 `String.split`，它基于 `String.Slice.split`，因此支持所有模式类型，并返回 `Std.Iter String.Slice`。

* [#11255](https://github.com/leanprover/lean4/pull/11255) 减少了使用字符串模式时的分配。
  尤其是 `startsWith`、`dropPrefix?`、`endsWith`、`dropSuffix?` 都得到了优化。

* [#11263](https://github.com/leanprover/lean4/pull/11263) 修复了新 `String` 接口中的若干内存泄漏。

* [#11266](https://github.com/leanprover/lean4/pull/11266) 为 `DHashMap`/`HashMap`/`HashSet` 及其外延变体添加 `BEq` 实例，并证明将其与哈希表等价性/外延变体相等性关联起来的引理。

* [#11267](https://github.com/leanprover/lean4/pull/11267) 重命名了 `DHashMap`/`HashMap`/`HashSet`/`DTreeMap`/`TreeMap`/`TreeSet` 上并集的同余引理，使之符合放在 `Equiv` 命名空间中的约定。

* [#11276](https://github.com/leanprover/lean4/pull/11276) 清理了 `String.find` 周边的接口，并统一迁移到新的位置类型 `String.ValidPos` 和 `String.Slice.Pos`。

* [#11281](https://github.com/leanprover/lean4/pull/11281) 为一些从未存在过、但对 #11180 之后迁移代码仍有帮助的函数添加了若干弃用项。

* [#11282](https://github.com/leanprover/lean4/pull/11282) 为 `String.Slice.contains` 添加别名 `String.Slice.any`。

* [#11285](https://github.com/leanprover/lean4/pull/11285) 在 `DecidablePred p` 成立时，为 `p : Char -> Prop` 添加 `Std.Slice.Pattern` 实例，从而允许写出诸如 `"hello".dropWhile (· = 'h')` 这样的代码。

* [#11286](https://github.com/leanprover/lean4/pull/11286) 添加了函数 `String.Slice.length`，其弃用说明如下：切片上不存在常数时间长度函数。
  请改用 `s.positions.count`；若只需要知道切片是否为空，则改用 `isEmpty`。

* [#11289](https://github.com/leanprover/lean4/pull/11289) 将 `String.foldl` 和 `String.isNat` 重新定义为使用其 `String.Slice` 对应版本。

* [#11290](https://github.com/leanprover/lean4/pull/11290) 将 `String.replaceStartEnd` 重命名为 `String.slice`，将 `String.replaceStart` 重命名为 `String.sliceFrom`，将 `String.replaceEnd` 重命名为 `String.sliceTo`；`String.Slice` 上对应函数也做了类似改名。

* [#11299](https://github.com/leanprover/lean4/pull/11299) 为 `Fin` 添加了许多 `@[grind]` 标注，并更新了测试。

* [#11308](https://github.com/leanprover/lean4/pull/11308) 将 `String` 上的 `front` 和 `back` 重新定义为通过 `String.Slice` 实现，并新增 `front?`、`back?`、`positions`、`chars`、`revPositions`、`revChars`、`byteIterator`、`revBytes`、`lines` 等 `String` 函数。

* [#11316](https://github.com/leanprover/lean4/pull/11316) 添加 `grind_pattern Exists.choose_spec => P.choose`。

* [#11317](https://github.com/leanprover/lean4/pull/11317) 添加 `grind_pattern Subtype.property => self.val`。

* [#11321](https://github.com/leanprover/lean4/pull/11321) 提供了关于 `Nat` 区间的专用引理，包括 `simp` 标注以及证明所有区间性质的归纳原理。

* [#11327](https://github.com/leanprover/lean4/pull/11327) 添加了两个用于证明 `a / c < b / c` 的引理。

* [#11341](https://github.com/leanprover/lean4/pull/11341) 添加了从 `String` 到 `String.Slice` 的强制转换。

* [#11343](https://github.com/leanprover/lean4/pull/11343) 将 `String.bytes` 重命名为 `String.toByteArray`。

* [#11354](https://github.com/leanprover/lean4/pull/11354) 添加了简单引理，说明从字符串中的某个位置开始搜索时，返回的位置至少不会早于该位置。

* [#11357](https://github.com/leanprover/lean4/pull/11357) 更新了 `String` 上的 `foldr`、`all`、`any` 和 `contains` 函数，使其以对应的 `String.Slice` 函数定义。

* [#11358](https://github.com/leanprover/lean4/pull/11358) 添加了 `String.Slice.toInt?` 及其变体。

* [#11376](https://github.com/leanprover/lean4/pull/11376) 试图提升 `String.contains`、`String.find` 等函数在使用 `Char` 或 `Char -> Bool` 模式时的性能。
  做法是把待匹配模式移出迭代器状态，以绕过编译器中缺失的拆箱优化。

* [#11380](https://github.com/leanprover/lean4/pull/11380) 将 `String.Slice.Pos.ofSlice` 重命名为 `String.Pos.ofToSlice`，以符合（尚未正式文档化的）“位置映射到位置”的命名约定。
  同时新增若干函数，使得对于从字符串和切片构造切片的每一种方式，现在都可以沿着该构造前后映射位置。

* [#11384](https://github.com/leanprover/lean4/pull/11384) 为 `grind` 推理 `String.Pos.Raw`、`String.Pos` 和 `String.Slice.Pos` 添加了必要实例。

* [#11399](https://github.com/leanprover/lean4/pull/11399) 为 `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` 添加差集操作支持，并证明若干相关引理。

* [#11404](https://github.com/leanprover/lean4/pull/11404) 为 `DTreeMap`/`TreeMap`/`TreeSet` 及其外延变体添加 `BEq` 实例，并证明若干引理，将其与哈希映射的等价性以及外延变体的相等性联系起来。

* [#11407](https://github.com/leanprover/lean4/pull/11407) 为 `DTreeMap`/`TreeMap`/`TreeSet` 添加差集操作，并证明若干相关引理。

* [#11421](https://github.com/leanprover/lean4/pull/11421) 为 `DHashMap`/`HashMap`/`HashSet` 及其外延变体添加可判定相等性。

* [#11439](https://github.com/leanprover/lean4/pull/11439) 对 String 接口做了小规模维护。

* [#11448](https://github.com/leanprover/lean4/pull/11448) 调整了常量 `DTreeMap`（及相关）查询中的 `Inhabited` 实例位置，例如 `Const.get!`；此时可以在证明键之前先提供 `Inhabited` 实例。

* [#11452](https://github.com/leanprover/lean4/pull/11452) 添加了若干引理：若某个 get 操作返回了值，则被查询的键必然包含在集合中。
  这些引理已添加到基于 HashMap 和 TreeMap 的集合中；`Init.getElem` 也添加了一个类似引理。

* [#11465](https://github.com/leanprover/lean4/pull/11465) 修复了代码库中文档和注释里的多个拼写错误。

* [#11503](https://github.com/leanprover/lean4/pull/11503) 将 `Char -> Bool` 模式标记为字符串搜索的默认实例。
  这意味着诸如 `" ".find (·.isWhitespace)` 这样的表达式现在可以无错精译。

* [#11521](https://github.com/leanprover/lean4/pull/11521) 修复了一个分段错误：当初始化新计时器的同时调用 reset 时会触发该错误。

* [#11527](https://github.com/leanprover/lean4/pull/11527) 为 `DTreeMap`/`TreeMap`/`TreeSet` 及其外延变体添加可判定相等性。

* [#11528](https://github.com/leanprover/lean4/pull/11528) 为所有 `DTreeMap` 及其派生容器添加引理，将 `minKey?` 和键列表上的 `min?` 联系起来。

* [#11542](https://github.com/leanprover/lean4/pull/11542) 从 `List.countP_eq_length_filter` 和 `Array.countP_eq_size_filter` 上移除了 `@[grind =]`，因为用户反馈这会带来问题。

* [#11548](https://github.com/leanprover/lean4/pull/11548) 为 `String.Slice` 添加 `Lean.ToJson` 和 `Lean.FromJson` 实例。

* [#11565](https://github.com/leanprover/lean4/pull/11565) 为 `DTreeMap`/`DHashMap` 派生容器添加引理，把 `insert`/`insertIfNew` 与 `toList` 关联起来。

* [#11574](https://github.com/leanprover/lean4/pull/11574) 添加了一个引理，表明自然数强制转换到任意有序环后是非负的。
  我们不能直接把它标注给 `grind`，但可能会把它加入 `grind` 的 linarith 内部机制。

* [#11578](https://github.com/leanprover/lean4/pull/11578) 将 `HashMap`/`TreeMap`/`ExtHashMap`/`ExtTreeMap` 上 `get` 操作的用法重构为 `getElem` 实例。

* [#11591](https://github.com/leanprover/lean4/pull/11591) 补充了关于 `ReaderT.run`、`OptionT.run`、`StateT.run` 和 `ExceptT.run` 如何与 `MonadControl` 操作交互的缺失引理。

* [#11596](https://github.com/leanprover/lean4/pull/11596) 在 `Int` 上添加 `@[suggest_for ℤ]`，在 `Rat` 上添加 `@[suggest_for ℚ]`，沿用 #11554 中 `Nat` 上 `@[suggest_for ℕ]` 建立的模式。

* [#11600](https://github.com/leanprover/lean4/pull/11600) 为基本操作上的 `EStateM.run` 添加了若干引理。

* [#11625](https://github.com/leanprover/lean4/pull/11625) 为 `decidable_of_bool` 添加 `@[expose]`，使得其他地方通过 `decide` 得到、并归约到 `decidable_of_bool` 的证明仍然可以继续归约。

* [#11654](https://github.com/leanprover/lean4/pull/11654) 更新了 `grind` 的文档字符串。
  其中此前仍提到已重命名为 `lia` 的 `cutsat`。这个问题是在 ItaLean 期间报告的。

```

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Tactics"
%%%

````markdown

* [#11226](https://github.com/leanprover/lean4/pull/11226) 终于移除了旧的 `grind` 框架 `SearchM`，并改用新的 `Action` 框架。

* [#11244](https://github.com/leanprover/lean4/pull/11244) 修复了 `grind` 中的一些小问题，为加入 `grind -revert` 做准备。

* [#11247](https://github.com/leanprover/lean4/pull/11247) 修复了 `grind` 预处理器中的一个问题：`simp` 可能会引入已赋值的（宇宙）元变量（例如执行 zeta 归约时）。

* [#11248](https://github.com/leanprover/lean4/pull/11248) 实现了 `revert` 选项，其默认值为 `false`。
  若要恢复旧的 `grind` 行为，应使用 `grind +revert`。
  以前，`grind` 采用 `RevSimpIntro` 习惯用法：先回退所有假设，再在化简并急切应用 `cases` 的过程中把它们重新引入。
  这种做法带来了若干问题：

  * 用户反馈 `grind` 会包含不必要的参数。见[这里](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20aggressively.20includes.20local.20hypotheses.2E/near/554887715)。
  * 还会引入不必要的节变量。可见 Sebastian Graf 贡献的新测试。
  * 最后，它还阻碍了我们像 `simp` 那样支持任意参数。在 `simp` 中，我实现了一个模拟局部宇宙多态定理的机制，但这种方法不能用于 `grind`，因为它没有回退（以及重新引入）局部宇宙多态定理的机制。要增加这样的机制需要做大量工作：我需要修改局部上下文对象。我考虑过维护从原始变量到新变量的替换，但这也很棘手，因为映射必须存储在 `grind` 目标对象中，而且它并不只是简单映射。回退完所有内容后，我需要保留一串原始变量，以便在重新引入它们时把它们加入映射，而急切的分情况拆分会让这件事复杂得多。整个方案显得过于混乱。

* [#11265](https://github.com/leanprover/lean4/pull/11265) 将自动生成的 `sizeOf` 定理标记为 `grind` 定理。

* [#11268](https://github.com/leanprover/lean4/pull/11268) 实现了对任意 `grind` 参数的支持。
  该特性类似于 `simp` 中的做法：把证明项视为局部宇宙多态引理。
  它依赖 `grind -revert`（见 #11248）。例如，用户现在可以写：

  ```lean
  def snd (p : α × β) : β := p.2
  theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

* [#11273](https://github.com/leanprover/lean4/pull/11273) 修复了 `grind` 在构造证明时的一个 bug。

* [#11295](https://github.com/leanprover/lean4/pull/11295) 修复了 `grind` 中用于 `ite` 和 `dite` 的传播规则的一个 bug。
  该问题会阻止相等式传播到卫星求解器。下面给出一个受影响的例子。

* [#11315](https://github.com/leanprover/lean4/pull/11315) 修复了一个影响 `grind -revert` 的问题。
  在这种模式下，假设中的已赋值元变量不会被实例化。该问题影响了 Mathlib 中两个文件。

* [#11318](https://github.com/leanprover/lean4/pull/11318) 修复了 `grind` 中局部声明 internalization 的一个问题，该问题会在使用 `grind -revert` 时暴露出来。
  这个 bug 影响了 Mathlib 中的一个 `grind` 证明。

* [#11319](https://github.com/leanprover/lean4/pull/11319) 改进了 `grind` 在 `n` 不是数值字面量时对 `Fin n` 的支持。

* [#11323](https://github.com/leanprover/lean4/pull/11323) 引入了新的 `grind` 选项 `funCC`（默认启用），它把同余闭包扩展到*函数值*相等式。
  启用 `funCC` 后，`grind` 会跟踪**部分应用函数**之间的相等式，从而支持如下推理：
  ```lean
  a : Nat → Nat
  f : (Nat → Nat) → (Nat → Nat)
  h : f a = a
  ⊢ (f a) m = a m

* [#11326](https://github.com/leanprover/lean4/pull/11326) 确保用户可以提供类型并非 `forall` 量化的 `grind` 证明参数。示例：

  ```lean
  opaque f : Nat → Nat
  axiom le_f (a : Nat) : a ≤ f a

* [#11330](https://github.com/leanprover/lean4/pull/11330) 将 `cutsat` 策略重命名为 `lia`，以更好地与定理证明社区的标准术语保持一致。

* [#11331](https://github.com/leanprover/lean4/pull/11331) 在 `grind` 中加入对 `LawfulOfScientific` 类的支持。示例：
  ```lean
  open Lean Grind Std
  variable [LE α] [LT α] [LawfulOrderLT α] [Field α] [OfScientific α]
           [LawfulOfScientific α] [IsLinearOrder α] [OrderedRing α]
  example : (2 / 3 : α) ≤ (0.67 : α) := by  grind
  example : (1.2 : α) ≤ (1.21 : α) := by grind
  example : (2 / 3 : α) ≤ (67 / 100 : α) := by grind
  example : (1.2345 : α) ≤ (1.2346 : α) := by grind
  example : (2.3 : α) ≤ (4.5 : α) := by grind
  example : (2.3 : α) ≤ (5/2 : α) := by grind
  ```

* [#11332](https://github.com/leanprover/lean4/pull/11332) 添加了 `grind_annotated "YYYY-MM-DD"` 命令，用于把文件标记为已手动为 grind 添加标注。

* [#11334](https://github.com/leanprover/lean4/pull/11334) 在 `grind linarith` 模块中加入显式的环约束归一化层。
  例如，当环是一个 `Field` 时，它会被用来清理分母。

* [#11335](https://github.com/leanprover/lean4/pull/11335) 在 `grind` 策略块中启用语法 `use [ns Foo]` 和 `instantiate only [ns Foo]`，其效果是激活该命名空间作用域下的全部 grind pattern。
  我们可以借此用 `grind` 实现专用策略，但只启用受控的定理子集。

* [#11348](https://github.com/leanprover/lean4/pull/11348) 通过移除 TODO 注释并取消对该命令的注释，在 `Init.Data.List.Lemmas` 中启用了 `grind_annotated` 命令。

* [#11350](https://github.com/leanprover/lean4/pull/11350) 为 `grind` 实现了一个辅助 simproc。
  它是 `grind linarith` 中清理分母所用基础设施的一部分。

* [#11365](https://github.com/leanprover/lean4/pull/11365) 为 `try?` 启用了并行性。
  目前我们把 `attempt_all` 阶段（有两个：一个针对包括 `grind` 和 `simp_all` 在内的内建策略，另一个针对所有用户扩展）替换为并行版本。
  暂时还没有改变基于 `first` 的阶段行为。

* [#11373](https://github.com/leanprover/lean4/pull/11373) 让库建议扩展状态在从 `module` 文件导入时也可用。

* [#11375](https://github.com/leanprover/lean4/pull/11375) 在类型是 `Field` 时，为 `grind linarith` 增加清理分母的支持。

* [#11391](https://github.com/leanprover/lean4/pull/11391) 为 `grind_pattern` 命令实现了新类型的约束。
  这些约束允许用户控制 `grind` 中的定理实例化。
  由于该变更会影响 `.olean` 格式，因此需要手动执行 `update-stage0`；否则该拉取请求会失败。

* [#11396](https://github.com/leanprover/lean4/pull/11396) 改变了 `set_library_suggestions` 的实现：它现在创建一个标记为 `@[library_suggestions]` 的辅助定义，而不是把 `Syntax` 直接存进环境扩展。
  这使得跨模块的库建议具有更好的持久性与一致性。

* [#11405](https://github.com/leanprover/lean4/pull/11405) 实现了如下 `grind_pattern` 约束：
  ```lean
  grind_pattern fax => f x  where
    depth x < 2

* [#11409](https://github.com/leanprover/lean4/pull/11409) 实现了对 `grind_pattern` 约束 `is_value` 与 `is_strict_value` 的支持。

* [#11410](https://github.com/leanprover/lean4/pull/11410) 修复了 grind 分母清理功能中的一个 kernel 类型不匹配错误。
  在生成涉及逆元数字（如 `2⁻¹`）的证明时，证明上下文会被压缩，只保留实际使用到的变量。
  这会涉及变量索引重命名——例如，若原始索引为 `{0: r, 1: 2⁻¹}` 而实际只用到 `2⁻¹`，那么它会被重命名为索引 0。

* [#11412](https://github.com/leanprover/lean4/pull/11412) 修复了一个问题：多次调用 `norm_cast` 后，`grind` 会因错误 “unexpected metadata found during internalization” 而失败。

* [#11428](https://github.com/leanprover/lean4/pull/11428) 在 `grind_pattern` 中实现了对 **guards** 的支持。
  这一新特性为定理实例化提供了更多控制。例如，考虑下面这个单调性定理：

  ```lean
  opaque f : Nat → Nat
  theorem fMono : x ≤ y → f x ≤ f y := ...
  ```

* [#11429](https://github.com/leanprover/lean4/pull/11429) 为 `grind_pattern` 命令编写文档，说明如何手动选择定理实例化模式，包括多模式以及约束系统（`=/=`、`=?=`、`size`、`depth`、`is_ground`、`is_value`、`is_strict_value`、`gen`、`max_insts`、`guard`、`check`）。

* [#11462](https://github.com/leanprover/lean4/pull/11462) 在 `try?` 的简单策略中把 `solve_by_elim` 作为后备。
  当 `rfl` 和 `assumption` 都失败，但 `solve_by_elim` 成功时（例如目标需要假设链式使用或回溯），`try?` 现在会建议 `solve_by_elim`。

* [#11464](https://github.com/leanprover/lean4/pull/11464) 改进了在未注册库建议引擎时的错误消息，建议为内建引擎导入 `Lean.LibrarySuggestions.Default`。

* [#11466](https://github.com/leanprover/lean4/pull/11466) 移除了 `exact?` 与 `apply?` 的“首轮尝试”行为；它们以前会在库搜索前，先在原始目标上尝试 `solve_by_elim`。
  这简化了 `librarySearch` 接口，并让这些策略专注于其主要用途：查找库引理。

* [#11468](https://github.com/leanprover/lean4/pull/11468) 为 `solve_by_elim` 添加 `+suggestions` 支持，沿用了 `grind +suggestions` 与 `simp_all +suggestions` 建立的模式。

* [#11469](https://github.com/leanprover/lean4/pull/11469) 为 `exact?` 和 `apply?` 策略添加 `+grind` 与 `+try?` 选项。

* [#11471](https://github.com/leanprover/lean4/pull/11471) 修复了使用 `grind` 交互模式时一个错误的 reducibility 设置。

* [#11480](https://github.com/leanprover/lean4/pull/11480) 新增 `grind` 选项 `reducible`（默认：`true`）。
  启用后，定义相等性测试只会展开标记为 `@[reducible]` 的声明。
  使用 `grind -reducible` 可在定义相等性测试期间允许展开不可约声明。
  该选项只影响定义相等性；规范化器和定理模式的内部化总会展开 reducible 声明，而不受该设置影响。

* [#11481](https://github.com/leanprover/lean4/pull/11481) 修复了 `grind?` 中的一个错误。
  使用 `grind` 交互模式给出的建议会丢失用户提供的配置选项。
  在下面的说明中，第三条建议会丢掉 `-reducible` 选项。

* [#11484](https://github.com/leanprover/lean4/pull/11484) 修复了 `grind` 模式校验中的一个错误。该问题会影响那些本身是命题的类型类。

* [#11487](https://github.com/leanprover/lean4/pull/11487) 添加了构造子单射性定理的异构版本。
  这些定理对带索引族很有用，并将被用于 `grind`。

* [#11491](https://github.com/leanprover/lean4/pull/11491) 在 `grind` 中实现了异构构造子单射性。

* [#11494](https://github.com/leanprover/lean4/pull/11494) 重新启用了带星号索引的引理，作为 `exact?` 和 `apply?` 的后备。

* [#11519](https://github.com/leanprover/lean4/pull/11519) 将 `Nat` 的幂与整除性定理标记给 `grind`。
  我们用新的 `grind_pattern` 约束来控制定理实例化。
  示例：

  ```lean
  example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
    grind

* [#11520](https://github.com/leanprover/lean4/pull/11520) 在 `grind_pattern` 命令中实现了约束 `not_value x`。
  它是约束 `is_value` 的否定。

* [#11522](https://github.com/leanprover/lean4/pull/11522) 为那些带有关联 simproc、但没有任何 theory solver 支持的 `Nat` 运算符实现了 `grind` propagator。
  示例：

  ```lean
  example (a b : Nat) : a = 3 → b = 6 → a &&& b = 2 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ||| b = 7 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ^^^ b = 5 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a <<< b = 192 := by grind
  example (a b : Nat) : a = 1135 → b = 6 → a >>> b = 17 := by grind
  ```

* [#11547](https://github.com/leanprover/lean4/pull/11547) 确保 `register_try?_tactic` 创建的辅助定义属于内部实现细节，不应对面向用户的检查器可见。

* [#11556](https://github.com/leanprover/lean4/pull/11556) 为 `exact?` 和 `apply?` 添加 `+all` 选项，用于收集所有成功引理，而不是在第一个完整解处停止。

* [#11573](https://github.com/leanprover/lean4/pull/11573) 修复了 `grind` 误把点记法项当作局部假设而拒绝它们的问题。

* [#11579](https://github.com/leanprover/lean4/pull/11579) 确保无自由变量定理会被正确处理为 `grind` 参数。
  另外，`grind [(thm)]` 与 `grind [thm]` 应按同样方式处理。

* [#11580](https://github.com/leanprover/lean4/pull/11580) 为 `grind` 添加了一个缺失的 `Nat.cast` 归一化规则。示例：
  ```lean
  example (n : Nat) : Nat.cast n = n := by
    grind
  ```

* [#11589](https://github.com/leanprover/lean4/pull/11589) 改进了 `grind` 模式的索引。
  我们现在会把嵌套无自由变量模式中出现的符号也纳入索引。
  这对尽量减少被激活的 E-匹配定理数量很重要。

* [#11593](https://github.com/leanprover/lean4/pull/11593) 修复了一个问题：当参数列表中使用了已弃用引理时，`grind` 不会显示弃用警告。

* [#11594](https://github.com/leanprover/lean4/pull/11594) 修复了 `grind?`，使其在建议中包含项参数（例如 `[show P by tac]`）。
  之前这些参数会丢失，因为项参数存储在 `extraFacts` 中，不像具名引理那样通过 E-匹配跟踪。

* [#11604](https://github.com/leanprover/lean4/pull/11604) 修复了 `grind` 处理无参数定理的方式。

* [#11605](https://github.com/leanprover/lean4/pull/11605) 修复了 `grind linarith` 中 `a^p` 项内部化器的一个错误。

* [#11609](https://github.com/leanprover/lean4/pull/11609) 改进了 `grind` 中的分情况拆分启发式。
  在这个拉取请求中，我们不会在第一个分支里增加分情况拆分计数。
  核心思路是利用非按时间顺序的回溯：若第一个分支可由不依赖分支假设的证明解决，我们就回溯并直接关闭原目标。
  在这种场景下，这次分情况拆分是“免费的”，并未对证明作出贡献。
  不对其计数后，当分情况拆分最终无关时，我们就能探索得更深。
  新的启发式修复了 #11545 中第二个示例。

* [#11613](https://github.com/leanprover/lean4/pull/11613) 确保我们会把环归一化器应用于从 `grind` 核心模块传播到 `grind lia` 的相等式。
  同时也确保归一化时使用安全 / 托管的多项式函数。

* [#11615](https://github.com/leanprover/lean4/pull/11615) 为 `grind` 添加了 `Int.subNatNat` 的归一化规则。

* [#11628](https://github.com/leanprover/lean4/pull/11628) 为 `grind` 中的 `Semiring` 添加了若干 `*` 归一化规则。

* [#11629](https://github.com/leanprover/lean4/pull/11629) 为 `grind` 使用的模式归一化代码添加了一个缺失条件。
  它应忽略支撑基项。

* [#11635](https://github.com/leanprover/lean4/pull/11635) 确保 `grind` 中使用的模式归一化器不会违反 `Grind.genPattern` 与 `Grind.getHEqPattern` 这些辅助构件所依赖的假设。

* [#11638](https://github.com/leanprover/lean4/pull/11638) 修复了 `grind` 中位向量字面量的内部化。
  修复后，以 `BitVec.ofNat` 建索引的定理能够被正确激活。

* [#11639](https://github.com/leanprover/lean4/pull/11639) 在 `grind ring` 中添加对 `BitVec.ofNat` 的支持。示例：

  ```lean
  example (x : BitVec 8) : (x - 16#8)*(x + 272#8) = x^2 := by
    grind
  ```

* [#11640](https://github.com/leanprover/lean4/pull/11640) 在 `grind lia` 中添加对 `BitVec.ofNat` 的支持。示例：

  ```lean
  example (x y : BitVec 8) : y < 254#8 → x > 2#8 + y → x > 1#8 + y := by
    grind
  ```

* [#11653](https://github.com/leanprover/lean4/pull/11653) 添加了与 #11628 引入的 `Semiring` 归一化规则相对应的传播规则。
  这些新规则只适用于非交换半环，因为 `grind` 对它们的支持有限。
  这些归一化规则在 Mathlib 中引入了意外行为，因为它们会中和诸如 `one_mul` 之类的参数：任何与此类参数关联的定理实例，都会被归一化器化成 `True`。

* [#11656](https://github.com/leanprover/lean4/pull/11656) 为 `grind` 添加对 `Int.sign`、`Int.fdiv`、`Int.tdiv`、`Int.fmod`、`Int.tmod` 和 `Int.bmod` 的支持。
  这些操作只是被预处理掉。我们假定它们在实践中并不常见。
  示例：
  ```lean
  example {x y : Int} : y = 0 → (x.fdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.tdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.fmod y) = x := by grind
  example {x y : Int} : y = 1 → (x.fdiv (2 - y)) = x := by grind
  example {x : Int} : x > 0 → x.sign = 1 := by grind
  example {x : Int} : x < 0 → x.sign = -1 := by grind
  example {x y : Int} : x.sign = 0 → x*y = 0 := by grind
  ```

* [#11658](https://github.com/leanprover/lean4/pull/11658) 修复了 `grind` 中参数化字面量内部化的一个错误，也就是类型为 `BitVec _` 或 `Fin _` 的字面量。

* [#11659](https://github.com/leanprover/lean4/pull/11659) 在为 `@[grind]` 生成模式建议时加入 `MessageData.withNamingContext`。
  这修复了在 ItaLean 期间报告的另一个问题。

* [#11660](https://github.com/leanprover/lean4/pull/11660) 修复了 `grind` 中另一个定理激活问题。

* [#11663](https://github.com/leanprover/lean4/pull/11663) 修复了 `grind` 模式校验器。
  它覆盖了实例未用隐式实例绑定器标记的情况。这种情况会出现在如下声明中：
  ```lean
  ZeroMemClass.zero_mem {S : Type} {M : outParam Type} {inst1 : Zero M} {inst2 : SetLike S M}
    [self : @ZeroMemClass S M inst1 inst2] (s : S) : 0 ∈ s
  ```

````

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Compiler"
%%%

```markdown

* [#11082](https://github.com/leanprover/lean4/pull/11082) 防止来自不同 Lean 包的（非 `@[export]`）定义发生符号冲突。

* [#11185](https://github.com/leanprover/lean4/pull/11185) 修复了 `reduceArity` 编译器过程，使其会考虑那些元数已被缩减的函数上的过量应用。
  以前该过程假定应用的参数个数始终等于签名中的参数个数。
  这通常是对的，因为只要返回类型还是函数类型，编译器就会急切引入参数，使得函数最终的返回类型不再是函数类型。
  但对于有时是函数类型、有时又不是函数类型的依赖类型，这个假设会失效，从而导致附加参数被丢弃。

* [#11210](https://github.com/leanprover/lean4/pull/11210) 修复了在处理 #11078 时暴露出的一个 LCNF 化简器缺陷。
  在某些由 `unsafeCast` 引起的场景中，化简器会记录关于 `cases` 的错误信息，从而在后续导致更多错误。

* [#11215](https://github.com/leanprover/lean4/pull/11215) 修复了一个问题：标题嵌套层级在不同 moduledoc 之间能被正确跟踪，但在单个 moduledoc 内部不能。

* [#11217](https://github.com/leanprover/lean4/pull/11217) 修复了 #10982 中闭包分配器修改的后续影响。
  据我们所知，这个错误只有在不使用 mimalloc 的非默认构建配置中才会明显出现，例如：
  cmake --preset release -DUSE_MIMALLOC=OFF

* [#11310](https://github.com/leanprover/lean4/pull/11310) 让特化器（正确地）在多次调用之间共享更多缓存键，从而减少代码膨胀。

* [#11340](https://github.com/leanprover/lean4/pull/11340) 修复了遇到非平凡结构类型投影时的错误编译。

* [#11362](https://github.com/leanprover/lean4/pull/11362) 加快了 ElimDeadBranches 编译器过程的终止。

* [#11366](https://github.com/leanprover/lean4/pull/11366) 按大小递增顺序排列送入 ElimDeadBranches 的声明。
  当存在大量迭代时，这可以提升性能。

* [#11381](https://github.com/leanprover/lean4/pull/11381) 修复了一个错误：闭项提取没有遵守 C 发射器的隐式不变量，即在强连通分量（SCC）内先放闭项声明、后放其他声明。
  这个错误目前尚未在实际使用中触发，但在即将对特化器进行修改的工作中被发现了。

* [#11383](https://github.com/leanprover/lean4/pull/11383) 修复了带有 `extern` 标记的未装箱参数的结构投影编译问题，并补上缺失的 `dec` 指令。
  这曾导致这类函数用作闭包或在解释器中使用时泄漏单个分配。

* [#11388](https://github.com/leanprover/lean4/pull/11388) 是 #11381 的后续工作。
  它在把声明保存进 Environment 之前通过拓扑排序，正确强制执行 EmitC 流程所要求的闭项与常量的顺序不变量。

* [#11426](https://github.com/leanprover/lean4/pull/11426) 关闭了 #11356。

* [#11445](https://github.com/leanprover/lean4/pull/11445) 稍微改进了创建装箱声明时涉及的类型。
  以前，返回装箱标量时用于返回值的 vdecl 类型总是 `tobj`。
  这并不是我们能给出的最精确标注。

* [#11451](https://github.com/leanprover/lean4/pull/11451) 调整了 LCNF 中的 λ 提升器：若可能则进行 η 收缩，而不是 λ 提升。
  这避免了整个代码库中产生几百个不必要的 λ 抽象。

* [#11517](https://github.com/leanprover/lean4/pull/11517) 为 Nat.mul 实现了常量折叠。

* [#11525](https://github.com/leanprover/lean4/pull/11525) 让 LCNF 化简器在所有备选都为 `.unreach` 时，将其直接化简为一个 `.unreach`。

* [#11530](https://github.com/leanprover/lean4/pull/11530) 引入了新的 `tagged_return` 属性。
  它允许用户将 `extern` 声明标记为保证总是返回 `tagged` 返回值。
  与 `object` 或 `tobject` 不同，编译器不会为其发出引用计数操作。
  未来将利用该属性信息进行更强的分析，以便在可能时移除引用计数。

* [#11576](https://github.com/leanprover/lean4/pull/11576) 移除了旧的 ElimDeadBranches 流程，并把新流程移到 λ 提升之后。

* [#11586](https://github.com/leanprover/lean4/pull/11586) 允许在 IR 类型系统中对 `tagged` 值进行投影。

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Documentation"
%%%

```markdown

* [#11119](https://github.com/leanprover/lean4/pull/11119) 在 “undefined identifier” 错误消息中加入澄清说明：当未定义标识符出现在通常可能适用自动绑定、但该处自动绑定已禁用的语法位置时，会给出该说明。
  对应说明也加入到了 `lean.unknownIdentifier` 错误解释中。

* [#11364](https://github.com/leanprover/lean4/pull/11364) 为参考手册中出现的常量补上缺失的文档字符串。

* [#11472](https://github.com/leanprover/lean4/pull/11472) 为 `mkSlice` 方法补上缺失的文档字符串。

* [#11550](https://github.com/leanprover/lean4/pull/11550) 审查了会出现在 Lean 参考手册中的 `Std.Do` 文档字符串，并补上缺失项。

* [#11575](https://github.com/leanprover/lean4/pull/11575) 修复了 `cases` 策略文档字符串中的一个拼写错误。

* [#11595](https://github.com/leanprover/lean4/pull/11595) 记录了 `tests/lean/run/` 中的测试会以 `-Dlinter.all=false` 运行，并解释了在测试检查器行为时如何启用特定检查器。

```

# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Server"
%%%

```markdown

* [#11162](https://github.com/leanprover/lean4/pull/11162) 降低了语言服务器的内存占用（尤其是监视进程）。在 Mathlib 中，内存占用大约减少了 1 GB。

* [#11164](https://github.com/leanprover/lean4/pull/11164) 确保对未知标识符给出的代码操作会在 `module` 中正确插入 `public` 和/或 `meta`。

* [#11577](https://github.com/leanprover/lean4/pull/11577) 修复了策略框架报告文件进度条范围时会覆盖嵌套在策略组合子里的策略块内部进度的问题。
  这只是纯粹的视觉改动；受支持组合子内部的增量重新精译不受影响。

```

# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Lake"
%%%

```markdown

* [#11198](https://github.com/leanprover/lean4/pull/11198) 修复了 Lake 中一条会建议错误 lakefile 语法的错误消息。

* [#11216](https://github.com/leanprover/lean4/pull/11216) 确保在 Lake 代码中始终为 `computeArtifact` 提供 `text` 参数，同时顺带修复了 `buildArtifactUnlessUpToDate` 的一个哈希错误。

* [#11270](https://github.com/leanprover/lean4/pull/11270) 为 Lake 添加模块解析过程，以消除在多个包中定义的模块歧义。

* [#11500](https://github.com/leanprover/lean4/pull/11500) 在构建目标所使用包的名称中加入工作区索引。
  为了澄清一个包名的不同用途之间的区别，这个拉取请求还弃用了 `Package.name`，转而使用更贴合具体用途的变体（例如 `Package.keyName`、`Package.prettyName`、`Package.origName`）。

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___27___0-_LPAR_2026-01-24_RPAR_--Other"
%%%

````markdown

* [#11328](https://github.com/leanprover/lean4/pull/11328) 修复了在某些精译负载下，语言服务器为每个文档版本意外保留的内存无法释放的问题。该问题肯定自 4.18.0 起就已存在。

* [#11437](https://github.com/leanprover/lean4/pull/11437) 添加了记录功能，使 `shake` 能更精确地跟踪一个导入是否仅仅因为它的 `attribute` 命令而必须保留。

* [#11496](https://github.com/leanprover/lean4/pull/11496) 为 Mathlib 中使用的 `shake` 实现了新的选项与标注：

  > 选项：
  >   --keep-implied
  > 保留那些虽被其他导入所蕴含、因此从技术上说已不再必需的现有导入
  >
  >   --keep-prefix
  > 若导入 `X` 会被它所蕴含的、更具体的导入 `X.Y...` 替换，
  > 则改为保留原始导入。更一般地，只要 `X` 属于当前模块原始的传递导入闭包，
  > 即使它原本不在原始导入列表中，也优先插入 `import X`
  >
  >   --keep-public
  > 保留所有 `public` 导入，以避免对外部下游模块造成破坏性变更
  >
  >   --add-public
  > 若新导入曾位于该模块原始的 public 闭包中，则将其以 `public` 形式加入。
  > 换言之，只有当 public 导入在 private 作用域中也未被使用时，才会从模块中移除；
  > 而那些被移除的导入，即使在下游模块中仅在 private 作用域中需要，也会被重新以 `public` 形式加入。
  > 与 `--keep-public` 不同，这可能引入破坏性变更，但仍会限制插入导入的数量。
  >
  > 标注：
  > 可以向 Lean 文件中加入下列标注来配置 `shake` 的行为。
  > 只会检查直接跟在指令前的子串 `shake: `，因此多个指令可以混在同一行中，例如 `-- shake: keep-downstream, shake: keep-all`，
  > 也可以被任意注释包围，例如 `-- shake: keep (元编程输出依赖)`。
  >
  >   * `module -- shake: keep-downstream`:
  > 在所有（当前）下游模块中保留此模块，并在需要时新增对它的导入。
  >
  >   * `module -- shake: keep-all`:
  > 按原样保留该模块中的全部现有导入。
  > 由于上游变化而现在需要的新导入仍可能被加入。
  >
  >   * `import X -- shake: keep`:
  > 在当前模块中保留这一特定导入。最常见的用例是保留某个 public 导入，
  > 因为下游模块需要它才能理解本模块中定义的元程序输出。
  > 例如，若定义了一个策略，它在运行时可能会合成对某个定理的引用，
  > 那么 `shake` 无法自行检测到这一点，因此该定理所在模块应被 public 导入，
  > 并在该策略所在模块中用 `keep` 标注。
  >     ```
  >     public import X  -- shake: keep (元编程输出依赖)
  >
  >     ...
  >
  >     elab \"my_tactic\" : tactic => do
  > ... mkConst ``f -- `f` 定义于 `X` 中，可能出现在该策略的输出里
  >     ```

* [#11507](https://github.com/leanprover/lean4/pull/11507) 优化了导入过程中的文件系统访问，在 Linux 上带来约 3% 的收益，在其他平台上可能更多。

````
