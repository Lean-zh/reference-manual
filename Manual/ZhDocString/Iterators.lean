/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Std.Data.Iterators
import Std.Data.TreeMap
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Iterators

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w u₁ u₂ w₁ w₂

open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

/--
一种依次发出 `β` 类型值的迭代器。它可以是有限的，也可以是无限的。

迭代器框架的更全面概览见根模块 `Std.Data.Iterators`。

如何迭代常见数据结构见 `Std.Data.Iterators.Producers`。按照约定，与对象关联的单子式迭代器可通过点记法取得。例如，`List.iterM IO` 会在单子 `IO` 中创建一个遍历列表的迭代器。

迭代器的使用方式见 `Init.Data.Iterators.Consumers`。例如，`it.toList` 会把迭代器 `it` 转换为列表；若有该迭代器有限的证明，`it.ensureTermination.toList` 可保证此操作终止。也始终可以用 `it.step` 手动迭代，并以终止度量 `it.finitelyManySteps` 和 `it.finitelyManySkips` 证明终止。

在单子中运行的迭代器见 `IterM`。

在内部，`Iter β` 包装一个包含状态信息的 `α` 类型元素。类型 `α` 通过类型类机制决定迭代器的实现；实际实现迭代器的类型类是 `Iterator α m β`。

使用组合子时，`α` 可能变得非常复杂。它是 `α` 的隐式参数，因此漂亮打印器默认不会打印这个庞大类型。若声明返回迭代器，以下写法不可行：

```lean
def x : Iter Nat := [1, 2, 3].iter
```

应当完全省略声明的类型：

```lean
def x := [1, 2, 3].iter

-- 若要确保 `x` 是发出 `Nat` 的迭代器
def x := ([1, 2, 3].iter : Iter Nat)
```
-/
structure c001 {α : Type w} (β : Type w) where
  /-- 迭代器的内部实现细节。 -/
  internalState : α

/--
一种在单子 `m` 中依次发出 `β` 类型值的迭代器。它可以是有限的，也可以是无限的。

迭代器框架的更全面概览见根模块 `Std.Data.Iterators`。

如何迭代常见数据结构见 `Std.Data.Iterators.Producers`。按照约定，与对象关联的单子式迭代器可通过点记法取得。例如，`List.iterM IO` 会在单子 `IO` 中创建一个遍历列表的迭代器。

迭代器的使用方式见 `Init.Data.Iterators.Consumers`。例如，`it.toList` 会把迭代器 `it` 转换为列表；若有该迭代器有限的证明，`it.ensureTermination.toList` 可保证此操作终止。也始终可以用 `it.step` 手动迭代，并以终止度量 `it.finitelyManySteps` 和 `it.finitelyManySkips` 证明终止。

若不需要单子式效应（`m = Id`），可使用接口更方便的 `Iter`。

在内部，`IterM m β` 包装一个包含状态信息的 `α` 类型元素。类型 `α` 通过类型类机制决定迭代器的实现；实际实现迭代器的类型类是 `Iterator α m β`。

使用组合子时，`α` 可能变得非常复杂。它是 `α` 的隐式参数，因此漂亮打印器默认不会打印这个庞大类型。若声明返回迭代器，以下写法不可行：

```lean
def x : IterM IO Nat := [1, 2, 3].iterM IO
```

应当完全省略声明的类型：

```lean
def x := [1, 2, 3].iterM IO

-- 若要确保 `x` 是在 `IO` 中发出 `Nat` 的迭代器
def x := ([1, 2, 3].iterM IO : IterM IO Nat)
```
-/
structure c002 {α : Type w} (m : Type w → Type v) (β : Type w) where
  /-- 迭代器的内部实现细节。 -/
  internalState : α

/-- 将迭代器状态包装为 `IterM` 对象。 -/
add_decl_doc c002.mk

/--
`IterStep α β` 表示迭代器（`Iter β` 或 `IterM m β`）执行的一步。
-/
inductive c003 : Sort u → Sort v → Sort (max (max 1 u) v) where
  /-- `IterStep.yield it out` 表示迭代器发出 `out`，并以 `it` 作为后继迭代器。 -/
  | yield : α → β → c003 α β
  /-- `IterStep.skip it` 表示迭代器本次迭代不发出任何值，并以 `it'` 作为后继迭代器。

允许 `skip` 步骤是为了让迭代器循环能生成高效代码。 -/
  | skip : α → c003 α β
  /-- `IterStep.done` 表示迭代器已经结束，不会再发出值，也不会再产生单子式效应；此时不提供后继迭代器。 -/
  | done : c003 α β

/--
`Iter.step` 返回的步骤对象类型，其中包含一个 `IterStep`，以及它是给定迭代器之合理步骤的证明。
-/
def c004 := @Iter.Step

/--
`IterM.step` 返回的步骤对象类型，其中包含一个 `IterStep`，以及它是给定迭代器之合理步骤的证明。
-/
def c005 := @IterM.Step

/--
`Iter (α := α) β` 或 `IterM (α := α) m β` 中迭代器的步进函数。

为了在使用 `step` 函数迭代时支持内蕴的终止性证明，步骤对象还携带一个证明，表明它是给定当前迭代器的“合理”步骤。
-/
class c006 (α : Type w) (m : Type w → Type v) (β : outParam (Type w)) where
  /-- 支配给定迭代器所允许步骤的关系。

“合理”步骤是对给定状态有意义的步骤；合理性可保证诸如后继迭代器仍来自同一集合、跳过所得迭代器会返回相同的下一个值，或下一个产出项确为原集合中的下一项等性质。 -/
  IsPlausibleStep : @Std.IterM α m β → Std.IterStep (@Std.IterM α m β) β → Prop
  /-- 执行一个迭代步骤。 -/
  step : (it : @Std.IterM α m β) → m (Std.Shrink (@Std.PlausibleIterStep (@Std.IterM α m β) β (IsPlausibleStep it)))

/--
`IterStep` 的一种变体，将步骤与该步骤“合理”的证明打包在一起。之后会选择合理性谓词来断言某个状态是另一状态的合理后继。将此证明与步骤打包对终止性证明很重要。

合理性谓词的具体选择见 `IterM.Step` 和 `Iter.Step`。
-/
def c007 := @PlausibleIterStep

/--
`yield` 情形的模式。另见 `IterStep.yield`。
-/
def c008 := @PlausibleIterStep.yield

/--
`skip` 情形的模式。另见 `IterStep.skip`。
-/
def c009 := @PlausibleIterStep.skip

/--
`done` 情形的模式。另见 `IterStep.done`。
-/
def c010 := @PlausibleIterStep.done

/--
`Finite α m` 断言 `IterM (α := α) m` 会在有限步后终止。技术上说，这意味着合理后继关系是良基的。
有了此类型类，以迭代器 `it` 进行良基递归时，可以用 `it.finitelyManySteps` 作为终止度量。
-/
class c011 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] : Prop where
  /-- 合理后继关系是良基的。 -/
  wf : WellFounded (@Std.IterM.IsPlausibleSuccessorOf α m β inferInstance)

/--
`Productive α m` 断言 `IterM (α := α) m` 会在有限次跳过后终止或发出一个值。技术上说，这意味着跳过期间的合理后继关系是良基的。
有了此类型类，以迭代器 `it` 进行良基递归时，可以用 `it.finitelyManySkips` 作为终止度量。
-/
class c012 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] : Prop where
  /-- 跳过期间的合理后继关系是良基的。 -/
  wf : WellFounded (@Std.IterM.IsPlausibleSkipSuccessorOf α m β inferInstance)

/--
对于迭代器 `it`，`it.ensureTermination` 提供一定会终止的消费者变体。
-/
def c013 := @Iter.ensureTermination

/--
对于迭代器 `it`，`it.ensureTermination` 提供一定会终止的消费者变体。
-/
def c014 := @IterM.ensureTermination

/--
`IteratorAccess α m` 为支持随机访问的迭代器提供高效实现。`it.nextAtIdx? n` 要么返回 `it` 发出第 `n` 个值的步骤（必为 `.yield _ _` 形式），要么在 `it` 尚未发出第 `n` 个值便终止时返回 `.done`。

对于单子式迭代器，由于 `nextAtIdx?` 可以走捷径，此操作的单子式效应可能不同于手动迭代到第 `n` 个值。由签名保证，返回值在 `IterM.IsPlausibleNthOutputStep` 的意义下是合理的。

此类是实验性的；迭代器 API 的用户不应显式依赖它。
-/
class c015 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- `nextAtIdx? it n` 要么返回 `it` 发出第 `n` 个值的步骤（必为 `.yield _ _` 形式），要么在 `it` 尚未发出第 `n` 个值便终止时返回 `.done`。 -/
  nextAtIdx? : (it : @Std.IterM α m β) → (n : Nat) → m (@Std.PlausibleIterStep (@Std.IterM α m β) β (@Std.IterM.IsPlausibleNthOutputStep α β m inferInstance n it))

/--
返回 `it` 发出第 `n` 个元素的步骤；若它更早终止，则返回 `.done`。与 `step` 不同，此函数一定返回 `.yield` 或 `.done`，绝不会返回 `.skip` 步骤。

对于单子式迭代器，由于 `nextAtIdx?` 可以走捷径，此操作的单子式效应可能不同于手动迭代到第 `n` 个值。由签名保证，返回值在 `IterM.IsPlausibleNthOutputStep` 的意义下是合理的。

此函数仅适用于通过实现 `IteratorAccess` 类型类而显式支持它的迭代器。
-/
def c016 := @IterM.nextAtIdx?

/--
`IteratorLoop α m` 为基于 `α` 的迭代器提供高效的循环式消费者实现，其基础是一个 `ForIn` 风格的循环构造。

对良基循环而言，其行为由 `LawfulIteratorLoop` 类型类完全刻画。

此类是实验性的；迭代器 API 的用户不应显式依赖它。不过，可以假定需要其实例的消费者适用于标准库提供的所有迭代器。
-/
class c017 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β]
    (n : Type u → Type u₁) where
  /-- 按 `for` 循环所期望的方式遍历迭代器 `it`。 -/
  forIn : ((γ : Type w) → (δ : Type u) → (γ → n δ) → m γ → n δ) →
    (γ : Type u) → (plausible : β → γ → ForInStep γ → Prop) →
    (it : @Std.IterM α m β) → γ →
    ((b : β) → @Std.IterM.IsPlausibleIndirectOutput α β m inferInstance it b →
      (c : γ) → n {s : ForInStep γ // plausible b c s}) → n γ

/--
这是 `IteratorLoop` 类的默认实现。
它只是使用 `IterM.step` 遍历迭代器。某些迭代器可以采用更高效的实现，此时应优先使用那些实现。
-/
def c018 := @IteratorLoop.defaultImplementation

/--
断言给定的 `IteratorLoop` 实例等于 `IteratorLoop.defaultImplementation`。
（即使二者相等，给定实例也可能高效得多。）
-/
class c019 {β : Type w} (α : Type w) (m : Type w → Type v) (n : Type u → Type u₁)
    [Monad m] [Monad n] [Std.Iterator α m β] [i : Std.IteratorLoop α m n] : Prop where
  /-- `i` 中 `IteratorLoop.forIn` 的实现等于默认实现。 -/
  lawful lift [Std.Internal.LawfulMonadLiftBindFunction lift] γ it init
      (Pl : β → γ → ForInStep γ → Prop) (wf : Std.IteratorLoop.WellFounded α m Pl)
      (f : (b : β) → @Std.IterM.IsPlausibleIndirectOutput α β m inferInstance it b →
        (c : γ) → n (Subtype (Pl b c))) :
    i.forIn lift γ Pl it init f =
      Std.IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

/--
目前，`Shrink α` 只是 `α` 的包装。

将来，只要有 `α` 实际上很小的证明，`Shrink` 应能把 `α` 缩到可能更小的宇宙，类似 Mathlib 的 `Shrink`，但后者的转换函数不可计算。在此之前，`Shrink α` 始终与 `α` 位于同一宇宙。

这个空操作类型的存在，是为了在真正的 `Shrink` 类型可用、且迭代器在宇宙方面变得更灵活时，减少破坏性变更。

转换函数 `Shrink.deflate` 与 `Shrink.inflate` 在 `α` 和 `Shrink α` 之间构成等价，但此等价刻意不是定义等价。
-/
def c020 := @Std.Shrink

/--
将 `Shrink α` 的元素转换为 `α` 的元素。
-/
def c021 := @Std.Shrink.inflate

/--
将 `α` 的元素转换为 `Shrink α` 的元素。
-/
def c022 := @Std.Shrink.deflate

/--
返回一个立即终止的迭代器。

**终止性质：**

* `Finite` 实例：总是可用
* `Productive` 实例：总是可用
-/
def c023 := @Iter.empty

/--
返回一个立即终止的迭代器。

**终止性质：**

* `Finite` 实例：总是可用
* `Productive` 实例：总是可用
-/
def c024 := @IterM.empty

/--
由初值 `init` 和函数 `f : α → α` 创建一个无限迭代器。它首先发出 `init`；此后每一步都把 `f` 应用于前一个值。因此，若刚刚发出了 `a`，下一步就会发出 `f a`。换言之，第 `n` 个值是 `Nat.repeat f n init`。

例如，若 `f := (· + 1)` 且 `init := 0`，迭代器便按顺序发出所有自然数。

**终止性质：**

* `Finite` 实例：不可用，也绝不可能存在
* `Productive` 实例：总是可用
-/
def c025 := @Iter.repeat

/--
让给定迭代器 `it` 执行一步；这一步可能发出一个值，并提供后继迭代器。若递归使用此函数，有时可用终止度量 `it.finitelyManySteps` 和 `it.finitelyManySkips` 证明终止。
-/
def c026 := @Iter.step

/--
让给定迭代器 `it` 执行一步；这一步可能发出一个值，并提供后继迭代器。若递归使用此函数，有时可用终止度量 `it.finitelyManySteps` 和 `it.finitelyManySkips` 证明终止。
-/
def c027 := @IterM.step

/--
在对有限迭代器进行良基递归的函数中使用的终止度量（另见 `Finite`）。
-/
def c028 := @Iter.finitelyManySteps

/--
在对有限迭代器进行良基递归的函数中使用的终止度量（另见 `Finite`）。
-/
def c029 := @IterM.finitelyManySteps

/--
此类型包装 `IterM`，使其可用作有限迭代器递归的终止度量。另见 `IterM.finitelyManySteps` 和 `Iter.finitelyManySteps`。
-/
structure c030 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- 被包装的迭代器。

在此包装中，它的有限性被用作终止度量。 -/
  it : @Std.IterM α m β

/--
在对能产迭代器进行良基递归的函数中使用的终止度量（另见 `Productive`）。
-/
def c031 := @Iter.finitelyManySkips

/--
在对能产迭代器进行良基递归的函数中使用的终止度量（另见 `Productive`）。
-/
def c032 := @IterM.finitelyManySkips

/--
此类型包装 `IterM`，使其可用作能产迭代器递归的终止度量。另见 `IterM.finitelyManySkips` 和 `Iter.finitelyManySkips`。
-/
structure c033 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- 被包装的迭代器。

在此包装中，它的能产性被用作终止度量。 -/
  it : @Std.IterM α m β

/--
从左侧用函数折叠迭代器，从 `init` 开始累积值。按顺序使用 `f` 将累积值与列表中的每个元素结合。

它等价于 `it.toList.foldl`。
-/
def c034 := @Iter.fold

/--
从左侧用单子式函数折叠迭代器，从 `init` 开始累积值。按顺序使用 `f` 将累积值与列表中的每个元素结合。

它等价于 `it.toList.foldlM`。
-/
def c035 := @Iter.foldM

/--
逐步遍历整个迭代器，并统计发出的输出数。

**性能**：

此函数的运行时间与迭代器执行的步骤数呈线性关系。
-/
def c036 := @Iter.length

/--
若纯谓词 `p` 对迭代器 `it` 发出的任一元素返回 `true`，则返回 `true`。

`O(|xs|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c037 := @Iter.any

/--
若单子式谓词 `p` 对迭代器 `it` 发出的任一元素返回 `true`，则返回 `true`。

`O(|xs|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c038 := @Iter.anyM

/--
若纯谓词 `p` 对迭代器 `it` 发出的所有元素返回 `true`，则返回 `true`。

`O(|xs|)`。遇到第一个不匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c039 := @Iter.all

/--
若单子式谓词 `p` 对迭代器 `it` 发出的所有元素返回 `true`，则返回 `true`。

`O(|xs|)`。遇到第一个不匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c040 := @Iter.allM

/--
返回迭代器中第一个使谓词 `p` 返回 `true` 的输出；若找不到这样的输出，则返回 `none`。

`O(|it|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 中的元素。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.find?` 总会在有限步后终止。

示例：
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 1) = none`
-/
def c041 := @Iter.find?

/--
返回迭代器中第一个使单子式谓词 `p` 返回 `true` 的输出；若找不到这样的元素，则返回 `none`。

`O(|it|)`。当 `f` 返回 `true` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findM?` 总会在有限步后终止。

示例：
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
def c042 := @Iter.findM?

/--
按顺序将 `f` 应用于迭代器的每个输出，并返回第一个非 `none` 的结果。若 `f` 对所有输出都返回 `none`，则返回 `none`。

`O(|it|)`。当 `f` 返回 `some _` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findSome?` 总会在有限步后终止。

示例：
 * `[7, 6, 5, 8, 1, 2, 6].iter.findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].iter.findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
def c043 := @Iter.findSome?

/--
按顺序将单子式函数 `f` 应用于迭代器的每个输出，并返回第一个非 `none` 的结果。若 `f` 对所有输出都返回 `none`，则返回 `none`。

`O(|it|)`。当 `f` 返回 `some _` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findSomeM?` 总会在有限步后终止。

示例：
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
def c044 := @Iter.findSomeM?

/--
返回 `it` 发出的第 `n` 个值；若 `it` 更早终止，则返回 `none`。

对于单子式迭代器，由于 `atIdx?` 可以走捷径，此操作的单子式效应可能不同于手动迭代到第 `n` 个值。由签名保证，返回值在 `IterM.IsPlausibleNthOutputStep` 的意义下是合理的。

此函数仅适用于通过实现 `IteratorAccess` 类型类而显式支持它的迭代器。
-/
def c045 := @Iter.atIdx?

/--
若可能，令迭代器 `it` 执行 `n` 步，并返回发出的第 `n` 个值；若 `it` 在发出 `n` 个值之前结束，则返回 `none`。

若迭代器不能产，此函数可能陷入无休止的迭代步骤循环。变体 `it.ensureTermination.atIdxSlow?` 保证在有限步后终止。
-/
def c046 := @Iter.atIdxSlow?

/--
遍历整个迭代器，执行每一步的单子式效应，并丢弃所有发出的值。
-/
def c047 := @IterM.drain

/--
从左侧用函数折叠迭代器，从 `init` 开始累积值。按顺序使用 `f` 将累积值与列表中的每个元素结合。

它等价于 `it.toList.foldl`。
-/
def c048 := @IterM.fold

/--
从左侧用单子式函数折叠迭代器，从 `init` 开始累积值。按顺序使用 `f` 将累积值与列表中的每个元素结合。

`f` 的单子式效应与迭代器步进函数可能产生的效应交错。因此，它*不一定*等价于 `(← it.toList).foldlM`。
-/
def c049 := @IterM.foldM

/--
逐步遍历整个迭代器，并统计发出的输出数。

**性能**：

此函数的运行时间与迭代器执行的步骤数呈线性关系。
-/
def c050 := @IterM.length

/--
若纯谓词 `p` 对迭代器 `it` 发出的任一元素返回 `true`，则返回 `ULift.up true`。

`O(|it|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 的输出。
-/
def c051 := @IterM.any

/--
若单子式谓词 `p` 对迭代器 `it` 发出的任一元素返回 `ULift.up true`，则返回 `ULift.up true`。

`O(|it|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c052 := @IterM.anyM

/--
若纯谓词 `p` 对迭代器 `it` 发出的所有元素返回 `true`，则返回 `ULift.up true`。

`O(|it|)`。遇到第一个不匹配项即短路。按迭代顺序检查 `it` 中的元素。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toListRev` 总会在有限步后终止。
-/
def c053 := @IterM.all

/--
若单子式谓词 `p` 对迭代器 `it` 发出的所有元素返回 `ULift.up true`，则返回 `ULift.up true`。

`O(|it|)`。遇到第一个不匹配项即短路。按迭代顺序检查 `it` 中的元素。
-/
def c054 := @IterM.allM

/--
返回迭代器中第一个使谓词 `p` 返回 `true` 的输出；若找不到这样的输出，则返回 `none`。

`O(|it|)`。遇到第一个匹配项即短路。按迭代顺序检查 `it` 中的元素。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.find?` 总会在有限步后终止。

示例：
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 5) = pure (some 1)`
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 1) = pure none`
-/
def c055 := @IterM.find?

/--
返回迭代器中第一个使单子式谓词 `p` 返回 `true` 的输出；若找不到这样的元素，则返回 `none`。

`O(|it|)`。当 `f` 返回 `true` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findM?` 总会在有限步后终止。

示例：
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
def c056 := @IterM.findM?

/--
按顺序将 `f` 应用于迭代器的每个输出，并返回第一个非 `none` 的结果。若 `f` 对所有输出都返回 `none`，则返回 `none`。

`O(|it|)`。当 `f` 返回 `some _` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findSome?` 总会在有限步后终止。

示例：
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).findSome? (fun x => if x < 5 then some (10 * x) else none) = pure (some 10)`
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).findSome? (fun x => if x < 1 then some (10 * x) else none) = pure none`
-/
def c057 := @IterM.findSome?

/--
按顺序将单子式函数 `f` 应用于迭代器的每个输出，并返回第一个非 `none` 的结果。若 `f` 对所有输出都返回 `none`，则返回 `none`。

`O(|it|)`。当 `f` 返回 `some _` 时短路。按迭代顺序检查 `it` 的输出。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.findSomeM?` 总会在有限步后终止。

示例：
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
def c058 := @IterM.findSomeM?

/--
返回 `it` 发出的第 `n` 个值；若 `it` 更早终止，则返回 `none`。

对于单子式迭代器，由于 `atIdx?` 可以走捷径，此操作的单子式效应可能不同于手动迭代到第 `n` 个值。由签名保证，返回值在 `IterM.IsPlausibleNthOutputStep` 的意义下是合理的。

此函数仅适用于通过实现 `IteratorAccess` 类型类而显式支持它的迭代器。
-/
def c059 := @IterM.atIdx?

/--
遍历给定迭代器，并把发出的值存入数组。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toArray` 总会在有限步后终止。
-/
def c060 := @Iter.toArray

/--
遍历给定迭代器，并把发出的值存入数组。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toArray` 总会在有限步后终止。
-/
def c061 := @IterM.toArray

/--
遍历给定迭代器，并把发出的值存入列表。由于列表只能在头部添加元素，`toListRev` 通常比 `toList` 更高效。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toList` 总会在有限步后终止。
-/
def c062 := @Iter.toList

/--
遍历给定迭代器，并把发出的值存入列表。由于列表只能在头部添加元素，`toListRev` 通常比 `toList` 更高效。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toList` 总会在有限步后终止。
-/
def c063 := @IterM.toList

/--
遍历给定迭代器，并按逆序把发出的值存入列表。由于列表只能在头部添加元素，`toListRev` 通常比 `toList` 更高效。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toListRev` 总会在有限步后终止。
-/
def c064 := @Iter.toListRev

/--
遍历给定迭代器，并按逆序把发出的值存入列表。由于列表只能在头部添加元素，`toListRev` 通常比 `toList` 更高效。

若迭代器不是有限的，此函数可能永远运行。变体 `it.ensureTermination.toListRev` 总会在有限步后终止。
-/
def c065 := @IterM.toListRev

/--
将迭代器的状态包装成 `Iter` 对象。
-/
def c066 := @IterM.mk

/--
把纯迭代器（`Iter β`）转换为恒等单子 `Id` 中的单子式迭代器（`IterM Id β`）。
-/
def c067 := @Iter.toIterM

/--
给定迭代器 `it` 和自然数 `n`，`it.take n` 会按顺序输出 `it` 最前面的至多 `n` 个值，然后终止。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 能产时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

`it` 每发出一个值，此组合子都会引入额外 O(1) 开销。
-/
def c068 := @Iter.take

/--
给定迭代器 `it` 和谓词 `P`，`it.takeWhile P` 会输出 `it` 发出的值，直到其中一个值被 `P` 拒绝。若某个发出的值被 `P` 拒绝，该值会被丢弃，迭代器随即终止。

**弹珠图：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it               ---a----b---c--d-e--⊥
it.takeWhile P   ---a----b---⊥

it               ---a----⊥
it.takeWhile P   ---a----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.takeWhile P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假，随后终止。
-/
def c069 := @Iter.takeWhile

/--
此组合子只适用于高级用例。

给定有限迭代器 `it`，返回一个行为与 `it` 完全相同、但类型与 `it.take n` 相同的迭代器。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.toTake   ---a----b---c--d-e--⊥
```

**终止性质：**

* `Finite` 实例：总是可用
* `Productive` 实例：总是可用

**性能：**

`it` 每发出一个值，此组合子都会引入额外 O(1) 开销。
-/
def c070 := @Iter.toTake

/--
给定迭代器 `it` 和自然数 `n`，`it.drop n` 会转发 `it` 除前 `n` 个之外的所有输出值。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.drop 3   ---------------d-e--⊥

it          ---a--⊥
it.drop 3   ------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

目前，即使迭代器已不再丢弃任何元素，`it` 每发出一个值，此组合子仍会引入额外 O(1) 开销。
-/
def c071 := @Iter.drop

/--
给定迭代器 `it` 和谓词 `P`，`it.dropWhile P` 会从第一个被 `P` 拒绝的值开始，发出 `it` 所发出的值；此前的元素都被丢弃。

若 `P` 是单子式的，请改用 `dropWhileM`。

**弹珠图：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it               ---a----b---c--d-e--⊥
it.dropWhile P   ------------c--d-e--⊥

it               ---a----⊥
it.dropWhile P   --------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

视 `P` 而定，即使 `it` 不能产，`it.dropWhileM P` 也可能能产。此时需要手动证明 `Productive` 实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假。此后，`it` 每发出一个值，组合子都会引入额外 O(1) 开销。
-/
def c072 := @Iter.dropWhile

/--
生成一个迭代器：先发出 `it` 的一个值，再丢弃 `n - 1` 个元素，然后再发出一个值，如此继续。换言之，它从第一个值开始，每隔 `n` 个值发出一个 `it` 的值。

若 `n = 0`，迭代器的行为与 `n = 1` 时相同：发出 `it` 的所有值。


**弹珠图：**

```
it               ---1----2----3---4----5
it.stepSize 2    ---1---------3--------5
```

**可用性：**

此操作目前仅适用于实现 `IteratorAccess` 的迭代器，例如 `PRange.iter` 范围迭代器。

**终止性质：**

* `Finite` 实例：仅当基础迭代器 `it` 有限时可用
* `Productive` 实例：总是可用
-/
def c073 := @Iter.stepSize

/--
若 `it` 是迭代器，则 `it.map f` 是另一个迭代器：它把函数 `f` 应用于 `it` 发出的所有值，并发出结果。

若 `f` 是单子式的，请改用 `mapM`。

**弹珠图：**

```text
it         ---a --b --c --d -e ----⊥
it.map     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = a'`、`f b = b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c074 := @Iter.map

/--
若 `it` 是迭代器，则 `it.mapM f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值，并发出结果。

基础迭代器 `it` 位于单子 `m` 中；只要有 `MonadLiftT m n` 实例，`f` 就可在任意单子 `n` 中返回值。

若 `f` 是纯函数，可改用更简单的 `it.map`。

**弹珠图（忽略单子式效应）：**

```text
it          ---a --b --c --d -e ----⊥
it.mapM     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = pure a'`、`f b = pure b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.mapM` 也会有限。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c075 := @Iter.mapM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `map` 与 `mapM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.mapWithPostcondition f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值，并发出结果。

`f` 应返回 `PostconditionT n _`，其中 `n` 是任意单子。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                          ---a --b --c --d -e ----⊥
it.mapWithPostcondition     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = pure a'`、`f b = pure b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.mapWithPostcondition` 也会有限。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。在上述例子中，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c076 := @Iter.mapWithPostcondition

/--
把值位于 `β` 的迭代器转换为值位于 `ULift β` 的迭代器。

`map` 等多数其他组合子无法跨越宇宙层级；此组合子可用于过渡到更高宇宙。

**弹珠图：**

```
it            ---a    ----b    ---c    --d    ---⊥
it.uLift n    ---.up a----.up b---.up c--.up d---⊥
```

**终止性质：**

* `Finite`：仅当原迭代器有限时可用
* `Productive`：仅当原迭代器能产时可用
-/
def c077 := @Iter.uLift

/--
设 `it` 为迭代器，`f` 为把 `it` 的输出映射到迭代器的函数。`it.flatMap f` 遍历 `it`，对每个输出应用 `f`，再遍历所得迭代器。`it.flatMap f` 会发出内部迭代器得到的全部值：先发出第一个内部迭代器的所有值，再发出第二个的所有值，依此类推。

**弹珠图：**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMap         ----a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it` 有限且内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c078 := @Iter.flatMap

/--
设 `it` 为迭代器，`f` 为单子式的、把 `it` 的输出映射到迭代器的函数。`it.flatMapM f` 遍历 `it`，对每个输出应用 `f`，再遍历所得迭代器。`it.flatMapM f` 会发出内部迭代器得到的全部值：先发出第一个内部迭代器的所有值，再发出第二个的所有值，依此类推。

**弹珠图（忽略单子式效应）：**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMapM        ----a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it` 有限且内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c079 := @Iter.flatMapM

/--
设 `it₁` 和 `it₂` 为迭代器，`f` 为把 `it₁` 的输出映射到与 `it₂` 同类型迭代器的函数。`it₁.flatMapAfter f it₂` 先遍历 `it₂`，然后遍历 `it₁.flatMap f it₂`，并发出二者的全部值。

此组合子的主要用途，是表示一个 `flatMap` 迭代器正在遍历某个内部迭代器时的中间状态。

**弹珠图：**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfter  f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it₁`、`it₂` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it₁` 有限，且 `it₂` 和内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it₁`、`it₂` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it₁` 每发出一个值，此组合子都会调用 `f`。
-/
def c080 := @Iter.flatMapAfter

/--
设 `it₁` 和 `it₂` 为迭代器，`f` 为单子式的、把 `it₁` 的输出映射到与 `it₂` 同类型迭代器的函数。`it₁.flatMapAfterM f it₂` 先遍历 `it₂`，然后遍历 `it₁.flatMap f it₂`，并发出二者的全部值。

此组合子的主要用途，是表示一个 `flatMap` 迭代器正在遍历某个内部迭代器时的中间状态。

**弹珠图（忽略单子式效应）：**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfterM f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it₁`、`it₂` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it₁` 有限，且 `it₂` 和内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it₁`、`it₂` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it₁` 每发出一个值，此组合子都会调用 `f`。
-/
def c081 := @Iter.flatMapAfterM

/--
若 `it` 是迭代器，则 `it.filter f` 是另一个迭代器：它把谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

若 `f` 是单子式的，请改用 `filterM`。

**弹珠图（忽略单子式效应）：**

```text
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```

（其中 `f a = f c = true`，且 `f b = f d = d e = false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Productive` 实例，所得迭代器仍会能产。例如，若 `f` 总是返回 `True`，则只要 `it` 能产，所得迭代器也能产。此时需要手动证明缺失的实例。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回值进行模式匹配。
-/
def c082 := @Iter.filter

/--
若 `it` 是迭代器，则 `it.filterM f` 是另一个迭代器：它把单子式谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

若 `f` 是纯函数，可改用更简单的 `it.filter`。

**弹珠图（忽略单子式效应）：**

```text
it             ---a--b--c--d-e--⊥
it.filterM     ---a-----c-------⊥
```

（其中 `f a = f c = pure true`，且 `f b = f d = d e = pure false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterWithPostcondition` 也会有限并且能产。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c083 := @Iter.filterM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `filter` 与 `filterM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.filterWithPostcondition f` 是另一个迭代器：它把单子式谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

`f` 应返回 `PostconditionT n (ULift Bool)`，其中 `n` 是任意单子。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                             ---a--b--c--d-e--⊥
it.filterWithPostcondition     ---a-----c-------⊥
```

（其中 `f a = f c = pure true`，且 `f b = f d = d e = pure false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterWithPostcondition` 也会有限并且能产。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。在上述例子中，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c084 := @Iter.filterWithPostcondition

/--
若 `it` 是迭代器，则 `it.filterMap f` 是另一个迭代器：它把函数 `f` 应用于 `it` 发出的所有值。`f` 应返回一个 `Option`。若返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

若 `f` 是单子式的，请改用 `filterMapM`。

**弹珠图：**

```text
it               ---a --b--c --d-e--⊥
it.filterMap     ---a'-----c'-------⊥
```

（其中 `f a = some a'`、`f c = c'`，且 `f b = f d = d e = none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Productive` 实例，所得迭代器仍会能产。例如，若 `f` 从不返回 `none`，此组合子便会保持能产性。此时需要手动证明缺失的实例。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c085 := @Iter.filterMap

/--
若 `it` 是迭代器，则 `it.filterMapM f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值。`f` 应返回单子中的 `Option`。若 `f` 返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

若 `f` 是纯函数，可改用更简单的 `it.filterMap`。

**弹珠图（忽略单子式效应）：**

```text
it                ---a --b--c --d-e--⊥
it.filterMapM     ---a'-----c'-------⊥
```

（其中 `f a = pure (some a)'`、`f c = pure (some c')`，且 `f b = f d = d e = pure none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 从不返回 `none`，此组合子便保持能产性；若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterMapM` 也会有限。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c086 := @Iter.filterMapM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `filterMap` 与 `filterMapM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.filterMapWithPostcondition f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值。`f` 应在单子中返回一个 `Option`。若 `f` 返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

`f` 应返回 `PostconditionT n (Option _)`，其中 `n` 是任意单子。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                                ---a --b--c --d-e--⊥
it.filterMapWithPostcondition     ---a'-----c'-------⊥
```

（其中 `f a = pure (some a')`、`f c = pure (some c')`，且 `f b = f d = d e = pure none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 从不返回 `none`，此组合子便保持能产性；若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterMapWithPostcondition` 也会有限。前一种情况下，可以考虑改用开箱即提供更多实例的 `map`/`mapM`/`mapWithPostcondition` 组合子。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。若 `f` 总是返回 `some _`，合适的后置条件是 `fun x => x.isSome`；若 `f` 总会失败，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c087 := @Iter.filterMapWithPostcondition

/--
给定两个迭代器 `left` 和 `right`，`left.zip right` 会发出 `left` 与 `right` 输出值组成的配对。当其中一个终止时，`zip` 迭代器也会终止。

**弹珠图：**

```text
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `left` 或 `right` 中一个有限、另一个能产时可用
* `Productive` 实例：仅当 `left` 与 `right` 都能产时可用

有时 `left.zip right` 虽然有限（或能产），上述实例却都不适用。例如，若 `left` 立即终止而 `right` 始终跳过，则 `left.zip.right` 有限，却没有可用的 `Finite`（甚至 `Productive`）实例。此类实例需要手动证明。

**性能：**

`left` 或 `right` 每执行一步，此组合子都会引入额外 O(1) 开销。

目前编译器不会拆箱内部状态，因此性能不如理论上所能达到的水平。
-/
def c088 := @Iter.zip

/--
为满足谓词 `P` 的值组成的迭代器逐个“附加”证明，返回值位于相应子类型 `{ x // P x }` 中的迭代器。

**终止性质：**

* `Finite` 实例：仅当基础迭代器有限时可用
* `Productive` 实例：仅当基础迭代器能产时可用
-/
def c089 := @Iter.attachWith

/--
把 `Id` 上的单子式迭代器（`IterM Id β`）转换为纯迭代器（`Iter β`）。
-/
def c090 := @IterM.toIter

/--
给定迭代器 `it` 和自然数 `n`，`it.take n` 会按顺序输出 `it` 最前面的至多 `n` 个值，然后终止。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 能产时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

`it` 每发出一个值，此组合子都会引入额外 O(1) 开销。
-/
def c091 := @IterM.take

/--
给定迭代器 `it` 和谓词 `P`，`it.takeWhile P` 会输出 `it` 发出的值，直到其中一个值被 `P` 拒绝。若某个发出的值被 `P` 拒绝，该值会被丢弃，迭代器随即终止。

若 `P` 是单子式的，请改用 `takeWhileM`。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it               ---a----b---c--d-e--⊥
it.takeWhile P   ---a----b---⊥

it               ---a----⊥
it.takeWhile P   ---a----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.takeWhile P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假，随后终止。
-/
def c092 := @IterM.takeWhile

/--
给定迭代器 `it` 和单子式谓词 `P`，`it.takeWhileM P` 会输出 `it` 发出的值，直到其中一个值被 `P` 拒绝。若某个发出的值被 `P` 拒绝，该值会被丢弃，迭代器随即终止。

若 `P` 是纯谓词，可改用更简单的 `takeWhile`。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it                ---a----b---c--d-e--⊥
it.takeWhileM P   ---a----b---⊥

it                ---a----⊥
it.takeWhileM P   ---a----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.takeWhileM P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假，随后终止。
-/
def c093 := @IterM.takeWhileM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `takeWhile` 与 `takeWhileM` 更易使用，足以满足大多数用例。*

给定迭代器 `it` 和单子式谓词 `P`，`it.takeWhileWithPostcondition P` 会输出 `it` 发出的值，直到其中一个值被 `P` 拒绝。若某个发出的值被 `P` 拒绝，该值会被丢弃，迭代器随即终止。

`P` 应返回 `PostconditionT m (ULift Bool)`。`PostconditionT` 变换器让调用者能在单子 `m` 中内蕴地证明关于 `P` 返回值的性质，从而可以依据 `P` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it                                ---a----b---c--d-e--⊥
it.takeWhileWithPostcondition P   ---a----b---⊥

it                                ---a----⊥
it.takeWhileWithPostcondition P   ---a----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.takeWhileWithPostcondition P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假，随后终止。
-/
def c094 := @IterM.takeWhileWithPostcondition

/--
此组合子只适用于高级用例。

给定有限迭代器 `it`，返回一个行为与 `it` 完全相同、但类型与 `it.take n` 相同的迭代器。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.toTake   ---a----b---c--d-e--⊥
```

**终止性质：**

* `Finite` 实例：总是可用
* `Productive` 实例：总是可用

**性能：**

`it` 每发出一个值，此组合子都会引入额外 O(1) 开销。
-/
def c095 := @IterM.toTake

/--
给定迭代器 `it` 和自然数 `n`，`it.drop n` 会转发 `it` 除前 `n` 个之外的所有输出值。

**弹珠图：**

```text
it          ---a----b---c--d-e--⊥
it.drop 3   ---------------d-e--⊥

it          ---a--⊥
it.drop 3   ------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

目前，即使迭代器已不再丢弃任何元素，`it` 每发出一个值，此组合子仍会引入额外 O(1) 开销。
-/
def c096 := @IterM.drop

/--
给定迭代器 `it` 和谓词 `P`，`it.dropWhile P` 会从第一个被 `P` 拒绝的值开始，发出 `it` 所发出的值；此前的元素都被丢弃。

若 `P` 是单子式的，请改用 `dropWhileM`。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it               ---a----b---c--d-e--⊥
it.dropWhile P   ------------c--d-e--⊥

it               ---a----⊥
it.dropWhile P   --------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假。此后，`it` 每发出一个值，组合子都会引入额外 O(1) 开销。
-/
def c097 := @IterM.dropWhile

/--
给定迭代器 `it` 和单子式谓词 `P`，`it.dropWhileM P` 会从第一个被 `P` 拒绝的值开始，发出 `it` 所发出的值；此前的元素都被丢弃。

若 `P` 是纯谓词，可改用更简单的 `dropWhile`。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it                ---a----b---c--d-e--⊥
it.dropWhileM P   ------------c--d-e--⊥

it                ---a----⊥
it.dropWhileM P   --------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.dropWhileM P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假。此后，`it` 每发出一个值，组合子都会引入额外 O(1) 开销。
-/
def c098 := @IterM.dropWhileM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `dropWhile` 与 `dropWhileM` 更易使用，足以满足大多数用例。*

给定迭代器 `it` 和单子式谓词 `P`，`it.dropWhileWithPostcondition P` 会从第一个被 `P` 拒绝的值开始，发出 `it` 所发出的值；此前的元素都被丢弃。

`P` 应返回 `PostconditionT m (ULift Bool)`。`PostconditionT` 变换器让调用者能在单子 `m` 中内蕴地证明关于 `P` 返回值的性质，从而可以依据 `P` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

假设谓词 `P` 接受 `a` 和 `b`，但拒绝 `c`：

```text
it                                ---a----b---c--d-e--⊥
it.dropWhileWithPostcondition P   ------------c--d-e--⊥

it                                ---a----⊥
it.dropWhileWithPostcondition P   --------⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

视 `P` 而定，即使 `it` 并非有限（或能产），`it.dropWhileWithPostcondition P` 也可能有限（或能产）。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

此组合子对 `it` 的每个输出调用 `P`，直到谓词求值为假。此后，`it` 每发出一个值，组合子都会引入额外 O(1) 开销。
-/
def c099 := @IterM.dropWhileWithPostcondition

/--
生成一个迭代器：先发出 `it` 的一个值，再丢弃 `n - 1` 个元素，然后再发出一个值，如此继续。换言之，它从第一个值开始，每隔 `n` 个值发出一个 `it` 的值。

若 `n = 0`，迭代器的行为与 `n = 1` 时相同：发出 `it` 的所有值。


**弹珠图：**

```
it               ---1----2----3---4----5
it.stepSize 2    ---1---------3--------5
```

**可用性：**

此操作目前仅适用于实现 `IteratorAccess` 的迭代器，例如 `PRange.iter` 范围迭代器。

**终止性质：**

* `Finite` 实例：仅当基础迭代器 `it` 有限时可用
* `Productive` 实例：总是可用
-/
def c100 := @IterM.stepSize

/--
若 `it` 是迭代器，则 `it.map f` 是另一个迭代器：它把函数 `f` 应用于 `it` 发出的所有值，并发出结果。

若 `f` 是单子式的，请改用 `mapM`。

**弹珠图：**

```text
it         ---a --b --c --d -e ----⊥
it.map     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = a'`、`f b = b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c101 := @IterM.map

/--
若 `it` 是迭代器，则 `it.mapM f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值，并发出结果。

基础迭代器 `it` 位于单子 `m` 中；只要有 `MonadLiftT m n` 实例，`f` 就可在任意单子 `n` 中返回值。

若 `f` 是纯函数，可改用更简单的 `it.map`。

**弹珠图（忽略单子式效应）：**

```text
it          ---a --b --c --d -e ----⊥
it.mapM     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = pure a'`、`f b = pure b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.mapM` 也会有限。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c102 := @IterM.mapM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `map` 与 `mapM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.mapWithPostcondition f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值，并发出结果。

`f` 应返回 `PostconditionT n _`，基础迭代器 `it` 位于单子 `m` 中；`n` 可以不同于 `m`，但 `it.mapWithPostcondition f` 要求有 `MonadLiftT m n` 实例。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                          ---a --b --c --d -e ----⊥
it.mapWithPostcondition     ---a'--b'--c'--d'-e'----⊥
```

（其中 `f a = pure a'`、`f b = pure b'`，依此类推。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 能产时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.mapWithPostcondition` 也会有限。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。在上述例子中，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c103 := @IterM.mapWithPostcondition

/--
把在单子 `m` 中运行且值位于 `β` 的迭代器，转换为在单子 `n` 中运行且值位于 `ULift β` 的迭代器。要求有 `MonadLift m (ULiftT n)` 实例。

**弹珠图：**

```
it            ---a    ----b    ---c    --d    ---⊥
it.uLift n    ---.up a----.up b---.up c--.up d---⊥
```

**终止性质：**

* `Finite`：仅当原迭代器有限时可用
* `Productive`：仅当原迭代器能产时可用
-/
def c104 := @IterM.uLift

/--
设 `it` 为迭代器，`f` 为把 `it` 的输出映射到迭代器的函数。`it.flatMap f` 遍历 `it`，对每个输出应用 `f`，再遍历所得迭代器。`it.flatMap f` 会发出内部迭代器得到的全部值：先发出第一个内部迭代器的所有值，再发出第二个的所有值，依此类推。

**弹珠图：**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMap         ----a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it` 有限且内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c105 := @IterM.flatMap

/--
设 `it` 为迭代器，`f` 为单子式的、把 `it` 的输出映射到迭代器的函数。`it.flatMapM f` 遍历 `it`，对每个输出应用 `f`，再遍历所得迭代器。`it.flatMapM f` 会发出内部迭代器得到的全部值：先发出第一个内部迭代器的所有值，再发出第二个的所有值，依此类推。

**弹珠图（忽略单子式效应）：**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMapM        ----a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it` 有限且内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c106 := @IterM.flatMapM

/--
设 `it₁` 和 `it₂` 为迭代器，`f` 为把 `it₁` 的输出映射到与 `it₂` 同类型迭代器的函数。`it₁.flatMapAfter f it₂` 先遍历 `it₂`，然后遍历 `it₁.flatMap f it₂`，并发出二者的全部值。

此组合子的主要用途，是表示一个 `flatMap` 迭代器正在遍历某个内部迭代器时的中间状态。

**弹珠图：**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfter  f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it₁`、`it₂` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it₁` 有限，且 `it₂` 和内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it₁`、`it₂` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it₁` 每发出一个值，此组合子都会调用 `f`。
-/
def c107 := @IterM.flatMapAfter

/--
设 `it₁` 和 `it₂` 为迭代器，`f` 为单子式的、把 `it₁` 的输出映射到与 `it₂` 同类型迭代器的函数。`it₁.flatMapAfterM f it₂` 先遍历 `it₂`，然后遍历 `it₁.flatMap f it₂`，并发出二者的全部值。

此组合子的主要用途，是表示一个 `flatMap` 迭代器正在遍历某个内部迭代器时的中间状态。

**弹珠图（忽略单子式效应）：**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfterM f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `it₁`、`it₂` 和内部迭代器都有限时可用
* `Productive` 实例：仅当 `it₁` 有限，且 `it₂` 和内部迭代器能产时可用

对某些函数 `f`，即使没有现成的 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若外部迭代器能产，且内部迭代器能产并且*可证明绝不为空*，则所得迭代器也能产。

**性能：**

`it₁`、`it₂` 或内部迭代器每发出一个值，此组合子都会引入额外 O(1) 开销。

外部迭代器 `it₁` 每发出一个值，此组合子都会调用 `f`。
-/
def c108 := @IterM.flatMapAfterM

/--
若 `it` 是迭代器，则 `it.filter f` 是另一个迭代器：它把谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

若 `f` 是单子式的，请改用 `filterM`。

**弹珠图（忽略单子式效应）：**

```text
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```

（其中 `f a = f c = true`，且 `f b = f d = d e = false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Productive` 实例，所得迭代器仍会能产。例如，若 `f` 总是返回 `True`，则只要 `it` 能产，所得迭代器也能产。此时需要手动证明缺失的实例。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回值进行模式匹配。
-/
def c109 := @IterM.filter

/--
若 `it` 是迭代器，则 `it.filterM f` 是另一个迭代器：它把单子式谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

基础迭代器 `it` 位于单子 `m` 中；只要有 `MonadLiftT m n` 实例，`f` 就可在任意单子 `n` 中返回值。

若 `f` 是纯函数，可改用更简单的 `it.filter`。

**弹珠图（忽略单子式效应）：**

```text
it             ---a--b--c--d-e--⊥
it.filterM     ---a-----c-------⊥
```

（其中 `f a = f c = pure true`，且 `f b = f d = d e = pure false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterWithPostcondition` 也会有限并且能产。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c110 := @IterM.filterM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `filter` 与 `filterM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.filterWithPostcondition f` 是另一个迭代器：它把单子式谓词 `f` 应用于 `it` 发出的所有值，并且只发出被 `f` 接受的值。

`f` 应返回 `PostconditionT n (ULift Bool)`，基础迭代器 `it` 位于单子 `m` 中；`n` 可以不同于 `m`，但 `it.filterWithPostcondition f` 要求有 `MonadLiftT m n` 实例。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                             ---a--b--c--d-e--⊥
it.filterWithPostcondition     ---a-----c-------⊥
```

（其中 `f a = f c = pure true`，且 `f b = f d = d e = pure false`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterWithPostcondition` 也会有限并且能产。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。在上述例子中，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`。
-/
def c111 := @IterM.filterWithPostcondition

/--
若 `it` 是迭代器，则 `it.filterMap f` 是另一个迭代器：它把函数 `f` 应用于 `it` 发出的所有值。`f` 应返回一个 `Option`。若返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

若 `f` 是单子式的，请改用 `filterMapM`。

**弹珠图：**

```text
it               ---a --b--c --d-e--⊥
it.filterMap     ---a'-----c'-------⊥
```

（其中 `f a = some a'`、`f c = c'`，且 `f b = f d = d e = none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Productive` 实例，所得迭代器仍会能产。例如，若 `f` 从不返回 `none`，此组合子便会保持能产性。此时需要手动证明缺失的实例。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c112 := @IterM.filterMap

/--
若 `it` 是迭代器，则 `it.filterMapM f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值。`f` 应返回单子中的 `Option`。若 `f` 返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

基础迭代器 `it` 位于单子 `m` 中；只要有 `MonadLiftT m n` 实例，`f` 就可在任意单子 `n` 中返回值。

若 `f` 是纯函数，可改用更简单的 `it.filterMap`。

**弹珠图（忽略单子式效应）：**

```text
it                ---a --b--c --d-e--⊥
it.filterMapM     ---a'-----c'-------⊥
```

（其中 `f a = pure (some a)'`、`f c = pure (some c')`，且 `f b = f d = d e = pure none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 从不返回 `none`，此组合子便保持能产性；若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterMapM` 也会有限。此时需要手动完成终止性证明。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c113 := @IterM.filterMapM

/--
*注意：这是一个非常通用的组合子，需要深入理解单子、依赖类型和终止性证明。变体 `filterMap` 与 `filterMapM` 更易使用，足以满足大多数用例。*

若 `it` 是迭代器，则 `it.filterMapWithPostcondition f` 是另一个迭代器：它把单子式函数 `f` 应用于 `it` 发出的所有值。`f` 应在单子中返回一个 `Option`。若 `f` 返回 `none`，则不发出任何值；若返回 `some x`，则发出 `x`。

`f` 应返回 `PostconditionT n (Option _)`，基础迭代器 `it` 位于单子 `m` 中；`n` 可以不同于 `m`，但 `it.filterMapWithPostcondition f` 要求有 `MonadLiftT m n` 实例。`PostconditionT` 变换器让调用者能在单子 `n` 中内蕴地证明关于 `f` 返回值的性质，从而可以依据 `f` 的具体行为证明终止。

**弹珠图（忽略单子式效应）：**

```text
it                                ---a --b--c --d-e--⊥
it.filterMapWithPostcondition     ---a'-----c'-------⊥
```

（其中 `f a = pure (some a)'`、`f c = pure (some c')`，且 `f b = f d = d e = pure none`。）

**终止性质：**

* `Finite` 实例：仅当 `it` 有限时可用
* `Productive` 实例：仅当 `it` 有限时可用

对某些映射函数 `f`，即使没有提供 `Finite`（或 `Productive`）实例，所得迭代器仍会有限（或能产）。例如，若 `f` 从不返回 `none`，此组合子便保持能产性；若 `f` 位于 `ExceptT` 单子中且总会失败，则即使 `it` 不有限，`it.filterMapWithPostcondition` 也会有限。前一种情况下，可以考虑改用开箱即提供更多实例的 `map`/`mapM`/`mapWithPostcondition` 组合子。

在这种情况下，只要 `PostconditionT n` 单子中携带的后置条件足够强，就能手动证明缺失的实例。若 `f` 总是返回 `some _`，合适的后置条件是 `fun x => x.isSome`；若 `f` 总会失败，合适的后置条件可以是 `fun _ => False`。

**性能：**

基础迭代器 `it` 每发出一个值，此组合子都会调用 `f`，并对返回的 `Option` 值进行模式匹配。
-/
def c114 := @IterM.filterMapWithPostcondition

/--
给定两个迭代器 `left` 和 `right`，`left.zip right` 会发出 `left` 与 `right` 输出值组成的配对。当其中一个终止时，`zip` 迭代器也会终止。

**弹珠图：**

```text
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```

**终止性质：**

* `Finite` 实例：仅当 `left` 或 `right` 中一个有限、另一个能产时可用
* `Productive` 实例：仅当 `left` 与 `right` 都能产时可用

有时 `left.zip right` 虽然有限（或能产），上述实例却都不适用。例如，若计算位于 `Except` 单子中，且 `left` 在调用 `step` 时立即失败，则 `left.zip right` 也会立即失败。此时需要手动证明 `Finite`（或 `Productive`）实例。

**性能：**

`left` 或 `right` 每执行一步，此组合子都会引入额外 O(1) 开销。

目前编译器不会拆箱内部状态，因此性能低于可能达到的水平。
-/
def c115 := @IterM.zip

/--
为满足谓词 `P` 的值组成的迭代器逐个“附加”证明，返回值位于相应子类型 `{ x // P x }` 中的迭代器。

**终止性质：**

* `Finite` 实例：仅当基础迭代器有限时可用
* `Productive` 实例：仅当基础迭代器能产时可用
-/
def c116 := @IterM.attachWith

/--
能产迭代器的归纳原理：要定义一个把每个迭代器 映射到 `motive it` 中元素的函数 `f`，可以依据 `f` 在 `it` 的合理跳过后继上的值来定义 `f it`。
-/
def c117 := @Iter.inductSkips

/--
能产单子式迭代器的归纳原理：要定义一个把每个迭代器 映射到 `motive it` 中元素的函数 `f`，可以依据 `f` 在 `it` 的合理跳过后继上的值来定义 `f it`。
-/
def c118 := @IterM.inductSkips

/--
有限迭代器的归纳原理：要定义一个把每个迭代器 映射到 `motive it` 中元素的函数 `f`，可以依据 `f` 在 `it` 的合理后继上的值来定义 `f it`。
-/
def c119 := @Iter.inductSteps

/--
有限单子式迭代器的归纳原理：要定义一个把每个迭代器 映射到 `motive it` 中元素的函数 `f`，可以依据 `f` 在 `it` 的合理后继上的值来定义 `f it`。
-/
def c120 := @IterM.inductSteps

/--
`PostconditionT m α` 表示单子 `m` 中的一项操作，并内蕴地证明某个后置条件对该单子式 `α` 值结果成立。它由关于 `α` 的谓词 `P` 和一个 `m ({ a // P a })` 元素组成；在迭代器语境下，它是进行内蕴验证（尤其是终止性证明）的有用工具。

若 `m` 是单子，则 `PostconditionT m` 也是单子。但请注意，`PostconditionT m α` 是结构体，因此编译器会为返回 `PostconditionT m α` 的递归函数生成低效代码；针对 `ReaderT`、`StateT` 等的优化不适用于结构体。

此外，`PostconditionT m α` 不是行为良好的单子变换器，因为 `PostconditionT.lift` 既不与 `pure` 交换，也不与 `bind` 交换。
-/
structure c121 (m : Type w → Type v) (α : Type w) where
  /-- 对 `m` 单子式操作的返回值成立的谓词。 -/
  Property : α → Prop
  /-- 实际的单子式操作。其返回值与它满足 `Property` 的证明打包在一起。 -/
  operation : m {x : α // Property x}

/--
把操作从 `PostConditionT m` 转换到 `m`，并丢弃后置条件。
-/
def c122 := @Std.Iterators.PostconditionT.run

/--
把操作从 `m` 提升到 `PostconditionT m`，但不断言任何非平凡的后置条件。

注意：`lift` 不是合法的提升函数。
例如，`pure a : PostconditionT m α` 与 `PostconditionT.lift (pure a : m α)` 并不相同。
-/
def c123 := @Std.Iterators.PostconditionT.lift

/--
把单子式值从 `m { a : α // P a }` 提升为 `PostconditionT m α` 值。
-/
def c124 := @Std.Iterators.PostconditionT.liftWithProperty

/--
断言某个迭代器 `it` 有可能在任意多步之后合理地发出值 `out`。
-/
inductive c125 : {α β : Type w} → [Std.Iterator α Id β] → @Std.Iter α β → β → Prop where
  /-- 该输出值有可能在下一步被合理地发出。 -/
  | direct {α β : Type w} [inst : Std.Iterator α Id β] {it : @Std.Iter α β} {out : β} :
      @Std.Iter.IsPlausibleOutput α β inst it out → @c125 α β inst it out
  /-- 该输出值有可能在下一步之后的某一步被合理地发出。 -/
  | indirect {α β : Type w} [inst : Std.Iterator α Id β]
      {it it' : @Std.Iter α β} {out : β} :
      @Std.Iter.IsPlausibleSuccessorOf α β inst it' it →
      @c125 α β inst it' out → @c125 α β inst it out

/--
若 `m` 是单子，则 `HetT m` 是具有以下两个特性的单子：

* 它把 `m` 推广到任意宇宙。
* 它像 `PostconditionT` 一样，跟踪一个对单子式返回值成立的后置条件性质。

此单子不可计算，仅用于让证明更方便，尤其是迭代器等价性的证明：它避免了宇宙问题，也省去用户手动处理后置条件的工作。

注意：与 `PostconditionT` 一样，它也不是合法的单子变换器。要从 `m` 提升到 `HetT m`，请使用 `HetT.lift`。

由于此单子从根本上是宇宙多态的，为保持一致，建议始终使用方法 `HetT.pure`、`HetT.map` 和 `HetT.bind`，而不要使用齐次版本 `Pure.pure`、`Functor.map` 和 `Bind.bind`。
-/
structure c126 (m : Type w → Type v) (α : Type u) where
  /-- 对 `m` 单子式操作的返回值成立的谓词。 -/
  Property : α → Prop
  /-- 可能的返回值等价于某个 `w`-小类型的证明。 -/
  small : Std.Internal.Small {x : α // Property x}
  /-- 实际的单子式操作。其返回值与它满足 `Property` 的证明打包，并被压缩到足以放入单子 `m` 的大小。 -/
  operation : m (@Std.Internal.USquash.{w, u} {x : α // Property x} small)

/--
使用 `HetT` 单子的 `IterM.step` 不可计算变体。它用于定义迭代器上的等价关系，即 `IterM.Equiv` 和 `Iter.Equiv`。
-/
noncomputable def c127 := @IterM.stepAsHetT

/--
以平凡后置条件把 `x : m α` 提升到 `HetT m α`。

注意：这不是合法的单子提升函数。
-/
noncomputable def c128 := @HetT.lift

/--
将给定函数应用于所含 `m` 单子式操作的结果，同时提供后置条件性质成立的证明，并返回 `m` 中的另一个操作。
-/
noncomputable def c129 := @HetT.prun

/--
`Pure.pure` 的宇宙异质版本。给定 `a : α`，它返回一个后置条件为 `(a = ·)` 的 `HetT m α` 元素。
-/
noncomputable def c130 := @HetT.pure

/--
`Functor.map` 的宇宙异质版本。
-/
noncomputable def c131 := @HetT.map

/--
`HetT.map` 的推广：它把后置条件性质提供给映射函数。
-/
noncomputable def c132 := @HetT.pmap

/--
`Bind.bind` 的宇宙异质版本。
-/
noncomputable def c133 := @HetT.bind

/--
`HetT.bind` 的推广：它把后置条件性质提供给映射函数。
-/
noncomputable def c134 := @HetT.pbind

/--
迭代器上的等价关系。只要不直接检查内部状态，等价迭代器的行为就相同。

两个迭代器（类型可以不同）等价，当且仅当它们具有相同的 `Iterator.IsPlausibleStep` 关系，并且其步进函数相同——这里后继迭代器只要求*在等价意义下*相同。这个余归纳定义刻画了如下思想：迭代器唯一相关的特征是其步进函数。能从迭代器取得的其他信息——例如它是列表迭代器还是数组迭代器——对等价性判断完全无关。
-/
def c135 := @Iter.Equiv

/--
单子式迭代器上的等价关系。只要不直接检查内部状态，等价迭代器的行为就相同。

两个迭代器（类型可以不同）等价，当且仅当它们具有相同的 `Iterator.IsPlausibleStep` 关系，并且其步进函数相同——这里后继迭代器只要求*在等价意义下*相同。这个余归纳定义刻画了如下思想：迭代器唯一相关的特征是其步进函数。能从迭代器取得的其他信息——例如它是列表迭代器还是数组迭代器——对等价性判断完全无关。
-/
def c136 := @IterM.Equiv

end Manual.ZhDocString.Iterators
