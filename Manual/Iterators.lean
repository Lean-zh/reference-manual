/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Std.Data.Iterators
import Std.Data.TreeMap

import Manual.Meta
import Manual.Interaction.FormatRepr
import Manual.ZhDocString.Iterators

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

#doc (Manual) "迭代器" =>
%%%
file := "Iterators"
tag := "iterators"
%%%

{deftech (key := "iterator")}_迭代器_提供对某个数据源中各元素的顺序访问。
典型的迭代器允许逐个访问列表、数组或 {name Std.TreeMap}`TreeMap` 等集合中的元素；它们也可以通过执行某种{tech (key := "monad")}[单子式]效果（例如读取文件）来提供数据访问。
迭代器为所有这些操作提供了统一接口。
依据迭代器接口编写的代码无需关心数据来自何处。

每个迭代器都维护一份内部状态，用以确定下一个值。
由于 Lean 是纯函数式语言，消费迭代器不会使其失效，而是会复制出一个状态已更新的迭代器。
一如既往，{tech (key := "reference count")}[引用计数]会将仅使用值一次的程序优化为以破坏性方式修改值的程序。

要使用迭代器，请导入 {module}`Std.Data.Iterators`。

:::example "混用集合" (file := "Mixing Collections")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
通常，使用 {name}`List.zip` 或 {name}`Array.zip` 合并列表与数组，需要先将其中一个转换成另一种集合。
使用迭代器，无需转换即可处理二者：
```lean (name := zip)
def colors : Array String := #["purple", "gray", "blue"]
def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

#eval colors.iter.zip codes.iter |>.toArray
```
```leanOutput zip
#[("purple", "aa27d1"), ("gray", "a0a0a0"), ("blue", "0000c5")]
```
:::

::::example "避免中间结构" (file := "Avoiding Intermediate Structures")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
:::paragraph
本例合并一个颜色数组和一个颜色编码列表。
程序分为三个中间阶段：
1. 将名称与编码组合成二元组。
2. 将二元组转换为可读字符串。
3. 用换行符连接这些字符串。
```lean (name := intermediate)
def colors : Array String := #["purple", "gray", "blue"]

def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

def go : IO Unit := do
  let colorCodes := colors.iter.zip codes.iter
  let colorCodes := colorCodes.map fun (name, code) =>
    s!"{name} ↦ #{code}"
  let colorCodes := colorCodes.fold (init := "") fun x y =>
    if x.isEmpty then y else x ++ "\n" ++ y
  IO.println colorCodes

#eval go
```
```leanOutput intermediate
purple ↦ #aa27d1
gray ↦ #a0a0a0
blue ↦ #0000c5
```
:::

计算的中间阶段不会分配新的数据结构。
相反，转换的所有步骤会融合为一个循环，由 {name}`Iter.fold` 每次执行一步。
每一步都会将一个颜色及其编码组合成二元组、改写为字符串，再加入结果字符串。
::::

Lean 标准库提供三类迭代器操作。
{deftech (key := "Producers")}_生产者_从某个数据源创建新的迭代器。
它们决定迭代器返回哪些数据以及如何计算这些数据，但不控制计算在_何时_发生。
{deftech (key := "Consumers")}_消费者_将迭代器中的数据用于某种目的。
消费者向迭代器请求数据，而迭代器只计算足以满足请求的数据。
{deftech (key := "iterator combinator")}_组合子_既是消费者也是生产者：它们从现有迭代器创建新的迭代器。
例如 {name}`Iter.map` 和 {name}`Iter.filter`。
所得迭代器通过消费其底层迭代器来生产数据；只有当它们自身被消费时，才会真正遍历底层集合。


:::keepEnv
```lean -show
/-- 一种集合类型。 -/
structure Coll : Type u where
/-- 集合 `Coll` 的元素。 -/
structure Elem : Type u where
/-- 返回 `c` 的迭代器。 -/
def Coll.iter (c : Coll) := (#[].iter : Iter Elem)
```
每种适合迭代的内置集合都可以被遍历。
换言之，集合库包含迭代器{tech (key := "producers")}[生产者]。
按照约定，集合类型 {name}`Coll` 会提供函数 {name}`Coll.iter`，返回遍历该集合元素的迭代器。
例如 {name}`List.iter`、{name}`Array.iter` 和 {name}`TreeMap.iter`。
此外，区间等其他内置类型也按同一约定支持迭代。
:::

# 运行时考量
%%%
file := "Run-Time-Considerations"
tag := "Lean-__________________--Iterators--Run-Time-Considerations"
%%%

在许多使用场景中，迭代器可以避免分配中间数据结构，从而提升性能。
若不使用迭代器，将列表与数组配对时，必须先把其中一个转换成另一种类型并分配中间结构，然后再使用相应的 {name List.zip}`zip` 函数。
使用迭代器即可避免这一中间结构。

消费迭代器时，应将所得计算视作单个循环，即使该迭代器本身是用组合子从多个底层迭代器构建的。
循环的一步可能会执行底层迭代器的多个步骤。
在许多情况下，Lean 编译器可以优化迭代器计算并消除中间开销，但并不保证总能如此。
若性能分析表明涉及多个数据源的紧密循环耗时显著，可能需要检查编译器的中间表示，以确认迭代器操作是否已融合。
尤其是，当中间表示中包含大量针对步骤的模式匹配时，这可能表示内联或特化失败。
此时可能需要手写尾递归函数，而不是使用高层接口。

# 迭代器定义
%%%
file := "Iterator-Definitions"
tag := "Lean-__________________--Iterators--Iterator-Definitions"
%%%

迭代器可以是单子式或纯的，也可以是有限、能产或潜在无限的。
{deftech (key:="monadic iterator")}_单子式_迭代器使用某个{tech (key := "monad")}[单子]中的副作用来发出各个值，因此必须在该单子中使用；而{deftech (key:="pure iterator")}_纯_迭代器不需要副作用。
例如，迭代目录中的所有文件需要 {name}`IO` 单子。
纯迭代器的类型为 {name}`Iter`，单子式迭代器则由 {name}`IterM` 表示。

{zhdocstring Iter Manual.ZhDocString.Iterators.c001}

{zhdocstring IterM Manual.ZhDocString.Iterators.c002}

类型 {name}`Iter` 和 {name}`IterM` 只是内部状态的包装。
该内部状态类型是迭代器类型的隐式参数。
对于 {name}`List.iter` 所产生的这类基本生产者迭代器，该类型相当简单；但由{tech (key := "iterator combinator")}[组合子]产生的迭代器会使用可能变得很庞大的多态状态类型。
由于 Lean 会先精译函数指定的返回类型，再精译其函数体，因此可能无法自动确定函数所返回迭代器类型的内部状态类型。
此时可以省略签名中的返回类型，改在定义体上添加类型标注，从而让定义体中调用的具体迭代器组合子参与确定状态类型。

:::example "迭代器状态类型" (file := "Iterator State Types")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators.Types (ListIterator ArrayIterator Map)
```

可以显式写出列表与数组迭代器的内部状态类型：
```lean
def reds := ["red", "crimson"]

example : @Iter (ListIterator String) String := reds.iter

example : @Iter (ArrayIterator String) String := reds.toArray.iter
```
但使用 {name}`Iter.map` 组合子时，其内部状态类型相当复杂：
```lean
example :
    @Iter
      (Map (ListIterator String) Id Id @id fun x : String =>
        pure x.length)
      Nat :=
  reds.iter.map String.length
```
省略状态类型会导致错误：
```lean +error (name := noStateType)
example : Iter Nat := reds.iter.map String.length
```
```leanOutput noStateType
don't know how to synthesize implicit argument `α`
  @Iter ?m.1 Nat
context:
⊢ Type

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
与其手写状态类型，不如省略返回类型，改在项的外部提供标注：
```lean
example := (reds.iter.map String.length : Iter Nat)

example :=
  show Iter Nat from
  reds.iter.map String.length
```
:::

实际的迭代过程是在收到请求时产生一系列迭代步骤。
每一步都会返回具有新内部状态的更新后迭代器，同时还会返回以下三者之一：数据值（{name}`IterStep.yield`）、提示调用方应再次请求数据值的标志（{name}`IterStep.skip`），或迭代已经结束的标志（{name}`IterStep.done`）。
若不能使用 {name IterStep.skip}`skip`，就会很难处理 {name}`Iter.filter` 这类不会为底层迭代器发出的每个值都产出结果的迭代器组合子。
借助 {name IterStep.skip}`skip`，{name Iter.filter}`filter` 的实现无需为了成为良定义函数而考虑底层迭代器是否{tech (key:="finite iterator")}[有限]；关于其有限性的推理可以在单独的证明中完成。
此外，否则 {name Iter.filter}`filter` 还需要一个内层循环，而编译器很难将其内联。

{zhdocstring IterStep Manual.ZhDocString.Iterators.c003}

{name}`Iter` 和 {name}`IterM` 所执行的步骤分别由类型 {name}`Iter.Step` 和 {name}`IterM.Step` 表示。
这两种步骤类型都是 {name}`IterStep` 的包装，其中包含用于跟踪终止行为的{ref "iterator-plausibility"}[额外证明]。

{zhdocstring Iter.Step Manual.ZhDocString.Iterators.c004}

{zhdocstring IterM.Step Manual.ZhDocString.Iterators.c005}

迭代器通过 {name}`Iterator.step` 产生步骤；它是 {name}`Iterator` 类型类的方法。
{name}`Iterator` 同时用于纯迭代器和单子式迭代器；纯迭代器可以对单子的选择完全多态，因此调用方可以用 {name}`Id` 将其实例化。

{zhdocstring Iterator Manual.ZhDocString.Iterators.c006 +allowMissing}

## 合理性
%%%
tag := "iterator-plausibility"
%%%

除了步骤函数，{name}`Iterator` 的实例还包含关系 {name}`Iterator.IsPlausibleStep`。
该关系之所以存在，是因为大多数迭代器既会维持其内部状态上的不变量，也会以可预测的方式产出值。
例如，数组迭代器会同时跟踪一个数组以及指向其中的当前索引。
推进数组迭代器会得到仍遍历同一底层数组的迭代器；当索引足够小时它会产出一个值，否则便结束。
从某个迭代器状态出发的{deftech (key := "plausible steps")}_合理步骤_，是指通过该迭代器对 {name Iterator.IsPlausibleStep}`IsPlausibleStep` 的实现而与该状态相关的步骤。
在逻辑层面跟踪合理性，使得推理单子式迭代器的终止行为成为可能。

{name}`Iter.Step` 与 {name}`IterM.Step` 都以 {name}`PlausibleIterStep` 定义；因此，这两种类型都可以对其命名空间使用{tech (key := "leading dot notation")}[前导点记法]。
可以使用三个{ref "match_pattern-functions"}[匹配模式函数] {name}`PlausibleIterStep.yield`、{name}`PlausibleIterStep.skip` 和 {name}`PlausibleIterStep.done` 分析 {name}`Iter.Step` 或 {name}`IterM.Step`。
这些函数把底层 {name}`IterStep` 中的信息与其外围证明对象配对。

{zhdocstring PlausibleIterStep Manual.ZhDocString.Iterators.c007}

{zhdocstring PlausibleIterStep.yield Manual.ZhDocString.Iterators.c008}

{zhdocstring PlausibleIterStep.skip Manual.ZhDocString.Iterators.c009}

{zhdocstring PlausibleIterStep.done Manual.ZhDocString.Iterators.c010}

## 有限且能产的迭代器
%%%
tag := "Lean-__________________--Iterators--Iterator-Definitions--Finite-and-Productive-Iterators"
%%%

:::paragraph
并非所有迭代器都保证返回有限个结果；遍历所有自然数完全合理。
同样，并非所有迭代器都保证返回一个结果或终止；迭代器可以用任意程序定义。
因此，Lean 将迭代器分为三类终止性类别：
* {deftech (key:="finite iterator")}_有限_迭代器保证在有限步后结束迭代。这些迭代器具有 {name}`Finite` 实例。
* {deftech (key:="productive iterator")}_能产_迭代器保证在有限步内产出一个值或终止，但它们可能产出无限多个值。这些迭代器具有 {name}`Productive` 实例。
* 其余终止行为未知的迭代器。这些迭代器不具有上述任何一种实例。

所有有限迭代器必然都是能产的。
:::

{zhdocstring Finite Manual.ZhDocString.Iterators.c011}

{zhdocstring Productive Manual.ZhDocString.Iterators.c012}

Lean 标准库提供了许多遍历迭代器的函数。这些消费者函数通常不会
对底层迭代器作任何假设。尤其是，对某些迭代器而言，这类函数可能永远运行下去。

有时，确保函数确实终止至关重要。
在这些情况下，组合子 {name}`Iter.ensureTermination` 会得到一种迭代器，它提供保证终止的消费者变体。
这些变体通常要求证明所涉及的迭代器是有限的。

{zhdocstring Iter.ensureTermination Manual.ZhDocString.Iterators.c013}

{zhdocstring IterM.ensureTermination Manual.ZhDocString.Iterators.c014}

::::example "迭代 `Nat`" (file := "Iterating Over Nat")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
:::paragraph
要编写依次产出每个自然数的迭代器，第一步是实现其内部状态。
该迭代器只需记住下一个自然数：
```lean
structure Nats where
  next : Nat
```
:::
:::paragraph
该迭代器只会产出下一个自然数。
因此，它的步骤函数绝不会返回 {name IterStep.skip}`skip` 或 {name IterStep.done}`done`。
每当它产出一个值时，该值就是内部状态的 {name Nats.next}`next` 字段，而后继迭代器的 {name Nats.next}`next` 字段则会增加一。
{tactic}`grind` 策略足以证明该步骤确实合理：
```lean
instance [Pure m] : Iterator Nats m Nat where
  IsPlausibleStep it
    | .yield it' n =>
      n = it.internalState.next ∧
      it'.internalState.next = n + 1
    | _ => False
  step it :=
    let n := it.internalState.next
    pure <| .deflate <|
      .yield { it with internalState.next := n + 1 } n (by grind)
```

每当定义迭代器时，都应提供 {name}`IteratorLoop` 实例。
{name}`Iter.toList` 或 `for` 循环等大多数迭代器消费者都需要它。
可以如下使用其默认实现：

```lean
instance [Pure m] [Monad n] : IteratorLoop Nats m n :=
  .defaultImplementation
```
:::

:::paragraph
```lean -show
section
variable [Pure m] [inst : Iterator Nats m Nat] (it it' : IterM (α := Nats) m Nat)
```
此 {name Iterator.step}`step` 函数是能产的，因为它绝不返回 {name IterStep.skip}`skip`。
因此，要证明每条 {name IterStep.skip}`skip` 链长度有限，可以利用这一事实：当 {lean}`it` 是 {name}`Nats` 迭代器时，{lean}`Iterator.IsPlausibleStep it (.skip it') = False`：
```lean -show
end
```
```lean
instance [Pure m] : Productive Nats m where
  wf := .intro <| fun _ => .intro _ nofun
```
因为 {name}`Nat` 有无限多个，所以该迭代器不是有限的。
:::


:::paragraph
可以使用此函数创建 {name}`Nats` 迭代器：
```lean
def Nats.iter : Iter (α := Nats) Nat :=
  IterM.mk { next := 0 } |>.toIter
```
:::

:::paragraph
运行以下函数可以打印所有自然数：
```lean
def f : IO Unit := do
  for x in Nats.iter do
    IO.println s!"{x}"
```
该函数永不终止，它会按递增顺序打印所有自然数，一个接
一个。
:::

:::paragraph
该迭代器与 {name}`Iter.zip` 等组合子配合使用时最为有用：
```lean (name := natzip)
#eval show IO Unit from do
  let xs : List String := ["cat", "dog", "pachycephalosaurus"]
  for (x, y) in Nats.iter.zip xs.iter do
    IO.println s!"{x}: {y}"
```
```leanOutput natzip
0: cat
1: dog
2: pachycephalosaurus
```
:::

:::paragraph
与前例不同，该循环会终止，因为 `xs.iter` 是有限迭代器。
可以通过提供 {name}`Finite` 实例来确保循环确实终止：
```lean (name := natfin)
#check type_of% (Nats.iter.zip ["cat", "dog"].iter).internalState

#synth Finite (Zip Nats Id (ListIterator String) String) Id
```
```leanOutput natfin
Zip Nats Id (ListIterator String) String : Type
```
```leanOutput natfin
Zip.instFinite₂
```
相比之下，`Nats.iter` 会产出无限多个值，因此没有 `Finite` 实例：
```lean (name := natinf) +error
#synth Finite Nats Id
```
```leanOutput natinf
failed to synthesize
  Finite Nats Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

因为 {name}`Nat` 有无限多个，使用 {name}`Iter.ensureTermination` 会导致错误：
```lean (name := natterm) +error
#eval show IO Unit from do
  for x in Nats.iter.ensureTermination do
    IO.println s!"{x}"
```
```leanOutput natterm
failed to synthesize instance of type class
  ForIn IO (Iter.Total Nat) ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::
::::

::::example "迭代三元组" (file := "Iterating Over Triples")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Finite)
```
类型 {name}`Triple` 包含三个相同类型的值：
```lean
structure Triple α where
  fst : α
  snd : α
  thd : α
```

遍历 {name}`Triple` 的迭代器，其内部状态可以由一个三元组和当前位置配对组成。
该位置可以是其中一个字段，也可以表示迭代已结束。
```lean
inductive TriplePos where
  | fst | snd | thd | done
```

可以使用位置查找元素：

```lean
def Triple.get? (xs : Triple α) (pos : TriplePos) : Option α :=
  match pos with
  | .fst => some xs.fst
  | .snd => some xs.snd
  | .thd => some xs.thd
  | _ => none
```

每个字段位置都有一个后继位置：
```lean
@[grind, grind cases]
inductive TriplePos.Succ : TriplePos → TriplePos → Prop where
  | fst : Succ .fst .snd
  | snd : Succ .snd .thd
  | thd : Succ .thd .done
```

迭代器本身将三元组与下一个元素的位置配对：
```lean
structure TripleIterator α where
  triple : Triple α
  pos : TriplePos
```

迭代从 {name TriplePos.fst}`fst` 开始：
```lean
def Triple.iter (xs : Triple α) : Iter (α := TripleIterator α) α :=
  IterM.mk {triple := xs, pos := .fst : TripleIterator α} |>.toIter
```

有两种合理步骤：若迭代器的位置存在后继，则下一个迭代器仍指向同一三元组，但位置变为后继位置；若不存在后继，则迭代完成。
```lean
@[grind]
inductive TripleIterator.IsPlausibleStep :
    @IterM (TripleIterator α) m α →
    IterStep (@IterM (TripleIterator α) m α) α →
    Prop where
  | yield :
    it.internalState.triple = it'.internalState.triple →
    it.internalState.pos.Succ it'.internalState.pos →
    it.internalState.triple.get? it.internalState.pos = some out →
    IsPlausibleStep it (.yield it' out)
  | done :
    it.internalState.pos = .done →
    IsPlausibleStep it .done
```

对应的步骤函数会产出该关系所描述的迭代器和值：
```lean
instance [Pure m] : Iterator (TripleIterator α) m α where
  IsPlausibleStep := TripleIterator.IsPlausibleStep
  step
    | ⟨xs, pos⟩ =>
      pure <| .deflate <|
      match pos with
      | .fst => .yield ⟨xs, .snd⟩ xs.fst ?_
      | .snd => .yield ⟨xs, .thd⟩ xs.snd ?_
      | .thd => .yield ⟨xs, .done⟩ xs.thd ?_
      | .done => .done <| ?_
where finally
  all_goals grind [Triple.get?]
```

现在可以将该迭代器转换为数组：
```lean
def abc : Triple Char := ⟨'a', 'b', 'c'⟩
```
```lean (name := abcToArray)
#eval abc.iter.toArray
```
```leanOutput abcToArray
#['a', 'b', 'c']
```

一般而言，`Iter.toArray` 可能永远运行。可以通过构造 `Finite (Triple Char) Id` 实例来
证明 `abc` 是有限的，并证明上例会在有限步后终止。
最简单的做法是从 {name}`TriplePos.done` 开始，反向推至 {name}`TriplePos.fst`，依次证明每个位置都只有有限长的后继链：

```lean
@[grind! .]
theorem acc_done [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .done : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | _, ⟨_, ⟨_, h⟩⟩ => by
      cases h <;> grind [IterStep.successor_done]

@[grind! .]
theorem acc_thd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .thd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_snd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .snd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_fst [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .fst : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

instance [Pure m] : Finite (TripleIterator α) m where
  wf := .intro <| fun
    | { internalState := { triple, pos } } => by
      cases pos <;> grind
```

要使该迭代器可用于 {keywordOf Lean.Parser.Term.doFor}`for` 循环，需要一个 {name}`IteratorLoop` 实例：
```lean
instance [Monad m] [Monad n] :
    IteratorLoop (TripleIterator α) m n :=
  .defaultImplementation
```
```lean (name := abc)
#eval show IO Unit from do
  for x in abc.iter do
    IO.println x
```
```leanOutput abc
a
b
c
```
::::

::::example "迭代器与效果" (file := "Iterators and Effects")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
遍历文件内容的一种方式，是在每一步从 {name IO.FS.Stream}`Stream` 读取指定数量的字节。
到达文件末尾时，迭代器可以让引用计数降为零，从而关闭文件：
```lean
structure FileIterator where
  stream? : Option IO.FS.Stream
  count : USize := 8192
```

可以打开文件并将其句柄转换为流，以创建迭代器：
```lean
def iterFile
    (path : System.FilePath)
    (count : USize := 8192) :
    IO (IterM (α := FileIterator) IO ByteArray) := do
  let h ← IO.FS.Handle.mk path .read
  let stream? := some (IO.FS.Stream.ofHandle h)
  return IterM.mk { stream?, count }
```

对于该迭代器，文件仍打开时 {name IterStep.yield}`yield` 是合理的，文件已关闭时 {name IterStep.done}`done` 是合理的。
实际的步骤函数会执行读取；若没有返回任何字节，则关闭文件：
```lean
instance : Iterator FileIterator IO ByteArray where
  IsPlausibleStep it
    | .yield .. =>
      it.internalState.stream?.isSome
    | .skip .. => False
    | .done => it.internalState.stream?.isNone
  step it := do
    match h : it.internalState.stream? with
    | none => return .deflate <| .done (by simp [h])
    | some stream =>
      let bytes ← stream.read it.internalState.count
      let it' :=
        { it with internalState.stream? :=
          if bytes.size == 0 then none else some stream
        }
      return .deflate <| .yield it' bytes (by simp [h])
```

要在循环中使用它，需要 {name}`IteratorLoop` 实例。
```lean
instance [Monad n] : IteratorLoop FileIterator IO n :=
  .defaultImplementation
```

这些辅助代码足以使用该迭代器计算文件大小：
```lean
def fileSize (name : System.FilePath) : IO Nat := do
  let mut size := 0
  let f := (← iterFile name)
  for bytes in f do
    size := size + bytes.size
  return size
```

::::

## 访问元素
%%%
tag := "Lean-__________________--Iterators--Iterator-Definitions--Accessing-Elements"
%%%

某些迭代器支持高效的随机访问。
例如，数组迭代器只需递增其维护的数组索引，即可在常数时间内跳过任意数量的元素。

{zhdocstring IteratorAccess Manual.ZhDocString.Iterators.c015 +allowMissing}

{zhdocstring IterM.nextAtIdx? Manual.ZhDocString.Iterators.c016}

## 循环
%%%
tag := "Lean-__________________--Iterators--Iterator-Definitions--Loops"
%%%

{zhdocstring IteratorLoop Manual.ZhDocString.Iterators.c017 +allowMissing}

{zhdocstring IteratorLoop.defaultImplementation Manual.ZhDocString.Iterators.c018}

{zhdocstring LawfulIteratorLoop Manual.ZhDocString.Iterators.c019 +allowMissing}

## 宇宙层级
%%%
tag := "Lean-__________________--Iterators--Iterator-Definitions--Universe-Levels"
%%%

为了让迭代器的{tech (key := "universe levels")}[宇宙层级]更加灵活，会在 {name}`Iterator.step` 的结果外应用包装类型 {name Std.Shrink}`Shrink`。
该类型目前只是占位符。
它的存在是为了在完整实现可用时缩小破坏性变更的范围。

{zhdocstring Std.Shrink Manual.ZhDocString.Iterators.c020}

{zhdocstring Std.Shrink.inflate Manual.ZhDocString.Iterators.c021}

{zhdocstring Std.Shrink.deflate Manual.ZhDocString.Iterators.c022}


## 基本迭代器
%%%
tag := "Lean-__________________--Iterators--Iterator-Definitions--Basic-Iterators"
%%%

除了集合类型提供的迭代器，还有两种不与任何底层数据结构关联的基本迭代器。
{name}`Iter.empty` 不产出任何数据并立即结束迭代，而 {name}`Iter.repeat` 会永远产出同一元素。
这些迭代器主要用作通过组合子构建的更大迭代器的组成部分。

{zhdocstring Iter.empty Manual.ZhDocString.Iterators.c023}

{zhdocstring IterM.empty Manual.ZhDocString.Iterators.c024}

{zhdocstring Iter.repeat Manual.ZhDocString.Iterators.c025}


# 消费迭代器
%%%
file := "Consuming-Iterators"
tag := "Lean-__________________--Iterators--Consuming-Iterators"
%%%

:::paragraph
消费迭代器主要有三种方式：

: 将其转换为顺序数据结构

  函数 {name}`Iter.toList`、{name}`Iter.toArray` 及其单子式对应项 {name}`IterM.toList` 和 {name}`IterM.toArray`，会构造按顺序包含迭代器各值的列表或数组。
  只有{tech (key := "finite iterators")}[有限迭代器]才能转换为顺序数据结构。

: {keywordOf Lean.Parser.Term.doFor}`for` 循环

  {keywordOf Lean.Parser.Term.doFor}`for` 循环可以消费迭代器，让每个值在循环体中可用。
  这要求迭代器具有针对该循环所用单子的 {name}`IteratorLoop` 实例。

: 逐步推进迭代器

  迭代器可以逐个提供其值，由客户端代码依次显式请求每个新值。
  逐步推进时，迭代器只执行足以产出所请求值的计算。
:::


:::example "将迭代器转换为列表" (file := "Converting Iterators to Lists")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
在 {name}`countdown` 中，使用 {name}`Iter.map` 将遍历区间的迭代器转换为遍历字符串的迭代器。
这次对 {name}`Iter.map` 的调用并不会遍历区间；直到调用 {name}`Iter.toList` 时，区间中的各个元素才会被产出并转换为字符串。
```lean (name := toListEx)
def countdown : String :=
  let steps : Iter String := (0...10).iter.map (s!"{10 - ·}!\n")
  String.join steps.toList

#eval IO.println countdown
```
```leanOutput toListEx
10!
9!
8!
7!
6!
5!
4!
3!
2!
1!
```
:::

:::example "将无限迭代器转换为列表" (file := "Converting Infinite Iterators to Lists")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
尝试从迭代器构造包含所有自然数的列表会产生无限循环：
```lean (name := toListInf) -keep
def allNats : List Nat :=
  let steps : Iter Nat := (0...*).iter
  steps.toList
```
组合子 {lean}`Iter.ensureTermination` 会产生排除了不终止情形的迭代器。
这类迭代器保证在有限步后终止，因此当 Lean 无法证明迭代器有限时便不能使用。
```lean (name := toListInf) +error -keep
def allNats : List Nat :=
  let steps := (0...*).iter.ensureTermination
  steps.toList
```
所得错误消息指出不存在 {name}`Finite` 实例：
```leanOutput toListInf
failed to synthesize instance of type class
  Finite (Rxi.Iterator Nat) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::example "在循环中消费迭代器" (file := "Consuming Iterators in Loops")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
该程序从区间创建一个字符串迭代器，然后在 {keywordOf Lean.Parser.Term.doFor}`for` 循环中消费这些字符串：
```lean (name := iterFor)
def countdown (n : Nat) : IO Unit := do
  let steps : Iter String := (0...n).iter.map (s!"{n - ·}!")
  for i in steps do
    IO.println i
  IO.println "Blastoff!"

#eval countdown 5
```
```leanOutput iterFor
5!
4!
3!
2!
1!
Blastoff!
```
:::

:::example "直接消费迭代器" (file := "Consuming Iterators Directly")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
函数 {name}`countdown` 直接调用区间迭代器的 {name Iter.step}`step` 函数，并处理三种可能情形。
```lean
def countdown (n : Nat) : IO Unit := do
  let steps : Iter Nat := (0...n).iter
  go steps
where
  go iter := do
    match iter.step with
    | .done _ => pure ()
    | .skip iter' _ => go iter'
    | .yield iter' i _ => do
      IO.println s!"{i}!"
      if i == 2 then
        IO.println s!"Almost there..."
      go iter'
  termination_by iter.finitelyManySteps
```
:::

## 逐步推进迭代器
%%%
tag := "Lean-__________________--Iterators--Consuming-Iterators--Stepping-Iterators"
%%%

可以使用 {name}`Iter.step` 或 {name}`IterM.step` 手动推进迭代器。

{zhdocstring Iter.step Manual.ZhDocString.Iterators.c026}

{zhdocstring IterM.step Manual.ZhDocString.Iterators.c027}

### 终止
%%%
tag := "Lean-__________________--Iterators--Consuming-Iterators--Stepping-Iterators--Termination"
%%%

手动推进有限迭代器时，可以使用终止度量 {name Iter.finitelyManySteps}`finitelyManySteps` 和 {name Iter.finitelyManySkips}`finitelyManySkips` 表明每一步都让迭代更接近结束。
{ref "well-founded-recursion"}[良基递归]的证明自动化已预先配置，可证明步骤之后的递归调用会减小这些度量。

:::example "有限次跳过" (file := "Finitely Many Skips")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
该函数在迭代器存在首个元素时返回它，否则返回 {name}`none`。
因为该迭代器必须能产，所以保证至多经过有限次 {name PlausibleIterStep.skip}`skip` 后返回一个元素。
即使面对无限迭代器，该函数也会终止。
```lean
def getFirst {α β} [Iterator α Id β] [Productive α Id]
    (it : @Iter α β) : Option β :=
  match it.step with
  | .done .. => none
  | .skip it' .. => getFirst it'
  | .yield _ x .. => pure x
termination_by it.finitelyManySkips
```
:::

{zhdocstring Iter.finitelyManySteps Manual.ZhDocString.Iterators.c028}

{zhdocstring IterM.finitelyManySteps Manual.ZhDocString.Iterators.c029}

{zhdocstring IterM.TerminationMeasures.Finite Manual.ZhDocString.Iterators.c030 +allowMissing}

{zhdocstring Iter.finitelyManySkips Manual.ZhDocString.Iterators.c031}

{zhdocstring IterM.finitelyManySkips Manual.ZhDocString.Iterators.c032}

{zhdocstring IterM.TerminationMeasures.Productive Manual.ZhDocString.Iterators.c033 +allowMissing}

## 消费纯迭代器
%%%
tag := "Lean-__________________--Iterators--Consuming-Iterators--Consuming-Pure-Iterators"
%%%

{zhdocstring Iter.fold Manual.ZhDocString.Iterators.c034}

{zhdocstring Iter.foldM Manual.ZhDocString.Iterators.c035}

{zhdocstring Iter.length Manual.ZhDocString.Iterators.c036}

{zhdocstring Iter.any Manual.ZhDocString.Iterators.c037}

{zhdocstring Iter.anyM Manual.ZhDocString.Iterators.c038}

{zhdocstring Iter.all Manual.ZhDocString.Iterators.c039}

{zhdocstring Iter.allM Manual.ZhDocString.Iterators.c040}

{zhdocstring Iter.find? Manual.ZhDocString.Iterators.c041 +allowMissing}

{zhdocstring Iter.findM? Manual.ZhDocString.Iterators.c042 +allowMissing}

{zhdocstring Iter.findSome? Manual.ZhDocString.Iterators.c043 +allowMissing}

{zhdocstring Iter.findSomeM? Manual.ZhDocString.Iterators.c044 +allowMissing}

{zhdocstring Iter.atIdx? Manual.ZhDocString.Iterators.c045}

{zhdocstring Iter.atIdxSlow? Manual.ZhDocString.Iterators.c046}

## 消费单子式迭代器
%%%
tag := "Lean-__________________--Iterators--Consuming-Iterators--Consuming-Monadic-Iterators"
%%%

{zhdocstring IterM.drain Manual.ZhDocString.Iterators.c047}

{zhdocstring IterM.fold Manual.ZhDocString.Iterators.c048}

{zhdocstring IterM.foldM Manual.ZhDocString.Iterators.c049}

{zhdocstring IterM.length Manual.ZhDocString.Iterators.c050}

{zhdocstring IterM.any Manual.ZhDocString.Iterators.c051}

{zhdocstring IterM.anyM Manual.ZhDocString.Iterators.c052}

{zhdocstring IterM.all Manual.ZhDocString.Iterators.c053}

{zhdocstring IterM.allM Manual.ZhDocString.Iterators.c054}

{zhdocstring IterM.find? Manual.ZhDocString.Iterators.c055 +allowMissing}

{zhdocstring IterM.findM? Manual.ZhDocString.Iterators.c056 +allowMissing}

{zhdocstring IterM.findSome? Manual.ZhDocString.Iterators.c057 +allowMissing}

{zhdocstring IterM.findSomeM? Manual.ZhDocString.Iterators.c058 +allowMissing}

{zhdocstring IterM.atIdx? Manual.ZhDocString.Iterators.c059}

## 收集器
%%%
tag := "Lean-__________________--Iterators--Consuming-Iterators--Collectors"
%%%

收集器消费迭代器，并以列表或数组返回其全部数据。
可被收集的迭代器必须是有限的。

{zhdocstring Iter.toArray Manual.ZhDocString.Iterators.c060}

{zhdocstring IterM.toArray Manual.ZhDocString.Iterators.c061}

{zhdocstring Iter.toList Manual.ZhDocString.Iterators.c062}

{zhdocstring IterM.toList Manual.ZhDocString.Iterators.c063}

{zhdocstring Iter.toListRev Manual.ZhDocString.Iterators.c064}

{zhdocstring IterM.toListRev Manual.ZhDocString.Iterators.c065}


# 迭代器组合子
%%%
file := "Iterator-Combinators"
tag := "Lean-__________________--Iterators--Iterator-Combinators"
%%%

迭代器组合子的文档通常包含{deftech (key := "marble diagrams")}_弹珠图_，用来展示底层迭代器返回的元素与组合子迭代器返回的元素之间的关系。
弹珠图提供的是示例，而非完整规约。
这些图由若干行组成。
每一行展示一个迭代器输出示例，其中 `-` 表示 {name PlausibleIterStep.skip}`skip`，项表示通过 {name PlausibleIterStep.yield}`yield` 返回的值，而 `⊥` 表示迭代结束。
空格表示没有发生迭代。
弹珠图中未绑定的标识符代表迭代器元素类型的任意值。


弹珠图中的垂直对齐表示因果关系：两个元素对齐意味着消费下方一行的迭代器会导致上方各行被消费。
特别地，将下方迭代器消费到第 $`n` 列，会导致上方迭代器的前 $`n` 列被消费。

:::paragraph
逐一返回底层迭代器各元素的恒等迭代器组合子，其弹珠图如下：
```
it    ---a-----b---c----d⊥
it.id ---a-----b---c----d⊥
```
:::
:::paragraph
将底层迭代器的每个元素复制一份的迭代器组合子，其弹珠图如下：
```
it           ---a  ---b  ---c  ---d⊥
it.double    ---a-a---b-b---c-c---d-d⊥
```
:::
:::paragraph
{name}`Iter.filter` 的弹珠图展示了底层迭代器的某些元素如何不出现在过滤后的迭代器中；它还展示了当底层迭代器返回不满足谓词的值时，推进过滤后的迭代器会得到 {name PlausibleIterStep.skip}`skip`：
```
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```
该图需要一条说明：
> （假定 `f a = f c = true` 且 `f b = f d = d e = false`）
:::
:::paragraph
{name}`Iter.zip` 的弹珠图展示了消费组合后的迭代器时如何消费底层迭代器：
```
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```
只要 `left` 发出 {name PlausibleIterStep.skip}`skip`，配对后的迭代器也会发出它。
当 `left` 发出 `a` 时，配对后的迭代器会再发出一次 {name PlausibleIterStep.skip}`skip`。
之后，配对后的迭代器转而消费 `right`；只要 `right` 发出 {name PlausibleIterStep.skip}`skip`，它也会发出该步骤。
当 `right` 发出 `x` 时，配对后的迭代器会发出二元组 `(a, x)`。
对 `left` 与 `right` 的这种交错消费会持续到其中一个停止，此时配对后的迭代器也会停止。
弹珠图上方各行中的空白表示该步骤没有消费相应迭代器。
:::


## 纯组合子
%%%
tag := "Lean-__________________--Iterators--Iterator-Combinators--Pure-Combinators"
%%%

{zhdocstring IterM.mk Manual.ZhDocString.Iterators.c066}

{zhdocstring Iter.toIterM Manual.ZhDocString.Iterators.c067}

{zhdocstring Iter.take Manual.ZhDocString.Iterators.c068}

{zhdocstring Iter.takeWhile Manual.ZhDocString.Iterators.c069}

{zhdocstring Iter.toTake Manual.ZhDocString.Iterators.c070}

{zhdocstring Iter.drop Manual.ZhDocString.Iterators.c071}

{zhdocstring Iter.dropWhile Manual.ZhDocString.Iterators.c072}

{zhdocstring Iter.stepSize Manual.ZhDocString.Iterators.c073}

{zhdocstring Iter.map Manual.ZhDocString.Iterators.c074}

{zhdocstring Iter.mapM Manual.ZhDocString.Iterators.c075}

{zhdocstring Iter.mapWithPostcondition Manual.ZhDocString.Iterators.c076}

{zhdocstring Iter.uLift Manual.ZhDocString.Iterators.c077}

{zhdocstring Iter.flatMap Manual.ZhDocString.Iterators.c078}

{zhdocstring Iter.flatMapM Manual.ZhDocString.Iterators.c079}

{zhdocstring Iter.flatMapAfter Manual.ZhDocString.Iterators.c080}

{zhdocstring Iter.flatMapAfterM Manual.ZhDocString.Iterators.c081}

{zhdocstring Iter.filter Manual.ZhDocString.Iterators.c082}

{zhdocstring Iter.filterM Manual.ZhDocString.Iterators.c083}

{zhdocstring Iter.filterWithPostcondition Manual.ZhDocString.Iterators.c084}

{zhdocstring Iter.filterMap Manual.ZhDocString.Iterators.c085}

{zhdocstring Iter.filterMapM Manual.ZhDocString.Iterators.c086}

{zhdocstring Iter.filterMapWithPostcondition Manual.ZhDocString.Iterators.c087}

{zhdocstring Iter.zip Manual.ZhDocString.Iterators.c088}

{zhdocstring Iter.attachWith Manual.ZhDocString.Iterators.c089}


## 单子式组合子
%%%
tag := "Lean-__________________--Iterators--Iterator-Combinators--Monadic-Combinators"
%%%

{zhdocstring IterM.toIter Manual.ZhDocString.Iterators.c090}

{zhdocstring IterM.take Manual.ZhDocString.Iterators.c091}

{zhdocstring IterM.takeWhile Manual.ZhDocString.Iterators.c092}

{zhdocstring IterM.takeWhileM Manual.ZhDocString.Iterators.c093}

{zhdocstring IterM.takeWhileWithPostcondition Manual.ZhDocString.Iterators.c094}

{zhdocstring IterM.toTake Manual.ZhDocString.Iterators.c095}

{zhdocstring IterM.drop Manual.ZhDocString.Iterators.c096}

{zhdocstring IterM.dropWhile Manual.ZhDocString.Iterators.c097}

{zhdocstring IterM.dropWhileM Manual.ZhDocString.Iterators.c098}

{zhdocstring IterM.dropWhileWithPostcondition Manual.ZhDocString.Iterators.c099}

{zhdocstring IterM.stepSize Manual.ZhDocString.Iterators.c100}

{zhdocstring IterM.map Manual.ZhDocString.Iterators.c101}

{zhdocstring IterM.mapM Manual.ZhDocString.Iterators.c102}

{zhdocstring IterM.mapWithPostcondition Manual.ZhDocString.Iterators.c103}

{zhdocstring IterM.uLift Manual.ZhDocString.Iterators.c104}

{zhdocstring IterM.flatMap Manual.ZhDocString.Iterators.c105}

{zhdocstring IterM.flatMapM Manual.ZhDocString.Iterators.c106}

{zhdocstring IterM.flatMapAfter Manual.ZhDocString.Iterators.c107}

{zhdocstring IterM.flatMapAfterM Manual.ZhDocString.Iterators.c108}

{zhdocstring IterM.filter Manual.ZhDocString.Iterators.c109}

{zhdocstring IterM.filterM Manual.ZhDocString.Iterators.c110}

{zhdocstring IterM.filterWithPostcondition Manual.ZhDocString.Iterators.c111}

{zhdocstring IterM.filterMap Manual.ZhDocString.Iterators.c112}

{zhdocstring IterM.filterMapM Manual.ZhDocString.Iterators.c113}

{zhdocstring IterM.filterMapWithPostcondition Manual.ZhDocString.Iterators.c114}

{zhdocstring IterM.zip Manual.ZhDocString.Iterators.c115}

{zhdocstring IterM.attachWith Manual.ZhDocString.Iterators.c116}

# 迭代器推理
%%%
file := "Reasoning-About-Iterators"
tag := "Lean-__________________--Iterators--Reasoning-About-Iterators"
%%%

## 消费者推理
%%%
tag := "Lean-__________________--Iterators--Reasoning-About-Iterators--Reasoning-About-Consumers"
%%%

迭代器库提供了大量有用的引理。
大多数关于有限迭代器的定理都可以通过将命题改写为关于列表的命题来证明，因为迭代器组合子与相应列表操作之间的对应关系已经得到证明。
实践中，许多此类定理已经注册为 {tactic}`simp` 引理。

:::paragraph
这些引理的命名规则非常容易预测，其中许多位于{tech (key := "default simp set")}[默认化简集]中。
其中最重要的包括：

 * {name}`Iter.all_toList`、{name}`Iter.any_toList` 和 {name}`Iter.foldl_toList` 等消费者引理，它们引入列表作为模型。

 * {name}`Iter.toList_map` 和 {name}`Iter.toList_filter` 等化简引理，它们把列表模型向目标内部推进。

 * {name}`List.toList_iter` 和 {name}`Array.toList_iter` 等生产者引理，它们用列表模型替换生产者，从目标中彻底消除迭代器。

后两类通常可由 {tactic}`simp` 自动处理。
:::

:::example "通过列表推理" (file := "Reasoning via Lists")
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
一个迭代器若将从另一迭代器消费的数乘以二，则其返回的每个元素都是偶数。
为证明该命题，可以使用 {name}`Iter.all_toList`、{name}`Iter.toList_map` 和 {name}`Array.toList_iter` 将关于迭代器的命题替换为关于列表的命题，随后由 {tactic}`simp` 完成目标：
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  rw [← Iter.all_toList]
  rw [Iter.toList_map]
  rw [Array.toList_iter]
  simp
```

事实上，由于所需的大多数引理都位于{tech (key := "default simp set")}[默认化简集]中，证明可以相当简短：
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  simp [← Iter.all_toList]
```
:::

## 逐步推理
%%%
tag := "Lean-__________________--Iterators--Reasoning-About-Iterators--Stepwise-Reasoning"
%%%

当没有足够引理通过改写为列表模型来证明某个性质时，可能需要直接推理迭代器的步骤函数。
本节的归纳原理适用于逐步推理。

{zhdocstring Iter.inductSkips Manual.ZhDocString.Iterators.c117}

{zhdocstring IterM.inductSkips Manual.ZhDocString.Iterators.c118}

{zhdocstring Iter.inductSteps Manual.ZhDocString.Iterators.c119}

{zhdocstring IterM.inductSteps Manual.ZhDocString.Iterators.c120}

标准库还包含描述所有生产者和组合子逐步行为的引理。
例如 {name}`List.step_iter_nil`、{name}`List.step_iter_cons` 和 {name}`IterM.step_map`。

## 用于推理的单子
%%%
tag := "Lean-__________________--Iterators--Reasoning-About-Iterators--Monads-for-Reasoning"
%%%

{zhdocstring Std.Iterators.PostconditionT Manual.ZhDocString.Iterators.c121}

{zhdocstring Std.Iterators.PostconditionT.run Manual.ZhDocString.Iterators.c122}

{zhdocstring Std.Iterators.PostconditionT.lift Manual.ZhDocString.Iterators.c123}

{zhdocstring Std.Iterators.PostconditionT.liftWithProperty Manual.ZhDocString.Iterators.c124}

{zhdocstring Iter.IsPlausibleIndirectOutput Manual.ZhDocString.Iterators.c125 +allowMissing}

{zhdocstring HetT Manual.ZhDocString.Iterators.c126}

{zhdocstring IterM.stepAsHetT Manual.ZhDocString.Iterators.c127}

{zhdocstring HetT.lift Manual.ZhDocString.Iterators.c128}

{zhdocstring HetT.prun Manual.ZhDocString.Iterators.c129}

{zhdocstring HetT.pure Manual.ZhDocString.Iterators.c130}

{zhdocstring HetT.map Manual.ZhDocString.Iterators.c131}

{zhdocstring HetT.pmap Manual.ZhDocString.Iterators.c132}

{zhdocstring HetT.bind Manual.ZhDocString.Iterators.c133}

{zhdocstring HetT.pbind Manual.ZhDocString.Iterators.c134}

## 等价性
%%%
tag := "Lean-__________________--Iterators--Reasoning-About-Iterators--Equivalence"
%%%

迭代器等价性依据迭代器的可观察行为定义，而非依据其实现。
尤其是，内部状态会被忽略。

{zhdocstring Iter.Equiv Manual.ZhDocString.Iterators.c135}

{zhdocstring IterM.Equiv Manual.ZhDocString.Iterators.c136}
