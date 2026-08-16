/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option format.width 60

#doc (Manual) "范围" =>
%%%
tag := "ranges"
%%%

{deftech (key := "range")}_范围_表示某种类型的连续元素序列，从下界到上界。
边界可以是开的，在这种情况下，边界值不属于该范围，也可以是闭的，在这种情况下，边界值属于该范围。
任一边界都可以被省略，在这种情况下，范围在相应的方向上无限延伸。

范围具有专用语法，包括一个起点、{keyword}`...` 和一个终点。
起点可以是 `*`，表示向下无限延伸的范围，也可以是一个项，表示具有特定起始值的范围。
默认情况下，范围是左闭的：它们包含其起点。
尾部的 `<` 表示该范围是左开的并且不包含其起点。
终点可以是 `*`，在这种情况下范围向上无限延伸，也可以是一个项，表示具有特定结束值的范围。
默认情况下，范围是右开的：它们不包含其终点。
终点可以前缀 `<` 以表示它是右开的；这是默认行为，不会改变含义，但可能更容易阅读。
它也可以前缀 `=` 以表示该范围是右闭的并且包含其终点。


:::example "自然数范围"
包含数字 {lean}`3` 到 {lean}`6` 的范围可以用多种方式编写：
```lean (name := rng1)
#eval (3...7).toList
```
```leanOutput rng1
[3, 4, 5, 6]
```
```lean (name := rng2)
#eval (3...=6).toList
```
```leanOutput rng2
[3, 4, 5, 6]
```
```lean (name := rng3)
#eval (2<...=6).toList
```
```leanOutput rng3
[3, 4, 5, 6]
```
:::

:::example "有限范围和无限范围"
该范围不能转换为列表，因为它是无限的：
```lean (name := rng4) +error
#eval (3...*).toList
```
左闭右无界范围的有限性通过 {name}`Std.Rxi.IsAlwaysFinite` 实例的存在来指示，而 {name}`Nat` 不存在该实例。
{name}`Std.Rco` 是这些范围的类型，而名称 {name}`Std.Rxi.IsAlwaysFinite` 表明它决定了所有右无界范围的有限性。
```leanOutput rng4
failed to synthesize instance of type class
  Std.Rxi.IsAlwaysFinite Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

尝试枚举负整数会导致类似的错误，这次是因为无法确定最小元素：
```lean (name := intrange) +error
#eval (*...(0 : Int)).toList
```
```leanOutput intrange
failed to synthesize instance of type class
  Std.PRange.Least? Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

有限类型中的无界范围表示该范围延伸到该类型的最大元素。
因为 {name}`UInt8` 有 256 个元素，所以此范围包含 253 个元素：
```lean (name := uintrange)
#eval ((3 : UInt8)...*).toArray.size
```
```leanOutput uintrange
253
```

:::



:::syntax term (title := "范围语法")

该范围是左闭右开的，并指示 {name}`Std.Rco`：
```grammar
$a...$b
```

该范围是左闭右开的，并指示 {name}`Std.Rco`：
```grammar
$a...<$b
```

该范围是左闭右闭的，并指示 {name}`Std.Rcc`：
```grammar
$a...=$b
```

该范围是左闭右无限的，并指示 {name}`Std.Rci`：
```grammar
$a...*
```

该范围是左开右开的，并指示 {name}`Std.Roo`：
```grammar
$a<...$b
```

该范围是左开右开的，并指示 {name}`Std.Roo`：
```grammar
$a<...<$b
```

该范围是左开右闭的，并指示 {name}`Std.Roc`：
```grammar
$a<...=$b
```
该范围是左开右无限的，并指示 {name}`Std.Roi`：
```grammar
$a<...*
```
该范围是左无限右开的，并指示 {name}`Std.Rio`：
```grammar
*...$b
```

此范围左侧无界、右侧开放，表示 {name}`Std.Ric`：
```grammar
*...<$b
```

该范围是左无限右闭的，并指示 {name}`Std.Ric`：
```grammar
*...=$b
```

该范围两端都是无限的，并指示 {name}`Std.Rii`：
```grammar
*...*
```
:::

# 范围类型

%%%
tag := "Lean-__________________--Basic-Types--Ranges--Range-Types"
%%%
{docstring Std.Rco +allowMissing}

{docstring Std.Rco.iter}

{docstring Std.Rco.toArray}

{docstring Std.Rco.toList}

{docstring Std.Rco.size}

{docstring Std.Rco.isEmpty}

{docstring Std.Rcc +allowMissing}

{docstring Std.Rcc.iter}

{docstring Std.Rcc.toArray}

{docstring Std.Rcc.toList}

{docstring Std.Rcc.size}

{docstring Std.Rcc.isEmpty}

{docstring Std.Rci +allowMissing}

{docstring Std.Rci.iter}

{docstring Std.Rci.toArray}

{docstring Std.Rci.toList}

{docstring Std.Rci.size}

{docstring Std.Rci.isEmpty}

{docstring Std.Roo +allowMissing}

{docstring Std.Roo.iter}

{docstring Std.Roo.toArray}

{docstring Std.Roo.toList}

{docstring Std.Roo.size}

{docstring Std.Roo.isEmpty}

{docstring Std.Roc +allowMissing}

{docstring Std.Roc.iter}

{docstring Std.Roc.toArray}

{docstring Std.Roc.toList}

{docstring Std.Roc.size}

{docstring Std.Roc.isEmpty}

{docstring Std.Roi +allowMissing}

{docstring Std.Roi.iter}

{docstring Std.Roi.toArray}

{docstring Std.Roi.toList}

{docstring Std.Roi.size}

{docstring Std.Roi.isEmpty}

{docstring Std.Rio +allowMissing}

{docstring Std.Rio.iter}

{docstring Std.Rio.toArray}

{docstring Std.Rio.toList}

{docstring Std.Rio.size}

{docstring Std.Rio.isEmpty}

{docstring Std.Ric +allowMissing}

{docstring Std.Ric.iter}

{docstring Std.Ric.toArray}

{docstring Std.Ric.toList}

{docstring Std.Ric.size}

{docstring Std.Ric.isEmpty}

{docstring Std.Rii}

{docstring Std.Rii.iter}

{docstring Std.Rii.toArray}

{docstring Std.Rii.toList}

{docstring Std.Rii.size}

{docstring Std.Rii.isEmpty}

# 范围相关类型类

%%%
tag := "Lean-__________________--Basic-Types--Ranges--Range-Related-Type-Classes"
%%%
{docstring Std.PRange.UpwardEnumerable}

{docstring Std.PRange.UpwardEnumerable.LE}

{docstring Std.PRange.UpwardEnumerable.LT}

{docstring Std.PRange.LawfulUpwardEnumerable}

{docstring Std.PRange.Least?}

{docstring Std.PRange.InfinitelyUpwardEnumerable +allowMissing}

{docstring Std.PRange.LinearlyUpwardEnumerable +allowMissing}

{docstring Std.Rxi.IsAlwaysFinite +allowMissing}

{docstring Std.Rxi.HasSize}

{docstring Std.Rxc.IsAlwaysFinite +allowMissing}

{docstring Std.Rxc.HasSize}

# 实现范围

%%%
tag := "Lean-__________________--Basic-Types--Ranges--Implementing-Ranges"
%%%
内置范围类型可以与任何类型一起使用，但它们的实用性取决于某些类型类实例的存在。
一般来说，范围要么被检查成员资格，要么被枚举或迭代。
为了检查一个值是否包含在范围内，使用 {name}`DecidableLT` 和 {name}`DecidableLE` 实例来将该值与范围各自的开、闭端点进行比较。
要获取范围的迭代器，只需要 {name}`Std.PRange.UpwardEnumerable` 和 {name}`Std.PRange.LawfulUpwardEnumerable` 的实例。
为了在 {keywordOf Lean.Parser.Term.doFor}`for` 循环中直接对其进行迭代，还需要 {name}`Std.PRange.LawfulUpwardEnumerableLE` 和 {name}`Std.PRange.LawfulUpwardEnumerableLT`。
为了枚举一个范围（例如，通过调用 {name Std.Rco.toList}`toList`），必须证明它是有限的。
这是通过提供 {name}`Std.Rxi.IsAlwaysFinite`、{name}`Std.Rxc.IsAlwaysFinite` 或 {name}`Std.Rxo.IsAlwaysFinite` 的实例来完成的。

::::example "实现范围" (open := true)
枚举类型 {name}`Day` 表示一周中的每一天：
```lean
inductive Day where
  | mo | tu | we | th | fr | sa | su
deriving Repr
```

:::paragraph
```imports -show
import Std.Data.Iterators
```

虽然在范围中使用这种类型已经是可能的，但它们并不是特别有用。
没有成员资格实例：
```lean +error (name := noMem)
#eval Day.we ∈ (Day.mo...=Day.fr)
```
```leanOutput noMem
failed to synthesize instance of type class
  Membership Day (Std.Rcc Day)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
范围不能被迭代：
```lean +error (name := noIter)
#eval show IO Unit from
  for d in Day.mo...=Day.fr do
    IO.println s!"It's {repr d}"
```
```leanOutput noIter
failed to synthesize instance of type class
  ForIn IO (Std.Rcc Day) ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
也不能枚举它们，即使该类型是有限的：
```lean +error (name := noEnum)
#eval (Day.sa...*).toList
```
```leanOutput noEnum
failed to synthesize instance of type class
  Std.PRange.UpwardEnumerable Day

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

:::paragraph
成员资格测试需要 {name}`DecidableLT` 和 {name}`DecidableLE` 实例。
获取它们的简单方法是为每一天编号，然后比较数字：
```lean
def Day.toNat : Day → Nat
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

instance : LT Day where
  lt d1 d2 := d1.toNat < d2.toNat

instance : LE Day where
  le d1 d2 := d1.toNat ≤ d2.toNat

instance : DecidableLT Day :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat < d2.toNat))

instance : DecidableLE Day :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat ≤ d2.toNat))
```
:::

:::paragraph
有了这些实例，成员资格测试将如预期般工作：
```lean
def Day.isWeekday (d : Day) : Bool := d ∈ Day.mo...Day.sa
```
```lean (name := thursday)
#eval Day.th.isWeekday
```
```leanOutput thursday
true
```
```lean (name := saturday)
#eval Day.sa.isWeekday
```
```leanOutput saturday
false
```
:::

:::paragraph
迭代和枚举都是重复应用后继函数的变体，直到达到范围的上界或该类型的最大元素。
该后继函数是 {name}`Std.PRange.UpwardEnumerable.succ?`。
在 {name}`Day` 的命名空间中定义该函数以与广义字段表示法一起使用也很方便：
```lean
def Day.succ? : Day → Option Day
  | mo => some tu
  | tu => some we
  | we => some th
  | th => some fr
  | fr => some sa
  | sa => some su
  | su => none

instance : Std.PRange.UpwardEnumerable Day where
  succ? := Day.succ?
```
:::

迭代还需要证明 {name Std.PRange.UpwardEnumerable.succ?}`succ?` 的实现是合理的。
其属性根据 {name}`Std.PRange.UpwardEnumerable.succMany?` 来表达，它迭代应用 {name Std.PRange.UpwardEnumerable.succ?}`succ?` 若干次，并基于 {name}`Nat.repeat` 和 {name Std.PRange.UpwardEnumerable.succ?}`succ?` 具有默认实现。
特别地，{name Std.PRange.LawfulUpwardEnumerable}`LawfulUpwardEnumerable` 实例需要证明 {name}`Std.PRange.UpwardEnumerable.succMany?` 与默认实现相对应，同时证明重复应用后继函数永远不会再次产生相同的元素。

:::paragraph
第一步是为关于 {name Std.PRange.UpwardEnumerable.succMany?}`succMany?` 的两个证明编写两个辅助引理。
虽然它们可以内联在实例声明中编写，但为了方便起见，可以让它们具有 {attrs}`@[simp]` 属性。
```lean
@[simp]
theorem Day.succMany?_zero (d : Day) :
  Std.PRange.succMany? 0 d = some d := by
  simp [Std.PRange.succMany?, Nat.repeat]

@[simp]
theorem Day.succMany?_add_one (n : Nat) (d : Day) :
    Std.PRange.succMany? (n + 1) d =
    (Std.PRange.succMany? n d).bind Std.PRange.succ? := by
  simp [Std.PRange.succMany?, Nat.repeat, Std.PRange.succ?]
```

证明后继函数中没有循环，需要使用一个方便的辅助引理，该引理可以计算任意两天之间的后继步数。
它被标记为 {attrs}`@[grind →]`，因为当存在与其前提相匹配的假设时，它会添加大量的新信息：
```lean
@[grind →]
theorem Day.succMany?_steps {d d' : Day} {steps} :
    Std.PRange.succMany? steps d = some d' →
    if d ≤ d' then steps = d'.toNat - d.toNat
    else False := by
  intro h
  match steps with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    cases d <;> cases d' <;>
    simp_all +decide [Std.PRange.succMany?, Nat.repeat, Day.succ?]
  | n + 7 =>
    simp at h
    cases h' : (Std.PRange.succMany? n d) with
    | none =>
      simp_all
    | some d'' =>
      rw [h'] at h
      cases d'' <;> contradiction
```
有了这个辅助引理，证明就非常简短了：
```lean
instance : Std.PRange.LawfulUpwardEnumerable Day where
  ne_of_lt d1 d2 h := by grind [Std.PRange.UpwardEnumerable.LT]
  succMany?_zero := Day.succMany?_zero
  succMany?_add_one := Day.succMany?_add_one
```
:::

:::paragraph
证明三种可枚举范围是有限的，使得枚举天数范围成为可能：
```lean
instance : Std.Rxo.IsAlwaysFinite Day where
  finite init hi :=
    ⟨7, by cases init <;> simp [Std.PRange.succ?, Day.succ?]⟩

instance : Std.Rxc.IsAlwaysFinite Day where
  finite init hi :=
    ⟨7, by cases init <;> simp [Std.PRange.succ?, Day.succ?]⟩

instance : Std.Rxi.IsAlwaysFinite Day where
  finite init := ⟨7, by cases init <;> rfl⟩
```
```lean (name := allWeekdays)
def allWeekdays : List Day := (Day.mo...Day.sa).toList
#eval allWeekdays
```
```leanOutput allWeekdays
[Day.mo, Day.tu, Day.we, Day.th, Day.fr]
```
添加 {name}`Std.PRange.Least?` 实例允许枚举左无界范围：
```lean (name := allWeekdays')
instance : Std.PRange.Least? Day where
  least? := some .mo

def allWeekdays' : List Day := (*...Day.sa).toList
#eval allWeekdays'
```
```leanOutput allWeekdays'
[Day.mo, Day.tu, Day.we, Day.th, Day.fr]
```
也可以创建一个可以枚举的迭代器，但它还不能与 {keywordOf Lean.Parser.Term.doFor}`for` 一起使用：
```lean (name := iterEnum)
#eval (Day.we...Day.fr).iter.toList
```
```leanOutput iterEnum
[Day.we, Day.th]
```
```lean (name := iterForNo) +error
#eval show IO Unit from do
  for d in (Day.mo...Day.th).iter do
    IO.println s!"It's {repr d}."
```
```leanOutput iterForNo
failed to synthesize instance of type class
  ForIn IO (Std.Iter Day) ?α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::paragraph
启用迭代，从而使天的范围功能完备的最后一步是证明在 {name}`Day` 上的小于和小于等于关系对应于由迭代后继函数导出的不等式概念。
这被捕获在类 {name}`Std.PRange.LawfulUpwardEnumerableLT` 和 {name}`Std.PRange.LawfulUpwardEnumerableLE` 中，它们要求这两个概念在逻辑上是等价的：
```lean
instance : Std.PRange.LawfulUpwardEnumerableLT Day where
  lt_iff d1 d2 := by
    constructor
    . intro lt
      simp only [Std.PRange.UpwardEnumerable.LT, Day.succMany?_add_one]
      exists d2.toNat - d1.toNat.succ
      cases d1 <;> cases d2 <;>
      simp_all [Day.toNat, Std.PRange.succ?, Day.succ?] <;>
      contradiction
    . intro ⟨steps, eq⟩
      have := Day.succMany?_steps eq
      cases d1 <;> cases d2 <;>
      simp only [if_false_right] at this <;>
      cases this <;> first | decide | contradiction

instance : Std.PRange.LawfulUpwardEnumerableLE Day where
  le_iff d1 d2 := by
    constructor
    . intro le
      simp only [Std.PRange.UpwardEnumerable.LE]
      exists d2.toNat - d1.toNat
      cases d1 <;> cases d2 <;>
      simp_all [Day.toNat, Std.PRange.succ?, Day.succ?] <;>
      contradiction
    . intro ⟨steps, eq⟩
      have := Day.succMany?_steps eq
      cases d1 <;> cases d2 <;>
      simp only [if_false_right] at this <;>
      cases this <;> grind
```
:::

:::paragraph
现在就可以在天的范围上进行迭代了：
```lean (name := done)
#eval show IO Unit from do
  for x in (Day.mo...Day.th).iter do
    IO.println s!"It's {repr x}"
```
```leanOutput done
It's Day.mo
It's Day.tu
It's Day.we
```
:::

::::

# 范围与切片

%%%
tag := "Lean-__________________--Basic-Types--Ranges--Ranges-and-Slices"
%%%
范围语法可与支持切片的数据结构结合使用，以选择结构的一个切片。

:::example "列表切片"
列表可以使用任何区间类型进行切片：
```lean
def groceries :=
  ["apples", "bananas", "coffee", "dates", "endive", "fennel"]
```

```lean (name := rco)
#eval groceries[1...4] |>.toList
```
```leanOutput rco
["bananas", "coffee", "dates"]
```
```lean (name := rcc)
#eval groceries[1...=4] |>.toList
```
```leanOutput rcc
["bananas", "coffee", "dates", "endive"]
```
```lean (name := rci)
#eval groceries[1...*] |>.toList
```
```leanOutput rci
["bananas", "coffee", "dates", "endive", "fennel"]
```
```lean (name := roo)
#eval groceries[1<...4] |>.toList
```
```leanOutput roo
["coffee", "dates"]
```
```lean (name := roc)
#eval groceries[1<...=4] |>.toList
```
```leanOutput roc
["coffee", "dates", "endive"]
```
```lean (name := ric)
#eval groceries[*...=4] |>.toList
```
```leanOutput ric
["apples", "bananas", "coffee", "dates", "endive"]
```
```lean (name := rio)
#eval groceries[*...4] |>.toList
```
```leanOutput rio
["apples", "bananas", "coffee", "dates"]
```
```lean (name := rii)
#eval groceries[*...*] |>.toList
```
```leanOutput rii
["apples", "bananas", "coffee", "dates", "endive", "fennel"]
```


:::

:::example "自定义切片"
{name}`Triple` 包含三个相同类型的值：
```lean
structure Triple (α : Type u) where
  fst : α
  snd : α
  thd : α
deriving Repr
```
在三元组中的位置可以是任何字段，或就在 {name Triple.thd}`thd` 之后：
```lean
inductive TriplePos where
  | fst | snd | thd | done
deriving Repr
```
三元组的切片由三元组、起始位置和停止位置组成。
起始位置包含在范围内，停止位置不包含在范围内：
```lean
structure TripleSlice (α : Type u) where
  triple : Triple α
  start : TriplePos
  stop : TriplePos
deriving Repr
```
{name}`TriplePos` 的范围可用于从三元组中选择切片，方法是为每种受支持的范围类型实现 {name Std.Rco.Sliceable}`Sliceable` 类的实例。
例如，{name}`Std.Rco.Sliceable` 允许左闭右开范围被用来对 {name}`Triple` 进行切片：
```lean
instance : Std.Rco.Sliceable (Triple α) TriplePos (TripleSlice α) where
  mkSlice triple range :=
    { triple, start := range.lower, stop := range.upper }
```
```lean (name := slice)
def abc : Triple Char := ⟨'a', 'b', 'c'⟩

open TriplePos in
#eval abc[snd...thd]
```
```leanOutput slice
{ triple := { fst := 'a', snd := 'b', thd := 'c' }, start := TriplePos.snd, stop := TriplePos.thd }
```
无限范围只有下界：
```lean (name := slice2)
instance : Std.Rci.Sliceable (Triple α) TriplePos (TripleSlice α) where
  mkSlice triple range :=
    { triple, start := range.lower, stop := .done }

open TriplePos in
#eval abc[snd...*]
```
```leanOutput slice2
{ triple := { fst := 'a', snd := 'b', thd := 'c' }, start := TriplePos.snd, stop := TriplePos.done }
```

:::

{docstring Std.Rco.Sliceable +allowMissing}

{docstring Std.Rcc.Sliceable +allowMissing}

{docstring Std.Rci.Sliceable +allowMissing}

{docstring Std.Roo.Sliceable +allowMissing}

{docstring Std.Roc.Sliceable +allowMissing}

{docstring Std.Roi.Sliceable +allowMissing}

{docstring Std.Rio.Sliceable +allowMissing}

{docstring Std.Ric.Sliceable +allowMissing}

{docstring Std.Rii.Sliceable +allowMissing}
