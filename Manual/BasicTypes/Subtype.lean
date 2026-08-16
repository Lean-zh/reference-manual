/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "子类型" =>
%%%
tag := "Subtype"
file := "Subtypes"
%%%

结构体 {name}`Subtype` 表示某个类型中满足某个谓词的元素。
它在数学与编程中都被广泛使用；在数学中，它的用法类似于子集；在编程中，它允许将关于某个值的已知信息表示为 Lean 逻辑可见的形式。

从语法上看，{name}`Subtype` 的一个元素类似于由底层类型中的值及其满足该命题的证明所组成的元组。
它与依值有序对类型（{name}`Sigma`）的区别在于第二个元素是命题的证明而非数据；它与存在量化的区别在于整个 {name}`Subtype` 是一个类型而不是命题。
尽管它在语法上是一个有序对，{name}`Subtype` 实际上更应被看作“带有关联证明义务的底层类型元素”。

子类型是 {ref "inductive-types-trivial-wrappers"}[平凡包装器]。
因此，在编译后的代码中，它们与底层类型具有完全相同的表示。


{zhdocstring Subtype Manual.ZhDocString.Ch19Ch20.G9.c207}

::::leanSection
```lean -show
variable {α : Type u} {p : Prop}
```
:::syntax term (title := "子类型")
```grammar
{ $x : $t:term // $t:term }
```

{lean}`{ x : α // p }` 是 {lean}`Subtype fun (x : α) => p` 的记法。

类型标注也可以省略：

```grammar
{ $x:ident // $t:term }
```

{lean}`{ x // p }` 是 {lean}`Subtype fun (x : _) => p` 的记法。
:::
::::

由于 {tech (key := "proof irrelevance")}[证明无关性] 和 {tech (key := "η-equivalence")}[η-等价]，当底层类型中的元素定义等价时，子类型中的两个元素也定义等价。
在证明中，可以使用 {tactic}`ext` 策略将“两个子类型元素相等”的目标化为“它们的值相等”的目标。

:::example "子类型的定义等价"

尽管内嵌的证明项不同，非空字符串 {lean}`s1` 和 {lean}`s2` 仍然定义等价。
因此，要证明它们相等，不需要做任何分类讨论。

```lean
def NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.ext_iff.mp h)

theorem s1_eq_s2 : s1 = s2 := by rfl
```
:::

:::example "子类型的外延相等"

非空字符串 {lean}`s1` 与 {lean}`s2` 本身就是定义等价的。
即便不利用这一事实，也可以通过它们内部字符串的相等来证明二者相等。
{tactic}`ext` 策略会把“非空字符串相等”的目标转化为“底层字符串相等”的目标。

```lean
abbrev NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.ext_iff.mp h)

theorem s1_eq_s2 : s1 = s2 := by
  ext
  dsimp only [s1, s2]
  rfl
```
:::

存在从子类型到底层类型的强制转换。
这使得子类型可以用在期望底层类型的地方，本质上等于擦除了“该值满足谓词”的证明。

:::example "子类型强制转换"

子类型中的元素可以强制转换为其底层类型。
这里，{name}`nine` 从 `Nat` 中包含 {lean  (type := "Nat")}`3` 的倍数的子类型，被强制转换成了 {lean}`Nat`。

```lean (name := subtype_coe)
abbrev DivBy3 := { x : Nat // x % 3 = 0 }

def nine : DivBy3 := ⟨9, by rfl⟩

set_option eval.type true in
#eval Nat.succ nine
```
```leanOutput subtype_coe
10 : Nat
```

:::
