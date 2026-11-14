/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Upstream
import Manual.Papers


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External (lit)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "同态标注" =>
%%%
file := "Homomorphism-Annotations"
tag := "grind-hom"
%%%

::::keepEnv
```lean -show
axiom T : Type
axiom U : Type
variable {x y : T} [LE T] [LE U] [LT T] [LT U] [OfNat T n]
axiom T.toU : T → U
axiom f : T → T → T
axiom g : U → U → U
axiom h : Nat → U
variable {p : Prop} [Decidable p]
```

通过定义从新领域到已有专用求解器所支持领域的映射，可以扩展 {tactic}`grind` 以处理新领域。
这种扩展由一个_同态_构成，即从新领域到既有领域的保结构转换。
换言之，为 {lean}`T` 定义满足特定性质的映射 {name}`T.toU`，将其映射到 {lean}`U`，就能让 {tactic}`grind` 利用 {lean}`U` 的现有求解器推理新类型 {lean}`T`。
Lean 为 {name}`Fin`、{name}`BitVec`、{name}`UInt8`–{name}`UInt64`、{name}`USize`、{name}`Int8`–{name}`Int64` 和 {name}`ISize` 提供同态重写规则，将它们重写到{ref "cutsat"}[`lia` 求解器的]领域。
此外，还会映射 {name}`String.Pos` 的不等关系与字节索引界，使 {tactic}`grind` 能够推理字符串位置。
同态重写由 {tactic}`grind` 的 `hom` 标志控制，默认启用。

```lean -show
-- These tests check the claims made just above: that each listed
-- type really is a homomorphism source type in this version of
-- Lean, and that `Nat` is not.
--
-- Each example proves an equality of the source type from an
-- equality of the images. Only the `=`-injection licenses that
-- step, so the example fails if the type loses its rules.
--
-- The trace assertions confirm that the homomorphism engine is
-- what did the work, rather than some other solver. Two quirks:
-- `trace.grind.hom.pred` is registered as inherited, so it must
-- be switched off explicitly or `Fin` also reports its range
-- facts; and `substring := true` still anchors the `trace:`
-- prefix, so the expected text must be a prefix of the message.

-- `Fin` and `BitVec` inject directly into `Nat`, so the negated
-- goal is the only thing translated.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] ¬a = b -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Fin 8) (h : a.val = b.val) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] ¬a = b -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : BitVec 8) (h : a.toNat = b.toNat) : a = b := by
  grind

-- The fixed-width integer types inject through `BitVec`, so the
-- hypothesis is translated as well as the goal.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt8) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt16) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt32) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt64) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : USize) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int8) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int16) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int32) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int64) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : ISize) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

-- `String.Pos` injects via its offset, then the byte index.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] p.offset = q.offset -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (s : String) (p q : s.Pos) (h : p.offset = q.offset) :
    p = q := by
  grind

-- `Nat` is not a source type: `cutsat` handles it natively, so
-- unlike the types above, these still succeed with `-hom`.
example (a b c : Nat) : a + (b + c) = (c + a) + b := by grind -hom
example (a b : Nat) (h : a ≤ b) (h₂ : b ≤ a) : a = b := by
  grind -hom
```


要使用此功能，映射首先必须对相等关系具有单射性。
也就是说，对 {lean}`T` 类型的 {lean}`x` 和 {lean}`y`，{lean}`x = y` 应与 {lean}`x.toU = y.toU` 逻辑等价。
给合适的单射性定理添加 {attr}`grind hom` 属性，即可启用此映射功能。

:::paragraph
要使映射有用，它应将 {lean}`T` 上所关注的运算转换为 {lean}`U` 上受 {tactic}`grind` 求解器支持的运算。
{attr}`grind hom` 属性可以添加到以下种类的定理上：

* 要将 {lean}`f` 转换为 {lean}`g`，应有 {lean}`(f x y).toU = g x.toU y.toU`。
* 可以通过证明 {lean}`x ≤ y ↔ x.toU ≤ y.toU` 和 {lean}`x < y ↔ x.toU < y.toU` 来转换序关系。
* 可以通过提供将数值字面量转换为取值于 {lean}`U` 的函数的定理来转换字面量。
  具体做法是为形如 {lean}`(OfNat.ofNat n : T).toU = h n` 的定理添加 {attr}`grind hom` 属性。
* 可以通过提供证明 {lean}`(if p then x else y).toU = if p then x.toU else y.toU` 的定理来转换条件表达式。

最后，还可以提供回退规则，在其他规则均未能重写某个项后应用。
这通常用于原本会与其他规则重叠的规则。
:::

给引理添加 {attr}`grind hom_pred` 标注，可以提供关于映射值域的额外事实。
这通常用于限制值域，例如断言 {name}`Fin.val` 的目标值小于对应 {name}`Fin` 的上界。
当这些引理所提及的常量出现在本身未被 {attr}`grind hom` 规则重写的项中时，就会实例化这些引理。
::::

同态引理在将陈述加入共享“白板”之前应用，而不是在求解器运行期间反复应用。
这可以高效得多。
由于映射为单射，新类型中项的_不等_蕴含求解器领域中对应项的不等，因此即使映射不是双射，也能直接使用 {tactic}`grind` 对陈述取反再推导矛盾的策略。
由于同态引理仅在流程很早的阶段运行，应用时不会使用旁条件证明器。
因此，它们不允许需要额外证明的条件重写（但仍可用实例隐式假设作为条件；若命题假设完全由左侧决定，也允许使用）。

同态规则使用三个属性声明：{attr}`grind hom`、{attr}`grind hom fallback` 和 {attr}`grind hom_pred`。
这些属性分别注册同态规则、其他 {attr}`grind hom` 规则不适用时尝试的回退规则，以及关于映射值域的事实。

:::syntax attr (title := "同态规则")
```grammar
grind hom
```
{zhincludeDocstringFrom Lean.Parser.Attr.grindHom}
:::

:::syntax attr (title := "回退同态规则")
```grammar
grind hom fallback
```
{zhincludeDocstringFrom Lean.Parser.Attr.grindHomFallback}
:::

:::syntax attr (title := "同态谓词")
```grammar
grind hom_pred
```
{zhincludeDocstringFrom Lean.Parser.Attr.grindHomPred}
:::


调试时，将 {option}`trace.grind.hom` 或 {option}`trace.grind.hom.pred` 设为 `true`，即可观察同态重写。

{zhOptionDocsFrom trace.grind.hom}

{zhOptionDocsFrom trace.grind.hom.pred}

:::example "极小整数"

极小数（即零到三的整数）可以用具有四个构造器的归纳类型表示：

```lean
inductive Tiny where
  | zero
  | one
  | two
  | three
```

```lean
namespace Tiny
```

提供几个实例后，就可以为 {name}`Tiny` 使用数值字面量：
```lean
instance : Zero Tiny where
  zero := .zero

instance : One Tiny where
  one := .one

instance : OfNat Tiny 2 where
  ofNat := .two

instance : OfNat Tiny 3 where
  ofNat := .three
```

它们可以与 {name}`Nat` 相互转换：
```lean
def toNat : Tiny → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3

def ofNat : (n : Nat) → n < 4 → Tiny
  | 0, _ => 0
  | 1, _ => 1
  | 2, _ => 2
  | 3, _ => 3
```

也可以互相比较：
```lean
instance : LE Tiny where
  le x y := x.toNat ≤ y.toNat

instance : LT Tiny where
  lt x y := x.toNat < y.toNat
```

{name}`Tiny.toNat` 是单射映射：
```lean
@[grind hom]
theorem eq_iff_toNat_eq (x y : Tiny) : x = y ↔ x.toNat = y.toNat := by
  cases x <;> cases y <;> simp [toNat]
```

类似地，由于 {inst}`LE Tiny` 和 {inst}`LT Tiny` 实例用 {name}`Nat` 上的对应实例定义，相应关系逻辑等价：
```lean
@[grind hom]
theorem le_iff_toNat_le (x y : Tiny) : x ≤ y ↔ x.toNat ≤ y.toNat := by
  rfl
@[grind hom]
theorem lt_iff_toNat_lt (x y : Tiny) : x < y ↔ x.toNat < y.toNat := by
  rfl
```

将 {name}`Tiny` 数转换为 {name}`Nat` 时，结果始终小于四。
给该事实的证明添加 {attr}`grind hom_pred` 属性后，只要 {name}`Tiny.toNat` 用于一个加入“白板”但未被 {attr}`grind hom` 规则重写的项，{tactic}`grind` 就会引入此事实：
```lean
@[grind hom_pred]
theorem toNat_lt_4 (x : Tiny) : x.toNat < 4 := by
  cases x <;> simp [toNat]
```

像 {name}`Tiny` 这样的有限类型，必须决定越界运算的含义。
这里将 {name}`Tiny.succ` 和加法定义为截断运算；模运算则是另一种合法实现。
```lean
def succ (x : Tiny) : Tiny :=
  match x with
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three => .three

instance : Add Tiny where
  add
  | .zero, y => y
  | .one, y => y.succ
  | .two, y => y.succ.succ
  | .three, y => y.succ.succ.succ
```

自然数加法不会截断，因此看起来很自然的做法是：先要求加法结果未被截断，再将其映射为自然数加法。
然而，这会产生错误：
```lean +error (name := homNoH)
@[grind hom]
theorem toNat_add_lt_4_eq_add (x y : Tiny)
    (h : x.toNat + y.toNat < 4) :
    (x + y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> simp [toNat] at h <;> rfl
```
```leanOutput homNoH
invalid `[grind hom]` theorem, `toNat_add_lt_4_eq_add` is conditional: hypothesis
  x.toNat + y.toNat < 4
is not determined by the left-hand side and would have to be discharged when the rule is applied. Homomorphism rules must be unconditional; use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems
```
这是因为条件重写不被允许；同态功能在 {tactic}`grind` 中应用得太早，无法支持它。

可以改为将极小数的加法映射为自然数上的截断加法：
```lean
@[grind hom]
theorem toNat_add_eq_add (x y : Tiny) :
    (x + y).toNat = min (x.toNat + y.toNat) 3 := by
  cases x <;> cases y <;> rfl
```
给定这些定义，我们可能预期下面的示例成功，但它并未成功：
```lean +error (name := noLits)
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
检查 {tactic}`grind` 的输出发现，问题在于它未能成功登记对 {lean}`(2 : Tiny) + (1 : Tiny) = (3 : Tiny)` 取反所产生的矛盾。
原因是重写过程不会重写 {lean (type := "Tiny")}`2` 这样的字面量（即 {lean}`OfNat.ofNat (α := Tiny) 2`），而将它们原样保留：
```leanOutput noLits
`grind` failed
case grind.1
h : ¬2 + 1 = 3
h_1 : toNat 1 + toNat 2 ≤ 3
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [assoc] Operator `min`

[grind] Diagnostics
```

将 {option}`trace.grind.hom` 设为 `true`，可以查看同态引理执行的重写，以及添加的 {attr}`grind hom_pred` 事实：
```lean +error (name := noLits')
set_option trace.grind.hom true in
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
```leanOutput noLits'
[grind.hom] ¬2 + 1 = 3
    ===>
    ¬min (toNat 2 + toNat 1) 3 = toNat 3
[grind.hom.pred] toNat 1 < 4
[grind.hom.pred] toNat 2 < 4
[grind.hom.pred] toNat 3 < 4
```

为每个受支持的字面量提供规则，即可修复该问题：
```lean
@[grind hom]
theorem toNat_zero_eq_zero : (0 : Tiny).toNat = 0 := by simp [toNat]
@[grind hom]
theorem toNat_one_eq_one : (1 : Tiny).toNat = 1 := by simp [toNat]
@[grind hom]
theorem toNat_two_eq_two : (2 : Tiny).toNat = 2 := by simp [toNat]
@[grind hom]
theorem toNat_three_eq_three : (3 : Tiny).toNat = 3 := by simp [toNat]
```

随后，证明就会成功，下面这个涉及加法截断行为的证明也能成功：
```lean
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind

example : (3 : Tiny) + (3 : Tiny) = (3 : Tiny) := by grind
```

启用 {option}`trace.grind.hom` 可发现 {attr}`grind hom_pred` 规则不再触发，因为所有 {name}`Tiny` 类型的子项现在都被重写了：
```lean (name := withLits)
set_option trace.grind.hom true in
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
```leanOutput withLits
[grind.hom] ¬2 + 1 = 3
    ===>
    ¬min 3 3 = 3
```
:::




:::example "差分列表" (tag := "difference-lists-hom")

差分列表将列表表示为函数，{ref "difference-lists-ac" (domain := Manual.examples)}[提供满足结合律的追加运算]。
通过 {attr}`grind hom` 将它们视为列表来推理很有吸引力；但默认的函数表示不具有所需的单射性：
```lean
namespace NotInj
def DList α := List α → List α
def DList.toList (xs : DList α) : List α := xs []

theorem DList.not_toList_inj :
    (∀ (α : Type) (xs ys : DList α), xs = ys ↔ xs.toList = ys.toList) →
    False := by
  intro h
  let l1 : DList Nat := fun xs => 1 :: 2 :: xs
  let l2 : DList Nat := fun _ => [1, 2]
  have : l1 ≠ l2 := by
    intro h
    have := congrFun h [3]
    simp [l1, l2] at this
  have toList_eq : l1.toList = l2.toList := rfl
  have := h Nat l1 l2 |>.mpr toList_eq
  contradiction

end NotInj
```

换言之，Lean 的函数类型包含一些实际上并非差分列表的函数。
要为差分列表使用 {attr}`grind hom`，就需要额外结构以排除这些反例：
```lean
@[ext]
structure DList α where
  appendTail : List α → List α
  wf : ∀ xs, appendTail xs = appendTail [] ++ xs

def DList.toList (xs : DList α) : List α :=
  xs.appendTail []
```
这一额外的良构性质排除了无效情形：
```lean
theorem DList.ext_toList (xs ys : DList α) (h : xs.toList = ys.toList) :
    xs = ys := by
  have : xs.appendTail = ys.appendTail := by
    funext zs
    rw [xs.wf, ys.wf]
    exact congrArg (· ++ zs) h
  cases xs; cases ys; simp_all

@[grind hom]
theorem DList.toList_inj (xs ys : DList α) :
    xs = ys ↔ xs.toList = ys.toList := by
  constructor
  . intro h; rw [h]
  . apply DList.ext_toList
```

现在可以将差分列表运算转换为列表运算：
```lean
def DList.nil : DList α where
  appendTail xs := xs
  wf := by simp

@[grind hom]
theorem DList.nil_toList : (.nil : DList α).toList = [] := by
  simp_all [nil, toList]

def DList.cons (x : α) (xs : DList α) : DList α where
  appendTail ys := x :: xs.appendTail ys
  wf ys := by
    simp only [List.cons_append, List.cons.injEq, true_and]
    apply xs.wf

@[grind hom]
theorem DList.cons_toList :
    (DList.cons x xs).toList = x :: xs.toList := by
  simp [cons, toList]

instance : Append (DList α) where
  append xs ys := {
    appendTail := xs.appendTail ∘ ys.appendTail
    wf zs := by
      have := xs.wf
      have := ys.wf
      grind
  }

@[grind hom]
theorem DList.append_toList {xs ys : DList α} :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  apply xs.wf
```

现在，{tactic}`grind` 能够推理差分列表的性质，以及差分列表与普通列表之间的转换：

```lean
variable (a b c : DList Nat)

example : (a ++ b) ++ c = a ++ (b ++ c) := by grind

example : a ++ .nil = a := by grind

example : .nil ++ a = a := by grind

example (h₁ : a.toList = [1,2]) (h₂ : b.toList = [3]) :
    (a ++ b).toList = [1,2,3] := by grind

example (h : a.toList = []) : a = .nil := by grind
```

```lean -show
-- The examples fail without hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : (a ++ b) ++ c = a ++ (b ++ c) := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : a ++ .nil = a := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : .nil ++ a = a := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (h₁ : a.toList = [1,2]) (h₂ : b.toList = [3]) :
    (a ++ b).toList = [1,2,3] := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (h : a.toList = []) : a = .nil := by grind -hom
```

更进一步，还可以显式使用额外的 {name}`List` 引理来推理差分列表：

```lean
example (h : a ++ b = a ++ c) : b = c := by
  grind [List.append_cancel_left]

example (h : a ++ c = b ++ c) : a = b := by
  grind [List.append_cancel_right]

example (h : a ++ b = .nil) : a = .nil := by
  grind [List.append_eq_nil_iff]
```
:::

:::example "一天中的时刻"

时刻可以用小时和分钟表示：

```lean
structure Time where
  hour : Fin 24
  minute : Fin 60
```

```lean
namespace Time
```

每个时刻都可以表示为从午夜起经过的分钟数。
这种表示并不唯一，因为超过一天的分钟数会回绕到次日的某个时刻。

```lean
def toMinutes (t : Time) : Nat :=
  t.hour.val * 60 + t.minute.val

def ofMinutes (n : Nat) : Time where
  hour := ⟨n / 60 % 24, by grind⟩
  minute := ⟨n % 60, by grind⟩
```

将两个时刻相加不太合理，但给时刻加上若干分钟以得到更晚的时刻，则完全合理。
```lean
def addMinutes (t : Time) (n : Nat) : Time :=
  ofMinutes (t.toMinutes + n)
```

若一个时刻在一天中出现得更早，就称它小于另一个时刻。
```lean
instance : LT Time where
  lt a b := a.toMinutes < b.toMinutes
```

使用 {attr}`grind hom`，可以将这些运算直接映射到自然数。

```lean
@[grind hom]
theorem eq_iff_toMinutes_eq (a b : Time) :
    a = b ↔ a.toMinutes = b.toMinutes := by
  constructor
  · intro h; rw [h]
  · obtain ⟨⟨h₁, _⟩, ⟨m₁, _⟩⟩ := a
    obtain ⟨⟨h₂, _⟩, ⟨m₂, _⟩⟩ := b
    simp only [toMinutes, mk.injEq, Fin.mk.injEq]
    grind

@[grind hom]
theorem lt_iff_toMinutes_lt (a b : Time) :
    a < b ↔ a.toMinutes < b.toMinutes := by
  rfl

@[grind hom]
theorem toMinutes_addMinutes (t : Time) (n : Nat) :
    (t.addMinutes n).toMinutes =
      (t.toMinutes + n) % 1440 := by
  have := t.hour.isLt
  have := t.minute.isLt
  simp only [addMinutes, ofMinutes, toMinutes]
  grind
```

然而，没有规则将关于 {name}`Time` 字段的事实关联到分钟计数。
这会使 {tactic}`grind` 在推理这些字段时失败：

```lean +error
example (a b : Time) (h : a.hour < b.hour) : a < b := by
  grind
```

一种解决方法是将 {name}`toMinutes` 的定义等式作为 {attr}`grind hom` 规则。
使用该规则会将_所有_ {name}`toMinutes` 的应用重写为关于时刻字段值的表达式。

```lean
theorem toMinutes_eq (t : Time) :
    t.toMinutes = t.hour.val * 60 + t.minute.val := by
  rfl

attribute [local grind hom] toMinutes_eq in
example (a b : Time) (h : a.hour < b.hour) : a < b := by
  grind
```

遗憾的是，在某些本应使用更具体规则的情况下，这条规则也会应用。
它作为回退规则很有用，但在可用其他规则时并非最佳选择。
特别地，它优先于 {name}`toMinutes_addMinutes`，导致下面的证明失败：

```lean +error (name := timeOrdinary)
attribute [local grind hom] toMinutes_eq in
set_option trace.grind.hom true in
example (t : Time) (h : t.hour < 23) :
    t < t.addMinutes 60 := by
  grind
```
```leanOutput timeOrdinary
[grind.hom.pred] ↑t.hour < 24
[grind.hom] t.hour < 23
    ===>
    ↑t.hour ≤ 22
[grind.hom.pred] ↑t.minute < 60
[grind.hom.pred] ↑(t.addMinutes 60).hour < 24
[grind.hom.pred] ↑(t.addMinutes 60).minute < 60
[grind.hom] t < t.addMinutes 60
    ===>
    60 * ↑t.hour + ↑t.minute + 1 ≤ 60 * ↑(t.addMinutes 60).hour + ↑(t.addMinutes 60).minute
```

解决方法是将 {name}`toMinutes_eq` 添加为回退规则：

```lean
attribute [grind hom fallback] toMinutes_eq
```

```lean (name := timeFallback)
set_option trace.grind.hom true in
example (t : Time) (h : t.hour < 23) :
    t < t.addMinutes 60 := by
  grind
```
```leanOutput timeFallback
[grind.hom.pred] ↑t.hour < 24
[grind.hom] t.hour < 23
    ===>
    ↑t.hour ≤ 22
[grind.hom.pred] ↑t.minute < 60
[grind.hom] t < t.addMinutes 60
    ===>
    60 * ↑t.hour + ↑t.minute + 1 ≤ (60 * ↑t.hour + ↑t.minute + 60) % 1440
```

设置回退规则后，所有这些证明都能成功：

```lean
example (t : Time) : t.addMinutes 1440 = t := by
  grind

example (t : Time) (m n : Nat) :
    (t.addMinutes m).addMinutes n =
      t.addMinutes (m + n) := by
  grind

example (t : Time) (h : t.hour = 23) (h' : t.minute = 59) :
    t.addMinutes 1 = ⟨0, 0⟩ := by
  grind
```
:::
