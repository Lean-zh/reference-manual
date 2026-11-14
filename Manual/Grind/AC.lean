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

#doc (Manual) "结合律与交换律" =>
%%%
file := "Associativity-and-Commutativity"
tag := "grind-ac"
%%%

若一个运算满足结合律，{tactic}`grind` 就能高效地将包含它的项重写为范式，从而更容易证明涉及该运算的等式。
这种重写可以利用运算的其他性质，例如交换律、幂等性，或某些值是单位元这一事实。
在向“白板”添加项时，以及响应其他求解器添加的事实时，都会进行重写。
该求解器通过 `ac` 标志控制，默认启用。
`acSteps` 选项控制允许的 `ac` 重写步数，默认值为 `1000`。

:::example "字符串" (file := "Strings")
`ac` 求解器可以推理字符串。
字符串处理代码经常先计算一个前缀，然后再追加其他值。
使用 `ac` 可以更方便地对这类代码进行推理：
```lean
example (dir file p) (h : dir ++ "/" = p) :
    dir ++ ("/" ++ file) = p ++ file := by grind
```

```lean -show +error
-- To make sure it's AC solving this
example (dir file p) (h : dir ++ "/" = p) :
    dir ++ ("/" ++ file) = p ++ file := by grind -ac
```
:::

# 范式
%%%
file := "Normal-Forms"
tag := "Lean-__________________--grind--______--_____________________--______"
%%%

:::leanSection
```lean -show
variable {α : Type u} {op : α → α → α} [Std.Associative op] {u x y z : α}
```

`ac` 求解器使用的范式取决于为该运算注册的性质。

: 结合律

  满足结合律的运算通过将嵌套的运算树展开为操作数列表来规范化。
  若 {lean}`op` 满足结合律，则 {lean}`op (op x y) z` 和 {lean}`op x (op y z)` 的范式都是 {lean}`[x, y, z]`。

: 交换律

  同时满足结合律与交换律的运算通过对操作数列表排序来规范化。
  若 {lean}`op` 满足结合律与交换律，则 {lean}`op z (op x y)` 和 {lean}`op (op x z) y` 的范式都是 {lean}`[x, y, z]`。
  换言之，范式是一个多重集。

: 幂等性

  若运算满足幂等性，则操作数列表中连续重复的元素会被合并。
  若 {lean}`op` 满足结合律与幂等性，则 {lean}`op x (op x y)` 的范式是 {lean}`[x, y]`，但 {lean}`op (op x y) x` 的范式仍是 {lean}`[x, y, x]`。
  若运算还满足交换律，则会先排序再合并，因此当 {lean}`op` 同时满足结合律、交换律与幂等性时，{lean}`op (op x y) x` 的范式也是 {lean}`[x, y]`。
  换言之，满足结合律、交换律与幂等性的运算的范式是一个集合。

: 单位元

  若运算具有单位元，则范式会去除该单位元。
  也就是说，若 {lean}`u` 是结合运算 {lean}`op` 的单位元，则 {lean}`op x (op u y)` 的范式是 {lean}`[x, y]`。

:::


# 扩展
%%%
file := "Extension"
tag := "Lean-__________________--grind--______--_____________________--______-0"
%%%

通过为运算提供 {name}`Std.Associative` 实例，可以扩展 `ac` 求解器以支持新运算。
{name}`Std.Commutative`、{name}`Std.IdempotentOp` 和 {name}`Std.LawfulIdentity` 实例让求解器能够识别更多相等的项，进一步扩展其能力。

{zhdocstringFrom Std.Associative}

{zhdocstringFrom Std.Commutative}

{zhdocstringFrom Std.IdempotentOp}

{zhdocstringFrom Std.LawfulIdentity}

扩展 {lit}`ac` 求解器时，观察其运行过程可能很有帮助。
可以使用 {option}`trace.grind.ac` 选项及更具体的 {option}`trace.grind.ac.assert`、{option}`trace.grind.ac.internalize`、{option}`trace.grind.ac.basis` 选项来观察其内部行为。
其中，{option}`trace.grind.ac.assert` 显示添加到“白板”的规范化结果。

{zhOptionDocsFrom trace.grind.ac}

{zhOptionDocsFrom trace.grind.ac.assert}

{zhOptionDocsFrom trace.grind.ac.internalize}

{zhOptionDocsFrom trace.grind.ac.basis}

:::example "幂等性与单位元" (file := "Idempotence and Identity")

{name}`Flags` 跟踪一组布尔标志，每个标志对应一个二进制位。
每个标志要么置位，要么清除；当位值为 {lean}`0` 时，所有标志都被清除。
对两个标志集的位表示进行按位或运算，即可得到它们的并集。
```lean
structure Flags where
  bits : Nat

namespace Flags

def union (a b : Flags) : Flags := ⟨a.bits ||| b.bits⟩
def none : Flags := ⟨0⟩

```
标志集的并运算满足结合律、交换律与幂等性，且 {name}`Flags.none` 是单位元：
```lean
instance : Std.Associative union where
  assoc x y z := by simp only [union, mk.injEq]; grind
instance : Std.Commutative union where
  comm x y := by simp only [union, mk.injEq]; grind
instance : Std.IdempotentOp union where
  idempotent x := by simp [union]
instance : Std.LawfulIdentity union none where
  left_id a := by simp [union, none]
  right_id a := by simp [union, none]
```
有了这些实例，`ac` 求解器可以解决以下全部目标。
第二个示例中，两个相同的参数在原始项中并不相邻，因此必须利用交换律才能使用幂等性。
```lean
example : union a (union b c) = union (union c a) b := by grind
example : union (union a b) a = union a b := by grind
example : union a none = a := by grind
example :
    union (union a b) (union none (union b c))
      = union a (union b c) := by
  grind
```
使用 {option}`trace.grind.ac.assert` 可以查看加入上下文的、带否定的范式等式：
```lean (name := traceAc)
set_option trace.grind.ac.assert true in
example : union (union a b) a = union a (union b none) := by grind
```
```leanOutput traceAc
[grind.ac.assert] a.union b ≠ a.union b
```

```lean -show
-- check solver
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union a (union b c) = union (union c a) b := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union (union a b) a = union a b := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union a none = a := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example :
    union (union a b) (union none (union b c))
      = union a (union b c) := by grind -ac

```

:::

::::example "差分列表" (tag := "difference-lists-ac") (file := "Difference Lists")

{deftech (key := "difference list")}_差分列表_用函数巧妙地表示列表，避免了反复在列表尾部追加元素所导致的二次开销。
由于 Lean 支持{ref "Array"}[高效数组]，日常代码通常不需要差分列表，但它们可以清楚地展示如何扩展 `ac` 求解器。

:::leanSection
```lean -show
variable {xs ys : List α}
```
差分列表是从列表到列表的函数。
列表 {lean}`xs` 被表示为一个函数，将其应用于 {lean}`ys` 会返回 {lean}`xs ++ ys`。
:::

```lean
def DList α := List α → List α
```

空列表由恒等函数表示。
要在列表开头添加元素，只需创建一个添加该元素的函数。
两个列表的追加操作对应函数复合。
```lean
def DList.empty : DList α := id

def DList.cons (x : α) (xs : DList α) : DList α :=
  fun ys => (x :: xs ys)

instance : Append (DList α) where
  append xs ys := xs ∘ ys
```

由于定义相等性包含函数的 β 与 η 定律，差分列表追加运算的结合律以及空差分列表为其左、右单位元的性质都可以通过自反性证明：
```lean
instance : Std.Associative (α := DList α) (· ++ ·) where
  assoc xs ys zs := by rfl

instance : Std.LawfulIdentity (α := DList α) (· ++ ·) .empty where
  left_id xs := by rfl
  right_id xs := by rfl
```

有了这些实例，{tactic}`grind` 就可以解决许多证明。
```lean
variable (a b c d x y : DList Nat)
```

由于追加满足结合律，可以重新组合项的括号，并去除单位元：
```lean
example : ((a ++ b) ++ c) ++ d = a ++ (b ++ (c ++ d)) := by grind

example : (a ++ .empty) ++ (.empty ++ b) = a ++ b := by grind

example : (.empty ++ .empty : DList Nat) = .empty := by grind
```

虽然{ref "simp-rewrites"}[简化引理]也能轻松解决这些问题，但 {tactic}`grind` 的 `ac` 求解器更加灵活。
要利用以下示例中的假设，仅仅将目标和假设重写为右结合的范式是不够的：
```lean
example (h : a ++ b = x) : a ++ (b ++ c) = x ++ c := by grind

example (h : a ++ b = x) :
    (a ++ .empty) ++ (b ++ c) = x ++ c := by grind

example (h₁ : a ++ b = x) (h₂ : x ++ c = y) :
    a ++ (b ++ c) = y := by grind
```
由于差分列表的追加运算不满足交换律，顺序仍然重要：
```lean +error (name := grindErr)
example : a ++ b = b ++ a := by grind
```
```leanOutput grindErr
`grind` failed
case grind
a b c d x y : DList Nat
h : ¬a ++ b = b ++ a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [assoc] Operator `HAppend.hAppend`
```
::::

# 排除项
%%%
file := "Exclusions"
tag := "Lean-__________________--grind--______--_____________________--_________"
%%%

`ac` 求解器不处理某些内置运算，具体包括 {name}`And`、{name}`Or` 和 {name}`Iff`。
{tactic}`grind` 的其他功能更适合处理它们。
当操作数类型具有 {name}`Lean.Grind.CommRing` 和/或 {name}`Lean.Grind.CommSemiring` 实例时，`ac` 会省略通常由{ref "grind-ring"}[`ring` 求解器]处理得更好的运算规则，即 `+`、`-`、`*`、`/` 和 `^`。

```lean -show
-- `And` and `Or` have `Std.Associative` instances, so the exclusion is
-- what stops the `ac` solver from claiming them.
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Prop) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := by grind

#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := by grind

-- Likewise `+` and `*`, which are left to the arithmetic solvers.
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Nat) : a + (b + c) = (c + a) + b := by grind

#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Nat) : a * (b * c) = (c * a) * b := by grind
```
