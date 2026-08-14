/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
此示例提取到单独的文件中，因为错误消息会显示行号，而我们不希望在编辑大文件时
反复更新它。
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "良基递归预处理示例（供其他位置嵌入）" =>

::::example "自定义数据类型的预处理"

此示例演示了要为自定义容器类型启用自动良基递归，需要具备哪些内容。
结构类型 {name}`Pair` 是同质序对：它恰好包含两个类型相同的元素。
可以把它看作一种总是恰好包含两个元素的列表或数组。

作为容器，{name}`Pair` 可以支持 {name Pair.map}`map` 操作。
为了支持递归调用出现在映射到 {name}`Pair` 上的函数体内的良基递归，需要一些额外定义，包括成员关系谓词、关联成员大小与包含该成员的序对大小的定理、引入和消去成员关系假设的辅助函数、用于插入这些辅助函数的 {attr}`wf_preprocess` 规则，以及对 {tactic}`decreasing_trivial` 策略的扩展。
这些步骤都会使 {name}`Pair` 更易使用，但没有哪一步是严格必需的；不必立即为每种类型实现所有步骤。

```lean
/-- 同质序对 -/
structure Pair (α : Type u) where
  fst : α
  snd : α

/-- 将函数映射到序对的元素上 -/
def Pair.map (f : α → β) (p : Pair α) : Pair β where
  fst := f p.fst
  snd := f p.snd
```

定义一个使用 {name}`Pair` 的二叉树嵌套归纳数据类型，并尝试定义其 {name Tree.map}`map` 函数，可以说明预处理规则的必要性。

```lean
/-- 使用 `Pair` 定义的二叉树 -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Pair (Tree α) → Tree α
```

直接定义 {name Tree.map}`map` 函数会失败：

```lean +error -keep (name := badwf)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

```leanOutput badwf (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
p : Pair (Tree α)
t' : Tree α
⊢ sizeOf t' < 1 + sizeOf p
```

:::paragraph
```lean -show
section
variable (t' : Tree α) (p : Pair (Tree α))
```
这个证明义务显然无法解决，因为没有任何信息将 {lean}`t'` 与 {lean}`p` 联系起来。
```lean -show
end
```
:::

启用这类函数定义的标准惯用法，是使用一个函数为集合中的每个元素附上其确实属于该集合的证明。
陈述这一性质需要成员关系谓词。

```lean
inductive Pair.Mem (p : Pair α) : α → Prop where
  | fst : Mem p p.fst
  | snd : Mem p p.snd

instance : Membership α (Pair α) where
  mem := Pair.Mem
```

每个归纳类型都会自动拥有一个 {name}`SizeOf` 实例。
集合中的元素应当小于该集合，但必须先证明这一事实，才能用它构造终止性证明：

```lean
theorem Pair.sizeOf_lt_of_mem {α} [SizeOf α]
    {p : Pair α} {x : α} (h : x ∈ p) :
    sizeOf x < sizeOf p := by
  cases h <;> cases p <;> (simp; omega)
```

下一步是定义 {name Pair.attach}`attach` 和 {name Pair.unattach}`unattach` 函数：前者为序对中的元素附上其属于该序对的证明，后者则移除该证明。
这里，{name}`Pair.unattach` 的类型更为一般，可用于任意{ref "Subtype"}[子类型]；这是一种典型模式。

```lean
def Pair.attach (p : Pair α) : Pair {x : α // x ∈ p} where
  fst := ⟨p.fst, .fst⟩
  snd := ⟨p.snd, .snd⟩

def Pair.unattach {P : α → Prop} :
    Pair {x : α // P x} → Pair α :=
  Pair.map Subtype.val
```

现在可以通过显式使用 {name}`Pair.attach` 和 {name}`Pair.sizeOf_lt_of_mem` 来定义 {name Tree.map}`Tree.map`：

```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.attach.map (fun ⟨t', _⟩ => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all +arith
  omega
```

这一变换可以完全自动化。
可以使用良基递归的预处理功能，自动引入 {lean}`Pair.attach` 函数。
这分两个阶段完成。
首先，当 {name}`Pair.map` 应用于函数的某个形参时，将其重写为 {name Pair.attach}`attach`/{name Pair.unattach}`unattach` 组合。
然后，当一个函数被映射到 {name}`Pair.unattach` 的结果上时，将该函数重写为接收成员关系证明，并把该证明引入作用域。
```lean
@[wf_preprocess]
theorem Pair.map_wfParam (f : α → β) (p : Pair α) :
    (wfParam p).map f = p.attach.unattach.map f := by
  cases p
  simp [wfParam, Pair.attach, Pair.unattach, Pair.map]

@[wf_preprocess]
theorem Pair.map_unattach {P : α → Prop}
    (p : Pair (Subtype P)) (f : α → β) :
    p.unattach.map f =
    p.map fun ⟨x, h⟩ =>
      binderNameHint x f <|
      f (wfParam x) := by
  cases p; simp [wfParam, Pair.unattach, Pair.map]
```

现在编写函数体时无需额外考虑，而终止性证明仍可使用成员关系假设。

```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all
  omega
```

可以仿照类似的内置定理，将 {name Pair.sizeOf_lt_of_mem}`sizeOf_lt_of_mem` 添加到 {tactic}`decreasing_trivial` 策略中，使证明完全自动化。

```lean
macro "sizeOf_pair_dec" : tactic =>
  `(tactic| with_reducible
    have := Pair.sizeOf_lt_of_mem ‹_›
    omega
    done)

macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| sizeOf_pair_dec)

def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

为保持示例简短，{tactic}`sizeOf_pair_dec` 策略专门适配了这一特定递归模式，并不足以泛用于通用容器库。
不过，它确实说明了库在实践中可以和标准库中的容器类型一样方便。

::::
