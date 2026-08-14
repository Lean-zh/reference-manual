/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "递归示例（供其他位置嵌入）" =>


:::example "所有较小值递归表"
此定义等价于 {name}`List.below`：
```lean
def List.below' {α : Type u} {motive : List α → Sort u} :
    List α → Sort (max (u + 1) u)
  | [] => PUnit
  | _ :: xs => motive xs ×' xs.below' (motive := motive)
```

```lean -show
theorem List.below_eq_below' : @List.below = @List.below' := by
  funext α motive xs
  induction xs <;> simp [below']
  congr
```

换言之，对于给定的{tech (key := "motive")}[动机]，{lean}`List.below'` 是一个包含该动机在列表所有后缀上的实现的类型。

递归参数越多，就需要对积类型进行更深层的嵌套迭代。
例如，二叉树有两个递归出现。
```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
```

其对应的所有较小值递归表包含该动机在所有子树上的实现：
```lean
def Tree.below' {α : Type u} {motive : Tree α → Sort u} :
    Tree α → Sort (max (u + 1) u)
  | .leaf => PUnit
  | .branch left _val right =>
    (motive left ×' left.below' (motive := motive)) ×'
    (motive right ×' right.below' (motive := motive))
```

```lean -show
theorem Tree.below_eq_below' : @Tree.below = @Tree.below' := by
  funext α motive t
  induction t
  next =>
    simp [Tree.below']
  next ihl ihr =>
    simp [Tree.below', ihl, ihr]

```

对于列表和树，`brecOn` 运算符都只要求一个分支，而不是每个构造器各有一个分支。
该分支接收一个列表或树，以及所有较小值的结果表；它应据此满足所给值的动机。
对所给值进行依赖分情况分析会自动精化记忆表的类型，从而提供所需的一切。

以下定义分别等价于 {name}`List.brecOn` 和 {name}`Tree.brecOn`。
原始递归辅助函数 {name}`List.brecOnTable` 和 {name}`Tree.brecOnTable` 在计算最终结果的同时计算所有较小值递归表，而 `brecOn` 运算符的实际定义只是投影出结果。
```lean
def List.brecOnTable {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs ×' xs.below' (motive := motive) :=
  match xs with
  | [] => ⟨step [] PUnit.unit, PUnit.unit⟩
  | x :: xs =>
    let res := xs.brecOnTable (motive := motive) step
    let val := step (x :: xs) res
    ⟨val, res⟩
```

```lean
def Tree.brecOnTable {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t ×' t.below' (motive := motive) :=
  match t with
  | .leaf => ⟨step .leaf PUnit.unit, PUnit.unit⟩
  | .branch left val right =>
    let resLeft := left.brecOnTable (motive := motive) step
    let resRight := right.brecOnTable (motive := motive) step
    let branchRes := ⟨resLeft, resRight⟩
    let val := step (.branch left val right) branchRes
    ⟨val, branchRes⟩
```

```lean
def List.brecOn' {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs :=
  (xs.brecOnTable (motive := motive) step).1
```

```lean
def Tree.brecOn' {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t :=
  (t.brecOnTable (motive := motive) step).1
```

```lean -show -keep
-- 证明上述等价性过于耗时，但求值几个示例至少能发现低级错误！

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x y z step => List.brecOn' (motive := motive) [x, y, z] step

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x y z step => List.brecOn (motive := motive) [x, y, z] step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x z step => Tree.brecOn' (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x z step => Tree.brecOn (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step
```

:::
