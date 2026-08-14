/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "递归示例（供其他位置嵌入）" =>


```lean -show
section
variable (n k : Nat) (mot : Nat → Sort u)
```
:::example "递归与递归器"
自然数加法可通过对第二个参数递归来定义。
这个函数显然是结构递归的。
```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```

若使用 {name}`Nat.rec` 定义，它就会远离大多数人习惯的记法。
```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```

若结构递归调用所用的数据并非函数参数的直接子项，就需要发挥创意，或采用复杂但系统的编码。
```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
理解这个函数的一种方式，是将它看作一种结构递归：每次调用都翻转一个位，并且仅在该位已设置时递增结果。
```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

无需发挥创意，可以改用一种称为{deftech (key := "course-of-values recursion")}[所有较小值递归]的通用技术。
所有较小值递归使用可针对每个归纳类型系统推导出的辅助定义；这些辅助定义以递归器来定义，Lean 会自动推导它们。
对于每个 {lean}`Nat` 值 {lean}`n`，类型 {lean}`n.below (motive := mot)` 为所有 {lean}`k < n` 提供一个类型为 {lean}`mot k` 的值，并将其表示为迭代的 {TODO}[xref sigma] 依赖序对类型。
所有较小值递归器 {name}`Nat.brecOn` 允许函数使用任意更小 {lean}`Nat` 值所对应的结果。
用它定义函数并不方便：
```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
该函数被标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为编译器不支持为所有较小值递归生成代码；这种递归旨在用于推理，而非生成高效代码。
不过，仍然可以使用内核测试该函数：
```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

如有必要，{lean}`half''` 函数体中的依赖模式匹配也可使用递归器（具体来说是 {name}`Nat.casesOn`）来编码：
```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```

这个定义仍然有效。
```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

然而，它现在已远离原始定义，而且变得难以为大多数人所理解。
递归器是出色的逻辑基础，却不是编写程序或证明的简便方式。
:::
```lean -show
end
```
