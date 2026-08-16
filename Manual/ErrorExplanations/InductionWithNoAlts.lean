/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductionWithNoAlts`" =>
%%%
shortTitle := "inductionWithNoAlts"
tag := "Lean-__________________--Error-Explanations--About___--inductionWithNoAlts"
%%%

{errorExplanationHeader lean.inductionWithNoAlts}

在 Lean 中使用归纳的策略证明需要用类似模式匹配的记法描述证明的各个情形。
不过，Mathlib 中的 `induction'` 策略以及自然数游戏使用的专用 `induction` 策略遵循不同的模式。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--inductionWithNoAlts--Examples"
%%%
:::errorExample "为归纳证明添加显式情形"
```broken
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with n n_ih
  rw [Nat.mul_zero]
  rw [Nat.mul_succ]
  rw [Nat.add_zero]
  rw [n_ih]
```
```output
Invalid syntax for induction tactic: The `with` keyword must be followed by a tactic or by an alternative (e.g. `| zero =>`), but here it is followed by the identifier `n`.
```
```fixed
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [Nat.mul_zero]
  | succ n n_ih =>
    rw [Nat.mul_succ]
    rw [Nat.add_zero]
    rw [n_ih]
```
这个错误例子具有自然数游戏中正确证明的结构；如果 `import Mathlib` 并将 `induction` 替换为 `induction'`，
该证明就能工作。基础 Lean 中的归纳策略要求 {keyword}`with` 关键字后跟一系列情形，
归纳情形的名称应在 {name Nat.succ}`succ` 情形中提供，而不是预先提供。
:::
