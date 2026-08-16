/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductiveParamMismatch`" =>
%%%
shortTitle := "inductiveParamMismatch"
%%%

{errorExplanationHeader lean.inductiveParamMismatch}

当归纳类型的参数在归纳声明中不统一时，会产生此错误。归纳类型的参数（即出现在
{keyword}`inductive` 关键字后冒号之前的参数）必须在其构造器类型中该类型的所有出现处都相同。
如果归纳类型的某个参数必须随构造器变化，请将它移到冒号右侧，使其成为索引。更多信息请参阅
{ref "inductive-types"}[归纳类型]。

注意，自动隐式内嵌提示在归纳声明中总是出现在冒号左侧（即作为参数），即使它们实际是索引。
因此，双击内嵌提示插入这类参数可能导致此错误。若发生这种情况，请将插入的参数改为索引。

# 示例

:::errorExample "作为参数的向量长度索引"
```broken
inductive Vec (α : Type) (n : Nat) : Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```
```output
Mismatched inductive type parameter in
  Vec α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```fixed
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

`Vec` 类型构造器的长度参数 `n` 被声明为参数，但 `nil` 和 `cons` 构造器中出现了该参数的其他值
（即 `0` 和 `n + 1`）。因此，错误出现在此类参数的首次出现处。要修正它，`n` 不能是归纳声明的参数，
而必须像修正示例中那样成为索引。另一方面，`α` 在声明中所有 `Vec` 的出现处都保持不变，因此是有效参数。
:::
