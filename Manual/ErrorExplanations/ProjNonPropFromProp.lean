/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`projNonPropFromProp`" =>
%%%
shortTitle := "projNonPropFromProp"
tag := "Lean-__________________--Error-Explanations--About___--projNonPropFromProp"
%%%

{errorExplanationHeader lean.projNonPropFromProp}
当尝试使用索引投影从命题证明中投影数据时，会产生此错误。
例如，如果 `h` 是存在性命题的证明，尝试提取见证 `h.1` 就是此错误的一个例子。
不允许此类投影，因为它们可能违反 Lean 禁止从 {lean}`Prop` 进行大消去的规定
（详见手册中的{ref "propositions"}[命题]一节）。

不要使用索引投影，而应考虑使用模式匹配
{keywordOf Lean.Parser.Term.let}`let`、{keywordOf Lean.Parser.Term.match}`match` 表达式，或
{tactic}`cases` 之类的解构策略，将一个命题类型消去到另一个命题类型。注意，只有当结果值也
位于 {lean}`Prop` 中时，这种消去才有效；否则将引发错误
{ref "lean.propRecLargeElim" (domain := Manual.errorExplanation)}[`lean.propRecLargeElim`]。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--projNonPropFromProp--Examples"
%%%
:::errorExample "尝试对存在性证明使用索引投影"

```broken
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > 0 :=
  ⟨h.1, Nat.lt_of_succ_lt h.2⟩
```
```output
Invalid projection: Cannot project a value of non-propositional type
  Nat
from the expression
  h
which has propositional type
  ∃ x, x > a + 1
```
```fixed "let"
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a :=
  let ⟨w, hw⟩ := h
  ⟨w, Nat.lt_of_succ_lt hw⟩
```
```fixed "cases"
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a := by
  cases h with
  | intro w hw =>
    exists w
    omega
```

不能使用索引投影提取存在性命题证明所关联的见证。必须使用模式匹配：
可以使用类似 {keywordOf Lean.Parser.Term.let}`let` 的项绑定，或类似 {tactic}`cases` 的策略。
:::
