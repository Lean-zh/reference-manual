/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "为库添加 `grind` 标注" =>
%%%
file := "Annotating-Libraries-for--grind"
tag := "grind-annotation"
%%%

要在库中有效使用 {tactic}`grind`，必须为库添加标注：给合适的引理应用 {attr}`grind` 属性，或声明 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern`。
这些标注引导 {tactic}`grind` 选择定理，进而在比喻中的白板上产生更多事实。
标注太少时，{tactic}`grind` 将无法使用这些引理；标注太多时，它可能变慢，或因耗尽资源限制而失败。
添加标注通常应当保守：只有当你认为模式一旦匹配，{tactic}`grind` 就应当_总是_实例化该定理时，才添加标注。

# `simp` 引理
%%%
tag := "grind-simp-lemmas"
%%%

通常，许多带有 {attrs}`@[simp]` 标注的定理也应带有 {attrs}`@[grind =]` 标注。
一个重要的例外是：我们通常避免让 {attrs}`@[simp]` 定理在右侧引入 {keywordOf Lean.Parser.Term.if}`if`，而倾向于使用一对分别以肯定条件和否定条件为假设的定理。
由于 {tactic}`grind` 的设计目标之一就是进行情形拆分，通常更适合改为给那个引入 {keywordOf Lean.Parser.Term.if}`if` 的单一定理添加 {attrs}`@[grind =]` 标注。

除了使用 {attrs}`@[grind =]` 促使 {tactic}`grind` 从左向右重写外，还可以使用 {attrs}`@[grind _=_]` 进行“饱和”：遇到任意一侧时都允许双向重写。

# 逆向与正向推理
%%%
tag := "grind-backwards-and-forwards-reasoning"
%%%

:::paragraph
对逆向推理定理使用 {attrs}`@[grind ←]`（它从定理结论生成模式）；也就是说，当定理结论与目标匹配时，就应尝试该定理。
标准库中带有 {attr}`grind ←` 标注的定理包括：
* ```signature
  Array.not_mem_empty (a : α) : ¬ a ∈ #[]
  ```
* ```signature
  Array.getElem_filter
    {xs : Array α} {p : α → Bool} {i : Nat}
    (h : i < (xs.filter p).size) :
    p (xs.filter p)[i]
  ```
* ```signature
  List.Pairwise.tail
    {l : List α} (h : Pairwise R l) :
    Pairwise R l.tail
  ```
在每个例子中，当引理的结论与证明目标匹配时，它便与当前证明相关。
:::

:::paragraph
对正向推理定理使用 {attrs}`@[grind →]`（它从假设生成模式），
也就是从白板上的已有事实传播出新事实的定理。
标准库中带有 {attr}`grind →` 标注的定理包括：
* ```signature
  List.getElem_of_getElem? {l : List α} :
    l[i]? = some a →
    ∃ h : i < l.length, l[i] = a
  ```
* ```signature
  Array.mem_of_mem_erase [BEq α] {a b : α} {xs : Array α}
    (h : a ∈ xs.erase b) :
    a ∈ xs
  ```
* ```signature
  List.forall_none_of_filterMap_eq_nil
    (h : filterMap f xs = []) :
    ∀ x ∈ xs, f x = none
  ```
在这些例子中，定理的假设决定它们何时与当前证明相关。
:::

使用 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` 命令创建的自定义模式有许多用途。
一种常见用途是引入关于项的不等式或成员关系命题。

:::keepEnv
```lean -show
section
def count := @Array.count
theorem countP_le_size [BEq α] {a : α} {xs : Array α} : count a xs ≤ xs.size := Array.countP_le_size
notation "..." => countP_le_size
```

例如，可以有：
```lean
variable [BEq α]

theorem count_le_size {a : α} {xs : Array α} : count a xs ≤ xs.size :=
  ...

grind_pattern count_le_size => count a xs
```
```lean -show
variable {a : α} {xs : Array α}
```
这样，一旦遇到 {lean}`count a xs` 项，就会登记该不等式（即使此前的问题中尚未涉及不等式）。

```lean -show
end
```
:::

还可以使用多模式施加更严格的限制，例如只有当白板上已经有关于大小的事实时，才引入关于大小的不等式：
```lean
theorem size_pos_of_mem {xs : Array α} (h : a ∈ xs) : 0 < xs.size :=
  sorry

grind_pattern size_pos_of_mem => a ∈ xs, xs.size
```
:::leanSection
```lean -show
variable {a : α} {xs : Array α}
```
若使用 {attrs}`@[grind →]` 属性，每当遇到 {lean}`a ∈ xs` 时都会实例化该定理；与之不同，这个模式只会在白板上已有 {lean}`xs.size` 时使用。
（注意，也可以使用 {attrs}`@[grind <=]` 属性产生这个 grind 模式；该属性先查看结论，再逆向查看假设以选择模式。
另一方面，{attrs}`@[grind →]` 只会选择 {lean}`a ∈ xs`。）
:::


::::keepEnv
:::leanSection
```lean -show
axiom R : Type
axiom sin : R → R
axiom cos : R → R
@[instance] axiom instAdd : Add R
@[instance] axiom instOfNatR : OfNat R n
@[instance] axiom instHPowR : HPow R Nat R
variable {x : R}
axiom sin_sq_add_cos_sq' : sin x ^ 2 + cos x ^ 2 = 1
notation "..." => sin_sq_add_cos_sq'
```
在 Mathlib 中，我们可能希望启用关于正弦和余弦函数的多项式推理，
因此添加如下自定义 grind 模式：
```lean
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 := ...

grind_pattern sin_sq_add_cos_sq => sin x, cos x
```
这样，一旦*同时*遇到具有同一个 {lean}`x` 的 {lean}`sin x` 和 {lean}`cos x`，就会实例化该定理。
随后，该定理会自动进入 Gröbner 基模块，用于推理同时包含 {lean}`sin x` 和 {lean}`cos x` 的多项式表达式。
另一种更激进的做法是分别编写两个 grind 模式，使该定理在遇到 {lean}`sin x` 或 {lean}`cos x` 中任意一个时就被实例化。
:::
::::
