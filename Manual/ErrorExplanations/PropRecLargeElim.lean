/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`propRecLargeElim`" =>
%%%
shortTitle := "propRecLargeElim"
%%%

{errorExplanationHeader lean.propRecLargeElim}


当尝试将命题证明消去到更高的类型宇宙时，会产生此错误。
由于 Lean 的类型论不允许从 {lean}`Prop` 进行大消去，因此不能对这类值进行模式匹配，
例如使用 {keywordOf Lean.Parser.Term.let}`let` 或
{keywordOf Lean.Parser.Term.match}`match` 来在非命题宇宙（即 `Type u`）中生成数据。
更准确地说，命题递归子的动机必须是命题。（此规则的例外情况请参阅手册中的
{ref "subsingleton-elimination"}[单例消去]一节。）

注意，任何将证明消去到非命题宇宙的表达式都会引发此错误，即使该表达式位于另一个
命题类型的表达式中（例如证明中的 {keywordOf Lean.Parser.Term.let}`let` 绑定）。
下方“在证明中定义中间数据值”的示例展示了这种情况。此类错误通常可以通过将递归子应用
“向外”移动来解决，使其动机成为正在证明的命题，而不是数据值项的类型。

# 示例

:::errorExample "在证明中定义中间数据值"
```broken
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  let val :=
    match inst with
    | .intro x => x
  ⟨val, Classical.em (p val)⟩
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Nonempty.casesOn` can only eliminate into `Prop`

α : Type
motive : Nonempty α → Sort ?u.48
h_1 : (x : α) → motive ⋯
inst✝ : Nonempty α
⊢ motive inst✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```fixed
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  match inst with
  | .intro x => ⟨x, Classical.em (p x)⟩
```
尽管所定义的 {keywordOf Lean.Parser.Command.example}`example` 具有命题类型，
`val` 的主体却不是；它的类型是 `α : Type`。因此，对 `Nonempty α`（一个命题）的证明进行
模式匹配以生成 `val`，需要将该证明消去到非命题类型中，这是不允许的。相反，必须将
{keywordOf Lean.Parser.Term.match}`match` 表达式移到 `example` 的顶层，此时结果是对示例
标题中所述存在性断言的 {lean}`Prop` 值证明。也可以使用模式匹配的
{keywordOf Lean.Parser.Term.let}`let` 绑定来完成这种重构。
:::

:::errorExample "从存在性证明中提取见证"

```broken
def getWitness {α : Type u} {p : α → Prop} (h : ∃ x, p x) : α :=
  match h with
  | .intro x _ => x
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

α : Type u
p : α → Prop
motive : (∃ x, p x) → Sort ?u.52
h_1 : (x : α) → (h : p x) → motive ⋯
h✝ : ∃ x, p x
⊢ motive h✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```fixed "in Prop"
-- 这是 `Exists.elim`
theorem useWitness {α : Type u} {p : α → Prop} {q : Prop}
    (h : ∃ x, p x) (hq : (x : α) → p x → q) : q :=
  match h with
  | .intro x hx => hq x hx
```
```fixed "in Type"
def getWitness {α : Type u} {p : α → Prop}
    (h : (x : α) ×' p x) : α :=
  match h with
  | .mk x _ => x
```
在此示例中，简单地移动模式匹配并不够；尝试定义的 `getWitness` 从根本上是不健全的。
（考虑 `p` 为 {lean}`fun (n : Nat) => n > 0` 的情况：如果 `h` 和 `h'` 是
{lean}`∃ x, x > 0` 的证明，其中 `h` 使用见证 `1`，而 `h'` 使用见证 `2`，
那么根据证明无关性 `h = h'`，可推出 `getWitness h = getWitness h'`——即 `1 = 2`。）

因此，必须重写 `getWitness`：函数的结果类型必须是命题（上面的第一个修正示例），
或者 `h` 不能是命题（第二个修正示例）。

在第一个修正示例中，`useWitness` 的结果类型现在是命题 `q`。这允许我们对 `h` 进行模式匹配
（因为我们将其消去到命题类型中），并将解包后的值传递给 `hq`。从编程角度看，可以将
`useWitness` 视为以延续传递风格重写 `getWitness`，限制后续计算仅使用其结果来构造
{lean}`Prop` 中的值，正如禁止命题大消去所要求的那样。注意，`useWitness` 就是存在性消去
原理 {name}`Exists.elim`。

第二个修正示例将 `h` 的类型从存在性命题改为一个取
{lean}`Type` 值的依赖对（对应于 {name}`PSigma` 类型构造器）。
由于该类型不是命题，将其消去到 `α : Type u` 不再无效，之前尝试的模式匹配现在可以通过
类型检查。
:::
