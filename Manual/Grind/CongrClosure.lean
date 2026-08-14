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

#doc (Manual) "同余闭包" =>
%%%
file := "Congruence-Closure"
tag := "congruence-closure"
%%%

:::leanSection
```lean -show
variable {a a' : α} {b b' : β} {f : α → β → γ}
```
{deftech (key := "Congruence closure")}_同余闭包_维护项在“相等”的自反、对称和传递闭包下的等价类，_并且_遵循“相等的参数产生相等的函数结果”这一规则。
形式化地说，如果 {lean}`a = a'` 且 {lean}`b = b'`，就会加入 {lean}`f a b = f a' b'`。
该算法会不断合并等价类，直至达到不动点。
如果发现矛盾，就可以立即关闭目标。
:::

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
沿用共享白板的比喻：

1. 每个假设 {typed}`h : t₁ = t₂` 都会画一条连接 {lean}`t₁` 与 {lean}`t₂` 的线。

2. 只要两个项由一条或多条线连接，就认为它们相等。
   很快，整片项群（{lean}`f a`、{lean}`g (f a)`、……）都会连接起来。

3. 如果同一归纳类型的两个不同构造器由一条或多条线连接起来，就发现了矛盾，目标随即关闭。
   例如，令 {lean}`True` 与 {lean}`False` 相等，或令 {lean  (type := "Option Nat")}`none` 与 {lean}`some 1` 相等，都会产生矛盾。

:::
::::

:::example "同余闭包" (open := true)
这个定理使用同余闭包证明：
```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  grind
```
最初，`f y`、`g y`、`x` 和 `y` 分属不同的等价类。
同余闭包引擎使用 `h₁` 合并 `x` 和 `y`，此后等价类为 `{x, y}`、`f y` 和 `g y`。
接着使用 `h₂` 合并 `f y` 和 `g y`，此后等价类为 `{x, y}` 和 `{f y, g y}`。
这足以证明 `f x = g x`，因为 `y` 和 `x` 位于同一个等价类中。

对构造器也使用类似的推理：
```lean
example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  grind
```
由于序对构造器 {name}`Prod.mk` 满足同余性，一旦 `a` 和 `b` 被归入同一个类，这两个元组便相等。
:::


# 同余闭包与化简
%%%
tag := "grind-congruence-closure-vs-simplification"
%%%

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
同余闭包与化简是两种根本不同的操作：

* {tactic}`simp` 会_重写_目标：一旦看到 {typed}`h : t₁ = t₂`，就把出现的 {lean}`t₁` 替换为 {lean}`t₂`。
  这种重写是有方向且破坏性的。
* {tactic}`grind` 会双向_累积_等式。它不重写任何项，而是让两个代表元处于同一个类中。所有其他引擎（{tech (key := "E‑matching")}[E‑匹配]、理论求解器和{tech (key := "constraint propagation")}[传播]）都可以查询这些类并加入新事实，闭包随后增量更新。

因此，在对称推理、互递归以及构造器深度嵌套等会使重写产生重复工作的情形下，同余闭包尤其稳健。
:::
::::
