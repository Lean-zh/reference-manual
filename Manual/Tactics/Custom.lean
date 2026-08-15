/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Conv

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option verso.docstring.allowMissing true

open Lean.Elab.Tactic

#doc (Manual) "自定义策略" =>
%%%
file := "Custom-Tactics"
tag := "custom-tactics"
%%%


```lean -show
open Lean
```

策略是语法类别 `tactic` 中的产生式。{TODO}[用于 syntax\_cats 的交叉引用宏]
给定某个策略的语法后，策略解释器负责在策略单子 {name}`TacticM` 中执行操作；该单子是 Lean 项繁释器的包装器，并跟踪执行策略所需的额外状态。
自定义策略包含对 `tactic` 类别的扩展，以及以下二者之一：
 * 一个将新语法转换为现有语法的 {tech (key := "macro")}[宏]；或
 * 一个执行 {name}`TacticM` 操作来实现该策略的繁释器。

# 策略宏
%%%
file := "Tactic Macros"
tag := "tactic-macros"
%%%

定义新策略最简单的方式，是将其定义为展开成既有策略的 {tech (key := "macro")}[宏]。
宏展开与策略执行交错进行。
策略解释器会在即将解释策略宏之前先将其展开。
由于策略脚本运行前不会完全展开其中的策略宏，因此它们可以使用递归；只要宏语法的递归出现位于某个可执行策略之下，就不会产生无限的展开链。

::::keepEnv
:::example "递归策略宏" (file := "Recursive tactic macro")
下面这个与 {tactic}`repeat` 类似的策略递归实现是通过宏展开定义的。
当参数 `$t` 失败时，{tactic}`rep` 的递归出现永远不会被调用，因而也永远不会被宏展开。
```lean
syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|
    first
      | $t; rep $t
      | skip)

example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl
```
:::
::::

与 Lean 中的其他宏一样，策略宏是 {tech (key := "hygiene")}[卫生的]。
全局名字的引用会在宏定义时解析，而策略宏引入的名字无法捕获其调用位置处的名字。

定义策略宏时，必须明确指定所匹配或构造的语法属于语法类别 `tactic`，这一点很重要。
否则，该语法会被解释为项语法，从而为策略匹配或构造错误的 AST。

## 可扩展的策略宏
%%%
file := "Extensible Tactic Macros"
tag := "tactic-macro-extension"
%%%


由于宏展开可能失败，{TODO}[交叉引用]多个宏可以匹配同一语法，从而允许回溯。
策略宏更进一步：即使某个策略宏成功展开，如果解释展开结果时失败，策略解释器也会尝试下一个展开。
Lean 的许多内置策略正是以此实现可扩展性——可以通过添加一条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明，为策略加入新行为。

::::keepEnv
:::example "扩展 {tactic}`trivial`" (file := "Extending trivial")

{tactic}`trivial` 被许多其他策略用来快速处理不值得打扰用户的子目标；它在设计上可通过新的宏展开进行扩展。
Lean 默认的 {lean}`trivial` 无法解决 {lean}`IsEmpty []` 目标：
```lean
def IsEmpty (xs : List α) : Prop :=
  ¬ xs ≠ []
```
```lean +error
example (α : Type u) : IsEmpty (α := α) [] := by trivial
```

该错误消息是 {tactic}`trivial` 最后尝试 {tactic}`assumption` 所造成的结果。
再添加一个展开，就能让 {tactic}`trivial` 处理这些目标：
```lean
def emptyIsEmpty : IsEmpty (α := α) [] := by simp [IsEmpty]

macro_rules | `(tactic|trivial) => `(tactic|exact emptyIsEmpty)

example (α : Type u) : IsEmpty (α := α) [] := by
  trivial
```
:::
::::

::::keepEnv
:::example "展开回溯" (file := "Expansion Backtracking")
当失败来自展开后语法的任意部分时，宏展开可以引发回溯。
通过在彼此独立的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明中提供多个展开，可以定义 {tactic}`first` 的中缀版本：
```lean
syntax tactic "<|||>" tactic : tactic
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t1
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t2

example : 2 = 2 := by
  rfl <|||> apply And.intro

example : 2 = 2 := by
  apply And.intro <|||> rfl
```

之所以需要多条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明，是因为每条声明都会定义一个始终采用首个匹配分支的模式匹配函数。
回溯的粒度是各条 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明，而非其中的单个分支。
:::
::::
