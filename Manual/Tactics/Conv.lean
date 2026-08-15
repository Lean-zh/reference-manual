/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "使用 {tactic}`conv` 定向重写" =>
%%%
file := "Targeted-Rewriting-with--conv"
tag := "conv"
%%%

{tactic}`conv`（即转换）策略允许在目标内进行定向重写。
{tactic}`conv` 的参数以一种与主策略语言互操作的独立语言编写；它既提供在目标内导航到特定子项的命令，也提供重写这些子项的命令。
当重写只应应用于目标的一部分（例如只应用于等式的一侧）而非全局应用时，或者重写应在某个绑定器之下进行、因而 {tactic}`rw` 等策略无法访问该项时，{tactic}`conv` 很有用。

转换策略语言与主策略语言非常相似：二者使用相同的证明状态；策略主要作用于主目标，并且可能失败，也可能成功并产生一系列新目标；宏展开与策略执行交错进行。
主策略语言中的策略旨在最终解决目标；与之不同，{tactic}`conv` 策略用于_改变_目标，使其适合由主策略语言进一步处理。
准备使用 {tactic}`conv` 重写的目标会以竖线而非推导符显示。

:::tactic "conv"
:::

::::example "使用 {tactic}`conv` 导航并重写" (file := "Navigation and Rewriting with conv")

在此示例中，加法出现了多次，而 {tactic}`rw` 默认会重写它遇到的第一个实例。
先使用 {tactic}`conv` 导航到特定子项再进行重写，{tactic}`rw` 就只能重写正确的项。

```lean
example (x y z : Nat) : x + (y + z) = (x + z) + y := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
```

::::

::::example "使用 {tactic}`conv` 在绑定器下重写" (file := "Rewriting Under Binders with conv")

在此示例中，加法位于绑定器之下，因此不能使用 {tactic}`rw`。
不过，在使用 {tactic}`conv` 导航到函数体之后，重写便会成功。
嵌套使用 {tactic}`conv` 会在对当前项的某个子项执行进一步转换之后，让控制返回该项中的当前位置。
由于重写后的目标是自反等式，{tactic}`conv` 会自动将其关闭。

```lean
example :
    (fun (x y z : Nat) =>
      x + (y + z))
    =
    (fun x y z =>
      (z + x) + y)
  := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
```

::::

# 控制结构
%%%
file := "Control Structures"
tag := "conv-control"
%%%


:::conv first (show := "first")
:::

:::conv convTry_ (show := "try")
:::

:::conv «conv_<;>_» (show:="<;>") +allowMissing
:::

:::conv convRepeat_ (show := "repeat")
:::

:::conv skip (show := "skip")
:::

:::conv nestedConv (show := "{ ... }")
:::

:::conv paren (show := "( ... )")
:::

:::conv convDone (show := "done")
:::

# 目标选择
%%%
file := "Goal Selection"
tag := "conv-goals"
%%%


:::conv allGoals (show := "all_goals")
:::

:::conv anyGoals (show := "any_goals")
:::

:::conv case (show := "case ... => ...")
:::

:::conv case' (show := "case' ... => ...")
:::

:::conv «convNext__=>_» (show := "next ... => ...")
:::

:::conv focus (show := "focus")
:::

:::conv «conv·_» (show := "· ...")
:::


:::conv failIfSuccess (show := "fail_if_success")
:::


# 导航
%%%
file := "Navigation"
tag := "conv-nav"
%%%


:::conv lhs (show := "lhs")
:::

:::conv rhs (show := "rhs")
:::

:::conv fun (show := "fun")
:::

:::conv congr (show := "congr")
:::

:::conv arg (show := "arg [@]i")
:::

:::syntax Lean.Parser.Tactic.Conv.enterArg (title := "{keyword}`enter` 的参数")
```grammar
$i:num
```
```grammar
@$i:num
```
```grammar
$x:ident
```
:::

:::conv enter (show := "enter")
:::


:::conv pattern (show := "pattern")
:::

:::conv ext (show := "ext")
:::

:::conv convArgs (show := "args")
:::

:::conv convLeft (show := "left")
:::

:::conv convRight (show := "right")
:::

:::conv convIntro___ (show := "intro")
:::

# 改变目标
%%%
file := "Changing the Goal"
tag := "conv-change"
%%%

## 归约
%%%
file := "Reduction"
tag := "conv-reduction"
%%%

:::conv cbv (show := "cbv")
:::

:::example "`cbv` 策略" (file := "The cbv Tactic")
{conv}`cbv` 策略可用于归约函数，其中包括通过 {ref "well-founded-recursion"}[良基递归]定义、在其他情况下不可归约的函数。
通常，{name}`f` 与其展开仅命题相等，因此 {tactic}`rfl` 无法证明等式 {lean}`f 5 = 5`：
```lean
def f (n : Nat) :=
  match n with
  | 0 => 0
  | n + 1 => f n + 1
termination_by (n,0)
```
```lean +error (name := nonEq)
example : f 5 = 5 := by rfl
```
```leanOutput nonEq
Tactic `rfl` failed: The left-hand side
  f 5
is not definitionally equal to the right-hand side
  5

⊢ f 5 = 5
```
在等式左侧使用 {conv}`cbv`，即可使该陈述成立：
```lean -show
-- The `cbv` tactic is presently experimental, and a warning is issued when it is used.
-- This option disables the warning:
set_option cbv.warning false
```
```lean
example : f 5 = 5 := by
  conv =>
    lhs
    cbv
```
:::

:::conv whnf (show := "whnf")
:::

:::conv reduce (show := "reduce")
:::

:::conv zeta (show := "zeta")
:::

:::conv delta (show := "delta")
:::

:::conv unfold (show := "unfold")
:::

## 化简
%%%
file := "Simplification"
tag := "conv-simp"
%%%

:::conv simp (show := "simp")
:::

:::conv dsimp (show := "dsimp")
:::

:::conv simpMatch (show := "simp_match")
:::

## 重写
%%%
file := "Rewriting"
tag := "conv-rw"
%%%

:::conv change (show := "change")
:::

:::conv rewrite (show := "rewrite")
:::

:::conv convRw__ (show := "rw")
:::

:::conv convErw__ (show := "erw")
:::

:::conv convApply_ (show := "apply")
:::

# 嵌套策略
%%%
file := "Nested Tactics"
tag := "conv-nested"
%%%


:::tactic Lean.Parser.Tactic.Conv.convTactic
:::

:::conv nestedTactic (show := "tactic")
:::

:::conv nestedTacticCore (show := "tactic'")
:::

:::tactic Lean.Parser.Tactic.Conv.convTactic (show := "conv'")
:::

:::conv convConvSeq (show := "conv => ...")
:::


# 调试工具
%%%
file := "Debugging Utilities"
tag := "conv-debug"
%%%

:::conv convTrace_state (show := "trace_state")
:::


# 其他
%%%
file := "Other"
tag := "conv-other"
%%%

:::conv convRfl (show := "rfl")
:::

:::conv normCast (show := "norm_cast")
:::
