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

open Lean Lean.Grind Lean.Meta.Grind


#doc (Manual) "约束传播" =>
%%%
file := "Constraint-Propagation"
tag := "grind-propagation"
%%%

{deftech (key := "Constraint propagation")}[约束传播] 作用于白板上的 {lean}`True` 与 {lean}`False` 两个桶。
每当某个项被加入其中一个桶时，{tactic}`grind` 都会触发许多小型的 {deftech (key := "forward rules")}_前向规则_，从它的逻辑后果中推导出更多信息：

: 布尔联结词

  ::::leanSection
  ```lean -show
  variable {A B : Prop}
  ```
  :::paragraph
  布尔联结词的真值表可用于推出更多为真或为假的事实。
  例如：
   * 如果 {lean}`A` 是 {lean}`True`，那么 {lean}`A ∨ B` 就变成 {lean}`True`。
   * 如果 {lean}`A ∧ B` 是 {lean}`True`，那么 {lean}`A` 和 {lean}`B` 都会变成 {lean}`True`。
   * 如果 {lean}`A ∧ B` 是 {lean}`False`，那么 {lean}`A`、{lean}`B` 中至少有一个会变成 {lean}`False`。
  :::
  ::::

: 归纳类型

  如果由同一个 {tech (key := "inductive type")}[归纳类型] 的两个不同构造子应用而成的项（例如 {name}`none` 和 {name}`some`）被放进同一个等价类，就会导出矛盾。
  如果由同一个构造子应用而成的两个项被放进同一个等价类，那么它们的参数也会被判定为相等。

: 投影
  :::leanSection
  ```lean -show
  variable {x x' : α} {y y' : β} {h : (x, y) = (x', y')} {a : α}
  ```

  从 {typed}`h : (x, y) = (x', y')` 可以推出 {lean}`x = x'` 和 {lean}`y = y'`。
  :::

: 强制转换

  :::leanSection
  ```lean -show
  variable {h : α = β} {a : α}
  ```
  任意项 {typed}`cast h a : β` 都会立刻与 {typed}`a : α` 判定为相等（使用 {tech (key := "heterogeneous equality")}[异质相等]）。
  :::

: 归约

  ::::keepEnv
  :::leanSection
  ```lean -show
  variable {α : Type u} {β : Type v} {a : α} {b : β}
  structure S α β where
    x : α
    y : β
  variable {p : S α β}
  ```
  定义性归约也会传播，因此 {lean}`(a, b).1` 会与 {lean}`a` 判定为相等。
  :::
  ::::

:::paragraph
下面给出一组_具有代表性_的传播器片段，用来展示它们的整体风格。
它们都遵循同一套骨架。

1. 检查子表达式的真值。

2. 如果还能推出更多事实，就要么用 ({lean}`pushEq`) 将项判定为相等（也就是把它们连接到比喻意义上的白板上），要么用 ({lean}`pushEqTrue` / {lean}`pushEqFalse`) 标示真值。
   这些步骤会借助诸如 {name}`Grind.and_eq_of_eq_true_left` 这样的内部辅助引理来构造证明项。

3. 如果出现矛盾，就用 ({lean}`closeGoal`) 关闭目标。

{deftech (key := "Upward propagation")}_向上传播_从子项的事实中推出关于整个项的事实，而 {deftech (key := "downward propagation")}_向下传播_则从整个项的事实中推出关于子项的事实。
:::

```lean -show
namespace ExamplePropagators
```
```lean -keep

/-- 对合取进行*向上*的相等传播。 -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left)
        a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True  ⇒  (a ∧ b) = a
    pushEq e a <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right)
        a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    -- a = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left)
        a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right)
        a b (← mkEqFalseProof b)

/--
当整个 `And` 已被证明为 `True` 时，真值会向*下*传播。
-/
builtin_grind_propagator propagateAndDown ↓And :=
  fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    -- (a ∧ b) = True  ⇒  a = True
    pushEqTrue a <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    -- (a ∧ b) = True  ⇒  b = True
    pushEqTrue b <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```
```lean -show
end ExamplePropagators
```



其他经常触发的传播器也遵循同样的模式：

::::leanSection
```lean -show
variable {A B : Prop} {a b : α}
```

:::table +header
*
  * 传播器
  * 处理对象
  * 说明
*
  * {lean}`propagateOrUp` / {lean}`propagateOrDown`
  * {lean}`A ∨ B`
  * 使用析取的真值表来推出更多真值
*
  * {lean}`propagateNotUp` / {lean}`propagateNotDown`
  * {lean}`¬ A`
  * 确保 {lean}`¬ A` 与 {lean}`A` 的真值相反
*
  * {lean}`propagateEqUp` / {lean}`propagateEqDown`
  * `a = b`
  * 桥接布尔值，检测构造子冲突 {TODO}[“桥接布尔值”是什么意思？请查明]
*
  * {lean}`propagateIte` / {lean}`propagateDIte`
  * {name}`ite` / {name}`dite`
  * 一旦已知条件的真值，就把该项与选中的分支判定为相等
*
  * `propagateEtaStruct`
  * 带有 `[grind ext]` 标记的结构体值
  * 生成 η‑展开 `a = ⟨a.1, …⟩`
:::
::::

:::comment
TODO (@kim-em)：上面没有给 `propagateEtaStruct` 加上 `{lean}` 字面量类型，因为它是私有的。
:::

许多针对 {lean}`Bool` 的专门变体都严格仿照这些规则（例如 {lean}`propagateBoolAndUp`）。

# 仅靠传播的示例
%%%
tag := "grind-propagation-only-examples"
%%%

下面这些目标*纯粹*依靠约束传播即可关闭——既不需要分类讨论，也不需要理论求解器：

```lean
-- 布尔联结词：a && !a 永远为 false。
example (a : Bool) : (a && !a) = false := by
  grind

-- 条件表达式（ite）：
-- 一旦条件为真，ite 就会选择 then 分支。
example (c : Bool) (t e : Nat) (h : c = true) :
    (if c then t else e) = t := by
  grind

-- 否定会向下传播真值。
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```

这些片段会立刻运行完成，因为相关传播器（{lean}`propagateBoolAndUp`、{lean}`propagateIte`、{lean}`propagateBoolNotDown`）会在假设被内化后立刻触发。
将选项 {option}`trace.grind.eqc` 设为 {lean}`true` 后，每当两个等价类合并时，{tactic}`grind` 都会打印一行信息，这很适合观察传播是如何发生的。


:::TODO

等该命令实现后，这一节应取消注释：

```lean -show
-- 用于确保该命令实现后，本节已被取消注释的测试
/--
error: elaboration function for `Lean.Parser.«command_Grind_propagator___(_):=_»` has not been implemented
-/
#guard_msgs in
grind_propagator ↑x(y) := _
```

{tactic}`grind` 仍在积极开发中，其实现很可能还会变化。
在 API 稳定之前，我们建议_不要编写自定义精译器或卫星求解器_。
如果项目本地确实需要自定义传播器，那么应使用 {keywordOf «command_Grind_propagator___(_):=_»}`grind_propagator` 命令来定义，而不是使用 {keywordOf «command_Builtin_grind_propagator____:=_»}`builtin_grind_propagator`（后者保留给 Lean 自身代码使用）。
添加新传播器时，应保持其*小而正交*——它们应在 ≤1 µs 内触发，并且要么推进一个事实，要么关闭目标。
这样可以让传播阶段的行为更可预测，也更容易调试。
:::

传播规则的集合会随着时间不断扩展和细化，因此 InfoView 中显示的 {lean}`True` 与 {lean}`False` 桶也会越来越丰富。
完整的等价类只会在 {tactic}`grind` _失败时_自动显示，而且只针对它无法关闭的第一个子目标——可以利用这些输出来检查缺失的事实，并理解为什么该子目标仍然未解。

:::example "识别缺失的事实"
在这个例子中，{tactic}`grind` 失败了：

```lean +error (name := missing)
example :
    x = y ∧ y = z →
    w = x ∨ w = v →
    w = z := by
  grind
```
生成的错误消息会给出识别到的等价类，以及为真和为假的命题：
```leanOutput missing (expandTrace := eqc)
`grind` failed
case grind
α : Sort u_1
x y z w v : α
left : x = y
right : y = z
h_1 : w = x ∨ w = v
h_2 : ¬w = z
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] w = x ∨ w = v
    [prop] w = v
  [eqc] False propositions
    [prop] w = x
    [prop] w = z
  [eqc] Equivalence classes
    [eqc] {x, y, z}
    [eqc] {w, v}
```
`x = y` 和 `y = z` 都是由约束传播从前提 `x = y ∧ y = z` 中发现的。
在这个证明中，{tactic}`grind` 对 `w = x ∨ w = v` 做了分类讨论。
在第二个分支里，它无法把 `w` 和 `z` 放进同一个等价类。
:::
