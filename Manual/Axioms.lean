/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "公理" =>
%%%
tag := "axioms"
file := "Axioms"
htmlSplit := .never
%%%
:::leanSection

```lean -show
universe u
```

{deftech (key := "Axioms")}_公理_是假定存在的常量。
公理的类型本身必须是类型（也就是说，它必须具有类型 {lean}`Sort u`），除此之外没有其他要求。
公理不会{tech (key := "reduction")}[归约]为其他项。
:::

在投入构造模型或证明定理所需的时间之前，可以先用公理试验某个想法会产生什么后果。
公理也可用于采纳 Lean 类型论中原本无法使用的推理原则；Lean 自身提供了{ref "standard-axioms"}[三个这样的公理]，且已知它们是一致的。
不过，使用公理应当谨慎：彼此不一致或本身就是假的公理会动摇证明赖以成立的根基。
Lean 会自动追踪每个证明所依赖的公理，以便审查。

# 公理声明
%%%
tag := "axiom-declarations"
%%%

公理声明包含名称和类型：

:::syntax Lean.Parser.Command.axiom (title := "公理声明")
```grammar
axiom $_ $_
```
:::

公理声明可以使用所有{ref "declaration-modifiers"}[声明修饰符]进行修饰。
文档注释、属性、{keyword}`private` 和 {keyword}`protected` 的含义与用于其他声明时相同。
修饰符 {keyword}`partial`、{keyword}`nonrec`、{keyword}`noncomputable` 和 {keyword}`unsafe` 不起作用。

# 一致性
%%%
tag := "axiom-consistency"
%%%

使用公理有风险。
公理会引入一个具有任意类型的新常量，而命题类型的一个元素就算作该命题的证明，因此公理甚至可用于证明假命题。
依赖某个公理的证明，其可信程度取决于该公理是否为真，以及它是否与所用的其他公理一致。
从本质上说，Lean 无法检查新公理是否一致；添加公理时请务必谨慎。

:::example "公理导致的不一致"
公理可能单独或与其他公理共同引入不一致。

假定一个假命题，就能证明任何命题：
```lean
axiom false_is_true : False

theorem two_eq_five : 2 = 5 := false_is_true.elim
```

与 Lean 的其他性质不相容的公理也可能导致不一致。
例如，在支持参数化性的语言中，参数化性是一种强大的推理技术，但它与 Lean 的标准公理不相容。
如果参数化性成立，那么 Wadler 的论文 [_Theorems for Free_](https://dl.acm.org/doi/pdf/10.1145/99370.99404)（1989）引言中的“自由定理”就会成立；该论文介绍了利用参数化性推导多态函数相关定理的技术。
将这个自由定理写成公理如下：
```lean
axiom List.free_theorem {α β}
  (f : {α : _} → List α → List α) (g : α → β) :
  f ∘ (List.map g) = (List.map g) ∘ f
```
然而，排中律的一个推论是所有命题都可判定；这意味着函数可以_检查_命题是真还是假。
这个函数无法编译，但它仍然存在。
由此可以定义不具参数化性的多态函数：
```lean
open Classical in
noncomputable def nonParametric
    {α : _} (xs : List α) :
    List α :=
  if α = Nat then [] else xs
```
这个函数的存在与“自由定理”矛盾：
```lean
theorem unit_not_nat : Unit ≠ Nat := by
  intro eq
  have ⟨allEq⟩ := eq ▸ (inferInstance : Subsingleton Unit)
  specialize allEq 0 1
  contradiction

example : False := by
  have := List.free_theorem nonParametric (fun () => 42)

  unfold nonParametric at this
  simp [unit_not_nat] at this

  have := congrFun this [()]
  contradiction
```
:::

# 归约
%%%
tag := "axiom-reduction"
%%%

即使是一致的公理也可能造成困难。
{tech (key := "Definitional equality")}[定义相等]按照归约规则来等同项。
{tech (key := "ι-reduction")}[ι-归约]规则规定了递归器与构造器的相互作用；由于公理不是构造器，该规则不适用于公理。
通常，不含自由变量的项会归约为构造器的应用，但公理可能使归约“卡住”，从而产生很大的项。

:::example "公理与卡住的归约"
用公理为 {lean}`Nat` 添加一个额外的 `0`，会使某些定义归约卡住。
在此例中，归约成功地将两个 {name}`Nat.succ` 构造器移到项的外层，但 {name}`Nat.rec` 遇到 {lean}`Nat.otherZero` 后就无法继续推进。
```lean (name := otherZero)
axiom Nat.otherZero : Nat

#reduce 4 + (Nat.otherZero + 2)
```
```leanOutput otherZero
((Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) Nat.otherZero).1 4).succ.succ
```
:::

此外，Lean 编译器无法为公理生成代码。
运行时，Lean 值必须由内存中的具体数据表示，但公理没有具体表示。
如果定义所包含的非证明代码依赖公理，就必须将其标记为 {keyword}`noncomputable`，且无法编译。

:::example "公理与编译"
用公理为 {lean}`Nat` 添加一个额外的 `0`，会使使用它的函数无法编译。
特别地，{name}`List.length'` 将公理 {name}`Nat.otherZero` 而不是 {name}`Nat.zero` 作为空列表的长度返回。
```lean (name := otherZero2) +error
axiom Nat.otherZero : Nat

def List.length' : List α → Nat
  | [] => Nat.otherZero
  | _ :: _ => xs.length
```
```leanOutput otherZero2
`Nat.otherZero` not supported by code generator; consider marking definition as `noncomputable`
```

在证明而非程序中使用的公理不会妨碍函数编译。
编译器不为证明生成代码，因此证明中的公理不会造成问题。
{lean}`nextOdd` 根据一个 {lean}`Nat` 计算下一个奇数；结果可能就是该数本身，也可能比它大一：
```lean
def nextOdd (k : Nat) :
    { n : Nat // n % 2 = 1 ∧ (n = k ∨ n = k + 1) } where
  val := if k % 2 = 1 then k else k + 1
  property := by
    by_cases k % 2 = 1 <;>
    simp [*] <;> omega
```
该策略证明生成的项传递地依赖三个公理：
```lean (name:=printAxNextOdd)
#print axioms nextOdd
```
```leanOutput printAxNextOdd
'nextOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
由于这些公理只出现在证明中，编译器可以顺利生成代码：
```lean (name := evalNextOdd)
#eval (nextOdd 4, nextOdd 5)
```
```leanOutput evalNextOdd
(5, 5)
```
:::

# 标准公理
%%%
tag := "standard-axioms"
%%%

Lean 中有七个标准公理。前三个公理是使用 Lean 开展数学工作的重要组成部分：
 * ```signature
   Classical.choice.{u} {α : Sort u} : Nonempty α → α
   ```
 * ```signature
   propext {a b : Prop} : (a ↔ b) → a = b
   ```
 * ```signature
   Quot.sound.{u} {α : Sort u}
     {r : α → α → Prop} {a b : α} :
     r a b → Quot.mk r a = Quot.mk r b
   ```

[Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=axioms-and-computation) 一书讨论了这三个公理。

公理 {name}`sorryAx` 是 {tactic}`sorry` 策略和 {lean}`sorry` 项实现的一部分。
完成的证明不应使用此公理，因为它可用于证明任何命题：
 * ```signature
   sorryAx.{u} (α : Sort u) (synthetic : Bool) : α
   ```
第二个参数标记该占位证明是否由错误恢复生成：普通的 `sorry` 使用 `false`，错误恢复生成的合成 `sorry` 使用 `true`。

最后三个公理并非真正因其_数学_内容而存在；从数学角度看，它们证明的都是平凡命题：

 * ```signature
    Lean.trustCompiler : True
   ```

 * ```signature
    Lean.ofReduceBool (a b : Bool) : Lean.reduceBool a = b → a = b
   ```
 * ```signature
    Lean.ofReduceNat (a b : Nat) : Lean.reduceNat a = b → a = b
   ```

相反，这些公理用于追踪依赖整个编译器正确性的证明，而不只是依赖小得多的{tech (key := "kernel")}[内核]。

:::example "创建并追踪信任编译器的证明"
调用函数 {name}`Lean.reduceBool` 和 {name}`Lean.reduceNat` 可以让编译器执行计算；这能大幅提升反射式证明实现的性能。

```lean
set_option linter.deprecated false in
def largeNumber : Nat := Lean.reduceNat (230_000 + 4_500 + 1_000_067)
```

所得项依赖公理 {name}`Lean.trustCompiler`，以追踪该计算依赖编译器正确性这一事实。

```lean (name := printAxExC1)
#print axioms largeNumber
```
```leanOutput printAxExC1
'largeNumber' depends on axioms: [Lean.trustCompiler]
```
:::

:::example "公理与 `native_decide` 策略"
{tactic}`native_decide` 策略并不诉诸 {name}`Lean.trustCompiler`，而是为每次调用创建一个专用公理。
这样就能针对每个公理所证明的确切命题进行审查。

```lean (name := printAxExC2)
set_option linter.defProp false in
def bigSum : (List.range 1_001).sum = 500_500 := by native_decide
#print axioms bigSum
```
```leanOutput printAxExC2
'bigSum' depends on axioms: [bigSum._native.native_decide.ax_1]
```

可以直接检查该公理的类型：
```lean (name := printAxExC3)
#check bigSum._native.native_decide.ax_1
```
```leanOutput printAxExC3
bigSum._native.native_decide.ax_1 : decide ((List.range 1001).sum = 500500) = true
```
:::

# 显示公理依赖
%%%
tag := "print-axioms"
%%%

命令 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` 后接一个已定义的标识符，会显示该定义传递依赖的所有公理。
换句话说，如果一个证明使用了另一个本身使用公理的证明，那么对二者执行 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` 时都会报告该公理。

::::keepEnv

这可用于审查证明所作的假设，例如检测一个证明是否传递地依赖 {tactic}`sorry` 策略。

```lean
set_option linter.defProp false in
set_option warn.sorry false in
def lazy : 4 == 2 + 1 + 1 := by sorry
```
```lean (name := printAxEx4)
#print axioms lazy
```
```leanOutput printAxEx4
'lazy' depends on axioms: [sorryAx]
```

:::example "打印简单定义的公理" (keep := true)

考虑以下三个常量：

```lean
def addThree (n : Nat) : Nat := 1 + n + 2
theorem excluded_middle (P : Prop) : P ∨ ¬ P := Classical.em P
theorem simple_equality (P : Prop) : (P ∨ False) = P := or_false P
```

像 {lean}`addThree` 这样可能确实需要求值的普通函数通常不依赖任何公理：

```lean (name := printAxEx2)
#print axioms addThree
```
```leanOutput printAxEx2
'addThree' does not depend on any axioms
```

排中律定理只有使用经典推理时才成立，因此经典推理的基础会与其他公理一同出现：

```lean (name := printAxEx1)
#print axioms excluded_middle
```
```leanOutput printAxEx1
'excluded_middle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

最后，等价命题相等这一观念直接依赖{tech (key := "propositional extensionality")}[命题外延性]。

```lean (name := printAxEx3)
#print axioms simple_equality
```
```leanOutput printAxEx3
'simple_equality' depends on axioms: [propext]
```
:::

:::example "将 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` 与 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 配合使用"

可以将 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`
与 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 配合使用，以确保
其他项目的库更新不会悄然
引入不需要的公理依赖。

例如，如果下面 {name}`double_neg_elim` 的证明发生变化，使用了比所列公理更多的公理，
那么 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令就会报告错误。

```lean
theorem double_neg_elim (P : Prop) : (¬ ¬ P) = P :=
  propext Classical.not_not

/--
info: 'double_neg_elim' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms double_neg_elim

```
:::


::::
