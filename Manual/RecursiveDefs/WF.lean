/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.RecursiveDefs.WF
import Manual.Papers
import Manual.RecursiveDefs.WF.GuessLexExample
import Manual.RecursiveDefs.WF.PreprocessExample

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "良基递归" =>
%%%
tag := "well-founded-recursion"
%%%

以 {deftech (key := "well-founded recursion")}_良基递归_ 定义的函数，是指其中每次递归调用的实参都在某种{ref "wf-rel"}[适当意义]下比函数形参_更小_的函数。
与{ref "structural-recursion"}[结构递归]不同，后者要求递归定义满足特定的_句法_要求，而良基递归的定义使用的是_语义_论证。
这使得更大一类递归定义能够被接受。
此外，当 Lean 的自动化无法构造终止性证明时，也可以手工给出。

Lean 编译器会以完全相同的方式对待所有这些定义。
在 Lean 的逻辑中，使用良基递归的定义通常不会 {tech (key := "definitional equality")}[在定义上] 归约。
不过，这些归约在命题相等层面仍然成立，而 Lean 会自动证明它们。
这通常不会让证明良基递归定义的性质变得更困难，因为可以利用这些命题性的归约来推理函数行为。
但这也意味着，这类函数通常不太适合出现在类型中。
即便其归约行为碰巧在定义上成立，它在内核中的速度通常仍比结构递归定义慢得多，因为内核必须连同定义一起展开终止性证明。
因此，只要可能，那些打算在类型中使用、或在其他依赖定义相等的重要场景中使用的递归函数，都应优先定义为结构递归。

若要显式使用良基递归，可以在函数或定理定义上添加 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句，用来指定函数终止所依据的 {deftech (key := "measure")}_度量_。
该度量应是一个在每次递归调用时都会减小的项；它可以是函数的某个形参、若干形参组成的元组，也可以是任意其他项。
这个度量的类型必须配备一个 {tech (key := "well-founded relation")}[良基关系]，它决定了“度量减小”究竟意味着什么。

:::syntax Lean.Parser.Termination.terminationBy (title := "显式良基递归")

{keywordOf Lean.Parser.Command.declaration}`termination_by` 子句用来引入终止性论证。

```grammar
termination_by $[$_:ident* =>]? $term
```

可选 `=>` 之前的标识符可以把尚未在声明头中绑定的函数形参带入作用域，而后面必需的项必须指明函数的某个形参，无论它是在声明头中引入，还是在该子句中局部引入。
:::

:::example "通过反复减法定义除法"
除法可以刻画为“除数能从被除数中减去多少次”。
这个操作不能用结构递归来精译，因为减法不是模式匹配。
不过 `n` 的值确实会在每次递归调用时减小，因此可以用良基递归来为这种“反复减法求除法”的定义提供正当性。

```lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```
:::

# 良基关系
%%%
tag := "wf-rel"
%%%

若不存在无限下降链，则关系 `≺` 是一个 {deftech (key := "well-founded relation")}_良基关系_

$$` x_0 ≻ x_1 ≻ \cdots`

在 Lean 中，凡是带有规范良基关系的类型，都是类型类 {name}`WellFoundedRelation` 的实例。

{zhdocstring WellFoundedRelation ZhDoc.RecursiveDefs.WF.WellFoundedRelation}

```lean -show
section
variable {α : Type u} {β : Type v} (a₁ a₂ : α) (b₁ b₂ : β) [WellFoundedRelation α] [WellFoundedRelation β]
variable {γ : Type u} (x₁ x₂ : γ) [SizeOf γ]
local notation x " ≺ " y => WellFoundedRelation.rel x y
```

最重要的实例有：

* {name}[`Nat`]，按 {lean  (type := "Nat → Nat → Prop")}`(· < ·)` 排序。

* {name}[`Prod`]，按字典序排序：当且仅当 {lean}`a₁ ≺ a₂`，或 {lean}`a₁ = a₂` 且 {lean}`b₁ ≺ b₂` 时，有 {lean}`(a₁, b₁) ≺ (a₂, b₂)`。

* 每个属于类型类 {name}`SizeOf`（其提供方法 {name}`SizeOf.sizeOf`）的类型，都带有一个良基关系。
  对这些类型，{lean}`x₁ ≺ x₂` 当且仅当 {lean}`sizeOf x₁ < sizeOf x₂`。对于 {tech (key := "inductive types")}[归纳类型]，Lean 会自动派生出 {lean}`SizeOf` 实例。

```lean -show
end
```

注意，存在一个低优先级实例 {name}`instSizeOfDefault`，它会为任意类型提供一个 {lean}`SizeOf` 实例，并且总是返回 {lean}`0`。
这个实例不能用来借助良基递归证明函数终止，因为 {lean}`0 < 0` 为假。

```lean -show

-- 检查关于 instSizeOfDefault 的断言

example {α} (x : α) : sizeOf x = 0 := by rfl

/-- info: instSizeOfDefault.{u} (α : Sort u) : SizeOf α -/
#check_msgs in
#check instSizeOfDefault

```

:::example "默认的 Size 实例"

函数类型一般并没有对终止性证明有用的良基关系。
因此，{ref "instance-synth"}[实例合成]会选中 {name}`instSizeOfDefault` 及其对应的良基关系。
如果度量本身是一个函数，那么就会选中默认的 {name}`SizeOf` 实例，证明也就不可能成功。

```lean -keep
def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
termination_by b
decreasing_by
  guard_target =
    @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
  simp only [sizeOf, default.sizeOf]
  guard_target = 0 < 0
  simp
  guard_target = False
  sorry
```
:::

# 终止性证明

一旦指定了 {tech (key := "measure")}[度量] 并确定了其 {tech (key := "well-founded relation")}[良基关系]，Lean 就会为每个递归调用生成终止性证明目标。

```lean -show
section
variable {α : Type u} {β : α → Type v} {β' : Type v} (more : β') (g : (x : α) → (y : β x) → β' → γ) [WellFoundedRelation γ] (a₁ p₁ : α) (a₂ : β a₁) (p₂ : β p₁)

local notation (name := decRelStx) x " ≺ " y => WellFoundedRelation.rel x y
local notation "…" => more

```

每个递归调用对应的证明目标都形如 {lean}`g a₁ a₂ … ≺ g p₁ p₂ …`，其中：
 * {lean}`g` 是把形参映射到度量值的函数；
 * {name WellFoundedRelation.rel}`≺` 是推断出来的良基关系；
 * {lean}`a₁` {lean}`a₂` {lean}`…` 是递归调用的实参；
 * {lean}`p₁` {lean}`p₂` {lean}`…` 是函数定义的形参。

证明目标的上下文，就是该递归调用所在的局部上下文。
尤其是，局部假设（例如由 `if h : _`、`match h : _ with ` 或 `have` 引入的那些）都是可用的。
如果函数的某个形参是某次模式匹配（例如通过 {keywordOf Lean.Parser.Term.match}`match` 表达式）的 {tech (key := "match discriminant")}[判别项]，那么在证明目标中，这个形参会被细化为与之匹配的模式。

```lean -show
end
```

整体的终止性证明目标由若干个子目标组成，每个递归调用对应一个子目标。
默认情况下，会使用策略 {tactic}`decreasing_trivial` 来证明每个证明目标。
也可以在 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句之后，通过可选的 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句提供自定义策略脚本。
该策略脚本只会运行一次；运行时同时拥有每个证明目标对应的一个子目标，而不是对每个证明目标分别运行。

```lean -show
section
variable {n : Nat}
```

::::example "终止性证明目标"

下面这个 Fibonacci 数的递归定义有两个递归调用，因此终止性证明中会产生两个目标。

```lean +error -keep (name := fibGoals)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals (whitespace := lax) -show
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), (h : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n h
  apply And.intro ?_ ?_
/--
n : Nat
h : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h : ¬n ≤ 1
⊢ n - 2 < n
-/

```



这里的 {tech (key := "measure")}[度量] 就是参数本身，而良基顺序则是自然数上的小于关系。
第一个证明目标要求用户证明：第一次递归调用的实参，也就是 {lean}`n - 1`，严格小于函数的形参 {lean}`n`。

这两个终止性证明都可以很容易地用 {tactic}`omega` 策略解决。

```lean -keep
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  · omega
  · omega
```
::::
```lean -show
end
```

:::example "细化后的参数"

如果函数的某个参数是某次模式匹配的 {tech (key := "match discriminant")}[判别项]，那么证明目标中会出现细化后的参数。

```lean +error -keep (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax) -show
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```

```proofState
∀ (n : Nat), n + 1 < n.succ.succ ∧ n < n.succ.succ := by
  intro n
  apply And.intro ?_ ?_
/--
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
-/

```

:::

:::paragraph
此外，上下文还会被补充进一些额外假设，以便更容易证明终止性。
例如：

 * 在 {ref "if-then-else"}[if-then-else 表达式]的各个分支中，会加入一个断言当前分支条件成立的假设，效果类似于使用依赖式 if-then-else 语法。
 * 在某些高阶函数的函数实参中，函数体的上下文会被补充进关于该实参的假设。

这个列表并不穷尽，而且该机制是可扩展的。
其详细说明见{ref "well-founded-preprocessing"}[预处理一节]。
:::

```lean -show
section
variable {x : Nat} {xs : List Nat} {n : Nat}
```

:::example "增强后的证明目标上下文"

这里，{keywordOf termIfThenElse}`if` 并不会把关于条件（也就是 {lean}`n ≤ 1` 是否成立）的局部假设加入各分支的局部上下文中。


```lean +error -keep (name := fibGoals3)
def fib (n : Nat) :=
  if n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals3 (whitespace := lax) -show
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```

不过，在终止性证明的上下文中，这些假设仍然可用：

```proofState
∀ (n : Nat), («h✝» : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n «h✝»
  apply And.intro ?_ ?_
/--
n : Nat
h✝ : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h✝ : ¬n ≤ 1
⊢ n - 2 < n
-/

```

位于 {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环体内的终止性证明目标也会被增强；这里增强进来的是一个关于 {name}`Std.Legacy.Range` 的成员资格假设：

```lean +error -keep (name := nestGoal3)
def f (xs : Array Nat) : Nat := Id.run do
  let mut s := xs.sum
  for i in [:xs.size] do
    s := s + f (xs.take i)
  pure s
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal3 (whitespace := lax) -show
unsolved goals
xs : Array Nat
s : Nat := xs.sum
i : Nat
h✝ : i ∈ [:xs.size]
⊢ sizeOf (xs.take i) < sizeOf xs
```

```proofState
∀ (xs : Array Nat)
  (i : Nat)
  («h✝» : i ∈ [:xs.size]),
   sizeOf (xs.take i) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
```

类似地，在下列这个（刻意构造的）例子中，终止性证明会额外带上一个说明 {lean}`x ∈ xs` 的假设。

```lean +error -keep (name := nestGoal1)
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.map (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal1 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
```

```proofState
∀ (n : Nat) (xs : List Nat) (x : Nat) («h✝» : x ∈ xs), sizeOf ([] : List Nat) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
/--
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
-/
```

这一特性要求为递归调用所嵌套其下的高阶函数进行特殊设置，详见{ref "well-founded-preprocessing"}[预处理一节]。
下面这个定义除了用一个自定义的等价函数替代 {name}`List.map` 之外，与上面完全相同；此时证明目标的上下文就不会被增强：

```lean +error -keep (name := nestGoal4)
def List.myMap := @List.map
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.myMap (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal4 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
⊢ sizeOf [] < sizeOf xs
```

```proofState
∀ (n : Nat) (xs : List Nat) (x : Nat), sizeOf ([] : List Nat) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
```

:::

```lean -show
end
```


```lean -show
section
```

::::TODO

:::example "嵌套递归调用与子类型"

我（Joachim）本想在这里加入一个好的例子：递归调用彼此嵌套，而且很可能需要在结果中引入一个子类型才能通过。但目前还想不到足够自然、足够漂亮的例子。

:::

::::

# 默认终止性证明策略

如果没有给出 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，那么会隐式使用 {tactic}`decreasing_tactic`，并将其分别应用到每个证明目标上。


:::tactic "decreasing_tactic" +replace

{tactic}`decreasing_tactic` 主要处理元组的字典序：如果积类型左分量 {tech (key := "definitional equality")}[定义相等]，它就应用 {name}`Prod.Lex.right`；否则应用 {name}`Prod.Lex.left`。
按这种方式预处理完元组之后，它会调用 {tactic}`decreasing_trivial` 策略。

:::


:::tactic "decreasing_trivial"

{tactic}`decreasing_trivial` 是一个可扩展的策略，它会应用若干常见启发式来解决终止性目标。
具体来说，它会尝试下列策略与定理：

* {tactic}`simp_arith`
* {tactic}`assumption`
* 定理 {name}`Nat.sub_succ_lt_self`、{name}`Nat.pred_lt_of_lt` 和 {name}`Nat.pred_lt`，用来处理常见的算术目标
* {tactic}`omega`
* {tactic}`array_get_dec` 与 {tactic}`array_mem_dec`，用于证明数组元素的大小小于数组本身的大小
* {tactic}`sizeOf_list_dec`，用于证明列表元素的大小小于列表本身的大小
* {name}`String.Legacy.Iterator.sizeOf_next_lt_of_hasNext` 与 {name}`String.Legacy.Iterator.sizeOf_next_lt_of_atEnd`，用于处理借助 {keywordOf Lean.Parser.Term.doFor}`for` 遍历字符串的情形

这个策略旨在通过 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 继续扩展出更多启发式。

:::


:::example "字典序不回溯"

需要更复杂 {tech (key := "measure")}[度量] 的递归函数，一个经典例子就是 Ackermann 函数：

```lean -keep
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

该度量是一个元组，因此每个递归调用的实参都必须在字典序意义下小于函数形参。
默认的 {tactic}`decreasing_tactic` 可以处理这种情况。

特别要注意，第三个递归调用的第二个实参小于第二个形参，而第一个实参与第一个形参在定义上相等。
这使得 {tactic}`decreasing_tactic` 可以应用 {name}`Prod.Lex.right`。

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

然而，若把函数定义改成下面这样，它就会失败：第三个递归调用的第一个实参虽然可证明小于或等于第一个形参，但二者在句法上并不相等：

```lean -keep +error (name := synack)
def synack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
m n : Nat
⊢ m / 2 + 1 < m + 1
```

由于 {name}`Prod.Lex.right` 不适用，该策略就改用了 {name}`Prod.Lex.left`，从而产生了上面那个无法证明的目标。

这个函数定义可能需要手工证明，并使用更一般的定理 {name}`Prod.Lex.right'`；该定理允许元组的第一个分量（其类型必须是 {name}`Nat`）只需小于或等于，而不必严格相等：
```signature
Prod.Lex.right' {β} (rb : β → β → Prop)
  {a₂ : Nat} {b₂ : β} {a₁ : Nat} {b₁ : β}
  (h₁ : a₁ ≤ a₂) (h₂ : rb b₁ b₂) :
  Prod.Lex Nat.lt rb (a₁, b₁) (a₂, b₂)
```

```lean -keep
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    omega
  -- 下一个目标对应第三个递归调用
  · apply Prod.Lex.right'
    · omega
    · omega
  · apply Prod.Lex.left
    omega
```

{tactic}`decreasing_tactic` 不使用更强的 {name}`Prod.Lex.right'`，因为那样一来在失败时就需要回溯。

:::

# 推断良基递归
%%%
tag := "inferring-well-founded-recursion"
%%%

如果递归函数定义没有指明终止性 {tech (key := "measure")}[度量]，Lean 就会尝试自动发现一个。
如果既没有提供 {keywordOf Lean.Parser.Command.declaration}`termination_by`，也没有提供 {keywordOf Lean.Parser.Command.declaration}`decreasing_by`，Lean 会先尝试{ref "inferring-structural-recursion"}[推断结构递归]，再尝试良基递归。
如果存在 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，则只会尝试良基递归。

为了推断一个合适的终止性 {tech (key := "measure")}[度量]，Lean 会考虑多个 {deftech (key := "basic termination measures")}_基础终止度量_——即类型为 {name}`Nat` 的终止度量——然后尝试这些度量的所有元组组合。

所考虑的基础终止度量有：

* 所有类型带有非平凡 {name}`SizeOf` 实例的形参
* 表达式 `e₂ - e₁`：前提是某个递归调用的局部上下文中有一个类型为 `e₁ < e₂` 或 `e₁ ≤ e₂` 的假设，其中 `e₁` 与 `e₂` 的类型都是 {name}`Nat`，且只依赖于函数形参。 {margin}[这种方法基于 {citehere manolios2006}[] 的工作。]
* 在互递归组中，还会使用一个额外的基础度量，以区分“对组内其他函数的递归调用”和“对当前正在定义函数本身的递归调用”（详见{ref "mutual-well-founded-recursion"}[互良基递归一节]）

{deftech (key := "Candidate measures")}_候选度量_ 是基础度量或基础度量的元组。
如果某个候选度量能让终止性证明策略消去所有证明目标（即由 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 指定的策略；若没有 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，则为 {tactic}`decreasing_trivial`），那么系统就会从中任意选择一个作为自动终止度量。

{keyword}`termination_by?` 子句会显示推断出的终止性注解。
它还可以通过给出的建议或代码操作自动加入源文件。

为了避免尝试所有度量元组所带来的组合爆炸，Lean 会先把所有 {tech (key := "basic termination measures")}[基础终止度量] 制成表格，判断每个基础度量是“递减”“严格递减”还是“非递减”。
所谓递减度量，是指它在至少一个递归调用处变小，且在任何递归调用处都不会增大；所谓严格递减度量，则是在所有递归调用处都变小。
非递减度量则是指终止性策略无法证明其递减或严格递减。
随后会根据这张表来选取合适的元组。{margin}[这种方法基于 {citehere bulwahn2007}[]。]
当找不到自动度量时，这张表会显示在错误消息中。

{spliceContents Manual.RecursiveDefs.WF.GuessLexExample}

```lean -show
section
variable {e₁ e₂ i j : Nat}
```
:::example "数组索引"

把 {lean}`e₂ - e₁` 形式的表达式纳入度量候选，目的是支持一种常见写法：向某个上界递增计数，尤其是以各种有趣方式遍历数组时。
在下面这个对有序数组进行二分查找的函数中，这个启发式帮助 Lean 找到了 {lean}`j - i` 这一度量。

```lean (name := binarySearch)
def binarySearch (x : Int) (xs : Array Int) : Option Nat :=
  go 0 xs.size
where
  go (i j : Nat) (hj : j ≤ xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then
        some mid
      else if x < y then
        go i mid
      else
        go (mid + 1) j
    else
      none
  termination_by?
```

从推断出的度量里包含一个冗余的 `j` 可以看出：推断出的终止性论证使用的是某个可行但任意的度量，而不是最优或最简的度量：
```leanOutput binarySearch
Try this:
  [apply] termination_by (j, j - i)
```

:::

```lean -show
end
```

:::example "推断期间的终止性证明策略"

由 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 指定的策略，在推断终止性 {tech (key := "measure")}[度量] 时与在实际终止性证明中使用时略有不同。

* 在推断期间，它只会应用于_单个_目标，尝试证明 {name LT.lt}`<` 或 {name LE.le}`≤` 在 {name}`Nat` 上成立。
* 在终止性证明期间，它会面对多个同时存在的目标（每个递归调用一个），且这些目标可能涉及二元组的字典序。

因此，某个 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 代码块即便在显式给出终止性论证时能够逐个解决目标，也可能导致终止度量的推断失败：

```lean -keep +error
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    omega
```

因此，只要写了显式的 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 证明，通常都建议同时写上 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句。

:::

:::example "推断过于强大"

由于 {tactic}`decreasing_tactic` 在字典序方面并不完备，以此避免回溯，Lean 可能会推断出某个终止性 {tech (key := "measure")}[度量]，但由此产生的目标却是该策略本身无法证明的。
此时，错误消息反映的是 策略证明失败，而不是“无法找到度量”。
{lean}`notAck` 中发生的正是这种情况：

```lean +error (name := badInfer)
def notAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => notAck m 1
  | m + 1, n + 1 => notAck m (notAck (m / 2 + 1) n)
decreasing_by all_goals decreasing_tactic
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
m n : Nat
⊢ m / 2 + 1 < m + 1
```

在这种情况下，显式写出终止性 {tech (key := "measure")}[度量] 会有帮助。

:::

# 互良基递归
%%%
tag := "mutual-well-founded-recursion"
%%%

Lean 支持用 {tech (key := "well-founded recursion")}[良基递归] 来定义 {tech (key := "mutually recursive")}[互递归] 函数。
互递归既可以通过 {tech (key := "mutual block")}[互递归块] 引入，也可能来自 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 代码块。
互良基递归的规则，会应用到由互递归组的{ref "mutual-syntax"}[精译步骤]所得、经过提升后且实际上互相递归的一组定义上。

如果互递归组中的任意一个函数带有 {keywordOf Lean.Parser.Command.declaration}`termination_by` 或 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，就会尝试良基递归。
如果互递归组中_任意_一个函数通过 {keywordOf Lean.Parser.Command.declaration}`termination_by` 指定了终止性 {tech (key := "measure")}[度量]，那么组内_所有_函数都必须指定终止度量，而且这些度量必须具有相同的类型。

如果没有指定终止性论证，则会像上文所述那样{ref "inferring-well-founded-recursion"}[自动推断]。在互递归的情况下，推断时还会考虑第三类基础度量：对互递归组中的每个函数，各自有一个在该函数上取 `1`、在其他函数上取 `0` 的度量。这使得 Lean 能对这些函数本身排序，从而允许某些“从一个函数调用另一个函数”的情况，即使形参并未减小。

:::example "参数不下降的互递归"

在下面这组互递归函数定义中，从 {lean}`g` 调用 {lean}`f` 时参数并没有减小。
尽管如此，由于额外的基础度量对函数本身施加了顺序，这个定义仍会被接受。

```lean (name := fg)
mutual
  def f : (n : Nat) → Nat
    | 0 => 0
    | n + 1 => g n
  termination_by?

  def g (n : Nat) : Nat := (f n) + 1
  termination_by?
end
```

为 {lean}`f` 推断出的终止性论证是：
```leanOutput fg
Try this:
  [apply] termination_by n => (n, 0)
```

为 {lean}`g` 推断出的终止性论证是：
```leanOutput fg
Try this:
  [apply] termination_by (n, 1)
```

:::

# 函数定义的预处理
%%%
tag := "well-founded-preprocessing"
%%%

在确定每个调用点的证明目标之前，Lean 会先对函数体做_预处理_，把它变换成一个等价但可能携带附加信息的定义。
这个预处理步骤主要用于向局部上下文补充求解终止性证明目标所必需的额外假设，从而免去用户手工做等价变换。
预处理会使用{ref "the-simplifier"}[化简器]，并且用户可以扩展它。

:::paragraph

预处理分三步进行：

1.  Lean 会用 {name}`wfParam` {tech (key := "gadget")}[小工具] 标注函数形参，或形参某个子项的各次出现。

    ```signature
    wfParam {α} (a : α) : α
    ```

    更精确地说，函数形参的每次出现都会被包上一层 {name}`wfParam`。
    只要某个 {keywordOf Lean.Parser.Term.match}`match` 表达式有_任意一个_判别项被 {name}`wfParam` 包裹，这个小工具就会被移除，并且所有模式匹配变量的每次出现（无论它是否来自那个带有 {name}`wfParam` 小工具的判别项）都会改为包上一层 {name}`wfParam`。
    此外，{name}`wfParam` 小工具还会从 {tech (key := "projection function")}[投影函数] 应用中被上浮出来。

2.  带标注的函数体会使用{ref "the-simplifier"}[化简器]进行化简，并且只使用来自 {attr}`wf_preprocess` {tech (key := "custom simp set")}[自定义 simp 集] 的化简规则。

3.  最后，移除所有残留的 {name}`wfParam` 标记。

对用于良基递归的函数形参进行这种标注，可以让预处理的化简规则区分“形参”和“其他项”。
:::

:::syntax attr (title := "良基递归的预处理 Simp 集")
```grammar
wf_preprocess
```

{zhincludeDocstring Lean.Parser.Attr.wf_preprocess ZhDoc.RecursiveDefs.WF.Parser.Attr.wf_preprocess}

:::

{zhdocstring wfParam ZhDoc.RecursiveDefs.WF.wfParam}

{attr}`wf_preprocess` simp 集中的某些重写规则会无条件地一般适用，而不理会 {lean}`wfParam` 标记。
特别地，定理 {name}`ite_eq_dite` 会被用来扩展 {ref "if-then-else"}[if-then-else 表达式]各分支的上下文，在其中加入关于条件的一个假设：{margin}[这个假设的名字应当是一个基于 `h` 的不可访问名；这一点可由对项 {lean}`()` 使用 {name}`binderNameHint` 看出。绑定变量名提示见{ref "bound-variable-name-hints"}[策略语言参考]。]

```signature
ite_eq_dite {P : Prop} {α : Sort u} {a b : α} [Decidable P]  :
  (if P then a else b) =
  if h : P then
    binderNameHint h () a
  else
    binderNameHint h () b
```


```lean -show
section
variable (xs : List α) (p : α → Bool) (f : α → β) (x : α)
```

:::paragraph

其他重写规则则会利用 {name}`wfParam` 标记来限制自身的适用范围；它们只在某个函数（例如 {name}`List.map`）作用于一个形参或其子项时才会使用，否则不会。
这通常分两步完成：

1.  像 {name}`List.map_wfParam` 这样的定理，会识别 {name}`List.map` 作用于函数形参（或其子项）的调用，并借助 {name}`List.attach` 用“它们确实是该列表元素”这一断言来丰富列表元素的类型：

    ```signature
    List.map_wfParam (xs : List α) (f : α → β) :
      (wfParam xs).map f = xs.attach.unattach.map f
    ```
2. 像 {name}`List.map_unattach` 这样的定理，会让这个断言对 {name}`List.map` 的函数参数可用。

    ```signature
    List.map_unattach (P : α → Prop)
      (xs : List { x : α // P x }) (f : α → β) :
      xs.unattach.map f = xs.map fun ⟨x, h⟩ =>
        binderNameHint x f <|
        binderNameHint h () <|
        f (wfParam x)
    ```

  如果 {lean}`f` 是一个 lambda 表达式，这个定理会使用 {name}`binderNameHint` 小工具来保留用户选择的绑定变量名。

通过把 {name}`List.attach` 的引入与所引入假设的传播分离开来，即使是在 `(xs.reverse.filter p).map f` 这样的链式调用中，也能把期望的 {lean}`x ∈ xs` 假设提供给 {lean}`f`。

:::

```lean -show
end
```

可以通过把选项 {option}`wf.preprocess` 设为 {lean}`false` 来关闭这一预处理。
若想查看预处理后的函数定义（包括移除 {name}`wfParam` 标记之前和之后的版本），可将选项 {option}`trace.Elab.definition.wf` 设为 {lean}`true`。

{zhOptionDocs trace.Elab.definition.wf ZhDoc.RecursiveDefs.WF.Option.traceElabDefinitionWf}

{spliceContents Manual.RecursiveDefs.WF.PreprocessExample}

# 理论与构造

```lean -show
section
variable {α : Type u}
```

本节极其简要地介绍一下通过 {tech (key := "well-founded recursion")}[良基递归] 给出终止性证明所依赖的数学构造；这些构造偶尔会显露到表面。
良基递归函数的精译建立在算子 {name}`WellFounded.fix` 之上。

{zhdocstring WellFounded.fix ZhDoc.RecursiveDefs.WF.WellFounded.fix}

类型 {lean}`α` 会实例化为函数的（会变化的）形参，并用 {name}`PSigma` 将它们打包成一个类型。
{name}`WellFounded` 关系则通过 {name}`invImage` 由终止性 {tech (key := "measure")}[度量] 构造出来。

{zhdocstring invImage ZhDoc.RecursiveDefs.WF.invImage}

函数体会被传给 {name}`WellFounded.fix`，其中形参会被适当地打包与拆包，而递归调用则替换为对 {name}`WellFounded.fix` 所提供值的调用。
由 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 策略生成的终止性证明，会插入到恰当的位置。

最后，递归函数的等式定理与展开定理会从 {name}`WellFounded.fix_eq` 推导出来。
这些定理隐藏了打包与拆包实参的细节，并以原始定义的形式描述函数行为。

在互递归的情况下，会用 {name}`PSum` 把函数的实参合并起来，从而构造一个等价的非互递归函数，并在结果类型与函数体中对该和类型做模式匹配。

{name}`WellFounded` 的定义建立在关系的_可达元素_这一概念之上：

{zhdocstring WellFounded ZhDoc.RecursiveDefs.WF.WellFounded}

{zhdocstring Acc ZhDoc.RecursiveDefs.WF.Acc}

::: example "通过反复减法定义除法：终止性证明"

通过反复减法定义除法的写法，也可以显式地借助良基递归来表达。
```lean
noncomputable def div (n k : Nat) : Nat :=
  (inferInstance : WellFoundedRelation Nat).wf.fix
    (fun n r =>
      if h : k = 0 then 0
      else if h : k > n then 0
      else 1 + (r (n - k) <| by
        show (n - k) < n
        omega))
    n
```
该定义必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为编译器不支持良基递归。
和 {tech (key := "recursors")}[递归器] 一样，它属于 Lean 逻辑的一部分。

这个除法定义应满足下列方程：
 * {lean}`∀{n k : Nat}, (k = 0) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k > n) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k ≠ 0) → (¬ k > n) → div n k = 1 + div (n - k) k`

这种归约行为并不 {tech (key := "definitional equality")}[在定义上] 成立：
```lean +error (name := nonDef) -keep
theorem div.eq0 : div n 0 = 0 := by rfl
```
```leanOutput nonDef
Tactic `rfl` failed: The left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0

n : Nat
⊢ div n 0 = 0
```
不过，借助 `WellFounded.fix_eq` 展开良基递归之后，这三个方程都可以被证明成立：
```lean
theorem div.eq0 : div n 0 = 0 := by
  unfold div
  apply WellFounded.fix_eq

theorem div.eq1 : k > n → div n k = 0 := by
  intro h
  unfold div
  rw [WellFounded.fix_eq]
  simp only [gt_iff_lt, dite_eq_ite, ite_eq_left_iff, Nat.not_lt]
  intros; omega

theorem div.eq2 :
    ¬ k = 0 → ¬ (k > n) →
    div n k = 1 + div (n - k) k := by
  intros
  unfold div
  rw [WellFounded.fix_eq]
  simp_all only [
    gt_iff_lt, Nat.not_lt,
    dite_false, dite_eq_ite,
    ite_false, ite_eq_right_iff
  ]
  omega
```
:::
