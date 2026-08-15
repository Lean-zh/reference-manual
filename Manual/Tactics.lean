/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Tactics

import Manual.Tactics.Reference
import Manual.Tactics.Conv
import Manual.Tactics.Custom

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

#doc (Manual) "策略证明" =>
%%%
tag := "tactics"
file := "Tactic-Proofs"
%%%

策略语言是一种用于构造证明的专用编程语言。
在 Lean 中，{tech (key := "propositions")}[命题]由类型表示，而证明则是这些类型的项。
{margin}[{ref "propositions"}[命题一节]更详细地介绍了命题。]
项的设计目标是便于指出类型的某个特定元素，而策略的设计目标则是便于证明某个类型存在元素。
之所以作此区分，是因为定义必须精确地选出所关注的对象、程序必须返回预期结果；但证明无关性意味着，从_技术_上说，并没有理由偏好某个证明项而非另一个。
例如，给定同一类型的两个假设时，程序必须仔细编写以使用正确的那个，而证明使用任一个都不会造成影响。

策略是修改{deftech (key := "proof state")}_证明状态_的命令式程序。{index}[proof state]
证明状态由一列有序的{deftech (key := "goals")}_目标_组成；每个目标都是局部假设的上下文以及一个需要构造元素的类型。策略可能_成功_并产生一列可能为空的后续目标（称为{deftech (key := "subgoals")}_子目标_），也可能因无法取得进展而_失败_。
如果策略成功且没有子目标，证明就完成了。
如果策略成功并产生一个或多个子目标，那么当这些子目标都得到证明时，原目标也就得到证明。
证明状态中的第一个目标称为{deftech (key := "main goal")}_主目标_。{index (subterm := "main")}[goal]{index}[main goal]
大多数策略只影响主目标，但可以用 {tactic}`<;>` 和 {tactic}`all_goals` 等运算符将策略应用到多个目标；也可以用项目符号、{tactic}`next` 或 {tactic}`case` 等运算符，将后续策略的焦点缩小到证明状态中的单个目标。

在幕后，策略会构造{deftech (key := "proof terms")}[证明项]。
证明项是以 Lean 类型论书写、可独立检查的定理成立证据。
每个证明都会由{tech (key := "kernel")}[内核]检查，也可由独立实现的外部检查器验证；因此，策略中的缺陷最坏只会导致令人困惑的错误消息，而不会产生错误的证明。
策略证明中的每个目标都对应证明项中尚未完成的一部分。

# 运行策略
%%%
tag := "by"
file := "Running-Tactics"
%%%

:::TODO
下面展示的 `by` 语法使用了逗号而不是分号
:::

:::syntax Lean.Parser.Term.byTactic (title := "使用 {keyword}`by` 的策略证明")
使用 {keywordOf Lean.Parser.Term.byTactic}`by` 可在项中包含策略；其后是一列缩进相同的策略：
```grammar
by
$t
```

也可以改用显式的大括号和分号：
```grammar
by { $t* }
```
:::

策略通过 {keywordOf Lean.Parser.Term.byTactic}`by` 项调用。
精译器遇到 {keywordOf Lean.Parser.Term.byTactic}`by` 时，会调用策略解释器来构造结果项。
凡是允许出现项的上下文，都可以通过 {keywordOf Lean.Parser.Term.byTactic}`by` 嵌入策略证明。

# 阅读证明状态
%%%
tag := "proof-states"
file := "Reading-Proof-States"
%%%

证明状态中的目标按顺序显示，主目标位于最上方。
目标可以具名，也可以匿名。
具名目标的顶部以 `case` 标示（称为{deftech (key := "case label")}_分支标签_），匿名目标则没有这种标示。
策略会为目标分配名称，通常依据构造器名称、参数名称、结构字段名称，或策略所实现推理步骤的性质来命名。

::::example (file := "Named goals") "具名目标"
```customCSS
#lawful-option-cases .goal-name { background-color: var(--lean-compl-yellow); }
```

此证明状态包含四个目标，并且全都有名称。
这是证明 {lean}`Monad Option` 实例满足定律（即提供 {lean}`LawfulMonad Option` 实例）的一部分；分支名称（在下方突出显示）来自 {name}`LawfulMonad` 的字段名。

```proofState (tag := "lawful-option-cases")
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
intro α β γ x f g
rotate_right
intro α β x f
rotate_right
intro α β f x
rotate_right
```
::::


::::example (file := "Anonymous Goals") "匿名目标"
此证明状态包含一个匿名目标。

```proofState
∀ (n k : Nat), n + k = k + n := by
intro n k
```
::::

可以使用 {tactic}`case` 和 {tactic}`case'` 策略，按目标名称选择新的主目标。
在本身具名的目标上下文中分配名称时，新目标的名称会附加到主目标名称之后，并以点号（`'.', Unicode FULL STOP (0x2e)`）分隔。

::::example (file := "Hierarchical Goal Names") "分层目标名称"

:::tacticExample
```setup
intro n k
induction n
```


尝试证明 {goal}`∀ (n k : Nat), n + k = k + n` 的过程中，可能出现此证明状态：
```pre
case zero
k : Nat
⊢ 0 + k = k + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```

执行 {tacticStep}`induction k` 后，两个新分支的名称都以 `zero` 为前缀，因为它们是在名为 `zero` 的目标中创建的：

```customCSS
#hierarchical-case-names .goal:not(:last-child) .goal-name { background-color: var(--lean-compl-yellow); }
```

```post (tag := "hierarchical-case-names")
case zero.zero
⊢ 0 + 0 = 0 + 0

case zero.succ
n✝ : Nat
a✝ : 0 + n✝ = n✝ + 0
⊢ 0 + (n✝ + 1) = n✝ + 1 + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```
:::
::::


每个目标都由一列假设和一个待证结论组成。
每个假设都有名称和类型；结论则是一个类型。
假设要么是某个类型的任意元素，要么是被假定为真的陈述。

::::example (file := "Assumption Names and Conclusion") "假设名称与结论"

```customCSS
#ex-assumption-names .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

此目标有四个假设：

```proofState (tag := "ex-assumption-names")
∀ (α) (xs : List α), xs ++ [] = xs := by
intro α xs
induction xs
sorry
rename_i x xs ih
```

:::keepEnv
```lean -show
axiom α : Type
axiom x : α
axiom xs : List α
axiom ih : xs ++ [] = xs
```

它们是：

 * {lean}`α`，任意类型
 * {lean}`x`，任意的 {lean}`α`
 * {lean}`xs`，任意的 {lean}`List α`
 * {lean}`ih`，归纳假设，断言在 {lean}`xs` 后追加空列表仍等于 {lean}`xs`。

结论断言：在归纳假设的等式两边都前置 `x`，所得列表仍然相等。
:::

::::

有些假设是{deftech (key := "inaccessible")}_不可访问的_，{index}[inaccessible] {index (subterm := "inaccessible")}[assumption]这意味着无法按名称显式引用它们。
创建假设时未指定名称，或假设名称被后来的假设遮蔽时，就会出现不可访问的假设。
不可访问的假设应视为匿名假设；之所以仍显示得像是具名，是因为后续假设或结论可能引用它们，而显示名称可以区分这些引用。
具体而言，不可访问假设的名称后会显示剑标（`†`）。


::::example (file := "Accessible Assumption Names") "可访问的假设名称"
```customCSS
#option-cases-accessible .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

在此证明状态中，所有假设都可访问。

```proofState (tag := "option-cases-accessible")
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


::::example (file := "Inaccessible Assumption Names") "不可访问的假设名称"
```customCSS
#option-cases-inaccessible .hypotheses .hypothesis:nth-child(even) .name { background-color: var(--lean-compl-yellow); }
```

在此证明状态中，只有第一个和第三个假设可访问。
第二个和第四个假设不可访问，其名称中的剑标表示无法引用它们。

```proofState (tag := "option-cases-inaccessible")
LawfulMonad Option := by
constructor
intro α _ f _
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


不可访问的假设仍然可以使用。
{tactic}`assumption` 或 {tactic}`simp` 等策略可以扫描整个假设列表并找出有用的假设；{tactic}`contradiction` 则能找出不可能成立的假设来消除当前目标，而无需为其命名。
{tactic}`rename_i` 和 {tactic}`next` 等其他策略可以为不可访问的假设命名，使其变得可访问。
此外，还可以把类型写在单书名号中，按类型引用假设。

::::syntax term (title := "按类型引用假设")
用单书名号括起一个项，表示引用作用域内具有该类型的某个项。

```grammar
‹$t›
```

这样便可按定理陈述而非名称引用局部引理，也可引用假设而不论其是否有显式名称。
::::

::::example (file := "Assumptions by Type") "按类型引用假设"

:::keepEnv
```lean -show
variable (n : Nat)
```
在以下证明中，反复使用 {tactic}`cases` 分析一个数。
证明开始时，这个数名为 `x`，但 {tactic}`cases` 会为后续的数生成不可访问的名称。
该证明没有提供名称，而是利用任一时刻都只有一个 {lean}`Nat` 类型假设这一事实，以 {lean}`‹Nat›` 引用它。
迭代结束后会有假设 `n + 3 < 3`，{tactic}`contradiction` 可以利用它消除该目标。
:::
```lean
example : x < 3 → x ∈ [0, 1, 2] := by
  intros
  iterate 3
    cases ‹Nat›
    . decide
  contradiction
```
::::

::::example (file := "Assumptions by Type, Outside Proofs") "证明之外按类型引用假设"

单书名号语法在证明之外也可使用：

```lean (name := evalGuillemets)
#eval
  let x := 1
  let y := 2
  ‹Nat›
```
```leanOutput evalGuillemets
2
```

不过，对于非命题而言，这通常不是好主意——当选中的是类型中的_哪个_元素很重要时，最好显式选择。
::::

## 隐藏证明与大型项
%%%
tag := "hiding-terms-in-proof-states"
file := "Hiding Proofs and Large Terms"
%%%

证明状态中的项可能相当庞大，假设也可能很多。
由于定义式证明无关性，证明项通常提供不了多少有用信息。
默认情况下，它们不会显示在证明状态的目标中，除非它们是{deftech (key := "atomic")}_原子的_，即不包含子项。
隐藏证明由两个选项控制：{option}`pp.proofs` 用于开关该功能，{option}`pp.proofs.threshold` 则确定隐藏证明的大小阈值。

:::example (file := "Hiding Proof Terms") "隐藏证明项"
在此证明状态中，`0 < n` 的证明被隐藏了。

```proofState
∀ (n : Nat) (i : Fin n), i.val > 5 → (⟨0, by cases i; omega⟩ : Fin n) < i := by
  intro n i gt
/--
n : Nat
i : Fin n
gt : ↑i > 5
⊢ ⟨0, ⋯⟩ < i
-/

```
:::



{zhOptionDocs pp.proofs ZhDoc.Tactics.Option.pp.proofs}

{zhOptionDocs pp.proofs.threshold ZhDoc.Tactics.Option.pp.proofs.threshold}


此外，非证明项过大时也可能被隐藏。
具体而言，Lean 会隐藏深度超过可配置阈值的项；总输出量达到一定程度后，也会隐藏项的其余部分。
可以用选项 {option}`pp.deepTerms` 启用或禁用深层项显示，并用 {option}`pp.deepTerms.threshold` 配置深度阈值。
美化打印器的最大步数可用选项 {option}`pp.maxSteps` 配置。
打印非常大的项可能导致工具变慢，甚至栈溢出；调整这些选项的值时请务必谨慎。

{zhOptionDocs pp.deepTerms ZhDoc.Tactics.Option.pp.deepTerms}

{zhOptionDocs pp.deepTerms.threshold ZhDoc.Tactics.Option.pp.deepTerms.threshold}

{zhOptionDocs pp.maxSteps ZhDoc.Tactics.Option.pp.maxSteps}

## 元变量
%%%
tag := "metavariables-in-proofs"
file := "Metavariables"
%%%

以问号开头的项是{deftech (key := "metavariables")}_元变量_，对应某个未知值。
它们既可以代表{tech (key := "universe")}[宇宙]层级，也可以代表项。
有些元变量产生于 Lean 的精译过程，即现有信息尚不足以确定某个值之时。
这些元变量名称的末尾带有数字部分，例如 `?m.392` 或 `?u.498`。
其他元变量则由策略或{tech (key := "synthetic holes")}[合成孔洞]产生。
这些元变量的名称不带数字部分。
由策略产生的元变量经常表现为目标，其{tech (key := "case labels")}[分支标签]与元变量名称一致。


::::example (file := "Universe Level Metavariables") "宇宙层级元变量"
在此证明状态中，`α` 的宇宙层级未知：
```proofState
∀ (α : _) (x : α) (xs : List α), x ∈ xs → xs.length > 0 := by
  intros α x xs elem
/--
α : Type ?u.912
x : α
xs : List α
elem : x ∈ xs
⊢ xs.length > 0
-/
```
::::

::::example (file := "Type Metavariables") "类型元变量"
在此证明状态中，列表元素的类型未知。
该元变量重复出现，因为两个位置上的未知类型必须相同。
```proofState
∀ (x : _) (xs : List _), x ∈ xs → xs.length > 0 := by
  intros x xs elem
/--
x : ?m.1035
xs : List ?m.1035
elem : x ∈ xs
⊢ xs.length > 0
-/
```
::::


::::example (file := "Metavariables in Proofs") "证明中的元变量"

:::tacticExample

{goal -show}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

在此证明状态中，
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
应用策略 {tacticStep}`apply Nat.lt_trans` 后得到如下证明状态，其中传递步骤的中间值 `?m` 未知：
```post
case h₁
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?m

case a
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?m < k

case m
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat
```
:::
::::

::::example (file := "Explicitly-Created Metavariables") "显式创建的元变量"
:::tacticExample
{goal -show}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

显式具名孔洞由元变量表示，并且还会产生证明目标。
在此证明状态中，
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
应用策略 {tacticStep}`apply @Nat.lt_trans i ?middle k ?p1 ?p2` 后得到如下证明状态，其中传递步骤的中间值 `?middle` 未知，并为项中的每个具名孔洞创建了目标：
```post
case middle
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat

case p1
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?middle

case p2
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?middle < k
```
:::
::::

可以使用选项 {option}`pp.mvars` 禁用元变量编号的显示。
使用 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 这类将 Lean 输出与预期字符串匹配的功能时，这一点很有用；这类功能对于编写自定义策略测试尤为有用。

{zhOptionDocs pp.mvars ZhDoc.Tactics.Option.pp.mvars}

::::draft
:::planned 68
演示并解释用于显示证明状态各步骤差异的差异标签。
:::
::::

# 策略语言
%%%
tag := "tactic-language"
file := "The-Tactic-Language"
%%%

策略脚本由一列策略组成，各策略之间用分号或换行分隔。
使用换行分隔时，各策略必须具有相同的缩进层级。
可以用显式的花括号和分号代替缩进。
策略序列可以用圆括号分组。
这样便可在语法上原本只接受单个策略的位置使用一列策略。

通常，执行从上到下进行，每个策略都在前一策略留下的证明状态中运行。
策略语言包含多种可以修改这一流程的控制结构。

每个策略都是 `tactic` 类别中的语法扩展。
这意味着策略可以自由定义自己的具体语法和解析规则。
不过，除少数例外，大多数策略都可以通过开头的关键字识别；例外通常是 {tactic}`<;>` 这类常用的内置控制结构。

## 控制结构
%%%
tag := "tactic-language-control"
file := "Control Structures"
%%%

严格来说，控制结构与其他策略之间没有根本区别。
任何策略都可以自由地接受其他策略作为参数，并安排它们在其认为合适的任意上下文中执行。
不过，即使这种区分是人为的，它仍然可能有用。
本节中的策略要么类似于编程中的传统控制结构，要么_仅仅_重新组合其他策略而自身不推进证明。

### 成功与失败
%%%
tag := "tactic-language-success-failure"
file := "Success and Failure"
%%%

在证明状态中运行时，每个策略要么成功，要么失败。
策略失败类似于异常：失败通常会不断“向上冒泡”，直至被处理。
与异常不同，没有运算符可以区分失败原因；{tactic}`first` 只是采用第一个成功的分支。

::: tactic "fail"
:::

:::tactic "fail_if_success"
:::

:::tactic "try"
:::

:::tactic "first"
:::


### 分支
%%%
tag := "tactic-language-branching"
file := "Branching"
%%%

策略证明可以使用模式匹配和条件表达式。
不过，它们的含义与在项中并不完全相同。
项应在变量值已知后执行；而证明执行时变量仍保持抽象，因此应同时考虑_所有_情况。
因此，在策略中使用 {keyword}`if` 和 {keyword}`match` 时，它们表示分类推理，而不是选择某个具体分支。
它们的所有分支都会执行；条件或模式匹配用于在每个分支中以更多信息精化主目标，而不是选出单个分支。

:::tactic "if"

:::

:::example (file := "Reasoning by cases with if") "使用 `if` 分类推理"
在 {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` 的每个分支中，都会加入一个反映 `n = 0` 是否成立的假设。

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
:::

:::tactic Lean.Parser.Tactic.match (show := "match")

进行模式匹配时，目标中{tech (key := "match discriminant")}[判别项]的各个实例会在每个分支中替换为与之匹配的模式。
随后每个分支都必须证明精化后的目标。
与 `cases` 策略相比，使用 `match` 可以让分类分析更加灵活；但每个分支都必须彻底解决其目标，因此更难将其纳入较大的自动化脚本。
:::

:::example (file := "Reasoning by cases with match") "使用 `match` 分类推理"
在 {keywordOf Lean.Parser.Tactic.match}`match` 的每个分支中，判别项 `n` 都被替换为 `0` 或 `k + 1`。
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```
:::

### 目标选择
%%%
tag := "tactic-language-goal-selection"
file := "Goal Selection"
%%%


大多数策略会影响{tech (key := "main goal")}[主目标]。
目标选择策略提供了将其他目标视作主目标的方法，会重新排列证明状态中的目标序列。


:::tactic "case"
:::

:::tactic "case'"
:::


:::tactic "rotate_left"
:::

:::tactic "rotate_right"
:::

#### 顺序执行
%%%
tag := "tactic-language-sequencing"
file := "Sequencing"
%%%

除了依次运行策略、让每个策略解决主目标之外，策略语言还支持根据目标的产生方式来顺序执行策略。
策略组合子 {tactic}`<;>` 可以将某个策略应用到另一策略产生的_每个_{tech (key := "subgoal")}[子目标]。
如果没有产生新目标，就不会运行第二个策略。

:::tactic "<;>"

如果该策略在任一{tech (key := "subgoals")}[子目标]上失败，整个 {tactic}`<;>` 策略就会失败。
:::

::::example (file := "Subgoal Sequencing") "子目标顺序执行"
:::tacticExample

```setup
  intro x h
```


{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

在此证明状态中：
```pre
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```
策略 {tacticStep}`cases h` 会产生以下两个目标：
```post
case inl
x : Nat
h✝ : x = 1
⊢ x < 3

case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::
:::tacticExample

```setup
  intro x h
```

{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre -show
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

运行 {tacticStep}`cases h ; simp [*]` 后，{tactic}`simp` 会解决第一个目标，留下第二个目标：
```post
case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::

:::tacticExample

```setup
  intro x h
```

{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre -show
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

将 `;` 替换为 {tactic}`<;>` 并运行 {tacticStep}`cases h <;> simp [*]`，会用 {tactic}`simp` 解决新产生的_两个_目标：

```post

```

:::

::::

#### 处理多个目标
%%%
tag := "tactic-language-multiple-goals"
file := "Working on Multiple Goals"
%%%

策略 {tactic}`all_goals` 和 {tactic}`any_goals` 允许将一个策略应用到证明状态中的每个目标。
两者的区别在于：如果策略在任一目标上失败，{tactic}`all_goals` 自身就会失败；而只有策略在所有目标上都失败时，{tactic}`any_goals` 才会失败。

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::


### 聚焦
%%%
tag := "tactic-language-focusing"
file := "Focusing"
%%%

聚焦策略会让后续策略不再考虑证明目标的某个子集（通常只留下主目标）。
除这里介绍的策略外，{tactic}`case` 和 {tactic}`case'` 策略也会聚焦于所选目标。

:::tactic Lean.cdot (show := "·")

通常认为，只要一行策略产生了多个新子目标，使用项目符号就是良好的 Lean 风格。
这样证明更易阅读和维护，因为推理步骤之间的联系更加清晰，而且编辑证明时子目标数量的任何变化都只会产生局部影响。
:::

:::tactic "next"
:::


:::tactic "focus"
:::

### 重复与迭代
%%%
tag := "tactic-language-iteration"
file := "Repetition and Iteration"
%%%

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


## 名称与卫生性
%%%
tag := "tactic-language-hygiene"
file := "Names and Hygiene"
%%%

在幕后，策略会生成证明项。
这些证明项存在于局部上下文中，因为证明状态中的假设对应项中的局部绑定器。
使用假设对应于引用变量。
假设的命名必须可预测，这一点非常重要；否则，策略内部实现的微小变更一旦导致选中不同的名称，就可能引发变量捕获或引用失效。

Lean 的策略语言具有_卫生性_。{index (subterm := "in tactics")}[hygiene]
这意味着策略语言遵守词法作用域：策略中出现的名称引用源代码中包围它的绑定，而不是由生成的代码决定；策略框架负责维持这一性质。
策略脚本中的变量引用，要么指向脚本开始时就在作用域内的名称，要么指向策略显式引入的绑定，而不是幕后为证明项选用的名称。

策略具有卫生性的一个结果是：引用假设的唯一方式是显式为其命名。
策略不能自行分配假设名称，而必须接受用户提供的名称；相应地，用户若想引用某个假设，就必须为其提供名称。
当假设没有用户提供的名称时，它在证明状态中显示时会带有剑标（`'†', DAGGER\t0x2020`）。
剑标表示该名称_不可访问_，无法被显式引用。

将选项 {option}`tactic.hygienic` 设为 `false` 可以禁用卫生性。
不建议这样做，因为许多策略依赖卫生系统来防止捕获，因而无需付出仔细手动选择名称的开销。

{zhOptionDocs tactic.hygienic ZhDoc.Tactics.Option.tactic.hygienic}

::::example (file := "Tactic hygiene: inaccessible assumptions") "策略卫生性：不可访问的假设"
:::tacticExample

```setup
skip
```
证明 {goal}`∀ (n : Nat), 0 + n = n` 时，初始证明状态为：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

策略 {tacticStep}`intro` 会产生一个带有不可访问假设的证明状态：

```post
n✝ : Nat
⊢ 0 + n✝ = n✝
```
:::
::::

::::example (file := "Tactic hygiene: accessible assumptions") "策略卫生性：可访问的假设"
:::tacticExample

```setup
skip
```
证明 {goal}`∀ (n : Nat), 0 + n = n` 时，初始证明状态为：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

策略 {tacticStep}`intro n` 显式提供名称 `n`，会产生一个假设名称可访问的证明状态：

```post
n : Nat
⊢ 0 + n = n
```
:::
::::

### 访问假设
%%%
tag := "tactic-language-assumptions"
file := "Accessing Assumptions"
%%%

许多策略提供了为其引入的假设指定名称的方法。
{tactic}`intro` 和 {tactic}`intros` 例如会接受假设名称作为参数；{tactic}`induction` 的 {keywordOf Lean.Parser.Tactic.induction}`with` 形式则可以同时选择分支、命名假设并聚焦。
假设没有名称时，可以使用 {tactic}`next`、{tactic}`case` 或 {tactic}`rename_i` 为其分配名称。

:::tactic "rename_i"
:::

## 假设管理
%%%
tag := "tactic-language-assumption-management"
file := "Assumption Management"
%%%

较大的证明可受益于证明状态管理：移除无关假设，并使假设名称更易理解。
除这些运算符外，{tactic}`rename_i` 可以重命名不可访问的假设；{tactic}`intro`、{tactic}`intros` 和 {tactic}`rintro` 则把蕴含或全称量化目标转换为带有额外假设的目标。

:::tactic "rename"
:::

:::tactic "revert"
:::

:::tactic "clear"
:::


## 局部定义与证明
%%%
tag := "tactic-language-local-defs"
file := "Local Definitions and Proofs"
%%%

{tactic}`have` 和 {tactic}`let` 都会创建局部假设。
一般来说，证明中间引理时应使用 {tactic}`have`；{tactic}`let` 应留给局部定义。

:::tactic Lean.Parser.Tactic.tacticHave__
:::

:::tactic Lean.Parser.Tactic.tacticHave'
:::

:::tactic Lean.Parser.Tactic.tacticLet__ (show := "let")
:::

:::tactic Lean.Parser.Tactic.letrec (show := "let rec")
:::

:::tactic Lean.Parser.Tactic.tacticLetI__
:::

:::tactic Lean.Parser.Tactic.tacticLet'__
:::

## 配置
%%%
tag := "tactic-config"
file := "Configuration"
%%%

许多策略都可配置。{index (subterm := "of tactics")}[configuration]
按照约定，各策略共享一种配置语法，以 {syntaxKind}`optConfig` 描述。
每个策略可用的具体选项会在该策略的文档中说明。

:::syntax Lean.Parser.Tactic.optConfig -open (title := "策略配置")
策略配置由零个或多个{deftech (key := "configuration items")}[配置项]组成：
```grammar
$x:configItem*
```
:::

:::syntax Lean.Parser.Tactic.configItem -open (title := "策略配置项")
每个配置项都有一个名称，对应底层的策略选项。
布尔选项可以使用前缀 `+` 和 `-` 启用或禁用：
```grammar
+$x
```
```grammar
-$x
```

可以使用类似于具名函数参数的语法，为选项赋予具体值：
```grammar
($x:ident := $t)
```

最后，名称 `config` 是保留名称，用于将整组选项作为数据结构传递。
所需的具体类型取决于策略。
```grammar
(config := $t)
```

:::

## 命名空间与选项管理
%%%
tag := "tactic-language-namespaces-options"
file := "Namespace and Option Management"
%%%

在策略脚本中，可以使用与项中相同的语法调整命名空间和选项。

:::tactic Lean.Parser.Tactic.set_option (show := "set_option")
:::

:::tactic Lean.Parser.Tactic.open (show := "open")
:::

### 控制展开
%%%
tag := "tactic-language-unfolding"
file := "Controlling Unfolding"
%%%

默认情况下，除检查定义相等性时外，只有标记为可归约的定义才会展开。
这些运算符可以在策略脚本的某一部分调整此默认行为。

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


# 选项
%%%
tag := "tactic-language-options"
file := "Options"
%%%

这些选项会影响策略的含义。

{zhOptionDocs tactic.customEliminators ZhDoc.Tactics.Option.tactic.customEliminators}

{zhOptionDocs tactic.skipAssignedInstances ZhDoc.Tactics.Option.tactic.skipAssignedInstances}

{zhOptionDocs tactic.simp.trace ZhDoc.Tactics.Option.tactic.simp.trace}


{include 0 Manual.Tactics.Reference}

{include 0 Manual.Tactics.Conv}

# 命名绑定变量
%%%
tag := "bound-variable-name-hints"
file := "Naming-Bound-Variables"
%%%

当{ref "the-simplifier"}[简化器]或 {tactic}`rw` 策略引入函数参数等新的绑定形式时，会根据所应用重写规则的陈述中的名称，为绑定变量选择名称。
必要时会使该名称保持唯一。
在某些情况下，例如{ref "well-founded-preprocessing"}[为使用良基递归的终止性证明预处理定义]时，终止性证明义务中出现的名称应当是原函数定义中写下的对应名称。

{name}`binderNameHint` {tech (key := "gadget")}[小工具]可用于指示：应根据其他某个项中绑定的变量来命名一个绑定变量。
按照约定，项 {lean}`()` 用于表示名称_不应_取自原定义。

{zhdocstring binderNameHint ZhDoc.Tactics.binderNameHint}


{include 0 Manual.Tactics.Custom}
