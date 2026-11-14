/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Upstream
import Manual.Papers

import Std.WP
import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option experimental.vcgen true

open Manual (comment)

open Std.WP Lean.Order

#doc (Manual) "`vcgen` 策略" =>
%%%
file := "The--vcgen--tactic"
tag := "vcgen-tactic"
%%%

:::tutorials
 * {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[使用 `vcgen` 验证命令式程序]
:::

{tactic}`vcgen` 策略实现了一个_验证条件生成器_：
它将涉及程序（例如用 Lean 命令式 {keywordOf Lean.Parser.Term.do}`do` 记法编写的程序）的目标分解成若干更小的{tech (key := "verification conditions")}_验证条件_（{deftech (key := "VCs")}[VC]），这些条件足以证明原目标。
除介绍 {tactic}`vcgen` 用法的参考资料外，本章还包含一篇可独立阅读的{ref "vcgen-tactic-tutorial" (remote := "tutorials")}[教程]。

要使用 {tactic}`vcgen`，必须导入 {module}`Std.WP` 和 {module}`Std.Tactic.Do`，并打开命名空间 {namespace}`Std.WP` 与 {namespace}`Lean.Order`。
对 {namespace}`Lean.Order` 的依赖是暂时的：此命名空间包含 {ref "partial-fixpoint-theory"}[{keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 背后的序理论]，这些内容尚未移至 {namespace}`Std`。


:::syntax tactic (title := "生成验证条件")
```grammar
vcgen $cfg:optConfig $[[$x,*]]?
  $[until $_]?
  $[invariants $inv*]?
  $[simplifying_assumptions $[$_]? $[[$_,*]]?]?
  $[with $_]?
```

为当前目标生成{tech (key := "verification conditions")}[验证条件]。

{keywordOf Lean.Parser.Tactic.vcgen}`until` 子句在首个匹配给定模式的目标处停止生成验证条件。
{keywordOf Lean.Parser.Tactic.vcgen}`invariants` 子句用于指定{tech (key := "loop invariants")}[循环不变式]。
生成验证条件时会使用这些不变式，它们也可以指导简化和自动化过程。
若存在 {keywordOf Lean.Parser.Tactic.vcgen}`simplifying_assumptions` 子句，则在生成验证条件时引入的假设会以与目标相同的方式简化。
由于 {tactic}`vcgen` 与 {tactic}`grind` 共享大量实现，{keywordOf Lean.Parser.Tactic.vcgen}`with` 子句允许对所有生成的验证条件应用{ref "grind-interactive"}[交互式 `grind` 策略]或普通策略。
:::

# 概览
%%%
file := "Overview"
tag := "Lean-__________________--The--vcgen--tactic--______"
%%%

{tactic}`vcgen` 的工作流程如下：

1. 按照{tech (key := "predicate transformer semantics")}[谓词变换器语义]重新解释程序。
   程序类型的 {name}`WP` 实例决定其解释。
   程序类型可以是单子计算，例如 {lean}`StateM Nat` 中的 {keywordOf Lean.Parser.Term.do}`do` 块。
   也支持非单子类型，例如小型命令式语言的语法树。
   每个程序都被解释为一个映射：它将任意{tech (key := "postcondition")}[后置条件]映射为保证该后置条件成立的{tech (key := "weakest preconditions")}[最弱前置条件]。
   大多数用户看不到这一步，但希望让自己的程序类型支持 {tactic}`vcgen` 的库作者需要理解它。
2. 由较小的程序组合成程序。
   程序的各个部分（例如 {keywordOf Lean.Parser.Term.do}`do` 块中的语句）都对应一个谓词变换器，并有通用规则通过顺序执行与控制流运算组合它们。
   带有前置条件和后置条件的语句称为{tech (key := "Hoare triple")}_霍尔三元组_。
   在程序中，每条语句的后置条件应足以证明下一条语句的前置条件；循环则要求指定{deftech (key := "loop invariant")}_循环不变式_，即在循环开始时及每次迭代结束时都必须为真的命题。
   指定的{tech (key := "Specification lemmas")}_规约引理_将函数与描述其行为的霍尔三元组关联起来。
3. 将程序的最弱前置条件语义应用于预期证明目标，会得到为证明该目标而必须成立的前置条件。
   剩余的断言间蕴涵不再含最弱前置条件，成为新的子目标，例如证明某条语句的后置条件蕴含下一条语句的前置条件。
   这些子目标称为{deftech (key := "verification conditions")}_验证条件_。
   用户提供的循环不变式会成为单独的子目标。
   {tactic}`vcgen` 执行此变换，用验证条件替换原目标。
   变换期间，{tactic}`vcgen` 使用规约引理解决关于各条语句的证明。
4. 给出循环不变式后，实践中许多验证条件都可以自动解决。
   无法自动解决的条件都是普通 Lean 目标，可以用普通 Lean 策略或 {keywordOf Lean.Parser.Tactic.vcgen}`with` 子句中的 {tactic}`grind` 模式步骤证明。


# 谓词变换器概述
%%%
file := "Predicate-Transformers"
tag := "Lean-__________________--The--vcgen--tactic--_____________________"
%%%

{deftech (key := "predicate transformer semantics")}_谓词变换器语义_将程序解释为从谓词到谓词的函数，而不是从值到值的函数。
{deftech (key := "postcondition")}_后置条件_是在程序运行后成立的断言；{deftech (key := "precondition")}_前置条件_则是为了保证后置条件成立而必须在程序运行前成立的断言。

{tactic}`vcgen` 使用的谓词变换器语义将后置条件变换为程序能够保证该后置条件成立时的{deftech (key := "weakest preconditions")}_最弱前置条件_。
若在所有状态下 $`P'` 都足以证明 $`P`，但 $`P` 不足以证明 $`P'`，则断言 $`P` 弱于 $`P'`。
逻辑等价的断言视为相等。

这里的谓词可以带状态：它们可以提及程序的当前状态。
此外，后置条件还可以把程序的返回值及其抛出的任何异常与最终状态关联起来。
每个可用于 {tactic}`vcgen` 的程序类型都由 {name}`WP` 实例指定断言类型和异常后置条件类型。
对于 {lean}`StateM Nat` 这样的状态单子，断言是状态上的谓词，类型为 {lean}`Nat → Prop`。
后置条件还将返回值作为首个参数，异常后置条件则为程序可能抛出的每种异常提供一个断言。


## 断言格
%%%
file := "Assertion-Lattices"
tag := "vcgen-assertion-lattices"
%%%

程序的谓词变换器语义基于一种命题可以提及程序状态的逻辑。
这里的“状态”不仅指可变状态，也包括通过 {name}`ReaderT` 等方式提供的只读值。
不同程序类型具有不同的断言类型，它可以是任意完备格。
更具体地说，断言类型需实例化 {name}`Assertion`；它是建立在 {name}`CompleteLattice` 上、可被 {tactic}`vcgen` 识别的 {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev`。

{zhdocstringFrom Assertion}

::::leanSection
```lean -show
variable {α : Type u} {P : α → Prop}
```
:::paragraph
格结构提供断言的逻辑词汇：

* 序关系 {name Lean.Order.PartialOrder.rel}`⊑` 表示蕴涵。
* 交 {name Lean.Order.meet}`⊓` 表示合取，并 {name Lean.Order.join}`⊔` 表示析取。
* 顶元 {name Lean.Order.top}`⊤` 是平凡断言，底元 {name Lean.Order.bot}`⊥` 是矛盾断言。
* 带索引的上确界 {name Lean.Order.iSup}`⨆` 表示存在量化，带索引的下确界 {name Lean.Order.iInf}`⨅` 表示全称量化。
  其记法类似普通量词；例如 {lean}`⨆ x : α, P x` 断言存在满足 {lean}`P` 的元素。
* Heyting 蕴涵 {name Lean.Order.himp}`⇨` 是断言语言内部的蕴涵。
:::
::::

:::leanSection
```lean -show
universe u
variable {Pred : Type u} [Assertion Pred] {P Q : Pred}
```
蕴涵关系与内部蕴涵的区别在于：前者是 Lean 逻辑中的陈述，后者属于断言语言；对断言 {lean}`P` 和 {lean}`Q`，{lean}`P ⊑ Q` 是 {lean}`Prop`，而 {lean}`P ⇨ Q` 仍是一个断言。
:::

{module}`Std.WP` 为 {lean}`Prop`、{lean}`Unit`、函数类型和有序对提供 {name}`Assertion` 实例。
{lean}`Prop` 上的格运算与普通逻辑联结词一致，其序关系就是逻辑蕴涵。
{lean}`Nat → Prop` 等函数类型上的格运算逐点进行，因此状态谓词间的蕴涵是全称量化的蕴涵。
{lean}`(Nat → Prop) × (Bool → Prop)` 等有序对上的格运算逐分量进行，因此成对谓词间的蕴涵是各分量谓词间蕴涵的合取。

:::example "不同断言类型上的蕴涵" (file := "Entailment-at-Different-Assertion-Types")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order
```
在 {lean}`Prop` 上，蕴涵关系就是逻辑蕴涵：
```lean
example (P Q : Prop) : (P ⊑ Q) = (P → Q) := rfl
```
在状态谓词类型上，蕴涵关系就是每个状态上的逻辑蕴涵：
```lean
example (f g : Nat → Prop) :
    (f ⊑ g) = ∀ n, f n → g n := rfl
```
有序对间的蕴涵关系是各分量蕴涵关系的合取：
```lean
example (f₁ f₂ : Nat → Prop) (g₁ g₂ : Bool → Prop) :
    ((f₁, g₁) ⊑ (f₂, g₂)) = ((f₁ ⊑ f₂) ∧ (g₁ ⊑ g₂)) := rfl
```
通过展开蕴涵序关系并对各个状态推理，可以证明状态谓词间的具体蕴涵：
```lean
def Positive : Nat → Prop := fun n => 0 < n
def AtLeastTwo : Nat → Prop := fun n => 2 ≤ n

example : AtLeastTwo ⊑ Positive := by
  simp [PartialOrder.rel, AtLeastTwo, Positive]
  intro x h
  grind
```
:::

::::leanSection
```lean -show
universe u
variable {P : Prop} {Pred : Type u} [Assertion Pred]
```
不涉及状态的普通命题可以使用{deftech (key := "corner brackets")}[角括号]嵌入任意断言格。
写作 {lean (type := "Pred")}`⌜P⌝`，这是 {name}`Lean.Order.CompleteLattice.ofProp` 的记法。
:::syntax term (title := "嵌入命题") (namespace := Lean.Order)
```grammar
⌜$_:term⌝
```
{zhincludeDocstringFrom Lean.Order.CompleteLattice.ofProp}
:::
::::

{zhdocstringFrom Lean.Order.CompleteLattice.ofProp}

:::leanSection
```lean -show
universe u
variable {p : Prop} {n k : Nat} {Pred : Type u} [Assertion Pred]
```
形如 {lean (type := "Pred")}`⌜p⌝` 的断言是{deftech (key := "pure assertion")}_纯断言_：其真假不依赖状态。
在断言类型 {lean}`Prop` 上，{lean (type := "Prop")}`⌜p⌝` 就是命题 {lean}`p` 本身；在 {lean}`Nat → Prop` 等状态谓词类型上，它是常值谓词 {lean (type := "Nat → Prop")}`fun _ => p`。
因此，具体单子的规约可以直接陈述命题，例如 {lean (type := "Nat → Prop")}`fun s => s = n`。
断言类型抽象时必须使用角括号，例如对单子及其断言类型 {lean}`Pred` 量化的规约。
此时 {lean}`n = k` 这样的命题不是断言，但 {lean (type := "Pred")}`⌜n = k⌝` 将它嵌入 {lean}`Pred`。
本章末尾的{ref "vcgen-monad-polymorphic" (domain := Manual.examples)}[单子多态示例]正是因此而使用角括号。
{tactic}`vcgen` 将纯前置条件移入普通 Lean 上下文，使其成为验证条件的假设。
:::

:::example "状态单子的断言" (file := "Assertions-for-State-Monads")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```
谓词 {name}`ItIsSecret` 表示一个 {name}`String` 类型的状态等于 {lean}`"secret"`：
```lean
def ItIsSecret : String → Prop := fun s => s = "secret"
```
此类断言间的蕴涵是逐点的逻辑蕴涵：
```lean
example : ItIsSecret ⊑ (⌜True⌝ : String → Prop) := by
  simp [ItIsSecret, PartialOrder.rel]
```
:::

## 异常后置条件
%%%
file := "Exception-Postconditions"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--Exception-Postconditions"
%%%

正常终止的后置条件是从返回值到断言的函数。
可能抛出异常的程序还需要{deftech (key := "exception postcondition")}_异常后置条件_，断言程序抛出异常时成立的性质。
给定单子的异常后置条件类型由其 {name}`WP` 实例决定。

例如，{lean}`ExceptT String (StateM Nat) Bool` 的 {name}`WP` 实例指定断言类型为 {lean}`Nat → Prop`，从而后置条件类型为 {lean}`Bool → Nat → Prop`，异常后置条件类型为 {lean}`String → Nat → Prop`。
没有异常的单子具有异常后置条件类型 {name}`Unit`。
:::leanSection
```lean -show
universe u
variable {Pred EPred ε : Type u} [Assertion Pred] [Assertion EPred]
```
对于断言类型为 {lean}`Pred`、异常后置条件类型为 {lean}`EPred` 的底层单子，{lean}`ExceptT ε` 这样的异常层会增加一个异常后置条件，得到类型 {lean}`(ε → Pred) × EPred`。
:::
由于单元类型与有序对类型都具有 {name}`Assertion` 实例，这些异常后置条件“栈”自动也是断言。
单子变换器的 {name}`WP` 实例确保单子变换器栈具有相应的异常后置条件栈。

:::syntax term (title := "异常后置条件栈") (namespace := Std.WP)
记法 `EStack⟨e₁, e₂, ...⟩` 是异常后置条件栈类型 `e₁ × (e₂ × (... × Unit))` 的简写，记法 `estack⟨v₁, v₂, ...⟩` 则构造该栈类型的值 `(v₁, v₂, ..., ())`。
```grammar
EStack⟨$_,*⟩
```
```grammar
estack⟨$_,*⟩
```
:::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {P : Pred} {α : Type u} {prog : m α} {Q' : α → Pred}
```
可能抛出异常的程序有两种规约解释。{deftech (key := "total correctness interpretation")}_全正确性解释_ {lean}`⦃P⦄ prog ⦃Q'⦄` 断言：若 {lean}`P` 成立，则 {lean}`prog` 正常终止，_且_结果满足 {lean}`Q'`。{deftech (key := "partial correctness interpretation")}_部分正确性解释_ {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` 断言：若 {lean}`P` 成立，_且_ {lean}`prog` 正常终止，_则_结果满足 {lean}`Q'`。
不显式提供异常后置条件的三元组使用底元断言 {lean}`(⊥ : EPred)`，因此采用全正确性解释；在 {lean (type := "EPred")}`⊥` 与 {lean (type := "EPred")}`⊤` 之间，异常后置条件表达一系列不同的正确性性质。
:::

## 谓词变换器
%%%
file := "Predicate-Transformers"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--_______________"
%%%

```lean -show
universe u v w
variable {Pred : Type u} {EPred : Type v} {α : Type w} [Assertion Pred] [Assertion EPred]
```

谓词变换器是从后置条件到描述前置条件的断言的函数。

{zhdocstringFrom Lean.Order.PredTrans}

:::leanSection
```lean -show
variable {x y : PredTrans Pred EPred α} {post post' : α → Pred} {epost epost' : EPred}
```
谓词变换器上的偏序逐点继承自断言格：若对所有 {lean}`post` 和 {lean}`epost` 都有 {lean}`x.apply post epost ⊑ y.apply post epost`，则 {lean}`x ⊑ y`。
{name}`WP` 实例产生的每个谓词变换器都是{deftech (key := "monotone")}_单调的_：若 {lean}`post ⊑ post'` 且 {lean}`epost ⊑ epost'`，则 {lean}`x.apply post epost ⊑ x.apply post' epost'`。

{zhdocstringFrom Lean.Order.PredTrans.Monotone}
:::

谓词变换器构成一个单子。
{name}`pure` 运算是恒等变换器，仅用其参数实例化后置条件。
{name}`bind` 运算符组合谓词变换器。

{zhdocstringFrom PredTrans.pure}

{zhdocstringFrom PredTrans.bind}

辅助运算 {name}`PredTrans.pushArg`、{name}`PredTrans.pushExceptT` 和 {name}`PredTrans.pushOptionT` 通过添加标准副作用来修改谓词变换器。
它们用于实现 {name}`StateT`、{name}`ExceptT` 和 {name}`OptionT` 等变换器的 {name}`WP` 实例；也可用来实现可按这些变换器之一理解的单子。
例如，{name}`PredTrans.pushArg` 通常用于状态单子，但也可以用它实现读取器单子的实例，将读取器的值视为只读状态。

{zhdocstringFrom PredTrans.pushArg}

{zhdocstringFrom PredTrans.pushExceptT}

{zhdocstringFrom PredTrans.pushOptionT}

### 最弱前置条件
%%%
file := "Weakest-Preconditions"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--_______________--__________________"
%%%

```lean -show
variable {Prog : Type u} {Value : Type v} [WP Prog Value Pred EPred] {prog : Prog} {post : Value → Pred} {epost : EPred}
```

程序类型的{tech (key := "weakest precondition")}[最弱前置条件]语义由 {name}`WP` 类型类提供。
实例 {lean}`WP Prog Value Pred EPred` 将类型为 {lean}`Prog`、结果类型为 {lean}`Value` 的程序解释为断言类型 {lean}`Pred` 与异常后置条件类型 {lean}`EPred` 上的单调谓词变换器。
类型 {lean}`Prog` 决定作为 {name}`outParam` 的 {lean}`Value`、{lean}`Pred` 和 {lean}`EPred`。
函数 {name}`wp` 应用该解释：{lean}`wp prog post epost` 是程序 {lean}`prog` 保证后置条件 {lean}`post` 与异常后置条件 {lean}`epost` 成立的最弱前置条件。

{zhdocstringFrom WP}

{zhdocstringFrom WP.wp}

若程序 {lean}`prog` 将两个后置条件之交的最弱前置条件分配为各后置条件最弱前置条件的交，就称其{deftech (key := "conjunctive")}_保持合取_。
类型类 {name}`WPConjunctive` 描述此性质，使 {lean}`prog` 的两个规约能够合并为一个最强规约。
这类似于合并{tech (key := "Hoare triples")}[霍尔三元组]的 {name}`Triple.and`。

{zhdocstringFrom WPConjunctive}

### 保持最弱前置条件的单子
%%%
file := "Monads-That-Preserve-Weakest-Preconditions"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--_______________--Monads-That-Preserve-Weakest-Preconditions"
%%%

{tactic}`vcgen` 的多数内置规约引理依赖 {name}`WPMonad` 实例。
{name}`WP` 实例针对某个具体类型提供，但单子是多态类型。
{lean}`StateM Nat Unit` 与 {lean}`StateM Nat String` 是不同类型，但它们的最弱前置条件应当相关。
{name}`WPMonad` 实例为单子可应用的每个类型所得到的类型赋予 {name}`WP` 解释。
它还携带证据，说明此解释对单子的 {name Pure.pure}`pure` 与 {name Bind.bind}`bind` 实现是可靠的。
因此，要证明关于 {keywordOf Lean.Parser.Term.do}`do` 块的性质，只需证明关于该块的{tech (key := "do elements")}[元素]链的性质。
换言之，{name}`WPMonad` 实例允许对 {keywordOf Lean.Parser.Term.do}`do` 块进行组合式推理。

{zhdocstringFrom WPMonad}

:::example "缺少 `WPMonad` 实例"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

单字段结构 {name}`Identity` 的行为类似恒等单子 {name}`Id`。它有 {name}`WP` 实例，但没有 {name}`WPMonad` 实例：
```lean
structure Identity (α : Type u) where
  run : α

variable {α : Type u}

instance : Monad Identity where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : WP (Identity α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => post x.run⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x.run

theorem Identity.of_run_eq_wp {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop)
    (hwp : wp prog P ()) : P x := by
  simp_all [wp, WP.trans, ← h]
```

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

缺少该实例时，{tactic}`vcgen` 无法使用 {name}`pure` 与 {name}`bind` 的规约。
例如，下列函数在 {name}`Identity` 中用 {keywordOf Lean.Parser.Term.doFor}`for` 循环反转列表：
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
定理 {name}`rev_correct` 陈述 {name}`rev` 与 {name}`List.reverse` 一致。
没有 {name}`WPMonad` 实例时，{tactic}`vcgen` 无法将 {name}`rev` 分解为 {name}`Id` 中的步骤序列，并报告没有规约适用于该程序：
```lean +error -keep (name := noInst)
theorem rev_correct {xs : List α} :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp h
  vcgen [rev]
```
```leanOutput noInst
No spec applicable to program (forIn xs [] fun x __s => pure (ForInStep.yield (x :: __s))) >>=
  pure in monad Identity. Candidates were [SpecProof.global Std.WP.Spec.bind].
```
若没有规约适用于 {name}`bind`，问题通常在于缺少 {name}`WPMonad` 实例。
添加合适的实例即可解决此问题：
```lean
instance : WPMonad Identity Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl
```
有了该实例和合适的不变式，{tactic}`vcgen` 及 {tactic}`grind` 模式的{ref "grind-interactive"}[策略] {grindTactic}`finish` 就能证明该定理。
```lean
theorem rev_correct {xs : List α} :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp h
  simp only [rev]
  vcgen invariants
  · fun pref suff out => out = pref.reverse
  with finish
```
:::

### 可靠性引理
%%%
file := "Soundness-Lemmas"
tag := "vcgen-soundness"
%%%

可从纯代码调用的单子通常提供调用运算，接收所需的输入状态，并返回与输出状态配对的值，或某种异常值。
例如 {name}`StateT.run`、{name}`ExceptT.run` 和 {name}`Id.run`。
{deftech (key := "Soundness lemmas")}_可靠性引理_在关于单子程序调用的陈述与其 {name}`WP` 实例给出的{tech (key := "weakest precondition")}[最弱前置条件]语义之间建立联系。
它们表明：若调用的最弱前置条件为真，则关于该调用的性质为真。

{zhdocstringFrom Id.of_run_eq_wp}

{zhdocstringFrom StateM.of_run_eq_wp}

{zhdocstringFrom StateM.of_run'_eq_wp}

{zhdocstringFrom ReaderM.of_run_eq_wp}

{zhdocstringFrom Except.of_eq_wp}

{zhdocstringFrom Option.of_eq_wp}

{zhdocstringFrom EStateM.of_run_eq_wp}

## 霍尔三元组
%%%
file := "Hoare-Triples"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--_______________-0"
%%%

{deftech (key := "Hoare triple")}_霍尔三元组_{citep hoare69}[] 由前置条件、程序和后置条件组成。
若在满足前置条件的状态中运行程序，所得状态将满足后置条件。

{zhdocstringFrom Triple}

::::syntax term (title := "霍尔三元组记法")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
```grammar
⦃ $_ ⦄ $_ ⦃ $_; $_ ⦄
```
:::leanSection
```lean -show
universe z
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPred}
```
{lean}`⦃ P ⦄ x ⦃ Q; E ⦄` 是 {lean}`Triple x P Q E` 的语法糖。
省略异常后置条件（如 {lean}`⦃ P ⦄ x ⦃ Q ⦄`）时，默认为底元断言 {lean (type := "EPred")}`⊥`，断言该程序不会抛出异常。
:::
::::

{zhdocstringFrom Triple.and}

{zhdocstringFrom Triple.mp}

## 规约引理
%%%
file := "Specification-Lemmas"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--____________"
%%%

{deftech (key := "Specification lemmas")}_规约引理_是将霍尔三元组关联到程序构造的指定定理，例如 {name Bind.bind}`bind`、{name Pure.pure}`pure`、循环或库函数应用。
同一程序构造可以有多个适用于不同情形的规约引理；按优先级依次尝试，直到其中一个可以实例化。
:::leanSection
```lean -show
variable {prog : Prog} {P : Pred} {Q : Value → Pred} {E : EPred}
variable {A : Sort u} {B : A → Sort v} {f : (a : A) → B a}
```
如{ref "vcgen-verification-conditions"}[验证条件]一节所述，{tactic}`vcgen` 通过应用程序部分与 {lean}`prog` 匹配的规约引理，分解目标 {lean}`P ⊑ wp prog Q E`。
若没有规约引理适用于 {lean}`prog`，{tactic}`vcgen` 会报告错误，列出 {lean}`prog` 和候选引理。
规约引理使程序推理具有_模块性_：函数 {lean}`f` 的规约引理只需证明一次，{tactic}`vcgen` 在每次调用 {lean}`f` 时应用它，无需展开 {lean}`f` 的定义。
在这方面，{name Pure.pure}`pure` 和 {name Bind.bind}`bind` 都是普通函数：规约引理 {name}`Spec.pure` 与 {name}`Spec.bind` 在具有 {name}`WPMonad` 实例的任意单子中都成立。
:::

将 {attr}`spec` 属性应用于陈述为霍尔三元组的定理时，会把该定理注册为规约引理。
这些引理按优先级顺序使用。

{attr}`spec` 属性也可以应用于定义。
用于定义时，它表示应在生成验证条件期间展开该定义。

:::syntax attr (title := "`spec` 规约属性")
```grammar
spec $[$_:prio]?
```
{zhincludeDocstringFrom Lean.Parser.Attr.spec}
:::

{deftech (key := "logical variable")}_逻辑变量_是规约引理中不出现在程序里的全称量化变量。
逻辑变量用于关联初始状态、最终状态和返回值。

{deftech (key := "auto-framing specification")}_自动框架规约_是一种规约引理：其后置条件为全称量化变量，前置条件则用该变量陈述。
{tactic}`vcgen` 应用自动框架规约时，合一会将后置条件实例化为后续程序所需的断言，因此无需再证明该后置条件蕴含后续前置条件。
后置条件中涉及程序未改变的状态部分的所有事实，都无需额外证明即可保留。
例如，规约引理 {name}`Spec.bind` 是自动框架规约：其前置条件是以第二个动作的最弱前置条件为后置条件，计算第一个动作的最弱前置条件。

```signature
Std.WP.Spec.bind.{u, v, w, w'}
  {m : Type u → Type v} [Monad m]
  {Pred : Type w} {EPred : Type w'}
  [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]
  {α β : Type u} {post : β → Pred} {epost : EPred}
  (x : m α) (f : α → m β) :
  ⦃ wp x
      (fun a =>
        binderNameHint a f
          (wp (f a) post
            epost))
      epost ⦄
  x >>= f
  ⦃ post; epost ⦄
```

:::example "逻辑变量" (file := "Logical-Variables")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

函数 {name}`double` 将 {name}`Nat` 状态的值翻倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
它的规约应当_关联_初始状态和最终状态，但无法预知它们的确切值。
该规约用逻辑变量表示初始状态：
```lean
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```

前置条件中的断言是函数，因为 {lean}`StateM Nat` 的断言类型为 {lean}`Nat → Prop`。

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat Unit) Unit (Nat → Prop) EStack⟨⟩
```

## 不变式规约
%%%
file := "Invariant-Specifications"
tag := "Lean-__________________--The--vcgen--tactic--_____________________--_______________-1"
%%%

{name}`ForIn.forIn` 与 {name}`ForIn'.forIn'` 的{tech (key := "specification lemmas")}[规约引理]接受 {name}`Invariant` 类型的参数，{tactic}`vcgen` 会确保其他自动化机制不会意外生成不变式。

{zhdocstringFrom Invariant}

不变式使用列表来建模 {keywordOf Lean.Parser.Term.doFor}`for` 循环中的值序列。
不变式是关于循环已消费元素的前缀、剩余元素的后缀、当前累加器状态，以及单子断言语言中其他状态参数的函数。

{zhdocstringFrom Invariant.withEarlyReturnNewDo}

# 验证条件
%%%
file := "Verification-Conditions"
tag := "vcgen-verification-conditions"
%%%

{tactic}`vcgen` 将以最弱前置条件表达的目标转换为一组不变式和验证条件；它们共同足以证明原目标。
特别地，{tech (key := "Hoare triples")}[霍尔三元组]通过最弱前置条件定义，因此可以用 {tactic}`vcgen` 证明。

:::leanSection
```lean -show
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α β : Type u} {e e' : m α} {P P' R : Pred} {Q Q' : α → Pred} {E E' : EPred} {φ : Prop} {x : m β} {f : β → m α} {a : β} {γ : Sort w} {e₁ e₂ : γ}
```
{TODO}[此模型尚未涵盖框架，即 `frames` 子句和 frameproc。]
目标的验证条件使用与 {tactic}`grind` 相同的机制生成。
生成过程如下：
1. 将目标变为断言间的蕴涵 {lean}`P ⊑ R`。
   引入绑定，将{tech (key := "Hoare triples")}[霍尔三元组]展开为 {lean}`P ⊑ wp e Q E`，并将 {lean}`wp e Q E` 形式的目标变为 {lean}`⊤ ⊑ wp e Q E`。
2. 将前置条件 {lean}`P` 移入局部上下文：纯断言 {lean (type := "Pred")}`⌜φ⌝` 变为假设 {lean}`φ`，{ref "vcgen-assertion-lattices"}[存在量化] {name Lean.Order.iSup}`⨆` 变为变量，状态谓词的参数也变为变量。
3. 按联结词递归地将断言 {lean}`R` 分解为目标：交 {name Lean.Order.meet}`⊓` 为每个合取项产生一个目标；{name Lean.Order.himp}`⇨` 的前件移入前置条件；纯断言 {lean (type := "Pred")}`⌜φ⌝` 转换为命题 {lean}`φ`；{name Lean.Order.top}`⊤` 目标立即关闭。
4. 若 {lean}`R` 为 {lean}`wp e Q E`，则分解程序 {lean}`e`：
   1. 引入 {keywordOf Lean.Parser.Term.«let»}`let` 绑定，使其成为假设。
   2. 若{tech (key := "auxiliary matching function")}[辅助匹配函数]应用的{tech (key := "match discriminant")}[判别式]是构造器应用，则将其归约；其他条件式或匹配则按每个分支拆成目标。
   3. 对函数应用，按优先级使用首个适用的规约引理。
      霍尔三元组形式的假设也视为规约引理。
      Lean 为 {name Bind.bind}`bind`、{name Pure.pure}`pure`、{name}`ForIn.forIn` 及 {keywordOf Lean.Parser.Term.do}`do` 记法去糖化后产生的其他函数提供规约引理。
      若没有规约引理适用，则 {tactic}`vcgen` 报错。

      使用 {name Lean.Order.PartialOrder.rel}`⊑` 的传递性应用规约引理 {lean}`P' ⊑ wp e' Q' E'`：目标 {lean}`P ⊑ wp e Q E` 可由 {lean}`P ⊑ P'` 和 {lean}`wp e' Q' E' ⊑ wp e Q E` 得到。
      当 {lean}`e'` 与 {lean}`e` 合一、{lean}`Q' ⊑ Q` 且 {lean}`E' ⊑ E` 时，第二个蕴涵成立。
      实际上，{tactic}`vcgen` 用引理的前置条件替换目标中的最弱前置条件，得到新目标 {lean}`P ⊑ P'`。
   5. 通过合一实例化引理中出现在程序内的变量。
      {tech (key := "auto-framing specification")}[自动框架规约]的全称量化后置条件成为 {lean}`Q`，因此 {lean}`Q' ⊑ Q` 由自反性成立，不再留下后置条件目标。
      否则，蕴涵 {lean}`Q' ⊑ Q` 和 {lean}`E' ⊑ E` 成为新目标。
      类型通过 {attr}`spec_invariant_type` 注册的假设成为不变式目标。
      引理的{tech (key := "logical variables")}[逻辑变量]以元变量形式出现在所有这些新目标中。
5. 对每个新目标重新从步骤 1 开始处理。
   例如，规约引理 {name}`Spec.bind` 是自动框架规约，前置条件为 {lean}`wp x (fun a => wp (f a) Q E) E`。
   对目标 {lean}`P ⊑ wp (x >>= f) Q E`，新目标为 {lean}`P ⊑ wp x (fun a => wp (f a) Q E) E`。
   对此目标应用 {lean}`x` 的规约引理时，后置条件间蕴涵的右侧为 {lean}`wp (f a) Q E`，因此以相同方式分解程序剩余部分。
   处理新目标前，其假设会{tech (key := "internalization")}[内部化]到 {tactic}`grind` 的“白板”中，假设相互矛盾的目标会被丢弃。
6. 无法再通过这些步骤分解的剩余目标就是验证条件。
   输出每个验证条件前，{tactic}`vcgen` 会解决其中为 {lean}`True` 的合取项，以及形如 {lean (type := "Prop")}`e₁ = e₂` 且 {lean}`e₁` 与 {lean}`e₂` 可通过合一变为定义相等的合取项。
   求解等式可能为元变量赋值，因此某些逻辑变量会被确定：合取项 `s = ?n` 会赋值 `?n := s`。
   未解决的合取项保留为验证条件。
7. 按生成顺序，将不变式子目标命名为 `inv1`、`inv2`、……，验证条件子目标命名为 `vc1`、`vc2`、……。

经过 {name Lean.Elab.Tactic.Do.VCGen.Config.stepLimit}`stepLimit` 个程序步骤后，验证条件生成会提前停止。
{keywordOf Lean.Parser.Tactic.vcgen}`until` 子句在首个匹配给定模式的程序处停止生成验证条件。
{keywordOf Lean.Parser.Tactic.vcgen}`with` 子句对每个剩余验证条件运行给定的 {tactic}`grind` 模式步骤。
{keywordOf Lean.Parser.Tactic.vcgen}`simplifying_assumptions` `[h₁, h₂]` 子句将 `h₁`、`h₂` 用作额外重写规则，重写绑定与分支引入的假设及每个最弱前置条件的状态参数。
这将中间目标保持在用户选择的规范形式中：例如，状态更新序列可以折叠为一次构造器应用，使目标大小不随更新次数增长。
简化后的假设也有助于 {tactic}`grind` 发现矛盾目标。
:::

# 为单子启用 {tactic}`vcgen`
%%%
file := "Enabling--vcgen--For-Monads"
tag := "Lean-__________________--The--vcgen--tactic--Enabling--vcgen--For-Monads"
%%%

若单子基于 Lean 标准库提供的{tech (key := "monad transformers")}[单子变换器]实现，例如 {name}`ExceptT` 和 {name}`StateT`，通常无需添加额外实例即可使用 {tactic}`vcgen`。
其他单子则需要 {name}`WP`、{name}`LawfulMonad` 和 {name}`WPMonad` 实例。

提供基本实例后，下一步是证明{ref "vcgen-soundness"}[可靠性引理]。
该引理应表明：运行单子计算并断言所需谓词时的最弱前置条件，确实足以证明该谓词。

除单子的定义外，典型的库还会提供一组原语运算符。
每个原语都应配备一个{tech (key := "Specification lemmas")}[规约引理]。
此外，将状态内部实现设为私有，并导出一组精心设计的断言运算符，可能也很有用。

库中原语运算的规约引理，应保留关于状态的所有未被刻意隐藏的事实。
虽然按运算如何将输入状态变成输出状态来思考更容易，但在后置条件为全称量化变量时，{tech (key := "verification condition")}[验证条件]生成更可靠，因为自动化可将其直接实例化为下一条语句的前置条件，而无需证明蕴涵。

:::example "自动框架规约" (file := "Auto-Framing-Specifications")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

函数 {name}`double` 将自然数状态翻倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
按时间顺序考虑，一个合理规约是输出状态值等于输入状态值的两倍。
使用表示初始状态的{tech (key := "logical variable")}[逻辑变量]来表达：
```lean -keep
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```
然而，等价的{tech (key := "auto-framing specification")}[自动框架规约]会在其他函数中使用 {name}`double` 时产生更小的验证条件：
```lean
@[spec]
theorem better_double_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => Q () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  vcgen with finish
```
```lean -show
variable {Q : Unit → Nat → Prop}
```
现在，前置条件只说明后置条件应当对初始状态的两倍成立。
{lean}`Q` 关于 {name}`double` 未改变的状态（例如单子变换器栈中的第二层状态）所陈述的任何性质，在调用后都仍成立。
调用 {name}`double` 时，{tactic}`vcgen` 将 {lean}`Q` 实例化为剩余程序所需的后置条件，因此不会留下后置条件间的蕴涵作为验证条件。

{name}`better_double_spec` 的前置条件恰好是 {name}`double` 的最弱前置条件，因此调用方依赖 {name}`double` 的完整行为。
自动框架规约也可以不规定所有细节。
例如，前置条件 {lean (type := "Nat → Prop")}`fun s => ∀ s', s ≤ s' → Q () s'` 只保证 {name}`double` 不会减小状态。
:::

:::example "日志单子"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

单子 {name}`LogM` 在计算期间维护一份只可追加的日志：
```lean
structure LogM (β : Type u) (α : Type v) : Type (max u v) where
  log : Array β
  value : α

instance : Monad (LogM β) where
  pure x := ⟨#[], x⟩
  bind x f :=
    let { log, value } := f x.value
    { log := x.log ++ log, value }
```
它还有一个 {name}`LawfulMonad` 实例。
```lean -show
instance : LawfulMonad (LogM β) where
  map_const := rfl
  id_map x := rfl
  seqLeft_eq x y := rfl
  seqRight_eq x y := rfl
  pure_seq g x := by
    simp [pure, Seq.seq, Functor.map]
  bind_pure_comp f x := by
    simp [pure, bind, Functor.map]
  bind_map f x := by
    simp [bind, Seq.seq, Functor.map]
  pure_bind x f := by
    simp [pure, bind]
  bind_assoc x f g := by
    simp [bind]
```

可以用 {name}`log` 写入日志，并用 {name}`LogM.run` 计算值及其相应日志。
```lean
def log (v : β) : LogM β Unit := { log := #[v], value := () }

def LogM.run (x : LogM β α) : α × Array β := (x.value, x.log)
```

{name}`WP` 实例没有从头编写，而是使用 {name}`PredTrans.pushArg`。
该运算符原本用于建模状态单子，但 {name}`LogM` 可以视为一个只能向状态追加内容的状态单子。
这种追加体现在实例主体中：初始状态会与操作产生的日志相拼接：
```lean
instance : WP (LogM β α) α (Array β → Prop) EStack⟨⟩ where
  wpTrans
    | { log, value } =>
      PredTrans.pushArg (fun s => pure (value, s ++ log))
  wp_trans_monotone x := fun _ _ _ _ _ hpost s =>
    hpost x.value (s ++ x.log)
```

{name}`WPMonad` 实例同样受益于这一状态单子的概念模型，证明十分简短：
```lean
instance : WPMonad (LogM β) (Array β → Prop) EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure x post epost := by
    simp [Lean.Order.le_pi_eq_forall, wp, WP.trans, pure]
  bind_le_wp_bind x f post epost := by
    simp [Lean.Order.le_pi_eq_forall, wp, WP.trans, bind]
```

可靠性引理有一个重要细节：最弱前置条件应用于空数组。
这是必要的，因为日志计算被建模为只可追加的状态，因此必须存在某个初始状态。
从语义上说，选择空数组才不会把并非来自程序的项放入日志；从技术上说，它还必须是与数组追加运算符可交换的值。
```lean
theorem LogM.of_run_eq_wp {α : Type u} {β : Type v}
    {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop)
    (hwp : wp prog (fun v l => P (v, l)) () #[]) : P x := by
  rw [← h]
  simp [wp, WP.trans] at hwp
  exact hwp
```

接下来，应为库中的每个运算符提供规约引理。
这里只有一个运算符：{name}`log`。
对于新的单子，这些证明往往必须突破{tech (key := "Hoare triple")}[霍尔三元组]和最弱前置条件的抽象边界；它们提供的规约随后可由库的客户端抽象地使用。
```lean
theorem log_spec {x : β} {s' : Array β} :
    ⦃ fun s => s = s' ⦄ log x ⦃ fun _ s => s = s'.push x ⦄ := by
  constructor
  simp [log, wp, WP.trans, Lean.Order.le_pi_eq_forall]
```

{name}`log` 的更好规约是一条{tech (key := "auto-framing specification")}[自动框架规约]：
```lean
@[spec]
theorem log_spec_better {x : β} {Q : Unit → Array β → Prop} :
    ⦃ fun s => Q () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  constructor
  simp [log, wp, WP.trans, Lean.Order.le_pi_eq_forall]
```

函数 {name}`logUntil` 会记录不超过某个界限的所有自然数，其所得日志的长度总是等于它的参数：
```lean
def logUntil (n : Nat) : LogM Nat Unit := do
  for i in 0...n do
    log i

theorem logUntil_length {n : Nat} : (logUntil n).run.2.size = n := by
  generalize h : (logUntil n).run = x
  unfold logUntil at h
  apply LogM.of_run_eq_wp h
  vcgen invariants
  · fun pref suff _ s => pref.length = s.size
  all_goals simp_all [Std.Internal.ForIn.toList_rco]
```
:::

# 解决验证条件
%%%
file := "Discharging-Verification-Conditions"
tag := "vcgen-discharging"
%%%

{tactic}`vcgen` 产生的验证条件都是普通 Lean 目标，因此可以用任何策略解决。
不过，由于 {tactic}`vcgen` 使用 {tactic}`grind` 的内部表示，使用{ref "grind-interactive"}[`grind` 策略]通常最快。
{keywordOf Lean.Parser.Tactic.vcgen}`with` 子句对每个剩余验证条件运行一个 {tactic}`grind` 模式步骤，通常是 {grindTactic}`finish`。
该步骤在 {tactic}`vcgen` 生成期间已{tech (key := "internalization")}[内部化]到 {tactic}`grind`“白板”的目标上下文中运行，因此无需为每个验证条件重新内部化上下文。
内部化单个验证条件的上下文所需时间与上下文大小呈线性关系，因此将所有验证条件共享的上下文前缀只内部化一次，比逐个内部化每份上下文更便宜。
若 {grindTactic}`finish` 只成功关闭部分目标，用 {grindTactic}`try` 包裹即可抑制错误。

处理具体单子时，验证条件直接描述结果值与状态。
单子多态定理则产生{ref "vcgen-assertion-lattices"}[抽象断言格]上的目标。
若这些目标可归约为纯断言间的蕴涵，{tactic}`grind` 就能解决，如下例所示。抽象格上的其他目标可能需要手动证明。

:::example "单子多态证明" (file := "Monad-Polymorphic-Proofs") (tag := "vcgen-monad-polymorphic")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```
函数 {name}`bump` 将状态增加指定的量，并返回所得值。
底层单子 {lean}`m` 及其断言类型保持抽象。
由于断言类型 {lean}`Pred` 是抽象的，以下规约使用{tech (key := "corner brackets")}[角括号]嵌入其命题。
```lean
variable {m : Type → Type v} [Monad m]
variable {Pred EPred : Type}
variable [Assertion Pred] [Assertion EPred]
variable [WPMonad m Pred EPred]

def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

{name}`bump` 的规约引理对抽象断言格量化，其验证条件是该格中的蕴涵。
{grindTactic}`finish` 步骤解决这些条件：
```lean
theorem bump_correct :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ fun r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  vcgen [bump] with finish
```
:::
