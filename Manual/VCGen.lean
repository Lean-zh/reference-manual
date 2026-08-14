/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option mvcgen.warning false

open Manual (comment)

open Std.Do

#doc (Manual) "`mvcgen` 策略" =>
%%%
tag := "mvcgen-tactic"
%%%

:::tutorials
 * {ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[使用 `mvcgen` 验证命令式程序]
:::

{tactic}`mvcgen` 策略实现了一个_单子验证条件生成器_：
它将涉及以 Lean 命令式 {keywordOf Lean.Parser.Term.do}`do` 记法编写的程序的目标，分解成若干更小的、足以证明原目标的{tech}_验证条件_（{deftech}[VC]）。
除介绍 {tactic}`mvcgen` 用法的参考资料外，本章还包含一篇可独立阅读的{ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[教程]。

要使用 {tactic}`mvcgen` 策略，必须导入 {module}`Std.Tactic.Do` 并打开命名空间 {namespace}`Std.Do`。


# 概览



{tactic}`mvcgen` 的工作流程如下：

1. 按照{tech}[谓词变换器语义]重新解释单子程序。
   {name}`WP` 实例决定如何解释该单子。
   每个程序都被解释为一个映射：它将任意{tech}[后置条件]映射为保证该后置条件成立的{tech}[最弱前置条件]。
   大多数用户看不到这一步，但希望让自己的单子支持 {tactic}`mvcgen` 的库作者需要理解它。
2. 由较小的程序组合成程序。
   {keywordOf Lean.Parser.Term.do}`do` 块中的每条语句都与一个谓词变换器相关联，并有通用规则借助顺序执行和控制流运算符来组合这些语句。
   带有前置条件和后置条件的语句称为{tech}_霍尔三元组_。
   在程序中，每条语句的后置条件应足以证明下一条语句的前置条件；循环则要求指定{deftech}_循环不变式_，即在循环开始时及每次迭代结束时都必须为真的命题。
   指定的{tech}_规约引理_将函数与描述其行为的霍尔三元组关联起来。
3. 将单子程序的最弱前置条件语义应用于所需证明的目标，便得到为证明该目标而必须成立的前置条件。
   任何缺失的步骤，例如循环不变式，或证明某条语句的前置条件蕴含其后置条件，都会成为新的子目标。
   这些缺失的步骤称为{deftech}_验证条件_。
   {tactic}`mvcgen` 策略执行这一变换，以验证条件替换原目标。
   在此变换过程中，{tactic}`mvcgen` 使用规约引理来解决关于各条语句的证明。
4. 给出循环不变式后，实践中许多验证条件都可以自动解决。
   无法自动解决的验证条件，可根据其是用程序断言逻辑还是普通命题表示，使用{ref "tactic-ref-spred"}[专用证明模式]或普通 Lean 策略来证明。


# 谓词变换器

{deftech}_谓词变换器语义_将程序解释为从谓词到谓词的函数，而不是从值到值的函数。
{deftech}_后置条件_是在程序运行后成立的断言；{deftech}_前置条件_则是为了保证后置条件成立而必须在程序运行前成立的断言。

{tactic}`mvcgen` 使用的谓词变换器语义将后置条件变换为程序能够保证该后置条件成立时的{deftech}_最弱前置条件_。
若在所有状态下 $`P'` 都足以证明 $`P`，但 $`P` 不足以证明 $`P'`，则断言 $`P` 弱于 $`P'`。
逻辑等价的断言视为相等。

这里的谓词是有状态的：它们可以提及程序的当前状态。
此外，后置条件还可以把程序的返回值及其抛出的任何异常与最终状态关联起来。
{name}`SPred` 是一种谓词类型，以单子状态为参数；该状态表示为组成状态的各字段类型所构成的列表。
{name}`SPred` 定义了通常的逻辑联结词和量词。
每个可与 {tactic}`mvcgen` 配合使用的单子，都由 {name}`WP` 实例为其指定状态类型；{name}`Assertion` 是该单子对应的断言类型，用于前置条件。
{name}`Assertion` 是 {name}`SPred` 的包装：{name}`SPred` 以状态类型列表为参数，而 {name}`Assertion` 以信息更丰富的类型为参数，并将其转换为供 {name}`SPred` 使用的状态类型列表。
{name}`PostCond` 将关于返回值的 {name}`Assertion` 与关于潜在异常的断言配对；可用的异常同样由该单子的 {name}`WP` 实例指定。


## 有状态谓词

单子程序的谓词变换器语义建立在一种允许命题提及程序状态的逻辑之上。
这里的“状态”不仅指可变状态，也包括通过 {name}`ReaderT` 等方式提供的只读值。
不同单子提供不同的状态类型，但每个具体状态始终都有类型。
给定一个状态类型列表，{name}`SPred` 就是这些状态上的谓词类型。

{name}`SPred` 本身并不与单子验证框架绑定。
相关的 {name}`Assertion` 根据单子 {name}`WP` 实例的 {name}`PostShape` 输出参数所表示的状态，为该单子计算合适的 {name}`SPred`。

{docstring Std.Do.SPred}

::::leanSection
```lean -show
variable {P : Prop} {σ : List (Type u)}
```
不提及状态的普通命题可通过添加一个平凡的全称量化而用作有状态谓词。
其语法写作 {lean (type := "SPred σ")}`⌜P⌝`，这是 {name}`SPred.pure` 的语法糖。
:::syntax term (title := "`SPred` 记法") (namespace := Std.Do)
```grammar
⌜$_:term⌝
```
{includeDocstring Std.Do.«term⌜_⌝»}
:::
::::

{docstring SPred.pure}

:::example "有状态谓词"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
谓词 {name}`ItIsSecret` 表示一个 {name}`String` 类型的状态等于 {lean}`"secret"`：
```lean
def ItIsSecret : SPred [String] := fun s => ⌜s = "secret"⌝
```
:::

### 蕴涵

有状态谓词之间以_蕴涵_关系联系。
有状态谓词的蕴涵定义为全称量化的蕴含：若 $`P` 和 $`Q` 是状态 $`\sigma` 上的谓词，则当 $`∀ s : \sigma, P(s) → Q(s)` 时，称 $`P` 蕴涵 $`Q`（写作 $`P \vdash_s Q`）。

{docstring Std.Do.SPred.entails}

{docstring Std.Do.SPred.bientails}

:::syntax term (title := "`SPred` 记法") (namespace := Std.Do)
```grammar
$_:term ⊢ₛ $_:term
```
{includeDocstring Std.Do.«term_⊢ₛ_»}

```grammar
⊢ₛ $_:term
```
{includeDocstring Std.Do.«term⊢ₛ_»}

```grammar
$_:term ⊣⊢ₛ $_:term
```

{includeDocstring Std.Do.«term_⊣⊢ₛ_»}
:::

:::leanSection
```lean -show
variable {σ : List (Type u)} {P Q : SPred σ}
```
有状态谓词逻辑包含蕴含联结词。
蕴涵关系与蕴含联结词的区别在于：蕴涵关系是 Lean 逻辑中的命题，而蕴含联结词位于有状态逻辑内部。
给定状态 {lean}`σ` 上的有状态谓词 {lean}`P` 和 {lean}`Q`，{lean (type := "Prop")}`P ⊢ₛ Q` 是 {lean}`Prop`，而 {lean (type := "SPred σ")}`spred(P → Q)` 是 {lean}`SPred σ`。
:::

### 记法

有状态谓词的语法与普通 Lean 项的语法有所重叠。
特别是，有状态谓词使用逻辑联结词和量词的通常语法。
在前置条件和后置条件等明显需要有状态谓词的上下文中，相关语法会自动启用；其他上下文必须使用 {keywordOf Std.Do.«termSpred(_)»}`spred` 显式启用该语法。
使用 {keywordOf Std.Do.«termTerm(_)»}`term` 运算符可恢复这些运算符的通常含义。

:::syntax term (title := "谓词项") (namespace := Std.Do)
{keywordOf Std.Do.«termSpred(_)»}`spred` 表示应将逻辑联结词和量词理解为有状态谓词中的对应构造，而 {keywordOf Std.Do.«termTerm(_)»}`term` 表示它们应取通常含义。
```grammar
spred($t)
```
```grammar
term($t)
```
:::

### 联结词与量词

:::syntax term (title := "谓词联结词") (namespace := Std.Do)
```grammar
spred($_ ∧ $_)
```
{name}`SPred.and` 的语法糖。

```grammar
spred($_ ∨ $_)
```
{name}`SPred.or` 的语法糖。

```grammar
spred(¬ $_)
```
{name}`SPred.not` 的语法糖。

```grammar
spred($_ → $_)
```
{name}`SPred.imp` 的语法糖。

```grammar
spred($_ ↔ $_)
```
{name}`SPred.iff` 的语法糖。
:::


{docstring SPred.and}

{docstring SPred.conjunction}

{docstring SPred.or}

{docstring SPred.not}

{docstring SPred.imp}

{docstring SPred.iff}

:::syntax term (title := "谓词量词") (namespace := Std.Do)
```grammar
spred(∀ $x:ident, $_)
```
```grammar
spred(∀ $x:ident : $ty,  $_)
```
```grammar
spred(∀ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∀ _, $_)
```
```grammar
spred(∀ _ : $ty,  $_)
```
```grammar
spred(∀ (_ $_* : $ty),  $_)
```
每种全称量化形式都是调用 {name}`SPred.forall` 的语法糖，所传函数以被量化变量为参数。

```grammar
spred(∃ $x:ident, $_)
```
```grammar
spred(∃ $x:ident : $ty,  $_)
```
```grammar
spred(∃ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∃ _, $_)
```
```grammar
spred(∃ _ : $ty,  $_)
```
```grammar
spred(∃ (_ $_* : $ty),  $_)
```
每种存在量化形式都是调用 {name}`SPred.exists` 的语法糖，所传函数以被量化变量为参数。
:::

{docstring SPred.forall}

{docstring SPred.exists}

### 有状态值

正如 {name}`SPred` 表示状态上的谓词，{name}`SVal` 表示由状态导出的值。

{docstring SVal}

{docstring SVal.getThe}

{docstring SVal.StateTuple}

{docstring SVal.curry}

{docstring SVal.uncurry}


## 断言

关于单子程序的断言语言以{deftech}_后置条件形状_为参数；该形状描述给定单子中计算的输入和输出。
前置条件可以提及单子状态的初始值；后置条件可以提及返回值和单子状态的最终值，并且还必须涵盖所有可能抛出的异常。
给定单子的后置条件形状决定该单子中的状态和异常。
{name}`PostShape.pure` 描述断言不能提及任何状态的单子，{name}`PostShape.arg` 描述一个状态值，{name}`PostShape.except` 描述一种可能的异常。
由于可以不断添加这些构造器，单子变换器的后置条件形状可以用其所变换的底层单子的后置条件形状来定义。
在幕后，后置条件形状会被转换为状态类型列表并丢弃异常，从而将 {name}`Assertion` 转换为适当的 {name}`SPred`。

{docstring PostShape}

{docstring PostShape.args}

{docstring Assertion}

{docstring PostCond}

:::syntax term (title := "后置条件")
```grammar
⇓ $_* => $_
```
这是嵌套积构造器序列的语法糖，并以 {lean}`()` 结尾；其中第一个元素是关于非异常返回值的断言，其余元素是关于后置条件中各异常情形的断言。
:::


{docstring ExceptConds}

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α  : Type u}  {prog : m α} {Q' : α → Assertion ps}
```
可能抛出异常的程序有两种后置条件。{deftech}_完全正确性解释_ {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 断言：若 {lean}`P` 成立，则 {lean}`prog` 会终止，且结果满足 {lean}`Q'`。{deftech}_部分正确性解释_ {lean}`⦃P⦄ prog ⦃⇓? r => Q' r⦄` 断言：若 {lean}`P` 成立，并且 {lean}`prog` 终止，则结果满足 {lean}`Q'`。
:::


:::syntax term (title := "无异常后置条件")
```grammar
⇓ $_* => $_
```
{includeDocstring PostCond.noThrow}
:::

{docstring PostCond.noThrow}

:::syntax term (title := "部分后置条件")
```grammar
⇓? $_* => $_
```
{includeDocstring PostCond.mayThrow}
:::

{docstring PostCond.mayThrow}

:::syntax term (title := "后置条件蕴涵")
```grammar
$_ ⊢ₚ $_
```
{name}`PostCond.entails` 的语法糖。
:::

{docstring PostCond.entails}


:::syntax term (title := "后置条件合取")
```grammar
$_ ∧ₚ $_
```
{name}`PostCond.and` 的语法糖。
:::

{docstring PostCond.and}

:::syntax term (title := "后置条件蕴含")
```grammar
$_ →ₚ $_
```
{name}`PostCond.imp` 的语法糖。
:::

{docstring PostCond.imp}


## 谓词变换器

谓词变换器是一个函数，它将某种后置条件状态上的后置条件映射为该状态上的断言。
该函数必须是{deftech}_合取的_，即必须对 {name}`PostCond.and` 满足分配律。

{docstring PredTrans}

{docstring PredTrans.Conjunctive}

{docstring PredTrans.Monotonic}

:::leanSection
```lean -show
variable {σ : List (Type u)} {ps : PostShape} {x y : PredTrans ps α} {Q : Assertion ps}
```
{inst}`LE PredTrans` 实例依据谓词变换器的逻辑强度定义；若应用一个变换器所得结果总是蕴涵应用另一个变换器所得结果，则前者强于后者。
换言之，若 {lean}`∀ Q, y Q ⊢ₛ x Q`，则 {lean}`x ≤ y`。
这意味着较强的谓词变换器被视为大于较弱的谓词变换器。
:::

谓词变换器构成一个单子。
{name}`pure` 运算符是恒等变换器；它只是用自己的参数实例化后置条件。
{name}`bind` 运算符组合谓词变换器。

{docstring PredTrans.pure}

{docstring PredTrans.bind}

辅助运算符 {name}`PredTrans.pushArg`、{name}`PredTrans.pushExcept` 和 {name}`PredTrans.pushOption` 通过添加一种标准副作用来修改谓词变换器。
它们用于实现 {name}`StateT`、{name}`ExceptT` 和 {name}`OptionT` 等变换器的 {name}`WP` 实例；也可用来实现可按这些变换器之一理解的单子。
例如，{name}`PredTrans.pushArg` 通常用于状态单子，但也可以用它实现读取器单子的实例，将读取器的值视为只读状态。

{docstring PredTrans.pushArg}

{docstring PredTrans.pushExcept}

{docstring PredTrans.pushOption}

### 最弱前置条件

单子的{tech}[最弱前置条件]语义由 {name}`WP` 类型类提供。
{name}`WP` 实例决定单子的后置条件形状，并提供逻辑规则，将单子操作解释为该后置条件形状上的谓词变换器。

{docstring WP}

:::syntax term (title := "最弱前置条件")
```grammar
wp⟦$_ $[: $_]?⟧
```
{includeDocstring Std.Do.«termWp⟦_:_⟧»}
:::

### 最弱前置条件单子态射

除了 {name}`WP` 实例外，{tactic}`mvcgen` 的大多数内置规约引理还依赖 {name}`WPMonad` 实例。
除了满足单子定律外，单子对 {name}`pure` 和 {name}`bind` 的实现之最弱前置条件，还应分别对应谓词变换器单子的 {name}`pure` 和 {name}`bind` 运算符。
缺少 {name}`WPMonad` 实例时，{tactic}`mvcgen` 通常会原样返回初始证明目标。

{docstring WPMonad}

:::example "缺少 `WPMonad` 实例"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

单字段结构 {name}`Identity` 的行为类似恒等单子 {name}`Id`。它有 {name}`WP` 实例，但没有 {name}`WPMonad` 实例：
```lean
structure Identity (α : Type u) where
  run : α

variable {α : Type u}

instance : Monad Identity where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : WP Identity .pure where
  wp x := PredTrans.pure x.run

theorem Identity.of_wp_run_eq {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := by
  simp_all [WP.wp, ← h]
```

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

缺少该实例会使 {tactic}`mvcgen` 无法使用 {name}`pure` 和 {name}`bind` 的规约。
其通常表现为生成一个与原目标相同的验证条件。
下面这个函数反转列表：
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
若其结果等于 {name}`List.reverse`，它就是正确的。
然而，{tactic}`mvcgen` 并没有让目标变得更容易证明：
```lean +error -keep (name := noInst)
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  mvcgen [rev]
```
```leanOutput noInst
unsolved goals
case vc1
α✝ : Type u_1
xs x : List α✝
h : (rev xs).run = x
out✝ : List α✝ := []
⊢ (wp⟦do
      let __s ← forIn xs out✝ fun x __s => pure (ForInStep.yield (x :: __s))
      pure __s⟧
    (PostCond.noThrow fun a => { down := a = xs.reverse })).down
```
如果验证条件就是原问题，甚至没有对 {name}`bind` 做任何简化，通常是因为缺少 {name}`WPMonad` 实例。
添加合适的实例即可解决此问题：
```lean
instance : WPMonad Identity .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl
```
有了该实例和合适的不变式，{tactic}`mvcgen` 与 {tactic}`grind` 就能证明该定理。
```lean
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  simp only [rev]
  mvcgen invariants
  · ⇓⟨xs, out⟩ =>
    ⌜out = xs.prefix.reverse⌝
  with grind
```
:::

### 充分性引理
%%%
tag := "mvcgen-adequacy"
%%%

可从纯代码调用的单子通常会提供一个调用运算符：它以任何必需的输入状态为参数，返回与输出状态配对的值，或某种异常值。
例如 {name}`StateT.run`、{name}`ExceptT.run` 和 {name}`Id.run`。
{deftech}_充分性引理_在关于单子程序调用的陈述与由其 {name}`WP` 实例给出的程序{tech}[最弱前置条件]语义之间架起桥梁。
它们表明：若调用的最弱前置条件为真，则关于该调用的性质为真。

{docstring Id.of_wp_run_eq}

{docstring StateM.of_wp_run_eq}

{docstring StateM.of_wp_run'_eq}

{docstring ReaderM.of_wp_run_eq}

{docstring Except.of_wp_eq}

{docstring EStateM.of_wp_run_eq}

## 霍尔三元组

{deftech}_霍尔三元组_{citep hoare69}[] 由前置条件、程序和后置条件组成。
若在满足前置条件的状态中运行程序，所得状态将满足后置条件。

{docstring Triple}

::::syntax term (title := "霍尔三元组")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
:::leanSection
```lean -show
variable [WP m ps] {x : m α} {P : Assertion ps} {Q : PostCond α ps}
```
{lean}`⦃P⦄ x ⦃Q⦄` 是 {lean}`Triple x P Q` 的语法糖。
:::
::::

{docstring Triple.and}

{docstring Triple.mp}

## 规约引理

{deftech}_规约引理_是将函数与霍尔三元组关联起来的指定定理。
当 {tactic}`mvcgen` 遇到函数时，它会检查是否注册了规约引理，并尝试用它们解决中间的{tech}[验证条件]。
若没有适用的规约引理，语句的前置条件与后置条件之间的联系就会成为验证条件。
规约引理使我们能对单子代码库进行组合式推理。

将 {attr}`spec` 属性应用于陈述为霍尔三元组的定理时，会把该定理注册为规约引理。
这些引理按优先级顺序使用。

{attr}`spec` 属性也可以应用于定义。
用于定义时，它表示应在生成验证条件期间展开该定义。

:::syntax attr (title := "规约引理")
```grammar
spec $[$_:prio]?
```
{includeDocstring Lean.Parser.Attr.spec}
:::

规约引理中的全称量化变量可用于关联输入状态、输出状态和返回值。
这些变量称为{deftech}_模式变量_。

:::example "模式变量"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

函数 {name}`double` 将 {name}`Nat` 状态的值翻倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
它的规约应当_关联_初始状态和最终状态，但无法预知它们的确切值。
该规约使用一个模式变量代表初始状态：
```lean
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```

前置条件中的断言之所以是函数，是因为 {lean}`StateM Nat` 的 {name}`PostShape` 为 {lean (type := "PostShape.{0}")}`.arg Nat .pure`，而 {lean}`Assertion (.arg Nat .pure)` 即 {lean}`SPred [Nat]`。

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat) (.arg Nat .pure : PostShape.{0})
example : Assertion (.arg Nat .pure) = SPred [Nat] := rfl
```

## 不变式规约

这些类型用于不变式。
{name}`ForIn.forIn` 和 {name}`ForIn'.forIn'` 的{tech}[规约引理]采用 {name}`Invariant` 类型的参数，而 {tactic}`mvcgen` 会确保其他自动化过程不会意外生成不变式。

{docstring Invariant}

{docstring Invariant.withEarlyReturn}

不变式使用列表来建模 {keywordOf Lean.Parser.Term.doFor}`for` 循环中的值序列。
循环中的当前位置用 {name}`List.Cursor` 跟踪；它将列表中的位置表示为该位置左侧元素与右侧元素的组合。
该类型并非传统的拉链结构；传统拉链为高效移动会反转前缀，而此类型用于规约和证明而非运行时代码，因此前缀保持原顺序。

{docstring List.Cursor}

{docstring List.Cursor.at}

{docstring List.Cursor.pos}

{docstring List.Cursor.current}

{docstring List.Cursor.tail}

{docstring List.Cursor.begin}

{docstring List.Cursor.end}


# 验证条件

{tactic}`mvcgen` 策略把以 {name}`SPred` 和最弱前置条件表示的目标转换为一组不变式和验证条件；它们共同足以证明原目标。
特别地，{tech}[霍尔三元组]以最弱前置条件定义，因此可以使用 {tactic}`mvcgen` 来证明。

:::leanSection
```lean -show
variable [Monad m] [WPMonad m ps] {e : m α} {P : Assertion ps} {Q : PostCond α ps}
```
目标的验证条件按如下方式生成：
1. 应用若干简化和重写。
2. 此时目标应形如 {lean}`P ⊢ₛ wp⟦e⟧ Q`（即从一组有状态假设到蕴含所需后置条件之最弱前置条件的蕴涵）。
3. 展开表达式 {lean}`e` 中的{tech}[可约]常量以及标记了 {attrs}`@[spec]` 的定义。
4. 若表达式是{tech}[辅助匹配函数]或条件式（{name}`ite` 或 {name}`dite`）的应用，则先对其化简。
   化简每个匹配器的{tech (key := "match discriminant")}[判别项]，并归约整个项，尝试消除该匹配器或条件式。
   若失败，则为每个分支生成一个新目标。
5. 若表达式是某个常量的应用，则按优先级顺序尝试适用的 {attrs}`@[spec]` 引理。
   Lean 为 {keywordOf Lean.Parser.Term.do}`do` 记法脱糖后产生的 {name Bind.bind}`bind`、{name Pure.pure}`pure` 和 {name}`ForIn.forIn` 等常量提供了规约引理。
   实例化引理有时会解决其前提，尤其是因与目标定义相等而确定的模式变量。
   但 {name}`Invariant` 类型的假设绝不会以这种方式实例化。
   若规约引理的前置条件或后置条件与目标不完全匹配，则创建新的元变量来证明所需的蕴涵。
   若尝试使用局部假设并分解后置条件中的合取之简单自动化无法立即解决它们，它们就会保留为验证条件。
6. 对该过程生成的每个剩余目标，若其形如 {lean}`P ⊢ₛ wp⟦e⟧ Q`，则递归生成验证条件；否则将其加入不变式或验证条件集合。
7. 为所得不变式和验证条件子目标在证明状态中赋予合适的名称。
8. 根据策略的配置参数，在每个验证条件上尝试 {tactic}`mvcgen_trivial` 和 {tactic}`mleave`。
:::

为库定义合适的{tech}[规约引理]可以改善验证条件生成。
良好的规约引理能减少生成的验证条件数量。
此外，确保项的{tech}[简化范式]适合模式匹配，并确保默认 simp 集包含足够的引理，可将所有可能的项归约到该范式，便能消除更多条件式和模式匹配。

# 为单子启用 `mvcgen`

如果单子基于 Lean 标准库提供的{tech}[单子变换器]实现，例如 {name}`ExceptT` 和 {name}`StateT`，那么它通常不需要额外的实例。
其他单子则需要 {name}`WP`、{name}`LawfulMonad` 和 {name}`WPMonad` 实例。
该策略旨在支持对可能中断、带状态的单线程控制进行建模的单子；换言之，即普通命令式编程中的各种效应。
更奇特的效应尚未得到研究。

提供基本实例后，下一步是证明一个{ref "mvcgen-adequacy"}[充分性引理]。
该引理应表明：运行单子计算并断言所需谓词时的最弱前置条件，确实足以证明该谓词。

除单子的定义外，典型的库还会提供一组原语运算符。
每个原语都应配备一个{tech}[规约引理]。
此外，将状态内部实现设为私有，并导出一组精心设计的断言运算符，可能也很有用。

库中原语运算符的规约引理最好给出这些运算符作为谓词变换器的精确规约。
尽管按运算符如何将输入状态变换为输出状态来思考往往更容易，但当后置条件完全自由时，{tech}[验证条件]生成会更加可靠。
这使自动化能够用下一条语句的确切前置条件来实例化后置条件，而无须证明一个蕴涵。
换言之，把前置条件规定为后置条件之函数的规约，在实践中优于仅仅关联前置条件与后置条件的规约。

:::example "模式后置条件"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

函数 {name}`double` 将自然数状态翻倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
按时间顺序思考，一个合理的规约是输出状态的值为输入状态值的两倍。
这使用一个代表初始状态的模式变量来表达：
```lean -keep
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```
然而，若将后置条件视为模式变量，可得到一个等价的规约；在其他函数中使用 {name}`double` 时，它会产生更小的验证条件：
```lean
@[spec]
theorem better_double_spec {Q : PostCond Unit (.arg Nat .pure)} :
    ⦃ fun s => Q.1 () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  mvcgen with grind
```
后置条件的第一个投影是其有状态断言。
现在，前置条件只说明后置条件应当对初始状态的两倍成立。
:::

:::example "日志单子"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

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
instance : WP (LogM β) (.arg (Array β) .pure) where
  wp
    | { log, value } =>
      PredTrans.pushArg (fun s => PredTrans.pure (value, s ++ log))
```

{name}`WPMonad` 实例同样受益于这一状态单子的概念模型，证明十分简短：
```lean
instance : WPMonad (LogM β) (.arg (Array β) .pure) where
  wp_pure x := by
    ext
    simp [wp, pure]

  wp_bind _ _ := by
    ext
    simp [wp, bind]
```

充分性引理有一个重要细节：最弱前置条件变换的结果被应用于空数组。
这是必要的，因为日志计算被建模为只可追加的状态，因此必须存在某个初始状态。
从语义上说，选择空数组才不会把并非来自程序的项放入日志；从技术上说，它还必须是与数组追加运算符可交换的值。
```lean
theorem LogM.of_wp_run_eq {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ v l => ⌜P (v, l)⌝) #[]) → P x := by
  rw [← h]
  intro h'
  simp [wp] at h'
  exact h'
```

接下来，应为库中的每个运算符提供规约引理。
这里只有一个运算符：{name}`log`。
对于新的单子，这些证明往往必须突破{tech}[霍尔三元组]和最弱前置条件的抽象边界；它们提供的规约随后可由库的客户端抽象地使用。
```lean
theorem log_spec {x : β} :
    ⦃ fun s => ⌜s = s'⌝ ⦄ log x ⦃ ⇓ () s => ⌜s = s'.push x⌝ ⦄ := by
  simp [log, Triple, wp]
```

{name}`log` 的更好规约使用模式后置条件：
```lean
variable {Q : PostCond Unit (.arg (Array β) .pure)}

@[spec]
theorem log_spec_better {x : β} :
    ⦃ fun s => Q.1 () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  simp [log, Triple, wp]
```

函数 {name}`logUntil` 会记录不超过某个界限的所有自然数，其所得日志的长度总是等于它的参数：
```lean
def logUntil (n : Nat) : LogM Nat Unit := do
  for i in 0...n do
    log i

theorem logUntil_length : (logUntil n).run.2.size = n := by
  generalize h : (logUntil n).run = x
  unfold logUntil at h
  apply LogM.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, _⟩ s => ⌜xs.pos = s.size⌝
  with
    simp_all [List.Cursor.pos] <;>
    grind [Std.PRange.Nat.size_rco, Std.Rco.length_toList]
```
:::

# 证明模式
%%%
tag := "mvcgen-proof-mode"
%%%

有状态目标可使用特殊的_证明模式_来证明；在该模式下，目标显示两个假设上下文：普通 Lean 上下文包含 Lean 变量，特殊的有状态上下文包含关于单子状态的假设。
在证明模式中，目标是 {name}`SPred` 而非 {lean}`Prop`，且整个目标等价于从所有假设之合取到结论的蕴涵关系（{name}`SPred.entails`）。

:::syntax Std.Tactic.Do.mgoalStx (title := "证明模式目标")
证明模式目标显示为一系列具名假设，每行一个，随后是 {keywordOf Std.Tactic.Do.mgoalStx}`⊢ₛ` 和一个目标。
```grammar
$[$_:ident : $t:term]*
⊢ₛ $_:term
```
:::

在证明模式中，特殊策略用于操作有状态上下文。
这些策略在策略参考的{ref "tactic-ref-spred"}[专门一节]中介绍。

处理具体单子时，{tactic}`mvcgen` 通常不会留下有状态证明目标——它们会被化简掉。
然而，关于任意单子的多态定理可能会留下有状态目标。

:::example "有状态证明"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
函数 {name}`bump` 将状态增加指定的量，并返回所得值。
```lean
variable [Monad m] [WPMonad m ps]
def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

下面刻意以较低层次的方式证明 {name}`bump` 的规约引理，以展示中间证明状态：
```lean
theorem bump_correct :
      ⦃ fun n => ⌜n = k⌝ ⦄
      bump (m := m) i
      ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro n_eq_k
  unfold bump
  unfold modifyThe
  mspec
  mspec
  mpure_intro
  constructor
  . trivial
  . simp_all
```

该引理也可以只用简化器证明：
```lean
theorem bump_correct' :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro _
  simp_all [bump]
```
:::
