/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
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

#doc (Manual) "The `vcgen` tactic" =>
%%%
tag := "vcgen-tactic"
%%%

:::tutorials
 * {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[Verifying Imperative Programs Using `vcgen`]
:::

The {tactic}`vcgen` tactic implements a _verification condition generator_:
It breaks down a goal involving a program, for example one written using Lean's imperative {keywordOf Lean.Parser.Term.do}`do` notation, into a number of smaller {tech}_verification conditions_ ({deftech}[VCs]) that are sufficient to prove the goal.
In addition to a reference that describes the use of {tactic}`vcgen`, this chapter includes a {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[tutorial] that can be read independently of the reference.

In order to use the {tactic}`vcgen` tactic, {module}`Std.WP` and {module}`Std.Tactic.Do` must be imported and the namespaces {namespace}`Std.WP` and {namespace}`Lean.Order` must be opened.
The dependency on {namespace}`Lean.Order` is a temporary measure: this namespace holds the {ref "partial-fixpoint-theory"}[order theory behind {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`], which is yet to move into {namespace}`Std`.


:::syntax tactic (title := "Verification Condition Generation")
```grammar
vcgen $cfg:optConfig $[[$x,*]]?
  $[until $_]?
  $[invariants $inv*]?
  $[simplifying_assumptions $[$_]? $[[$_,*]]?]?
  $[with $_]?
```

Generates {tech}[verification conditions] for the current goal.

The {keywordOf Lean.Parser.Tactic.vcgen}`until` clause stops verification condition generation at the first goal that matches the provided pattern.
The {keywordOf Lean.Parser.Tactic.vcgen}`invariants` clause allows {tech}[loop invariants] to be specified.
These invariants are used during verification condition generation and can inform the simplification and automation passes.
If the {keywordOf Lean.Parser.Tactic.vcgen}`simplifying_assumptions` clause is present, then hypotheses introduced during verfication condition generation are simplified in the same manner as the goals.
Because {tactic}`vcgen` shares much of its implementation with {tactic}`grind`, the {keywordOf Lean.Parser.Tactic.vcgen}`with` clause allows either an {ref "grind-interactive"}`interactive `grind` tactic` or an ordinary tactic to be applied in all generated verification conditions.
:::

# 概览

The workflow of {tactic}`vcgen` consists of the following:

1. Programs are re-interpreted according to a {tech}[predicate transformer semantics].
   An instance of {name}`WP` for the program type determines the interpretation.
   The program type can be a monadic computation, such as a {keywordOf Lean.Parser.Term.do}`do`-block in {lean}`StateM Nat`.
   Non-monadic types, such as the syntax trees of a small imperative langauge, are also supported.
   每个程序都被解释为一个映射：它将任意{tech (key := "postcondition")}[后置条件]映射为保证该后置条件成立的{tech (key := "weakest preconditions")}[最弱前置条件]。
   This step is invisible to most users, but library authors who want to enable their program types to work with {tactic}`vcgen` need to understand it.
2. 由较小的程序组合成程序。
   Each part of a program, such as a statement in a {keywordOf Lean.Parser.Term.do}`do`-block, is associated with a predicate transformer, and there are general-purpose rules for combining these parts with sequencing and control-flow operators.
   带有前置条件和后置条件的语句称为{tech (key := "Hoare triple")}_霍尔三元组_。
   在程序中，每条语句的后置条件应足以证明下一条语句的前置条件；循环则要求指定{deftech (key := "loop invariant")}_循环不变式_，即在循环开始时及每次迭代结束时都必须为真的命题。
   指定的{tech (key := "Specification lemmas")}_规约引理_将函数与描述其行为的霍尔三元组关联起来。
3. Applying the weakest-precondition semantics of a program to a desired proof goal results in the precondition that must hold in order to prove the goal.
   The remaining entailments between assertions, such as a proof that the postcondition of one statement implies the precondition of the next, contain no weakest preconditions and become new subgoals.
   These subgoals are called the {deftech}_verification conditions_.
   Loop invariants that the user supplies become separate subgoals.
   The {tactic}`vcgen` tactic performs this transformation, replacing the goal with its verification conditions.
   During this transformation, {tactic}`vcgen` uses specification lemmas to discharge proofs about individual statements.
4. 给出循环不变式后，实践中许多验证条件都可以自动解决。
   Those that cannot are ordinary Lean goals, provable with ordinary Lean tactics or with the {tactic}`grind`-mode step of the {keywordOf Lean.Parser.Tactic.vcgen}`with` clause.


# 谓词变换器概述

{deftech (key := "predicate transformer semantics")}_谓词变换器语义_将程序解释为从谓词到谓词的函数，而不是从值到值的函数。
{deftech (key := "postcondition")}_后置条件_是在程序运行后成立的断言；{deftech (key := "precondition")}_前置条件_则是为了保证后置条件成立而必须在程序运行前成立的断言。

The predicate transformer semantics used by {tactic}`vcgen` transforms postconditions into the {deftech}_weakest preconditions_ under which the program will ensure the postcondition.
若在所有状态下 $`P'` 都足以证明 $`P`，但 $`P` 不足以证明 $`P'`，则断言 $`P` 弱于 $`P'`。
逻辑等价的断言视为相等。

The predicates in question can be stateful: they can mention the program's current state.
此外，后置条件还可以把程序的返回值及其抛出的任何异常与最终状态关联起来。
Each program type that can be used with {tactic}`vcgen` is assigned an assertion type and an exception postcondition type by an instance of {name}`WP`.
For a state monad such as {lean}`StateM Nat`, an assertion is a predicate on the state, of type {lean}`Nat → Prop`.
A postcondition additionally takes the return value as its first argument, and the exception postcondition includes an assertion for each exception that the program can throw.


## Assertion Lattices
%%%
tag := "vcgen-assertion-lattices"
%%%

The predicate transformer semantics of programs is based on a logic in which propositions may mention the program's state.
这里的“状态”不仅指可变状态，也包括通过 {name}`ReaderT` 等方式提供的只读值。
Different program types have different assertion types, which can be any complete lattice.
More specifically, assertion types instantiate {name}`Assertion`, which is a {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` over {name}`CompleteLattice` that is recognized by {tactic}`vcgen`.

{docstring Assertion}

::::leanSection
```lean -show
variable {α : Type u} {P : α → Prop}
```
:::paragraph
The lattice structure provides the logical vocabulary of assertions:

* The order relation {name Lean.Order.PartialOrder.rel}`⊑` is entailment.
* The meet {name Lean.Order.meet}`⊓` is conjunction and the join {name Lean.Order.join}`⊔` is disjunction.
* The top element {name Lean.Order.top}`⊤` is the trivial assertion and the bottom element {name Lean.Order.bot}`⊥` is the absurd assertion.
* The indexed supremum {name Lean.Order.iSup}`⨆` is existential quantification and the indexed infimum {name Lean.Order.iInf}`⨅` is universal quantification.
  Their notation resembles that of ordinary quantifiers; for example, {lean}`⨆ x : α, P x` asserts the existence of something that satisfies {lean}`P`.
* The Heyting implication {name Lean.Order.himp}`⇨` is implication internal to the assertion language.
:::
::::

:::leanSection
```lean -show
universe u
variable {Pred : Type u} [Assertion Pred] {P Q : Pred}
```
The difference between entailment and implication is that entailment is a statement in Lean's logic, while implication is internal to the assertion language: for assertions {lean}`P` and {lean}`Q`, {lean}`P ⊑ Q` is a {lean}`Prop` while {lean}`P ⇨ Q` is again an assertion.
:::

{module}`Std.WP` comes with {name}`Assertion` instances for {lean}`Prop`, {lean}`Unit`, function types, and pairs.
The lattice operations on {lean}`Prop` coincide with the ordinary logical connectives, with entailment being implication.
The lattice operations on a function type such as {lean}`Nat → Prop` operate pointwise, so entailment of state predicates is universally-quantified implication.
The lattice operations on a pair such as {lean}`(Nat → Prop) × (Bool → Prop)` operate component-wise, so entailment of paired predicates is the conjunction of entailments of the component predicates.

:::example "Entailment at Different Assertion Types"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order
```
At {lean}`Prop`, entailment is implication:
```lean
example (P Q : Prop) : (P ⊑ Q) = (P → Q) := rfl
```
At a state predicate type, entailment is implication at every state:
```lean
example (f g : Nat → Prop) :
    (f ⊑ g) = ∀ n, f n → g n := rfl
```
Entailment of pairs is conjunction of entailments:
```lean
example (f₁ f₂ : Nat → Prop) (g₁ g₂ : Bool → Prop) :
    ((f₁, g₁) ⊑ (f₂, g₂)) = ((f₁ ⊑ f₂) ∧ (g₁ ⊑ g₂)) := rfl
```
A concrete entailment between state predicates can be proved by unfolding the entailment order and reasoning about each state:
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
Ordinary propositions that do not mention the state can be embedded into any assertion lattice with {deftech}[corner brackets].
This is written with the syntax {lean (type := "Pred")}`⌜P⌝`, which is notation for {name}`Lean.Order.CompleteLattice.ofProp`.
:::syntax term (title := "Embedding Propositions") (namespace := Lean.Order)
```grammar
⌜$_:term⌝
```
{includeDocstring Lean.Order.CompleteLattice.ofProp}
:::
::::

{docstring Lean.Order.CompleteLattice.ofProp}

:::leanSection
```lean -show
universe u
variable {p : Prop} {n k : Nat} {Pred : Type u} [Assertion Pred]
```
An assertion of the form {lean (type := "Pred")}`⌜p⌝` is {deftech (key := "pure assertion")}_pure_: its truth is independent of the state.
At the assertion type {lean}`Prop`, {lean (type := "Prop")}`⌜p⌝` is the proposition {lean}`p` itself, and at a state predicate type such as {lean}`Nat → Prop`, it is the constant predicate {lean (type := "Nat → Prop")}`fun _ => p`.
Specifications for a concrete monad can therefore state propositions directly, as in {lean (type := "Nat → Prop")}`fun s => s = n`.
Corner brackets are necessary when the assertion type is abstract, as in a specification that quantifies over a monad and its assertion type {lean}`Pred`.
In this case, a proposition such as {lean}`n = k` is not an assertion, but {lean (type := "Pred")}`⌜n = k⌝` embeds it into {lean}`Pred`.
The {ref "vcgen-monad-polymorphic" (domain := Manual.examples)}[monad-polymorphic example] at the end of this chapter uses corner brackets for this reason.
{tactic}`vcgen` moves pure preconditions into the ordinary Lean context, where they become hypotheses of the verification conditions.
:::

:::example "Assertions for State Monads"
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
Entailment between such assertions is pointwise implication:
```lean
example : ItIsSecret ⊑ (⌜True⌝ : String → Prop) := by
  simp [ItIsSecret, PartialOrder.rel]
```
:::

## Exception Postconditions

A postcondition for successful termination is a function from the return value to an assertion.
Programs that can throw exceptions additionally require an {deftech}_exception postcondition_ that asserts what holds when the program throws an exception.
The exception postcondition type of a given monad is determined by its {name}`WP` instance.

For example, the {name}`WP` instance for {lean}`ExceptT String (StateM Nat) Bool` determines {lean}`Nat → Prop` as the assertion type, hence {lean}`Bool → Nat → Prop` as the postcondition type, and {lean}`String → Nat → Prop` as the exception postcondition type.
A monad without exceptions has the exception postcondition type {name}`Unit`.
:::leanSection
```lean -show
universe u
variable {Pred EPred ε : Type u} [Assertion Pred] [Assertion EPred]
```
For a base monad with assertion type {lean}`Pred` and exception postcondition type {lean}`EPred`, an exception layer such as {lean}`ExceptT ε` contributes one more exception postcondition, which gives the type {lean}`(ε → Pred) × EPred`.
:::
Since unit and pair types come with {name}`Assertion` instances, these “stacks” of exception postconditions are automatically assertions as well.
The {name}`WP` instances for monad transformers ensure that stacks of monad transformers have corresponding exception postcondition stacks.

:::syntax term (title := "Exception Postcondition Stacks") (namespace := Std.WP)
The notation `EStack⟨e₁, e₂, ...⟩` abbreviates the type of exception postcondition stack `e₁ × (e₂ × (... × Unit))`, and the notation `estack⟨v₁, v₂, ...⟩` builds a value `(v₁, v₂, ..., ())` of such a stack.
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
Specifications for programs that might throw exceptions come in two varieties. The {deftech}_total correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'⦄` asserts that, given {lean}`P` holds, then {lean}`prog` terminates normally _and_ {lean}`Q'` holds for the result. The {deftech}_partial correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` asserts that, given {lean}`P` holds, and _if_ {lean}`prog` terminates normally _then_ {lean}`Q'` holds for the result.
A triple without an explicit exception postcondition carries the bottom assertion {lean}`(⊥ : EPred)` and thus has the total interpretation; between {lean (type := "EPred")}`⊥` and {lean (type := "EPred")}`⊤`, the exception postcondition expresses a spectrum of correctness properties.
:::

## 谓词变换器

```lean -show
universe u v w
variable {Pred : Type u} {EPred : Type v} {α : Type w} [Assertion Pred] [Assertion EPred]
```

A predicate transformer is a function from postconditions into assertions that describe preconditions.

{docstring Lean.Order.PredTrans}

:::leanSection
```lean -show
variable {x y : PredTrans Pred EPred α} {post post' : α → Pred} {epost epost' : EPred}
```
The partial order on predicate transformers is inherited pointwise from the assertion lattice: {lean}`x ⊑ y` when {lean}`x.apply post epost ⊑ y.apply post epost` for all {lean}`post` and {lean}`epost`.
Every predicate transformer that a {name}`WP` instance produces is {deftech}_monotone_: if {lean}`post ⊑ post'` and {lean}`epost ⊑ epost'`, then {lean}`x.apply post epost ⊑ x.apply post' epost'`.

{docstring Lean.Order.PredTrans.Monotone}
:::

谓词变换器构成一个单子。
The {name}`pure` operator is the identity transformer; it simply instantiates the postcondition with its argument.
{name}`bind` 运算符组合谓词变换器。

{docstring PredTrans.pure}

{docstring PredTrans.bind}

The helper operators {name}`PredTrans.pushArg`, {name}`PredTrans.pushExceptT`, and {name}`PredTrans.pushOptionT` modify a predicate transformer by adding a standard side effect.
它们用于实现 {name}`StateT`、{name}`ExceptT` 和 {name}`OptionT` 等变换器的 {name}`WP` 实例；也可用来实现可按这些变换器之一理解的单子。
例如，{name}`PredTrans.pushArg` 通常用于状态单子，但也可以用它实现读取器单子的实例，将读取器的值视为只读状态。

{docstring PredTrans.pushArg}

{docstring PredTrans.pushExceptT}

{docstring PredTrans.pushOptionT}

### 最弱前置条件

```lean -show
variable {Prog : Type u} {Value : Type v} [WP Prog Value Pred EPred] {prog : Prog} {post : Value → Pred} {epost : EPred}
```

The {tech}[weakest precondition] semantics of a program type is provided by the {name}`WP` type class.
An instance {lean}`WP Prog Value Pred EPred` interprets programs of type {lean}`Prog` with results of type {lean}`Value` as monotone predicate transformers over the assertion type {lean}`Pred` and the exception postcondition type {lean}`EPred`.
The type {lean}`Prog` determines {lean}`Value`, {lean}`Pred` and {lean}`EPred` as {name}`outParam`s.
The function {name}`wp` applies the interpretation: {lean}`wp prog post epost` is the weakest precondition under which the program {lean}`prog` establishes the postcondition {lean}`post` and the exception postcondition {lean}`epost`.

{docstring WP}

{docstring WP.wp}

A program {lean}`prog` that is {deftech}_conjunctive_ distributes a weakest precondition of a meet of two postconditions into a meet of the weakest preconditions of the postconditions.
The type class {name}`WPConjunctive` captures this property, which allows two specifications for {lean}`prog` to be combined into a single strongest one.
This is analogous to {name}`Triple.and`, which combines {tech}[Hoare triples].

{docstring WPConjunctive}

### Monads That Preserve Weakest Preconditions

Most of the built-in specification lemmas for {tactic}`vcgen` rely on the presence of a {name}`WPMonad` instance.
A {name}`WP` instance is provided for a particular type, but a monad is a polymorphic type.
{lean}`StateM Nat Unit` and {lean}`StateM Nat String` are different types, but their weakest preconditions should be related.
Instances of {name}`WPMonad` assign a {name}`WP` interpretation to each for every type that the monad can be applied to.
It additionally contains evidence that this interpretation is sound for the monad's implementations of {name Pure.pure}`pure` and {name Bind.bind}`bind`.
This means that to prove something about a {keywordOf Lean.Parser.Term.do}`do` block, it suffices to prove it about the chain of {tech (key := "do elements")}[elements] of the block.
In other words, a {name}`WPMonad` instance enables compositional reasoning about {keywordOf Lean.Parser.Term.do}`do` blocks.

{docstring WPMonad}

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

The missing instance prevents {tactic}`vcgen` from using its specifications for {name}`pure` and {name}`bind`.
For example, the following function reverses a list with a {keywordOf Lean.Parser.Term.doFor}`for` loop in {name}`Identity`:
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
The theorem {name}`rev_correct` states that {name}`rev` agrees with {name}`List.reverse`.
Without a {name}`WPMonad` instance, {tactic}`vcgen` cannot decompose {name}`rev` into a sequence of steps in {name}`Id` and reports that no specification applies to the program:
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
When no specification is applicable to {name}`bind`, the problem is usually a missing {name}`WPMonad` instance.
添加合适的实例即可解决此问题：
```lean
instance : WPMonad Identity Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl
```
With this instance, and a suitable invariant, {tactic}`vcgen` and the {tactic}`grind`-mode {ref "grind-interactive"}[tactic] {grindTactic}`finish` can prove the theorem.
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

### Soundness Lemmas
%%%
tag := "vcgen-soundness"
%%%

Monads that can be invoked from pure code typically provide an invocation operator that takes any required input state as a parameter and returns either a value paired with an output state or some kind of exceptional value.
例如 {name}`StateT.run`、{name}`ExceptT.run` 和 {name}`Id.run`。
{deftech}_Soundness lemmas_ provide a bridge between statements about invocations of monadic programs and those programs' {tech}[weakest precondition] semantics as given by their {name}`WP` instances.
它们表明：若调用的最弱前置条件为真，则关于该调用的性质为真。

{docstring Id.of_run_eq_wp}

{docstring StateM.of_run_eq_wp}

{docstring StateM.of_run'_eq_wp}

{docstring ReaderM.of_run_eq_wp}

{docstring Except.of_eq_wp}

{docstring Option.of_eq_wp}

{docstring EStateM.of_run_eq_wp}

## 霍尔三元组

{deftech (key := "Hoare triple")}_霍尔三元组_{citep hoare69}[] 由前置条件、程序和后置条件组成。
若在满足前置条件的状态中运行程序，所得状态将满足后置条件。

{docstring Triple}

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
{lean}`⦃ P ⦄ x ⦃ Q; E ⦄` is syntactic sugar for {lean}`Triple x P Q E`.
When the exception postcondition is omitted, as in {lean}`⦃ P ⦄ x ⦃ Q ⦄`, it defaults to the bottom assertion {lean (type := "EPred")}`⊥`, asserting that the program does not throw an exception.
:::
::::

{docstring Triple.and}

{docstring Triple.mp}

## 规约引理

{deftech}_Specification lemmas_ are designated theorems that associate a Hoare triple with a program construct, such as {name Bind.bind}`bind`, {name Pure.pure}`pure`, a loop, or an application of a library function.
A given program construct may have multiple specification lemmas that are applicable in different situations; they are tried in priority order until one can be instantiated.
:::leanSection
```lean -show
variable {prog : Prog} {P : Pred} {Q : Value → Pred} {E : EPred}
variable {A : Sort u} {B : A → Sort v} {f : (a : A) → B a}
```
The {tactic}`vcgen` tactic decomposes a goal {lean}`P ⊑ wp prog Q E` by applying a specification lemma whose program matches {lean}`prog`, as the section on {ref "vcgen-verification-conditions"}[verification conditions] describes.
If no specification lemma applies to {lean}`prog`, then {tactic}`vcgen` reports an error that names {lean}`prog` and the candidate lemmas.
Specification lemmas make reasoning about programs _modular_: the specification lemma of a function {lean}`f` is proved once, and {tactic}`vcgen` applies it at every call of {lean}`f` without unfolding the definition of {lean}`f`.
In this respect, {name Pure.pure}`pure` and {name Bind.bind}`bind` are ordinary functions: the specification lemmas {name}`Spec.pure` and {name}`Spec.bind` hold in every monad with a {name}`WPMonad` instance.
:::

将 {attr}`spec` 属性应用于陈述为霍尔三元组的定理时，会把该定理注册为规约引理。
这些引理按优先级顺序使用。

{attr}`spec` 属性也可以应用于定义。
用于定义时，它表示应在生成验证条件期间展开该定义。

:::syntax attr (title := "`spec` 规约属性")
```grammar
spec $[$_:prio]?
```
{includeDocstring Lean.Parser.Attr.spec}
:::

A {deftech}_logical variable_ is a universally quantified variable of a specification lemma that does not occur in the program.
Logical variables are used to relate the initial state to the final state and the return value.

An {deftech}_auto-framing specification_ is a specification lemma whose postcondition is a universally quantified variable, with a precondition that is stated in terms of that variable.
When {tactic}`vcgen` applies an auto-framing specification, unification instantiates the postcondition with the assertion that the rest of the program requires; this means that there's no need to prove that the postcondition entails the subsequent precondition.
Every fact that the postcondition states about parts of the state that the program does not change is preserved without further proof.
As an example, the specification lemma {name}`Spec.bind` is auto-framing: its precondition is the weakest precondition of the first action with respect to the weakest precondition of the second.

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

:::example "Logical Variables"
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
The specification uses a logical variable to stand for the initial state:
```lean
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```

The assertion in the precondition is a function because the assertion type of {lean}`StateM Nat` is {lean}`Nat → Prop`.

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat Unit) Unit (Nat → Prop) EStack⟨⟩
```

## 不变式规约

The {tech}[specification lemmas] for {name}`ForIn.forIn` and {name}`ForIn'.forIn'` take parameters of type {name}`Invariant`, and {tactic}`vcgen` ensures that invariants are not accidentally generated by other automation.

{docstring Invariant}

不变式使用列表来建模 {keywordOf Lean.Parser.Term.doFor}`for` 循环中的值序列。
An invariant is a function of the prefix of elements that the loop has already consumed, the suffix of elements that remain, the current accumulator state, and any further state arguments of the monad's assertion language.

{docstring Invariant.withEarlyReturnNewDo}

# 验证条件
%%%
tag := "vcgen-verification-conditions"
%%%

The {tactic}`vcgen` tactic converts a goal that's expressed in terms of weakest preconditions to a set of invariants and verification conditions that, together, suffice to prove the original goal.
In particular, {tech}[Hoare triples] are defined in terms of weakest preconditions, so {tactic}`vcgen` can be used to prove them.

:::leanSection
```lean -show
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α β : Type u} {e e' : m α} {P P' R : Pred} {Q Q' : α → Pred} {E E' : EPred} {φ : Prop} {x : m β} {f : β → m α} {a : β} {γ : Sort w} {e₁ e₂ : γ}
```
{TODO}[This model does not cover frames: the `frames` clause and frameprocs.]
The verification conditions for a goal are generated using the same machinery as {tactic}`grind`.
Generation proceeds as follows:
1. The goal is brought into the form of an entailment {lean}`P ⊑ R` between assertions.
   Binders are introduced, {tech}[Hoare triples] are unfolded to {lean}`P ⊑ wp e Q E`, and goals of the form {lean}`wp e Q E` become {lean}`⊤ ⊑ wp e Q E`.
2. The precondition {lean}`P` is moved into the local context: a pure assertion {lean (type := "Pred")}`⌜φ⌝` becomes a hypothesis {lean}`φ`, an {ref "vcgen-assertion-lattices"}[existential] {name Lean.Order.iSup}`⨆` becomes a variable, and the arguments of a state predicate become variables.
3. The assertion {lean}`R` is recursively decomposed into goals based on its connectives: meets {name Lean.Order.meet}`⊓` are split into one goal per conjunct, the antecedents of {name Lean.Order.himp}`⇨` are mvoed into the precondition, pure assertions {lean (type := "Pred")}`⌜φ⌝` are transformed into the proposition {lean}`φ`, and {name Lean.Order.top}`⊤` goals are closed immediately.
4. If {lean}`R` is {lean}`wp e Q E`, then the program {lean}`e` is decomposed:
   1. A {keywordOf Lean.Parser.Term.«let»}`let`-binding is introduced, becoming a hypothesis.
   2. An application of an {tech}[auxiliary matching function] whose {tech (key := "match discriminant")}[discriminant] is a constructor application is reduced; any other conditional or match is split into one goal per branch.
   3. An application of a function is handled by the first applicable specification lemma in priority order.
      Hypotheses that are Hoare triples also count as specification lemmas.
      Lean includes specification lemmas for {name Bind.bind}`bind`, {name Pure.pure}`pure`, {name}`ForIn.forIn` and the other functions that result from desugaring {keywordOf Lean.Parser.Term.do}`do`-notation.
      If no specification lemma applies, then {tactic}`vcgen` reports an error.

      A specification lemma {lean}`P' ⊑ wp e' Q' E'` is applied by transitivity of {name Lean.Order.PartialOrder.rel}`⊑`: the goal {lean}`P ⊑ wp e Q E` follows from {lean}`P ⊑ P'` and {lean}`wp e' Q' E' ⊑ wp e Q E`.
      The second entailment holds when {lean}`e'` unifies with {lean}`e`, {lean}`Q' ⊑ Q` and {lean}`E' ⊑ E`.
      In effect, {tactic}`vcgen` replaces the weakest precondition in the goal by the precondition of the lemma, which gives the new goal {lean}`P ⊑ P'`.
   5. The variables in the lemma that occur in the program are instantiated using unification.
      The universally quantified postcondition of an {tech}[auto-framing specification] becomes {lean}`Q`, so {lean}`Q' ⊑ Q` holds by reflexivity and no goal for the postcondition remains.
      Otherwise, the entailments {lean}`Q' ⊑ Q` and {lean}`E' ⊑ E` become new goals.
      Assumptions of a type registered with {attr}`spec_invariant_type` become invariant goals.
      The {tech}[logical variables] of the lemma appear as metavariables in all of these new goals.
5. Each new goal is processed again from step 1.
   For example, the specification lemma {name}`Spec.bind` is auto-framing and has the precondition {lean}`wp x (fun a => wp (f a) Q E) E`.
   For a goal {lean}`P ⊑ wp (x >>= f) Q E`, the new goal is {lean}`P ⊑ wp x (fun a => wp (f a) Q E) E`.
   When a specification lemma for {lean}`x` applies to this goal, the entailment between the postconditions has {lean}`wp (f a) Q E` on the right, so the rest of the program is decomposed in the same way.
   Before a new goal is processed, its hypotheses are {tech (key := "internalization")}[internalized] into {tactic}`grind`'s “whiteboard”, and a goal whose hypotheses are contradictory is dropped.
6. The verification conditions are the remaining goals that cannot be further decomposed by these steps.
   Before each verification condition is emitted, {tactic}`vcgen` solves its conjuncts that are either {lean}`True` or an equality {lean (type := "Prop")}`e₁ = e₂` where {lean}`e₁` and {lean}`e₂` can be made definitionally equal by unification..
   Solving an equality can assign a metavariable, so some logical variables become assigned: a conjunct `s = ?n` assigns `?n := s`.
   The unsolved conjuncts remain as the verification condition.
7. The resulting subgoals receive the names `inv1`, `inv2`, … for invariants and `vc1`, `vc2`, … for verification conditions, in the order of generation.

VC generation stops early after {name Lean.Elab.Tactic.Do.VCGen.Config.stepLimit}`stepLimit` program steps.
An {keywordOf Lean.Parser.Tactic.vcgen}`until` clause stops VC generation at the first program that matches the given pattern.
A {keywordOf Lean.Parser.Tactic.vcgen}`with` clause runs the given {tactic}`grind`-mode step on every remaining verification condition.
A clause {keywordOf Lean.Parser.Tactic.vcgen}`simplifying_assumptions` `[h₁, h₂]` rewrites the hypotheses that binders and branches introduce, and the state arguments of each weakest precondition, with `h₁` and `h₂` as additional rewrite rules.
This keeps the intermediate goals in a normal form that the user chooses: for example, a sequence of state updates can fold into one constructor application, so that the goals do not grow with the number of updates.
Simplified hypotheses also help {tactic}`grind` to detect contradictory goals.
:::

# Enabling {tactic}`vcgen` For Monads

If a monad is implemented in terms of {tech}[monad transformers] that are provided by the Lean standard library, such as {name}`ExceptT` and {name}`StateT`, then it should not require additional instances to work with {tactic}`vcgen`.
其他单子则需要 {name}`WP`、{name}`LawfulMonad` 和 {name}`WPMonad` 实例。

Once the basic instances are provided, the next step is to prove a {ref "vcgen-soundness"}[soundness lemma].
该引理应表明：运行单子计算并断言所需谓词时的最弱前置条件，确实足以证明该谓词。

除单子的定义外，典型的库还会提供一组原语运算符。
每个原语都应配备一个{tech (key := "Specification lemmas")}[规约引理]。
此外，将状态内部实现设为私有，并导出一组精心设计的断言运算符，可能也很有用。

The specification lemmas for the library's primitive operators should preserve every fact about the state that they do not deliberately hide.
While it's often easier to think in terms of how the operator transforms an input state into an output state, {tech}[verification condition] generation works more reliably when the postcondition is universally quantified, so that automation can instantiate it with the precondition of the next statement instead of proving an entailment.

:::example "Auto-Framing Specifications"
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
Thinking chronologically, a reasonable specification is that the value of the output state is twice that of the input state.
This is expressed using a {tech}[logical variable] that stands for the initial state:
```lean -keep
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```
However, an equivalent {tech}[auto-framing specification] leads to smaller verification conditions when {name}`double` is used in other functions:
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
Any property that {lean}`Q` states about state that {name}`double` does not change, such as a second state layer in a monad transformer stack, holds after the call.
At a call of {name}`double`, {tactic}`vcgen` instantiates {lean}`Q` with the postcondition that the rest of the program requires, so no entailment between postconditions remains as a verification condition.

The precondition of {name}`better_double_spec` is exactly the weakest precondition of {name}`double`, so callers depend on the complete behavior of {name}`double`.
An auto-framing specification can also leave details open.
For example, the precondition {lean (type := "Nat → Prop")}`fun s => ∀ s', s ≤ s' → Q () s'` only promises that {name}`double` does not decrease the state.
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

The soundness lemma has one important detail: the weakest precondition is applied to the empty array.
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

A better specification for {name}`log` is an {tech}[auto-framing specification]:
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

# Discharging Verification Conditions
%%%
tag := "vcgen-discharging"
%%%

The verification conditions that {tactic}`vcgen` produces are ordinary Lean goals, so any tactic can discharge them.
However, because {tactic}`vcgen` uses {tactic}`grind`'s internal representations, it is often fastest to discharge them using {ref "grind-interactive"}[`grind` tactics].
The {keywordOf Lean.Parser.Tactic.vcgen}`with` clause runs a single {tactic}`grind`-mode step, typically {grindTactic}`finish`, on every remaining verification condition.
The step runs inside the goal context that {tactic}`vcgen` {tech (key:="internalization")}[internalized] into {tactic}`grind`'s “whiteboard” during generation, so the context is not re-internalized for every verification condition.
Internalizing the context of a single verification condition takes time linear in the size of that context, so internalizing the context prefix that all verification conditions share only once is cheaper than internalizing each context on its own.
If {grindTactic}`finish` succeeds at closing only some of the goals, wrapping it in {grindTactic}`try` suppresses the errors.

When working with concrete monads, the verification conditions speak directly about result values and states.
Monad-polymorphic theorems instead lead to goals over an {ref "vcgen-assertion-lattices"}[abstract assertion lattice].
{tactic}`grind` discharges such goals when they reduce to entailments between pure assertions, as in the following example. Other goals over an abstract lattice can require a manual proof.

:::example "Monad-Polymorphic Proofs" (tag := "vcgen-monad-polymorphic")
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```
函数 {name}`bump` 将状态增加指定的量，并返回所得值。
The underlying monad {lean}`m` and its assertion types stay abstract.
Because the assertion type {lean}`Pred` is abstract, the specification below embeds its propositions with {tech}[corner brackets].
```lean
variable {m : Type → Type v} [Monad m]
variable {Pred EPred : Type}
variable [Assertion Pred] [Assertion EPred]
variable [WPMonad m Pred EPred]

def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

The specification lemma for {name}`bump` quantifies over the abstract assertion lattice, and its verification conditions are entailments in that lattice.
The {grindTactic}`finish` step discharges them:
```lean
theorem bump_correct :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ fun r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  vcgen [bump] with finish
```
:::
