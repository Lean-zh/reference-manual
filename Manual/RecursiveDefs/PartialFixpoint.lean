/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity
import Manual.RecursiveDefs.PartialFixpoint.Theory

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600

#doc (Manual) "偏不动点递归" =>
%%%
tag := "partial-fixpoint"
%%%

所有定义在根本上都是方程：被定义的新常量等于定义的右侧。
对于以 {ref "structural-recursion"}[结构递归] 定义的函数，这个方程在 {tech (key := "definitional equality")}[定义上]成立，并且函数应用会返回唯一的值。
对于以 {ref "well-founded-recursion"}[良基递归] 定义的函数，这个方程可能只在 {tech (key := "proposition")}[命题上]成立，但函数对任意类型正确的实参应用，都等于定义所规定的相应值。
在这两种情形下，函数对所有输入都终止这一事实，意味着函数应用计算出的值总是唯一确定的。


在某些函数并非对所有实参都终止的情况下，这个方程未必能为每个输入_唯一地_确定返回值；但尽管如此，仍可能存在满足该定义方程的函数。
此时，仍可能把它定义为一个 {deftech (key := "partial fixpoint")}_偏不动点_。
任何满足该定义方程的函数，都可以用来说明该方程不会造成逻辑矛盾，随后再把这个方程证明为该函数的定理。
和其他递归函数定义策略一样，编译后的代码会使用函数最初写下来的形式；类似于借助消去器或基于可达性证明的递归来定义函数，定义偏不动点所用到的函数，只是为了在 Lean 的逻辑中为其方程提供数学推理上的正当性。

术语 {tech (key := "partial fixpoint")}_偏不动点_ 是 Lean 特有的。
凡是声明为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数，只要其返回值类型可被占据，就不需要终止性证明；但从 Lean 逻辑的视角看，它们是完全不透明的。
而偏不动点则不同：在写证明时，可以按照其定义方程对它们进行重写。
从逻辑上说，偏不动点是一些全函数：把它们应用到实参上时不会 {tech (key := "definitional equality")}[在定义上] 归约，但 Lean 会为它们提供等式重写规则。
它们之所以称为“偏”，是因为定义方程未必会为所有可能的实参指定一个值。


偏不动点不仅能定义那些无法用结构递归或良基递归表达的函数；在其他情况下，这项技术同样有用。
即便某个定义方程已经完整描述了函数行为，且原则上也能用 {ref "well-founded-recursion"}[良基递归] 给出终止性证明，把函数定义为偏不动点仍可能更方便，因为这样无需书写终止性证明。

只有在显式请求时——即在定义上标注 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`——递归函数才会按偏不动点来定义。

:::paragraph
可以定义为偏不动点的函数有两类：

 * 返回类型可被占据的尾递归函数

 * 返回值位于某个合适单子中的函数，例如 {name}`Option` 单子

这两类函数都建立在同一套理论与构造之上：链完备偏序中单调方程的最小不动点。

:::

与结构递归和良基递归一样，Lean 也允许把 {tech (key := "mutually recursive")}[互递归] 函数定义为偏不动点。
要使用这一特性，{tech (key := "mutual block")}[互递归块] 中的每个函数定义都必须带有 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 修饰符。

```lean -show
section
variable (p : Nat → Bool)
```

:::example "按偏不动点定义"

下面这个函数寻找使谓词 {lean}`p` 成立的最小自然数。
如果 `p` 永远不成立，那么这个方程并没有规定其行为：在这种情况下，函数 {lean}`find` 返回 {lean  (type := "Nat")}`42` 或任意其他 {lean}`Nat`，都依然满足该方程。

```lean
def find (p : Nat → Bool) (i : Nat := 0) : Nat :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint
```

精译器能够证明，满足该方程的函数确实存在。
在 Lean 的逻辑中，{lean}`find` 被定义为任意一个这样的函数。
:::

```lean -show
end
```

# 尾递归函数
%%%
tag := "partial-fixpoint-tailrec"
%%%

:::paragraph

若满足下列两个条件，递归函数就可以定义为偏不动点：

 1. 函数的返回类型可被占据（与{ref "partial-unsafe"}[标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数]类似）——拥有 {name}`Nonempty` 或 {name}`Inhabited` 实例皆可。
 2. 所有递归调用都位于函数的 {tech (key := "tail position")}[尾位置]。

若函数体中的一个表达式属于下列情形，则它处于 {deftech (key := "tail position")}_尾位置_：

 * 函数体本身；
 * 处于尾位置的 {keywordOf Lean.Parser.Term.match}`match` 表达式的各个分支；
 * 处于尾位置的 {keywordOf termIfThenElse}`if` 表达式的各个分支；
 * 处于尾位置的 {keywordOf Lean.Parser.Term.let}`let` 表达式的函数体。

特别地，{keywordOf Lean.Parser.Term.match}`match` 表达式的 {tech (key := "match discriminant")}[判别项]、{keywordOf termIfThenElse}`if` 表达式的条件，以及函数实参，都不处于尾位置。

:::

```lean -show
-- 测试只需 nonempty 即可
inductive A : Type where
  | mkA
  | mkA'

instance : Nonempty A := ⟨.mkA⟩

def getA (n : Nat) : A :=
  getA (n + 1)
partial_fixpoint

example (n : Nat) : getA n = getA (n + 3) := by
  conv => lhs; rw [getA, getA, getA]
```

:::example "循环也是尾递归函数"

由于函数体本身就是一个 {tech (key := "tail position")}[尾位置]，无限循环函数 {lean}`loop` 是尾递归的。
它可以定义为偏不动点。

```lean
def loop (x : Nat) : Nat := loop (x + 1)
partial_fixpoint
```

:::

:::example "带分支的尾递归"

{lean}`Array.find` 也可以借助良基递归加上终止性证明来构造，但用 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 来定义往往更方便，因为这样不需要终止性证明。

```lean
def Array.find (xs : Array α) (p : α → Bool)
    (i : Nat := 0) : Option α :=
  if h : i < xs.size then
    if p xs[i] then
      some xs[i]
    else
      Array.find xs p (i + 1)
  else
    none
partial_fixpoint
```

如果递归调用的结果不是直接返回，而是先传给另一个函数，那么它就不在尾位置，此定义也就会失败。

```lean -keep +error (name := nonTailPos)
def List.findIndex (xs : List α) (p : α → Bool) : Int :=
  match xs with
  | [] => -1
  | x::ys =>
    if p x then
      0
    else
      have r := List.findIndex ys p
      if r = -1 then -1 else r + 1
partial_fixpoint
```
递归调用处的错误消息是：
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    if ys✝.findIndex p = -1 then -1 else ys✝.findIndex p + 1
  Tried to apply 'monotone_ite', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
```

:::

# 单子函数
%%%
tag := "partial-fixpoint-monadic"
%%%


如果函数的返回类型是某个带有 {name}`Lean.Order.MonoBind` 实例的单子（例如 {name}`Option`），那么把函数定义为偏不动点会更强大。
这时，递归调用不再局限于尾位置，还可以出现在 {name}`bind`、{name}`List.mapM` 等高阶单子函数内部。

能够支持这一点的高阶函数集合是{ref "partial-fixpoint-theory"}[可扩展的]，因此这里不给出穷尽列表。
理想状态是：只要一个单子递归函数定义是通过 {name}`bind` 这类抽象单子操作构造出来的，并且没有拆开单子的抽象（例如对 {name}`Option` 的值做模式匹配），它就应该被接受。
特别地，使用 {tech (key := "{keywordOf Lean.Parser.Term.do}`do`-notation")}[{keywordOf Lean.Parser.Term.do}`do` 记法] 应当可行。

:::example "单子函数"

下面这个函数在 {name}`Option` 单子中实现了 Ackermann 函数，并且无需显式或隐式终止性证明即可被接受：

```lean -keep
def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint
```

如果适当设置，递归调用也可以出现在 {name}`List.mapM` 之类的高阶函数内部，以及 {tech (key := "{keywordOf Lean.Parser.Term.do}`do`-notation")}[{keywordOf Lean.Parser.Term.do}`do` 记法] 中：

```lean -keep
structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint
```

若对递归调用的结果做模式匹配，就会阻止该定义作为偏不动点通过：

```lean -keep +error (name := monoMatch)
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      match List.findIndex ys p with
      | none => none
      | some r => some (r + 1)
partial_fixpoint
```
```leanOutput monoMatch
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    match ys✝.findIndex p with
    | none => none
    | some r => some (r + 1)
```

在这个具体例子里，用 {name}`Functor.map` 代替显式模式匹配就有帮助：

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```
:::

# 偏正确性定理
%%%
tag := "partial-correctness-theorem"
%%%


对于每个定义为偏不动点的函数，Lean 都会证明其定义方程成立。
这使得人们可以通过重写来进行证明。
不过，这些等式定理不足以推理函数在那些其规范本身不终止的实参上的行为。
在运行时会导致无限递归的代码路径，在证明中最终只会变成无限长的重写链。

另一方面，在合适单子中的偏不动点还会提供额外定理，把“不终止”所对应的未定义值映射为该单子中的适当值。
在 {name}`Option` 单子中，当定义方程规定某些输入上不终止时，偏不动点在这些输入上的值就等于 {name}`Option.none`。
基于这一事实，Lean 会为该函数证明一个 {deftech (key := "partial correctness theorem")}_偏正确性定理_，使人们能够在函数结果为 {name}`Option.some` 时推出相应事实。


::::example "偏正确性定理"

回忆前面的例子 {lean}`List.findIndex`：

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```

有了这个函数定义，Lean 会自动证明下面的偏正确性定理：

```signature
List.findIndex.partial_correctness.{u_1} {α : Type u_1}
  (p : α → Bool)
  (motive : List α → Nat → Prop)
  (h :
    ∀ (findIndex : List α → Option Nat),
      (∀ (xs : List α) (r : Nat), findIndex xs = some r → motive xs r) →
        ∀ (xs : List α) (r : Nat),
          (match xs with
              | [] => none
              | x :: ys =>
                if p x = true then some 0
                else (fun x => x + 1) <$> findIndex ys) = some r →
            motive xs r)
  (xs : List α) (r : Nat) :
  xs.findIndex p = some r →
    motive xs r
```

:::paragraph
这里的动机（motive）是 {lean}`List.findIndex` 的参数类型与返回类型之间的一个关系，其中返回类型里的 {name}`Option` 已被去掉。
若给定一个签名与 {lean}`List.findIndex` 相容的任意偏函数，并且满足下列条件：

 * 对所有该任意函数返回某个值（而不是 {name}`none`）的输入，动机都成立；

 * 按定义方程进行一步重写、并把其中递归调用替换为该任意函数后，也能推出动机成立；

那么，对所有 {lean}`List.findIndex` 返回 {name}`some` 的输入，动机都成立。

:::

偏正确性定理是一条推理原理。
它可以用来证明：得到的数字是该列表中的一个合法索引，而且谓词在该索引处成立：

```lean
theorem List.findIndex_implies_pred
    (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i →
    ∃x, xs[i]? = some x ∧ p x := by
  apply List.findIndex.partial_correctness
          (motive := fun xs i => ∃ x, xs[i]? = some x ∧ p x)
  intro findIndex ih xs r hsome
  split at hsome
  next => contradiction
  next x ys =>
    split at hsome
    next =>
      have : r = 0 := by simp_all
      simp_all
    next =>
      simp only [Option.map_eq_map, Option.map_eq_some_iff] at hsome
      obtain ⟨r', hr, rfl⟩ := hsome
      specialize ih _ _ hr
      simpa
```

::::

# 偏不动点下的互递归
%%%
tag := "mutual-partial-fixpoint"
%%%

Lean 支持使用 {tech (key := "partial fixpoint")}[偏不动点] 来定义 {tech (key := "mutually recursive")}[互递归] 函数。
互递归既可以通过 {tech (key := "mutual block")}[互递归块] 引入，也可能来自 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 代码块。
带偏不动点的互递归规则，会应用到由互递归组的{ref "mutual-syntax"}[精译步骤]所得、经过提升后且实际上互相递归的一组定义上。

若互递归组中的所有函数都带有 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 子句，就会采用这一策略。

{include 1 Manual.RecursiveDefs.PartialFixpoint.Theory}
