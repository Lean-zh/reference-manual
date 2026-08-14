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


open Lean.Grind

#doc (Manual) "`if`-`then`-`else` 规范化" =>
%%%
tag := "grind-if-then-else-norm"
%%%

```lean -show
open Std
```

这个例子展示了 {tactic}`grind` “开箱即用”的威力。
后续示例会探讨如何把添加 {attrs}`@[grind]` 标注纳入开发流程，从而让 {tactic}`grind` 在新领域中更有效。
这个例子并不依赖 {tactic}`grind` 的任何代数扩展；我们只使用：
* 对库中已标注定理的实例化，
* {tech (key := "Congruence closure")}[同余闭包]，以及
* 分类讨论。

这里的解法建立在 Chris Hughes 早先的形式化基础上，但有几项显著改进：
* 验证与代码彼此分离，
* 证明现在是一行式写法，把 {tactic}`fun_induction` 与 {tactic}`grind` 结合起来，
* 该证明对代码变动（例如把 {name}`HashMap` 换成 {name}`TreeMap`）以及对精确验证条件的改动都具有稳健性。


# 问题
%%%
tag := "grind-the-problem"
%%%

下面是 Rustan Leino 对这个问题的原始描述，由 Leonardo de Moura [发布在](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge) Lean Zulip 上：

> 该数据结构是一种表达式，由布尔字面量、变量以及 if-then-else 表达式构成。

  目标是把这类表达式规范化成如下形式：
  a) 没有嵌套 if：if 表达式的条件部分本身不是 if 表达式
  b) 没有常量测试：if 表达式的条件部分不是常量
  c) 没有冗余 if：if 的 then 分支与 else 分支不相同
  d) 每个变量至多求值一次：条件中的自由变量与 then 分支中的自由变量不相交，也与 else 分支中的自由变量不相交。

  需要证明某个规范化函数会产生满足这四个条件的表达式，同时还要证明这个规范化函数保持原表达式的语义不变。

# 形式化陈述
%%%
tag := "grind-the-formal-statement"
%%%

:::leanFirst
为了在 Lean 中形式化这一陈述，我们使用归纳类型 {name}`IfExpr`：

```lean
/--
if 表达式要么是布尔字面量，
要么是带编号的变量，
要么是一个 if-then-else 表达式，
其中每个子表达式也都是 if 表达式。
-/
inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq
```
:::

:::leanFirst
然后定义一些归纳谓词与一个 {name IfExpr.eval}`eval` 函数，以便陈述所需的四个性质：

```lean
namespace IfExpr

/--
若某个 if 表达式包含一个 if-then-else，
并且其中的 “if” 本身又是 if-then-else，
则称该表达式具有“嵌套 if”。
-/
def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

/--
若某个 if 表达式包含一个 if-then-else，
并且其中的 “if” 本身是字面量，
则称该表达式具有“常量 if”。
-/
def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e =>
    i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

/--
若某个 if 表达式包含一个 if-then-else，
且其中的 “then” 与 “else” 子句完全相同，
则称该表达式具有“冗余 if”。
-/
def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf ||
      t.hasRedundantIf || e.hasRedundantIf

/--
if 表达式中出现的所有变量，
按从左到右的顺序列出，
且不去重。
-/
def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

/--
一个用来表达两个列表不相交的辅助函数。
-/
def _root_.List.disjoint {α} [DecidableEq α] :
    List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

/--
如果一个 if 表达式满足：对每个 if-then-else，
“if” 子句中的变量与 “then” 子句中的变量不相交，
并且 “if” 子句中的变量与 “else” 子句中的变量也不相交，
那么这个 if 表达式对每个变量至多求值一次。
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars &&
        i.disjoint && t.disjoint && e.disjoint

/--
如果一个 if 表达式
没有嵌套 if、常量 if 或冗余 if，
并且每个变量至多求值一次，
那么它就是“规范化的”。
-/
def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf &&
    !e.hasRedundantIf && e.disjoint

/--
在某个变量赋值下对 if 表达式求值。
-/
def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr
```
:::

有了这些定义之后，我们就可以陈述这个问题了。挑战在于构造下面这个类型的一个元素（而且还要写得漂亮！）：

```lean
def IfNormalization : Type :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```

# 其他解法
%%%
tag := "grind-other-solutions"
%%%

到这里，不妨先停下来，至少做下面这些事情中的一项：

:::comment
TODO (@david-christiansen)：这里我们放了一个指向 live-lean 的链接和一份外部托管的代码文件。没法保证它们始终同步。:-(
:::

* 试着自己证明它！对于初学者来说，这相当有挑战性！
  你可以在无需任何安装的情况下，直接在 Live Lean 编辑器里[动手试试](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fgist.githubusercontent.com%2Fkim-em%2Ff416b31fe29de8a3f1b2b3a84e0f1793%2Fraw%2F75ca61230b50c126f8658bacd933ecf7bfcaa4b8%2Fgrind_ite.lean)。
* 阅读 Chris Hughes 的[解法](https://github.com/leanprover-community/mathlib4/blob/master/Archive/Examples/IfNormalization/Result.lean)，
  它被收录在 Mathlib Archive 中。
  这个解法很好地利用了 Aesop，但并不理想，因为
  1. 它用一个子类型来定义解法，同时给出构造并证明其性质。
     我们认为从风格上看，最好把这两件事分开。
  2. 即使用了 Aesop 自动化，在能够把证明交给 Aesop 之前，仍然需要大约 15 行手工证明工作。
* 阅读 Wojciech Nawrocki 的[解法](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Rustan's.20challenge/near/398824748)。
  这个版本使用的自动化更少，大约有 300 行证明工作。

# 使用 {tactic}`grind` 的解法
%%%
tag := "grind-the-solution-using-tactic-grind"
%%%

实际上，要解决这个问题并不算太难：
我们只需要一个递归函数，沿途携带一份“已经赋值的变量”记录；
然后每当对某个变量做分支时，就在各个分支中加入新的赋值。
它还需要把那些“条件”位置又出现了 if-then-else 的嵌套 if-then-else 表达式拍平。
（这部分是从 Chris Hughes 的解法中提取出来的，但去掉了子类型。）

下面我们在 `IfExpr` 命名空间里工作。
```lean
namespace IfExpr
```

:::keepEnv

```lean +error (name := failed_to_show_termination)
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)

```

这一定义相当直接，但立刻就会遇到一个问题：

```leanOutput failed_to_show_termination (stopAt := "Could not find a decreasing measure.")
fail to show termination for
  IfExpr.normalize
with errors
failed to infer structural recursion:
Cannot use parameter assign:
  the type HashMap Nat Bool does not have a `.brecOn` recursor
Cannot use parameter #2:
  failed to eliminate recursive application
    normalize assign (a.ite (b.ite t e) (c.ite t e))


Could not find a decreasing measure.
```


这里 Lean 告诉我们，它看不出这个函数一定会终止。
很多时候 Lean 很擅长自行判断这一点，但对于足够复杂的函数，
我们就需要介入并给它一点提示。

在这个例子里，我们可以看出，Lean 感到困难的是如下递归调用：
`ite (ite a b c) t e` 会在 `(ite a (ite b t e) (ite c t e))` 上调用 {lean}`normalize`。
Lean 已经基于自动生成的 {name}`sizeOf` 函数，猜测了一个看似合理的终止度量，
但无法证明由此产生的目标，
本质上是因为 `t` 和 `e` 在递归调用中各自出现了多次。
:::

要处理这类问题，我们几乎总是应该放弃使用自动生成的 `sizeOf` 函数，
转而自行构造终止度量。这里我们使用

```lean
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1
```


这里有很多不同的函数都能用。基本思路是提高“条件”分支的“权重”
（也就是 `2 * normSize i` 中的乘法因子），
这样一来，只要“条件”部分缩小了一些，即使 “then” 和 “else” 分支变大了，整个表达式仍可视为缩小。
我们给这个定义加上了 {attrs}`@[simp]` 标注，这样 Lean 的自动终止性检查器就被允许展开这个定义。

有了这个定义之后，就可以借助 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句通过定义检查：

:::keepEnv
```lean
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize
```

现在该来证明这个函数的一些性质了。
我们直接把想要的所有性质打包在一起：

```lean -keep
theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign :=
  sorry
```

也就是说：
* {lean}`normalize` 的结果按照最初的定义确实是规范化的，
* 如果我们先用某些赋值去规范化一个 if-then-else 表达式，再对剩余变量求值，
  那么得到的结果，与在原始 if-then-else 表达式上使用这两组赋值的复合后再求值得到的结果相同，
* 并且任何出现在赋值中的变量，都不会再出现在规范化后的表达式中。

你也许会觉得，应该把这三个性质分别表述成独立引理，
但事实证明，把它们一次性同时证明会非常方便，因为这样就可以用 {tactic}`fun_induction`
策略，在递归调用处直接假设这些性质都对 {lean}`normalize` 成立，
然后 {tactic}`grind` 就会把所有事实组合起来得到结论：

```lean
-- 我们告诉 `grind` 展开上面定义的这些定义。
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint

theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

{tactic}`fun_induction` 加上 {tactic}`grind` 的组合在这里竟然直接奏效，着实令人惊叹。
我们对此非常兴奋，也希望将来能看到更多这种风格的证明！

高度自动化证明带来的一个美妙结果是：你往往可以在完全不改动证明的前提下，灵活调整命题表述！
例如，上面“任何出现在赋值中的变量都不再出现在规范化后的表达式中”这一断言，
可以有很多不同的表述方式（虽然不能省略！）。
这些变化其实都无关紧要，
而 {tactic}`grind` 既能证明它们，也能使用它们：

这里我们使用 `assign.contains v = false`：
```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) →
          assign.contains v = false := by
  fun_induction normalize with grind
```

这里则使用 `assign[v]? = none`：

```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind
```

事实上，对 `grind` 来说，用 {name}`HashMap` 还是 {name}`TreeMap`
来存储赋值也完全无关紧要，
我们可以直接替换这个实现细节，而完全不用改动证明：

:::


```lean -show
-- 我们必须重复这些标注，因为当前环境已经回滚到了定义 `normalize` 之前。
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint
```
```lean
def normalize (assign : Std.TreeMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize

theorem normalize_spec
    (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

（之所以能够这样做，是因为 {tactic}`grind` 所需的、同时适用于 {name}`HashMap` 和 {name}`TreeMap` 的所有引理，都已经在标准库中加好了标注。）

如果你想亲自试试这段代码，
可以在[这里](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_ite.lean)找到完整文件，
或者干脆直接在 Live Lean 编辑器中[无需安装即可游玩](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover%2Flean4%2Frefs%2Fheads%2Fmaster%2Ftests%2Flean%2Frun%2Fgrind_ite.lean)。

```lean -show
end IfExpr
```
