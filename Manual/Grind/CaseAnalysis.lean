/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Grind


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "情形分析" =>
%%%
tag := "grind-split"
%%%

除同余闭包和约束传播外，{tactic}`grind` 还会进行情形分析。
进行情形分析时，{tactic}`grind` 会考虑一个项所有可能的构造方式，或某个特定项的每个可能取值，其方式类似于 {tactic}`cases` 和 {tactic}`split` 策略。
这种情形分析并非穷举式的：{tactic}`grind` 只会在配置的深度上限内递归拆分情形，并由配置选项和标注控制哪些项可作为拆分候选。


# 选择启发式方法

{tactic}`grind` 综合以下三类信号来决定要拆分哪个子项：

: 结构标志

  以下配置标志决定 {tactic}`grind` 是否进行特定的情形拆分：

  : `splitIte`（默认 {lean}`true`）

    拆分每个 {keywordOf Lean.Parser.Term.ite}`if` 项，就像使用 {tactic}`split` 策略一样。

  : `splitMatch`（默认 {lean}`true`）

    拆分每个 {keywordOf Lean.Parser.Term.match}`match` 项，就像使用 {tactic}`split` 策略一样。

  :  `splitImp`（默认 {lean}`false`）

    :::leanSection
    ```lean -show
    variable {A : Prop} {B : Sort u}
    ```
    对于形如 {lean}`A → B` 且前件 {lean}`A` 是*命题*的假设，通过考虑 {lean}`A` 的所有可能情况进行拆分。
    算术前件会受到特殊处理：如果 {lean}`A` 是算术文字（即由 `≤`、`=`、`¬`、{lean}`Dvd` 等运算符构成的命题），那么_即使 `splitImp := false`_，{tactic}`grind` 也会拆分它，以便整数求解器传播事实。
    :::

: 全局限制

  {tactic}`grind` 的 `splits := n` 选项限制搜索树的深度。
  一旦某个分支进行了 `n` 次拆分，{tactic}`grind` 就不再继续拆分该分支；如果无法关闭该分支，它会报告已达到拆分阈值。

: 手动标注

  可以用 {attr}`grind cases` 属性标记归纳谓词或结构。
  {tactic}`grind` 会将该谓词的每个实例视为拆分候选。


:::syntax attr (title := "情形分析")
```grammar
grind cases
```
{zhincludeDocstring Lean.Parser.Attr.grindCases ZhDoc.Parser.Attr.grindCases}
:::

:::syntax attr (title := "及早情形分析")
```grammar
grind cases eager
```
{zhincludeDocstring Lean.Parser.Attr.grindCasesEager ZhDoc.Parser.Attr.grindCasesEager}
:::


:::example "拆分条件表达式"
在此示例中，{tactic}`grind` 通过考虑条件表达式的两种情况来证明定理：
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind
```

禁用 `splitIte` 会导致证明失败：
```lean +error (name := noSplitIte)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind -splitIte
```
具体而言，在发现条件表达式等于 {lean}`0` 后，它无法继续推进：
```leanOutput noSplitIte (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
```

禁止所有情形拆分会因同样的原因导致证明失败：
```lean +error (name := noSplitsAtAll)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 0)
```
```leanOutput noSplitsAtAll (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
```

只允许一次拆分便已足够：
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 1)
```
:::

:::example "拆分模式匹配"
在此示例中，禁用对模式匹配的情形拆分会导致 {tactic}`grind` 失败：
```lean +error (name := noSplitMatch)
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind -splitMatch
```
```leanOutput noSplitMatch (expandTrace := eqc)
`grind` failed
case grind
y x : Nat
h : y =
  match x with
  | 0 => 1
  | x => 2
h_1 : y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] (x = 0 → False) →
          (match x with
            | 0 => 1
            | x => 2) =
            2
  [eqc] Equivalence classes
    [eqc] {y, 0}
      [eqc] {match x with
          | 0 => 1
          | x => 2}
    [eqc] {x = 0 → False, (fun x_0 => x_0 = 0 → False) x, x = 0 → False}
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```
启用该选项后证明成功：
```lean
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind
```
:::

:::example "拆分谓词"
{lean}`Not30` 以一种略显冗长的方式表述一个数不等于 {lean}`30`：
```lean
inductive Not30 : Nat → Prop where
  | gt : x > 30 → Not30 x
  | lt : x < 30 → Not30 x
```

默认情况下，{tactic}`grind` 无法证明 {lean}`Not30` 确实蕴含该数不等于 {lean}`30`：
```lean +error (name := not30fail)
example : Not30 n → n ≠ 30 := by grind
```
这是因为 {tactic}`grind` 没有考虑 {lean}`Not30` 的两种情形：
```leanOutput not30fail (expandTrace := eqc)
`grind` failed
case grind
n : Nat
h : Not30 n
h_1 : n = 30
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] Not30 n
  [eqc] Equivalence classes
    [eqc] {n, 30}
  [cutsat] Assignment satisfying linear constraints
```

为 {lean}`Not30` 添加 {attr}`grind cases` 属性后，证明便能成功：
```lean
attribute [grind cases] Not30

example : Not30 n → n ≠ 30 := by grind
```

类似地，{lean}`Even` 上的 {attr}`grind cases` 属性允许 {tactic}`grind` 进行情形拆分：
```lean (name := blah)
@[grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n + 2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  grind

set_option trace.grind.split true in
example (h : Even (n + 2)) : Even n := by
  grind
```

:::

# 性能

情形分析功能强大，但计算代价高昂：每增加一层情形拆分，搜索空间都会成倍增长。
因此务必谨慎，避免不必要的拆分。
具体而言：
* *仅当*目标确实需要更深的分支时才增大 `splits`；每多一层都会成倍扩大搜索空间。
* 当大型模式匹配定义使搜索树急剧膨胀时，禁用 `splitMatch`；可设置 {option}`trace.grind.split` 来观察这种情况。
* 标志可以组合使用，例如 `by grind -splitMatch (splits := 10) +splitImp`。
* {attr}`grind cases` 属性是{ref "scoped-attributes"}_有作用域的_。
  修饰符 {keywordOf Lean.Parser.Term.attrKind}`local` 和 {keywordOf Lean.Parser.Term.attrKind}`scoped` 可将额外拆分限制在某个节或命名空间内。

{zhOptionDocs trace.grind.split ZhDoc.Option.trace.grind.split}
