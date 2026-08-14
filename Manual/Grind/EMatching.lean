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

#doc (Manual) "E-匹配" =>
%%%
file := "E___matching"
tag := "e-matching"
%%%

{deftech (key := "E-matching")}_E-匹配_是一种用基项高效实例化量化定理陈述的过程。
它被广泛用于 SMT 求解器中，而 {tactic}`grind` 也利用它来高效实例化定理。
当它与 {tech (key := "Congruence closure")}[同余闭包] 结合使用时尤其有效，能够让 {tactic}`grind` 自动发现等式与已标注定理的非显然后果。

E-匹配会基于定理索引，把新的事实加入这个比喻意义上的白板。
当白板中出现与索引匹配的项时，E-匹配引擎就会实例化相应定理，而由此得到的项又能供后续的 {tech (key := "Congruence closure")}[同余闭包]、{tech (key := "Constraint propagation")}[约束传播] 与特定理论求解器继续使用。
每一个由 E-匹配加入白板的事实，都称为一个 {deftech (key := "e-matching instance")}_实例_。
为定理添加 E-匹配标注、从而把它们加入索引，是让 {tactic}`grind` 有效利用库内容的关键。

除了用户指定的定理以外，{tactic}`grind` 还会把为 {keywordOf Lean.Parser.Term.match}`match` 表达式自动生成的等式当作 E-匹配定理使用。
在幕后，{tech (key := "Lean elaborator")}[精译器]会生成实现模式匹配的辅助函数，以及描述其行为的等式定理。
将这些等式与 E-匹配配合使用，就能让 {tactic}`grind` 化简这些模式匹配实例。


# 模式
%%%
tag := "e-matching-patterns"
%%%

E-匹配索引是一张由_模式_组成的表。
当某个项与表中的某个模式匹配时，{tactic}`grind` 就会尝试实例化并应用相应定理，从而产生更多事实与等式。
选择合适的模式，是有效使用 {tactic}`grind` 的重要一环：如果模式过于严格，有用的定理就可能无法应用；如果模式过于宽泛，性能则可能下降。


::::example "E-匹配模式"
考虑下面这些函数和定理：
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

```lean -show
variable {x a b : Nat}
```
定理 {lean}`gf` 断言：对所有自然数 {lean}`x`，都有 {lean}`g (f x) = x`。
属性 {attr}`grind =` 告诉 {tactic}`grind` 使用等式左边的 {lean}`g (f x)` 作为 E-匹配启发式实例化时的模式。

这个证明目标并不包含 {lean}`g (f x)` 的实例，但 {tactic}`grind` 仍然能够将其解决：
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```

虽然 {lean}`g a` 并不是模式 {lean}`g (f x)` 的一个实例，但在等式 {lean}`f b = a` 的意义下，它会变成一个实例。
把 {lean}`g a` 中的 {lean}`a` 替换成 {lean}`f b` 后，我们得到项 {lean}`g (f b)`，它就与模式 {lean}`g (f x)` 匹配，对应赋值为 `x := b`。
因此，定理 {lean}`gf` 会以 `x := b` 进行实例化，并断言新的等式 {lean}`g (f b) = b`。
随后，{tactic}`grind` 使用同余闭包推出蕴含的等式 {lean}`g a = g (f b)`，从而完成证明。
::::


{keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 命令可用于手动为定理选择 E-匹配模式。
开启选项 {option}`trace.grind.ematch.instance` 后，{tactic}`grind` 会为其生成的每个定理实例打印一条追踪消息，这在确定 E-匹配模式时会很有帮助。

:::syntax command (title := "E-匹配模式选择")
```grammar
grind_pattern $_ => $_,*
```
将一个定理与一个或多个模式关联起来。
如果在同一个 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 命令中给出了多个模式，那么必须_全部_匹配到项，{tactic}`grind` 才会尝试实例化该定理。

```grammar
grind_pattern $_ => $_,* where $_
```
可选的 {keywordOf Lean.Parser.Command.grind_pattern}`where` 子句给出了一组约束；只有满足这些约束时，{tactic}`grind` 才会尝试实例化该定理。
每个约束都形如 `variable =/= value`，用于阻止在模式变量会被赋成指定值时发生实例化。
这对于避免某些问题项导致的无界或过度实例化很有用。
:::

::::example "选择模式"
{attr}`grind =` 属性会把等式左边用作 {lean}`gf` 的 E-匹配模式：
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

例如，在下面这种情况下，模式 `g (f x)` 就过于严格：
定理 `gf` 不会被实例化，因为目标里甚至根本不包含函数符号 `g`。

在这个例子中，{tactic}`grind` 会失败，因为模式太严格：目标不包含函数符号 {lean}`g`。
```lean +error (name := restrictivePattern)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
```leanOutput restrictivePattern (expandTrace := eqc)
`grind` failed
case grind
b a c : Nat
h₁ : f b = a
h₂ : f c = a
h : ¬b = c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] b = c
  [eqc] Equivalence classes
    [eqc] {a, f b, f c}
```

只用 `f x` 作为模式，就足以让 {tactic}`grind` 自动解决该目标：
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

开启 {option}`trace.grind.ematch.instance` 后，就可以看到 E-匹配找到的等式：
```lean (name := ematchInstanceTrace)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  set_option trace.grind.ematch.instance true in
  grind
```
```leanOutput ematchInstanceTrace
[grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
```

在 E-匹配之后，证明之所以成功，是因为同余闭包会把 `g (f c)` 与 `g (f b)` 判定为相等；这是由于 `f b` 和 `f c` 都等于 `a`。
因此，`b` 与 `c` 必须处于同一个等价类中。

::::

当多个模式被一起指定时，只有它们全部在当前上下文中匹配成功，{tactic}`grind` 才会尝试实例化该定理。
这称为 {deftech (key := "multi-pattern")}_多模式_。
对于传递性规则这类引理，它尤其有用，因为规则适用时往往要求多个前提同时在场。
通过多次调用 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern`，或者使用 {attrs}`@[grind _=_]` 属性，一个定理也可以关联到多个彼此独立的模式。
只要这些独立模式中有_任意一个_匹配成功，该定理就会被实例化。

::::example "多模式"

{lean}`R` 是 {lean}`Int` 上的一个传递二元关系：
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z
```

要利用 {lean}`R` 的传递性，{tactic}`grind` 必须已经能够同时满足两个前提。
这可以通过一个 {tech (key := "multi-pattern")}[多模式] 来表示：
```lean
grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```

```lean -show
variable {x y z a b c d : Int}
```

多模式 `R x y, R y z` 告诉 {tactic}`grind`：只有当上下文中同时存在 {lean}`R x y` 与 {lean}`R y z` 时，才实例化 {lean}`Rtrans`。
在这个例子里，{tactic}`grind` 先由 {lean}`R a b` 与 {lean}`R b c` 应用 {lean}`Rtrans` 推出 {lean}`R a c`，然后再次重复同样的推理，由 {lean}`R a c` 与 {lean}`R c d` 推出 {lean}`R a d`。
::::

::::example "模式约束"
某些定理组合可能导致无界实例化，也就是 E-匹配反复生成越来越长的项。
考虑与 {name}`List.flatMap` 和 {name}`List.reverse` 有关的定理。
如果 {name}`List.flatMap_def`、{name}`List.flatMap_reverse` 与 {name}`List.reverse_flatMap` 都被加上 {attrs}`@[grind =]` 标注，那么一旦 {name}`List.flatMap_reverse` 被实例化，就会发生下面这一连串实例化，不断构造出带有更多 {name}`List.reverse` 组合的函数。
这一点可以用 `#grind_lint` 命令观察到：
```
attribute [local grind =] List.reverse_flatMap

set_option trace.grind.ematch.instance true in
#grind_lint inspect List.flatMap_reverse
```
追踪输出展示了这种无界实例化：
```
[grind.ematch.instance] List.flatMap_def: List.flatMap (List.reverse ∘ f) l = (List.map (List.reverse ∘ f) l).flatten
[grind.ematch.instance] List.flatMap_def: List.flatMap f l.reverse = (List.map f l.reverse).flatten
[grind.ematch.instance] List.flatMap_reverse: List.flatMap f l.reverse = (List.flatMap (List.reverse ∘ f) l).reverse
[grind.ematch.instance] List.reverse_flatMap: (List.flatMap (List.reverse ∘ f) l).reverse =
  List.flatMap (List.reverse ∘ List.reverse ∘ f) l.reverse
[grind.ematch.instance] List.flatMap_def: List.flatMap (List.reverse ∘ List.reverse ∘ f) l.reverse =
  (List.map (List.reverse ∘ List.reverse ∘ f) l.reverse).flatten
```

这种模式会无限继续下去，每次迭代都会在组合中再添一个 {name}`List.reverse`。
{keywordOf Lean.Parser.Command.grind_pattern}`where` 子句可以通过排除有问题的实例化来阻止这种情况：
```
grind_pattern reverse_flatMap => (l.flatMap f).reverse where
  f =/= List.reverse ∘ _
```
这会指示 {tactic}`grind` 使用模式 `(l.flatMap f).reverse`，但只在 `f` 不是与 {name}`List.reverse` 的复合时才使用，从而阻止那条无界实例化链。

你可以用 `#grind_lint check` 查找有问题的模式，也可以用 `#grind_lint check in List` 或 `#grind_lint check in module Std.Data` 在特定命名空间或模块中检查。
::::

{attr}`grind` 属性会用启发式方法自动生成 E-匹配模式或多模式，而不必用 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` 显式指定模式。
它包含若干变体，用来选择不同的启发式。
{attr}`grind?` 属性会显示一条信息消息，指出所选模式——这对调试非常有帮助！

模式是定理陈述的子表达式。
如果某个子表达式的头部是可索引常量，那么它就是 {deftech (key := "indexable")}_可索引的_；如果它能固定定理某个参数的取值，就称它 {deftech (key := "cover")}_覆盖_ 了该参数。
可索引常量指除 {name}`Eq`、{name}`HEq`、{name}`Iff`、{name}`And`、{name}`Or` 与 {name}`Not` 之外的所有常量。
一个模式或多模式所覆盖参数的集合，称为它的 {deftech (key := "coverage")}_覆盖度_。
有些常量的优先级低于其他常量；特别是算术运算符 {name}`HAdd.hAdd`、{name}`HSub.hSub`、{name}`HMul.hMul`、{name}`Dvd.dvd`、{name}`HDiv.hDiv` 与 {name}`HMod.hMod` 的优先级都较低。
如果不存在一个更小的可索引子表达式，并且它的头常量优先级至少同样高，那么该可索引子表达式就是 {deftech (key := "minimal")}_极小的_。

:::syntax attr (title := "Grind 模式")
当把 {attr}`grind` 属性加到某个定义上时，每当 `grind` 遇到该定义，就会把它展开为其主体。
在使用模块系统时，如果该定义的主体不可见（例如没有通过 {attrs}`@[expose]` 暴露），那么 {attr}`grind` 属性会被忽略。

```grammar
grind $[$_:grindMod]?
```
{attr}`grind` 属性会根据给定修饰符所决定的策略，自动为定理生成 E-匹配模式。
如果没有提供修饰符，那么 {attr}`grind` 会建议合适的修饰符，并显示相应生成的模式。

```grammar
grind! $[$_:grindMod]?
```
{attr}`grind!` 属性会根据给定修饰符所决定的策略，自动为定理生成 E-匹配模式。
此外，它还强制要求所选模式必须是极小的可索引子表达式。

```grammar
grind? $[$_:grindMod]?
```

{attr}`grind?` 会显示所生成的模式。

```grammar
grind!? $[$_:grindMod]?
```
{attr}`grind!?` 属性等价于 {attr}`grind!`，不同之处在于它会显示生成结果，便于检查。


在没有任何修饰符时，{attrs}`@[grind]` 会先遍历结论，再从左到右遍历各个假设；每当某个模式能扩大覆盖度时，就将其加入，并在所有参数都被覆盖时停止。
这一默认策略也可以通过 {keywordOf Lean.Parser.Attr.grindDef}`.` 修饰符显式请求。
除了使用默认策略之外，该属性还会检查哪些其他策略也适用，并显示所有由此得到的模式。
:::

```lean -keep -show
-- 如果新增了 grind 修饰符，这个测试就会开始失败。这样可以确保它们都
-- 已被文档记录（或者至少已经明确决定某一个不写入文档）。
open Lean Parser Attr
open Lean Elab Command

deriving instance Repr for ParserDescr

def getName : ParserDescr → CommandElabM String
  | .nodeWithAntiquot name .. => pure name
  | other => throwError m!"Expected a {.ofConstName ``nodeWithAntiquot}, got {repr other}"

def getOrElse (descr : ParserDescr) : CommandElabM (Array ParserDescr) := do
  match descr with
  | .binary `orelse x y => return (← getOrElse x) ++ (← getOrElse y)
  | other => return #[other]

def getGrindAlts (descr : ParserDescr) : CommandElabM (Array String) := do
  if let .nodeWithAntiquot "grindMod" ``grindMod d' := descr then
    let cases ← getOrElse d'
    return (← cases.mapM getName).qsort
  else throwError "Expected a {.ofConstName ``nodeWithAntiquot}, got {repr descr}"

/--
info: `grindMod` can be these:
grindBwd
grindCases
grindCasesEager
grindDef
grindEq
grindEqBoth
grindEqBwd
grindEqRhs
grindExt
grindFunCC
grindFwd
grindGen
grindHom
grindHomPred
grindInj
grindIntro
grindLR
grindNorm
grindRL
grindSym
grindUnfold
grindUsr
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let allMods ← getGrindAlts grindMod
  IO.println "`grindMod` can be these:"
  for gmod in allMods do
    IO.println gmod

```

:::syntax Lean.Parser.Attr.grindMod (title := "默认模式")
```grammar
.
```
```grammar
·
```
{zhincludeDocstring Lean.Parser.Attr.grindDef ZhDoc.Parser.Attr.grindDef}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "等式重写")
```grammar
=
```
{zhincludeDocstring Lean.Parser.Attr.grindEq ZhDoc.Parser.Attr.grindEq}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "反向等式重写")
```grammar
=_
```
{zhincludeDocstring Lean.Parser.Attr.grindEqRhs ZhDoc.Parser.Attr.grindEqRhs}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "双向等式重写")
```grammar
_=_
```
{zhincludeDocstring Lean.Parser.Attr.grindEqBoth ZhDoc.Parser.Attr.grindEqBoth}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "前向推理")
```grammar
→
```
{zhincludeDocstring Lean.Parser.Attr.grindFwd ZhDoc.Parser.Attr.grindFwd}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "后向推理")
```grammar
←
```
{zhincludeDocstring Lean.Parser.Attr.grindBwd ZhDoc.Parser.Attr.grindBwd}
:::

检查 {attrs}`@[grind]` 属性生成的模式非常重要，以确保它们匹配到的是引理中正确的部分。
如果模式过于严格，那么在它本应相关的情形下，引理也不会被应用，从而降低自动化程度。
如果模式过于宽泛，那么引理会在许多无助于证明的场景中被尝试，性能因此受损。

另外，还有三个较少使用的引理修饰符：

:::syntax Lean.Parser.Attr.grindMod (title := "从左到右遍历")
```grammar
=>
```
```grammar
⇒
```
{zhincludeDocstring Lean.Parser.Attr.grindLR ZhDoc.Parser.Attr.grindLR}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "从右到左遍历")
```grammar
<=
```
```grammar
⇐
```
{zhincludeDocstring Lean.Parser.Attr.grindRL ZhDoc.Parser.Attr.grindRL}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "等式上的后向推理")
```grammar
←=
```
{zhincludeDocstring Lean.Parser.Attr.grindEqBwd ZhDoc.Parser.Attr.grindEqBwd}
:::

:::example "`@[grind ←=]` 属性"
```lean -show
variable {α} {a b : α} [Inv α]
```
当尝试证明 {lean}`a⁻¹ = b` 时，由于存在 {attrs}`@[grind ←=]` 标注，{tactic}`grind` 会使用 {name}`inv_eq`。
```lean
@[grind ←=]
theorem inv_eq [One α] [Mul α] [Inv α] {a b : α}
    (w : a * b = 1) : a⁻¹ = b :=
  sorry
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "函数值的同余闭包")
```grammar
funCC
```
{zhincludeDocstring Lean.Parser.Attr.grindFunCC ZhDoc.Parser.Attr.grindFunCC}
:::


还有一些额外修饰符可用于把其他类型的引理加入索引。
这包括外延性定理、函数的单射性定理，以及一个将归纳定义谓词的所有构造子快捷加入索引的方式。

:::syntax Lean.Parser.Attr.grindMod (title := "外延性")
```grammar
ext
```
{zhincludeDocstring Lean.Parser.Attr.grindExt ZhDoc.Parser.Attr.grindExt}

此外，给某个结构体加上 {attrs}`@[grind ext]` 还会注册它的外延性定理。
:::


::::example "`@[grind ext]` 属性"

{lean}`Point` 是一个带有两个字段的结构体：
```lean
structure Point where
  x : Int
  y : Int
```
默认情况下，{tactic}`grind` 可以解决下面这样的目标，因为定义相等对积类型包含 {tech (key := "η-equivalence")}[η-等价]：
```lean
example (p : Point) : p = ⟨p.x, p.y⟩ := by grind
```
不过，它无法解决下面这种需要诉诸命题相等的目标：
```lean +error (name := noExt)
example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by grind
```
```leanOutput noExt
`grind` failed
case grind
p : Point
a : Int
h : a = p.x
h_1 : ¬p = { x := a, y := p.y }
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
```


在证明诸如“把点的字段交换两次等于恒等”的定理时，就可能遇到这种目标：
```lean
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩
```
```lean +error (name := noExt')
theorem swap_swap_eq_id : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
```leanOutput noExt'
`grind` failed
case grind
h : ¬((fun p => { x := p.y, y := p.x }) ∘ fun p => { x := p.y, y := p.x }) = id
w : Point
h_1 : ¬{ x := w.x, y := w.y } = id w
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns

[grind] Diagnostics
```
给 {name}`Point` 添加 {attrs}`@[grind ext]` 属性后，{tactic}`grind` 既能解决最初的例子，也能证明下面这个定理：
```lean
attribute [grind ext] Point

example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by
  grind

theorem swap_swap_eq_id' : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
::::

:::syntax Lean.Parser.Attr.grindMod (title := "单射性")
```grammar
inj
```
{zhincludeDocstring Lean.Parser.Attr.grindInj ZhDoc.Parser.Attr.grindInj}
:::

:::example "单射性模式"
函数 {name}`double` 会把它的参数翻倍：
```lean
def double (x : Nat) : Nat := x + x
```
默认情况下，{tactic}`grind` 无法证明下面这个定理：
```lean +error
theorem A {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
不过，{name}`double` 是单射的，而这一事实可以用 {attr}`grind inj` 属性为 {tactic}`grind` 注册：
```lean
@[grind inj]
theorem double_inj : Function.Injective double := by
  simp only [double, Function.Injective]
  grind
```
这个单射性引理就足以证明该定理：
```lean
theorem B {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "构造子模式")
```grammar
intro
```
{zhincludeDocstring Lean.Parser.Attr.grindIntro ZhDoc.Parser.Attr.grindIntro}
:::

:::example "构造子的模式"
谓词 {name}`Decreasing` 表示一个整数列表中的每个值都小于它前面的那个值，而函数 {name}`decreasing` 会检查这一性质，并返回一个 {name}`Bool`。
```lean
inductive Decreasing : List Int → Prop
  | nil : Decreasing []
  | singleton : Decreasing [x]
  | cons : Decreasing (x :: xs) → y > x → Decreasing (y :: x :: xs)

def decreasing : List Int → Bool
  | [] | [_] => true
  | y :: x :: xs => y > x && decreasing (x :: xs)
```

如果且仅如果 {name}`Decreasing` 对其参数成立时该函数返回 {name}`true`，那么这个函数就是正确的。
尝试用 {tactic}`fun_induction` 与 {tactic}`grind` 的组合来证明这一点，会立刻失败，三个分支一个也证不出来：
```lean +error (name := decreasingCorrect1)
def decreasingCorrect : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
h : True = ¬Decreasing []
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
head : Int
h : True = ¬Decreasing [head]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind.1
y x : Int
xs : List Int
ih1 : (decreasing (x :: xs) = true) = Decreasing (x :: xs)
h : (-1 * y + x + 1 ≤ 0 ∧ decreasing (x :: xs) = true) = ¬Decreasing (y :: x :: xs)
left : -1 * y + x + 1 ≤ 0
left_1 : decreasing (x :: xs) = true
right_1 : ¬Decreasing (y :: x :: xs)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
```
给 {name}`Decreasing` 添加 {attr}`grind intro` 属性后，会为它的三个构造子分别加入 E-匹配模式。这样一来，{tactic}`grind` 就能证明前两个目标，而最后一个目标只需再对某个假设做一次分类讨论即可：
```lean
attribute [grind intro] Decreasing

def decreasingCorrect' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> try grind
  case case3 y x xs ih =>
    apply propext
    constructor
    . grind
    . intro
      | .cons hDec hLt =>
        grind
```
给 {name}`Decreasing` 添加 {attr}`grind cases` 后，这个分类讨论也会自动完成，从而得到一个完全自动化的证明：
```lean
attribute [grind cases] Decreasing

def decreasingCorrect'' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "预处理时展开")
```grammar
unfold
```
{zhincludeDocstring Lean.Parser.Attr.grindUnfold ZhDoc.Parser.Attr.grindUnfold}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "规范化规则")
```grammar
norm
```
{zhincludeDocstring Lean.Parser.Attr.grindNorm ZhDoc.Parser.Attr.grindNorm}
:::

{tactic}`grind` 策略可以处理某些求解基础设施并不丰富的源代数（例如位向量），做法是把它“嵌入”到另一个求解基础设施更丰富的代数中（例如自然数或整数）。
同态规则描述了这种从源到目标的嵌入，以及该嵌入如何与其他运算交换（例如在位向量情形下的加法或乘法）。
同态谓词则给出了关于该嵌入的更多事实，供 {tactic}`grind` 使用（例如长度为 $`n` 的位向量对应于一个小于 $`2^n` 的自然数）。

:::syntax Lean.Parser.Attr.grindMod (title := "同态规则")
```grammar
hom
```
{zhincludeDocstring Lean.Parser.Attr.grindHom ZhDoc.Parser.Attr.grindHom}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "同态谓词")
```grammar
hom_pred
```
{zhincludeDocstring Lean.Parser.Attr.grindHomPred ZhDoc.Parser.Attr.grindHomPred}
:::

{TODO}[Grind 的同态基础设施值得补一个示例]

{TODO}[为 `grind` 模式中的 `gen` 修饰符编写文档]

# 检查模式
%%%
tag := "grind-inspecting-patterns"
%%%

{attr}`grind?` 属性是 {attr}`grind` 属性的一个变体，它还会额外显示所生成的模式或 {tech (key := "multi-pattern")}[多模式]。
模式与多模式都会显示为子表达式列表，其中每个子表达式都是一个模式；普通模式则显示为单元素列表。
在这些显示出来的模式里，已定义常量的名字会原样打印。
当定理的参数出现在模式中时，它们会用数字而不是名字来显示。
具体来说，这些参数按从右到左的顺序编号，从 0 开始；这种表示法称为 {deftech (key := "de Bruijn indices")}_de Bruijn 索引_。

:::example "模式检查示例" (open := true)
要想让 {tactic}`grind` 使用下面这个“整除具有传递性”的证明，就需要为它提供 E-匹配模式：
```lean
theorem div_trans {n k j : Nat} : n ∣ k → k ∣ j → n ∣ j := by
  intro ⟨d₁, p₁⟩ ⟨d₂, p₂⟩
  exact ⟨d₁ * d₂, by rw [p₂, p₁, Nat.mul_assoc]⟩
```
正确的属性是 {attrs}`@[grind →]`，因为每个前提都应该对应一个模式。
使用 {attrs}`@[grind? →]` 可以看到实际生成了哪些模式：
```lean (name := grindHuh)
attribute [grind? →] div_trans
```
一共有两个：
```leanOutput grindHuh
div_trans: [@Dvd.dvd `[Nat] `[Nat.instDvd] #4 #3, @Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2]
```
参数按从右到左编号，因此 `#0` 是假设 `k ∣ j`，而 `#4` 是 `n`。
因此，这两个模式分别对应项 `n ∣ k` 与 `k ∣ j`。
:::

从假设和结论的子表达式中选择模式的规则相当微妙。
:::TODO
补充更多说明
:::

:::example "前向模式生成" (open := true)
```lean
axiom p : Nat → Nat
axiom q : Nat → Nat
```

```lean (name := h1)
@[grind!? →] theorem h₁ (w : p (q x) = 7) : p (x + 1) = q x := sorry
```
```leanOutput h1
h₁: [q #1]
```
模式是 `q x`。
从右往左数，参数 `#0` 是前提 `w`，参数 `#1` 是隐式参数 `x`。

为什么 `@[grind! →]` 会选择 `q #1` 呢？
属性 `@[grind! →]` 会通过从左到右遍历各个假设（也就是类型为命题的参数）来寻找模式。
在这里，只有一个假设：`p (q x) = 7`。
前面描述的启发式规则是：{attr}`grind!` 会寻找一个极小的 {tech (key := "indexable")}[可索引] 子表达式，它能够 {tech (key := "cover")}[覆盖] 某个此前尚未覆盖的参数。
这里只有一个尚未覆盖的参数，也就是 `x`。
整个假设 `p (q x) = 7` 不能用，因为 {tactic}`grind` 不会对等式建立索引。
右边的 `7` 也没有帮助，因为它并不能确定 `x` 的值。
`p (q x)` 也不合适，因为它并不极小：其中包含 `q x`，而 `q x` 本身就是可索引的（其头部是常量 `q`），并且它也能够确定 `x` 的值。
表达式 `q x` 本身则是极小的，因为 `x` 并不可索引。
因此，`q x` 被选为了模式。
:::

:::example "后向模式生成" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

在这个例子中，{keywordOf Lean.Parser.Attr.grindMod}`←` 修饰符表示应当在结论中寻找模式：
```lean (name := h2)
set_option trace.grind.debug.ematch.pattern true in
@[grind? ←] theorem h₂ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
这里使用的是等式左边，因为 {name}`Eq` 不可索引，而 {name}`HAdd.hAdd` 的优先级又低于 {lean}`p`。
```leanOutput h2
h₂: [p (#1 + 1)]
```
:::

:::example "双向等式模式生成" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在这个例子中，会从等式结论中生成两个彼此独立的 E-匹配模式。
其中一个匹配左边，另一个匹配右边。
```lean (name := h3)
@[grind? _=_] theorem h₃ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h3
h₃: [q #1]
```

这里使用的是整个等式左边，而不是仅仅使用 `x + 1`，因为 {name}`HAdd.hAdd` 的优先级低于 {lean}`p`。
```leanOutput h3
h₃: [p (#1 + 1)]
```
:::

:::example "来自结论与假设的模式" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

在不加任何修饰符时，{attrs}`@[grind]` 会先检查结论，再检查前提，从而生成一个多模式：
```lean (name := h4)
@[grind? .] theorem h₄ (w : p x = q y) : p (x + 2) = 7 := sorry
```
这里，参数 `x` 是 `#2`，`y` 是 `#1`，而 `w` 是 `#0`。
生成得到的多模式包含等式左边，因为它是结论中唯一一个既 {tech (key := "minimal")}[极小] 又 {tech (key := "indexable")}[可索引]，并且能够覆盖某个参数（即 `x`）的子表达式。
它还包含 `q y`，因为这是前提 `w` 中唯一一个能够覆盖额外参数（即 `y`）的极小可索引子表达式。
```leanOutput h4
h₄: [p (#2 + 2), q #1]
```
:::

:::example "失败的后向模式生成" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在这个例子中，模式生成会失败，因为定理的结论没有提到参数 `y`。
```lean (name := h5) +error
@[grind? ←] theorem h₅ (w : p x = q y) : p (x + 2) = 7 := sorry
```
```leanOutput h5
`@[grind ←] theorem h₅` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
```
:::

:::example "从左到右生成" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在这个例子中，模式是通过先从左到右遍历前提、再遍历结论而生成的：
```lean (name := h6)
@[grind? =>] theorem h₆
    (_ : q (y + 2) = q y)
    (_ : q (y + 1) = q y) :
    p (x + 2) = 7 :=
  sorry
```
在这些模式里，`y` 是参数 `#3`，`x` 是参数 `#2`，因为 {tech (key := "automatic implicit parameters")}[自动隐式参数] 是按从左到右的顺序插入的，而在定理陈述中 `y` 出现在 `x` 之前。
两个前提分别是参数 `#1` 和 `#0`。
在生成的多模式中，`y` 由第一个前提的某个子表达式覆盖，而 `x` 由结论中的某个子表达式覆盖：
```leanOutput h6
h₆: [q (#3 + 2), p (#2 + 2)]
```
:::


# E-匹配的资源限制
%%%
tag := "grind-limits"
%%%

E-匹配可能生成无界数量的定理 {tech (key := "e-matching instance")}[实例]。
出于效率和终止性的双重考虑，{tactic}`grind` 通过两种机制限制 E-匹配的运行次数：

: 代数层级

  每个项都会被赋予一个 {deftech (key := "generation")}_generation_，而由 E-匹配生成的项，其 generation 会比所有用于实例化该定理的项中的最大 generation 大 1。
  E-匹配只会考虑 generation 低于某个可配置阈值的项。
  {tactic}`grind` 的 `gen` 选项控制这个 generation 阈值。

: 轮数限制

  每次调用 E-匹配引擎都称为一 {deftech (key := "round")}_轮_。
  E-匹配只会执行有限轮。
  {tactic}`grind` 的 `ematch` 选项控制这个轮数上限。


:::example "实例过多" (open := true)

E-匹配可能生成过多的定理 {tech (key := "e-matching instance")}[实例]。
有些模式甚至会生成无界数量的实例。

在这个例子中，{name}`s_eq` 以模式 `s x` 被加入索引：
```lean (name := ematchUnboundedPat)
def s (x : Nat) := 0

@[grind? =] theorem s_eq (x : Nat) : s x = s (x + 1) :=
  rfl
```
```leanOutput ematchUnboundedPat
s_eq: [s #0]
```

尝试使用这个定理会生成许多把 {lean}`s` 应用于具体值的事实。
特别地，在这五轮中的每一轮里，{lean}`s_eq` 都会用一个新的 {lean}`Nat` 来实例化。
首先，{tactic}`grind` 用 `x := 0` 实例化 {lean}`s_eq`，从而生成项 {lean}`s 1`。
这个项又会匹配模式 `s x`，于是进一步以 `x := 1` 实例化 {lean}`s_eq`，生成项 {lean}`s 2`，
如此继续，直到达到轮数上限。
```lean +error (name := ematchUnbounded)
example : s 0 > 0 := by
  grind
```

```leanOutput ematchUnbounded (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

把轮数上限提高到 20 后，E-匹配会因为默认的 generation 上限 8 而终止：
```lean +error (name := ematchUnbounded2)
example : s 0 > 0 := by
  grind (ematch := 20)
```
```leanOutput ematchUnbounded2 (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
    [prop] s 5 = s 6
    [prop] s 6 = s 7
    [prop] s 7 = s 8
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`

[grind] Diagnostics
```
:::

:::example "提高 E-匹配限制"


{lean}`iota` 会返回所有严格小于其参数的数字所构成的列表，而定理 {lean}`iota_succ` 描述了它在 {lean}`Nat.succ` 上的行为：
```lean
def iota : Nat → List Nat
  | 0 => []
  | n + 1 => n :: iota n

@[grind =] theorem iota_succ : iota (n + 1) = n :: iota n :=
  rfl
```

事实 {lean}`(iota 20).length > 10` 可以通过反复实例化 {lean}`iota_succ` 与 {lean}`List.length_cons` 来证明。
然而，{tactic}`grind` 默认并不会成功：
```lean +error (name := biggerGrindLimits)
example : (iota 20).length > 10 := by
  grind
```
```leanOutput biggerGrindLimits (expandTrace := limits) (expandTrace := facts)
`grind` failed
case grind
h : (iota 20).length ≤ 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] (iota 20).length ≤ 10
    [prop] iota 20 = 19 :: iota 19
    [prop] iota 19 = 18 :: iota 18
    [prop] (19 :: iota 19).length = (iota 19).length + 1
    [prop] iota 18 = 17 :: iota 17
    [prop] (18 :: iota 18).length = (iota 18).length + 1
    [prop] iota 17 = 16 :: iota 16
    [prop] (17 :: iota 17).length = (iota 17).length + 1
    [prop] iota 16 = 15 :: iota 15
    [prop] (16 :: iota 16).length = (iota 16).length + 1
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

由于 E-匹配轮数受限，这条实例化链没有走完。
提高这些限制后，{tactic}`grind` 就可以成功：

```lean
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```

当选项 {option}`diagnostics` 设为 {lean}`true` 时，{tactic}`grind` 会显示它为每个定理生成了多少实例。
这有助于找出那些由于模式设计而触发过多实例的定理。
在这里，诊断信息显示 {name}`iota_succ` 被实例化了 12 次：
```lean (name := grindDiagnostics)
set_option diagnostics true in
set_option diagnostics.threshold 10 in
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```
```leanOutput grindDiagnostics (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] iota_succ ↦ 12
    [thm] List.length_cons ↦ 11
  [app] Applications
  [grind] Simplifier
    [simp] used theorems (max: 15, num: 2):
    [simp] tried theorems (max: 46, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```
:::

默认情况下，{tactic}`grind` 会把为 {keywordOf Lean.Parser.Term.match}`match` 表达式自动生成的等式当作 E-匹配定理使用。
这可以通过把 `matchEqs` 标志设为 {lean}`false` 来禁用。

:::example "E-匹配与模式匹配"

打开诊断信息后可以看到，{tactic}`grind` 在 E-匹配期间使用了辅助匹配函数的某一条等式：
```lean (name := gt1diag)
theorem gt1 (x y : Nat) :
    x = y + 1 →
    0 < match x with
        | 0 => 0
        | _ + 1 => 1 := by
  set_option diagnostics true in
  grind
```
```leanOutput gt1diag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gt1.match_1.congr_eq_2 ↦ 1
  [app] Applications
```
这个定理的类型如下：
```lean (name := gt1matchtype)
#check gt1.match_1.congr_eq_2
```
```leanOutput gt1matchtype
gt1.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0)
  (h_2 : (n : Nat) → motive n.succ) (n✝ : Nat) (heq_1 : x✝ = n✝.succ) :
  (match x✝ with
    | 0 => h_1 ()
    | n.succ => h_2 n) ≍
    h_2 n✝
```

禁用匹配器函数等式后，证明就会失败：

```lean +error (name := noMatchEqs)
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind -matchEqs
```
```leanOutput noMatchEqs
`grind` failed
case grind.2
x y : Nat
h : x = y + 1
h_1 : (match x with
  | 0 => 0
  | n.succ => 1) =
  0
n : Nat
h_2 : x = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
  [ring] Rings

[grind] Diagnostics
```
:::

{zhOptionDocs trace.grind.ematch.instance ZhDoc.Option.trace.grind.ematch.instance}

:::comment
待补
* 反模式
* 局部属性与全局属性
* `gen` 修饰符？
:::
