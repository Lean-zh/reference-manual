/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G2
import Manual.Papers


open Manual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "基本命题" =>
%%%
tag := "basic-props"
%%%

除了蕴含和全称量词外，逻辑连接词和量词都在 {lean}`Prop` 宇宙中实现为 {tech}[归纳类型]。
从某种意义上说，本章介绍的连接词并不特殊——任何用户都可以实现它们。
不过，标准库和内置证明自动化工具广泛使用了这些基本连接词。



# 真与假
%%%
tag := "true-false"
%%%

从根本上说，Lean 中只有两个命题：{lean}`True` 和 {lean}`False`。
命题外延公理（{name}`propext`）允许将逻辑等价的命题视为相等；每个真命题都与 {lean}`True` 逻辑等价。
同样，每个假命题都与 {lean}`False` 逻辑等价。

{lean}`True` 是一个归纳定义的命题，只有一个不接受参数的构造器。
证明 {lean}`True` 总是可能的。
另一方面，{lean}`False` 是一个没有构造器的归纳定义命题。
证明它需要在当前上下文中找到矛盾。

{lean}`True` 和 {lean}`False` 都是 {ref "subsingleton-elimination"}[至多单元素类型]；这意味着它们可用于计算非命题类型的元素。
对于 {lean}`True`，这相当于忽略证明，因为证明并不携带信息。
对于 {lean}`False`，这表示当前代码不可达，因此无需完成。

{zhdocstring True Manual.ZhDocString.Ch19Ch20.G2.c159}

{zhdocstring False Manual.ZhDocString.Ch19Ch20.G2.c160}

{zhdocstring False.elim Manual.ZhDocString.Ch19Ch20.G2.c161}

:::example "死代码与至多单元素消去"


{lean}`f` 的定义中的第四个分支不可达，因此无需提供具体的 {lean}`String` 值：
```lean
def f (n : Nat) : String :=
  if h1 : n < 11 then
    "Small"
  else if h2 : n > 13 then
    "Large"
  else if h3 : n % 2 = 1 then
    "Odd"
  else if h4 : n ≠ 12 then
    False.elim (by omega)
  else "Twelve"
```
在此例中，{name}`False.elim` 向 Lean 表明当前局部上下文不一致：证明 {name}`False` 就足以放弃该分支。

类似地，{name}`g` 的定义看起来可能不会终止。
然而，递归调用位于程序的一条不可达路径上。
用于生成终止性证明的自动化能够检测出局部假设之间的矛盾。
```lean
def g (n : Nat) : String :=
  if n < 11 then
    "Small"
  else if n > 13 then
    "Large"
  else if n % 2 = 1 then
    "Odd"
  else if n ≠ 12 then
    g (n + 1)
  else "Twelve"
termination_by n
```
:::

# 逻辑连接词

%%%
tag := "Lean-__________________--Basic-Propositions--Logical-Connectives"
%%%
合取实现为归纳定义的命题 {name}`And`。
构造器 {name}`And.intro` 表示合取的引入规则：要证明合取，只需分别证明两个合取项。
类似地，{name}`And.elim` 表示消去规则：给定合取的证明，以及一个假设两个合取项成立的其他命题的证明，就可以证明该命题。
由于 {name}`And` 是 {tech}[至多单元素类型]，{name}`And.elim` 也可参与数据计算。
但它不应与 {name}`PProd` 混淆：使用选择公理等不可计算的推理原则定义数据（包括 {lean}`Prod`）会使 Lean 无法编译和运行所得程序，而在命题证明中使用它们则没有这个问题。

在 {ref "tactics"}[策略]证明中，可以显式使用 {name}`And.intro`，并通过 {tactic}`apply` 证明合取，但更常见的是使用 {tactic}`constructor`。
当证明目标中嵌套了多个合取时，可以使用 {tactic}`and_intros` 在各个相关位置应用 {name}`And.intro`。
上下文中的合取假设可以用 {tactic}`cases`、使用 {tactic}`let` 或 {tactic (show := "match")}`Lean.Parser.Tactic.match` 进行模式匹配，或用 {tactic}`rcases` 化简。

{zhdocstring And Manual.ZhDocString.Ch19Ch20.G2.c162}

{zhdocstring And.elim Manual.ZhDocString.Ch19Ch20.G2.c163}

析取实现为归纳定义的命题 {name}`Or`。
它有两个构造器，分别对应两个引入规则：证明任一析取项即可证明析取。
虽然 {lean}`Or` 的定义与 {lean}`Sum` 类似，但实际使用时差异很大。
由于 {lean}`Sum` 是类型，可以检查给定值由哪一个构造器创建。
另一方面，{lean}`Or` 构成命题：无法检查证明析取的项来确定哪一项为真。
换言之，由于 {lean}`Or` 不是 {tech}[至多单元素类型]，其证明不能参与计算。

在 {ref "tactics"}[策略]证明中，可以显式使用任一构造器（{name}`Or.inl` 或 {name}`Or.inr`），并通过 {tactic}`apply` 证明析取。
{tactic}`left` 和 {tactic}`right` 策略分别选择左、右析取项。
上下文中的析取假设可以用 {tactic}`cases`、使用 {tactic (show := "match")}`Lean.Parser.Tactic.match` 进行模式匹配，或用 {tactic}`rcases` 化简。

{zhdocstring Or Manual.ZhDocString.Ch19Ch20.G2.c164}

当任一析取项是 {tech}[可判定的]时，就可以使用 {lean}`Or` 计算数据。
这是因为判定过程的结果提供了合适的分支条件。

{zhdocstring Or.by_cases Manual.ZhDocString.Ch19Ch20.G2.c165}

{zhdocstring Or.by_cases' Manual.ZhDocString.Ch19Ch20.G2.c166}


```lean -show
section
variable {P : Prop}
```
否定并不编码为归纳类型；{lean}`¬P` 定义为 {lean}`P → False`。
换言之，要证明否定，只需假设被否定的陈述并推出矛盾。
这也意味着，可以从某命题及其否定的证明立即推出 {lean}`False`，再用它证明任意命题或构造任意类型的元素。
```lean -show
end
```


{zhdocstring Not Manual.ZhDocString.Ch19Ch20.G2.c167}

{zhdocstring absurd Manual.ZhDocString.Ch19Ch20.G2.c168}

{zhdocstring Not.elim Manual.ZhDocString.Ch19Ch20.G2.c169}




```lean -show
section
variable {A B : Prop}
```
蕴含使用 {tech}[命题] {tech}[宇宙]中的{ref "function-types"}[函数类型]表示。
要证明 {lean}`A → B`，只需证明 {lean}`B`，同时假设 {lean}`A`。
这对应于 {keywordOf Lean.Parser.Term.fun}`fun` 的类型规则。
类似地，函数应用的类型规则对应于{deftech}_肯定前件_：给定 {lean}`A → B` 的证明和 {lean}`A` 的证明，就可以证明 {lean}`B`。

:::example "真值函数蕴含"
将蕴含表示为命题宇宙中的函数，等价于传统定义 {lean}`A → B` 为 {lean}`(¬A) ∨ B`。
这可以使用{tech}[命题外延]和排中律证明：
```lean
theorem truth_functional_imp {A B : Prop} :
    ((¬ A) ∨ B) = (A → B) := by
  apply propext
  constructor
  . rintro (h | h) a <;> trivial
  . intro h
    by_cases A
    . apply Or.inr; solve_by_elim
    . apply Or.inl; trivial
```
:::

```lean -show
end
```


逻辑等价（即“当且仅当”）使用一个结构表示，该结构等价于两个方向蕴含的合取。

{zhdocstring Iff Manual.ZhDocString.Ch19Ch20.G2.c170}

{zhdocstring Iff.elim Manual.ZhDocString.Ch19Ch20.G2.c171}

:::syntax term (title := "命题连接词")
除蕴含外，逻辑连接词通常使用专用语法，而不是使用它们的定义名称：
```grammar
$_ ∧ $_
```
```grammar
$_ ∨ $_
```
```grammar
¬ $_
```
```grammar
$_ ↔ $_
```
:::


# 量词

%%%
tag := "Lean-__________________--Basic-Propositions--Quantifiers"
%%%
正如蕴含在 {lean}`Prop` 中实现为普通函数类型，全称量化在 {lean}`Prop` 中实现为依赖函数类型。
由于 {lean}`Prop` 是{tech}[非直谓的]，任何{tech}[陪域]为 {lean}`Prop` 的函数类型本身也是 {lean}`Prop`，即使{tech}[定义域]是 {lean}`Type`。
依赖函数的类型规则与全称量化的引入、消去规则完全对应：若谓词对类型中任意选取的元素都成立，则它对所有元素成立。
若谓词对所有元素都成立，则可将其实例化为任意个体的证明。

:::syntax term (title := "全称量化")

```grammar
∀ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
forall $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∀ $_ $[$_]*, $_
```

```grammar
forall $_ $[$_]*, $_
```

全称量词绑定一个或多个变量，这些变量随后在最终项中处于作用域内。
标识符也可以是 `_`。
带括号的类型注解允许多个绑定变量具有不同类型，而不带括号的形式要求它们类型相同。
:::

尽管全称量词由函数表示，其证明也不应被视为计算。
由于证明无关性以及命题的消去限制，无法实际使用这些证明计算数据。
因此，它们可以自由使用不易计算的推理原则，例如经典选择公理。


存在量化实现为类似于 {name}`Subtype` 和 {name}`Sigma` 的结构：它包含一个{deftech}_见证_（满足谓词的值），以及该见证确实满足谓词的证明。
换言之，它是一种依赖对类型。
与 {name}`Subtype` 和 {name}`Sigma` 不同，它是一个{tech}[命题]；这意味着程序通常不能使用存在性陈述的证明来取得满足谓词的值。

编写证明时，{tactic}`exists` 策略允许为（可能嵌套的）存在性陈述指定一个或多个见证。
另一方面，{tactic}`constructor` 策略会为见证创建一个{tech}[元变量]；提供谓词证明也可能同时解出该元变量。
可以使用 {tactic}`let` 或 {tactic (show := "match")}`Lean.Parser.Tactic.match` 进行模式匹配，或使用 {tactic}`cases`、{tactic}`rcases`，分别取得存在性假设的各个组成部分。

:::example "证明存在性陈述"

证明存在某个自然数等于四与五之和时，{tactic}`exists` 策略要求提供该和，并使用 {tactic}`trivial` 构造等式证明：

```lean
theorem ex_four_plus_five : ∃ n, 4 + 5 = n := by
  exists 9
```

另一方面，{tactic}`constructor` 策略要求提供证明。
{tactic}`rfl` 策略在检查定义等价时会顺带确定该和。

```lean
theorem ex_four_plus_five' : ∃ n, 4 + 5 = n := by
  constructor
  rfl
```


:::

{zhdocstring Exists Manual.ZhDocString.Ch19Ch20.G2.c172}

:::syntax term (title := "存在量化")

```grammar
∃ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
exists $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∃ $_ $[$_]*, $_
```

```grammar
exists $_ $[$_]*, $_
```

存在量词绑定一个或多个变量，这些变量随后在最终项中处于作用域内。
标识符也可以是 `_`。
带括号的类型注解允许多个绑定变量具有不同类型，而不带括号的形式要求它们类型相同。
如果绑定了多个变量，结果就是多个向右嵌套的 {name}`Exists` 实例。
:::

{zhdocstring Exists.choose Manual.ZhDocString.Ch19Ch20.G2.c173}

# 命题等式
%%%
tag := "propositional-equality"
%%%

{deftech}_命题等式_是允许将两个项相等表述为命题的运算符。
{tech}[定义等价]会在必要时自动检查。
因此，为了使检查算法快速且易于理解，其表达能力受到限制。
另一方面，命题等式必须显式证明并显式使用——Lean 检查证明的有效性，而不是判断陈述是否为真。
作为交换，它的表达能力强得多：许多项在命题上相等，却不定义等价。

命题等式定义为归纳类型。
其唯一构造器 {name}`Eq.refl` 要求等式两边的值相同；这隐含地使用了{tech}[定义等价]。
命题等式也可以看作模定义等价的最小自反关系。
除 {name}`Eq.refl` 外，等式证明还由 {name}`propext` 和 {name}`Quot.sound` 公理生成。


{zhdocstring Eq Manual.ZhDocString.Ch19Ch20.G2.c174}

:::syntax term (title := "命题等式")
```grammar
$_ = $_
```
命题等式通常用中缀运算符 `=` 表示。
:::

{zhdocstring rfl Manual.ZhDocString.Ch19Ch20.G2.c175}

{zhdocstring Eq.symm Manual.ZhDocString.Ch19Ch20.G2.c176}

{zhdocstring Eq.trans Manual.ZhDocString.Ch19Ch20.G2.c177}

{zhdocstring Eq.subst Manual.ZhDocString.Ch19Ch20.G2.c178}

{zhdocstring cast Manual.ZhDocString.Ch19Ch20.G2.c179}

{zhdocstring congr Manual.ZhDocString.Ch19Ch20.G2.c180}

{zhdocstring congrFun Manual.ZhDocString.Ch19Ch20.G2.c181}

{zhdocstring congrArg Manual.ZhDocString.Ch19Ch20.G2.c182}

{zhdocstring Eq.mp Manual.ZhDocString.Ch19Ch20.G2.c183}

{zhdocstring Eq.mpr Manual.ZhDocString.Ch19Ch20.G2.c184}

:::syntax term (title := "强制转换")
```grammar
$_ ▸ $_
```
当项的类型包含等式一侧作为子项时，可以使用 `▸` 运算符进行重写。
如果等式两侧都出现在项的类型中，则将左侧重写为右侧。
:::

## 等式证明的唯一性
%%%
tag := "UIP"
%%%

:::keepEnv

由于定义证明无关性，命题等式证明是_唯一的_：两个数学对象不可能以不同方式相等。

```lean
theorem Eq.unique {α : Sort u}
    (x y : α)
    (p1 p2 : x = y) :
    p1 = p2 := by
  rfl
```

Streicher 的 K 公理{citep streicher1993}[]及其计算规则同样是定义证明无关性的结果。
K 公理是与 {name}`Eq.unique` 逻辑等价的原则，实现为命题等式的另一种{tech}[递归器]。
```lean
def K {α : Sort u}
    {motive : {x : α} → x = x → Sort v}
    (d : {x : α} → motive (Eq.refl x))
    (x : α) (z : x = x) :
    motive z :=
  d

example {α : Sort u} {a : α}
    {motive : {x : α} → x = x → Sort u}
    {d : {x : α} → motive (Eq.refl x)} :
    K (motive := motive) d a rfl = d := by
  rfl
```

:::

## 异构等式
%%%
tag := "HEq"
%%%

{deftech}_异构等式_是{tech}[命题等式]的一种形式，不要求等式两项具有相同类型。
不过，使用它的 {name}`rfl` 版本_证明_两项相等时，仍要求类型和项都定义等价。
换言之，它允许表述更多陈述。

异构等式在实践中通常不如普通命题等式方便。
不要求等式两侧类型相同所带来的灵活性，也意味着它有更少的有用性质。
它常因依赖模式匹配而出现：当准确反映相应控制流所需的普通等式假设不满足类型要求时，{tactic}`split` 策略和函数归纳{TODO}[xref]会向上下文加入异构等式假设。
在这些情况下，内置自动化只能使用异构等式。


{zhdocstring HEq Manual.ZhDocString.Ch19Ch20.G2.c185}

:::syntax term (title := "异构等式")
```grammar
$_ ≍ $_
```

```lean -show
section
variable (x : α) (y : β)
```
异构等式 {lean}`HEq x y` 可写作 {lean}`x ≍ y`。
```lean -show
end
```

:::

{zhdocstring HEq.rfl Manual.ZhDocString.Ch19Ch20.G2.c186}


:::::leanSection
::::example "异构等式"
```lean -show
variable {α : Type u} {n k l₁ l₂ l₃ : Nat}
```

类型 {lean}`Vector α n` 是 {lean}`Array α` 的包装器，其中包含数组大小为 {lean}`n` 的证明。
{name}`Vector` 的追加满足结合律，但无法直接用普通命题等式表述这一事实：
```lean
variable
  {xs : Vector α l₁} {ys : Vector α l₂} {zs : Vector α l₃}
set_option linter.unusedVariables false
```
```lean (name := assocFail) +error -keep
theorem Vector.append_associative :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by sorry
```
问题在于自然数加法的结合律在命题上成立，但不定义等价：
```leanOutput assocFail
Type mismatch
  xs ++ ys ++ zs
has type
  Vector α (l₁ + l₂ + l₃)
but is expected to have type
  Vector α (l₁ + (l₂ + l₃))
```

:::paragraph
一种解决方案是在陈述中使用自然数加法的结合律：
```lean
theorem Vector.append_associative' :
    xs ++ (ys ++ zs) =
    Nat.add_assoc _ _ _ ▸ ((xs ++ ys) ++ zs) := by
  sorry
```
不过，在某些情况下，这样的证明陈述很难处理。
:::

:::paragraph
另一种方案是使用异构等式：
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by sorry
```
:::

此时，{ref "the-simplifier"}[简化器]可以重写等式两侧，而无需保持它们的类型。
不过，证明该定理最终仍需证明长度相匹配。
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by
  cases xs; cases ys; cases zs
  simp
  congr 1
  . omega
  . apply heq_of_eqRec_eq
    . rfl
    . apply propext
      constructor <;> intro h <;> simp_all +arith
```
::::
:::::

{zhdocstring HEq.elim Manual.ZhDocString.Ch19Ch20.G2.c187}

{zhdocstring HEq.ndrec Manual.ZhDocString.Ch19Ch20.G2.c188}

{zhdocstring HEq.ndrecOn Manual.ZhDocString.Ch19Ch20.G2.c189}

{zhdocstring HEq.subst Manual.ZhDocString.Ch19Ch20.G2.c190}

{zhdocstring eq_of_heq Manual.ZhDocString.Ch19Ch20.G2.c191}

{zhdocstring heq_of_eq Manual.ZhDocString.Ch19Ch20.G2.c192}

{zhdocstring heq_of_eqRec_eq Manual.ZhDocString.Ch19Ch20.G2.c193}

{zhdocstring eqRec_heq Manual.ZhDocString.Ch19Ch20.G2.c194}

{zhdocstring cast_heq Manual.ZhDocString.Ch19Ch20.G2.c195}

{zhdocstring heq_of_heq_of_eq Manual.ZhDocString.Ch19Ch20.G2.c196}

{zhdocstring type_eq_of_heq Manual.ZhDocString.Ch19Ch20.G2.c197}
