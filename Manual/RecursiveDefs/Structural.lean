/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Joachim Breitner
-/

import VersoManual
import Manual.RecursiveDefs.Structural.RecursorExample
import Manual.RecursiveDefs.Structural.CourseOfValuesExample

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option guard_msgs.diff true

#doc (Manual) "结构递归" =>
%%%
tag := "structural-recursion"
%%%

结构递归函数是指每次递归调用都作用于相对于该实参在结构上更小的项的函数。
所有递归调用中都必须是同一个形参变小；这个形参称为 {deftech (key := "decreasing parameter")}_递减参数_。
结构递归比递归器提供的原始递归更强，因为递归调用可以使用该实参更深层嵌套的子项，而不只是它的直接子项。
不过，实现结构递归所用的构造本身仍是基于递归器实现的；这些辅助构造见{ref "recursor-elaboration-helpers"}[归纳类型一节]。

支配结构递归的规则在本质上是_句法性的_。
许多递归定义在计算行为上确实体现为结构递归，但并不会被这些规则接受；这是因为该分析必须完全自动化，这一限制是根本性的结果。
{tech (key := "Well-founded recursion")}[良基递归]提供了一种证明终止性的语义方法，既可用于递归函数并非结构递归的情形，也可用于函数虽按结构递归计算、却不满足句法要求的情形。

```lean -show
section
variable (n n' : Nat)
```
:::example "结构递归与减法"
函数 {lean}`countdown` 是结构递归的。
形参 {lean}`n` 与模式 {lean}`n' + 1` 进行匹配，这意味着在模式匹配的第二个分支中，{lean}`n'` 是 {lean}`n` 的直接子项：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown n'
```

若把模式匹配替换为等价的布尔测试与减法，就会报错：
```lean +error (name := countdown') -keep
def countdown' (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
这是因为这里并没有对形参 {lean}`n` 做模式匹配。
虽然这个函数确实会终止，但其终止性的论证依赖于 if、相等测试和减法的性质，而不是 {lean}`Nat` 作为 {tech (key := "inductive type")}[归纳类型] 的一般性特征。
这些论证要用 {tech (key := "well-founded recursion")}[良基递归] 来表达；只要对函数定义做一点改动，就能让 Lean 的良基递归自动支持构造出另一份终止性证明。
这个版本不是分支于 {lean}`Nat` 的布尔相等测试结果，而是分支于 {tech (key := "propositional equality")}[命题相等] 的可判定性：

```lean
def countdown' (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```

这里，Lean 的自动化会依据命题相等和减法的事实自动构造终止性证明。
其底层采用的是良基递归，而不是结构递归。
:::
```lean -show
end
```

结构递归既可以显式使用，也可以自动推断。
在显式结构递归中，函数定义会声明哪个形参是 {tech (key := "decreasing parameter")}[递减参数]。
若未显式声明终止性策略，Lean 会同时搜索递减参数，以及可供 {tech (key := "well-founded recursion")}[良基递归] 使用的递减度量。
显式标注结构递归有以下好处：
 * 可以加快精译，因为无需搜索。
 * 能为读者记录终止性论证。
 * 在明确希望使用结构递归的场景下，可以防止意外改用良基递归。

# 显式结构递归
%%%
tag := "The-Lean-Language-Reference--Definitions--Recursive-Definitions--Structural-Recursion--Explicit-Structural-Recursion"
%%%

若要显式使用结构递归，可以在函数或定理定义上添加 {keywordOf Lean.Parser.Command.declaration}`termination_by structural` 子句，用以指定 {tech (key := "decreasing parameter")}[递减参数]。
递减参数可以引用签名中已命名的形参。
若签名写成函数类型，则递减参数还可以是签名中未命名的形参；此时可在箭头（{keywordOf Lean.Parser.Command.declaration}`=>`）前写出其余形参的名称，将它们引入作用域。

:::example "指定递减参数"

当递减参数是函数的具名形参时，可以直接引用其名称来指定。

```lean -keep
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n
```

当递减参数在签名中未命名时，可以在 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句中局部引入一个名称。

```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
:::

:::syntax Lean.Parser.Termination.terminationBy (title := "显式结构递归")

`termination_by structural` 子句用来引入递减参数。

```grammar
termination_by structural $[$_:ident* =>]? $term
```

可选 `=>` 之前的标识符可以把尚未在声明头中绑定的函数形参带入作用域，而后面必需的项必须指明函数的某个形参，无论它是在声明头中引入，还是在该子句中局部引入。
:::

递减参数必须满足下列条件：

* 它的类型必须是 {tech (key := "inductive type")}[归纳类型]。

* 若其类型是 {tech (key := "indexed family")}[索引族]，则所有索引都必须是该函数的形参。

* 若递减参数的归纳类型或索引族带有数据类型参数，则这些数据类型参数本身只能依赖属于 {tech (key := "fixed prefix")}[固定前缀] 的函数形参。

{deftech (key := "fixed parameter")}_固定参数_ 是指在所有递归调用中都原样传递、且不是递归参数类型之索引的函数形参。
{deftech (key := "fixed prefix")}_固定前缀_ 是函数形参中满足“全部固定”的最长前缀。

:::example "不合格的递减参数"

递减参数的类型必须是归纳类型。
在 {lean}`notInductive` 中，被指定为递减参数的是一个函数：

```lean +error (name := badnoindct)
def notInductive (x : Nat → Nat) : Nat :=
  notInductive (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified measure for structural recursion:
  its type is not an inductive
```

若递减参数是索引族，则所有索引都必须是变量。
在 {lean}`constantIndex` 中，索引族 {lean}`Fin'` 却被应用到了一个常量值上：

```lean +error (name := badidx)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def constantIndex (x : Fin' 100) : Nat := constantIndex .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified measure for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```

递减参数类型中的参数，不能依赖那些位于变化参数或索引之后的函数形参。
在 {lean}`afterVarying` 中，{tech (key := "fixed prefix")}[固定前缀] 为空，因为第一个形参 `n` 会变化，所以 `p` 不属于固定前缀：

```lean +error (name := badparam)
inductive WithParam' (p : Nat) : Nat → Type where
  | zero : WithParam' p (n+1)
  | succ : WithParam' p n → WithParam' p (n+1)

def afterVarying (n : Nat) (p : Nat) (x : WithParam' p n) : Nat :=
  afterVarying (n+1) p .zero
termination_by structural x
```
```leanOutput badparam
failed to infer structural recursion:
Cannot use parameter x:
  failed to eliminate recursive application
    afterVarying (n + 1) p WithParam'.zero
```
:::

此外，函数的每次递归调用都必须作用于递减参数的某个 {deftech (key := "strict sub-term")}_真子项_。

 * 递减参数自身是一个子项，但不是真子项。
 * 若某个子项是 {keywordOf Lean.Parser.Term.match}`match` 表达式或其他模式匹配语法的 {tech (key := "match discriminant")}[判别项]，则与该判别项匹配的模式，会成为各个 {tech (key := "match alternative")}[匹配分支] 的 {tech (key := "right-hand side")}[右侧] 中的子项。
   尤其是，这里会使用 {ref "match-generalization"}[匹配泛化] 的规则，把判别项与右侧中模式项的出现关联起来；因此它遵守 {tech (key := "definitional equality")}[定义相等]。
   当且仅当判别项是真子项时，该模式才是真子项。
 * 若某个子项是作用于若干实参的构造器，那么它的递归实参都是真子项。

```lean -show
section
variable (n : Nat)
```
::::example "嵌套模式与子项"

在下例中，递减参数 {lean}`n` 与嵌套模式 {lean  (type := "Nat")}`.succ (.succ n)` 匹配。因此 {lean  (type := "Nat")}`.succ (.succ n)` 是 {lean  (type := "Nat")}`n` 的一个（非严格）子项，于是 {lean  (type := "Nat")}`n` 和 {lean  (type := "Nat")}`.succ n` 都是真子项，所以该定义会被接受。

```lean
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```

为便于说明，这个例子使用 {lean  (type := "Nat")}`.succ n` 和 {lean  (type := "Nat")}`.succ (.succ n)`，而不是等价的、{lean}`Nat` 专用的 {lean}`n+1` 与 {lean}`n+2`。

:::TODO
链接到这种特殊语法的文档位置。
:::

::::
```lean -show
end
```

```lean -show
section
variable {α : Type u} (n n' : Nat) (xs : List α)
```
:::example "对复杂表达式做匹配可能阻碍精译"

在下例中，递减参数 {lean}`n` 并不是 {keywordOf Lean.Parser.Term.match}`match` 表达式的直接 {tech (key := "match discriminant")}[判别项]。
因此，{lean}`n'` 不会被视为 {lean}`n` 的子项。

```lean +error -keep (name := badtarget)
def half (n : Nat) : Nat :=
  match Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by structural n
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```

若改用 {tech (key := "well-founded recursion")}[良基递归]，并显式把判别项与匹配模式联系起来，这个定义就能被接受。

```lean
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```

类似地，下面这个例子也会失败：虽然 {lean}`xs.tail` 会归约为 {lean}`xs` 的一个真子项，但按照上述规则，这一点对 Lean 来说并不可见。
特别地，{lean}`xs.tail` 与 {lean}`xs` 的某个真子项并不 {tech (key := "definitional equality")}[定义相等]。

```lean +error -keep
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```

:::
```lean -show
end
```


:::example "结构递归中的同时匹配与匹配成对值"

用于证明终止性的这些策略有一个重要后果：*同时匹配两个 {tech (key := "match discriminant")}[判别项] 与匹配一个二元组并不等价*。
同时匹配会保留判别项与模式之间的联系，使模式匹配不仅能细化局部上下文中假设的类型，也能细化 {keywordOf Lean.Parser.Term.match}`match` 的期望类型。
本质上，{keywordOf Lean.Parser.Term.match}`match` 的精译规则会对判别项作特殊处理；因此，对判别项做出虽能保持程序运行时含义、却不一定保持编译时含义的改动，并不安全。

下面这个求两个自然数最小值的函数，是按其第一个参数做结构递归定义的：
```lean -keep
def min' (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min' n' k' + 1
termination_by structural n
```

若把对两个参数的同时模式匹配改写为对一个二元组做匹配，终止性分析就会失败：
```lean +error (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```

这是因为在把递归调用与更小的实参值对应起来时，该分析只考虑对形参本身的直接模式匹配。
把判别项包进一个二元组会破坏这种联系。
:::

:::example "成对值下的结构递归"

下面这个求一对数中两个分量之最小值的函数，无法通过结构递归精译。
```lean +error (name := minpair) -keep
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by structural nk
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```

这是因为该形参的类型 {name}`Prod` 并不是递归的。
因此，它的构造器没有可通过模式匹配暴露出来的递归参数。

不过，这个定义可以通过 {tech (key := "well-founded recursion")}[良基递归] 被接受：
```lean
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by nk
```
:::

```lean -show
section
variable (n n' : Nat)
```
:::example "结构递归与定义相等"

尽管 {lean}`countdown` 的递归出现被应用到了一个并非递减参数真子项的项上，下列定义仍会被接受：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown (n' + 0)
termination_by structural n
```

这是因为 {lean}`n' + 0` 与 {lean}`n'` {tech (key := "definitional equality")}[定义相等]，而后者是 {lean}`n` 的真子项。
由模式匹配产生的 {tech (key := "strict sub-term")}[子项] 会通过 {ref "match-generalization"}[匹配泛化] 的规则与 {tech (key := "match discriminant")}[判别项] 关联起来，而这些规则尊重定义相等。

在 {lean}`countdown'` 中，递归出现被应用到了 {lean}`0 + n'` 上；它与 `n'` 并不定义相等，因为自然数上的加法是按照第二个参数做结构递归的：
```lean +error (name := countdownNonDefEq)
def countdown' (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown' (0 + n')
termination_by structural n
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```

:::
```lean -show
end
```

# 互结构递归
%%%
tag := "mutual-structural-recursion"
%%%

Lean 支持用结构递归来定义 {tech (key := "mutually recursive")}[互递归] 函数。
互递归既可以通过 {tech (key := "mutual block")}[互递归块] 引入，也可能来自 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 代码块。
互结构递归的规则，会应用到由互递归组的{ref "mutual-syntax"}[精译步骤]所得、经过提升后且实际上互相递归的一组定义上。
若互递归组中的每个函数都带有指明该函数递减实参的 {keyword}`termination_by structural` 注解，那么这些定义就会按结构递归来翻译。

此时，对递减实参的要求会扩展为：

 * 所有递减实参的类型都必须来自同一个归纳类型，或者更一般地，来自同一个{ref "mutual-inductive-types"}[互归纳类型组]。

 * 递减参数类型中的参数，对所有函数都必须相同，且只能依赖于函数实参的_共同_固定前缀。

这些函数不必与互归纳类型一一对应。
多个函数可以拥有同一类型的递减实参，而与该递减实参互递归的类型也不必全都对应到某个函数。

:::example "非互递归类型上的互结构递归"

下面这个例子展示了在一个非互递归的归纳数据类型上进行互递归：

```lean
mutual
  def even : Nat → Prop
    | 0 => True
    | n+1 => odd n
  termination_by structural n => n

  def odd : Nat → Prop
    | 0 => False
    | n+1 => even n
  termination_by structural n => n
end
```
:::

:::example "互归纳类型上的互结构递归"

下面这个例子展示了在互归纳类型上的递归。
函数 {lean}`Exp.size` 与 {lean}`App.size` 互相递归。

```lean
mutual
  inductive Exp where
    | var : String → Exp
    | app : App → Exp

  inductive App where
    | fn : String → App
    | app : App → Exp → App
end

mutual
  def Exp.size : Exp → Nat
    | .var _ => 1
    | .app a => a.size
  termination_by structural e => e

  def App.size : App → Nat
    | .fn _ => 1
    | .app a e => a.size + e.size + 1
  termination_by structural a => a
end
```

{lean}`App.numArgs` 的定义是在类型 {lean}`App` 上做结构递归。
它说明互递归组中的归纳类型不必全部都参与处理。

```lean
def App.numArgs : App → Nat
  | .fn _ => 0
  | .app a _ => a.numArgs + 1
termination_by structural a => a
```

:::

::::draft
:::planned 235

描述在{ref "nested-inductive-types"}[嵌套归纳类型]上的互结构递归。

:::
::::

# 推断结构递归
%%%
tag := "inferring-structural-recursion"
%%%


若递归或互递归函数定义中没有 {keyword}`termination_by` 子句，Lean 就会尝试推断一个合适的结构递减实参；做法实际上是按顺序尝试所有合适的形参。
若这一步搜索失败，Lean 随后会尝试推断 {tech (key := "well-founded recursion")}[良基递归]。

对互递归函数而言，会尝试形参的各种组合，但会设置上限以避免组合爆炸。
如果只有部分互递归函数带有 {keyword}`termination_by structural` 子句，那么对这些函数只考虑所指定的形参；而对其余函数，则会把所有形参都作为结构递归候选。

{keyword}`termination_by?` 子句会显示推断出的终止性注解。
它还可以通过给出的建议或代码操作自动加入源文件。

:::example "推断出的终止性注解"
Lean 会自动推断函数 {lean}`half` 是结构递归的。
{keyword}`termination_by?` 子句会显示推断出的终止性注解，并且可以一键自动加入源文件。

```lean (name := inferStruct)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by?
```
```leanOutput inferStruct
Try this:
  [apply] termination_by structural x => x
```
:::

# 使用按所有较小值递归的精译
%%%
tag := "elab-as-course-of-values"
%%%

本节将更详细地说明精译结构递归函数时所使用的构造。
这种精译使用了由归纳类型递归器自动生成的 {ref "recursor-elaboration-helpers"}[`below` 与 `brecOn` 构造]。

{spliceContents Manual.RecursiveDefs.Structural.RecursorExample}

结构递归分析会尝试把递归 {tech (key := "pre-definition")}[预定义] 翻译成对相应结构递归构造的使用。
在这一步里，模式匹配已经被翻译成匹配器函数的调用；终止性检查器会对这些调用作特殊处理。
接着，它会对每一组参数尝试使用 `brecOn` 的翻译。

{spliceContents Manual.RecursiveDefs.Structural.CourseOfValuesExample}

`below` 构造把某个类型的每个值映射到“某个函数在_所有_更小值上的调用结果”；它可以理解为一张记忆化表，其中已经包含了所有更小值的结果。
`below` 构造中“更小值”的概念，与 {tech (key := "strict sub-terms")}[真子项] 的定义直接对应。

递归器要求为该归纳类型的每个构造器各提供一个实参；在 {tech (key := "ι-reduction")}[ι-归约] 时，这些实参会以该构造器的参数（以及对递归参数递归后的结果）来调用。
而按所有较小值递归的算子 `brecOn` 只要求一个同时覆盖全部构造器的分支。
这个分支会收到一个值以及一张 `below` 表；该表包含对所有比给定值更小的值递归所得的结果，分支应利用表中的内容来满足这个给定值对应的动机。
若函数在某个给定参数（或参数组）上是结构递归的，那么所有递归调用的结果都已经出现在这张表里。

当递归函数的函数体被改写为对某个形参调用 `brecOn` 时，该形参与其“所有较小值表”都会进入作用域。
分析器会遍历函数体，寻找递归调用。
如果对这个形参做了匹配，那么它在局部上下文中的各次出现会先被{ref "match-generalization"}[泛化]，再用模式实例化；“所有较小值表”的类型也同样如此。
通常，这种模式匹配会让“所有较小值表”的类型变得更具体，从而能够访问更小值对应的递归结果。
这种泛化过程实现了“模式是匹配判别项的 {tech (key := "strict sub-term")}[子项]”这一规则。
当检测到函数的递归出现时，就会查询“所有较小值表”，看看其中是否含有所检查实参对应的结果。
若有，递归调用即可替换成从该表中的一次投影。
若没有，则说明这里所考虑的参数不支持结构递归。

```lean -show
section
```

:::example "精译过程示例"
逐步考察 {name}`half` 的精译时，第一步是手工把它反糖化成一个更简单的形式。
这并不完全符合 Lean 的实际处理方式，但当出现的 {name}`OfNat` 实例更少时，输出会容易阅读得多。
这个较易读的定义：
```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
可以改写成下面这个更底层一些的版本：
```lean -keep
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```

精译器一开始会先精译出一个预定义，其中递归仍然保留，但除此之外，该定义已经落在 Lean 的核心类型论里。
开启编译器对预定义的追踪，并让美化打印更显式，就可以看到得到的预定义：
```lean -keep -show
-- 测试下一代码块——更新时请目测核对其对应关系！
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
trace: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
返回的跟踪消息是：{TODO}[跟踪信息没有显示在序列化后的信息里——需要查明原因，以便让这个测试更可靠；更理想的是，为 Verso 增加正式的跟踪渲染支持]
```
[Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x
        (fun (_ : Unit) => Nat.zero)
        (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
```
辅助匹配函数的定义是：
```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
@[instance_reducible] def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
把它排版得更易读一些，则为：
```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
换言之，{name}`half` 中使用的那组特定模式配置，被编码进了 {name}`half.match_1`。

这个定义是 {name}`half` 预定义的一个更易读版本：
```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- 0 的分支
      (fun _ => 0) -- 1 的分支
      (fun n => Nat.succ (half' n)) -- n + 2 的分支
```

要把它精译为一个结构递归函数，第一步是建立对 `bRecOn` 的调用。
该定义必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为 Lean 不支持为 {name}`Nat.brecOn` 这类递归器生成代码。
```lean +error -keep
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- 待翻译：
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- 0 的分支
      (fun _ => 0) -- 1 的分支
      (fun n => Nat.succ (half' n)) -- n + 2 的分支
-/
```

下一步是把原函数体中出现的 `x` 替换为 {name Nat.brecOn}`brecOn` 提供的 `n`。
由于 `table` 的类型依赖于 `x`，因此在用 {name}`half.match_1` 分情况时，它也必须一并泛化，从而得到一个带额外参数的动机。

```lean +error -keep (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- 待翻译：
      (fun _ => 0) -- 0 的分支
      (fun _ => 0) -- 1 的分支
      (fun n => Nat.succ (half' n)) -- n + 2 的分支
-/
```
这三个分支中的占位符分别需要如下类型：
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_1`
context:
x n : Nat
table : Nat.below n
⊢ Unit → Nat.below Nat.zero → Nat
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_2`
context:
x n : Nat
table : Nat.below n
⊢ Unit → Nat.below 1 → Nat
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_3`
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → Nat.below n.succ.succ → Nat
```

预定义中的前两个分支都是常量函数，没有递归需要检查：

```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- 待翻译：
      (fun n => Nat.succ (half' n)) -- n + 2 的分支
-/
```

最后一个分支包含递归调用。
它应当被翻译为对“所有较小值表”的一次查找。
最后一个洞的类型，用更易读的形式写出来是：
```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
它等价于
```leanTerm
(n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat
```

```lean -show
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat) := rfl
```

```lean -show

variable {n : Nat}
```

“所有较小值表”中的第一个 {lean}`Nat`，是对 {lean}`n + 1` 递归所得的结果；第二个则是对 {lean}`n` 递归所得的结果。
因此，递归调用可以替换成一次查找，于是精译成功：

```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```

实际的精译器会在动机中插入带新鲜名称的哨兵类型，以此跟踪“当前检查是否结构递归的参数”与“所有较小值表中的位置”之间的对应关系。
:::

```lean -show
end
```

::::draft
::: planned 56
对互递归函数精译过程的说明
:::
::::
