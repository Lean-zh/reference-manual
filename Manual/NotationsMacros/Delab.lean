/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.PrettyPrinter.Delaborator

import Manual.Meta
import Manual.ZhDocString.NotationsMacros.Core


open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean (Syntax Expr)

#doc (Manual) "扩展 Lean 的输出" =>
%%%
tag := "unexpand-and-delab"
file := "Extending-Lean___s-Output"
%%%

用新语法扩展 Lean，并用宏和精译器实现这种新语法，能让用户更方便地向 Lean 表达想法。
不过，Lean 是一个_交互式_定理证明器：它给出的反馈也同样必须便于理解。
语法扩展不仅应当用于_输入_，也应当用于_输出_。

:::paragraph
让 Lean 在输出中使用语法扩展，主要有两种机制：

: 逆展开器

  逆展开器是 {tech (key := "macros")}[宏] 的逆过程。
  宏通过翻译用旧语法实现新语法，把新特性_展开_为既有特性的编码。
  与宏一样，{deftech (key := "unexpanders")}_逆展开器_ 会把 {lean}`Syntax` 翻译成 {lean}`Syntax`；与宏不同的是，它们会把这些编码变换回新的扩展形式。

: 反精译器

  反精译器是 {tech (key := "elaborators")}[精译器] 的逆过程。
  精译器会把 {lean}`Syntax` 翻译成核心类型论的 {lean}`Expr`，而 {deftech (key := "delaborators")}_反精译器_ 则会把 {lean}`Expr` 翻译成 {lean}`Syntax`。
:::

在显示一个 {name}`Expr` 之前，系统会先对它做反精译，再做反展开。
反精译器会跟踪其输出源自原始 {name}`Expr` 的哪个位置；这个位置信息被编码到结果语法的 {name Lean.SourceInfo}`SourceInfo` 中。
正如宏展开会自动用与原始语法位置对应的合成源码信息来标注结果语法一样，逆展开机制也会保留结果语法与底层 {name}`Expr` 的关联。
这种关联使 Lean 的交互功能能够在 {tech (key := "proof states")}[证明状态] 和诊断信息中显示结果语法时，提供与之相关的进一步信息。

# 逆展开器
%%%
tag := "Unexpanders"
%%%

正如宏被注册在一张把 {tech (key := "syntax kinds")}[语法种类] 映射到宏实现的表中一样，逆展开器也被注册在一张把常量名映射到逆展开器实现的表中。
在 Lean 向用户显示语法之前，它会尝试按照这张表重写语法中对每个常量的应用。
上下文中那些并非应用的位置，也会被视为带零个实参的应用。

反展开按由内向外的顺序进行。
传给逆展开器的是应用的语法；其中隐式参数已被隐藏，而且实参已经先完成反展开。
如果选项 {option}`pp.explicit` 为 {lean}`true`，或者 {option}`pp.notation` 为 {lean}`false`，那么就不会使用逆展开器。

::::::::leanSection
```lean -show
open Lean.PrettyPrinter (Unexpander UnexpandM)
```

逆展开器的类型是 {lean}`Lean.PrettyPrinter.Unexpander`，它是 `Syntax → Lean.PrettyPrinter.UnexpandM Syntax` 的缩写。
在本节剩余部分中，名称 {lean}`Unexpander` 和 {lean}`UnexpandM` 都不再带限定名。
{lean}`UnexpandM` 是一个单子；借助其实例 {name Lean.MonadQuotation}`MonadQuotation` 与 {lean}`MonadExcept Unit`，它支持引用与失败。

逆展开器要么返回已经反展开的语法，要么使用 {lean  (type := "UnexpandM Syntax")}`throw ()` 失败。
如果逆展开器成功，得到的语法还会再次反展开；如果失败，则会尝试下一个逆展开器。
如果没有任何逆展开器能成功处理该语法，那么它的子节点会继续被反展开，直到所有可能的反展开机会都耗尽。

{zhdocstring Lean.PrettyPrinter.Unexpander Manual.ZhDocString.NotationsMacros.Core.PrettyPrinter.Unexpander}

{zhdocstring Lean.PrettyPrinter.UnexpandM Manual.ZhDocString.NotationsMacros.Core.PrettyPrinter.UnexpandM}

通过施加 {attr}`app_unexpander` 属性，可以为某个常量注册逆展开器。
{ref "operators"}[自定义运算符]和 {ref "notations"}[记法]会自动为它们引入的语法创建逆展开器。

:::syntax attr (title := "逆展开器注册")
```grammar
app_unexpander $_:ident
```

为某个常量的应用注册一个类型为 {name}`Unexpander` 的逆展开器。
:::


:::::example "自定义 Unit 类型" (file := "Custom Unit Type")
::::keepEnv
可以定义一个与 {lean}`Unit` 等价、但拥有自身记法的类型：把它写成一个零字段结构体，再配上一个宏即可：
```lean
structure Solo where
  mk ::

syntax "‹" "›" : term

macro_rules
  | `(term|‹›) => ``(Solo.mk)
```


虽然这个新记法可以用于书写定理陈述，但它不会出现在证明状态中。
例如，在证明所有 {lean}`Solo` 类型的值都等于 {lean}`‹›` 时，初始证明状态是：
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = { }
-/

```
这个证明状态使用 {tech (key := "structure instance")}[结构体实例] 语法来显示构造子。
可以用逆展开器覆盖这一选择。
由于 {name}`Solo.mk` 不能应用于任何实参，因此逆展开器可以完全忽略它收到的语法；这个语法总会是 {lean (type := "UnexpandM Syntax")}`` `(Solo.mk) ``。

```lean
@[app_unexpander Solo.mk]
def unexpandSolo : Lean.PrettyPrinter.Unexpander
  | _ => `(‹›)
```

有了这个逆展开器后，证明的初始状态现在就会以正确的语法渲染出来：
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = ‹›
-/

```

::::
:::::

:::::example "反展开与参数" (file := "Unexpansion and Arguments")

{name}`ListCursor` 表示 {lean}`List` 中的一个位置。
{name}`ListCursor.before` 保存位置之前元素构成的逆序列表，而 {name}`ListCursor.after` 保存位置之后的元素。

```lean
structure ListCursor (α) where
  before : List α
  after : List α
deriving Repr
```

列表光标既可以向左移动，也可以向右移动：
```lean
def ListCursor.left : ListCursor α → Option (ListCursor α)
  | ⟨[], _⟩ => none
  | ⟨l :: ls, rs⟩ => some ⟨ls, l :: rs⟩

def ListCursor.right : ListCursor α → Option (ListCursor α)
  | ⟨_, []⟩ => none
  | ⟨ls, r :: rs⟩ => some ⟨r :: ls, rs⟩
```

它也可以一路移动到最左端或最右端：
```lean
def ListCursor.rewind : ListCursor α → ListCursor α
  | xs@⟨[], _⟩ => xs
  | ⟨l :: ls, rs⟩ => rewind ⟨ls, l :: rs⟩
termination_by xs => xs.before

def ListCursor.fastForward : ListCursor α → ListCursor α
  | xs@⟨_, []⟩ => xs
  | ⟨ls, r :: rs⟩ => fastForward ⟨r :: ls, rs⟩
termination_by xs => xs.after
```

```lean -show
def ListCursor.ofList (xs : List α) : ListCursor α where
  before := []
  after := xs

def ListCursor.toList : (xs : ListCursor α) → List α
  | ⟨[], rs⟩ => rs
  | ⟨l::ls, rs⟩ => toList ⟨ls, l :: rs⟩
termination_by xs => xs.before
```

不过，必须把先前元素的列表反转这一点，会让列表光标难以理解。
可以为光标设计一种记法，用一面旗帜（`🚩`）在列表中标记光标所在的位置：
```lean
syntax "[" term,* " 🚩 " term,* "]": term
macro_rules
  | `([$ls,* 🚩 $rs,*]) =>
    ``(ListCursor.mk [$[$((ls : Array Lean.Term).reverse)],*] [$rs,*])
```
在这个宏中，元素序列的类型是 {lean}``Syntax.TSepArray `term ","``。
把它标注为 {lean}`Array Lean.Term` 会触发一次强制转换，从而可以应用 {name}`Array.reverse`；类似的强制转换还会把分隔逗号重新插入。
这些强制转换见 {ref "typed-syntax"}[带类型语法] 一节。

虽然这种语法可以使用，但它不会出现在 Lean 的输出中：
```lean (name := flagNo)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagNo
{ before := [3, 2, 1], after := [4, 5] } : ListCursor Nat
```

逆展开器可以解决这个问题。
这个逆展开器依赖于内建的列表字面量逆展开器，前提是它们已经把这两个列表重写好了：
```lean
@[app_unexpander ListCursor.mk]
def unexpandListCursor : Lean.PrettyPrinter.Unexpander
  | `($_ [$ls,*] [$rs,*]) =>
    `([$((ls : Array Lean.Term).reverse),* 🚩 $(rs),*])
  | _ => throw ()
```

```lean (name := flagYes)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagYes
[1, 2, 3 🚩 4, 5] : ListCursor Nat
```

```lean (name := flagYes2)
#reduce [1, 2, 3 🚩 4, 5].right
```
```leanOutput flagYes2
some [1, 2, 3, 4 🚩 5]
```

```lean (name := flagYes3)
#reduce [1, 2, 3 🚩 4, 5].left >>= (·.left)
```
```leanOutput flagYes3
some [1 🚩 2, 3, 4, 5]
```

:::::

::::::::


# 反精译器
%%%
tag := "delaborators"
%%%
::::::::leanSection
```lean -show
open Lean.PrettyPrinter.Delaborator (DelabM Delab)
open Lean (Term)
```
反精译器的类型是 {lean}`Lean.PrettyPrinter.Delaborator.Delab`，它是 {lean}`Lean.PrettyPrinter.Delaborator.DelabM Term` 的缩写。
与逆展开器不同，反精译器并不是按普通函数来实现的。
这样做是为了更容易正确实现它们：单子 {name}`DelabM` 会跟踪当前正在反精译的表达式位置，从而使反精译机制能够给结果语法打上相应标注。

反精译器通过 {attr}`delab` 属性注册。
内部有一张表，把 {name}`Expr` 各个构造子的名字（不带命名空间）映射到反精译器。
此外，系统还会查询名字 `app.`﻿$`c`，以寻找常量 $`c` 的应用所对应的反精译器；也会查询名字 `mdata.`﻿$`k`，以寻找元数据中只含单个键 $`k` 的 {name}`Expr.mdata` 构造子所对应的反精译器。

:::syntax attr (title := "反精译器注册")
{attr}`delab` 属性会为所指明的 {lean}`Expr` 构造子或元数据键注册一个反精译器。
```grammar
delab $_:ident
```

{keyword}`app_delab ` 属性会在当前 {tech (key := "section scope")}[作用域] 中对常量名完成 {tech (key := "resolve")}[解析] 后，为其应用注册反精译器。
```grammar
app_delab $_:ident
```
:::

::::leanSection
```lean -show
open Lean.PrettyPrinter.Delaborator.SubExpr
```
:::paragraph
单子 {name}`DelabM` 是一个 {tech (key := "reader monad")}[读取器单子]，其中包含对当前 {lean}`Expr` 位置的访问能力。
递归反精译时，不是把某个子表达式显式传给另一个函数，而是通过调整读取器单子所跟踪的位置来完成。
在反精译器中处理子表达式时，最重要的一些函数位于命名空间 `Lean.PrettyPrinter.Delaborator.SubExpr` 中：
 * {name}`getExpr` 取回当前表达式以供分析。
 * {name}`withAppFn` 把当前位置调整为应用中的函数位置。
 * {name}`withAppArg` 把当前位置调整为应用中的实参位置。
 * {name}`withAppFnArgs` 把当前表达式分解为一个非应用函数及其参数，并依次聚焦到它们上面。
 * {name}`withBindingBody` 下降到函数或函数类型的主体中。

还提供了更多函数，用于下降到 {name}`Expr` 其余构造子中。
:::
::::


::::::::

::::draft
:::planned 122

 * 反精译示例与组合子参考
 * 漂亮打印
 * 括号器
:::
::::
