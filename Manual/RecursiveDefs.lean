/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.RecursiveDefs

import Manual.RecursiveDefs.Structural
import Manual.RecursiveDefs.WF
import Manual.RecursiveDefs.PartialFixpoint
import Manual.RecursiveDefs.CoinductivePredicates

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode



#doc (Manual) "递归定义" =>
%%%
tag := "recursive-definitions"
file := "Recursive-Definitions"
%%%

允许任意递归函数定义会使 Lean 的逻辑不一致。一般递归使得可以写出环形证明：“{tech (key := "proposition")}[命题] $`P` 为真，因为命题 $`P` 为真”。在证明之外，一个无限循环可以被赋予类型 {name}`Empty`，再结合 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 或 {name Empty.rec}`Empty.rec`，即可“证明”任意定理。

直接禁止递归函数定义将大幅降低 Lean 的实用性：{tech (key := "inductive type")}[归纳类型]是定义谓词与数据的关键，而它们本身具有递归结构。
此外，多数有用的递归函数并不威胁自洽性，而无限循环通常意味着定义有误而非有意为之。
Lean 并未一禁了之，而是要求每个递归函数都以安全的方式定义。
在精译递归定义的过程中，Lean 的精译器还会同时给出该定义安全的理由。{margin}[可参阅精译概览中的 {ref "elaboration-results"}[精译器的输出]一节，了解递归定义精译在整体精译流程中的位置。]

可以定义的递归函数主要有六类：

: 结构递归函数

  结构递归函数接收某个实参，并且仅在该实参的真子项上进行递归调用。{margin}[严格来说，类型为 {tech (key := "indexed families")}[索引族] 的实参会与其索引成组，把整个集合视作一个整体。]
  精译器会把递归翻译成对该实参的 {tech (key := "recursor")}[递归器] 的调用。
  由于每个类型正确的递归器使用都保证避免无限回归，这样的翻译即构成函数终止性的证据。
  通过递归器定义的函数应用在定义上等同于递归结果，并且在内核中通常较为高效。


: 良基关系上的递归

  有些函数也难以改写为结构递归；例如，某个函数之所以终止，是因为随着数组索引增大，索引与数组长度之差在减小，但此时由于增长的是函数的实参本身，{name}`Nat.rec` 并不适用。
  在这种情形下，存在一个随每次递归调用而减少的终止{tech (key := "measure")}[度量]，但该度量本身并非函数的一个实参。
  这时可以使用 {tech (key := "well-founded recursion")}[良基递归] 来定义函数。
  良基递归是一种技术：系统地把“伴随度量递减的递归函数”转化为“基于证明的递归函数”，该证明表明任意度量递减序列最终会在最小值处终止。
  用良基递归定义的函数应用不一定与其返回值在定义上相等，但这种相等可以作为命题来证明。
  即便存在定义相等，这类函数在计算上仍常常较慢，因为它们需要归约通常很大的证明项。

: 作为偏不动点的递归函数

  一个函数的定义可以理解为一条给出其行为的方程。
  在某些情况下，即使该递归函数对所有输入未必终止，仍可证明存在一个满足此规格的函数。
  该策略甚至适用于某些函数定义对所有输入未必终止的情形。
  由此得到的偏函数作为这些方程的不动点而出现，被称为 {tech (key := "partial fixpoints")}[偏不动点]。

  尤其是，返回类型位于某些单子中的函数（例如 {name}`Option`）可以用该策略来定义。
  对这类单子函数，Lean 还会生成额外的偏正确性定理。
  与良基递归类似，按偏不动点定义的函数应用在定义上不等同于其返回值，但 Lean 会生成定理，在命题层面将该函数与其展开式以及定义中所给的归约行为相等同。

: 作为不动点的余归纳与归纳谓词

  取值于 {lean}`Prop` 的递归函数，可以定义为完备格上单调算子的最大不动点或最小不动点。
  余归纳谓词使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 或 {keywordOf Lean.Parser.Command.declaration}`coinductive` 命令定义，用来描述无限序列、互模拟等潜在的无限行为。
  归纳谓词使用 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 定义；它提供了标准归纳类型之外的另一种选择，并可用于归纳—余归纳混合互递归块。

: 余域非空的偏函数

  在许多应用中，某些函数的具体实现并不需要被推理。
  一个递归函数可能仅作为证明自动化步骤实现的一部分，或仅是不会被形式化证明正确性的普通程序。
  在这类场景中，Lean 内核不需要该定义在“定义相等”或“命题相等”层面成立；只要保持逻辑自洽即可。
  被标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数会被内核视作不透明常量，既不会被展开也不会被归约。
  为保持自洽性，唯一的要求是其返回类型可被占据。
  偏函数在编译后的代码中仍可照常使用，也可出现在命题与证明中；只是它们在 Lean 逻辑中的等式理论非常薄弱。

: 不安全的递归定义

  不安全定义不受偏定义的任何限制。
  它们可自由使用一般递归，并可使用会打破等式理论假设的 Lean 特性，例如强制转换原语（{name}`unsafeCast`）、检查指针相等（{name}`ptrAddrUnsafe`），以及观察{tech (key := "reference counts")}[引用计数]（{name}`isExclusiveUnsafe`）。
  但凡引用不安全定义的声明本身也必须标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe`，以清楚表明此处不保证逻辑自洽。
  在编译后的代码中，不安全操作可用于以更高效的实现替换其他函数的实现，而内核仍然使用原始定义。
  被替换的函数可以是不透明的，此时该函数名在逻辑中的等式理论是平凡的；也可以是普通函数，此时逻辑中仍会使用该函数。
  请谨慎使用这一特性：逻辑自洽性虽不受威胁，但若不安全实现有误，Lean 程序的实际行为可能会偏离其经验证的逻辑模型。


:::TODO

总览所有策略及其性质的表格

:::


如{ref "elaboration-results"}[精译器输出概览]所述，递归函数的精译分为两个阶段：
 1. 先假定 Lean 的内核类型论允许递归定义，对定义进行精译。
    除递归调用外，这个临时定义已被完整精译；编译器也从这些临时定义生成代码。

 2. 随后进行终止性分析，尝试使用五种技术向 Lean 内核说明该函数是安全的。
    若定义标有 {keywordOf Lean.Parser.Command.declaration}`unsafe` 或 {keywordOf Lean.Parser.Command.declaration}`partial`，则采用相应技术。
    若存在显式的 {keywordOf Lean.Parser.Command.declaration}`termination_by`、{keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`、{keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 或 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句，则只尝试该子句指定的技术。
    若不存在这些子句，精译器会进行搜索：依次把函数的每个形参作为结构递归候选，并尝试寻找一个在每次递归调用时沿良基关系递减的度量。

本节描述支配递归函数的规则。介绍互递归之后，将逐一说明五种递归定义技术，并讨论各自推理能力与灵活性之间的权衡。

# 互递归
%%%
tag := "mutual-syntax"
%%%


就像递归定义是在其定义体中提到正在被定义的名字一样，{deftech (key := "mutually recursive")}_互递归_ 的定义指的是：它们本身可以是递归的，或彼此相互引用。
要在多个声明之间使用互递归，必须把它们放入一个 {deftech (key := "mutual block")}[互递归块] 中。


:::syntax command (title := "互递声明块")
互递的一般语法为：

```grammar
mutual
  $[$declaration:declaration]*
end
```
其中各声明必须是定义或定理。
:::


在一个互递声明块中，各声明的名称不在彼此的类型签名的作用域内，但在彼此的定义体中可见。
尽管这些名称不在签名的作用域内，它们也不会被当作自动绑定的隐式参数插入。


:::example "互递声明块的作用域"
在互递声明块中定义的名称不在彼此的签名作用域内。

```lean +error (name := mutScope) -keep
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
Unknown identifier `NaturalNum`
```

若不使用互递块，该定义即可通过：
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
:::


:::example "互递块的作用域与自动隐式参数"
在互递声明块中定义的名称不在彼此的签名作用域内。不过，它们也不能作为自动绑定的隐式参数使用：

```lean +error (name := mutScopeTwo) -keep
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
Unknown identifier `α`
```

若改用不同的名称，则会自动添加该隐式参数：
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
:::


递归定义的精译总是在互递块这一粒度上进行；即便某个声明并不处在互递块中，也会好比其周围包了一层单元素的互递块。
通过 {keywordOf Lean.Parser.Term.letrec}`let rec` 与
{keywordOf Lean.Parser.Command.declaration}`where` 引入的局部定义会被从其上下文提升出去；必要时为捕获到的自由变量引入参数；并被视作 {keywordOf Lean.Parser.Command.mutual}`mutual` 块中的独立定义。 {TODO}[在此处或项相关章节中更详细地解释这一机制。]
因此，写在 {keywordOf Lean.Parser.Command.declaration}`where` 块中的辅助定义，既可以彼此互递归，也可以和所在的主体定义互递归，但它们不能在彼此的类型签名中相互引用。

在精译的第一步结束后（此时定义仍是递归的），在使用上述技术消解递归之前，Lean 会在互递块中的这些定义里识别出真正（互相）递归的团簇{TODO}[定义这一术语，它很有用]，并按照依赖顺序分别处理它们。

{include 0 Manual.RecursiveDefs.Structural}

{include 0 Manual.RecursiveDefs.WF}

{include 0 Manual.RecursiveDefs.PartialFixpoint}

{include 0 Manual.RecursiveDefs.CoinductivePredicates}

# 偏定义与不安全定义
%%%
tag := "partial-unsafe"
%%%



大多数 Lean 函数既可在 Lean 的类型论中进行推理，也可被编译并运行；但凡被标记为 {keyword}`partial` 或 {keyword}`unsafe` 的定义，则无法在逻辑层面进行有意义的推理。
从逻辑视角看，{keyword}`partial` 函数是不透明常量；而凡是引用 {keyword}`unsafe` 定义的定理都会被直接拒绝。
作为无法用于推理的交换条件，这些定义受到的约束大幅减少：这使得一些原本不切实际或成本过高而难以给出证明的程序仍然可以编写，同时又不牺牲其余部分的形式化推理。
本质上，Lean 的 {keyword}`partial` 子集是一种传统的函数式编程语言，但与定理证明功能深度集成；而 {keyword}`unsafe` 子集则在少数情形下允许打破 Lean 的运行时不变式，但相应地与定理证明功能的集成程度较低。
类似地，{keyword}`noncomputable` 定义可以使用在程序中不合语义、但在逻辑中有意义的特性。

## 偏函数
%%%
tag := "partial-functions"
%%%


{keyword}`partial` 修饰符只能用于函数定义。
偏函数无需展示终止性，Lean 也不会尝试证明它终止。
之所以称为“偏”，是因为它们未必为定义域中的每个元素指定到余域元素的映射：对某些（乃至所有）输入，它们可能无法终止。
这类定义会被精译为包含显式递归的 {tech (key := "pre-definitions")}[预定义] 并由内核进行类型检查；不过在逻辑层面它们随后会被当作不透明常量。

函数的返回类型必须是可被占据的；这可确保自洽性。
否则，偏函数就可能拥有诸如 {lean}`Unit → Empty` 的类型。
结合 {name}`Empty.elim`，即便该函数并不归约，也可以据此“证明” {lean}`False`。

对于偏定义，内核负责以下检查：
* 确认预定义的类型确为一个良构类型；
* 确认预定义的类型是函数类型；
* 通过需求 {lean}`Nonempty` 或 {lean}`Inhabited` 实例，确保函数的余域是可被占据的；
* 在“假设 Lean 拥有递归定义”的前提下，检查生成项会通过类型检查。

尽管递归定义不是内核类型论的一部分，仍然可以用内核来检查定义体是否具有正确的类型。
其工作方式与其他函数式语言相同：在一个“该定义已与其类型绑定”的环境中检查定义体，从而为递归的使用做类型检查。
一旦确认通过类型检查，定义体会被丢弃，内核仅保留那个不透明常量。
与所有 Lean 函数一样，编译器会基于精译得到的 {tech (key := "pre-definitions")}[预定义] 生成代码。

即便内核不会对偏函数展开，仍可以在不依赖其具体实现的前提下，对调用它们的其他函数开展推理。


:::example "证明中的偏函数"
递归函数 {name}`nextPrime` 通过对候选数做试除测试来计算给定数之后的下一个素数，这样的做法效率不高。
由于素数是无限多的，它总是会终止；然而要正式给出这一点的证明并不容易，因此它被标记为 {keyword}`partial`。

```lean
def isPrime (n : Nat) : Bool := Id.run do
  for i in [2:n] do
    if i * i > n then return true
    if n % i = 0 then return false
  return true

partial def nextPrime (n : Nat) : Nat :=
  let n := n + 1
  if isPrime n then n else nextPrime n
```

尽管如此，仍然可以证明下面两个函数是相等的：
```lean
def answerUser (n : Nat) : String :=
  s!"The next prime is {nextPrime n}"

def answerOtherUser (n : Nat) : String :=
  " ".intercalate [
    "The",
    "next",
    "prime",
    "is",
    toString (nextPrime n)
  ]
```
事实上，该证明只需使用 {tactic}`rfl`：

```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
  rfl
```
:::

## 不安全定义
%%%
tag := "unsafe"
%%%


不安全定义的保障比偏函数更少。
它们的余域不必是可被占据的，且不限于函数定义；同时还能使用一些可能违反内部不变式或破坏抽象的 Lean 特性。
因此，它们完全不能用作数学推理的一部分。

类型论会把偏函数当作不透明常量处理；而不安全定义只能被其他不安全定义引用。
因此，任何调用了不安全函数的函数本身也必须是不安全的；定理则不允许被声明为不安全。

除了不受限制地使用递归之外，不安全函数还能在类型间强制转换、检查两个值是否为内存中的同一对象、读取指针值、以及在原本纯净的代码中运行 {lean}`IO` 动作。
使用这些算子需要对 Lean 的实现有深入理解。

{zhdocstring unsafeCast ZhDoc.RecursiveDefs.unsafeCast}

{zhdocstring ptrEq ZhDoc.RecursiveDefs.ptrEq}

{zhdocstring ptrEqList ZhDoc.RecursiveDefs.ptrEqList}

{zhdocstring ptrAddrUnsafe ZhDoc.RecursiveDefs.ptrAddrUnsafe}

{zhdocstring isExclusiveUnsafe ZhDoc.RecursiveDefs.isExclusiveUnsafe}

{zhdocstring unsafeIO ZhDoc.RecursiveDefs.unsafeIO}

{zhdocstring unsafeEIO ZhDoc.RecursiveDefs.unsafeEIO}

{zhdocstring unsafeBaseIO ZhDoc.RecursiveDefs.unsafeBaseIO}



不安全算子经常被用来利用底层细节编写高性能代码。
类似于通过 FFI 在运行时用 C 代码替换 Lean 代码的方式，{TODO}[添加交叉引用] 也可以在运行时程序中用不安全 Lean 代码替换安全 Lean 代码。
这可以通过在待替换的函数（通常是 {keyword}`opaque` 定义）上添加 {attr}`implemented_by` 属性来实现。
这并不会威胁 Lean 作为逻辑的自洽性：被替换的常量已通过内核检查，而不安全替代仅用于运行时代码。
但这仍然是有风险的——无论是 C 代码还是不安全代码，都可能执行任意副作用。


:::syntax attr (title := "替换运行时实现")
{attr}`implemented_by` 属性指示编译器在已编译代码中将某个常量替换为另一个常量。
被替换上去的常量可以是不安全的。
```grammar
implemented_by $_:ident
```
:::


:::example "使用指针检查相等性"

通常，{lean}`BEq` 实例的相等判定需要完全遍历两个参数以判断它们是否相等。
如果它们其实就是内存中的同一个对象，这样的遍历就显得很浪费。
在遍历之前先做一次指针相等性测试，可以尽早捕获这种情况。

比较的类型是 {name}`Tree`（二叉树）：
```lean
inductive Tree α where
  | empty
  | branch (left : Tree α) (val : α) (right : Tree α)
```

一个不安全函数可以用指针相等来更快地结束结构相等性测试；当指针不相等时，再回退到结构检查：
```lean
unsafe def Tree.fastBEq [BEq α] (t1 t2 : Tree α) : Bool :=
  if ptrEq t1 t2 then
    true
  else
    match t1, t2 with
    | .empty, .empty => true
    | .branch l1 x r1, .branch l2 y r2 =>
      if ptrEq x y || x == y then
        l1.fastBEq l2 && r1.fastBEq r2
      else false
    | _, _ => false
```

在一个不透明定义上添加 {attr}`implemented_by` 属性，就能在安全与不安全代码之间搭桥：
```lean
@[implemented_by Tree.fastBEq]
opaque Tree.beq [BEq α] (t1 t2 : Tree α) : Bool

instance [BEq α] : BEq (Tree α) where
  beq := Tree.beq
```
:::


::::example "利用运行时表示"

由于 {name}`Fin` 与其底层的 {name}`Nat` 具有相同的运行时表示，{lean}`List.map Fin.val` 可以用 {name}`unsafeCast` 来替换，从而避免一次在实践中“什么也没做”的线性时间遍历：
```lean
unsafe def unFinImpl (xs : List (Fin n)) : List Nat :=
  unsafeCast xs

@[implemented_by unFinImpl]
def unFin (xs : List (Fin n)) : List Nat :=
  xs.map Fin.val
```

:::paragraph
从 Lean 内核的视角看，{lean}`unFin` 是用 {name}`List.map` 定义的：
```lean
theorem unFin_length_eq_length {xs : List (Fin n)} :
    (unFin xs).length = xs.length := by
  simp [unFin]
```
在已编译代码中，则不会发生对该列表的遍历。
:::

这种替换方式具有风险：证明与已编译代码之间的一致性完全依赖于两个实现的等价性，而这点无法在 Lean 中证明。
这种一致性依赖 Lean 实现层面的细节。
这些“逃逸舱门”应当非常谨慎地使用。
::::

# 控制归约
%%%
tag := "reducibility"
htmlSplit := .never
%%%


在检查证明与程序时，Lean 会考虑 {deftech (key := "reducibility")}_可约性_，它也称为_透明性_。
定义的可约性决定精译和证明执行过程中可以在哪些上下文展开它。

可约性分为五个等级：

: {deftech (key := "irreducible")}[不可约]

  在精译过程中，不可约定义完全不会被展开。
  对定义应用 {attr}`irreducible` 属性可使其不可约。

: {deftech (key := "semireducible")}[半可约]

  半可约定义不会被类型类实例合成或 {tactic}`simp` 等潜在代价较高的自动化过程展开，但在检查定义相等性和解析{tech (key := "generalized field notation")}[广义字段记法]时会展开。
  {keywordOf Lean.Parser.Command.declaration}`def` 命令通常创建半可约定义，除非属性指定了不同等级；不过，采用{tech (key := "well-founded recursion")}[良基递归]的定义默认不可约。

: {deftech (key := "implicit reducible")}[隐式参数可约]

  检查函数隐式实参的{tech (key := "definitional equality")}[定义相等性]时，会展开隐式参数可约的定义。
  这里的隐式实参包括普通{tech (key := "implicit")}[隐式]实参、{tech (key := "instance implicit")}[实例隐式]实参和{tech (key := "strict implicit")}[严格隐式]实参。
  如果某个定义出现在隐式实参的类型中，并且预期它能够归约，就应将其设为隐式参数可约。

: {deftech (key := "instance reducible")}[实例可约]

  类型类{tech (key := "synthesis")}[实例合成]期间会展开实例可约的定义。
  所有类型类实例都应当是实例可约或完全可约的。
  由 {keywordOf Lean.Parser.Command.instance}`instance` 命令创建的实例会自动标记为实例可约。

: {deftech (key := "reducible")}[可约]

  可约定义几乎会在所有场合按需展开。
  类型类实例合成、定义相等性检查以及语言的其余部分，基本都会把这种定义视作缩写。
  {keywordOf Lean.Parser.Command.declaration}`abbrev` 命令创建的定义采用这一等级。

:::example "可约性与实例合成"
下面这三个 {lean}`String` 的别名分别是可约、半可约与不可约：

```lean
abbrev Phrase := String

def Clause := String

@[irreducible]
def Utterance := String
```

在精译器进行定义相等检查时，可约与半可约别名会被展开，从而被视为与 {lean}`String` 等价：
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"
```
相对地，不可约别名不会在定义相等测试中被展开，因此作为字符串的类型会被拒绝：
```lean +error (name := irred)

def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
Type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```

由于 {lean}`Phrase` 是可约的，{inst}`ToString String` 实例可被当作 {inst}`ToString Phrase` 实例来用：
```lean
#synth ToString Phrase
```

然而 {lean}`Clause` 是半可约的，因此不能直接使用 {inst}`ToString String` 实例：
```lean +error (name := toStringClause)

#synth ToString Clause
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

可以显式启用该实例：构造一个会化简为 {lean}`ToString String` 实例的 {lean}`ToString Clause` 实例。
该示例之所以可行，是因为在进行定义相等检查时会展开半可约定义：
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
```
:::



:::example "可约性与广义字段记法"
在查找匹配名称时，{tech (key := "generalized field notation")}[广义字段记法] 会展开可约与半可约的声明。
给定 {name}`List` 的一个半可约别名 {name}`Sequence`：
```lean
def Sequence := List

def Sequence.ofList (xs : List α) : Sequence α := xs
```
广义字段记法允许从类型为 {lean}`Sequence Nat` 的项上访问 {name}`List.reverse`：
```lean
#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```

然而，一旦将 {name}`Sequence` 声明为不可约，就会阻止展开：
```lean +error (name := irredSeq)

attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`, so it is not possible to project the field `reverse` from an expression
  xs
of type `Sequence Nat`
```
:::

:::syntax attr (title := "可约性标注")
可以使用如下五种可约性属性之一来设置某个定义的可约性：


```grammar
reducible
```
```grammar
instance_reducible
```
```grammar
implicit_reducible
```
```grammar
semireducible
```
```grammar
irreducible
```
这些属性只能在被修改定义所在的同一文件中全局应用；不过，它们也可以在任意位置以 {keywordOf attrInst (parser := Lean.Parser.Term.attrKind)}`local` 方式应用。

:::

## 可约性与策略
%%%
tag := "The-Lean-Language-Reference--Definitions--Recursive-Definitions--Controlling-Reduction--Reducibility-and-Tactics"
%%%


下面这些策略可控制大多数策略会展开哪些定义：{tactic}`with_reducible`、{tactic}`with_reducible_and_instances` 与 {tactic}`with_unfolding_all`。


:::example "可约性与策略"
函数 {lean}`plus`、{lean}`sum` 与 {lean}`tally` 都是 {lean}`Nat.add` 的同义名，且分别为可约、半可约与不可约：

```lean
abbrev plus := Nat.add

def sum := Nat.add

@[irreducible]
def tally := Nat.add
```

可约同义名会被 {tactic}`simp` 展开：
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```

半可约同义名则不会被 {tactic}`simp` 展开：
```lean -keep +error (name := simpSemi)

theorem sum_eq_add : sum x y = x + y := by simp
```
不过，由 {tactic}`rfl` 触发的定义相等检查会展开 {lean}`sum`：
```lean
theorem sum_eq_add : sum x y = x + y := by rfl
```
不可约的 {lean}`tally` 不会被定义相等所化简。
```lean  -keep +error (name := reflIr)
theorem tally_eq_add : tally x y = x + y := by rfl
```
当显式提供时，{tactic}`simp` 可以展开任意定义，甚至包括不可约的：
```lean  -keep (name := simpName)

theorem tally_eq_add : tally x y = x + y := by simp [tally]
```
类似地，可将证明的一部分放入 {tactic}`with_unfolding_all` 块中以忽略不可约性：
```lean
theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
```
:::

:::example "可约性与隐式实参"
函数 {lean}`plus`、{lean}`sum` 与 {lean}`tally` 都是 {lean}`Nat.add` 的同义名，且分别为可约、实例可约与不可约：
```lean
abbrev plus := Nat.add

@[instance_reducible]
def sum := Nat.add

def tally := Nat.add
```

{name}`Nonzero` 的实例包含一个给定数字不等于零的证明。
函数 {name}`notZero` 从合成得到的实例中提取该证明：
```lean
class Nonzero (n : Nat) where
  non_zero : n ≠ 0

instance Nonzero.instSucc : Nonzero (n + 1) where
  non_zero := by grind

def notZero (n : Nat) [Nonzero n] : n ≠ 0 := Nonzero.non_zero
```

对于可约定义 {name}`plus`，可以找到该实例：
```lean
#check notZero (plus 2 2)
```
对于实例可约定义 {name}`sum`，同样可以找到该实例。
这是因为类型 {lean}`Nonzero (sum 2 2)` 是 {name}`notZero` 的一个 {tech (key := "instance implicit")}[实例隐式]参数的类型。
具体而言，{name}`sum` 会归约为本身也是实例可约的 {name}`Nat.add`，因此该类型会归约为 {lean}`Nonzero 4`：
```lean
#check notZero (sum 2 2)
```

由于 {name}`tally` 不会被归约，其实例合成会失败：
```lean +error (name := notZeroTally)
#check notZero (tally 2 2)
```
```leanOutput notZeroTally
failed to synthesize instance of type class
  Nonzero (tally 2 2)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

在其他上下文中，例如调用 {tactic}`simp` 时，{name}`plus` 会被展开：
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```

不过，实例可约的同义名不会被 {tactic}`simp` 展开：
```lean -keep +error (name := simpInst)
theorem sum_eq_add : sum x y = x + y := by simp
```
```leanOutput simpInst
`simp` made no progress
```

:::


## 修改可约性
%%%
tag := "The-Lean-Language-Reference--Definitions--Recursive-Definitions--Controlling-Reduction--Modifying-Reducibility"
%%%


可以在定义所在的模块中，使用 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令施加相应属性，从而全局修改某个定义的可约性。
在其他模块中，可通过带 {keyword}`local` 修饰符的属性应用来修改已导入定义的可约性。
{keywordOf Lean.Parser.commandSeal__}`seal` 与 {keywordOf Lean.Parser.commandUnseal__}`unseal` 命令是该流程的便捷写法。


:::syntax command (title := "局部不可约性")

{zhincludeDocstring Lean.Parser.commandSeal__ ZhDoc.RecursiveDefs.Parser.commandSeal__}

```grammar
seal $_:ident $_*
```
:::


:::syntax command (title := "局部可约性")
{zhincludeDocstring Lean.Parser.commandUnseal__ ZhDoc.RecursiveDefs.Parser.commandUnseal__}

```grammar
unseal $_:ident $_*
```

:::

## 选项
%%%
tag := "The-Lean-Language-Reference--Definitions--Recursive-Definitions--Controlling-Reduction--Options"
%%%


出于性能考虑，精译器与许多策略会构建索引与缓存。
其中不少会考虑可约性；而一旦全局改变了可约性，就无法使这些索引/缓存失效并重新生成。
默认情况下，会禁止对可约性进行可能带来不可预测结果的不安全修改；不过，可通过 {option}`allowUnsafeReducibility` 选项启用之。

{zhOptionDocs allowUnsafeReducibility ZhDoc.RecursiveDefs.Option.allowUnsafeReducibility}
