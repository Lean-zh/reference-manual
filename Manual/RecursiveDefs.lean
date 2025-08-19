/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.RecursiveDefs.Structural
import Manual.RecursiveDefs.WF
import Manual.RecursiveDefs.PartialFixpoint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode



#doc (Manual) "Recursive Definitions" =>
%%%
tag := "recursive-definitions"
file := "Recursive Definitions"
%%%

-- Allowing arbitrary recursive function definitions would make Lean's logic inconsistent.
-- General recursion makes it possible to write circular proofs: "{tech}[proposition] $`P` is true because proposition $`P` is true".
-- Outside of proofs, an infinite loop could be assigned the type {name}`Empty`, which can be used with {keywordOf Lean.Parser.Term.nomatch}`nomatch` or {name Empty.rec}`Empty.rec` to prove any theorem.
--
-- Banning recursive function definitions outright would render Lean far less useful: {tech}[inductive types] are key to defining both predicates and data, and they have a recursive structure.
-- Furthermore, most useful recursive functions do not threaten soundness, and infinite loops usually indicate mistakes in definitions rather than intentional behavior.
-- Instead of banning recursive functions, Lean requires that each recursive function is defined safely.
-- While elaborating recursive definitions, the Lean elaborator also produces a justification that the function being defined is safe.{margin}[The section on {ref "elaboration-results"}[the elaborator's output] in the overview of elaboration contextualizes the elaboration of recursive definitions in the overall context of the elaborator.]

允许任意递归函数定义会使 Lean 的逻辑不一致。一般递归使得可以写出环形证明：“{tech key := "proposition"}[命题] $`P` 为真，因为命题 $`P` 为真”。在证明之外，一个无限循环可以被赋予类型 {name}`Empty`，再结合 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 或 {name Empty.rec}`Empty.rec`，即可“证明”任意定理。

直接禁止递归函数定义将大幅降低 Lean 的实用性：{tech key := "inductive types"}[归纳类型] 是定义谓词与数据的关键，而它们本身具有递归结构。此外，多数有用的递归函数并不威胁自洽性，而无限循环通常意味着定义有误而非有意为之。Lean 并未一禁了之，而是要求每个递归函数都以安全的方式定义。在繁释递归定义的过程中，Lean 的繁释器还会同时给出该定义安全的理由。{margin}[可参阅繁释概览中的 {ref "elaboration-results"}[繁释器的输出] 一节，了解递归定义繁释在整体繁释流程中的位置。]

-- There are five main kinds of recursive functions that can be defined:
--
-- : Structurally recursive functions
--
--   Structurally recursive functions take an argument such that the function makes recursive calls only on strict sub-components of said argument.{margin}[Strictly speaking, arguments whose types are {tech}[indexed families] are grouped together with their indices, with the whole collection considered as a unit.]
--   The elaborator translates the recursion into uses of the argument's {tech}[recursor].
--   Because every type-correct use of a recursor is guaranteed to avoid infinite regress, this translation is evidence that the function terminates.
--   Applications of functions defined via recursors are definitionally equal to the result of the recursion, and are typically relatively efficient inside the kernel.

可以定义的递归函数主要有五类：

: 结构化递归函数

  结构化递归函数接收某个实参，并且仅在该实参的真子项上进行递归调用。{margin}[严格来说，类型为 {tech key := "indexed families"}[索引族] 的实参会与其索引成组，把整个集合视作一个整体。]
  繁释器会把递归翻译成对该实参的 {tech key := "recursor"}[递归器] 的调用。
  由于每个类型正确的递归器使用都保证避免无限回归，这样的翻译即构成函数终止性的证据。
  通过递归器定义的函数应用在定义上等同于递归结果，并且在内核中通常较为高效。

-- : Recursion over well-founded relations
--
--   Many functions are also difficult to convert to structural recursion; for instance, a function may terminate because the difference between an array index and the size of the array decreases as the index increases, but {name}`Nat.rec` isn't applicable because the index that increases is the function's argument.
--   Here, there is a {tech}[measure] of termination that decreases at each recursive call, but the measure is not itself an argument to the function.
--   In these cases, {tech}[well-founded recursion] can be used to define the function.
--   Well-founded recursion is a technique for systematically transforming recursive functions with a decreasing measure into recursive functions over proofs that every sequence of reductions to the measure eventually terminates at a minimum.
--   Applications of functions defined via well-founded recursion are not necessarily definitionally equal to their return values, but this equality can be proved as a proposition.
--   Even when definitional equalities exist, these functions are frequently slow to compute with because they require reducing proof terms that are often very large.

: 良构关系上的递归

  有些函数也难以改写为结构化递归；例如，某个函数之所以终止，是因为随着数组索引增大，索引与数组长度之差在减小，但此时由于增长的是函数的实参本身，{name}`Nat.rec` 并不适用。
  在这种情形下，存在一个随每次递归调用而减少的终止{tech key := "measure"}[度量]，但该度量本身并非函数的一个实参。
  这时可以使用 {tech key := "well-founded recursion"}[良构递归] 来定义函数。
  良构递归是一种技术：系统地把“伴随度量递减的递归函数”转化为“基于证明的递归函数”，该证明表明任意度量递减序列最终会在最小值处终止。
  用良构递归定义的函数应用不一定与其返回值在定义上相等，但这种相等可以作为命题来证明。
  即便存在定义相等，这类函数在计算上仍常常较慢，因为它们需要归约通常很大的证明项。

-- : Recursive functions as partial fixpoints
--
--   The definition of a function can be understood as an equation that specifies its behavior.
--   In certain cases, the existence of a function that satisfies this specification can be proven even when the recursive function does not necessarily terminate for all inputs.
--   This strategy is even applicable in some cases where the function definition does not necessarily terminate for all inputs.
--   These partial functions emerge as fixed points of these equations are called {tech}_partial fixpoints_.
--
--   In particular, any function whose return type is in certain monads (e.g. {name}`Option`) can be defined using this strategy.
--   Lean generates additional partial correctness theorems for these monadic functions.
--   As with well-founded recursion, applications of functions defined as partial fixpoints are not definitionally equal to their return values, but Lean generates theorems that propositionally equate the function to its unfolding and to the reduction behavior specified in its definition.

: 作为偏不动点的递归函数

  一个函数的定义可以理解为一条给出其行为的方程。
  在某些情况下，即使该递归函数对所有输入未必终止，仍可证明存在一个满足此规格的函数。
  该策略甚至适用于某些函数定义对所有输入未必终止的情形。
  由此得到的偏函数作为这些方程的不动点而出现，被称为 {tech key := "partial fixpoints"}[偏不动点]。

  尤其是，返回类型位于某些单子中的函数（例如 {name}`Option`）可以用该策略来定义。
  对这类单子函数，Lean 还会生成额外的偏正确性定理。
  与良构递归类似，按偏不动点定义的函数应用在定义上不等同于其返回值，但 Lean 会生成定理，在命题层面将该函数与其展开式以及定义中所给的归约行为相等同。

-- : Partial functions with nonempty codomains
--
--   For many applications, it's not important to reason about the implementation of certain functions.
--   A recursive function might be used only as part of the implementation of proof automation steps, or it might be an ordinary program that will never be formally proved correct.
--   In these cases, the Lean kernel does not need either definitional or propositional equalities to hold for the definition; it suffices that soundness is maintained.
--   Functions marked {keywordOf Lean.Parser.Command.declaration}`partial` are treated as opaque constants by the kernel and are neither unfolded nor reduced.
--   All that is required for soundness is that their return type is inhabited.
--   Partial functions may still be used in compiled code as usual, and they may appear in propositions and proofs; their equational theory in Lean's logic is simply very weak.

: 余域非空的偏函数

  在许多应用中，某些函数的具体实现并不需要被推理。
  一个递归函数可能仅作为证明自动化步骤实现的一部分，或仅是不会被形式化证明正确性的普通程序。
  在这类场景中，Lean 内核不需要该定义在“定义相等”或“命题相等”层面成立；只要保持逻辑自洽即可。
  被标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数会被内核视作不透明常量，既不会被展开也不会被归约。
  为保持自洽性，唯一的要求是其返回类型可被占据（inhabited）。
  偏函数在编译后的代码中仍可照常使用，也可出现在命题与证明中；只是它们在 Lean 逻辑中的等式理论非常薄弱。

-- : Unsafe recursive definitions
--
--   Unsafe definitions have none of the restrictions of partial definitions.
--   They may freely make use of general recursion, and they may use features of Lean that break assumptions about its equational theory, such as primitives for casting ({name}`unsafeCast`), checking pointer equality ({name}`ptrAddrUnsafe`), and observing {tech}[reference counts] ({name}`isExclusiveUnsafe`).
--   However, any declaration that refers to an unsafe definition must itself be marked {keywordOf Lean.Parser.Command.declaration}`unsafe`, making it clear when logical soundness is not guaranteed.
--   Unsafe operations can be used to replace the implementations of other functions with more efficient variants in compiled code, while the kernel still uses the original definition.
--   The replaced function may be opaque, which results in the function name having a trivial equational theory in the logic, or it may be an ordinary function, in which case the function is used in the logic.
--   Use this feature with care: logical soundness is not at risk, but the behavior of programs written in Lean may diverge from their verified logical models if the unsafe implementation is incorrect.

: 不安全的递归定义

  不安全定义不受偏定义的任何限制。
  它们可自由使用一般递归，并可使用会打破等式理论假设的 Lean 特性，例如强制转换原语（{name}`unsafeCast`）、检查指针相等（{name}`ptrAddrUnsafe`），以及观察{tech key := "reference counts"}[引用计数]（{name}`isExclusiveUnsafe`）。
  但凡引用不安全定义的声明本身也必须标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe`，以清楚表明此处不保证逻辑自洽。
  在编译后的代码中，不安全操作可用于以更高效的实现替换其他函数的实现，而内核仍然使用原始定义。
  被替换的函数可以是不透明的，此时该函数名在逻辑中的等式理论是平凡的；也可以是普通函数，此时逻辑中仍会使用该函数。
  请谨慎使用这一特性：逻辑自洽性虽不受威胁，但若不安全实现有误，Lean 程序的实际行为可能会偏离其经验证的逻辑模型。

-- :::TODO
--
-- Table providing an overview of all strategies and their properties
--
-- :::

:::TODO

总览所有策略及其性质的表格

:::

-- As described in the {ref "elaboration-results"}[overview of the elaborator's output], elaboration of recursive functions proceeds in two phases:
--  1. The definition is elaborated as if Lean's core type theory had recursive definitions.
--     Aside from using recursion, this provisional definition is fully elaborated.
--     The compiler generates code from these provisional definitions.
--
--  2. A termination analysis attempts to use the four techniques to justify the function to Lean's kernel.
--     If the definition is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` or {keywordOf Lean.Parser.Command.declaration}`partial`, then that technique is used.
--     If an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by` clause is present, then the indicated technique is the only one attempted.
--     If there is no such clause, then the elaborator performs a search, testing each parameter to the function as a candidate for structural recursion, and attempting to find a measure with a well-founded relation that decreases at each recursive call.
--
-- This section describes the rules that govern recursive functions.
-- After a description of mutual recursion, each of the five kinds of recursive definitions is specified, along with the tradeoffs between reasoning power and flexibility that go along with each.

如 {ref "elaboration-results"}[繁释器输出概览] 所述，递归函数的繁释分两阶段进行：
 1. 首先，按“Lean 的核心类型论自带递归定义”的假想来繁释该定义。除了使用递归之外，这个临时定义会被完全繁释。编译器会基于这些临时定义生成代码。

 2. 随后进行终止性分析，尝试用四种技术之一向 Lean 内核证明该函数是可接受的。若定义被标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe` 或 {keywordOf Lean.Parser.Command.declaration}`partial`，则直接采用相应技术。若给出了显式的 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句，则只尝试其中指明的技术。若无此类子句，繁释器会进行搜索：依次尝试将每个形参作为结构化递归的候选，并尝试寻找某个随每次递归调用而减少、且具良构关系的度量。

本节描述支配递归函数的规则。介绍互递归之后，将逐一给出这五类递归定义的规范，并讨论各自的推理能力与灵活性之间的权衡。

# Mutual Recursion
%%%
tag := "mutual-syntax"
%%%

-- Just as a recursive definition is one that mentions the name being defined in the body of the definition, {deftech}_mutually recursive_ definitions are definitions that may be recursive or mention one another.
-- To use mutual recursion between multiple declarations, they must be placed in a {deftech}[mutual block].

就像递归定义是在其定义体中提到正在被定义的名字一样，{deftech key := "mutually recursive"}_互递归_ 的定义指的是：它们本身可以是递归的，或彼此相互引用。
要在多个声明之间使用互递归，必须把它们放入一个 {deftech key := "mutual block"}[互递归块] 中。

-- :::syntax command (title := "Mutual Declaration Blocks")
-- The general syntax for mutual recursion is:
--
-- ```grammar
-- mutual
--   $[$declaration:declaration]*
-- end
-- ```
-- where the declarations must be definitions or theorems.
-- :::

:::syntax command (title := "互递声明块")
互递的一般语法为：

```grammar
mutual
  $[$declaration:declaration]*
end
```
其中各声明必须是定义或定理。
:::

-- The declarations in a mutual block are not in scope in each others' signatures, but they are in scope in each others' bodies.
-- Even though the names are not in scope in signatures, they will not be inserted as auto-bound implicit parameters.

在一个互递声明块中，各声明的名称不在彼此的类型签名的作用域内，但在彼此的定义体中可见。
尽管这些名称不在签名的作用域内，它们也不会被当作自动绑定的隐式参数插入。

-- :::example "Mutual Block Scope"
-- Names defined in a mutual block are not in scope in each others' signatures.
--
-- ```lean (error := true) (name := mutScope) (keep := false)
-- mutual
--   abbrev NaturalNum : Type := Nat
--   def n : NaturalNum := 5
-- end
-- ```
-- ```leanOutput mutScope
-- unknown identifier 'NaturalNum'
-- ```
--
-- Without the mutual block, the definition succeeds:
-- ```lean
-- abbrev NaturalNum : Type := Nat
-- def n : NaturalNum := 5
-- ```
-- :::

:::example "互递声明块的作用域"
在互递声明块中定义的名称不在彼此的签名作用域内。

```lean (error := true) (name := mutScope) (keep := false)
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
unknown identifier 'NaturalNum'
```

若不使用互递块，该定义即可通过：
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
:::

-- :::example "Mutual Block Scope and Automatic Implicit Parameters"
-- Names defined in a mutual block are not in scope in each others' signatures.
-- Nonetheless, they cannot be used as automatic implicit parameters:
--
-- ```lean (error := true) (name := mutScopeTwo) (keep := false)
-- mutual
--   abbrev α : Type := Nat
--   def identity (x : α) : α := x
-- end
-- ```
-- ```leanOutput mutScopeTwo
-- unknown identifier 'α'
-- ```
--
-- With a different name, the implicit parameter is automatically added:
-- ```lean
-- mutual
--   abbrev α : Type := Nat
--   def identity (x : β) : β := x
-- end
-- ```
-- :::

:::example "互递块的作用域与自动隐式参数"
在互递声明块中定义的名称不在彼此的签名作用域内。不过，它们也不能作为自动绑定的隐式参数使用：

```lean (error := true) (name := mutScopeTwo) (keep := false)
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
unknown identifier 'α'
```

若改用不同的名称，则会自动添加该隐式参数：
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
:::

-- Elaborating recursive definitions always occurs at the granularity of mutual blocks, as if there were a singleton mutual block around every declaration that is not itself part of such a block.
-- Local definitions introduced via {keywordOf Lean.Parser.Term.letrec}`let rec` and
--  {keywordOf Lean.Parser.Command.declaration}`where` are lifted out of their context, introducing parameters for captured free variables as necessary, and treated as if they were separate definitions within the {keywordOf Lean.Parser.Command.mutual}`mutual` block as well. {TODO}[Explain this mechanism in more detail, here or in the term section.]
-- Thus, helpers defined in a {keywordOf Lean.Parser.Command.declaration}`where` block may use mutual recursion both with one another and with the definition in which they occur, but they may not mention each other in their type signatures.
--
-- After the first step of elaboration, in which definitions are still recursive, and before translating recursion using the techniques above, Lean identifies the actually (mutually) recursive cliques{TODO}[define this term, it's useful]  among the definitions in the mutual block and processes them separately and in dependency order.

递归定义的繁释总是在互递块这一粒度上进行；即便某个声明并不处在互递块中，也会好比其周围包了一层单元素的互递块。
通过 {keywordOf Lean.Parser.Term.letrec}`let rec` 与
{keywordOf Lean.Parser.Command.declaration}`where` 引入的局部定义会被从其上下文提升出去；必要时为捕获到的自由变量引入参数；并被视作 {keywordOf Lean.Parser.Command.mutual}`mutual` 块中的独立定义。 {TODO}[Explain this mechanism in more detail, here or in the term section.]
因此，写在 {keywordOf Lean.Parser.Command.declaration}`where` 块中的辅助定义，既可以彼此互递归，也可以和所在的主体定义互递归，但它们不能在彼此的类型签名中相互引用。

在繁释的第一步结束后（此时定义仍是递归的），在使用上述技术消解递归之前，Lean 会在互递块中的这些定义里识别出真正（互相）递归的团簇{TODO}[define this term, it's useful]，并按照依赖顺序分别处理它们。

{include 0 Manual.RecursiveDefs.Structural}

{include 0 Manual.RecursiveDefs.WF}

{include 0 Manual.RecursiveDefs.PartialFixpoint}

# Partial and Unsafe Definitions
%%%
tag := "partial-unsafe"
%%%


-- While most Lean functions can be reasoned about in Lean's type theory as well as compiled and run, definitions marked {keyword}`partial` or {keyword}`unsafe` cannot be meaningfully reasoned about.
-- From the perspective of the logic, {keyword}`partial` functions are opaque constants, and theorems that refer to {keyword}`unsafe` definitions are summarily rejected.
-- In exchange for the inability to use these functions for reasoning, there are far fewer requirements placed on them; this can make it possible to write programs that would be impractical or cost-prohibitive to prove anything about, while not giving up formal reasoning for the rest.
-- In essence, the {keyword}`partial` subset of Lean is a traditional functional programming language that is nonetheless deeply integrated with the theorem proving features, and the {keyword}`unsafe` subset features the ability to break Lean's runtime invariants in certain rare situations, at the cost of less integration with Lean's theorem-proving features.
-- Analogously, {keyword}`noncomputable` definitions may use features that don't make sense in programs, but are meaningful in the logic.

大多数 Lean 函数既可在 Lean 的类型论中进行推理，也可被编译并运行；但凡被标记为 {keyword}`partial` 或 {keyword}`unsafe` 的定义，则无法在逻辑层面进行有意义的推理。
从逻辑视角看，{keyword}`partial` 函数是不透明常量；而凡是引用 {keyword}`unsafe` 定义的定理都会被直接拒绝。
作为无法用于推理的交换条件，这些定义受到的约束大幅减少：这使得一些原本不切实际或成本过高而难以给出证明的程序仍然可以编写，同时又不牺牲其余部分的形式化推理。
本质上，Lean 的 {keyword}`partial` 子集是一种传统的函数式编程语言，但与定理证明功能深度集成；而 {keyword}`unsafe` 子集则在少数情形下允许打破 Lean 的运行时不变式，但相应地与定理证明功能的集成程度较低。
类似地，{keyword}`noncomputable` 定义可以使用在程序中不合语义、但在逻辑中有意义的特性。

## Partial Functions
%%%
tag := "partial-functions"
%%%

-- The {keyword}`partial` modifier may only be applied to function definitions.
-- Partial functions are not required to demonstrate termination, and Lean does not attempt to do so.
-- These functions are “partial” in the sense that they do not necessarily specify a mapping from each element of the domain to an element of the codomain, because they might fail to terminate for some or all elements of the domain.
-- They are elaborated into {tech}[pre-definitions] that contain explicit recursion, and type checked using the kernel; however, they are subsequently treated as opaque constants by the logic.
--
-- The function's return type must be inhabited; this ensures soundness.
-- Otherwise, a partial function could have a type such as {lean}`Unit → Empty`.
-- Together with {name}`Empty.elim`, the existence of such a function could be used to prove {lean}`False` even if it does not reduce.
--
-- With partial definitions, the kernel is responsible for the following:
-- * It ensures that the pre-definition's type is indeed a well-formed type.
-- * It checks that the pre-definition's type is a function type.
-- * It ensures that the function's codomain is inhabited by demanding a {lean}`Nonempty` or {lean}`Inhabited` instance.
-- * It checks that the resulting term would be type-correct if Lean had recursive definitions.
--
-- Even though recursive definitions are not part of the kernel's type theory, the kernel can still be used to check that the body of the definition has the right type.
-- This works the same way as in other functional languages: uses of recursion are type checked by checking the body in an environment in which the definition is already associated with its type.
-- Having ensured that it type checks, the body is discarded and only the opaque constant is retained by the kernel.
-- As with all Lean functions, the compiler generates code from the elaborated {tech}[pre-definition].
--
-- Even though partial functions are not unfolded by the kernel, it is still possible to reason about other functions that call them so long as this reasoning doesn't depend on the implementation of the partial function itself.

{keyword}`partial` 修饰符只能用于函数定义。
偏函数无需展示终止性，Lean 也不会尝试证明它终止。
之所以称为“偏”，是因为它们未必为定义域中的每个元素指定到余域元素的映射：对某些（乃至所有）输入，它们可能无法终止。
这类定义会被繁释为包含显式递归的 {tech key := "pre-definitions"}[预定义] 并由内核进行类型检查；不过在逻辑层面它们随后会被当作不透明常量。

函数的返回类型必须是可被占据（inhabited）的；这可确保自洽性。
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
与所有 Lean 函数一样，编译器会基于繁释得到的 {tech key := "pre-definitions"}[预定义] 生成代码。

即便内核不会对偏函数展开，仍可以在不依赖其具体实现的前提下，对调用它们的其他函数开展推理。

-- :::example "Partial Functions in Proofs"
-- The recursive function {name}`nextPrime` inefficiently computes the next prime number after a given number by repeatedly testing candidates with trial division.
-- Because there are infinitely many prime numbers, it always terminates; however, formulating this proof would be nontrivial.
-- It is thus marked {keyword}`partial`.
--
-- ````lean
-- def isPrime (n : Nat) : Bool := Id.run do
--   for i in [2:n] do
--     if i * i > n then return true
--     if n % i = 0 then return false
--   return true
--
-- partial def nextPrime (n : Nat) : Nat :=
--   let n := n + 1
--   if isPrime n then n else nextPrime n
-- ````
--
-- It is nonetheless possible to prove that the following two functions are equal:
-- ```lean
-- def answerUser (n : Nat) : String :=
--   s!"The next prime is {nextPrime n}"
--
-- def answerOtherUser (n : Nat) : String :=
--   " ".intercalate [
--     "The",
--     "next",
--     "prime",
--     "is",
--     toString (nextPrime n)
--   ]
-- ```
-- The proof contains two {tactic}`simp` steps to demonstrate that the two functions are not syntactically identical.
-- In particular, the desugaring of string interpolation resulted in an extra {lean}`toString ""` at the end of {lean}`answerUser`'s result.
-- ```lean
-- theorem answer_eq_other : answerUser = answerOtherUser := by
--   funext n
--   simp only [answerUser, answerOtherUser]
--   simp only [toString, String.append_empty]
--   rfl
-- ```
-- :::

:::example "证明中的偏函数"
递归函数 {name}`nextPrime` 通过对候选数做试除测试来计算给定数之后的下一个素数，这样的做法效率不高。
由于素数是无限多的，它总是会终止；然而要正式给出这一点的证明并不容易，因此它被标记为 {keyword}`partial`。

````lean
def isPrime (n : Nat) : Bool := Id.run do
  for i in [2:n] do
    if i * i > n then return true
    if n % i = 0 then return false
  return true

partial def nextPrime (n : Nat) : Nat :=
  let n := n + 1
  if isPrime n then n else nextPrime n
````

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
证明包含两步 {tactic}`simp`，用来展示这两个函数在语法上并不相同。
尤其是，字符串插值的反糖导致 {lean}`answerUser` 的结果末尾多了一个 {lean}`toString ""`：
```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
  funext n
  simp only [answerUser, answerOtherUser]
  simp only [toString, String.append_empty]
  rfl
```
:::

## Unsafe Definitions
%%%
tag := "unsafe"
%%%

-- Unsafe definitions have even fewer safeguards than partial functions.
-- Their codomains do not need to be inhabited, they are not restricted to function definitions, and they have access to features of Lean that might violate internal invariants or break abstractions.
-- As a result, they cannot be used at all as part of mathematical reasoning.
--
-- While partial functions are treated as opaque constants by the type theory, unsafe definitions may only be referenced from other unsafe definitions.
-- As a consequence, any function that calls an unsafe function must be unsafe itself.
-- Theorems are not allowed to be declared unsafe.
--
-- In addition to unrestricted use of recursion, unsafe functions can cast from one type to another, check whether two values are the very same object in memory, retrieve pointer values, and run {lean}`IO` actions from otherwise-pure code.
-- Using these operators requires a thorough understanding of the Lean implementation.

不安全定义的保障比偏函数更少。
它们的余域不必是可被占据的，且不限于函数定义；同时还能使用一些可能违反内部不变式或破坏抽象的 Lean 特性。
因此，它们完全不能用作数学推理的一部分。

类型论会把偏函数当作不透明常量处理；而不安全定义只能被其他不安全定义引用。
因此，任何调用了不安全函数的函数本身也必须是不安全的；定理则不允许被声明为不安全。

除了不受限制地使用递归之外，不安全函数还能在类型间强制转换、检查两个值是否为内存中的同一对象、读取指针值、以及在原本纯净的代码中运行 {lean}`IO` 动作。
使用这些算子需要对 Lean 的实现有深入理解。

{docstring unsafeCast}

{docstring ptrEq (allowMissing := true)}

{docstring ptrEqList (allowMissing := true)}

{docstring ptrAddrUnsafe (allowMissing := true)}

{docstring isExclusiveUnsafe}

{docstring unsafeIO}

{docstring unsafeEIO}

{docstring unsafeBaseIO}


-- Frequently, unsafe operators are used to write fast code that takes advantage of low-level details.
-- Just as Lean code may be replaced at runtime with C code via the FFI,{TODO}[xref] safe Lean code may be replaced with unsafe Lean code for runtime programs.
-- This is accomplished by adding the {attr}`implemented_by` attribute to the function that is to be replaced, which is often an {keyword}`opaque` definition.
-- While this does not threaten Lean's soundness as a logic because the constant to be replaced has already been checked by the kernel and the unsafe replacement is only used in run-time code, it is still risky.
-- Both C code and unsafe code may execute arbitrary side effects.

不安全算子经常被用来利用底层细节编写高性能代码。
类似于通过 FFI 在运行时用 C 代码替换 Lean 代码的方式，{TODO}[xref] 也可以在运行时程序中用不安全 Lean 代码替换安全 Lean 代码。
这可以通过在待替换的函数（通常是 {keyword}`opaque` 定义）上添加 {attr}`implemented_by` 属性来实现。
这并不会威胁 Lean 作为逻辑的自洽性：被替换的常量已通过内核检查，而不安全替代仅用于运行时代码。
但这仍然是有风险的——无论是 C 代码还是不安全代码，都可能执行任意副作用。

-- :::syntax attr (title := "Replacing Run-Time Implementations")
-- The {attr}`implemented_by` attribute instructs the compiler to replace one constant with another in compiled code.
-- The replacement constant may be unsafe.
-- ```grammar
-- implemented_by $_:ident
-- ```
-- :::

:::syntax attr (title := "替换运行时实现")
{attr}`implemented_by` 属性指示编译器在已编译代码中将某个常量替换为另一个常量。
被替换上去的常量可以是不安全的。
```grammar
implemented_by $_:ident
```
:::

-- :::example "Checking Equality with Pointers"
--
-- Ordinarily, a {lean}`BEq` instance's equality predicate must fully traverse both of its arguments to determine whether they are equal.
-- If they are, in fact, the very same object in memory, this is wasteful indeed.
-- A pointer equality test can be used prior to the traversal to catch this case.
--
-- The type being compared is {name}`Tree`, a type of binary trees.
-- ```lean
-- inductive Tree α where
--   | empty
--   | branch (left : Tree α) (val : α) (right : Tree α)
-- ```
--
-- An unsafe function may use pointer equality to terminate the structural equality test more quickly, falling back to structural checks when pointer equality fails.
-- ```lean
-- unsafe def Tree.fastBEq [BEq α] (t1 t2 : Tree α) : Bool :=
--   if ptrEq t1 t2 then
--     true
--   else
--     match t1, t2 with
--     | .empty, .empty => true
--     | .branch l1 x r1, .branch l2 y r2 =>
--       if ptrEq x y || x == y then
--         l1.fastBEq l2 && r1.fastBEq r2
--       else false
--     | _, _ => false
-- ```
--
-- An {attr}`implemented_by` attribute on an opaque definition bridges the worlds of safe and unsafe code.
-- ```lean
-- @[implemented_by Tree.fastBEq]
-- opaque Tree.beq [BEq α] (t1 t2 : Tree α) : Bool
--
-- instance [BEq α] : BEq (Tree α) where
--   beq := Tree.beq
-- ```
-- :::

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

-- ::::example "Taking Advantage of Run-Time Representations"
--
-- Because a {name}`Fin` is represented identically to its underlying {name}`Nat`, {lean}`List.map Fin.val` can be replaced by {name}`unsafeCast` to avoid a linear-time traversal that, in practice, does nothing:
-- ```lean
-- unsafe def unFinImpl (xs : List (Fin n)) : List Nat :=
--   unsafeCast xs
--
-- @[implemented_by unFinImpl]
-- def unFin (xs : List (Fin n)) : List Nat :=
--   xs.map Fin.val
-- ```
--
-- :::paragraph
-- From the perspective of the Lean kernel, {lean}`unFin` is defined using {name}`List.map`:
-- ```lean
-- theorem unFin_length_eq_length {xs : List (Fin n)} :
--     (unFin xs).length = xs.length := by
--   simp [unFin]
-- ```
-- In compiled code, there is no traversal of the list.
-- :::
--
-- This kind of replacement is risky: the correspondence between the proof and the compiled code depends fully on the equivalence of the two implementations, which cannot be proved in Lean.
-- The correspondence relies on details of Lean's implementation.
-- These “escape hatches” should be used very carefully.
-- ::::

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

# Controlling Reduction
%%%
tag := "reducibility"
htmlSplit := .never
%%%

-- While checking proofs and programs, Lean takes {deftech}_reducibility_, also known as _transparency_, into account.
-- A definition's reducibility controls the contexts in which it is unfolded during elaboration and proof execution.

在检查证明与程序时，Lean 会考虑 {deftech key := "reducibility"}[可约性]（亦称“_透明性_”）。
某个定义的可约性决定了它在繁释与证明执行过程中会被展开的上下文。

-- There are three levels of reducibility:
--
-- : {deftech}[Reducible]
--
--   Reducible definitions are unfolded essentially everywhere, on demand.
--   Type class instance synthesis, definitional equality checks, and the rest of the language treat the definition as being essentially an abbreviation.
--   This is the setting applied by the {keywordOf Lean.Parser.Command.declaration}`abbrev` command.
--
-- : {deftech}[Semireducible]
--
--   Semireducible definitions are not unfolded by potentially expensive automation such as type class instance synthesis or {tactic}`simp`, but they are unfolded while checking definitional equality and while resolving {tech}[generalized field notation].
--   The {keywordOf Lean.Parser.Command.declaration}`def` command generally creates semireducible definitions unless a different reducibility level is specified with an attribute; however, definitions that use {tech}[well-founded recursion] are irreducible by default.
--
-- : {deftech}[Irreducible]
--
--   Irreducible definitions are not unfolded at all during elaboration.
--   Definitions can be made irreducible by applying the {attr}`irreducible` attribute.

可约性有三个层级：

: {deftech key := "Reducible"}[可约]

  可约定义基本在各处按需展开。
  类型类实例合成、定义相等性检查，以及语言中的其它机制都会将此类定义视为一种近似“缩写”的存在。
  {keywordOf Lean.Parser.Command.declaration}`abbrev` 命令即应用了这一设定。

: {deftech key := "Semireducible"}[半可约]

  半可约定义不会被潜在昂贵的自动化流程（如类型类实例合成或 {tactic}`simp`）展开，但在进行定义相等性检查或解析{tech key := "generalized field notation"}[广义字段记法]时会展开。
  {keywordOf Lean.Parser.Command.declaration}`def` 命令通常会创建半可约定义，除非通过属性显式指定了不同的可约性；不过，采用{tech key := "well-founded recursion"}[良构递归]的定义默认是不可约的。

: {deftech key := "Irreducible"}[不可约]

  不可约定义在繁释期间完全不会被展开。
  可通过添加 {attr}`irreducible` 属性将某个定义设为不可约。

-- :::example "Reducibility and Instance Synthesis"
-- These three aliasees for {lean}`String` are respectively reducible, semireducible, and irreducible.
-- ```lean
-- abbrev Phrase := String
--
-- def Clause := String
--
-- @[irreducible]
-- def Utterance := String
-- ```
--
-- The reducible and semireducible aliases are unfolded during the elaborator's definitional equality check, causing them to be considered equivalent to {lean}`String`:
-- ```lean
-- def hello : Phrase := "Hello"
--
-- def goodMorning : Clause := "Good morning"
-- ```
-- The irreducible alias, on the other hand, is rejected as the type for a string, because the elaborator's definitional equality test does not unfold it:
-- ```lean (error := true) (name := irred)
-- def goodEvening : Utterance := "Good evening"
-- ```
-- ```leanOutput irred
-- type mismatch
--   "Good evening"
-- has type
--   String : Type
-- but is expected to have type
--   Utterance : Type
-- ```
--
-- Because {lean}`Phrase` is reducible, the {inst}`ToString String` instance can be used as a {inst}`ToString Phrase` instance:
-- ```lean
-- #synth ToString Phrase
-- ```
--
-- However, {lean}`Clause` is semireducible, so the {inst}`ToString String` instance cannot be used:
-- ```lean (error := true) (name := toStringClause)
-- #synth ToString Clause
-- ```
-- ```leanOutput toStringClause
-- failed to synthesize
--   ToString Clause
--
-- Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- ```
--
-- The instance can be explicitly enabled by creating a {lean}`ToString Clause` instance that reduces to the {lean}`ToString String` instance.
-- This example works because semireducible definitions are unfolded while checking definitional equality:
-- ```lean
-- instance : ToString Clause := inferInstanceAs (ToString String)
-- ```
-- :::

:::example "可约性与实例合成"
下面这三个 {lean}`String` 的别名分别是可约、半可约与不可约：
```lean
abbrev Phrase := String

def Clause := String

@[irreducible]
def Utterance := String
```

在繁释器进行定义相等检查时，可约与半可约别名会被展开，从而被视为与 {lean}`String` 等价：
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"
```
相对地，不可约别名不会在定义相等测试中被展开，因此作为字符串的类型会被拒绝：
```lean (error := true) (name := irred)
def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
type mismatch
  "Good evening"
has type
  String : Type
but is expected to have type
  Utterance : Type
```

由于 {lean}`Phrase` 是可约的，{inst}`ToString String` 实例可被当作 {inst}`ToString Phrase` 实例来用：
```lean
#synth ToString Phrase
```

然而 {lean}`Clause` 是半可约的，因此不能直接使用 {inst}`ToString String` 实例：
```lean (error := true) (name := toStringClause)
#synth ToString Clause
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

可以显式启用该实例：构造一个会化简为 {lean}`ToString String` 实例的 {lean}`ToString Clause` 实例。
该示例之所以可行，是因为在进行定义相等检查时会展开半可约定义：
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
```
:::


-- :::example "Reducibility and Generalized Field Notation"
-- {tech}[Generalized field notation] unfolds reducible and semireducible declarations while searching for matching names.
-- Given the semireducible alias {name}`Sequence` for {name}`List`:
-- ```lean
-- def Sequence := List
--
-- def Sequence.ofList (xs : List α) : Sequence α := xs
-- ```
-- generalized field notation allows {name}`List.reverse` to be accessed from a term of type {lean}`Sequence Nat`.
-- ```lean
-- #check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
-- ```
--
-- However, declaring {name}`Sequence` to be irreducible prevents the unfolding:
-- ```lean (error := true) (name := irredSeq)
-- attribute [irreducible] Sequence
--
-- #check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
-- ```
-- ```leanOutput irredSeq
-- invalid field 'reverse', the environment does not contain 'Sequence.reverse'
--   xs
-- has type
--   Sequence Nat
-- ```
-- :::

:::example "可约性与广义字段记法"
在查找匹配名称时，{tech key := "generalized field notation"}[广义字段记法] 会展开可约与半可约的声明。
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
```lean (error := true) (name := irredSeq)
attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
invalid field 'reverse', the environment does not contain 'Sequence.reverse'
  xs
has type
  Sequence Nat
```
:::

-- :::syntax attr (title := "Reducibility Annotations")
-- A definition's reducibility can be set using one of the three reducibility attributes:
--
-- ```grammar
-- reducible
-- ```
-- ```grammar
-- semireducible
-- ```
-- ```grammar
-- irreducible
-- ```
-- These attributes can only be applied globally in the same file as the definition being modified, but they may be {keywordOf attrInst parser:=Lean.Parser.Term.attrKind}`local`ly applied anywhere.
-- :::

:::syntax attr (title := "可约性标注")
可以使用如下三种可约性属性之一来设置某个定义的可约性：

```grammar
reducible
```
```grammar
semireducible
```
```grammar
irreducible
```
这些属性只能在被修改定义所在的同一文件中全局应用；不过，它们也可以在任意位置以 {keywordOf attrInst parser:=Lean.Parser.Term.attrKind}`local` 方式应用。
:::

## Reducibility and Tactics

-- The tactics {tactic}`with_reducible`, {tactic}`with_reducible_and_instances`, and {tactic}`with_unfolding_all` control which definitions are unfolded by most tactics.

下面这些战术可控制大多数战术会展开哪些定义：{tactic}`with_reducible`、{tactic}`with_reducible_and_instances` 与 {tactic}`with_unfolding_all`。



-- :::example "Reducibility and Tactics"
-- The functions {lean}`plus`, {lean}`sum`, and {lean}`tally` are all synonyms for {lean}`Nat.add` that are respectively reducible, semireducible, and irreducible:
-- ```lean
-- abbrev plus := Nat.add
--
-- def sum := Nat.add
--
-- @[irreducible]
-- def tally := Nat.add
-- ```
--
-- The reducible synonym is unfolded by {tactic}`simp`:
-- ```lean
-- theorem plus_eq_add : plus x y = x + y := by simp
-- ```
--
-- The semireducible synonym is not, however, unfolded by {tactic}`simp`:
-- ```lean (keep := false) (error := true) (name := simpSemi)
-- theorem sum_eq_add : sum x y = x + y := by simp
-- ```
-- Nonetheless, the definitional equality check induced by {tactic}`rfl` unfolds the {lean}`sum`:
-- ```lean
-- theorem sum_eq_add : sum x y = x + y := by rfl
-- ```
-- The irreducible {lean}`tally`, however, is not reduced by definitional equality.
-- ```lean  (keep := false) (error := true) (name := reflIr)
-- theorem tally_eq_add : tally x y = x + y := by rfl
-- ```
-- The {tactic}`simp` tactic can unfold any definition, even irreducible ones, when they are explicitly provided:
-- ```lean  (keep := false) (name := simpName)
-- theorem tally_eq_add : tally x y = x + y := by simp [tally]
-- ```
-- Similarly, part of a proof can be instructed to ignore irreducibility by placing it in a {tactic}`with_unfolding_all` block:
-- ```lean
-- theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
-- ```
-- :::

:::example "可约性与战术"
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
```lean (keep := false) (error := true) (name := simpSemi)
theorem sum_eq_add : sum x y = x + y := by simp
```
不过，由 {tactic}`rfl` 触发的定义相等检查会展开 {lean}`sum`：
```lean
theorem sum_eq_add : sum x y = x + y := by rfl
```
不可约的 {lean}`tally` 不会被定义相等所化简：
```lean  (keep := false) (error := true) (name := reflIr)
theorem tally_eq_add : tally x y = x + y := by rfl
```
当显式提供时，{tactic}`simp` 可以展开任意定义，甚至包括不可约的：
```lean  (keep := false) (name := simpName)
theorem tally_eq_add : tally x y = x + y := by simp [tally]
```
类似地，可将证明的一部分放入 {tactic}`with_unfolding_all` 块中以忽略不可约性：
```lean
theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
```
:::

## Modifying Reducibility

-- The reducibility of a definition can be globally modified in the module in which it is defined by applying the appropriate attribute with the {keywordOf Lean.Parser.Command.attribute}`attribute` command.
-- In other modules, the reducibility of imported definitions can be modified by applying the attribute with the {keyword}`local` modifier.
-- The {keywordOf Lean.Parser.commandSeal__}`seal` and  {keywordOf Lean.Parser.commandUnseal__}`unseal` commands are a shorthand for this process.

可以在定义所在的模块中，使用 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令施加相应属性，从而全局修改某个定义的可约性。
在其他模块中，可通过带 {keyword}`local` 修饰符的属性应用来修改已导入定义的可约性。
{keywordOf Lean.Parser.commandSeal__}`seal` 与 {keywordOf Lean.Parser.commandUnseal__}`unseal` 命令是该流程的便捷写法。

-- :::syntax command (title := "Local Irreducibility")
--
-- {includeDocstring Lean.Parser.commandSeal__}
--
-- ```grammar
-- seal $_:ident $_*
-- ```
-- :::

:::syntax command (title := "局部不可约性")

{includeDocstring Lean.Parser.commandSeal__}

```grammar
seal $_:ident $_*
```
:::

-- :::syntax command (title := "Local Reducibility")
-- {includeDocstring Lean.Parser.commandUnseal__}
--
-- ```grammar
-- unseal $_:ident $_*
-- ```
--
-- :::

:::syntax command (title := "局部可约性")
{includeDocstring Lean.Parser.commandUnseal__}

```grammar
unseal $_:ident $_*
```

:::

## Options

-- For performance, the elaborator and many tactics construct indices and caches.
-- Many of these take reducibility into account, and there's no way to invalidate and regenerate them if reducibility changes globally.
-- Unsafe changes to reducibility settings that could have unpredictable results are disallowed by default, but they can be enabled by using the {option}`allowUnsafeReducibility` option.

出于性能考虑，繁释器与许多战术会构建索引与缓存。
其中不少会考虑可约性；而一旦全局改变了可约性，就无法使这些索引/缓存失效并重新生成。
默认情况下，会禁止对可约性进行可能带来不可预测结果的不安全修改；不过，可通过 {option}`allowUnsafeReducibility` 选项启用之。

{optionDocs allowUnsafeReducibility}
