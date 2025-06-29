/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Language.Functions


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-
#doc (Manual) "Functions" =>
%%%
tag := "functions"
%%%
-/

#doc (Manual) "函数" =>
%%%
file := "Functions"
tag := "functions"
%%%

/-
Function types are a built-in feature of Lean.
{deftech}[Functions] map the values of one type (the {deftech}_domain_) into those of another type (the {deftech}_codomain_), and {deftech}_function types_ specify the domain and codomain of functions.
-/

Lean 内建支持函数类型。
{deftech key := "Functions"}[函数] 将一个类型的值（称为 {deftech key := "domain"}_定义域_）映射到另一个类型的值（称为 {deftech key := "codomain"}_陪域_），
而 {deftech key := "function types"}_函数类型_ 用于指定函数的定义域与陪域。

/-
There are two kinds of function type:

 : {deftech}[Dependent]

   Dependent function types explicitly name the parameter, and the function's codomain may refer explicitly to this name.
   Because types can be computed from values, a dependent function may return values from any number of different types, depending on its argument.{margin}[Dependent functions are sometimes referred to as {deftech}_dependent products_, because they correspond to an indexed product of sets.]

 : {deftech}[Non-Dependent]

   Non-dependent function types do not include a name for the parameter, and the codomain does not vary based on the specific argument provided.
-/

函数类型有两种形式：

: {deftech key := "Dependent"}[依值]

   依值函数类型会显式命名参数，并允许函数的陪域类型显式地引用该名称。
   由于类型可以依赖于值，依值函数可根据输入参数返回不同类型的值。{margin}[依值函数有时也被称为 {deftech key := "dependent products"}_依值积_，因为它们对应于集合的索引积。]

: {deftech key := "Non-Dependent"}[非依值]

   非依值函数类型不会为参数命名，并且陪域类型不依赖于具体参数。

/-
::::keepEnv
:::example "Dependent Function Types"

The function {lean}`two` returns values in different types, depending on which argument it is called with:

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

The body of the function cannot be written with `if...then...else...` because it does not refine types the same way that {keywordOf Lean.Parser.Term.match}`match` does.
:::
::::
-/

::::keepEnv
:::example "依值函数类型"

函数 {lean}`two` 根据传入参数的不同，返回不同类型的值：

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

函数体不能直接用 `if...then...else...` 写出，因为它不会像 {keywordOf Lean.Parser.Term.match}`match` 那样细化类型。
:::
::::

/-
In Lean's core language, all function types are dependent: non-dependent function types are dependent function types in which the parameter name does not occur in the {tech}[codomain].
Additionally, two dependent function types that have different parameter names may be definitionally equal if renaming the parameter makes them equal.
However, the Lean elaborator does not introduce a local binding for non-dependent functions' parameters.
-/

在 Lean 的核心语言中，所有函数类型实际上都是依值的：非依值函数类型只是参数名未出现在 {tech key := "codomain"}[陪域] 中的依值函数类型而已。
此外，只要名称变换后一致，使用不同参数名的两个依值函数类型可以是定义等价的。
不过，Lean 的繁释器不会为非依值函数的参数引入局部绑定。

/-
:::example "Definitional Equality of Dependent and Non-Dependent Functions"
The types {lean}`(x : Nat) → String` and {lean}`Nat → String` are definitionally equal:
```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
Similarly, the types {lean}`(n : Nat) → n + 1 = 1 + n` and {lean}`(k : Nat) → k + 1 = 1 + k` are definitionally equal:
```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
:::
-/

:::example "依值函数与非依值函数的定义等价性"
类型 {lean}`(x : Nat) → String` 和 {lean}`Nat → String` 是定义等价的：
```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
同样，类型 {lean}`(n : Nat) → n + 1 = 1 + n` 和 {lean}`(k : Nat) → k + 1 = 1 + k` 也是定义等价的：
```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
:::

/-
:::::keepEnv
::::example "Non-Dependent Functions Don't Bind Variables"

:::keepEnv
A dependent function is required in the following statement that all elements of an array are non-zero:
```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
:::

:::keepEnv
This is because the elaborator for array access requires a proof that the index is in bounds.
The non-dependent version of the statement does not introduce this assumption:
```lean (error := true) (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
:::
::::
:::::
-/

:::::keepEnv
::::example "非依值函数不会绑定变量"

:::keepEnv
下述关于“数组所有元素均非零”的定义需要依值函数：
```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
:::

:::keepEnv
这是因为繁释器对于数组访问需要传入一个下标不越界的证明。
非依值的版本则不会引入这个已知条件：
```lean (error := true) (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
:::
::::
:::::

/-
While the core type theory does not feature {tech}[implicit] parameters, function types do include an indication of whether the parameter is implicit.
This information is used by the Lean elaborator, but it does not affect type checking or definitional equality in the core theory and can be ignored when thinking only about the core type theory.
-/

虽然核心类型理论没有 {tech key := "implicit"}[隐式] 参数功能，函数类型仍可记录参数是否为隐式。
这一属性仅被 Lean 的繁释器利用，对核心的类型检查和定义等价完全无影响，因此思考核心理论时可以忽略这一信息。

/-
:::example "Definitional Equality of Implicit and Explicit Function Types"
The types {lean}`{α : Type} → (x : α) → α` and {lean}`(α : Type) → (x : α) → α` are definitionally equal, even though the first parameter is implicit in one and explicit in the other.
```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```

:::
-/

:::example "隐式和显式函数类型的定义等价性"
即使一个参数是隐式、另一个是显式，类型 {lean}`{α : Type} → (x : α) → α` 和 {lean}`(α : Type) → (x : α) → α` 也是定义等价的。
```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```

:::

/-
# Function Abstractions
-/

# 函数抽象
%%%
file := "Function Abstractions"
tag := "function-abstractions"
%%%

/-
In Lean's type theory, functions are created using {deftech}_function abstractions_ that bind a variable.
{margin}[In various communities, function abstractions are also known as _lambdas_, due to Alonzo Church's notation for them, or _anonymous functions_ because they don't need to be defined with a name in the global environment.]
When the function is applied, the result is found by {tech key:="β"}[β-reduction]: substituting the argument for the bound variable.
In compiled code, this happens strictly: the argument must already be a value.
When type checking, there are no such restrictions; the equational theory of definitional equality allows β-reduction with any term.
-/

在 Lean 的类型理论中，函数是通过 {deftech key := "function abstractions"}_函数抽象_ 来创建的，它会绑定一个变量。
{margin}[在某些社区里，这一概念又被称为 _λ 表达式（lambda）_（源于 Alonzo Church 的记号），或 _匿名函数_（因其无需在全局环境中指定名称）。]
应用函数时，Lean 通过 {tech key := "β"}[β-规约]，用实参替换被绑定的变量。
在编译代码时，这是严格发生的——参数须先被求值为值。
类型检查阶段则没有这样的限制，定义等价的等式理论允许对任意项做 β-规约。


/-
In Lean's {ref "function-terms"}[term language], function abstractions may take multiple parameters or use pattern matching.
These features are translated to simpler operations in the core language, where all functions abstractions take exactly one parameter.
Not all functions originate from abstractions: {tech}[type constructors], {tech}[constructors], and {tech}[recursors] may have function types, but they cannot be defined using function abstractions alone.
-/

在 Lean 的 {ref "function-terms"}[项语言] 中，函数抽象可以接收多个参数或在参数位置用模式匹配。
这些高级特性会被翻译为底层核心语言中的简单操作，核心语言中每次函数抽象严格只接收一个参数。
此外，并非所有函数都由函数抽象构建：{tech key := "type constructor"}[类型构造子]、{tech key := "constructor"}[构造子]、{tech key := "recursor"}[递归子] 都可能拥有函数类型，但不能仅通过函数抽象定义。

/-
# Currying
%%%
tag := "currying"
%%%
-/

# 柯里化
%%%
file := "Currying"
tag := "currying"
%%%

/-
In Lean's core type theory, every function maps each element of the {tech}[domain] to a single element of the {tech}[codomain].
In other words, every function expects exactly one parameter.
Multiple-parameter functions are implemented by defining higher-order functions that, when supplied with the first parameter, return a new function that expects the remaining parameters.
This encoding is called {deftech}_currying_, popularized by and named after Haskell B. Curry.
Lean's syntax for defining functions, specifying their types, and applying them creates the illusion of multiple-parameter functions, but the result of elaboration contains only single-parameter functions.
-/

在 Lean 的核心类型理论中，每个函数都仅将 {tech key := "domain"}[定义域] 的每一个元素映射到 {tech key := "codomain"}[陪域] 的单个元素。
换言之，函数实际上只接受一个参数。
多参数函数实现时，实际上是通过定义高阶函数——先接收第一个参数，返回一个新函数，该新函数再接收剩余参数。
这样的编码方式称为 {deftech key := "currying"}_柯里化_，此术语由并以 Haskell B. Curry 命名、推广。
Lean 提供的函数定义、类型声明与应用语法表现为多参数函数，但繁释之后的本质都是只带一个参数的函数抽象。

/-
# Extensionality
%%%
tag := "function-extensionality"
%%%
-/

# 外延性
%%%
file := "Extensionality"
tag := "function-extensionality"
%%%

/-
Definitional equality of functions in Lean is {deftech}_intensional_.
This means that definitional equality is defined _syntactically_, modulo renaming of bound variables and {tech}[reduction].
To a first approximation, this means that two functions are definitionally equal if they implement the same algorithm, rather than the usual mathematical notion of equality that states that two functions are equal if they map equal elements of the {tech}[domain] to equal elements of the {tech}[codomain].
-/

Lean 中函数的定义等价是 {deftech key := "intensional"}_内涵性_的。
也就是说，定义等价的判定本质是基于语法的（仅考虑绑定变量的重命名及 {tech key := "reduction"}[规约]）。
粗略而言，只有当两个函数本质上实现了“同一算法”时，才被认为定义等价；而数学上通常的函数相等——即若它们对所有相同输入都有相同输出——则不一定如此。

/-
Definitional equality is used by the type checker, so it's important that it be predictable.
The syntactic character of intensional equality means that the algorithm to check it can be feasibly specified.
Checking extensional equality involves proving essentially arbitrary theorems about equality of functions, and there is no clear specification for an algorithm to check it.
This makes extensional equality a poor choice for a type checker.
Function extensionality is instead made available as a reasoning principle that can be invoked when proving the {tech}[proposition] that two functions are equal.
-/

定义等价是类型检查器赖以工作的基础，因此需要可预测性。
内涵等价中的语法特征，使得验证算法容易形式化；而若要求外延等价则意味着答案可能要靠证明任意的函数相等性定理，无法提出规范的检查算法，因此不适合作为类型检查依据。
函数的外延性被设计为一种可供推理用的原则——可在证明两个函数相等的 {tech key := "proposition"}[命题] 时调用。


/-
::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

In addition to reduction and renaming of bound variables, definitional equality does support one limited form of extensionality, called {tech}_η-equivalence_, in which functions are equal to abstractions whose bodies apply them to the argument.
Given {lean}`f` with type {lean}`(x : α) → β x`, {lean}`f` is definitionally equal to {lean}`fun x => f x`.
::::
-/

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- 下段内容的验证示例
example : (fun x => f x) = f := by rfl
```

除了规约与绑定变量重命名外，Lean 的定义等价还支持一种特殊形式的外延性，即 {tech key := "η-equivalence"}[η-等价]：一个函数与“把它作用于参数后返回”的函数抽象定义等价。
对于 {lean}`(x : α) → β x` 类型的 {lean}`f`，{lean}`f` 与 {lean}`fun x => f x` 是定义等价的。
::::

/-
When reasoning about functions, the theorem {lean}`funext`{margin}[Unlike some intensional type theories, {lean}`funext` is a theorem in Lean. It can be proved {ref "quotient-funext"}[using quotient types].] or the corresponding tactics {tactic}`funext` or {tactic}`ext` can be used to prove that two functions are equal if they map equal inputs to equal outputs.
-/

在函数推理时，可以使用定理 {lean}`funext`{margin}[与某些内涵型理论不同，{lean}`funext` 在 Lean 中是一个定理，可以通过 {ref "quotient-funext"}[商类型] 证明]，或相关的 {tactic}`funext` 和 {tactic}`ext` 策略，证明两个函数仅当对所有输入映射结果相等时亦相等。

{zhdocstring funext ZhDoc.funext}

/-
# Totality and Termination
%%%
tag := "totality"
%%%
-/

# 完全性与终止性
%%%
file := "Totality and Termination"
tag := "totality"
%%%

/-
Functions can be defined recursively using {keywordOf Lean.Parser.Command.declaration}`def`.
From the perspective of Lean's logic, all functions are {deftech}_total_, meaning that they map each element of the {tech}[domain] to an element of the {tech}[codomain] in finite time.{margin}[Some programming language communities use the term _total_ in a different sense, where functions are considered total if they do not crash due to unhandled cases but non-termination is ignored.]
The values of total functions are defined for all type-correct arguments, and they cannot fail to terminate or crash due to a missing case in a pattern match.
-/

Lean 支持用 {keywordOf Lean.Parser.Command.declaration}`def` 来递归定义函数。
从 Lean 逻辑的角度看，所有函数都是 {deftech key := "total"}_完全_ 的：即每个 {tech key := "domain"}[定义域] 元素都能在有限步之内映射为 {tech key := "codomain"}[陪域] 的某个元素。{margin}[某些编程语言社区对“完全”的定义略有不同，仅要求不因未覆盖所有可能而崩溃，允许不终止。]
完全函数对所有类型正确参数都有定义，并且不会因模式匹配遗漏或无限递归而导致崩溃或无终止。

/-
While the logical model of Lean considers all functions to be total, Lean is also a practical programming language that provides certain "escape hatches".
Functions that have not been proven to terminate can still be used in Lean's logic as long as their {tech}[codomain] is proven nonempty.
These functions are treated as uninterpreted functions by Lean's logic, and their computational behavior is ignored.
In compiled code, these functions are treated just like any others.
Other functions may be marked unsafe; these functions are not available to Lean's logic at all.
The section on {ref "partial-unsafe"}[partial and unsafe function definitions] contains more detail on programming with recursive functions.
-/

尽管 Lean 的逻辑模型要求函数完全，Lean 作为实用编程语言也提供了若干“逃生口”：
那些未被证明终止的函数，只要其 {tech key := "codomain"}[陪域] 被证明是非空的，也可用于 Lean 的逻辑中。
此类函数逻辑层面会被视作“未解释函数”，其计算行为在推理中被忽略；但在编译后照常可被调用。
还有些函数被标记为 unsafe，不可用于 Lean 逻辑。
有关递归函数的更多细节，见 {ref "partial-unsafe"}[偏函数和 unsafe 函数定义] 小节。

/-
Similarly, operations that should fail at runtime in compiled code, such as out-of-bounds access to an array, can only be used when the resulting type is known to be inhabited.
These operations result in an arbitrarily chosen inhabitant of the type in Lean's logic (specifically, the one specified in the type's {name}`Inhabited` instance).
-/

同理，某些编译期可运行失败的操作（如数组越界访问）在已知结果类型 inhabitable（可被占用）时可以正常使用。
此时，逻辑层面这些操作会返回一个任意选定的该类型 inhabitant（具体是类型 {name}`Inhabited` 实例指定的值）。

/-
:::example "Panic"
The function {name}`thirdChar` extracts the third element of an array, or panics if the array has two or fewer elements:
```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
The (nonexistent) third elements of {lean}`#['!']` and {lean}`#['-', 'x']` are equal, because they result in the same arbitrarily-chosen character:
```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
Indeed, both are equal to {lean}`'A'`, which happens to be the default fallback for {lean}`Char`:
```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
:::
-/

:::example "崩溃示例"
函数 {name}`thirdChar` 提取数组第三个元素，若数组太短则“崩溃”返回默认值：
```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
对于 {lean}`#['!']` 和 {lean}`#['-', 'x']` 这种原本没第三个元素的数组，返回“第三个元素”其实等价——都为任意字符：
```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
实际上，基于 {lean}`Char` 的默认实现，这两个都等于 {lean}`'A'`：
```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
:::

/-
# API Reference
%%%
tag := "function-api"
%%%
-/

# API 参考
%%%
file := "API Reference"
tag := "function-api"
%%%


`Function` 命名空间下提供了丰富的泛用函数操作工具。

{zhdocstring Function.comp ZhDoc.Function.comp}

{zhdocstring Function.const ZhDoc.Function.const}

{zhdocstring Function.curry ZhDoc.Function.curry}

{zhdocstring Function.uncurry ZhDoc.Function.uncurry}
