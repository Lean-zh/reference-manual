/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "组合错误与状态单子" =>
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Combined-Error-and-State-Monads"
%%%

```lean -show
variable (ε : Type u) (σ σ' : Type u) (α : Type u)
```

{name}`EStateM` 单子同时具有异常和可变状态。
{lean}`EStateM ε σ α` 在逻辑上等价于 {lean}`ExceptT ε (StateM σ) α`。
{lean}`ExceptT ε (StateM σ)` 求值得到类型 {lean}`σ → Except ε α × σ`，而类型 {lean}`EStateM ε σ α` 求值得到 {lean}`σ → EStateM.Result ε σ α`。
{name}`EStateM.Result` 是一个与 {name}`Except` 非常相似的归纳类型，不过它的两个构造器都多了一个状态字段。
在编译后的代码中，这种表示为每次单子绑定减少了一层间接访问。

```lean -show
/-- info: σ → Except ε α × σ -/
#check_msgs in
#reduce (types := true) ExceptT ε (StateM σ) α

/-- info: σ → EStateM.Result ε σ α -/
#check_msgs in
#reduce (types := true) EStateM ε σ α
```

{docstring EStateM}

{docstring EStateM.Result}

{docstring EStateM.run}

{docstring EStateM.run'}

{docstring EStateM.adaptExcept}

{docstring EStateM.fromStateM +allowMissing}

# 状态回滚
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Combined-Error-and-State-Monads--State-Rollback"
%%%

以不同顺序组合 {name}`StateT` 和 {name}`ExceptT`，会使异常与状态产生不同的交互。
一种顺序会在捕获异常时回滚状态变更；另一种顺序则会保留变更。
后一种选择符合大多数命令式编程语言的语义，但前一种选择对基于搜索的问题非常有用。
通常只应回滚部分而非全部状态；可以把 {name}`ExceptT`“夹”在两个独立的 {name}`StateT` 之间来实现这一点。

为避免使用 {lean}`StateT σ (EStateM ε σ') α` 再增加一层间接访问，{name}`EStateM` 提供了 {name}`EStateM.Backtrackable` {tech (key := "type class")}[类型类]。
该类指定状态中可以保存和恢复的部分。
{name}`EStateM` 随后会在错误处理前后安排保存和恢复。

{docstring EStateM.Backtrackable}

{name EStateM.Backtrackable}`Backtrackable` 有一个普遍适用的实例，它既不保存也不恢复任何内容。
因为实例合成会优先选择最新的实例，所以只有在未定义其他实例时才会使用这个通用实例。

{docstring EStateM.nonBacktrackable}

# 实现
%%%
tag := "The-Lean-Language-Reference--Functors___-Monads-and--do--Notation--Varieties-of-Monads--Combined-Error-and-State-Monads--Implementations"
%%%

通常不会直接调用这些函数，而是通过相应的类型类访问它们。

{docstring EStateM.map}

{docstring EStateM.pure}

{docstring EStateM.bind}

{docstring EStateM.orElse}

{docstring EStateM.orElse'}

{docstring EStateM.seqRight}

{docstring EStateM.tryCatch}

{docstring EStateM.throw}

{docstring EStateM.get}

{docstring EStateM.set}

{docstring EStateM.modifyGet}
