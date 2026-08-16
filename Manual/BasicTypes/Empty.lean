/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "空类型" =>
%%%
tag := "empty"
%%%

空类型 {name}`Empty` 表示不可能的值。
它是一个完全没有构造子的归纳类型。

平凡类型 {name}`Unit` 只有一个不接受参数的构造子，可用于为不需要或不关心结果的计算建模；而 {name}`Empty` 可用于根本不应有任何计算发生的情形。
用 {name}`Empty` 实例化多态类型，可以将该类型的某些构造子——即带有相应类型参数的构造子——标记为不可能，从而排除某些不希望出现的代码路径。

出现类型为 {name}`Empty` 的项，表示程序已经到达一条不可能的代码路径。
由于没有构造子，这种类型绝不会有值。
在不可能的代码路径上没有理由继续编写代码；可使用函数 {name}`Empty.elim` 脱离这条不可能的路径。

{name}`Empty` 的宇宙多态对应物是 {name}`PEmpty`。

{docstring Empty}

{docstring PEmpty}


:::example "不可能的代码路径"

函数 {lean}`f` 的类型签名表明它可能抛出异常，但允许异常类型为任意类型：
```lean
def f (n : Nat) : Except ε Nat := pure n
```

将 {lean}`f` 的异常类型实例化为 {lean}`Empty`，便可利用 {lean}`f` 实际上从不抛出异常这一事实，将其转换为一个类型表明不会抛出异常的函数。
具体而言，这样便可使用 {lean}`Empty.elim`，避免处理不可能存在的异常值。

```lean
def g (n : Nat) : Nat :=
  match f (ε := Empty) n with
  | .error e =>
    Empty.elim e
  | .ok v => v
```
:::

# API 参考

%%%
tag := "Lean-__________________--Basic-Types--The-Empty-Type--API-Reference"
%%%
{docstring Empty.elim}

{docstring PEmpty.elim}
