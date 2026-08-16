/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean Doc
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`ctorResultingTypeMismatch`" =>
%%%
shortTitle := "ctorResultingTypeMismatch"
%%%

{errorExplanationHeader lean.ctorResultingTypeMismatch}

在归纳声明中，每个构造器的结果类型必须与所声明的类型匹配；否则就会产生此错误。也就是说，
归纳类型的每个构造器都必须返回该类型的值。更多信息请参阅{ref "inductive-types"}[归纳类型]。
注意，如果所定义的归纳类型没有索引，可以省略构造器的结果类型。

# 示例

:::errorExample "结果类型中的拼写错误"
```broken
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Treee α
```
```output
Unexpected resulting type for constructor `Tree.node`: Expected an application of
  Tree
but found
  ?m.2
```
```fixed
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α
```
:::

:::errorExample "构造器参数后缺少结果类型"
```broken
inductive Credential where
  | pin      : Nat
  | password : String
```
```output
Unexpected resulting type for constructor `Credential.pin`: Expected
  Credential
but found
  Nat
```
```fixed "resulting type"
inductive Credential where
  | pin      : Nat → Credential
  | password : String → Credential
```
```fixed "named parameter"
inductive Credential where
  | pin (num : Nat)
  | password (str : String)
```

如果标注了构造器类型，就必须提供完整类型（包括结果类型）。另一种方式是使用命名绑定项书写构造器参数；
这样便可省略不含索引的构造器结果类型。
:::
