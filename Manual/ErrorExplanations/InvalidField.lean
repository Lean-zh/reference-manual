/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`invalidField`" =>
%%%
shortTitle := "invalidField"
tag := "Lean-__________________--Error-Explanations--About___--invalidField"
file := "About___--invalidField"
%%%

{errorExplanationHeader lean.invalidField}

此错误表示遇到了包含点号后跟标识符的表达式，但无法将该标识符理解为字段。

Lean 的字段表示法非常强大，但这也可能令人困惑：表达式
`color.value` 可以是单个 {ref "identifiers-and-resolution"}[标识符]，
也可以是对{ref "structure-fields"}[结构体字段]的引用，
还可以使用{ref "generalized-field-notation"}[广义字段表示法]对值 `color` 调用函数。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--invalidField--Examples"
%%%
:::errorExample "错误的字段名称"

```broken
#eval (4 + 2).suc
```
```output
Invalid field `suc`: The environment does not contain `Nat.suc`, so it is not possible to project the field `suc` from an expression
  4 + 2
of type `Nat`
```
```fixed
#eval (4 + 1).succ
```

无效字段错误最简单的原因是所查找的函数（例如 `Nat.suc`）不存在。
:::

:::errorExample "从错误表达式投影"
```broken
#eval '>'.leftpad 10 ['a', 'b', 'c']
```
```output
Invalid field `leftpad`: The environment does not contain `Char.leftpad`, so it is not possible to project the field `leftpad` from an expression
  '>'
of type `Char`
```
```fixed
#eval ['a', 'b', 'c'].leftpad 10 '>'
```

点号前表达式的类型完全决定字段投影所调用的函数。不存在 `Char.leftpad`，
而使用广义字段表示法调用 `List.leftpad` 的唯一方式是让列表出现在点号之前。
:::

:::errorExample "类型不够具体"
```broken
def double_plus_one {α} [Add α] (x : α) :=
   (x + x).succ
```
```output
Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  x + x
has type `α` which does not have the necessary form.
```
```fixed
def double_plus_one (x : Nat) :=
   (x + x).succ
```

`Add` 类型类足以执行加法 `x + x`，但 `.succ` 字段表示法必须知道更多信息，
才能确定实际要从哪个类型投影 `succ`，否则无法工作。
:::

:::errorExample "类型信息不足"

```broken
example := fun (n) => n.succ.succ
```
```output
Invalid field notation: Type of
  n
is not known; cannot resolve field `succ`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Fin.succ`
  • `Nat.succ`
  • `Lean.Level.succ`
  • `Std.PRange.succ`
  • `Lean.Level.PP.Result.succ`
  • `Std.Time.Internal.Bounded.LE.succ`
```
```fixed
example := fun (n : Nat) => n.succ.succ
```

只有能够确定被投影的类型时，才能使用广义字段表示法。可能需要添加类型注解，
才能使广义字段表示法正常工作。
:::
