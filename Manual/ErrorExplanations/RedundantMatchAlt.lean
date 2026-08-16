/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`redundantMatchAlt`" =>
%%%
shortTitle := "redundantMatchAlt"
tag := "Lean-__________________--Error-Explanations--About___--redundantMatchAlt"
file := "About___--redundantMatchAlt"
%%%

{errorExplanationHeader lean.redundantMatchAlt}

当模式匹配中的某个分支永远不可达时，会产生此错误：任何匹配所提供模式的表达式也会匹配某个
在前面的分支。有关模式匹配的更多细节，请参阅手册中的
{ref "pattern-matching"}[模式匹配]章节。

此错误可能出现在任何模式匹配表达式中，包括
{keywordOf Lean.Parser.Term.match}`match`表达式、等式函数定义、`if let`
绑定，以及带回退分支的单子式 {keywordOf Lean.Parser.Term.let}`let` 绑定。

在包含多个分支的模式匹配中，如果一个不太具体的模式位于它所涵盖的更具体模式之前，就可能发生此错误。
请注意，表达式会按从上到下的顺序与模式匹配，因此具体模式应位于通用模式之前。

在只指定一个模式的 {keywordOf termIfLet}`if let` 绑定和带回退分支的单子式
{keywordOf Lean.Parser.Term.let}`let` 绑定中，此错误表示指定的模式总会匹配。在这种情况下，
可以将相关绑定替换为标准的模式匹配 {keywordOf Lean.Parser.Term.let}`let`。

此错误的一个常见原因是，本应匹配构造器的模式被解释成了变量绑定。例如，在该类型的命名空间之外，
如果构造器名称（如 `cons`）写成不带前缀（{name}`List`）的形式，就会发生这种情况。
默认启用的“构造器名称作为变量”代码检查器会对任何类似构造器名称的变量模式显示警告。

此错误几乎总是表示其所在代码存在问题。不过，如有需要，`set_option match.ignoreUnusedAlts true`
会禁用此错误的检查，并允许通过丢弃未使用分支来编译含有冗余分支的模式匹配。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--redundantMatchAlt--Examples"
%%%
:::errorExample "模式匹配顺序错误"
```broken
def seconds : List (List α) → List α
  | [] => []
  | _ :: xss => seconds xss
  | (_ :: x :: _) :: xss => x :: seconds xss
```
```output
Redundant alternative: Any expression matching
  (head✝ :: x :: tail✝) :: xss
will match one of the preceding alternatives
```
```fixed
def seconds : List (List α) → List α
  | [] => []
  | (_ :: x :: _) :: xss => x :: seconds xss
  | _ :: xss => seconds xss
```

由于任何匹配 `(_ :: x :: _) :: xss` 的表达式也会匹配 `_ :: xss`，因此错误实现中的最后一个
分支永远不会到达。我们通过将更具体的分支移到更通用的分支之前来解决此问题。
:::

:::errorExample "不必要的回退分支"
```broken
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
    | return 0
  return m + n
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
  return m + n
```

这里，回退分支用于捕获 `p` 中所有不匹配 `(m, n)` 的值。
然而，不存在这样的值，因此回退分支是不必要的，可以将其删除。当使用 `if let pat := e` 且
`e` 总会匹配 `pat` 时，也会产生类似错误。
:::

:::errorExample "模式被视为变量而非构造器"
```broken
example (xs : List Nat) : Bool :=
  match xs with
  | nil => false
  | _ => true
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (xs : List Nat) : Bool :=
  match xs with
  | .nil => false
  | _ => true
```

在原始示例中，`nil` 被视为变量而非构造器名称，因为此定义不在 {name}`List` 命名空间内。
因此，`xs` 的所有值都会匹配第一个模式，使第二个模式未被使用。请注意，“构造器名称作为变量”
代码检查器会在 `nil` 处显示警告，指出它与有效构造器名称相似。如修正示例所示使用点前缀记法，
或指定完整构造器名称 {name}`List.nil`，即可实现预期行为。
:::
