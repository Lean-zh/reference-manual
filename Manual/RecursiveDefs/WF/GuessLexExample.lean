/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
此示例提取到单独的文件中，因为错误消息会显示行号，而我们不希望在编辑大文件时
反复更新它。
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "终止性失败（供其他位置嵌入）" =>

:::example "终止性失败"

如果没有 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句，Lean 会尝试推断良基递归的度量。
如果推断失败，它就会打印上文所述的表格。
在此示例中，{keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句只是阻止 Lean 同时尝试结构递归，从而让错误消息保持针对性。

```lean +error -keep (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 32:6-25 = = =
2) 33:6-23 = < _
3) 34:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```

这三个递归调用通过其源码位置来标识。
这条消息表达了以下事实：

* 在第一次递归调用中，所有参数都（可证明地）等于对应的形参
* 在第二次递归调用中，第一个参数等于第一个形参，且第二个参数可证明地小于第二个形参。
  此递归调用没有检查第三个参数，因为要判定不存在合适的终止参数，并不需要检查它。
* 在第三次递归调用中，第一个参数严格减小，其他参数则未被检查。

当终止性证明以这种方式失败时，发现问题的一种好方法是使用 {keywordOf Lean.Parser.Command.declaration}`termination_by` 明确指出预期的终止参数。
这样会显示失败策略所产生的消息。

:::
