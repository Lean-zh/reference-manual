/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean4.32.2 (2026-07-28)" =>
%%%
tag := "release-v4.32.2"
file := "v4.32.2"
%%%

此版本修复了内核中的一个健全性错误。

该问题由 Ramana Kumar 发现并由 Kiran Gopinathan 报告。

恶意元程序可以欺骗内核接受 `False` 的证明或任何其他定理。内核对具有幻像类型参数的嵌套归纳类型的处理不完整，并且绕过了类型检查器。

即使使用 `comparator` 也可以利用该错误。

外部检查器 `nanoda` 不会遇到同样的错误。然而，根据这个错误的性质，可以编写利用它的证明项，同时利用外部检查器中不相关的错误，正如 Kumar 在 `nanoda` 中一个[最近独立报告并修复的错误](https://github.com/ammkrn/nanoda_lib/pull/22/changes)所演示的那样。我们强烈建议必须考虑恶意证明并遵循 {ref "validating-comparator"}[验证证明的推荐方法] 的用户也升级到最新的 `nanoda` 版本。

FRO 认真对待这些问题，并将投资检查器生态系统，以实现内核和检查器的更强化、更多测试和更独立的实现。

有关错误的更多详细信息，请参阅 [议题 #14576](https://github.com/leanprover/lean4/issues/14576) ，有关修复的详细信息，请参阅 [PR #14577](https://github.com/leanprover/lean4/pull/14577) 。
