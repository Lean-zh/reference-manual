import Manual.ZhDocString.Upstream
import Std.Async
import Std.WP

open Verso.Genre Manual

/-- error: 上游文档已改变，须重新核对中文翻译：Std.Async.Async -/
#guard_msgs in
run_cmd do
  let _ ← Lean.Elab.Command.liftCoreM <| upstreamTranslation "Std.Async.Async" "Changed upstream documentation"

/-- error: 缺少上游新增文档的中文翻译：missing.translation -/
#guard_msgs in
run_cmd do
  let _ ← Lean.Elab.Command.liftCoreM <| upstreamTranslation "missing.translation" "Missing documentation"

#doc (Manual) "上游新增 API 中文文档检查" =>
%%%
file := "upstream-docs-smoke"
tag := "upstream-docs-smoke"
%%%

{zhdocstringFrom Std.Async.Selector}

{zhdocstringFrom Std.Async.Signal}

{zhdocstringFrom Std.WP.WPMonad}

{zhOptionDocsFrom trace.grind.ac}

:::zhgrindTactic "skip"
:::
