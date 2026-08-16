/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.1.0 (2023-09-26)" =>
%%%
tag := "release-v4.1.0"
file := "v4.1.0"
%%%

```markdown
* 缺失 token 时的错误定位已得到[改进](https://github.com/leanprover/lean4/pull/2393)。特别是，这应能让不完整策略证明中的错误更容易发现。

* 在完成配置文件的精译后，Lake 现在会将配置缓存到 `lakefile.olean` 中。后续运行 Lake 时将导入这个 OLean，而不是重新精译配置文件。这带来了显著的性能提升（基准测试表明，使用 OLean 可将 Lake 的启动时间减半），但有一些重要细节需要注意：
  + 每次修改 `lakefile.lean` 或 `lean-toolchain` 后，Lake 都会重新生成这个 OLean。你也可以向 `lake` 传入新的 `--reconfigure` / `-R` 选项来强制重新配置。
  + Lake 配置选项（即 `-K`）会固定在精译当时。若 `lake` 正在使用缓存配置，此时设置这些选项将不起作用。要更改选项，请用 `-R` / `--reconfigure` 运行 `lake`。
  + **`lakefile.olean` 是本地配置，不应提交到 Git。因此，现有 Lake 包需要把它加入各自的 `.gitignore`。**

* `Lake.buildO` 的签名已更改，`args` 被拆分为 `weakArgs` 和 `traceArgs`。`traceArgs` 会包含在输入跟踪中，而 `weakArgs` 不会。有关如何适配此变更的示例，请参见 Lake 的 [FFI 示例](https://github.com/leanprover/lean4/blob/releases/v4.1.0/src/lake/examples/ffi/lib/lakefile.lean)。

* `Lean.importModules`、`Lean.Elab.headerToImports` 和 `Lean.Elab.parseImports` 的签名

* `rewrite` 策略的配置对象中现已加入[`occs` 字段](https://github.com/leanprover/lean4/pull/2470)，
  以便控制模式的哪些出现位置会被重写。
  这原先是 `Lean.MVarId.rewrite` 的一个单独参数，
  现在已改为 `Rewrite.Config` 的一个额外字段。
  过去用户策略无法访问它。

```
