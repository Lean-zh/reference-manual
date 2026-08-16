/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.3.0 (2023-11-30)" =>
%%%
tag := "release-v4.3.0"
file := "v4.3.0"
%%%

```markdown
* `simp [f]` 不再展开 `f` 的部分应用。参见 issue [#2042](https://github.com/leanprover/lean4/issues/2042)。
  若要修复受此变更影响的证明，请使用 `unfold f` 或 `simp (config := { unfoldPartialApp := true }) [f]`。
* 默认情况下，`simp` 将不再尝试使用 Decidable 实例来重写项。特别是，并非所有可判定目标都会被 `simp` 关闭，在这种情况下 `decide` tactic 可能会有帮助。可以使用 `decide` 这一 simp 配置选项在局部恢复旧版 `simp` 行为，例如 `simp (config := {decide := true})`；这也包括使用 Decidable 实例来验证数值不等式等辅助目标。

* 许多缺陷修复：
  * [为项树强制类型转换精化器添加左/右作用，并将 `^`` 设为右作用](https://github.com/leanprover/lean4/pull/2778)
  * [修复 #2775：不要捕获最大递归深度错误](https://github.com/leanprover/lean4/pull/2790)
  * [`cases` tactic 下 `Decidable` 实例归约过慢](https://github.com/leanprover/lean4/issues/2552)
  * [`simp` 不会在绑定器中重写](https://github.com/leanprover/lean4/issues/1926)
  * [即使设置了 `zeta := false` 选项，`simp` 仍会展开 `let`](https://github.com/leanprover/lean4/issues/2669)
  * [禁用 beta/zeta 时的 `simp` 与判别树问题](https://github.com/leanprover/lean4/issues/2281)
  * [`rw ... at h` 引入未知自由变量](https://github.com/leanprover/lean4/issues/2711)
  * [`dsimp` 不使用由未应用常量构成的 `rfl` 定理](https://github.com/leanprover/lean4/issues/2685)
  * [若自反相等目标被元数据包裹，`dsimp` 不会将其关闭](https://github.com/leanprover/lean4/issues/2514)
  * [`rw [h]` 会优先使用环境中的 `h`，而非局部上下文中的 `h`](https://github.com/leanprover/lean4/issues/2729)
  * [`assumption` tactic 缺少 `withAssignableSyntheticOpaque`](https://github.com/leanprover/lean4/issues/2361)
  * [忽略字段默认值的警告](https://github.com/leanprover/lean4/issues/2178)
* [在语言服务器中编辑文档时取消尚未完成的任务](https://github.com/leanprover/lean4/pull/2648)。
* [移除 `Fin.mod` 和 `Fin.div` 中不必要的 `%` 运算](https://github.com/leanprover/lean4/pull/2688)
* [避免在 `Array.mem` 中使用 `DecidableEq`](https://github.com/leanprover/lean4/pull/2774)
* [确保 `USize.size` 能与 `?m + 1` 统一](https://github.com/leanprover/lean4/issues/1926)
* [改进与 emacs eglot 客户端的兼容性](https://github.com/leanprover/lean4/pull/2721)

**Lake：**

* [`lake new MyProject math` 的合理默认值](https://github.com/leanprover/lean4/pull/2770)
* 将 `postUpdate?` 配置选项改为 `post_update` 声明。有关新语法的更多信息，请参见 `post_update` 语法的文档字符串。
* [若工作区加载时清单不存在，则自动创建它](https://github.com/leanprover/lean4/pull/2680)。
* 配置声明（即 `package`、`lean_lib` 和 `lean_exe`）中的 `:=` 语法已弃用。例如，`package foo := {...}` 现已弃用。
* [支持通过 `LAKE_PKG_URL_MAP` 覆盖包 URL](https://github.com/leanprover/lean4/pull/2709)
* 将默认构建目录（例如 `build`）、默认包目录（例如 `lake-packages`）以及编译后的配置（例如 `lakefile.olean`）移动到 Lake 输出专用的新目录 `.lake` 中。云端发布构建归档也存储在这里，从而修复了 [#2713](https://github.com/leanprover/lean4/issues/2713)。
* 将清单格式更新为版本 7（变更细节见 [lean4#2801](https://github.com/leanprover/lean4/pull/2801)）。
* 弃用包配置中的 `manifestFile` 字段。
* 现在对 `lakefile.olean` 兼容性进行了更严格的检查（更多细节见 [#2842](https://github.com/leanprover/lean4/pull/2842)）。

```
