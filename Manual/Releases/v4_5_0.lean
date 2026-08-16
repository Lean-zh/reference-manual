/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.5.0 (2024-02-01)" =>
%%%
tag := "release-v4.5.0"
file := "v4.5.0"
%%%

````markdown
* 修改字符串字面量的词法语法，加入字符串间隙，即形如 `"\" newline whitespace*` 的转义序列。
  它会被解释为空字符串，并允许字符串跨越多行而不引入额外空白。
  下面这段与 `"this is a string"` 等价。
  ```lean
  "this is \
     a string"
  ```
  参见 [PR #2821](https://github.com/leanprover/lean4/pull/2821) 和 [RFC #2838](https://github.com/leanprover/lean4/issues/2838)。

* 添加原始字符串字面量语法。例如，`r"\n"` 等价于 `"\\n"`，不会进行转义处理。
  若要在原始字符串中包含双引号字符，可以在边界 `"` 的前后添加足够多的 `#` 字符，
  例如 `r#"the "the" is in quotes"#` 对应 `"the \"the\" is in quotes"`。
  参见 [PR #2929](https://github.com/leanprover/lean4/pull/2929) 和 [issue #1422](https://github.com/leanprover/lean4/issues/1422)。

* 底层 `termination_by'` 子句已不再受支持。

  迁移指南：请改用 `termination_by`，例如：
  ```diff
  -termination_by' measure (fun ⟨i, _⟩ => as.size - i)
  +termination_by i _ => as.size - i
  ```

  如果你想使用的良基关系不是 `WellFoundedRelation` 类型类
  会为终止性参数自动推断出的那个，
  可以使用标准库中的 `WellFounded.wrap` 显式给出：
  ```diff
  -termination_by' ⟨r, hwf⟩
  +termination_by x => hwf.wrap x
  ```

* 在 LSP `TextEdit` 中支持代码片段编辑。更多细节见 `Lean.Lsp.SnippetString`。

* 部件 API 的弃用项与变更。
  - `Widget.UserWidgetDefinition` 已弃用，改用 `Widget.Module`。注解 `@[widget]` 已弃用，改用 `@[widget_module]`。要迁移一个 `UserWidgetDefinition` 类型的定义，请删除 `name` 字段，并将类型替换为 `Widget.Module`。删除 `name` 后，将不再在面板部件上方绘制标题栏。若要恢复，可将其作为组件的一部分绘制，例如使用 `<details open=true><summary class='mv2 pointer'>{name}</summary>{rest_of_widget}</details>`。一个迁移示例见[此处](https://github.com/leanprover/std4/pull/475/files#diff-857376079661a0c28a53b7ff84701afabbdf529836a6944d106c5294f0e68109R43-R83)。
  - 新命令 `show_panel_widgets` 允许显示始终开启和局部开启的面板部件。
  - `RpcEncodable` 的部件属性现在可以存储在信息树中。
  - 更多细节与动机见 [RFC 2963](https://github.com/leanprover/lean4/issues/2963)。

* 如果无法为终止性证明自动找到可用的字典序，现在会解释原因。
  参见 [GuessLex：若找不到度量，则解释原因](https://github.com/leanprover/lean4/pull/2960)。

* 提供打印[推断出的终止性参数](https://github.com/leanprover/lean4/pull/3012)的选项。
  设置 `set_option showInferredTerminationBy true` 后，你会得到如下消息
  ```
  Inferred termination argument:
  termination_by
  ackermann n m => (sizeOf n, sizeOf m)
  ```
  用于显示自动生成的 `termination_by` 子句。

* 为[无效的 mutual 代码块](https://github.com/leanprover/lean4/pull/2949)提供更详细的错误信息。

* [`simp?` 与 `simp_all?` 的输出](https://github.com/leanprover/lean4/pull/2923)[有多项改进](https://github.com/leanprover/lean4/pull/2969)。

* 带有 `withLocation *` 的策略在关闭主目标时[不再失败](https://github.com/leanprover/lean4/pull/2917)。

* 实现了 `test_extern` 命令，用于为 `@[extern]` 和 `@[implemented_by]` 函数编写测试。
  用法如下
  ```
  import Lean.Util.TestExtern

  test_extern Nat.add 17 37
  ```
  首符号必须是带有 `@[extern]` 或 `@[implemented_by]` 属性的常量。返回类型必须具有 `DecidableEq` 实例。

以下问题已修复：
[#2853](https://github.com/leanprover/lean4/issues/2853), [#2953](https://github.com/leanprover/lean4/issues/2953), [#2966](https://github.com/leanprover/lean4/issues/2966),
[#2971](https://github.com/leanprover/lean4/issues/2971), [#2990](https://github.com/leanprover/lean4/issues/2990), [#3094](https://github.com/leanprover/lean4/issues/3094).

修复 `Option.getD` 中[默认值急切求值](https://github.com/leanprover/lean4/pull/3043)的问题。
在文件源码不可用时，避免 [`leanPosToLspPos` 中的 panic](https://github.com/leanprover/lean4/pull/3071)。
改进 `List.all` 和 `List.any` 的[短路行为](https://github.com/leanprover/lean4/pull/2972)。

Lake 的若干缺陷修复：[#3036](https://github.com/leanprover/lean4/issues/3036), [#3064](https://github.com/leanprover/lean4/issues/3064), [#3069](https://github.com/leanprover/lean4/issues/3069)。

````
