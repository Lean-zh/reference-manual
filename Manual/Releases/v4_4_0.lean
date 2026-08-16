/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.4.0 (2023-12-31)" =>
%%%
tag := "release-v4.4.0"
file := "v4.4.0"
%%%

````markdown
* Lake 和语言服务器现在支持通过 `moreServerOptions` 配置字段设置按包划分的服务器选项，也支持通过 `leanOptions` 配置字段设置同时作用于语言服务器和 `lean` 的选项。设置这两个字段之一来替代 `moreServerArgs`，可以确保查看依赖中的文件时使用该依赖自身的选项。此外，`moreServerArgs` 正在被 `moreGlobalServerArgs` 字段取代并将被弃用。参见 PR [#2858](https://github.com/leanprover/lean4/pull/2858)。

  下面这个 Lakefile 使用了已弃用的包声明：
  ```lean
  def moreServerArgs := #[
    "-Dpp.unicode.fun=true"
  ]
  def moreLeanArgs := moreServerArgs

  package SomePackage where
    moreServerArgs := moreServerArgs
    moreLeanArgs := moreLeanArgs
  ```

  ……可更新为下面这个包声明，以使用按包划分的选项：
  ```lean
  package SomePackage where
    leanOptions := #[⟨`pp.unicode.fun, true⟩]
  ```
* [重命名请求处理器](https://github.com/leanprover/lean4/pull/2462)。
* [import 自动补全](https://github.com/leanprover/lean4/pull/2904)。
* [使用 `pp.beta` 在美观打印时做 beta 归约](https://github.com/leanprover/lean4/pull/2864)。
* [在 .olean 中嵌入并检查 git 哈希](https://github.com/leanprover/lean4/pull/2766)。
* [为良基递归猜测字典序](https://github.com/leanprover/lean4/pull/2874)。
* [允许在元组、列表和 tactic 中使用尾随逗号](https://github.com/leanprover/lean4/pull/2643)。

以下问题已修复：[#2628](https://github.com/leanprover/lean4/issues/2628)、[#2883](https://github.com/leanprover/lean4/issues/2883)、
[#2810](https://github.com/leanprover/lean4/issues/2810)、[#2925](https://github.com/leanprover/lean4/issues/2925) 与 [#2914](https://github.com/leanprover/lean4/issues/2914)。

**Lake：**

* `lake init .` 和不带参数的 `lake init` 现在都会将当前目录用作包名。[#2890](https://github.com/leanprover/lean4/pull/2890)
* `lake new` 和 `lake init` 现在会对无效包名报错，例如 `..`、`foo/bar`、`Init`、`Lean`、`Lake` 和 `Main`。参见 issue [#2637](https://github.com/leanprover/lean4/issues/2637) 与 PR [#2890](https://github.com/leanprover/lean4/pull/2890)。
* `lean_lib` 不再将其名称转换为大驼峰命名（例如，`lean_lib bar` 现在会包含名为 `bar.*` 的模块，而不是 `Bar.*`）。参见 issue [#2567](https://github.com/leanprover/lean4/issues/2567) 与 PR [#2889](https://github.com/leanprover/lean4/pull/2889)。
* Lean 和 Lake 现在已正确支持非标识符形式的库名（例如，`lake new 123-hello` 与 `import «123Hello»` 现在都能正常工作）。参见 issue [#2865](https://github.com/leanprover/lean4/issues/2865) 与 PR [#2889](https://github.com/leanprover/lean4/pull/2888)。
* Lake 现在会过滤从已编译配置（`lakefile.olean`）中加载的环境扩展，只保留与 Lake 工作区加载流程有关的部分。这解决了因环境扩展类型不匹配而导致的段错误（例如在配置中通过 `elab` 定义自定义精化器时）。参见 issue [#2632](https://github.com/leanprover/lean4/issues/2632) 与 PR [#2896](https://github.com/leanprover/lean4/pull/2896)。
* 如果构建目录被删除，云端发布现在会被正确地重新解包。参见 PR [#2928](https://github.com/leanprover/lean4/pull/2928)。
* Lake 的 `math` 模板已简化。参见 PR [#2930](https://github.com/leanprover/lean4/pull/2930)。
* `lake exe <target>` 现在会像帮助文本所说的那样，把 `target` 按构建目标解析，而不是按基础名称解析。例如，`lake exe @mathlib/runLinter` 现在应可正常工作。参见 PR [#2932](https://github.com/leanprover/lean4/pull/2932)。
* `lake new foo.bar [std]` 现在会生成名为 `foo-bar` 的可执行文件，而 `lake new foo.bar exe` 也会正确创建 `foo/bar.lean`。参见 PR [#2932](https://github.com/leanprover/lean4/pull/2932)。
* 依赖树中较后的包和库现在会优先于较早者。也就是说，较后的条目会“遮蔽”较早的条目。这样的顺序更符合编程语言中声明的一般工作方式。这会破坏任何依赖旧顺序的包。参见 issue [#2548](https://github.com/leanprover/lean4/issues/2548) 与 PR [#2937](https://github.com/leanprover/lean4/pull/2937)。
* 可执行文件根模块不再被错误地当作可导入模块，因此 `findModule?` 不会再拾取它们。参见 PR [#2937](https://github.com/leanprover/lean4/pull/2937)。

````
