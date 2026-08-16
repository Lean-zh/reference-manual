/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.2.0 (2023-10-31)" =>
%%%
tag := "release-v4.2.0"
file := "v4.2.0"
%%%

```markdown
* 为不包含元变量的项添加了 [isDefEq 缓存](https://github.com/leanprover/lean4/pull/2644)。
* 将 [`Environment.mk`](https://github.com/leanprover/lean4/pull/2604) 和 [`Environment.add`](https://github.com/leanprover/lean4/pull/2642) 设为私有，并加入 [`replay`](https://github.com/leanprover/lean4/pull/2617) 作为更安全的替代方案。
* `IO.Process.output` 不再继承调用者的标准输入。
* [不要阻止](https://github.com/leanprover/lean4/pull/2612) 默认层级 `match` 归约的缓存。
* 当用户写出无效的 case 标签时，会[列出合法的 case 标签](https://github.com/leanprover/lean4/pull/2629)。
* `DecidableEq` 的派生处理器[现在支持](https://github.com/leanprover/lean4/pull/2591)互递归归纳类型。
* [在 Lake 中显示失败导入的路径](https://github.com/leanprover/lean4/pull/2616)。
* [修复 macOS 上的链接器警告](https://github.com/leanprover/lean4/pull/2598)。
* **Lake：**添加 `postUpdate?` 包配置选项。包可以用它指定一些代码，在该包或其某个下游依赖成功执行 `lake update` 之后运行。（[lake#185](https://github.com/leanprover/lake/issues/185)）
* 改进 Lake 的启动时间（[#2572](https://github.com/leanprover/lean4/pull/2572), [#2573](https://github.com/leanprover/lean4/pull/2573)）
* `refine e` 现在会用在精化 `e` 期间创建的元变量替换主目标，并且不再捕获 `e` 中已有的元变量（[#2502](https://github.com/leanprover/lean4/pull/2502)）。
  * 这通过对 `withCollectingNewGoalsFrom` 的修改实现，同时也影响 `elabTermWithHoles`、`refine'`、`calc`（tactic）和 `specialize`。同样地，这些机制现在的输出都只包含新创建的元变量。
  * 先前，`e` 中新创建的元变量和既有元变量会在不同边界情况下以不一致的方式被返回，从而导致信息视图中目标重复（问题 [#2495](https://github.com/leanprover/lean4/issues/2495)）、目标被错误关闭（问题 [#2434](https://github.com/leanprover/lean4/issues/2434)），以及由于 `refine e` 捕获了先前创建、却意外出现在 `e` 中的目标而产生不直观行为（无对应问题；见该 PR）。

```
