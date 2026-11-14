/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.33.1 (2026-08-21)" =>
%%%
tag := "release-v4.33.1"
file := "v4.33.1"
%%%

此补丁版本修复运行时和内核问题，建议所有 `v4.33.0` 或更早版本的用户升级。

此版本合入了 11 项更改。
除下面列出的 2 项新增功能
和 7 项修复外，
还有 0 项重构，
0 项文档改进，
1 项性能改进，
1 项测试套件改进，
以及 0 项其他更改。

# 语言
%%%
file := "Language"
tag := "Manual-Releases-v4_33_1-Language"
%%%

```markdown

- [#14582](https://github.com/leanprover/lean4/pull/14582)
使内核拒绝正在声明的数据类型被应用于声明参数和宇宙层级以外实参的归纳声明。此前这种非一致出现可能隐藏在内核检查无法覆盖的位置：会擦除它们的归约背后，或嵌套出现的参数化实参中；后者会从内核生成的辅助声明中丢弃，因此此前只检查其类型正确性。

```

# 编译器
%%%
file := "Compiler"
tag := "Manual-Releases-v4_33_1-Compiler"
%%%

```markdown

- [#14838](https://github.com/leanprover/lean4/pull/14838)
防止对象的 32 位引用计数溢出导致内存损坏。在至少有 18GB 可用内存的机器上，此问题可触发官方内核中的释放后使用，并进一步构造 False 的证明。不依赖 Lean 运行时的 nanoda 等内核不受影响。

```

# 其他
%%%
file := "Other"
tag := "Manual-Releases-v4_33_1-Other"
%%%

```markdown

- [#14833](https://github.com/leanprover/lean4/pull/14833)
要求 GMP 6.3.0 或更新版本，并使官方发行版链接 GMP 6.3.0。旧 GMP 的缺陷可能让 Lean 在边界情况下产生不可靠（即错误）的结果；不依赖 GMP 的独立内核会检测到这种不可靠性。此前可移植 Linux 发行版链接的是 GMP 6.1.2，来自为可移植性采用的旧 glibc nixpkgs。

- [#14849](https://github.com/leanprover/lean4/pull/14849)
使内核拒绝表示大小超过可配置限制（默认 128 MB）的 `Nat` 字面量及计算，防止病态或对抗性输入让内核花费无界内存和时间构造巨大数值，并将内核算术保持在其任意精度整数后端经过充分测试的范围内。少数确实要在内核中计算极大数值的工作负载，可通过 `LEAN_NAT_MAX_SIZE` 环境变量提高限制。

- [#14847](https://github.com/leanprover/lean4/pull/14847)
为内核 `is_prop` 缺陷增加一个测试。
攻击由 Daniel Selsam（OpenAI）提交，使用 OpenAI 内部模型生成。

- [#14843](https://github.com/leanprover/lean4/pull/14843)
将 #14807 的修复应用于 `inductive.h`。如其注释所述，代码应使用 `is_prop` 检查 `e_type` 是否为命题，但此前仍内联了有缺陷的旧实现。

- [#14808](https://github.com/leanprover/lean4/pull/14808)
  为内核增加新的防御性检查。内核为归纳类型生成递归器后，会用不再复查它们的 `add_core` 安装递归器及其计算规则。新增验证过程会（1）检查每个生成递归器的类型，（2）检查各计算规则保持类型：将递归器应用于构造器并归约后，所得项的类型必须是递归器声明的结果类型。这可以发现次要前提类型与归约规则不一致的递归器，例如次要前提需要归纳假设而规则没有提供。仅检查规则右侧具有某个类型并不充分，因为应用不足的次要前提仍是类型正确的函数项。这是纵深防御，不改变内核对良构归纳类型的接受行为，仅拒绝本来就不合法的声明。

- [#14807](https://github.com/leanprover/lean4/pull/14807)
  修复可靠性问题。内核的 `is_prop` 通过获取推断类型的弱头范式，并检查结果在语法上是否为 `Sort 0`，来判断项是否为命题。若推断类型未归约到 sort 而停滞，旧实现返回 `false`，而不将其视为非法项。这使投影推断中的证明无关性防护被跳过，从而能从当作 `Prop` 使用的值投影出非证明字段，并推导 `False`。修复后用 `ensure_sort` 计算推断类型，归约并要求结果为 sort，否则抛出 `(kernel) type expected`。独立实现的 Lean 内核 nanoda 也接受该伪造证明；我们认为 lean4lean 外部内核没有此缺陷。

- [#14806](https://github.com/leanprover/lean4/pull/14806)
  修复内核的可靠性问题。内核用并查集缓存成功的 `is_def_eq` 查询。由于实现的 `is_def_eq` 可靠但不完备，因而不满足传递性，并查集计算的传递闭包使结果依赖此前查询顺序：`is_def_eq(v0, v2)` 单独查询可能返回 `false`，但在 `is_def_eq(v0, v1)` 与 `is_def_eq(v1, v2)` 成功后可能返回 `true`。精心构造的输入利用这一点建立类型与计算规则不一致的递归器，进而推导 `False`。修复将并查集替换为以查询对为键的普通缓存，使 `is_def_eq` 重新仅取决于两个实参。问题由 Daniel Selsam（OpenAI）使用内部模型报告，随后一个 OpenAI 智能体构造了两种不同攻击。nanoda 及 Joachim Breitner 新开发的 lean-inductive-models 都能检测这两种攻击。

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  添加使用线程检测器编译的支持。由于这会增加内存消耗并显著降低 Lean 速度，仅运行很小的测试子集，以保持合理耗时；开发者需自行向该集合添加其他测试。

```
