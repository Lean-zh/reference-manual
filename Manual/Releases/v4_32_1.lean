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

#doc (Manual) "Lean4.32.1 (2026-07-22)" =>
%%%
tag := "release-v4.32.1"
file := "v4.32.1"
%%%

此版本修复了内核中的一个健全性错误。

该问题是由 Patrick Hulin 在 GPT-5.6 Sol 的帮助下发现的。

恶意元程序可以利用此错误来欺骗内核接受 `False` 的证明或任何其他定理。它要求恶意元程序与内核在同一进程中运行。在这种情况下，恶意元程序已经有其他更直接的方法让系统接受不良证明，因此这个错误不会创建新的攻击向量。

使用比较器的 {ref "validating-comparator"}[检查可能不诚实的证明的推荐方法]*不受*此错误的影响。

有关错误的更多详细信息，请参阅 [议题 #14484](https://github.com/leanprover/lean4/issues/14484) ，有关修复的详细信息，请参阅 [PR #14498](https://github.com/leanprover/lean4/pull/14498) 。
