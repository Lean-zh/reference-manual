/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Runtime

/--
若 `a` 是共享值（即其引用计数 RC(a) 大于 1），则显示给定消息；无论是否显示消息，
都原样返回 `a`。
-/
def dbgTraceIfShared {α : Type u} (_s : String) (a : α) : α := a

namespace Option

/--
启用后，跟踪 Lean 编译器中间表示（IR）生成阶段的最终结果。
-/
def trace.compiler.ir.result : Prop := True

end Option
end ZhDoc.Runtime
