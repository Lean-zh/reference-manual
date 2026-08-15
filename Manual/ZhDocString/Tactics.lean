/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Tactics

universe u v w

/--
关系复合的类型类。它接收两个“输入”关系 `r` 与 `s`，并产生一个“输出”关系 `t`；
若 `r a b` 与 `s b c` 成立，就可得到 `t a c`。`calc` 策略用它连接关系不同的相邻步骤。
-/
class Trans (r : α → β → Sort u) (s : β → γ → Sort v)
    (t : outParam (α → γ → Sort w)) where
  /-- 对涉及的关系作一般化的传递复合。 -/
  trans : r a b → s b c → t a c

/--
为绑定器名称提供提示，但不改变表达式的值。化简器在使用带此标记的重写规则时，
可用 `binder` 的名称命名新引入的绑定器。
-/
@[simp, expose, implicit_reducible]
def binderNameHint {α : Sort u} {β : Sort v} {γ : Sort w}
    (_v : α) (_binder : β) (e : γ) : γ := e

namespace Rewrite

/-- 控制精化器在判断定义相等时可以展开哪些常量。 -/
inductive TransparencyMode where
  /-- 展开所有常量，包括标记为 `@[irreducible]` 的常量。 -/
  | all
  /-- 展开除 `@[irreducible]` 常量之外的所有常量。 -/
  | default
  /-- 只展开标记为 `@[reducible]` 的常量。 -/
  | reducible
  /-- 展开可约常量与标记为 `@[instance_reducible]` 的常量。 -/
  | instances
  /-- 不展开任何常量。 -/
  | none
  /-- 展开可约、`@[instance_reducible]` 与 `@[implicit_reducible]` 常量。 -/
  | implicit
  deriving Inhabited, BEq

/-- 指定与某表达式匹配的哪些出现位置应被重写。 -/
inductive Occurrences where
  /-- 重写所有出现位置。 -/
  | all
  /-- 只重写给定索引所指的出现位置。 -/
  | pos (idxs : List Nat)
  /-- 重写给定索引之外的所有出现位置。 -/
  | neg (idxs : List Nat)
  deriving Inhabited, BEq

/-- 控制 `apply` 或重写操作产生的未赋值元变量如何成为新目标。 -/
inductive ApplyNewGoals where
  /-- 先列出不依赖其他目标的元变量。 -/
  | nonDependentFirst
  /-- 只将不依赖其他目标的元变量加入目标列表。 -/
  | nonDependentOnly
  /-- 将所有未赋值元变量加入目标列表。 -/
  | all

/-- 控制重写产生的新目标如何加入目标列表。 -/
abbrev NewGoals := ApplyNewGoals

/-- 配置 `rewrite` 与 `rw` 策略的行为。 -/
structure Config where
  /-- 重写时用于展开常量的透明度模式。 -/
  transparency : TransparencyMode := .reducible
  /-- 是否支持 `?x + 1 =?= e` 一类偏移约束。 -/
  offsetCnstrs : Bool := true
  /-- 要重写哪些出现位置。 -/
  occs : Occurrences := .all
  /-- 如何把结果中的元变量转换成新目标。 -/
  newGoals : NewGoals := .nonDependentFirst

end Rewrite

namespace Option
namespace pp
/-- （美化打印器）为 `true` 时显示证明；为 `false` 时把表达式内部的证明替换为 `⋯`。 -/
def proofs : Prop := True
namespace proofs
/-- （美化打印器）当 `pp.proofs` 为 `false` 时，从何种证明复杂度开始用 `⋯` 替换证明。默认值为 `0`。 -/
def threshold : Prop := True
end proofs
/-- （美化打印器）是否显示深层嵌套项；为 `false` 时用 `⋯` 替换过深的项。 -/
def deepTerms : Prop := True
namespace deepTerms
/-- （美化打印器）当 `pp.deepTerms` 为 `false` 时，从何种深度开始用 `⋯` 替换项。默认值为 `50`。 -/
def threshold : Prop := True
end deepTerms
/-- （美化打印器）访问表达式的最大次数；超过后将项打印为 `⋯`。默认值为 `5000`。 -/
def maxSteps : Prop := True
/-- （美化打印器）是否显示元变量名称；关闭时，表达式元变量显示为 `?_`，宇宙层级元变量显示为 `_`。 -/
def mvars : Prop := True
end pp

namespace tactic
/-- 确保策略引入的名称满足卫生性要求。默认值为 `true`。 -/
def hygienic : Prop := True
/-- 是否允许 `induction` 与 `cases` 使用由 `@[induction_eliminator]` 和 `@[cases_eliminator]` 注册的自定义消去器。默认值为 `true`。 -/
def customEliminators : Prop := True
/-- 在 `rw` 与 `simp` 中，实例隐式实参已有赋值时是否跳过重新合成实例。默认值为 `true`。 -/
def skipAssignedInstances : Prop := True
namespace simp
/-- 启用追踪时，让 `simp` 或 `dsimp` 打印与当前调用等价的 `simp only` 调用。默认值为 `false`。 -/
def trace : Prop := True
end simp
end tactic

namespace cbv
/-- 控制 `cbv` 策略可执行的最大步数。默认值为 `100000`。 -/
def maxSteps : Prop := True
/-- 启用后，在使用 `cbv` 策略时显示一条警告。默认值为 `false`。 -/
def warning : Prop := True
end cbv
end Option

end ZhDoc.Tactics
