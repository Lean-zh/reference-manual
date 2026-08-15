/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Terms

/--
用于支持可选参数的辅助类型。

声明中的绑定器 `(x : α := default)` 是 `x : optParam α default` 的语法糖；若调用处没有
提供该参数，精译器会尝试使用 `default` 作为实参。
-/
@[reducible] def optParam (α : Sort u) (_default : α) : Sort u := α

/--
用于支持自动参数的辅助类型。它与 `optParam` 类似，但使用给定的策略构造缺省实参。
与 `optParam` 一样，它只影响精译过程；例如，类型类合成不会运行这里给出的策略。
-/
abbrev autoParam.{u} (α : Sort u) (_tactic : Lean.Syntax) : Sort u := α

/--
自然数值字面量的重载接口。

例如，表达式 `37 : α` 会触发 `OfNat α 37` 的实例合成，并被精译为
`(OfNat.ofNat 37 : α)`。严格地说，原始自然数值字面量由项构造子 `nat_lit` 表示；
它们始终具有类型 `Nat`，因此生成的项不会在参数外再套一层 `OfNat.ofNat`。
-/
class OfNat (α : Type u) (_ : Nat) where
  /--
  用户写下 `1 : α` 之类的数值字面量时，解析器会自动插入 `OfNat.ofNat`。
  因而，类型类实例可以根据自然数值及目标类型 `α` 自定义字面量的含义。
  -/
  ofNat : α

/--
十进制及科学计数法数值字面量（例如 `1.23`、`3.12e10`）的重载接口。

示例：
- `1.23` 是 `OfScientific.ofScientific (nat_lit 123) true (nat_lit 2)` 的语法糖；
- `121e100` 是 `OfScientific.ofScientific (nat_lit 121) false (nat_lit 100)` 的语法糖。

这里使用原始自然数值字面量 `nat_lit`；生成的项不会再套一层 `OfNat.ofNat`。
-/
class OfScientific (α : Type u) where
  /--
  根据给定的尾数、指数符号和十进制指数生成一个值。指数符号为 `true` 时表示负指数。

  示例：
  - `1.23` 是 `OfScientific.ofScientific (nat_lit 123) true (nat_lit 2)` 的语法糖；
  - `121e100` 是 `OfScientific.ofScientific (nat_lit 121) false (nat_lit 100)` 的语法糖。

  这里使用原始自然数值字面量 `nat_lit`；生成的项不会再套一层 `OfNat.ofNat`。
  -/
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : α

namespace Option

/--
控制美化打印时是否使用字段表示法，包括结构体投影；若声明带有 `@[pp_nodot]` 属性，
则不使用字段表示法。
-/
def pp.fieldNotation : Prop := True

end Option
end ZhDoc.Terms
