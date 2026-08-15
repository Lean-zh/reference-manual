/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Coercions

universe u v

/--
`Coe α β` 是从 `α` 到 `β` 的强制转换类型类。它可以与其他 `Coe` 实例传递地组成转换链。
当 `x` 的类型为 `α`，但它出现在预期类型为 `β` 的上下文中时，Lean 会自动使用该强制转换。
可以使用运算符 `↑x` 显式触发强制转换。
-/
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
`CoeHead α β` 用于在强制转换链开头至多应用一次、按从左到右方向进行的强制转换。
-/
class CoeHead (α : Sort u) (β : semiOutParam (Sort v)) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/-- `CoeOut α β` 用于按从左到右方向应用的强制转换。 -/
class CoeOut (α : Sort u) (β : semiOutParam (Sort v)) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
`CoeTail α β` 用于只能出现在强制转换序列末尾的转换。也就是说，`α` 还可以通过
`Coe σ α` 和 `CoeHead τ σ` 实例进一步转换，但 `β` 只能是表达式的预期类型。
-/
class CoeTail (α : semiOutParam (Sort u)) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
`CoeT` 是 Lean 在解决类型错误时调用的核心类型类。也可以用记法 `↑x` 或双重类型标注
`((x : α) : β)` 显式触发它。

`CoeT` 转换链的文法为 `CoeHead? CoeOut* Coe* CoeTail? | CoeDep`。
-/
class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  /--
  类型为 `β` 的结果值。输入 `x : α` 是该类型类的参数，因此这个 `β` 类型的值可以依赖于
  `x` 上的其他类型类。
  -/
  coe : β

/--
`CoeDep α (x : α) β` 是依赖强制转换的类型类：类型 `β` 可以依赖于 `x`。更准确地说，
类型类搜索可以使用 `x` 的值，因而允许实例将 `β` 与 `x` 关联起来。

依赖强制转换不参与普通强制转换的传递式链合成；它们必须与类型不匹配的两端精确一致。
-/
class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  /--
  类型为 `β` 的结果值。输入 `x : α` 是该类型类的参数，因此这个 `β` 类型的值可以依赖于
  `x` 上的其他类型类。
  -/
  coe : β

namespace Lean.Attr

/--
在函数上标记 `@[coe]` 属性（该函数通常也应出现在形如
`instance : Coe A B := ⟨myFn⟩` 的声明中），可以让反精译器在打印表达式时把该函数的应用
显示为 `↑`。
-/
def coe : Unit := ()

end Lean.Attr

/--
典范同态 `Nat → R`。在大多数用法中，目标类型具有（半）环结构，而该同态应为（半）环同态。

`NatCast` 与 `IntCast` 使不同程序库中可用自然数记法表示的自定义类型能够采用一致的 `simp`
标准形，而不必建立了解所有组合的强制转换化简集。程序库应尽可能便于通过 `NatCast` 工作。
例如在 Mathlib 中，只要 `R` 是带 `1` 的加法幺半群，就会有这样的同态，因而也会有
`NatCast R` 实例。

典型示例是 `Int.ofNat`。
-/
class NatCast (R : Type u) where
  /-- 典范映射 `Nat → R`。 -/
  protected natCast : Nat → R

namespace Nat

/--
典范同态 `Nat → R`。在大多数用法中，目标类型具有（半）环结构，而该同态应为（半）环同态。

`NatCast` 与 `IntCast` 使不同程序库中可用自然数记法表示的自定义类型能够采用一致的 `simp`
标准形，而不必建立了解所有组合的强制转换化简集。程序库应尽可能便于通过 `NatCast` 工作。
例如在 Mathlib 中，只要 `R` 是带 `1` 的加法幺半群，就会有这样的同态，因而也会有
`NatCast R` 实例。

典型示例是 `Int.ofNat`。
-/
protected def cast {R : Type u} [NatCast R] : Nat → R := NatCast.natCast

end Nat

/--
典范同态 `Int → R`。在大多数用法中，目标类型具有环结构，而该同态应为环同态。

`IntCast` 与 `NatCast` 使不同程序库中可用自然数记法表示的自定义类型能够采用一致的 `simp`
标准形，而不必建立了解所有组合的强制转换化简集。程序库应尽可能便于通过 `IntCast` 工作。
例如在 Mathlib 中，只要 `R` 是带 `1` 的加法群，就会有这样的同态，因而也会有 `IntCast R`
实例。
-/
class IntCast (R : Type u) where
  /-- 典范映射 `Int → R`。 -/
  protected intCast : Int → R

namespace Int

/--
典范同态 `Int → R`。在大多数用法中，目标类型具有环结构，而该同态应为环同态。

`IntCast` 与 `NatCast` 使不同程序库中可用自然数记法表示的自定义类型能够采用一致的 `simp`
标准形，而不必建立了解所有组合的强制转换化简集。程序库应尽可能便于通过 `IntCast` 工作。
例如在 Mathlib 中，只要 `R` 是带 `1` 的加法群，就会有这样的同态，因而也会有 `IntCast R`
实例。
-/
protected def cast {R : Type u} [IntCast R] : Int → R := IntCast.intCast

end Int

/--
`CoeSort α β` 是到 Sort 的强制转换。`β` 必须是一个宇宙。当 `a : α` 出现在预期类型的位置，
例如 `(x : a)` 或 `a → a` 中时，就会触发该转换。
`CoeSort` 实例也适用于 `CoeOut`。
-/
class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  /-- 将类型为 `α` 的值强制转换到 `β`；`β` 必须是一个宇宙。 -/
  coe : α → β

/--
`CoeFun α (γ : α → Sort v)` 是到函数的强制转换。`γ a` 应当是一个函数类型（或可强制转换为
函数的类型）。当元素 `f : α` 出现在 `f x` 这样的应用中，而该应用因 `f` 不是函数类型而
本来无意义时，就会触发该转换。
`CoeFun` 实例也适用于 `CoeOut`。
-/
class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  /--
  将值 `f : α` 强制转换为类型 `γ f`。为了解决类型错误的应用 `f x`，`γ f` 应当是函数类型
  或另一个 `CoeFun` 类型。
  -/
  coe : (f : α) → γ f

/--
实现 `CoeHead* Coe* CoeTail?` 的辅助类。
用户通常不应直接实现该类。
-/
class CoeHTCT (α : Sort u) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
实现 `CoeHead CoeOut* Coe*` 的辅助类。
用户通常不应直接实现该类。
-/
class CoeHTC (α : Sort u) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
实现 `CoeOut* Coe*` 的辅助类。
用户通常不应直接实现该类。
-/
class CoeOTC (α : Sort u) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

/--
实现 `Coe*` 的辅助类。
用户通常不应直接实现该类。
-/
class CoeTC (α : Sort u) (β : Sort v) where
  /-- 将类型为 `α` 的值强制转换为类型 `β`。可通过记法 `↑x` 或双重类型标注 `((x : α) : β)` 使用。 -/
  coe : α → β

end ZhDoc.Coercions
