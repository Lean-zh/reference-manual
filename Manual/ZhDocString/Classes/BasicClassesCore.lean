import Init
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Classes.BasicClasses

universe u v w

/--
要么给出命题 `p` 为真的证明，要么给出命题 `p` 为假的证明。这等价于一个 `Bool`，
再配上该 `Bool` 为 `true` 当且仅当 `p` 为真的证明。

`Decidable` 实例主要通过 `if` 表达式和 `decide` 策略使用。在条件表达式中，命题的
`Decidable` 实例用于选择分支。运行时，这种分类生成的代码与基于 `Bool` 的条件表达式
所生成的代码相同。在证明中，`decide` 策略会合成 `Decidable p` 的实例，尝试将其归约为
`isTrue h`，若成功便使用证明 `h` 完成目标。

由于 `Decidable` 携带数据，在编写左侧包含 `Decidable` 实例的 `@[simp]` 引理时，最好使用
`{_ : Decidable p}` 而不是 `[Decidable p]`，这样非典范实例可以通过合一找到，而不是通过
实例合成找到。
-/
class inductive Decidable (p : Prop) where
  /-- 通过提供 `¬p` 的证明来证明 `p` 可判定。 -/
  | isFalse (h : Not p) : Decidable p
  /-- 通过提供 `p` 的证明来证明 `p` 可判定。 -/
  | isTrue (h : p) : Decidable p

/--
可判定谓词。

如果对每个可能的参数，相应命题都是 `Decidable`，那么该谓词就是可判定的。
-/
def DecidablePred : Unit := ()

/--
可判定关系。

如果对所有可能的参数，相应命题都是 `Decidable`，那么该关系就是可判定的。
-/
def DecidableRel : Unit := ()

/--
一个类型的任意元素之间的命题相等性都是 `Decidable`。

换言之，`DecidableEq α` 的实例提供了一种方法，可对所有 `a b : α` 判定命题 `a = b`。
-/
def DecidableEq : Unit := ()

/-- `DecidableRel (· < · : α → α → Prop)` 的缩写。 -/
def DecidableLT : Unit := ()

/-- `DecidableRel (· ≤ · : α → α → Prop)` 的缩写。 -/
def DecidableLE : Unit := ()

namespace Decidable

/--
将可判定命题转换为 `Bool`。

如果 `p : Prop` 可判定，那么 `decide p : Bool` 在 `p` 为真时是 `true`，在 `p` 为假时是
`false`。
-/
def decide : Unit := ()

/--
当命题 `p` 可判定，并且无论 `p` 为真还是为假都足以构造 `q` 时，构造一个 `q`。

这是依赖式 if-then-else 运算符 `dite` 的同义形式。
-/
def byCases : Unit := ()

end Decidable

/--
`Inhabited α` 是一个类型类，表示 `α` 有一个指定元素，称为 `(default : α)`。这种类型有时
称为“居留类型”。

需要在“定义域之外”被调用时仍返回该类型值的函数会使用这个类。例如，若 `arr : Array α`，
则 `Array.get! arr i : α` 在 `i` 越界时会报告 panic；但这不会终止程序，因此函数仍必须返回
一个 `α` 类型的值（逻辑一致性事实上也要求如此），此时它返回 `default`。
-/
class Inhabited (α : Sort u) where
  /-- `default` 生成任意居留类型的“默认”元素。该元素没有任何特别规定的性质，但通常是全零值。 -/
  default : α

/--
`Nonempty α` 是一个类型类，表示 `α` 不是空类型，即该类型中存在一个元素。它与
`Inhabited α` 的区别在于，`Nonempty α` 是一个 `Prop`，所以它实际上不携带 `α` 的元素，
只携带“存在这种元素”的证明。
给定 `Nonempty α`，可以使用 `Classical.choice` 以非构造方式构造 `α` 的元素。
-/
class inductive Nonempty (α : Sort u) : Prop where
  /-- 如果 `val : α`，那么 `α` 非空。 -/
  | intro (val : α) : Nonempty α

/--
_子单例_是至多有一个元素的类型：它要么为空，要么有唯一元素。

由于证明无关性，所有命题都是子单例：假命题为空，而真命题的任意两个证明彼此相等。
某些非命题类型也是子单例。
-/
class Subsingleton (α : Sort u) : Prop where
  /-- 通过证明任意两个元素相等来证明 `α` 是子单例。 -/
  intro ::
  /-- 子单例中的任意两个元素都相等。 -/
  allEq : (a b : α) → a = b

namespace Subsingleton

/-- 如果一个类型是子单例，那么它的所有元素都相等。 -/
def elim : Unit := ()

/--
如果两个类型相等，并且其中一个是子单例，那么它们的所有元素都
[异质相等](lean-manual://section/HEq)。
-/
def helim : Unit := ()

end Subsingleton

/--
可以转换为字符串以供显示的类型。

不要求所得字符串能够被解析回原始数据（具有这种期望的相似类型类参见 `Repr`）。
-/
class ToString (α : Type u) where
  /-- 将一个值转换为字符串。 -/
  toString : α → String

/-- 具有零元素的类型。 -/
class Zero (α : Type u) where
  /-- 该类型的零元素。 -/
  zero : α

/-- `n ≠ 0` 的类型类版本。 -/
class NeZero {R : Type u} [Zero R] (n : R) : Prop where
  /-- 命题 `n` 不等于零。 -/
  out : n ≠ Zero.zero

/--
异质加法记法的类型类。
它启用记法 `a + b : γ`，其中 `a : α`、`b : β`。
-/
class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a + b` 计算 `a` 与 `b` 的和。该记法的含义取决于类型。 -/
  hAdd : α → β → γ

/-- `HAdd` 的同质版本：`a + b : α`，其中 `a b : α`。 -/
class Add (α : Type u) where
  /-- `a + b` 计算 `a` 与 `b` 的和。参见 `HAdd`。 -/
  add : α → α → α

/--
异质减法记法的类型类。
它启用记法 `a - b : γ`，其中 `a : α`、`b : β`。
-/
class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a - b` 计算 `a` 与 `b` 的差。该记法的含义取决于类型。
  * 对自然数，此运算在 0 处饱和：当 `a ≤ b` 时，`a - b = 0`。
  -/
  hSub : α → β → γ

/-- `HSub` 的同质版本：`a - b : α`，其中 `a b : α`。 -/
class Sub (α : Type u) where
  /-- `a - b` 计算 `a` 与 `b` 的差。参见 `HSub`。 -/
  sub : α → α → α

/--
异质乘法记法的类型类。
它启用记法 `a * b : γ`，其中 `a : α`、`b : β`。
-/
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a * b` 计算 `a` 与 `b` 的积。该记法的含义取决于类型。 -/
  hMul : α → β → γ

/-- 标量乘法运算的类型类，记作 `•`（输入 `\bu`）。 -/
class SMul (M : Type u) (α : Type v) where
  /--
  `m • a : α` 表示 `m : M` 与 `a : α` 的积。该记法的含义取决于类型，但预期用于左作用。
  -/
  smul : M → α → α

/-- `HMul` 的同质版本：`a * b : α`，其中 `a b : α`。 -/
class Mul (α : Type u) where
  /-- `a * b` 计算 `a` 与 `b` 的积。参见 `HMul`。 -/
  mul : α → α → α

/--
异质除法记法的类型类。
它启用记法 `a / b : γ`，其中 `a : α`、`b : β`。
-/
class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a / b` 计算 `a` 除以 `b` 的结果。该记法的含义取决于类型。
  * 对 `Nat`、`Int`、`Rat`、`Real` 等大多数类型，`a / 0` 定义为 `0`。
  * 对 `Nat`，`a / b` 向下取整。
  * 对 `Int`，当 `b` 为正时 `a / b` 向下取整，当 `b` 为负时向上取整。其实现为
    `Int.ediv`，这是满足 `a % b + b * (a / b) = a` 且在 `b ≠ 0` 时满足
    `0 ≤ a % b < natAbs b` 的唯一函数。函数 `Int.fdiv`（向下取整）和 `Int.tdiv`
    （向零截断）提供其他取整约定。
  * 对 `Float`，`a / 0` 遵循 IEEE 754 除法语义，通常得到 `inf` 或 `nan`。
  -/
  hDiv : α → β → γ

/-- `HDiv` 的同质版本：`a / b : α`，其中 `a b : α`。 -/
class Div (α : Type u) where
  /-- `a / b` 计算 `a` 除以 `b` 的结果。参见 `HDiv`。 -/
  div : α → α → α

/-- `∣` 运算（输入 `\|`）的记法类型类；该运算表示整除。 -/
class Dvd (α : Type _) where
  /-- 整除。`a ∣ b`（输入 `\|`）表示存在某个 `c`，使得 `b = a * c`。 -/
  dvd : α → α → Prop

/--
异质模／余数记法的类型类。
它启用记法 `a % b : γ`，其中 `a : α`、`b : β`。
-/
class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a % b` 计算 `a` 除以 `b` 的余数。该记法的含义取决于类型。
  * 对 `Nat` 和 `Int`，它满足 `a % b + b * (a / b) = a`，且 `a % 0` 定义为 `a`。
  -/
  hMod : α → β → γ

/-- `HMod` 的同质版本：`a % b : α`，其中 `a b : α`。 -/
class Mod (α : Type u) where
  /-- `a % b` 计算 `a` 除以 `b` 的余数。参见 `HMod`。 -/
  mod : α → α → α

/--
异质幂运算记法的类型类。
它启用记法 `a ^ b : γ`，其中 `a : α`、`b : β`。
-/
class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^ b` 计算 `a` 的 `b` 次幂。该记法的含义取决于类型。 -/
  hPow : α → β → γ

/--
`HPow` 的同质版本：`a ^ b : α`，其中 `a : α`、`b : β`。（右参数与左参数类型不必相同，
因为即使在同质情形中也常有这种需求。）

类型可以通过提供 `NatPow` 或 `HomogeneousPow` 的实例来选择特定的默认行为：
- `NatPow` 用于指数优先为 `Nat` 的类型。
- `HomogeneousPow` 用于底数和指数优先具有相同类型的类型。
-/
class Pow (α : Type u) (β : Type v) where
  /-- `a ^ b` 计算 `a` 的 `b` 次幂。参见 `HPow`。 -/
  pow : α → β → α

/--
指数为 `Nat` 的 `Pow` 同质版本。此类的用途是提供默认 `Pow` 实例，使精译过程中可以将
指数特化为 `Nat`。

例如，如果 `x ^ 2` 应优先精译为 `2 : Nat`，那么 `x` 的类型应提供此类的实例。
-/
class NatPow (α : Type u) where
  /-- `a ^ n` 计算 `a` 的 `n` 次幂，其中 `n : Nat`。参见 `Pow`。 -/
  protected pow : α → Nat → α

/--
指数与底数类型相同的完全同质 `Pow` 版本。此类的用途是提供默认 `Pow` 实例，使精译过程中
可以将指数特化为与底数相同的类型。也就是说，当 `x ^ y` 应精译为 `x` 和 `y` 具有相同
类型时，该类型应提供此类的实例。

例如，`Float` 类型提供此类的实例，因此 `(2.2 ^ 2.2 : Float)` 这样的表达式可以精译。
-/
class HomogeneousPow (α : Type u) where
  /-- `a ^ b` 计算 `a` 的 `b` 次幂，其中 `a` 和 `b` 具有相同类型。 -/
  protected pow : α → α → α

/-- `a <<< b : γ` 记法背后的类型类，其中 `a : α`、`b : β`。 -/
class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a <<< b` 计算将 `a` 左移 `b` 位的结果。该记法的含义取决于类型。
  * 对 `Nat`，这等价于 `a * 2 ^ b`。
  * 对 `UInt8` 及其他固定位宽无符号类型，计算相同，但结果会截断到相应位宽。
  -/
  hShiftLeft : α → β → γ

/-- `HShiftLeft` 的同质版本：`a <<< b : α`，其中 `a b : α`。 -/
class ShiftLeft (α : Type u) where
  /-- `a <<< b : α` 的实现。参见 `HShiftLeft`。 -/
  shiftLeft : α → α → α

/-- `a >>> b : γ` 记法背后的类型类，其中 `a : α`、`b : β`。 -/
class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a >>> b` 计算将 `a` 右移 `b` 位的结果。该记法的含义取决于类型。
  * 对 `Nat` 和 `UInt8` 等固定位宽无符号类型，这等价于 `a / 2 ^ b`。
  -/
  hShiftRight : α → β → γ

/-- `HShiftRight` 的同质版本：`a >>> b : α`，其中 `a b : α`。 -/
class ShiftRight (α : Type u) where
  /-- `a >>> b : α` 的实现。参见 `HShiftRight`。 -/
  shiftRight : α → α → α

/--
取负记法的类型类。
它启用记法 `-a : α`，其中 `a : α`。
-/
class Neg (α : Type u) where
  /-- `-a` 计算 `a` 的负值或相反值。该记法的含义取决于类型。 -/
  neg : α → α

/-- `a &&& b : γ` 记法背后的类型类，其中 `a : α`、`b : β`。 -/
class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a &&& b` 计算 `a` 与 `b` 的逐位与。该记法的含义取决于类型。 -/
  hAnd : α → β → γ

/--
`HAnd` 的同质版本：`a &&& b : α`，其中 `a b : α`。
（之所以称为 `AndOp`，是因为 `And` 已用于命题合取。）
-/
class AndOp (α : Type u) where
  /-- `a &&& b : α` 的实现。参见 `HAnd`。 -/
  and : α → α → α

/-- `a ||| b : γ` 记法背后的类型类，其中 `a : α`、`b : β`。 -/
class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ||| b` 计算 `a` 与 `b` 的逐位或。该记法的含义取决于类型。 -/
  hOr : α → β → γ

/--
`HOr` 的同质版本：`a ||| b : α`，其中 `a b : α`。
（之所以称为 `OrOp`，是因为 `Or` 已用于命题析取。）
-/
class OrOp (α : Type u) where
  /-- `a ||| b : α` 的实现。参见 `HOr`。 -/
  or : α → α → α

/-- `a ^^^ b : γ` 记法背后的类型类，其中 `a : α`、`b : β`。 -/
class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^^^ b` 计算 `a` 与 `b` 的逐位异或。该记法的含义取决于类型。 -/
  hXor : α → β → γ

/-- `HXor` 的同质版本：`a ^^^ b : α`，其中 `a b : α`。 -/
class XorOp (α : Type u) where
  /-- `a ^^^ b : α` 的实现。参见 `HXor`。 -/
  xor : α → α → α

/--
异质追加记法的类型类。
它启用记法 `a ++ b : γ`，其中 `a : α`、`b : β`。
-/
class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ++ b` 是 `a` 与 `b` 的连接结果，通常读作“追加”。该记法的含义取决于类型。 -/
  hAppend : α → β → γ

/-- `HAppend` 的同质版本：`a ++ b : α`，其中 `a b : α`。 -/
class Append (α : Type u) where
  /-- `a ++ b` 是 `a` 与 `b` 的连接结果。参见 `HAppend`。 -/
  append : α → α → α

/--
`GetElem` 和 `GetElem?` 类实现元素查找记法，具体包括 `xs[i]`、`xs[i]?`、`xs[i]!` 和
`xs[i]'p`。

这两个类都以 `coll`、`idx` 和 `elem` 类型为索引，它们分别是容器、索引和元素类型。
一个容器可以支持使用多种索引类型进行查找。关系 `valid` 决定索引何时保证有效；有效索引
的查找保证不会失败。

例如，数组的实例形如 `GetElem (Array α) Nat α (fun xs i => i < xs.size)`。换言之，给定数组
`xs` 和自然数 `i`，当 `valid xs i` 成立时，`xs[i]` 返回一个 `α`；这里 `valid xs i` 在 `i`
小于数组大小时为真。`Array` 还支持使用 `USize` 而非 `Nat` 索引。无论哪种情况，由于边界
在编译时检查，运行时都不需要检查。

对于 `xs[i]`（其中 `xs : coll` 且 `i : idx`），Lean 会寻找
`GetElem coll idx elem valid` 的实例，并据此推断返回类型 `elem` 以及保证 `xs[i]` 产生有效
`elem` 值所需的旁条件 `valid`。系统调用 `get_elem_tactic` 策略自动证明有效性；`xs[i]'p`
记法则使用证明 `p` 满足有效性条件。若证明 `p` 很长，通常更容易用 `have` 将其放入上下文，
因为 `get_elem_tactic` 会尝试 `assumption`。

证明旁条件 `valid xs i` 会自动交给 `get_elem_tactic`；可以用 `macro_rules` 向
`get_elem_tactic_extensible` 添加更多分支来扩展该策略。

`xs[i]?` 和 `xs[i]!` 不产生证明义务：前者返回 `Option elem`，以 `none` 表示值不存在；后者
返回 `elem`，但在值不存在时会 panic，并根据 `Inhabited elem` 实例返回 `default : elem`。
这些操作由 `GetElem?` 类提供；只要 `valid xs i` 总是可判定，就可以从 `GetElem` 类生成默认
实例。

重要实例包括：
  * `arr[i] : α`，其中 `arr : Array α` 且 `i : Nat` 或 `i : USize`：执行数组索引，不做运行时
    边界检查，并产生证明旁目标 `i < arr.size`。
  * `l[i] : α`，其中 `l : List α` 且 `i : Nat`：索引列表，并产生证明旁目标 `i < l.length`。
-/
class GetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
    (valid : outParam (coll → idx → Prop)) where
  /--
  语法 `arr[i]` 获取容器 `arr` 的第 `i` 个元素。如果应用存在证明旁条件，
  `get_elem_tactic` 策略会自动推断它们。
  -/
  getElem (xs : coll) (i : idx) (h : valid xs i) : elem

/--
`GetElem` 和 `GetElem?` 类实现元素查找记法，具体包括 `xs[i]`、`xs[i]?`、`xs[i]!` 和
`xs[i]'p`。容器、索引、元素类型及有效性关系的含义与 `GetElem` 相同。
-/
class GetElem? (coll : Type u) (idx : Type v) (elem : outParam (Type w))
    (valid : outParam (coll → idx → Prop)) extends _root_.GetElem coll idx elem valid where
  /--
  语法 `arr[i]?` 获取容器 `arr` 的第 `i` 个元素；若元素存在则包装在 `some` 中，否则返回
  `none`。
  -/
  getElem? : coll → idx → Option elem

  /--
  语法 `arr[i]!` 获取容器 `arr` 的第 `i` 个元素；若元素存在则返回它，否则在运行时 panic，
  并返回 `Inhabited elem` 中的 `default` 项。
  -/
  getElem! [_root_.Inhabited elem] (xs : coll) (i : idx) : elem :=
    match getElem? xs i with | some e => e | none => outOfBounds

/--
合法的 `GetElem?` 实例（它扩展 `GetElem`）应使可能失败的 `GetElem?.getElem?` 和
`GetElem?.getElem!` 运算符在有效性谓词成立时成功，在不成立时失败。
-/
class LawfulGetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w))
    (dom : outParam (cont → idx → Prop)) [ge : _root_.GetElem? cont idx elem dom] : Prop where
  /-- `GetElem?.getElem?` 在有效性谓词成立时成功，否则失败。 -/
  getElem?_def (c : cont) (i : idx) [_root_.Decidable (dom c i)] :
      c[i]? = if h : dom c i then some (c[i]'h) else none := by
    intros
    try simp only [getElem?] <;> congr

  /-- `GetElem?.getElem!` 的成败与 `GetElem?.getElem?` 的成败一致。 -/
  getElem!_def [_root_.Inhabited elem] (c : cont) (i : idx) :
      c[i]! = match c[i]? with | some e => e | none => default := by
    intros
    simp only [getElem!, getElem?, outOfBounds_eq_default]

end ZhDoc.Classes.BasicClasses
