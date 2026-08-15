import VersoManual
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Classes.BasicClasses

/--
`BEq α` 是为 `α` 提供布尔值相等关系的类型类，记作 `a == b`。与使用
`a = b` 的 `DecidableEq α` 不同，该关系取值于 `Bool` 而不是 `Prop`，也不要求满足
自反性或与 `=` 一致之类的公理。它主要用于编程。若需要保证 `==` 与 `=` 一致，
请参阅 `LawfulBEq`。

通常应将“变化较多”的项放在左侧，将“较为固定”的项放在右侧。
-/
class BEq (α : Type u) where
  /-- 布尔相等性测试，记作 `a == b`。 -/
  beq : α → α → Bool

/-- 可哈希为 `UInt64` 的类型。 -/
class Hashable (α : Sort u) where
  /-- 将一个值哈希为 `UInt64`。 -/
  hash : α → UInt64

/-- 一种不透明的哈希混合操作，用于实现积类型的哈希。 -/
def mixHash : Unit := ()

/--
布尔相等性测试与命题相等一致。

换言之：
 * `a == b` 蕴含 `a = b`。
 * `a == a` 为真。
-/
class LawfulBEq (α : Type u) [_root_.BEq α] : Prop extends _root_.ReflBEq α where
  /-- 若 `a == b` 求值为 `true`，则 `a` 与 `b` 在逻辑上相等。 -/
  eq_of_beq : {a b : α} → a == b → a = b

/-- `ReflBEq α` 表示 `BEq` 的实现是自反的。 -/
class ReflBEq (α) [_root_.BEq α] : Prop where
  /-- `==` 是自反的，即 `(a == a) = true`。 -/
  protected rfl {a : α} : a == a

/-- `EquivBEq` 表示 `BEq` 的实现是一个等价关系。 -/
class EquivBEq (α) [_root_.BEq α] : Prop extends _root_.PartialEquivBEq α, _root_.ReflBEq α

/--
`α` 上的 `BEq α` 与 `Hashable α` 实例彼此兼容。这意味着 `a == b` 蕴含
`hash a = hash b`。

若 `BEq` 实例是合法的，则该性质自动成立。
-/
class LawfulHashable (α : Type u) [_root_.BEq α] [_root_.Hashable α] where
  /-- 若 `a == b`，则 `hash a = hash b`。 -/
  hash_eq (a b : α) : a == b → _root_.Hashable.hash a = _root_.Hashable.hash b

/-- 合法的哈希函数遵循其布尔相等性测试。 -/
def hash_eq : Unit := ()

/--
`Ord α` 通过函数 `compare : α → α → Ordering` 为 `α` 提供可计算的全次序。

实例通常具有传递性、自反性和反对称性，但类型类并不强制这些性质。

该类具有派生处理器，因此在归纳类型或结构体后添加 `deriving Ord` 时，Lean 会尝试创建
一个 `Ord` 实例。
-/
class Ord (α : Type u) where
  /-- 使用 `[Ord α]` 实例中包含的比较器比较 `α` 中的两个元素。 -/
  compare : α → α → _root_.Ordering

/--
通过比较应用某个函数所得的结果来比较两个值。

具体而言，通过比较 `f x` 与 `f y` 来比较 `x` 与 `y`。

示例：
 * `compareOn (·.length) "apple" "banana" = .lt`
 * `compareOn (· % 3) 5 6 = .gt`
 * `compareOn (·.foldl max 0) [1, 2, 3] [3, 2, 1] = .eq`
-/
def compareOn : Unit := ()

namespace Ord

/--
反转一个 `Ord` 实例的次序。

结果是一个 `Ord α` 实例：当 `ord` 返回 `Ordering.gt` 时它返回 `Ordering.lt`，
当 `ord` 返回 `Ordering.lt` 时它返回 `Ordering.gt`。
-/
def opposite : Unit := ()

end Ord

/--
按全次序进行比较所得的结果。

被比较项之间的关系可以是：
 * `Ordering.lt`：小于
 * `Ordering.eq`：等于
 * `Ordering.gt`：大于
-/
inductive Ordering where
  /-- 小于。 -/
  | lt
  /-- 等于。 -/
  | eq
  /-- 大于。 -/
  | gt

namespace Ordering

/--
交换小于与大于这两种比较结果。

示例：
 * `Ordering.lt.swap = Ordering.gt`
 * `Ordering.eq.swap = Ordering.eq`
 * `Ordering.gt.swap = Ordering.lt`
-/
def swap : Unit := ()

/--
若 `a` 与 `b` 均为 `Ordering`，则除非 `a` 是 `.eq`，`a.then b` 都返回 `a`；当
`a` 是 `.eq` 时，它返回 `b`。此外，它还具有类似布尔运算 `&&` 的“短路”行为：若
`a` 不是 `.eq`，则不会求值表达式 `b`。

这是构造字典序比较函数时很有用的基本操作。对结构体使用 `deriving Ord` 语法时，
会通过 `Ord` 实例依次比较各字段，并以等价于 `Ordering.then` 的方式组合结果。

可使用 `compareLex` 按字典序组合两个比较函数。

示例：
```lean example
structure Person where
  name : String
  age : Nat

-- 先按姓名升序排列；姓名相同时，再按年龄降序排列
instance : Ord Person where
  compare a b := (compare a.name b.name).then (compare b.age a.age)
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Dana", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 20⟩
```
```output
Ordering.lt
```
-/
def «then» : Unit := ()

/-- 检查比较结果是否为 `lt`。 -/
def isLT : Unit := ()

/-- 检查比较结果是否为 `lt` 或 `eq`。 -/
def isLE : Unit := ()

/-- 检查比较结果是否为 `eq`。 -/
def isEq : Unit := ()

/-- 检查比较结果是否不为 `eq`。 -/
def isNe : Unit := ()

/-- 检查比较结果是否为 `gt` 或 `eq`。 -/
def isGE : Unit := ()

/-- 检查比较结果是否为 `gt`。 -/
def isGT : Unit := ()

end Ordering

/--
使用可判定的严格小于关系和相等关系求出一个 `Ordering`。

具体而言，若 `x < y`，结果为 `Ordering.lt`；若 `x = y`，结果为 `Ordering.eq`；
否则结果为 `Ordering.gt`。

`compareOfLessAndBEq` 使用 `BEq` 而不是 `DecidableEq`。
-/
def compareOfLessAndEq : Unit := ()

/--
使用可判定的严格小于关系和布尔相等性测试求出一个 `Ordering`。

具体而言，若 `x < y`，结果为 `Ordering.lt`；若 `x == y`，结果为 `Ordering.eq`；
否则结果为 `Ordering.gt`。

`compareOfLessAndEq` 使用 `DecidableEq` 而不是 `BEq`。
-/
def compareOfLessAndBEq : Unit := ()

/--
使用 `cmp₁` 和 `cmp₂` 按字典序比较 `a` 与 `b`。

首先用 `cmp₁` 比较 `a` 与 `b`。若其返回 `Ordering.eq`，则用 `cmp₂` 比较
`a` 与 `b`，以打破平局。

若要按字典序组合两个 `Ordering`，请使用 `Ordering.then`。
-/
def compareLex : Unit := ()

/-- `LT α` 是支持记法 `x < y`（其中 `x y : α`）的类型类。 -/
class LT (α : Type u) where
  /-- 严格小于关系：`x < y`。 -/
  lt : α → α → Prop

/-- `LE α` 是支持记法 `x ≤ y`（其中 `x y : α`）的类型类。 -/
class LE (α : Type u) where
  /-- 小于等于关系：`x ≤ y`。 -/
  le : α → α → Prop

/--
从 `Ord` 实例构造一个 `LT` 实例；该实例断言 `compare` 的结果为 `Ordering.lt`。
-/
def ltOfOrd : Unit := ()

/--
从 `Ord` 实例构造一个 `LE` 实例；该实例断言 `compare` 的结果满足 `Ordering.isLE`。
-/
def leOfOrd : Unit := ()

namespace Ord

/-- 从 `Ord` 实例构造一个 `BEq` 实例。 -/
def toBEq : Unit := ()

/-- 从 `Ord` 实例构造一个 `LE` 实例。 -/
def toLE : Unit := ()

/-- 从 `Ord` 实例构造一个 `LT` 实例。 -/
def toLT : Unit := ()

/-- 根据 `α` 和 `β` 上的次序，构造积类型 `α × β` 上的字典序。 -/
def lex : Unit := ()

/--
按字典序组合两个已有实例，构造一个 `Ord` 实例。

所得实例先用 `ord₁` 比较元素；若其返回 `Ordering.eq`，再用 `ord₂` 比较。

函数 `compareLex` 可以在不构造中间 `Ord` 实例的情况下完成这种比较。
`Ordering.then` 可以按字典序组合各次比较的结果。
-/
def lex' : Unit := ()

/--
构造一个 `Ord` 实例，它根据应用 `f` 所得的结果比较值。

具体而言，`ord.on f` 根据 `ord` 比较 `f x` 与 `f y`，从而比较 `x` 与 `y`。

函数 `compareOn` 可以在不构造中间 `Ord` 实例的情况下完成这种比较。
-/
def on : Unit := ()

end Ord

/-- 对类型 `α` 的两个值执行可重载的最大值操作。 -/
class Max (α : Type u) where
  /-- 返回两个参数中较大的一个。 -/
  max : α → α → α

/-- 对类型 `α` 的两个值执行可重载的最小值操作。 -/
class Min (α : Type u) where
  /-- 返回两个参数中较小的一个。 -/
  min : α → α → α

/-- 从可判定的 `≤` 操作构造一个 `Min` 实例。 -/
def minOfLe : Unit := ()

/-- 从可判定的 `≤` 操作构造一个 `Max` 实例。 -/
def maxOfLe : Unit := ()

end ZhDoc.Classes.BasicClasses
