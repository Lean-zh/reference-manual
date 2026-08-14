import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc

/--
半环，即配备加法、乘法以及自然数到该类型的映射，并满足相应相容性条件的类型。

若该类型还带有取负运算，请改用 `Ring`；若乘法可交换，请改用 `CommSemiring`；若既有取负运算且乘法可交换，请改用 `CommRing`。
-/
class Semiring (α : Type u) extends Add α, Mul α where
  /-- 每个半环中都有从自然数到该半环的典范映射，它给出 `0` 和 `1` 的值。注意，此函数不一定是单射。 -/
  [natCast : NatCast α]
  /-- 半环中的自然数数值。字段 `ofNat_eq_natCast` 保证它们在命题意义下等于 `natCast` 的值。 -/
  [ofNat : ∀ n, OfNat α n]
  /-- 自然数标量乘法。 -/
  [nsmul : SMul Nat α]
  /-- 自然数幂运算。 -/
  [npow : HPow α Nat α]
  /-- 零是加法右单位元。 -/
  add_zero : ∀ a : α, a + 0 = a
  /-- 加法可交换。 -/
  add_comm : ∀ a b : α, a + b = b + a
  /-- 加法满足结合律。 -/
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  /-- 乘法满足结合律。 -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  /-- 一是乘法右单位元。 -/
  mul_one : ∀ a : α, a * 1 = a
  /-- 一是乘法左单位元。 -/
  one_mul : ∀ a : α, 1 * a = a
  /-- 乘法对加法满足左分配律。 -/
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  /-- 乘法对加法满足右分配律。 -/
  right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c
  /-- 零对乘法具有右吸收性。 -/
  zero_mul : ∀ a : α, 0 * a = 0
  /-- 零对乘法具有左吸收性。 -/
  mul_zero : ∀ a : α, a * 0 = 0
  /-- 任意元素的零次幂为一。 -/
  pow_zero : ∀ a : α, a ^ 0 = 1
  /-- 幂运算的后继律。 -/
  pow_succ : ∀ a : α, ∀ n : Nat, a ^ (n + 1) = (a ^ n) * a
  /-- 数值与加法的定义相容。 -/
  ofNat_succ : ∀ a : Nat, OfNat.ofNat (α := α) (a + 1) = OfNat.ofNat a + 1 := by intros; rfl
  /-- 数值与自然数的典范映射相容。 -/
  ofNat_eq_natCast : ∀ n : Nat, OfNat.ofNat (α := α) n = Nat.cast n := by intros; rfl
  /-- 乘以数值与自然数的典范映射相容。 -/
  nsmul_eq_natCast_mul : ∀ n : Nat, ∀ a : α, n • a = Nat.cast n * a := by intros; rfl

attribute [implicit_reducible] Semiring.npow Semiring.ofNat Semiring.natCast

/--
环，即配备加法、取负、乘法以及整数到该类型的映射，并满足相应相容性条件的类型。

若乘法可交换，请改用 `CommRing`。
-/
class Ring (α : Type u) extends Semiring α, Neg α, Sub α where
  /-- 每个环中都有从整数到该环的典范映射。 -/
  [intCast : IntCast α]
  /-- 整数标量乘法。 -/
  [zsmul : SMul Int α]
  /-- 取负是加法的左逆。 -/
  neg_add_cancel : ∀ a : α, -a + a = 0
  /-- 减法等于加上相反数。 -/
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  /-- 负整数的标量乘法等于相应标量乘法的相反数。 -/
  neg_zsmul : ∀ (i : Int) (a : α), (-i : Int) • a = -(i • a)
  /-- 自然数标量乘法与整数标量乘法相容。 -/
  zsmul_natCast_eq_nsmul : ∀ n : Nat, ∀ a : α, (n : Int) • a = n • a := by intros; rfl
  /-- 整数的典范映射与自然数的典范映射相容。 -/
  intCast_ofNat : ∀ n : Nat, Int.cast (OfNat.ofNat (α := Int) n) = OfNat.ofNat (α := α) n := by intros; rfl
  /-- 整数的典范映射与取负运算相容。 -/
  intCast_neg : ∀ i : Int, Int.cast (R := α) (-i) = -Int.cast i := by intros; rfl

/--
交换半环，即乘法可交换的半环。

若该类型还带有取负运算，请改用 `CommRing`。
-/
class CommSemiring (α : Type u) extends Semiring α where
  /-- 乘法可交换。 -/
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul := by intro a; rw [mul_comm, mul_one]
  mul_zero := by intro a; rw [mul_comm, zero_mul]
  right_distrib := by intro a b c; rw [mul_comm, left_distrib, mul_comm c, mul_comm c]

/-- 交换环，即乘法可交换的环。 -/
class CommRing (α : Type u) extends Ring α, CommSemiring α

/-- 域，即每个非零元素都有逆元的交换环。 -/
class Field (α : Type u) extends CommRing α, Inv α, Div α where
  /-- 幂运算符。 -/
  [zpow : HPow α Int α]
  /-- 除法等于乘以逆元。 -/
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  /-- 零不等于一；域是非平凡的。 -/
  zero_ne_one : (0 : α) ≠ 1
  /-- 零的逆元定义为零。这是一项“无效值”约定。 -/
  inv_zero : (0 : α)⁻¹ = 0
  /-- 非零元素的逆元是其右逆。 -/
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1
  /-- 任意元素的零次幂为一。 -/
  zpow_zero : ∀ a : α, a ^ (0 : Int) = 1
  /-- 任意元素的第 `n+1` 次幂等于其第 `n` 次幂乘以该元素。 -/
  zpow_succ : ∀ (a : α) (n : Nat), a ^ (n + 1 : Int) = a ^ (n : Int) * a
  /-- 负次幂等于相应正次幂的逆元。 -/
  zpow_neg : ∀ (a : α) (n : Int), a ^ (-n) = (a ^ n)⁻¹

/--
若 `OfNat.ofNat x = 0` 当且仅当 `x % p = 0`，则称环 `α` 的特征为 `p`。

当 `p = 0` 时，`x % p = x`，因此这表示 `OfNat.ofNat` 是从 `Nat` 到 `α` 的单射。

对于半环，这里采用更强的条件：`OfNat.ofNat x = OfNat.ofNat y` 当且仅当 `x % p = y % p`。
-/
class IsCharP (α : Type u) [Semiring α] (p : outParam Nat) where
  /-- 半环中的两个数值相等，当且仅当它们作为自然数模 `p` 同余。 -/
  ofNat_ext_iff : Prop

/--
若 `k ≠ 0` 且 `k • a = k • b` 能推出 `a = b`，则称模没有自然数零因子（其中 `k` 是自然数，`a`、`b` 是模中的元素）。

对于整数模，这等价于：`k ≠ 0` 且 `k • a = 0` 能推出 `a = 0`。（参见另一构造器 `NoNatZeroDivisors.mk'` 及定理 `eq_zero_of_mul_eq_zero`。）
-/
class NoNatZeroDivisors (α : Type u) [Lean.Grind.NatModule α] where
  /-- 若 `k • a = k • b`，且 `k ≠ 0`，则 `a = b`。 -/
  no_nat_zero_divisors : ∀ (k : Nat) (a b : α), k ≠ 0 → k • a = k • b → a = b

namespace NoNatZeroDivisors

/-- 当存在 `IntModule` 实例时，用于构造 `NoNatZeroDivisors` 的另一种构造器。 -/
def mk' : Prop := True

end NoNatZeroDivisors

/-- 加法满足右消去律的类型，即 `a + c = b + c` 蕴含 `a = b`。 -/
class AddRightCancel (M : Type u) [Add M] where
  /-- 加法满足右消去律。 -/
  add_right_cancel : ∀ a b c : M, a + c = b + c → a = b

/--
自然数上的模，即配备零、加法和自然数标量乘法，并满足相应相容性条件的类型。

等价地说，它是加法交换幺半群。若该类型带有取负运算，请改用 `IntModule`。
-/
class NatModule (M : Type u) extends Lean.Grind.AddCommMonoid M where
  /-- 自然数标量乘法。 -/
  [nsmul : SMul Nat M]
  /-- 零的标量乘法为零。 -/
  zero_nsmul : ∀ a : M, 0 • a = 0
  /-- 后继数的标量乘法。 -/
  add_one_nsmul : ∀ n : Nat, ∀ a : M, (n + 1) • a = n • a + a

/--
整数上的模，即配备零、加法、取负、减法和整数标量乘法，并满足相应相容性条件的类型。

等价地说，它是加法交换群。
-/
class IntModule (M : Type u) extends Lean.Grind.AddCommGroup M where
  /-- 自然数标量乘法。 -/
  [nsmul : SMul Nat M]
  /-- 整数标量乘法。 -/
  [zsmul : SMul Int M]
  /-- 零的标量乘法为零。 -/
  zero_zsmul : ∀ a : M, (0 : Int) • a = 0
  /-- 一的标量乘法是恒等映射。 -/
  one_zsmul : ∀ a : M, (1 : Int) • a = a
  /-- 标量乘法对整数加法满足分配律。 -/
  add_zsmul : ∀ n m : Int, ∀ a : M, (n + m) • a = n • a + m • a
  /-- 自然数标量乘法与整数标量乘法相容。 -/
  zsmul_natCast_eq_nsmul : ∀ n : Nat, ∀ a : M, (n : Int) • a = n • a

/-- 若 `a ≤ b ↔ a + c ≤ b + c`，则称加法与预序相容。 -/
class OrderedAdd (M : Type u) [HAdd M M M] [LE M] [Std.IsPreorder M] where
  /-- `a + c ≤ b + c` 当且仅当 `a ≤ b`。 -/
  add_le_left_iff : ∀ {a b : M} (c : M), a ≤ b ↔ a + c ≤ b + c

/--
若一个环还配备预序，加法、取负和乘法均与该预序相容，并且 `0 < 1`，则称其为严格有序环。
-/
class OrderedRing (R : Type u) [Semiring R] [LE R] [LT R] [Std.IsPreorder R]
    extends OrderedAdd R where
  /-- 在严格有序半环中，`0 < 1`。 -/
  zero_lt_one : Prop
  /-- 在严格有序半环中，可用正元素 `0 < c` 从左侧乘不等式 `a < b`，得到 `c * a < c * b`。 -/
  mul_lt_mul_of_pos_left : Prop
  /-- 在严格有序半环中，可用正元素 `0 < c` 从右侧乘不等式 `a < b`，得到 `a * c < b * c`。 -/
  mul_lt_mul_of_pos_right : Prop

/-- 整数区间，可以是有限、半无限或无限区间。 -/
inductive IntInterval : Type where
  | /-- 有限区间 `[lo, hi)`。 -/
    co (lo hi : Int)
  | /-- 半无限区间 `[lo, ∞)`。 -/
    ci (lo : Int)
  | /-- 半无限区间 `(-∞, hi)`。 -/
    io (hi : Int)
  | /-- 无限区间 `(-∞, ∞)`。 -/
    ii

/-- `ToInt α I` 表示可以将 `α` 忠实地嵌入整数区间 `I`。 -/
class ToInt (α : Type u) (range : outParam Lean.Grind.IntInterval) where
  /-- 嵌入函数。 -/
  toInt : α → Int
  /-- 嵌入函数是单射。 -/
  toInt_inj : ∀ x y, toInt x = toInt y → x = y
  /-- 嵌入函数的值落在指定区间内。 -/
  toInt_mem : ∀ x, toInt x ∈ range

namespace Parser.Attr

/-- `cases` 修饰符将归纳定义的谓词标记为适合进行情形拆分。 -/
def grindCases := Prop

/-- `cases eager` 修饰符将归纳定义的谓词标记为适合进行情形拆分，并指示 `grind` 在预处理假设时立即拆分。 -/
def grindCasesEager := Prop

/--
`.` 修饰符指示 `grind` 先遍历定理的结论，再从左到右遍历各项假设，以选择一个多模式；这称为默认修饰符。每当遇到覆盖尚未覆盖参数的子表达式时，就将其加入模式，直到所有参数均被覆盖。使用 `grind!` 时，只考虑最小的可索引子表达式。
-/
def grindDef := Prop

/-- `=` 修饰符指示 `grind` 检查定理结论是否为等式，然后将等式左侧用作模式。若左侧没有出现所有参数，此操作可能失败。 -/
def grindEq := Prop

/-- `=_` 修饰符指示 `grind` 检查定理结论是否为等式，然后将等式右侧用作模式。若右侧没有出现所有参数，此操作可能失败。 -/
def grindEqRhs := Prop

/-- `_=_` 修饰符类似一个展开为 `=` 和 `=_` 的宏。它添加两个模式，使等式定理可由任一方向触发。 -/
def grindEqBoth := Prop

/--
`→` 修饰符指示 `grind` 从定理的假设中选择一个多模式，即使用该定理进行前向推理。它从左到右遍历各项假设，每遇到覆盖尚未覆盖参数的子表达式，就将其加入模式，直到所有参数均被覆盖。使用 `grind!` 时，只考虑最小的可索引子表达式。
-/
def grindFwd := Prop

/--
`←` 修饰符指示 `grind` 从定理结论中选择一个多模式，即使用该定理进行后向推理。若结论中未出现定理的所有参数，此操作可能失败。每遇到覆盖尚未覆盖参数的子表达式，就将其加入模式，直到所有参数均被覆盖。使用 `grind!` 时，只考虑最小的可索引子表达式。
-/
def grindBwd := Prop

/--
`⇒` 修饰符指示 `grind` 先从左到右遍历全部假设，再遍历结论，以选择一个多模式。每遇到覆盖尚未覆盖参数的子表达式，就将其加入模式，直到所有参数均被覆盖。使用 `grind!` 时，只考虑最小的可索引子表达式。
-/
def grindLR := Prop

/--
`⇐` 修饰符指示 `grind` 先遍历结论，再从右到左遍历全部假设，以选择一个多模式。每遇到覆盖尚未覆盖参数的子表达式，就将其加入模式，直到所有参数均被覆盖。使用 `grind!` 时，只考虑最小的可索引子表达式。
-/
def grindRL := Prop

/--
`←=` 修饰符专用于对等式进行后向推理，与其他 `grind` 修饰符不同。当定理结论是等式命题且以 `@[grind ←=]` 标注时，只要假设了对应的不等关系，`grind` 就会实例化该定理；这是因为 `grind` 的所有证明均采用反证法。通常，`grind` 属性生成模式时不会考虑 `=` 符号。
-/
def grindEqBwd := Prop

/--
`funCC` 修饰符标记支持**函数值同余闭包**的全局函数。对于应用 `f a₁ a₂ … aₙ`，启用 `funCC` 后，`grind` 会为所有部分应用生成并跟踪等式：`f a₁`、`f a₁ a₂`、……、`f a₁ a₂ … aₙ`。
-/
def grindFunCC := Prop

/-- `ext` 修饰符标记供 `grind` 使用的外延性定理。例如，标准库用此属性标记 `funext`。每当 `grind` 遇到不等关系 `a ≠ b` 时，它会尝试应用类型与 `a`、`b` 相匹配的外延性定理。 -/
def grindExt := Prop

/-- `inj` 修饰符标记供 `grind` 使用的单射性定理。定理结论必须形如 `Function.Injective f`，且项 `f` 至少包含一个常量符号。 -/
def grindInj := Prop

/--
`intro` 修饰符指示 `grind` 将归纳谓词的构造器（引入规则）用作 E-matching 定理。例如：
```
inductive Even : Nat → Prop where
| zero : Even 0
| add2 : Even x → Even (x + 2)

attribute [grind intro] Even
example (h : Even x) : Even (x + 6) := by grind
example : Even 0 := by grind
```
这里，`attribute [grind intro] Even` 的作用类似于一个宏，会展开为
`attribute [grind] Even.zero` 和 `attribute [grind] Even.add2`。
这对构造器较多的归纳谓词尤其方便。
-/
def grindIntro := Prop

/--
`unfold` 修饰符指示 `grind` 在预处理阶段展开给定定义。例如：
```
@[grind unfold] def h (x : Nat) := 2 * x
example : 6 ∣ 3*h x := by grind
```
-/
def grindUnfold := Prop

/--
`norm` 修饰符指示 `grind` 将定理用作规范化规则，即在预处理阶段应用该定理。
这一功能面向了解预处理器与 `grind` 搜索过程如何交互的高级用户。
新用户仍可将其限用于能从目标中彻底消除某个符号的定理，例如：
```
theorem max_def : max n m = if n ≤ m then m else n
```
以下是一个反例：
```
opaque f : Int → Int → Int → Int
theorem fax1 : f x 0 1 = 1 := sorry
theorem fax2 : f 1 x 1 = 1 := sorry
attribute [grind norm] fax1
attribute [grind =] fax2

example (h : c = 1) : f c 0 c = 1 := by
  grind -- 失败
```
在此例中，`fax1` 是规范化规则，但它无法应用于输入目标，因为 `f c 0 c` 不是 `f x 0 1` 的实例。
不过，模等式 `c = 1` 而言，`f c 0 c` 匹配模式 `f 1 x 1`。
因此，`grind` 以 `x := 0` 实例化 `fax2`，得到等式 `f 1 0 1 = 1`，随后规范化器将其化简为 `True`，结果没有获得任何有用信息。
未来计划加入检查器，以自动检测这类问题。

示例：
```
opaque f : Nat → Nat
opaque g : Nat → Nat

@[grind norm] axiom fax : f x = x + 2
@[grind norm ←] axiom fg : f x = g x

example : f x ≥ 2 := by grind
example : f x ≥ g x := by grind
example : f x + g x ≥ 4 := by grind
```
-/
def grindNorm := Prop

/--
`hom` 修饰符将定理标记为 `grind` 的同态规则。

同态规则把项从源代数转换到拥有专用求解器的目标代数。一组同态规则可编码代数同态 `h : A → B`：每条规则说明 `h` 如何与某项源域运算交换，例如 `h (f x y) = g (h x) (h y)`。
以下示例使用 `BitVec.toNat`，把位向量运算注入整数算术：
```
@[grind hom] theorem toNat_add (x y : BitVec w) :
    (x + y).toNat = (x.toNat + y.toNat) % 2^w
```
规则必须是无条件等式（或 `Iff`）。它们会在 E-图外反复应用至不动点，只有最终结果会被内部化。
-/
def grindHom := Prop

/--
`hom_pred` 修饰符将定理标记为 `grind` 的同态谓词。

同态谓词是 `grind` 会针对所内部化的项立即实例化的事实。
定理结论必须含有应用 `f a₁ … aₙ`，其末尾参数恰为定理的显式参数；头符号 `f` 将成为触发器。
典型用途包括注入函数的值域事实，以及把关系转换到目标域。例如：
```
@[grind hom_pred] theorem BitVec.toNat_range (x : BitVec w) : x.toNat < 2^w
@[grind hom_pred] theorem UInt8.le_iff (a b : UInt8) : a ≤ b ↔ a.toBitVec ≤ b.toBitVec
```
第一条定理由形如 `BitVec.toNat x` 的项触发，第二条则由 `a ≤ b` 应用触发。
`grind` 会利用 `a` 和 `b` 的类型排除无关的实例化。
-/
def grindHomPred := Prop

end Parser.Attr

namespace Option

/-- 启用后，`grind` 会输出关于命题拆分过程的跟踪消息。 -/
def trace.grind.split := Prop

/-- 启用后，`grind` 会为其生成的每个 E-matching 定理实例输出一条跟踪消息；这有助于检查和调试实例化模式。 -/
def trace.grind.ematch.instance := Prop

end Option

end ZhDoc
