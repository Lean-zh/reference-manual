import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.RecursiveDefs

/--
此函数把类型 `α` 的值强制转换为类型 `β`，在编译器中不执行任何操作。它是
**极其危险**的：无法保证 `α` 与 `β` 具有相同的数据表示，因而可能导致内存不安全；
它在逻辑上也不可靠，因为可以直接把 `True` 强制转换为 `False`。出于这些原因，
此函数被标记为 `unsafe`。

其实现先把 `α` 与 `β` 提升到同一个宇宙，再使用
`cast (lcProof : ULift (PLift α) = ULift (PLift β))` 实际执行强制转换。
这些操作在编译器中全都不执行任何操作。

正确使用此函数需要了解源类型和目标类型的数据表示。以下几类强制转换在当前运行时中
是安全的：

* 当 `α` 与 `β` 的表示兼容时，从 `Array α` 到 `Array β`；更一般地，其他归纳类型亦然。
* `Quot α r` 与 `α` 之间。
* `@Subtype α p` 与 `α` 之间；更一般地，只含一个类型为 `α` 的非 `Prop` 字段的任何结构体亦然。
* 当 `α` 是装箱的泛型类型时，在 `α` 与 `NonScalar` 之间转换；所谓装箱的泛型类型，
  是指接受任意类型 `α`、且不会特化为 `UInt8` 等标量类型的函数所处理的类型。
-/
def unsafeCast : Unit := ()

/--
比较两个对象的指针是否相等。

若两个对象在运行时恰好分配在同一地址上，则它们的指针相等。此函数是不安全的，
因为它能够区分定义相等的值。
-/
def ptrEq : Unit := ()

/--
逐元素比较两个对象列表的指针是否相等。当两个列表长度相同，且对应索引处对象的
指针都相等时，返回 `true`。

若两个对象在运行时恰好分配在同一地址上，则它们的指针相等。此函数是不安全的，
因为它能够区分定义相等的值。
-/
def ptrEqList : Unit := ()

/--
返回对象被分配到的地址。

此函数是不安全的，因为它能够区分定义相等的值。
-/
def ptrAddrUnsafe : Unit := ()

/--
若 `a` 是独占对象，则返回 `true`。

对象为单线程使用且其引用计数为 1 时，该对象是独占的。此函数是不安全的，因为它
能够区分定义相等的值。
-/
def isExclusiveUnsafe : Unit := ()

/--
在纯上下文中执行任意副作用，并通过 `Except` 表示异常。这是一项**危险**操作，
很容易破坏 Lean 程序含义所依赖的重要假设。只有在透彻理解编译器内部机制、并且
仅用于实现观察上纯净的操作时，才应极其谨慎地使用它。

此函数并不是把 `EIO ε α` 或 `IO α` 转换为 `α` 的好方法；应改用
[`do` 记法](lean-manual://section/do-notation)。

由于所得值会被视为无副作用的项，编译器可能对该函数的调用重新排序、复制或删除。
副作用甚至可能被提升到常量的初始化过程中，因此即使原本永远不会调用，也可能在
初始化时发生。
-/
def unsafeIO : Unit := ()

/--
在纯上下文中执行任意副作用，并通过 `Except` 表示异常。这是一项**危险**操作，
很容易破坏 Lean 程序含义所依赖的重要假设。只有在透彻理解编译器内部机制、并且
仅用于实现观察上纯净的操作时，才应极其谨慎地使用它。

此函数并不是把 `EIO ε α` 或 `IO α` 转换为 `α` 的好方法；应改用
[`do` 记法](lean-manual://section/do-notation)。

由于所得值会被视为无副作用的项，编译器可能对该函数的调用重新排序、复制或删除。
副作用甚至可能被提升到常量的初始化过程中，因此即使原本永远不会调用，也可能在
初始化时发生。
-/
def unsafeEIO : Unit := ()

/--
在纯上下文中执行任意副作用。这是一项**危险**操作，很容易破坏 Lean 程序含义所
依赖的重要假设。只有在透彻理解编译器内部机制、并且仅用于实现观察上纯净的操作时，
才应极其谨慎地使用它。

此函数并不是把 `BaseIO α` 转换为 `α` 的好方法；应改用
[`do` 记法](lean-manual://section/do-notation)。

由于所得值会被视为无副作用的项，编译器可能对该函数的调用重新排序、复制或删除。
副作用甚至可能被提升到常量的初始化过程中，因此即使原本永远不会调用，也可能在
初始化时发生。
-/
def unsafeBaseIO : Unit := ()

namespace Parser

/--
`seal foo` 命令确保定义 `foo` 被封闭，即将其标记为 `[irreducible]`。当希望阻止
证明中的 `foo` 发生归约时，此命令尤其有用。

就功能而言，`seal foo` 等价于 `attribute [local irreducible] foo`。该属性规定
只在局部作用域内把 `foo` 视为不可约，从而既维持所需的抽象层次，又不影响全局设置。
-/
def commandSeal__ : Unit := ()

/--
`unseal foo` 命令确保定义 `foo` 被解除封闭，即将其标记为 `[semireducible]`，也就是
默认的可约性设置。需要在证明中允许 `foo` 进行一定程度的归约时，可以使用此命令。

就功能而言，`unseal foo` 等价于 `attribute [local semireducible] foo`。应用该属性
只会在局部作用域内把 `foo` 设为半可约。
-/
def commandUnseal__ : Unit := ()

end Parser

namespace Option

/--
允许用户修改声明的可约性设置，即使这类修改被认为可能有危险。例如，`simp` 与类型类
解析会维护项索引，其中会展开可约声明；修改可约性可能使这些索引与缓存失效。

默认值为 `false`。
-/
def allowUnsafeReducibility : Bool := false

end Option

namespace Order

/--
偏序是一个自反、传递且反对称的关系。

此类型类用于构造 `partial_fixpoint`，不应作其他用途。
-/
class PartialOrder (α : Sort u) where
  /--
  “小于等于”关系，亦可理解为“近似”关系。

  此关系用于构造 `partial_fixpoint`，不应作其他用途。
  -/
  rel : α → α → Prop
  /-- “小于等于”关系（或“近似”关系）是自反的。 -/
  rel_refl : ∀ {x : α}, rel x x
  /-- “小于等于”关系（或“近似”关系）是传递的。 -/
  rel_trans : ∀ {x y z : α}, rel x y → rel y z → rel x z
  /-- “小于等于”关系（或“近似”关系）是反对称的。 -/
  rel_antisymm : ∀ {x y : α}, rel x y → rel y x → x = y

/--
链完备偏序（CCPO）是一种偏序，其中每条链都有最小上界。

此类型类用于构造 `partial_fixpoint`，不应作其他用途。
-/
class CCPO (α : Sort u) extends PartialOrder α where
  /-- 每条链的最小上界都存在。 -/
  has_csup : Unit

/--
若函数把相关元素映射为相关元素，则该函数是单调的。

此定义用于构造 `partial_fixpoint`，不应作其他用途。
-/
def monotone : Unit := ()

/--
单调函数的最小不动点，是对该函数进行超限迭代所得链的最小上界。

定义本身并非严格需要 `monotone f` 假设；然而没有该假设时，定义并没有太大意义。
此外，让每次使用 `fix` 时都带上单调性要求，也可简化 `fix_eq` 等定理的应用。

此定义用于构造 `partial_fixpoint`，不应作其他用途。
-/
def fix : Unit := ()

/--
链完备偏序中单调函数的不动点主定理：`fix` 构造出的值确实是不动点。

此定理用于构造 `partial_fixpoint`，不应作其他用途。
-/
def fix_eq : Unit := ()

/--
完备格是一种偏序，其中每个子集都有最小上界。
-/
class CompleteLattice (α : Sort u) extends PartialOrder α where
  /-- 任意子集的最小上界都存在。 -/
  has_sup : Unit

/--
函数 `f` 的最小不动点，即所有前不动点的下确界。
-/
def lfp : Unit := ()

/--
单调函数 `f` 的最小不动点确实是不动点。
-/
def lfp_fix : Unit := ()

/--
单调函数 `f` 的最小不动点所满足的 Park 归纳原理。
此定理显式接受一个 `f` 单调的见证。
-/
def lfp_le_of_le_monotone : Unit := ()

end Order
end ZhDoc.RecursiveDefs
