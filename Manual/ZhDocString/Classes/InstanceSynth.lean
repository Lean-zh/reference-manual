import Lean

namespace ZhDoc.Classes.InstanceSynth

set_option checkBinderAnnotations false

/--
`inferInstance` 通过类型类推断（实例合成）合成任意目标类型的值。此函数与恒等函数具有相同的类型签名，
但参数 `[i : α]` 上的方括号表示 Lean 将尝试通过类型类推断构造该参数。
（如果 `α` 不是一个类型类，此过程将失败。）例如：
```
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

example : foo.default = (default, default) :=
  rfl
```
-/
def inferInstance {α : Sort u} [i : α] : α := i

/--
`inferInstanceAs α` 合成一个类型为 `α` 的实例，然后调整它以符合预期类型 `β`；
`β` 必须能够从上下文中推断出来。

例如：
```
def D := Nat
instance : Inhabited D := inferInstanceAs (Inhabited Nat)
```

这种调整会确保所得实例在低于 `semireducible` 的透明度下归约时，不会“泄漏”右侧的
`Nat`；在这些透明度下，`D` 本来也不会被展开。这样可以防止“滥用定义相等”。

更具体地说，给定“源类型”（参数）和“目标类型”（预期类型），`inferInstanceAs`
先为源类型合成实例，再按需展开并重新包装实例的组成部分（字段、嵌套实例），使其与
目标类型兼容。各个步骤由下列选项控制；它们默认都启用，并且可以在移植代码时禁用：

* `backward.inferInstanceAs.wrap`：实例调整的总开关，同时作用于 `inferInstanceAs`
  和默认派生处理器（`deriving`）；
* `backward.inferInstanceAs.wrap.reuseSubInstances`：对子实例字段复用目标类型已有的实例，
  以避免菱形中的实例不是定义相等的；
* `backward.inferInstanceAs.wrap.instances`：将不可约实例包装在辅助定义中；
* `backward.inferInstanceAs.wrap.data`：将数据字段包装在辅助定义中（证明字段总会被包装）。

如果只需合成实例而不必在类型之间进行迁移，请改用 `inferInstance`；必要时可为预期类型
添加类型标注。
-/
def «inferInstanceAs» (α : Sort u) [i : α] : α := i

/--
用于在类型类中标记输出参数的辅助构造。

例如，`Membership` 类定义为：
```
class Membership (α : outParam (Type u)) (γ : Type v)
```
这表示每当出现形如 `Membership ?α ?γ` 的类型类目标时，Lean 会等到 `?γ` 已知后再求解；
随后运行实例合成，并接受为 `?α` 取任意值时找到的第一个解，由此确定 `?α` 应取的值。

这表达了如下事实：在 `a ∈ s` 这样的项中，`s` 可能是 `Set α`、`List α`，或其他带有
成员关系操作的类型；无论哪种情况，都可以通过查看容器类型来确定“成员”类型 `α`。
-/
def outParam (α : Sort u) : Sort u := α

/--
用于在类型类中标记半输出参数的辅助构造。

半输出参数会影响类型类实例各参数的处理顺序。Lean 会确定一个顺序：只有当实例参数的
所有非（半）输出参数都已确定后，才尝试合成该参数（也就是说，这些参数不能含有在
类型类合成期间创建的、可赋值的元变量）。这会排除 `[Mul β] : Add α` 之类的实例，
因为 `β` 可以是任意类型。把参数标记为半输出参数，就是承诺该类型类的实例总会为它
填入一个值。

例如，`Coe` 类定义为：
```
class Coe (α : semiOutParam (Sort u)) (β : Sort v)
```
这表示所有 `Coe` 实例都应当为 `α` 提供一个具体值（即不是可赋值的元变量）。
`Coe Nat Int` 或 `Coe α (Option α)` 这样的实例是合适的，但 `Coe α Nat` 不合适，
因为它没有为 `α` 提供值。
-/
def semiOutParam (α : Sort u) : Sort u := α

namespace Option

/-- 在类型类实例合成期间，使用依赖“实例在道德上是规范的”这一假设的优化。 -/
def backward.synthInstance.canonInstances : Bool := true

/--
每个类型类实例合成问题可使用的最大心跳数。一次心跳计数表示一千次（小型）内存分配；
设为 `0` 表示不设上限。
-/
def synthInstance.maxHeartbeats : Nat := 20000

/-- 类型类实例合成过程中，用于构造一个解的实例数量上限。 -/
def synthInstance.maxSize : Nat := 128

/-- 在 `inferInstanceAs` 和默认派生处理器（`deriving`）中包装实例体。 -/
def backward.inferInstanceAs.wrap : Bool := true

/--
递归处理子实例时，复用目标类型已有的实例，而不是重新包装它们；这对于避免实例菱形中
出现并非定义相等的实例可能十分重要。
-/
def backward.inferInstanceAs.wrap.reuseSubInstances : Bool := true

/-- 将不可约实例包装在辅助定义中，以修正它们的类型。 -/
def backward.inferInstanceAs.wrap.instances : Bool := true

/-- 将数据字段包装在辅助定义中，以修正它们的类型。 -/
def backward.inferInstanceAs.wrap.data : Bool := true

end Option
end ZhDoc.Classes.InstanceSynth
