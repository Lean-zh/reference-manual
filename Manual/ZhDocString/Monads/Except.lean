import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Monads.Except

/--
一种状态与异常的组合单子，其中异常不会自动回滚状态。

`EStateM.Backtrackable` 的实例提供了一种在需要时回滚部分状态的方法。

`EStateM ε σ` 等价于 `ExceptT ε (StateM σ)`，但效率更高。
-/
def eStateM (ε σ α : Type u) : Type u := _root_.EStateM ε σ α

namespace EStateM

/--
状态与异常组合单子返回的值，其中异常不会自动回滚状态。

`Result ε σ α` 等价于 `Except ε α × σ`，但使用单个组合归纳类型可以得到效率更高的数据表示。
-/
inductive Result (ε σ α : Type u) where
  /-- 类型为 `α` 的成功值以及新状态 `σ`。 -/
  | ok : α → σ → Result ε σ α
  /-- 类型为 `ε` 的异常以及新状态 `σ`。 -/
  | error : ε → σ → Result ε σ α

/--
执行初始状态为 `s` 的 `EStateM` 动作。返回值包含最终状态，并表明是抛出了异常还是返回了值。
-/
def run {ε σ α : Type u} (x : _root_.EStateM ε σ α) (s : σ) :
    _root_.EStateM.Result ε σ α := _root_.EStateM.run x s

/--
执行初始状态为 `s` 的 `EStateM`，取得返回值 `α` 并丢弃最终状态。如果抛出了未处理的异常，则返回 `none`。
-/
def run' {ε σ α : Type u} (x : _root_.EStateM ε σ α) (s : σ) : Option α :=
  _root_.EStateM.run' x s

/--
使用函数变换异常，而不改变成功结果。
-/
def adaptExcept {ε σ α ε' : Type u} (f : ε → ε') (x : _root_.EStateM ε σ α) :
    _root_.EStateM ε' σ α := _root_.EStateM.adaptExcept f x

/--
将状态单子动作转换为带异常的状态单子动作。

所得动作不会抛出异常。
-/
def fromStateM {ε σ α : Type} (x : StateM σ α) : _root_.EStateM ε σ α :=
  _root_.EStateM.fromStateM x

/--
`EStateM` 中的异常处理器会保存由 `δ` 确定的部分状态，并在捕获异常时将其恢复。默认情况下，`δ` 是 `Unit`，不会保存任何信息。
-/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  /-- 提取状态中应在处理异常时回滚的信息。 -/
  save : σ → δ
  /--
  使用应回滚的已保存信息来更新当前状态。处理异常时，这个更新后的状态将成为当前状态。
  -/
  restore : σ → δ → σ

/--
一个不从状态中保存任何信息的后备 `Backtrackable` 实例。这样，每种类型都可以用作 `EStateM` 的状态，且不发生回滚。

因为这是最先声明的 `Backtrackable _ σ` 实例，所以只有在没有注册其他 `Backtrackable _ σ` 实例时才会选中它。
-/
@[instance_reducible]
def nonBacktrackable {σ : Type u} : _root_.EStateM.Backtrackable PUnit σ :=
  _root_.EStateM.nonBacktrackable

/--
使用函数变换 `EStateM ε σ` 动作返回的值。
-/
def map {ε σ α β : Type u} (f : α → β) (x : _root_.EStateM ε σ α) :
    _root_.EStateM ε σ β := _root_.EStateM.map f x

/--
返回一个值，而不修改状态或抛出异常。
-/
def pure {ε σ α : Type u} (a : α) : _root_.EStateM ε σ α := _root_.EStateM.pure a

/--
依次执行两个 `EStateM ε σ` 动作，将第一个动作返回的值传给第二个动作。
-/
def bind {ε σ α β : Type u} (x : _root_.EStateM ε σ α)
    (f : α → _root_.EStateM ε σ β) : _root_.EStateM ε σ β := _root_.EStateM.bind x f

/--
不依赖具体异常值的失败处理。

`Backtrackable δ σ` 实例用于在运行 `x₁` 之前保存部分状态的快照。如果捕获到异常，则使用保存的快照更新状态，从而回滚部分状态。如果没有提供 `Backtrackable` 实例，则使用 `δ` 为 `Unit` 的后备实例，不回滚任何信息。
-/
def orElse {ε σ α δ : Type u} [_root_.EStateM.Backtrackable δ σ]
    (x₁ : _root_.EStateM ε σ α) (x₂ : Unit → _root_.EStateM ε σ α) :
    _root_.EStateM ε σ α := _root_.EStateM.orElse x₁ x₂

/--
另一种 `orElse` 运算符，允许调用者在两个操作都失败时选择应使用哪个异常。默认使用第一个异常，因为标准的 `orElse` 使用第二个。
-/
def orElse' {ε σ α δ : Type u} [_root_.EStateM.Backtrackable δ σ]
    (x₁ x₂ : _root_.EStateM ε σ α) (useFirstEx : Bool := true) :
    _root_.EStateM ε σ α := _root_.EStateM.orElse' x₁ x₂ useFirstEx

/--
依次执行两个 `EStateM ε σ` 动作，先运行 `x`，再运行 `y`。忽略第一个动作的返回值。
-/
def seqRight {ε σ α β : Type u} (x : _root_.EStateM ε σ α)
    (y : Unit → _root_.EStateM ε σ β) : _root_.EStateM ε σ β :=
  _root_.EStateM.seqRight x y

/--
处理状态与错误组合单子中抛出的异常。

`Backtrackable δ σ` 实例用于在运行 `x` 之前保存部分状态的快照。如果捕获到异常，则使用保存的快照更新状态，从而回滚部分状态。如果没有提供 `Backtrackable` 实例，则使用 `δ` 为 `Unit` 的后备实例，不回滚任何信息。
-/
def tryCatch {ε σ δ : Type u} [_root_.EStateM.Backtrackable δ σ] {α : Type u}
    (x : _root_.EStateM ε σ α) (handle : ε → _root_.EStateM ε σ α) :
    _root_.EStateM ε σ α := _root_.EStateM.tryCatch x handle

/--
向最近的外围处理器抛出类型为 `ε` 的异常。
-/
def throw {ε σ α : Type u} (e : ε) : _root_.EStateM ε σ α := _root_.EStateM.throw e

/--
取得单子可变状态的当前值。
-/
def get {ε σ : Type u} : _root_.EStateM ε σ σ := _root_.EStateM.get

/--
用新值替换单子的可变状态的当前值。
-/
def set {ε σ : Type u} (s : σ) : _root_.EStateM ε σ PUnit := _root_.EStateM.set s

/--
对当前状态应用一个函数，该函数既计算新状态也计算一个值。新状态替换当前状态，并返回该值。

它等价于 `do let (a, s) := f (← get); set s; pure a`。但是，使用 `modifyGet` 可能具有更高的性能，因为它不会增加对状态值的新引用。额外的引用会妨碍数据的原地更新。
-/
def modifyGet {ε σ α : Type u} (f : σ → α × σ) : _root_.EStateM ε σ α :=
  _root_.EStateM.modifyGet f

end EStateM

/--
`Except ε α` 是这样一种类型：它表示类型为 `ε` 的错误，或者带有类型为 `α` 的值的成功结果。

`Except ε : Type u → Type v` 是一个表示可能抛出异常的计算的 `Monad`：`pure` 操作是 `Except.ok`，而 `bind` 操作返回遇到的第一个 `Except.error`。
-/
inductive Except (ε : Type u) (α : Type v) where
  /-- 类型为 `ε` 的失败值。 -/
  | error : ε → Except ε α
  /-- 类型为 `α` 的成功值。 -/
  | ok : α → Except ε α

namespace Except

/--
`Except ε` 单子中的成功计算：返回 `a`，且不抛出异常。
-/
def pure {ε : Type u} {α : Type v} (a : α) : _root_.Except ε α := _root_.Except.pure a

/--
依次执行两个可能抛出异常的操作，并允许第二个操作依赖第一个操作返回的值。

如果第一个操作抛出异常，那么该异常就是计算结果。如果第一个操作成功、但第二个操作抛出异常，那么后一个异常就是结果。如果两者都成功，那么结果就是第二个计算的结果。

这是 `Except ε` 的 `>>=` 运算符的实现。
-/
def bind {ε : Type u} {α : Type v} {β : Type w} (ma : _root_.Except ε α)
    (f : α → _root_.Except ε β) : _root_.Except ε β := _root_.Except.bind ma f

/--
使用函数变换成功结果，而在抛出异常时不做任何事情。

示例：
 * `(pure 2 : Except String Nat).map toString = pure "2"`
 * `(throw "Error" : Except String Nat).map toString = throw "Error"`
-/
def map {ε : Type u} {α : Type v} {β : Type w} (f : α → β) :
    _root_.Except ε α → _root_.Except ε β := _root_.Except.map f

/--
使用函数变换异常，而不改变成功结果。

示例：
 * `(pure 2 : Except String Nat).mapError (·.length) = pure 2`
 * `(throw "Error" : Except String Nat).mapError (·.length) = throw 5`
-/
def mapError {ε : Type u} {ε' : Type v} {α : Type w} (f : ε → ε') :
    _root_.Except ε α → _root_.Except ε' α := _root_.Except.mapError f

/--
处理 `Except ε` 单子中抛出的异常。

如果 `ma` 成功，则返回它的结果。如果它抛出异常，则以异常值调用 `handle`。

示例：
 * `(pure 2 : Except String Nat).tryCatch (pure ·.length) = pure 2`
 * `(throw "Error" : Except String Nat).tryCatch (pure ·.length) = pure 5`
 * `(throw "Error" : Except String Nat).tryCatch (fun x => throw ("E: " ++ x)) = throw "E: Error"`
-/
def tryCatch {ε : Type u} {α : Type v} (ma : _root_.Except ε α)
    (handle : ε → _root_.Except ε α) : _root_.Except ε α := _root_.Except.tryCatch ma handle

/--
从 `Except ε` 单子中抛出的异常恢复。通常通过 `<|>` 运算符使用。

`Except.tryCatch` 是一个相关运算符，它允许恢复过程依赖于抛出的是_哪个_异常。
-/
def orElseLazy {ε : Type u} {α : Type v} (x : _root_.Except ε α)
    (y : Unit → _root_.Except ε α) : _root_.Except ε α := _root_.Except.orElseLazy x y

/-- 如果值是 `Except.ok`，则返回 `true`；否则返回 `false`。 -/
abbrev isOk {ε : Type u} {α : Type v} : _root_.Except ε α → Bool := _root_.Except.isOk

/--
如果抛出了异常，则返回 `none`；成功时返回用 `some` 包裹的值。

示例：
 * `(pure 10 : Except String Nat).toOption = some 10`
 * `(throw "Failure" : Except String Nat).toOption = none`
-/
def toOption {ε : Type u} {α : Type v} : _root_.Except ε α → Option α :=
  _root_.Except.toOption

/-- 如果值是 `Except.ok`，则返回 `true`；否则返回 `false`。 -/
def toBool {ε : Type u} {α : Type v} : _root_.Except ε α → Bool := _root_.Except.toBool

end Except

/--
异常单子提供抛出错误和处理错误的能力。

在这个类中，`ε` 是 `outParam`，这意味着它从 `m` 推断得出。`MonadExceptOf ε` 提供相同的操作，但允许 `ε` 影响实例合成。

当处理器没有异常类型标注时，`MonadExcept.tryCatch` 用于对 `do` 块中的 `try ... catch ...` 步骤进行脱糖。
-/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  /-- 向最近的外围处理器抛出类型为 `ε` 的异常。 -/
  throw {α : Type v} : ε → m α
  /-- 捕获 `body` 中抛出的错误，并将它们传给 `handler`。不捕获 `handler` 中的错误。 -/
  tryCatch {α : Type v} : (body : m α) → (handler : ε → m α) → m α

namespace MonadExcept

/--
将 `Except ε` 动作重新解释为异常单子 `m` 中的动作：前者成功时后者成功，前者抛出异常时后者也抛出异常。
-/
def ofExcept {m : Type u → Type v} {ε : Type w} {α : Type u} [Monad m]
    [_root_.MonadExcept ε m] : _root_.Except ε α → m α := _root_.MonadExcept.ofExcept

/--
忽略抛出了哪个异常的无条件错误恢复。通常通过 `<|>` 运算符使用。

如果两个计算都抛出异常，那么结果是第二个异常。
-/
def orElse {ε : Type u} {m : Type v → Type w} [_root_.MonadExcept ε m] {α : Type v}
    (t₁ : m α) (t₂ : Unit → m α) : m α := _root_.MonadExcept.orElse t₁ t₂

/--
另一种无条件错误恢复运算符，允许调用者指定当两个操作都抛出异常时应抛出哪个异常。

默认抛出第一个异常，因为 `<|>` 运算符会抛出第二个。
-/
def orelse' {ε : Type u} {m : Type v → Type w} [_root_.MonadExcept ε m] {α : Type v}
    (t₁ t₂ : m α) (useFirstEx : Bool := true) : m α :=
  _root_.MonadExcept.orelse' t₁ t₂ useFirstEx

end MonadExcept

/--
异常单子提供抛出错误和处理错误的能力。

在这个类中，`ε` 是 `semiOutParam`，这意味着它可以影响实例的选择。`MonadExcept ε` 提供相同的操作，但要求能够从 `m` 推断出 `ε`。

当处理器带有类型标注时，显式接受异常类型的 `tryCatchThe` 用于对 `do` 块中的 `try ... catch ...` 步骤进行脱糖。
-/
class MonadExceptOf (ε : semiOutParam (Type u)) (m : Type v → Type w) where
  /-- 向最近的外围 `catch` 抛出类型为 `ε` 的异常。 -/
  throw {α : Type v} : ε → m α
  /-- 捕获 `body` 中抛出的错误，并将它们传给 `handler`。不捕获 `handler` 中的错误。 -/
  tryCatch {α : Type v} (body : m α) (handler : ε → m α) : m α

/--
抛出异常，并显式指定异常类型。当一个单子支持抛出多种类型的异常时，这很有用。

如需让程序从 `m` 推断异常类型的版本，请使用 `throw`。
-/
abbrev throwThe (ε : Type u) {m : Type v → Type w} [_root_.MonadExceptOf ε m]
    {α : Type v} (e : ε) : m α := _root_.throwThe ε e

/--
捕获错误，并使用 `handle` 恢复。异常类型是显式指定的。当一个单子支持抛出或处理多种类型的异常时，这很有用。

如需让程序从 `m` 推断异常类型的版本，请使用 `tryCatch`。
-/
abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [_root_.MonadExceptOf ε m]
    {α : Type v} (x : m α) (handle : ε → m α) : m α := _root_.tryCatchThe ε x handle

/--
提供一种能力，确保无论发生异常还是其他失败，某个动作都会执行的单子。

`MonadFinally.tryFinally'` 用于对 `try ... finally ...` 语法进行脱糖。
-/
class MonadFinally (m : Type u → Type v) where
  /--
  运行一个动作，并确保之后总会运行另一个动作。

  更具体地说，`tryFinally' x f` 运行 `x`，然后运行最终处理计算 `f`。如果 `x` 成功并得到某个值 `a : α`，则返回 `f (some a)`。如果 `x` 按 `m` 对失败的定义而失败，则返回 `f none`。

  可以认为 `tryFinally'` 的作用与命令式编程语言中的 `finally` 块相同。
  -/
  tryFinally' {α β : Type u} : (x : m α) → (f : Option α → m β) → m (α × β)

/--
向单子 `m` 添加类型为 `ε` 的异常。
-/
def exceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  _root_.ExceptT ε m α

namespace ExceptT

/--
在带异常的变换后单子中运行底层单子的计算。
-/
def lift {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (t : m α) :
    _root_.ExceptT ε m α := _root_.ExceptT.lift t

/--
把可能抛出异常的单子动作作为可能返回异常值的动作使用。

这是 `ExceptT.mk` 的逆操作。
-/
def run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : _root_.ExceptT ε m α) :
    m (_root_.Except ε α) := _root_.ExceptT.run x

/--
返回值 `a`，既不抛出异常，也不产生任何其他效果。
-/
def pure {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) :
    _root_.ExceptT ε m α := _root_.ExceptT.pure a

/--
依次执行两个可能抛出异常的动作。通常通过 `do` 记法或 `>>=` 运算符使用。
-/
def bind {ε : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}
    (ma : _root_.ExceptT ε m α) (f : α → _root_.ExceptT ε m β) :
    _root_.ExceptT ε m β := _root_.ExceptT.bind ma f

/--
处理一个除抛出异常外不可能有_其他_效果的动作所抛出的异常。
-/
def bindCont {ε : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}
    (f : α → _root_.ExceptT ε m β) : _root_.Except ε α → m (_root_.Except ε β) :=
  _root_.ExceptT.bindCont f

/--
处理 `ExceptT ε` 变换器中产生的异常。
-/
def tryCatch {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u}
    (ma : _root_.ExceptT ε m α) (handle : ε → _root_.ExceptT ε m α) :
    _root_.ExceptT ε m α := _root_.ExceptT.tryCatch ma handle

/--
把可能返回异常值的单子动作作为变换后单子中可能抛出相应异常的动作使用。

这是 `ExceptT.run` 的逆操作。
-/
def mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (_root_.Except ε α)) :
    _root_.ExceptT ε m α := _root_.ExceptT.mk x

/--
使用 `f` 变换成功计算的值。通常通过 `<$>` 运算符使用。
-/
def map {ε : Type u} {m : Type u → Type v} [Monad m] {α β : Type u} (f : α → β)
    (x : _root_.ExceptT ε m α) : _root_.ExceptT ε m β := _root_.ExceptT.map f x

/--
使用函数 `f` 变换异常。

这是 `Except.mapError` 的 `ExceptT` 版本。
-/
def adapt {ε : Type u} {m : Type u → Type v} [Monad m] {ε' α : Type u} (f : ε → ε') :
    _root_.ExceptT ε m α → _root_.ExceptT ε' m α := _root_.ExceptT.adapt f

end ExceptT

/--
向单子 `m` 添加类型为 `ε` 的异常。

此实现不使用 `Except ε` 来模拟异常，而是使用延续传递风格。它具有与 `ExceptT ε` 不同的性能特征。
-/
def exceptCpsT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type (max (u + 1) v) :=
  _root_.ExceptCpsT ε m α

namespace ExceptCpsT

/--
返回计算的值，不再区分它是异常还是成功结果。

这对应于提前返回。
-/
def runCatch {m : Type u → Type v} {α : Type u} [Monad m]
    (x : _root_.ExceptCpsT α m α) : m α := _root_.ExceptCpsT.runCatch x

/--
通过提供显式的成功延续和失败延续来使用可能抛出异常的单子动作。
-/
def runK {m : Type u → Type v} {β ε α : Type u} (x : _root_.ExceptCpsT ε m α)
    (ok : α → m β) (error : ε → m β) : m β := _root_.ExceptCpsT.runK x ok error

/--
把可能抛出异常的单子动作作为可能返回异常值的动作使用。
-/
def run {m : Type u → Type v} {ε α : Type u} [Monad m]
    (x : _root_.ExceptCpsT ε m α) : m (_root_.Except ε α) := _root_.ExceptCpsT.run x

/--
把底层单子中的动作提升到变换后的异常单子中运行。
-/
def lift {m : Type u → Type v} {α ε : Type u} [Monad m] (x : m α) :
    _root_.ExceptCpsT ε m α := _root_.ExceptCpsT.lift x

end ExceptCpsT

end Manual.ZhDocString.Monads.Except
