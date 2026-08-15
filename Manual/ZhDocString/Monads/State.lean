/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Monads.State

universe u v w

/--
类型上的恒等函数，主要用于其 `Monad` 实例。

恒等单子可与单子变换器配合使用，以构造用于特定目的的单子。此外，也可以在本来不使用
单子的代码中通过 `do` 记法使用局部可变性、`for` 循环和提前返回等控制结构。

示例：
```lean example
def containsFive (xs : List Nat) : Bool := Id.run do
  for x in xs do
    if x == 5 then return true
  return false
```

```lean example
#eval containsFive [1, 3, 5, 7]
```
```output
true
```
-/
@[implicit_reducible] def Id (type : Type u) : Type u := type

namespace Id

/--
运行恒等单子中的计算。

此函数就是恒等函数。由于它的参数类型为 `Id α`，其参数中的 `do` 记法会使用
`Monad Id` 实例。
-/
def run (x : _root_.Id α) : α := _root_.Id.run x

end Id

/--
为单子增加失败能力。与普通异常不同，它无法说明失败发生的原因。
-/
@[implicit_reducible] def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  _root_.OptionT m α

namespace OptionT

/--
在底层单子 `m` 中执行一个可能失败的动作；失败时返回 `none`。
-/
def run {m : Type u → Type v} {α : Type u} (x : _root_.OptionT m α) : m (Option α) :=
  _root_.OptionT.run x

/--
把返回 `Option` 的动作转换为可能失败的动作，其中 `none` 表示失败。
-/
def mk {m : Type u → Type v} {α : Type u} (x : m (Option α)) : _root_.OptionT m α :=
  _root_.OptionT.mk x

/--
以给定值成功。
-/
def pure {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : _root_.OptionT m α :=
  _root_.OptionT.pure a

/--
依次执行两个可能失败的动作。仅当第一个动作成功时才运行第二个动作。
-/
def bind {m : Type u → Type v} [Monad m] {α β : Type u}
    (x : _root_.OptionT m α) (f : α → _root_.OptionT m β) : _root_.OptionT m β :=
  _root_.OptionT.bind x f

/--
可恢复的失败。
-/
def fail {m : Type u → Type v} [Monad m] {α : Type u} : _root_.OptionT m α :=
  _root_.OptionT.fail

/--
从失败中恢复。通常通过 `<|>` 运算符使用。
-/
def orElse {m : Type u → Type v} [Monad m] {α : Type u}
    (x : _root_.OptionT m α) (y : Unit → _root_.OptionT m α) : _root_.OptionT m α :=
  _root_.OptionT.orElse x y

/--
把底层单子中的计算转换为可能失败的计算，尽管该计算本身并不会失败。

此函数通常通过 `MonadLiftT` 实例隐式使用，作为[自动提升](lean-manual://section/monad-lifting)的一部分。
-/
def lift {m : Type u → Type v} [Monad m] {α : Type u} (x : m α) : _root_.OptionT m α :=
  _root_.OptionT.lift x

/--
把失败视作 `Unit` 类型的异常来处理。
-/
def tryCatch {m : Type u → Type v} [Monad m] {α : Type u}
    (x : _root_.OptionT m α) (handle : PUnit → _root_.OptionT m α) : _root_.OptionT m α :=
  _root_.OptionT.tryCatch x handle

end OptionT

/--
为单子增加访问 `ρ` 类型只读值的能力。该值可以由 `withReader` 局部覆盖，但不能修改。

所得单子中的动作是以局部值为参数、返回 `m` 中普通动作的函数。
-/
@[implicit_reducible] def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) := _root_.ReaderT ρ m α

/--
具有 `ρ` 类型只读值访问能力的单子。该值可以由 `withReader` 局部覆盖，但不能修改。
-/
abbrev ReaderM (ρ : Type u) := _root_.ReaderM ρ

namespace ReaderT

/--
在底层单子 `m` 中执行一个来自带只读值单子的动作。
-/
def run {ρ : Type u} {m : Type u → Type v} {α : Type u}
    (x : _root_.ReaderT ρ m α) (r : ρ) : m α := _root_.ReaderT.run x r

/--
获取读取器单子的局部值。通常通过 `read` 使用；当有多个局部值可用时，则通过 `readThe` 使用。
-/
def read {ρ : Type u} {m : Type u → Type v} [Monad m] : _root_.ReaderT ρ m ρ :=
  _root_.ReaderT.read

/--
使用 `f` 修改读取器单子的局部值。所得计算把 `f` 应用于传入的局部值，再将结果传给内部计算。
-/
def adapt {ρ ρ' α : Type u} {m : Type u → Type v} (f : ρ' → ρ) :
    _root_.ReaderT ρ m α → _root_.ReaderT ρ' m α := _root_.ReaderT.adapt f

/--
返回给定值 `a`，忽略读取器单子的局部值。通常通过 `Pure.pure` 使用。
-/
def pure {ρ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) :
    _root_.ReaderT ρ m α := _root_.ReaderT.pure a

/--
依次执行两个读取器单子计算。二者都会获得局部值，而第二个计算还会获得第一个计算的值。
通常通过 `>>=` 运算符使用。
-/
def bind {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}
    (x : _root_.ReaderT ρ m α) (f : α → _root_.ReaderT ρ m β) : _root_.ReaderT ρ m β :=
  _root_.ReaderT.bind x f

/--
从错误中恢复。两个分支都会获得同一个局部值。通常通过 `<|>` 运算符使用。
-/
def orElse {ρ : Type u} {m : Type u → Type v} {α : Type u} [Alternative m]
    (x₁ : _root_.ReaderT ρ m α) (x₂ : Unit → _root_.ReaderT ρ m α) :
    _root_.ReaderT ρ m α := _root_.ReaderT.orElse x₁ x₂

/--
以可恢复的错误失败。
-/
def failure {ρ : Type u} {m : Type u → Type v} {α : Type u} [Alternative m] :
    _root_.ReaderT ρ m α := _root_.ReaderT.failure

end ReaderT

/--
读取器单子能够在计算中隐式传递一个值。该值可以读取，但不能写入。
`MonadWithReader ρ` 实例还允许为子计算局部覆盖此值。

在此类中，`ρ` 是 `semiOutParam`，这意味着它可以影响实例的选择。
`MonadReader ρ` 提供相同的操作，但要求能从 `m` 推断出 `ρ`。
-/
class MonadReaderOf (ρ : semiOutParam (Type u)) (m : Type u → Type v) where
  /-- 获取局部值。 -/
  read : m ρ

/--
读取器单子能够在计算中隐式传递一个值。该值可以读取，但不能写入。
`MonadWithReader ρ` 实例还允许为子计算局部覆盖此值。

在此类中，`ρ` 是 `outParam`，这意味着它由 `m` 推断。
`MonadReaderOf ρ` 提供相同的操作，但允许 `ρ` 影响实例合成。
-/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  /--
  获取局部值。

  当有多个值可用时，使用 `readThe` 显式指定类型。
  -/
  read : m ρ

/--
获取类型为 `ρ` 的局部值。当单子支持读取多种类型的值时，此函数很有用。

若希望由 `m` 推断类型 `ρ`，请使用 `read`。
-/
def readThe (ρ : Type u) {m : Type u → Type v} [_root_.MonadReaderOf ρ m] : m ρ :=
  _root_.readThe ρ

/--
还允许局部覆盖值的读取器单子。

在此类中，`ρ` 是 `semiOutParam`，这意味着它可以影响实例的选择。
`MonadWithReader ρ` 提供相同的操作，但要求能从 `m` 推断出 `ρ`。
-/
class MonadWithReaderOf (ρ : semiOutParam (Type u)) (m : Type u → Type v) where
  /--
  在运行动作时局部修改读取器单子的值。

  在内部动作 `x` 执行期间，读取该值会返回把 `f` 应用于原值所得的结果。从 `x` 返回控制后，
  读取器单子的值会恢复。
  -/
  withReader {α : Type u} (f : ρ → ρ) (x : m α) : m α

/--
还允许局部覆盖值的读取器单子。

在此类中，`ρ` 是 `outParam`，这意味着它由 `m` 推断。
`MonadWithReaderOf ρ` 提供相同的操作，但允许 `ρ` 影响实例合成。
-/
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  /--
  在运行动作时局部修改读取器单子的值。

  在内部动作 `x` 执行期间，读取该值会返回把 `f` 应用于原值所得的结果。从 `x` 返回控制后，
  读取器单子的值会恢复。
  -/
  withReader {α : Type u} : (f : ρ → ρ) → (x : m α) → m α

/--
在运行动作时局部修改读取器单子的值，并显式指定该局部值的类型。当单子支持读取多种类型的值时，
此函数很有用。

在内部动作 `x` 执行期间，读取该值会返回把 `f` 应用于原值所得的结果。从 `x` 返回控制后，
读取器单子的值会恢复。

若希望由 `m` 推断局部值的类型，请使用 `withReader`。
-/
def withTheReader (ρ : Type u) {m : Type u → Type v} [_root_.MonadWithReaderOf ρ m]
    {α : Type u} (f : ρ → ρ) (x : m α) : m α := _root_.withTheReader ρ f x

/--
状态单子提供一个给定类型的值（即_状态_），该值可以获取或替换。实例可以通过传递状态值、
使用可变引用单元（例如 `ST.Ref σ`）或其他方式实现这些操作。

在此类中，`σ` 是 `outParam`，这意味着它由 `m` 推断。`MonadStateOf σ` 提供相同的操作，
但允许 `σ` 影响实例合成。

状态单子的可变状态在多个 `do` 块或函数之间可见，这不同于 `do` 记法中的
[局部可变状态](lean-manual://section/do-notation-let-mut)。
-/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) where
  /-- 获取单子当前的可变状态值。 -/
  get : m σ
  /-- 用新值替换当前的可变状态值。 -/
  set : σ → m PUnit
  /--
  把一个函数应用于当前状态，该函数同时计算新状态和一个值。新状态替换当前状态，并返回该值。

  它等价于 `do let (a, s) := f (← get); set s; pure a`。不过，使用 `modifyGet` 可能有更高性能，
  因为它不会增加状态值的新引用；额外引用可能妨碍对数据进行原地更新。
  -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

/--
获取单子当前的可变状态值。
-/
def get {σ : Type u} {m : Type u → Type v} [_root_.MonadState σ m] : m σ :=
  _root_.MonadState.get

/--
修改当前状态，用把 `f` 应用于该状态所得的结果替换其值。

若要显式选择要修改的状态类型，请使用 `modifyThe`。

它等价于 `do set (f (← get))`。不过，使用 `modify` 可能有更高性能，因为它不会增加状态值的
新引用；额外引用可能妨碍对数据进行原地更新。
-/
def modify {σ : Type u} {m : Type u → Type v} [_root_.MonadState σ m]
    (f : σ → σ) : m PUnit := _root_.modify f

/--
把一个函数应用于当前状态，该函数同时计算新状态和一个值。新状态替换当前状态，并返回该值。

它等价于 `do let (a, s) := f (← get); set s; pure a`。不过，使用 `modifyGet` 可能有更高性能，
因为它不会增加状态值的新引用；额外引用可能妨碍对数据进行原地更新。
-/
def modifyGet {σ α : Type u} {m : Type u → Type v} [_root_.MonadState σ m]
    (f : σ → Prod α σ) : m α := _root_.MonadState.modifyGet f

/--
用把 `f` 应用于状态所得的结果替换状态，并返回状态的旧值。

它等价于 `get <* modify f`，但可能更加高效。
-/
def getModify {σ : Type u} {m : Type u → Type v} [_root_.MonadState σ m]
    (f : σ → σ) : m σ := _root_.getModify f

/--
状态单子提供一个给定类型的值（即_状态_），该值可以获取或替换。实例可以通过传递状态值、
使用可变引用单元（例如 `ST.Ref σ`）或其他方式实现这些操作。

在此类中，`σ` 是 `semiOutParam`，这意味着它可以影响实例的选择。`MonadState σ` 提供相同的
操作，但要求能从 `m` 推断出 `σ`。

状态单子的可变状态在多个 `do` 块或函数之间可见，这不同于 `do` 记法中的
[局部可变状态](lean-manual://section/do-notation-let-mut)。
-/
class MonadStateOf (σ : semiOutParam (Type u)) (m : Type u → Type v) where
  /-- 获取单子当前的可变状态值。 -/
  get : m σ
  /-- 用新值替换当前的可变状态值。 -/
  set : σ → m PUnit
  /--
  把一个函数应用于当前状态，该函数同时计算新状态和一个值。新状态替换当前状态，并返回该值。

  它等价于 `do let (a, s) := f (← get); set s; pure a`。不过，使用 `modifyGet` 可能有更高性能，
  因为它不会增加状态值的新引用；额外引用可能妨碍对数据进行原地更新。
  -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

/--
获取显式给定类型 `σ` 的当前状态。当当前单子提供多种状态类型时，此函数从中选择一种。
-/
def getThe (σ : Type u) {m : Type u → Type v} [_root_.MonadStateOf σ m] : m σ :=
  _root_.getThe σ

/--
修改显式给定类型 `σ` 的当前状态，用把 `f` 应用于该状态所得的结果替换其值。当当前单子提供
多种状态类型时，此函数从中选择一种。

它等价于 `do set (f (← get))`。不过，使用 `modify` 可能有更高性能，因为它不会增加状态值的
新引用；额外引用可能妨碍对数据进行原地更新。
-/
def modifyThe (σ : Type u) {m : Type u → Type v} [_root_.MonadStateOf σ m]
    (f : σ → σ) : m PUnit := _root_.modifyThe σ f

/--
把一个函数应用于显式给定类型 `σ` 的当前状态。该函数同时计算新状态和一个值；新状态替换当前
状态，并返回该值。

它等价于 `do let (a, s) := f (← getThe σ); set s; pure a`。不过，使用 `modifyGetThe` 可能有
更高性能，因为它不会增加状态值的新引用；额外引用可能妨碍对数据进行原地更新。
-/
def modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v}
    [_root_.MonadStateOf σ m] (f : σ → Prod α σ) : m α := _root_.modifyGetThe σ f

/--
基于二元组的状态单子。

`StateM σ` 中的动作是接受初始状态、返回一个值与最终状态之二元组的函数。
-/
@[reducible] def StateM (σ α : Type u) : Type u := _root_.StateM σ α

/--
为单子增加 `σ` 类型的可变状态。

所得单子中的动作是接受初始状态、并在 `m` 中返回一个值与状态之二元组的函数。
-/
@[implicit_reducible] def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) := _root_.StateT σ m α

namespace StateT

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值与最终状态
组成的二元组。
-/
def run {σ : Type u} {m : Type u → Type v} {α : Type u}
    (x : _root_.StateT σ m α) (s : σ) : m (α × σ) := _root_.StateT.run x s

/--
获取单子当前的可变状态值。

这会增加状态的引用计数，因而可能妨碍原地更新。
-/
def get {σ : Type u} {m : Type u → Type v} [Monad m] : _root_.StateT σ m σ :=
  _root_.StateT.get

/--
用新值替换可变状态。
-/
def set {σ : Type u} {m : Type u → Type v} [Monad m] (s : σ) :
    _root_.StateT σ m PUnit := _root_.StateT.set s

/--
从错误中恢复。错误恢复时会回滚状态。通常通过 `<|>` 运算符使用。
-/
def orElse {σ : Type u} {m : Type u → Type v} [Monad m] [Alternative m] {α : Type u}
    (x₁ : _root_.StateT σ m α) (x₂ : Unit → _root_.StateT σ m α) :
    _root_.StateT σ m α := _root_.StateT.orElse x₁ x₂

/--
以可恢复的错误失败。错误恢复时会回滚状态。
-/
def failure {σ : Type u} {m : Type u → Type v} [Monad m] [Alternative m] {α : Type u} :
    _root_.StateT σ m α := _root_.StateT.failure

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值，并丢弃
最终状态。
-/
def run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u}
    (x : _root_.StateT σ m α) (s : σ) : m α := _root_.StateT.run' x s

/--
依次执行两个动作。通常通过 `>>=` 运算符使用。
-/
def bind {σ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}
    (x : _root_.StateT σ m α) (f : α → _root_.StateT σ m β) : _root_.StateT σ m β :=
  _root_.StateT.bind x f

/--
把一个函数应用于当前状态，该函数同时计算新状态和一个值。新状态替换当前状态，并返回该值。

它等价于 `do let (a, s) := f (← StateT.get); StateT.set s; pure a`。不过，使用
`StateT.modifyGet` 可能有更高性能，因为它不会增加状态值的新引用；额外引用可能妨碍对数据
进行原地更新。
-/
def modifyGet {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u}
    (f : σ → α × σ) : _root_.StateT σ m α := _root_.StateT.modifyGet f

/--
在带状态的单子中运行底层单子的动作。状态不会被修改。

此函数通常通过 `MonadLiftT` 实例隐式使用，作为[自动提升](lean-manual://section/monad-lifting)的一部分。
-/
def lift {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (t : m α) :
    _root_.StateT σ m α := _root_.StateT.lift t

/--
修改计算所返回的值。通常通过 `<$>` 运算符使用。
-/
def map {σ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}
    (f : α → β) (x : _root_.StateT σ m α) : _root_.StateT σ m β :=
  _root_.StateT.map f x

/--
返回给定值而不修改状态。通常通过 `Pure.pure` 使用。
-/
def pure {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) :
    _root_.StateT σ m α := _root_.StateT.pure a

end StateT

/--
状态单子变换器的另一种实现；其内部使用延续传递风格而非二元组。
-/
@[implicit_reducible] def StateCpsT (σ : Type u) (m : Type u → Type v) (α : Type u) :=
  _root_.StateCpsT σ m α

namespace StateCpsT

/--
通过提供初始状态和延续，运行以延续传递风格表示的有状态计算。
-/
def runK {α σ : Type u} {m : Type u → Type v} (x : _root_.StateCpsT σ m α)
    (s : σ) (k : α → σ → m β) : m β := _root_.StateCpsT.runK x s k

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值与最终状态
组成的二元组。

虽然状态在内部以延续传递风格表示，所得值与非 CPS 状态单子的结果相同。
-/
def run {α σ : Type u} {m : Type u → Type v} [Monad m]
    (x : _root_.StateCpsT σ m α) (s : σ) : m (α × σ) := _root_.StateCpsT.run x s

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值，并丢弃
最终状态。
-/
def run' {α σ : Type u} {m : Type u → Type v} [Monad m]
    (x : _root_.StateCpsT σ m α) (s : σ) : m α := _root_.StateCpsT.run' x s

/--
在带状态的单子中运行底层单子的动作。状态不会被修改。

此函数通常通过 `MonadLiftT` 实例隐式使用，作为[自动提升](lean-manual://section/monad-lifting)的一部分。
-/
def lift {α σ : Type u} {m : Type u → Type v} [Monad m] (x : m α) :
    _root_.StateCpsT σ m α := _root_.StateCpsT.lift x

end StateCpsT

/--
用于推断 `EST` 和 `ST` 单子的“状态”的辅助类。
-/
class STWorld (σ : outParam Type) (m : Type → Type)

/--
使用实际可变引用单元（即 `ST.Ref ω σ`）的状态单子。

宏 `StateRefT σ m α` 会从 `m` 推断 `ω`，通常应改用该宏。
-/
@[instance_reducible] def StateRefT' (ω : Type) (σ : Type) (m : Type → Type) (α : Type) : Type :=
  _root_.StateRefT' ω σ m α

namespace StateRefT'

/--
获取单子当前的可变状态值。

这会增加状态的引用计数，因而可能妨碍原地更新。
-/
def get {ω σ : Type} {m : Type → Type} [lift : _root_.MonadLiftT (_root_.ST ω) m] :
    _root_.StateRefT' ω σ m σ := fun ref => lift.monadLift ref.get

/--
用新值替换可变状态。
-/
def set {ω σ : Type} {m : Type → Type} [_root_.MonadLiftT (_root_.ST ω) m]
    (s : σ) : _root_.StateRefT' ω σ m PUnit := _root_.StateRefT'.set s

/--
把一个函数应用于当前状态，该函数同时计算新状态和一个值。新状态替换当前状态，并返回该值。

它等价于先执行 `get` 再执行 `set`。不过，使用 `modifyGet` 可能有更高性能，因为它不会增加
状态值的新引用；额外引用可能妨碍对数据进行原地更新。
-/
def modifyGet {ω σ : Type} {m : Type → Type} {α : Type}
    [lift : _root_.MonadLiftT (_root_.ST ω) m] (f : σ → α × σ) :
    _root_.StateRefT' ω σ m α := fun ref => lift.monadLift (ref.modifyGet f)

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值与最终状态
组成的二元组。

单子 `m` 必须支持 `ST` 效应，才能创建和修改引用单元。
-/
def run {ω σ : Type} {m : Type → Type} [monad : Monad m]
    [lift : _root_.MonadLiftT (_root_.ST ω) m] {α : Type}
    (x : _root_.StateRefT' ω σ m α) (s : σ) : m (α × σ) := do
  let ref ← lift.monadLift (_root_.ST.mkRef s)
  let a ← x ref
  let s ← lift.monadLift ref.get
  monad.pure (a, s)

/--
在底层单子 `m` 中执行一个来自增加了状态的单子的动作。给定初始状态，它返回一个值，并丢弃
最终状态。

单子 `m` 必须支持 `ST` 效应，才能创建和修改引用单元。
-/
def run' {ω σ : Type} {m : Type → Type} [monad : Monad m]
    [lift : _root_.MonadLiftT (_root_.ST ω) m] {α : Type}
    (x : _root_.StateRefT' ω σ m α) (s : σ) : m α := do
  let (a, _) ← run x s
  monad.pure a

/--
在带状态的单子中运行底层单子的动作。状态不会被修改。

此函数通常通过 `MonadLiftT` 实例隐式使用，作为[自动提升](lean-manual://section/monad-lifting)的一部分。
-/
def lift {ω σ : Type} {m : Type → Type} {α : Type} (x : m α) :
    _root_.StateRefT' ω σ m α := _root_.StateRefT'.lift x

end StateRefT'
end ZhDoc.Monads.State
