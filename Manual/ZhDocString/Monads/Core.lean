/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Monads.Core

universe u v w u₁ u₂ w₁ w₂

/--
函数式编程意义下的函子：函数 `f : Type u → Type v` 能将一个函数映射到其内容之上。
这个 `map` 运算符写作 `<$>`，并通过 `Functor` 实例重载。

此 `map` 函数应当保持恒等函数和函数复合。换言之，对于所有项 `v : f α`，应有：

 * `id <$> v = v`

 * 对所有函数 `h : β → γ` 和 `g : α → β`，`(h ∘ g) <$> v = h <$> g <$> v`

所有 `Functor` 实例都应满足这些要求，但不要求它们_证明_这一点。可以通过 `LawfulFunctor`
类型类要求或提供这些证明。

假定实例合法，这一定义对应于范畴论中的[函子](https://en.wikipedia.org/wiki/Functor)概念，
其中所考虑的特殊范畴以类型为对象、以类型间的函数为态射。
-/
class Functor (f : Type u → Type v) : Type (max (u + 1) v) where
  /--
  在函子内部应用函数。此方法用于重载 `<$>` 运算符。

  映射常值函数时，应改用 `Functor.mapConst`，因为它可能效率更高。

  标识符中记法的约定：

   * `<$>` 在标识符中的推荐拼写是 `map`。
  -/
  map : {α β : Type u} → (α → β) → f α → f β
  /--
  映射常值函数。

  给定 `a : α` 和 `v : f β`，`mapConst a v` 等价于 `(fun _ => a) <$> v`。对某些函子，
  可以更高效地实现它；其他所有函子都可使用默认实现。
  -/
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)

/--
`pure` 函数通过 `Pure` 实例重载。

`Pure` 通常经由 `Monad` 或 `Applicative` 实例使用。
-/
class Pure (f : Type u → Type v) where
  /--
  给定 `a : α`，`pure a : f α` 表示一个什么也不做并返回 `a` 的动作。

  示例：
  * `(pure "hello" : Option String) = some "hello"`
  * `(pure "hello" : Except (Array String) String) = Except.ok "hello"`
  * `(pure "hello" : StateM Nat String).run 105 = ("hello", 105)`
  -/
  pure {α : Type u} : α → f α

/--
`<*>` 运算符使用函数 `Seq.seq` 重载。

`Functor` 类型类中的 `<$>` 可将普通函数映射到函子的内容上，而 `<*>` 则可应用位于函子
“内部”的函数。将 `f` 看作可能的副作用时，这会刻画求值顺序：`seq` 安排产生函数的副作用
先于产生实参值的副作用发生。

对大多数应用，应使用 `Applicative` 或 `Monad`，而不是直接使用 `Seq`。
-/
class Seq (f : Type u → Type v) : Type (max (u + 1) v) where
  /--
  `<*>` 运算符的实现。

  在单子中，`mf <*> mx` 与 `do let f ← mf; x ← mx; pure (f x)` 相同：它先对函数求值，
  再对实参求值，最后将前者应用于后者。

  为避免令人意外的求值语义，`mx` 以“惰性”方式取得，即使用 `Unit → f α` 函数。

  标识符中记法的约定：

   * `<*>` 在标识符中的推荐拼写是 `seq`。
  -/
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

/--
`<*` 运算符使用 `seqLeft` 重载。

将 `f` 看作潜在副作用时，`<*` 先对左实参求值，再对右实参求值以执行二者的副作用，
丢弃右实参的值并返回左实参的值。

对大多数应用，应使用 `Applicative` 或 `Monad`，而不是直接使用 `SeqLeft`。
-/
class SeqLeft (f : Type u → Type v) : Type (max (u + 1) v) where
  /--
  依次执行两个项的副作用，并丢弃第二个项的值。此函数通常通过 `<*` 运算符调用。

  给定 `x : f α` 和 `y : f β`，`x <* y` 先运行 `x`，再运行 `y`，最后返回 `x` 的结果。

  第二个实参的求值通过将它包装在函数中而延迟，从而使 `f` 能实现“短路”行为。

  标识符中记法的约定：

   * `<*` 在标识符中的推荐拼写是 `seqLeft`。
  -/
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

/--
`*>` 运算符使用 `seqRight` 重载。

将 `f` 看作潜在副作用时，`*>` 先对左实参求值，再对右实参求值以执行二者的副作用，
丢弃左实参的值并返回右实参的值。

对大多数应用，应使用 `Applicative` 或 `Monad`，而不是直接使用 `SeqRight`。
-/
class SeqRight (f : Type u → Type v) : Type (max (u + 1) v) where
  /--
  依次执行两个项的副作用，并丢弃第一个项的值。此函数通常通过 `*>` 运算符调用。

  给定 `x : f α` 和 `y : f β`，`x *> y` 先运行 `x`，再运行 `y`，最后返回 `y` 的结果。

  第二个实参的求值通过将它包装在函数中而延迟，从而使 `f` 能实现“短路”行为。

  标识符中记法的约定：

   * `*>` 在标识符中的推荐拼写是 `seqRight`。
  -/
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

/--
[应用函子](lean-manual://section/monads-and-do)比 `Functor` 更强大，但不如 `Monad` 强大。

应用函子使用 `<*>` 运算符（重载为 `seq`）刻画副作用的顺序执行，但不能刻画依赖数据的
副作用。较早计算的结果不能用于控制较晚的副作用。

应用函子应满足四条定律。`Applicative` 实例不要求证明这些定律；这些定律是
`LawfulApplicative` 类型类的一部分。
-/
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map := fun x y => Seq.seq (Pure.pure x) fun _ => y
  seqLeft := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

/--
`Alternative` 函子是一个可以“失败”或“为空”的 `Applicative` 函子，并带有二元运算 `<|>`，
该运算会“收集值”或寻找“最靠左的成功”。

重要实例包括：
* `Option`，其中 `failure := none`，而 `<|>` 返回最靠左的 `some`。
* 解析器组合子通常为错误处理和回溯提供 `Applicative` 实例。

错误恢复与状态可能以微妙方式相互作用。例如，`OptionT (StateT σ Id)` 的 `Alternative`
实现在从失败中恢复时保留对状态所作的修改，而 `StateT σ (OptionT Id)` 则丢弃这些修改。
-/
class Alternative (f : Type u → Type v) : Type (max (u + 1) v) extends Applicative f where
  /--
  产生空集合或可恢复的失败。`<|>` 运算符收集值或从失败中恢复。详见 `Alternative`。
  -/
  failure : {α : Type u} → f α
  /--
  依照 `Alternative` 实例，收集值或通过返回最靠左的成功从 `failure` 中恢复。也可使用
  `<|>` 运算符语法书写。
  -/
  orElse : {α : Type u} → f α → (Unit → f α) → f α

/--
`>>=` 运算符通过 `bind` 的实例重载。

`Bind` 通常经由扩展它的 `Monad` 使用。
-/
class Bind (m : Type u → Type v) where
  /--
  依次执行两个计算，并允许第二个计算依赖第一个计算所得的值。

  若 `x : m α` 且 `f : α → m β`，则 `x >>= f : m β` 表示执行 `x` 得到类型为 `α` 的值，
  然后将它传给 `f` 所得的结果。

  标识符中记法的约定：

   * `>>=` 在标识符中的推荐拼写是 `bind`。
  -/
  bind : {α β : Type u} → m α → (α → m β) → m β

/--
[单子](https://en.wikipedia.org/wiki/Monad_(functional_programming))是函数式编程中顺序控制流
与副作用的一种抽象。单子既允许副作用依次执行，也允许依赖数据的副作用：较早步骤产生的值
可以影响较晚步骤执行的副作用。

可以直接使用 `Monad` 接口。不过，最常见的用法是通过
[`do` 记法](lean-manual://section/do-notation)访问它。

大多数 `Monad` 实例会提供 `pure` 和 `bind` 的实现，并对从 `Applicative` 继承的其他方法
使用默认实现。单子应满足某些定律，但实例不要求证明这一点。`LawfulMonad` 实例表示给定单子的
运算是合法的。
-/
class Monad (m : Type u → Type v) : Type (max (u + 1) v) extends Applicative m, Bind m where
  map f x := Bind.bind x (Function.comp Pure.pure f)
  seq f x := Bind.bind f fun y => Functor.map y (x ())
  seqLeft x y := Bind.bind x fun a => Bind.bind (y ()) (fun _ => Pure.pure a)
  seqRight x y := Bind.bind x fun _ => y ()

/--
丢弃函子中的值，同时保留函子的结构。

当使用 `Applicative` 函子或 `Monad` 实现副作用，而某个操作只应为其副作用而执行时，
丢弃值尤其有用。在 `do` 记法中，值被丢弃的语句必须返回 `Unit`；可以使用 `discard`
显式丢弃这些语句的值。
-/
def discard := @_root_.Functor.discard

/-- 若命题 `p` 为真，则什么也不做；否则（使用 `failure`）失败。 -/
def guard := @_root_.guard

/-- 若 `f` 成功并得到值 `x`，则返回 `some x`；否则返回 `none`。 -/
def optional := @_root_.optional

/--
将单子动作 `x` 的结果转换为 `Bool`。若结果为 `true`，则返回 `y`；否则返回 `x` 的原始结果。

这是短路运算符 `&&` 的单子对应物，通常通过 `<&&>` 运算符使用。

标识符中记法的约定：

 * `<&&>` 在标识符中的推荐拼写是 `andM`。
-/
def andM := @_root_.andM

/--
将单子动作 `x` 的结果转换为 `Bool`。若结果为 `true`，则返回该结果并忽略 `y`；否则运行 `y`
并返回其结果。

这是短路运算符 `||` 的单子对应物，通常通过 `<||>` 运算符使用。

标识符中记法的约定：

 * `<||>` 在标识符中的推荐拼写是 `orM`。
-/
def orM := @_root_.orM

/-- 运行单子动作并返回其结果的否定。 -/
def notM := @_root_.notM

namespace Bind

/--
Kleisli 箭头的从左到右复合。

标识符中记法的约定：

 * `>=>` 在标识符中的推荐拼写是 `kleisliRight`。
-/
def kleisliRight := @_root_.Bind.kleisliRight

/--
Kleisli 箭头的从右到左复合。

标识符中记法的约定：

 * `<=<` 在标识符中的推荐拼写是 `kleisliLeft`。
-/
def kleisliLeft := @_root_.Bind.kleisliLeft

/--
与 `Bind.bind` 相同，但实参顺序相反。

标识符中记法的约定：

 * `=<<` 在标识符中的推荐拼写是 `bindLeft`。
-/
def bindLeft := @_root_.Bind.bindLeft

end Bind

namespace Functor

/--
将函数映射到函子上，但交换参数顺序，使函数位于最后。

此函数是参数顺序反转的 `Functor.map`，通常通过 `<&>` 运算符使用。

标识符中记法的约定：

 * `<&>` 在标识符中的推荐拼写是 `mapRev`。
-/
def mapRev := @_root_.Functor.mapRev

end Functor

/--
满足函子定律的函子。

`Functor` 类型类包含函子的运算，但不要求实例证明它们满足函子定律。`LawfulFunctor` 实例
包含这些定律成立的证明。由于 `Functor` 实例可以为 `mapConst` 提供优化实现，
`LawfulFunctor` 实例还必须证明该优化实现等价于标准实现。
-/
class LawfulFunctor (f : Type u → Type v) [_root_.Functor f] : Prop where
  /-- `mapConst` 的实现等价于默认实现。 -/
  map_const : ∀ {α β : Type u},
    (_root_.Functor.mapConst : α → f β → f α) = _root_.Functor.map ∘ Function.const β
  /-- `map` 的实现保持恒等函数。 -/
  id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  /-- `map` 的实现保持函数复合。 -/
  comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α),
    (h ∘ g) <$> x = h <$> g <$> x

/--
满足应用函子定律的应用函子。

`Applicative` 类型类包含应用函子的运算，但不要求实例证明它们满足应用函子定律。
`LawfulApplicative` 实例包含这些定律成立的证明。

由于 `Applicative` 实例可以为 `seqLeft` 和 `seqRight` 提供优化实现，
`LawfulApplicative` 实例还必须证明这些优化实现等价于标准实现。
-/
class LawfulApplicative (f : Type u → Type v) [_root_.Applicative f] : Prop
    extends LawfulFunctor f where
  /-- `seqLeft` 等价于默认实现。 -/
  seqLeft_eq : ∀ {α β : Type u} (x : f α) (y : f β),
    x <* y = Function.const β <$> x <*> y
  /-- `seqRight` 等价于默认实现。 -/
  seqRight_eq : ∀ {α β : Type u} (x : f α) (y : f β),
    x *> y = Function.const α id <$> x <*> y
  /--
  `pure` 出现在 `seq` 之前等价于 `Functor.map`。

  这意味着紧邻 `seq` 之前出现的 `pure` 确实是纯的。
  -/
  pure_seq : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x
  /--
  将函数映射到 `pure` 的结果上，等价于在 `pure` 之下应用该函数。

  这意味着相对于 `Functor.map`，`pure` 确实是纯的。
  -/
  map_pure : ∀ {α β : Type u} (g : α → β) (x : α),
    g <$> (pure x : f α) = pure (g x)
  /--
  `pure` 出现在 `seq` 之后等价于 `Functor.map`。

  这意味着紧邻 `seq` 之后出现的 `pure` 确实是纯的。
  -/
  seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α),
    g <*> pure x = (fun h => h x) <$> g
  /--
  `seq` 满足结合律。

  在保持计算顺序不变的前提下改变 `seq` 调用的嵌套，会得到等价的计算。这意味着 `seq`
  除了安排顺序之外不做任何额外工作。
  -/
  seq_assoc : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)),
    h <*> (g <*> x) = Function.comp <$> h <*> g <*> x

/--
合法单子是满足某种行为规范的单子。所有 `Monad` 实例都应满足这些定律，但并非所有实现都
必须给出证明。

`LawfulMonad.mk'` 是一个替代构造器，它为许多字段提供了有用的默认值。
-/
class LawfulMonad (m : Type u → Type v) [_root_.Monad m] : Prop
    extends LawfulApplicative m where
  /--
  `bind` 后接与函数复合的 `pure`，等价于函子映射。

  这意味着 `bind` 之后的 `pure` 确实是纯的，不会产生副作用。
  -/
  bind_pure_comp : ∀ {α β : Type u} (f : α → β) (x : m α),
    (do let a ← x; pure (f a)) = f <$> x
  /--
  `bind` 后接函子映射，等价于 `Applicative` 的顺序执行。

  这意味着 `Monad` 与 `Applicative` 的副作用顺序执行方式相同。
  -/
  bind_map : ∀ {α β : Type u} (f : m (α → β)) (x : m α),
    (do let g ← f; g <$> x) = f <*> x
  /--
  `pure` 后接 `bind`，等价于函数应用。

  这意味着 `bind` 之前的 `pure` 确实是纯的，不会产生副作用。
  -/
  pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
  /--
  `bind` 满足结合律。

  在保持计算顺序不变的前提下改变 `bind` 调用的嵌套，会得到等价的计算。这意味着 `bind`
  除了依赖数据地安排顺序之外不做更多工作。
  -/
  bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
    x >>= f >>= g = x >>= fun x => f x >>= g

namespace LawfulMonad

/-- 常见情况下具有更多可使用默认值字段的 `LawfulMonad` 替代构造器。 -/
abbrev mk' := @_root_.LawfulMonad.mk'

end LawfulMonad

/--
单子 `m` 中的计算可以在单子 `n` 中运行。编译器会自动插入这些转换。

通常，`n` 由若干单子变换器应用于 `m` 而成，但这不是强制要求。

新实例应使用此类型类 `MonadLift`。需要将一个单子提升到另一个单子的客户端则应请求
`MonadLiftT`；后者是 `MonadLift` 的自反传递闭包。
-/
class MonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- 将动作从单子 `m` 转换到单子 `n`。 -/
  monadLift : {α : Type u} → m α → n α

/--
单子 `m` 中的计算可以在单子 `n` 中运行。编译器会自动插入这些转换。

通常，`n` 由若干单子变换器应用于 `m` 而成，但这不是强制要求。

这是 `MonadLift` 的自反传递闭包。需要将一个单子提升到另一个单子的客户端应请求
`MonadLiftT` 实例。新实例则应为 `MonadLift` 本身定义。
-/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  /-- 将动作从单子 `m` 转换到单子 `n`。 -/
  monadLift : {α : Type u} → m α → n α

/--
一种将 `m` 中完全多态的函数解释到 `n` 中的方法。这样的函数可以被看作可能改变 `m` 中的
副作用，但不能根据所提供的具体值来改变副作用。

`MonadFunctor` 的客户端通常应使用 `MonadFunctorT`，后者是 `MonadFunctor` 的自反传递闭包。
新实例应为 `MonadFunctor` 定义。
-/
class MonadFunctor (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- 将 `m` 的完全多态变换提升到 `n` 中。 -/
  monadMap : {α : Type u} → ({β : Type u} → m β → m β) → n α → n α

/--
一种将 `m` 中完全多态的函数解释到 `n` 中的方法。这样的函数可以被看作可能改变 `m` 中的
副作用，但不能根据所提供的具体值来改变副作用。

这是 `MonadFunctor` 的自反传递闭包，会按需自动串接 `MonadFunctor` 实例。
`MonadFunctor` 的客户端通常应使用 `MonadFunctorT`，但新实例应为 `MonadFunctor` 定义。
-/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) where
  /-- 将 `m` 的完全多态变换提升到 `n` 中。 -/
  monadMap : {α : Type u} → ({β : Type u} → m β → m β) → n α → n α

/--
一种将计算从一个单子提升到另一个单子的方法，同时为被提升的计算提供一种解释外层单子计算的
手段。这样便可自动提升高阶运算。

客户端通常应使用 `control` 或 `controlAt`，它们请求 `MonadControlT` 实例；后者是
`MonadControl` 的自反传递闭包。新实例应为 `MonadControl` 本身定义。
-/
class MonadControl (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- 可用于同时重建返回值及外层单子所用任何状态的类型。 -/
  stM : Type u → Type u
  /--
  将动作从内层单子 `m` 提升到外层单子 `n`。内层单子可以使用反向提升运算符来运行 `n`
  动作，并一并返回值和状态。
  -/
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  /--
  将内层单子中返回状态和值的单子动作提升为外层单子中的动作。额外状态信息用于恢复传给
  `liftWith` 参数的反向提升所产生的副作用结果。
  -/
  restoreM : {α : Type u} → m (stM α) → n α

/--
一种将计算从一个单子提升到另一个单子的方法，同时为被提升的计算提供一种解释外层单子计算的
手段。这样便可自动提升高阶运算。

客户端通常应使用 `control` 或 `controlAt`，它们请求 `MonadControlT` 实例；后者是
`MonadControl` 的自反传递闭包。新实例应为 `MonadControl` 本身定义。
-/
class MonadControlT (m : Type u → Type v) (n : Type u → Type w) where
  /-- 可用于同时重建返回值及外层单子所用任何状态的类型。 -/
  stM : Type u → Type u
  /--
  将动作从内层单子 `m` 提升到外层单子 `n`。内层单子可以使用反向提升运算符来运行 `n`
  动作，并一并返回值和状态。
  -/
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  /--
  将内层单子中返回状态和值的单子动作提升为外层单子中的动作。额外状态信息用于恢复传给
  `liftWith` 参数的反向提升所产生的副作用结果。
  -/
  restoreM : {α : Type u} → stM α → n α

/--
将运算从内层单子提升到外层单子，并向其提供反向提升运算符，使外层单子计算可在内层单子中
运行。被提升的运算必须返回重建反向提升在外层单子中的副作用所需的额外信息；这些额外信息由
`stM` 决定。

此函数将内层单子作为隐式参数。若要显式指定它，请使用 `controlAt`。
-/
def control := @_root_.control

/--
将运算从内层单子提升到外层单子，并向其提供反向提升运算符，使外层单子计算可在内层单子中
运行。被提升的运算必须返回重建反向提升在外层单子中的副作用所需的额外信息；这些额外信息由
`stM` 决定。

此函数将内层单子作为显式参数。若要推断该单子，请使用 `control`。
-/
def controlAt := @_root_.controlAt

/--
`do` 块中的单子迭代，使用 `for x in xs` 记法。

参数 `m` 是执行迭代所在 `do` 块的单子，`ρ` 是被迭代集合的类型，`α` 是元素类型。
-/
class ForIn (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) where
  /--
  以单子方式迭代集合 `xs` 的内容，带有局部状态 `b`，并允许提前终止。

  由于 `do` 块支持局部可变绑定以及 `return` 和 `break`，传给 `ForIn.forIn` 的单子动作除了
  集合的当前元素之外还接收一个初始状态，并返回更新后的状态以及迭代应继续还是终止的指示。
  若该动作返回 `ForInStep.done`，则 `ForIn.forIn` 应停止迭代并返回更新后的状态。若该动作
  返回 `ForInStep.yield`，则当还有后续元素时，`ForIn.forIn` 应继续迭代，并把更新后的状态
  传给该动作。

  关于如何将 `for` 循环翻译为 `ForIn.forIn` 的更多信息，见
  [Lean 参考手册](lean-manual://section/monad-iteration-syntax)。
  -/
  forIn : {β : Type u₁} → ρ → β → (α → β → m (_root_.ForInStep β)) → m β

/--
`do` 块中带成员关系证明的单子迭代，使用 `for h : x in xs` 记法。

参数 `m` 是执行迭代所在 `do` 块的单子，`ρ` 是被迭代集合的类型，`α` 是元素类型，`d` 是要
提供的特定成员关系谓词。
-/
class ForIn' (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v))
    (d : outParam (_root_.Membership α ρ)) where
  /--
  以单子方式迭代集合 `xs` 的内容，带有局部状态 `b`，并允许提前终止。每次迭代时，循环体
  都会获得当前元素属于该集合的证明。

  由于 `do` 块支持局部可变绑定以及 `return` 和 `break`，传给 `ForIn'.forIn'` 的单子动作
  除了集合的当前元素及其成员关系证明之外还接收一个初始状态。该动作返回更新后的状态以及
  迭代应继续还是终止的指示。若动作返回 `ForInStep.done`，则 `ForIn'.forIn'` 应停止迭代并
  返回更新后的状态。若动作返回 `ForInStep.yield`，则当还有后续元素时，`ForIn'.forIn'`
  应继续迭代，并把更新后的状态传给该动作。

  关于如何将 `for` 循环翻译为 `ForIn'.forIn'` 的更多信息，见
  [Lean 参考手册](lean-manual://section/monad-iteration-syntax)。
  -/
  forIn' : {β : Type u₁} → (x : ρ) → β →
    ((a : α) → a ∈ x → β → m (_root_.ForInStep β)) → m β

/--
用于编译 `for x in xs` 记法的指示，表明循环体是否提前终止。

集合的 `ForIn` 或 `ForIn'` 实例描述如何迭代其元素。表示循环体的单子动作返回
`ForInStep α`，其中 `α` 是用于实现 `let mut` 等功能的局部状态。
-/
inductive ForInStep (α : Type u) where
  /--
  循环应提前终止。

  循环体中使用 `break` 或 `return` 会产生 `ForInStep.done`。
  -/
  | done : α → ForInStep α
  /--
  循环应带着下一次迭代继续，并使用所返回的状态。

  `continue` 以及到达循环体末尾会产生 `ForInStep.yield`。
  -/
  | yield : α → ForInStep α

namespace ForInStep

/-- 从 `ForInStep` 中提取值，忽略它是 `ForInStep.done` 还是 `ForInStep.yield`。 -/
def value := @_root_.ForInStep.value

end ForInStep

/--
在某种容器类型上进行重载的单子迭代。

`ForM m γ α` 实例描述如何在单子 `m` 中，把单子运算迭代应用于类型为 `γ`、元素类型为 `α`
的容器。元素类型应由单子和容器唯一确定。

使用 `ForM.forIn` 可从 `ForM` 实例构造 `ForIn` 实例，从而能在 `do` 记法中使用 `for`
运算符。
-/
class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  /-- 在集合 `coll` 的每个元素上运行单子动作 `f`。 -/
  forM : γ → (α → m PUnit) → m PUnit

namespace ForM

/-- 从 `ForM` 实例创建 `ForIn.forIn` 的适当实现。 -/
def forIn := @_root_.ForM.forIn

end ForM

/-- 需要时插入单子提升（即 `liftM` 和强制转换）。 -/
def autoLift : Lean.Option Bool := Lean.Meta.autoLift

end Manual.ZhDocString.Monads.Core
