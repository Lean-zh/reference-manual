import Std.Tactic.Do

namespace ZhDoc

open Std.Do

universe u v

namespace PredTrans

/-- 变换后的前置条件会随后置条件增强而增强。 -/
def Monotonic : Prop := True

/--
变换后置条件的合取，等价于对各后置条件分别变换后再取合取。
-/
def Conjunctive : Prop := True

/--
恒等谓词变换器：它把后置条件中关于返回值的断言实例化到 `a`。
-/
def pure : Prop := True

/-- 通过复合两个谓词变换器，将它们按顺序连接起来。 -/
def bind : Prop := True

/--
为后置条件形状为 `ps` 的谓词变换器加入对 `σ` 类型状态作断言的能力，所得后置条件形状为 `.arg σ ps`。
这是通过把 `StateT σ (PredTrans ps) α` 解释为 `PredTrans (.arg σ ps) α` 实现的。

这种解释也适用于读取器效应或只能追加的状态等各种类似状态的效应，只需将它们视为状态即可。
-/
def pushArg : Prop := True

/--
为后置条件形状为 `ps` 的谓词变换器加入对 `ε` 类型异常作断言的能力，所得后置条件形状为 `.except ε ps`。
这是通过把 `ExceptT ε (PredTrans ps) α` 解释为 `PredTrans (.except ε ps) α` 实现的。

这种解释也适用于提前终止等各种类似异常的效应，只需将它们视为异常即可。
-/
def pushExcept : Prop := True

/--
为后置条件形状为 `ps` 的谓词变换器加入对提前终止作断言的能力，所得后置条件形状为 `.except PUnit ps`。
这是通过把 `OptionT (PredTrans ps) α` 解释为 `PredTrans (.except PUnit ps) α` 实现的，其中将 `Option` 建模为等价于 `Except PUnit`。
-/
def pushOption : Prop := True

end PredTrans

/--
用谓词变换器 `PredTrans ps α` 表示单子程序 `x : m α` 的最弱前置条件解释。
单子 `m` 决定 `ps : PostShape`。

在实际推理中，除了 `WP m ps`，通常还需要一个 `WPMonad m ps` 实例。
-/
class WP (m : Type u → Type v) (ps : outParam PostShape.{u}) where
  /-- 将单子程序 `x : m α` 解释为谓词变换器 `PredTrans ps α`。 -/
  wp {α} (x : m α) : PredTrans ps α

/--
`wp⟦x⟧ Q` 按定义等于 `(WP.wp x).apply Q`。
-/
def «termWp⟦_:_⟧» : Prop := True

/--
带最弱前置条件（`WP`）的单子，并且其解释还是一个保持 `pure` 和 `bind` 的单子态射。

实践中，对于没有 `WPMonad` 实例的单子，`mvcgen` 通常无法有效地推理程序。
`Pure.pure`、`Bind.bind` 以及 `Functor.map` 等运算符的规约引理，都要求相应单子具有 `WPMonad` 实例。
-/
class WPMonad (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m]
    extends LawfulMonad m, WP m ps where
  /-- `WP.wp` 保持 `pure`。 -/
  wp_pure : ∀ {α} (a : α), WP.wp (m := m) (pure a) = Std.Do.PredTrans.pure a
  /-- `WP.wp` 保持 `bind`。 -/
  wp_bind : ∀ {α β} (x : m α) (f : α → m β),
    WP.wp (m := m) (do let a ← x; f a) = do let a ← WP.wp (m := m) x; WP.wp (m := m) (f a)

namespace Id

/--
`Id.run` 的可靠性引理。它由 `WPSound.of_wp_canReturn` 推导而来：
`Id.run prog = x` 正是 `MonadAttach.CanReturn prog x` 的见证。
-/
def of_wp_run_eq : Prop := True

end Id

namespace StateM

/-- `StateM.run` 的可靠性引理；它是 `StateT.of_wp_run` 在 `Id` 上的特化。 -/
def of_wp_run_eq : Prop := True

/-- `StateM.run'` 的可靠性引理；它是 `StateT.of_wp_run` 在 `Id` 上的特化。 -/
def of_wp_run'_eq : Prop := True

end StateM

namespace ReaderM

/-- `ReaderM.run` 的可靠性引理；它是 `ReaderT.of_wp_run` 在 `Id` 上的特化。 -/
def of_wp_run_eq : Prop := True

end ReaderM

namespace Except

/-- `Except` 的可靠性引理；它是 `ExceptT.of_wp_run` 在 `Id` 上的特化。 -/
def of_wp_eq : Prop := True

end Except

namespace EStateM

/--
`EStateM.run` 的可靠性引理。
当需要证明表达式 `x`（定义为 `EStateM.run prog s`）的性质，并希望用 `mvcgen` 推理 `prog` 时，此引理很有用。
-/
def of_wp_run_eq : Prop := True

end EStateM

/--
用于推理单子程序的霍尔三元组。霍尔三元组 `Triple x P Q` 是 `x` 的一个*规约*：
若断言 `P` 在 `x` 运行前成立，则后置条件 `Q` 在 `x` 运行后成立。

`⦃P⦄ x ⦃Q⦄` 是 `Triple x P Q` 的便捷语法。
-/
def Triple : Prop := True

namespace Triple

/--
同一程序 `x` 的两个霍尔三元组规约的合取。
该定理便于分解证明：可分别证明关于 `x` 的互不相关的事实，再用此定理将它们合并。
-/
def and : Prop := True

/--
同一程序 `x` 的两个霍尔三元组规约上的肯定前件规则。
该定理便于拆分证明。若 `h₁ : Triple x P₁ Q₁` 证明了 `x` 的基础性质，而
`h₂ : Triple x P₂ (Q₁ →ₚ Q₂)` 是建立在 `Q₁` 基础上的 `Q₂` 高级证明，
则 `mp x h₁ h₂` 给出关于 `x` 的 `Q₂` 证明。
-/
def mp : Prop := True

end Triple

/--
带 `spec` 属性的定理由 `mspec` 和 `mvcgen` 策略使用。

* 当该属性用于定理 `foo_spec : Triple (foo a b c) P Q` 时，`mspec` 和 `mvcgen` 会将
  `foo_spec` 用作调用 `foo` 的规约。
* 否则，当该属性用于一个可由 `@[simp]` 化简的定义时，该定义会加入 `mvcgen` 的内部
  simp 集；此 simp 集用于在 `wp⟦·⟧` 上下文中化简模式匹配的判别项和常量的应用。
-/
def spec : Prop := True

/--
`for ... in ...` 循环的规约所使用的循环不变式类型。
循环不变式是一个接受下列参数的 `PostCond`：

* 表示循环迭代状态的 `List.Cursor xs`。它以 `for` 循环迭代的元素列表 `xs` 为参数。
* 类型为 `β` 的状态元组；它是若干层 `MProd` 的嵌套，表示 `let mut` 变量和提前返回。

循环规约引理按如下方式使用它：进入循环前，游标前缀为空，后缀为 `xs`；
离开循环后，游标前缀为 `xs`，后缀为空；归纳步骤中，不变式对首元素为 `x` 的后缀成立；
运行循环体后，把 `x` 移到前缀，不变式仍然成立。
-/
def Invariant : Prop := True

namespace Invariant

/--
用于为带提前返回的循环指定循环不变式的辅助定义。

返回类型为 `γ` 的 `for ... in ...` 循环会精译为如下调用：
```lean
forIn (β := MProd (Option γ) ...) (b := ⟨none, ...⟩) collection loopBody
```
注意，`MProd` 状态元组的第一个分量是可选的提前返回值。没有提前返回时它为 `none`，
循环以 `r` 提前返回时则为 `some r`。

此函数可根据循环体是否提前终止来指定不同的不变式。发生提前返回时，循环实际上已经结束；
不变式中的附加断言 `⌜xs.suffix = []⌝` 编码了这一事实。该断言对顺利证明归纳步骤至关重要：
它与循环体开始处归纳假设中的 `xs.suffix = x::rest` 相矛盾，因此用户无需证明“循环已经提前返回，
却又执行下一次循环体迭代”这一虚假情形。
-/
def withEarlyReturn : Prop := True

end Invariant

namespace List

/--
指向列表中特定位置的指针。列表游标用于 `mvcgen` 策略的循环不变式。

将游标向左或向右移动所需时间与游标当前位置成线性关系，因此这种数据结构不适合运行时代码。
-/
structure Cursor {α : Type u} (l : _root_.List α) : Type u where
  /-- 列表中位于当前位置之前的元素。 -/
  «prefix» : _root_.List α
  /--
  从当前位置开始的元素。若当前位置在最后一个元素之后，则后缀为空；否则，后缀的第一个元素
  就是游标当前指向的元素。
  -/
  suffix : _root_.List α
  /-- 将前缀与后缀连接起来可得到原列表。 -/
  property : «prefix» ++ suffix = l

namespace Cursor

/--
在列表 `l` 的位置 `n` 创建游标。
前缀包含最前面的 `n` 个元素，后缀包含其余元素。
若 `n` 大于列表长度，则游标位于列表末尾。
-/
def «at» : Prop := True

/--
游标在列表中的位置。
这是前缀元素数量的简写。
-/
def pos : Prop := True

/--
返回游标当前位置的元素。

要求当前位置确实存在元素：后缀必须非空，因此游标不能位于列表末尾。
-/
def current : Prop := True

/--
将游标向前推进一个位置，把当前元素从后缀移到前缀。

要求游标尚未位于列表末尾。
-/
def tail : Prop := True

/--
在列表开头（位置 0）创建游标。
前缀为空，后缀为整个列表。
-/
def begin : Prop := True

/--
在列表末尾创建游标。
前缀为整个列表，后缀为空。
-/
def «end» : Prop := True

end Cursor
end List

end ZhDoc
