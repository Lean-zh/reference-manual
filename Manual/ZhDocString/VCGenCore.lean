import Manual.ZhDocString
import Std.Tactic.Do

namespace ZhDoc

/--
状态上的谓词，其中每个状态由一个组成状态类型列表定义。

示例：
```lean example
SPred [Nat, Bool] = (Nat → Bool → ULift Prop)
```
-/
axiom SPred (σs : List (Type u)) : Type u

namespace SPred

/--
将纯命题 `P : Prop` 嵌入 `SPred`。
建议优先使用记法 `⌜P⌝`。
-/
axiom pure : Unit

/-- 将纯 Lean 值嵌入 `SVal`。这是 `SPred.pure` 的别名。 -/
axiom embedSyntax : Unit

/--
`SPred` 中的蕴涵。

如果在 `P` 为真的每个状态中 `Q` 也为真，就称谓词 `P` 蕴涵谓词 `Q`。
与蕴含（`SPred.imp`）不同，蕴涵本身不是 `SPred`，而是普通命题。
-/
axiom entails : Unit

/--
`SPred` 中的逻辑等价。

逻辑等价的谓词相等。可使用 `SPred.bientails.to_eq` 将双向蕴涵转换为等式。
-/
axiom bientails : Unit

/-- `SPred` 中的蕴涵；`SPred.entails` 的语法糖。 -/
axiom entailsSyntax : Unit

/-- `SPred` 中的重言式；`SPred.entails ⌜True⌝` 的语法糖。 -/
axiom tautologySyntax : Unit

/-- `SPred` 中的双向蕴涵；`SPred.bientails` 的语法糖。 -/
axiom bientailsSyntax : Unit

/-- `SPred` 中的合取：同时满足 `P` 和 `Q` 的状态满足 `spred(P ∧ Q)`。 -/
axiom and : Unit

/--
有状态谓词列表的合取。当且仅当一个状态满足 `env` 中的所有谓词时，它满足
`conjunction env`。
-/
axiom conjunction : Unit

/-- `SPred` 中的析取：满足 `P` 或 `Q` 的状态满足 `spred(P ∨ Q)`。 -/
axiom or : Unit

/-- `SPred` 中的否定：不满足 `P` 的状态满足 `spred(¬ P)`。 -/
axiom not : Unit

/--
`SPred` 中的蕴含：只要满足 `P` 就也满足 `Q` 的状态满足 `spred(P → Q)`。
-/
axiom imp : Unit

/--
`SPred` 中的双条件：同时满足 `P` 和 `Q`，或二者都不满足的状态满足
`spred(P ↔ Q)`。
-/
axiom iff : Unit

/-- `SPred` 中的全称量词。 -/
axiom «forall» : Unit

/-- `SPred` 中的存在量词。 -/
axiom «exists» : Unit

end SPred

/--
由柯里化的状态元组索引的值。

示例：
```
example : SVal [Nat, Bool] String = (Nat → Bool → String) := rfl
```
-/
axiom SVal (σs : List (Type u)) (α : Type u) : Type u

namespace SVal

/-- 获取 `SVal` 中类型为 `σ` 的最上层状态。 -/
axiom getThe : Unit

/-- 捕获一个 `SVal` 完整状态的元组。 -/
axiom StateTuple : Unit

/-- 将接受 `StateTuple` 的函数柯里化为 `SVal`。 -/
axiom curry : Unit

/-- 将 `SVal` 反柯里化为接受 `StateTuple` 的函数。 -/
axiom uncurry : Unit

end SVal

/--
用于对单子进行推理的后置条件的“形状”。

后置条件形状是对许多可能的单子效应的抽象，其依据是能够模拟这些效应的纯函数结构。单子的后置条件形状由其 `WP` 实例给出，并用于确定其 `Assertion` 和 `PostCond`。
-/
inductive PostShape : Type (u + 1) where
  /-- 此单子中的断言和后置条件既不使用状态，也不使用异常。 -/
  | pure : PostShape
  /--
  此单子中的断言可以提及类型为 `σ` 的状态的当前值，后置条件则可以提及该状态的最终值。
  -/
  | arg : (σ : Type u) → PostShape → PostShape
  /--
  此单子中的后置条件包含关于类型为 `ε`、由提前终止产生的异常值的断言。
  -/
  | except : (ε : Type u) → PostShape → PostShape

namespace PostShape

/--
提取 `PostShape.arg` 构造器下的状态类型列表，并丢弃异常类型。

这些状态类型决定单子中断言的形状。
-/
axiom args : Unit

end PostShape

/--
关于后置条件形状为 `ps` 的单子的各个状态字段的断言。

具体而言，它是将 `SPred` 应用于给定谓词形状中各个 `.arg` 的缩写，因此所有关于 `SPred` 的定理都适用。

示例：
```lean example
example : Assertion (.arg ρ .pure) = (ρ → ULift Prop) := rfl
example : Assertion (.except ε .pure) = ULift Prop := rfl
example : Assertion (.arg σ (.except ε .pure)) = (σ → ULift Prop) := rfl
example : Assertion (.except ε (.arg σ .pure)) = (σ → ULift Prop) := rfl
```
-/
axiom Assertion : Unit

/--
给定谓词形状的后置条件：正常终止情形有一个 `Assertion`，谓词形状中的每个 `.except` 层也各有一个 `Assertion`。
```
variable (α σ ε : Type)
example : PostCond α (.arg σ .pure) = ((α → σ → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε .pure) = ((α → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → ULift Prop) × (ε → σ → ULift Prop) × PUnit) := rfl
```
-/
axiom PostCond : Unit

/--
关于后置条件形状中声明的每种潜在异常的断言。

示例：
```lean example
example : ExceptConds (.pure) = Unit := rfl
example : ExceptConds (.except ε .pure) = ((ε → ULift Prop) × Unit) := rfl
example : ExceptConds (.arg σ (.except ε .pure)) = ((ε → ULift Prop) × Unit) := rfl
example : ExceptConds (.except ε (.arg σ .pure)) = ((ε → σ → ULift Prop) × Unit) := rfl
```
-/
axiom ExceptConds : Unit

namespace PostCond

/--
表示完全正确性的后置条件。
也就是说，它表示所断言的计算会无异常地结束，*并且*其结果满足给定谓词 `p`。
-/
axiom noThrow : Unit

/--
表示完全正确性的后置条件。
也就是说，它表示所断言的计算会无异常地结束，*并且*其结果满足给定谓词 `p`。
-/
axiom noThrowSyntax : Unit

/--
表示部分正确性的后置条件。
也就是说，它表示*如果*所断言的计算无异常地结束，*那么*其结果满足给定谓词 `p`。
当计算抛出异常时，不作任何断言。
-/
axiom mayThrow : Unit

/--
表示部分正确性的后置条件。
也就是说，它表示*如果*所断言的计算无异常地结束，*那么*其结果满足给定谓词 `p`。
当计算抛出异常时，不作任何断言。
-/
axiom mayThrowSyntax : Unit

/--
后置条件的蕴涵。

它由以下两部分组成：
 * 对所有可能的返回值，关于返回值的断言之间存在蕴涵。
 * 异常条件之间存在蕴涵。

后置条件的蕴含（`PostCond.imp`）会产生新的后置条件，而蕴涵则是普通命题。
-/
axiom entails : Unit

/--
后置条件的合取。

它按点定义：关于返回值的断言取合取，关于每种潜在异常的断言也分别取合取。
-/
axiom and : Unit

/--
后置条件的蕴含。

它按点定义：关于返回值的断言取蕴含，关于每种潜在异常的断言也分别取蕴含。

后置条件的蕴涵（`PostCond.entails`）是普通命题，而后置条件的蕴含本身仍是后置条件。
-/
axiom imp : Unit

end PostCond

/-- 后置条件越强，变换后得到的前置条件也越强。 -/
axiom PredTransMonotonic : Unit

/--
变换后置条件的合取，等价于分别变换这些后置条件后再取合取。
-/
axiom PredTransConjunctive : Unit

/--
给定 `ps : PostShape` 和返回类型 `α : Type` 时的谓词变换器类型。谓词变换器
`x : PredTrans ps α` 是一个函数：它接受后置条件 `Q : PostCond α ps`，并返回前置条件
`x.apply Q : Assertion ps`。
-/
structure PredTrans (ps : PostShape) (α : Type u) : Type u where
  /-- 实现谓词变换器的函数。 -/
  trans : Unit
  /--
  谓词变换器满足合取性：`t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`。
  因此，后置条件越强，得到的前置条件也越强。
  -/
  conjunctiveRaw : Unit

end ZhDoc
