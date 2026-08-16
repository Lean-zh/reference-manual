/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.25.0 (2025-11-14)" =>
%%%
tag := "release-v4.25.0"
file := "v4.25.0"
%%%

````markdown
本次发布共合入 398 项改动。除下文列出的 141 项功能新增和 83 项修复外，还有 21 项重构、9 项文档改进、4 项性能改进、5 项测试套件改进，以及 135 项其他改动。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights"
%%%

````markdown

Lean v4.25.0 带来了多项令人兴奋的新特性。编辑器集成为 “try this” 建议增加了交互性，Lake 增加了远程缓存支持。新的语言特性包括：自动为类型类方法生成规格定理、余归纳谓词，以及 `mvcgen` 中的不变式建议。`grind` 获得了一个交互模式，允许用户控制证明搜索，并可建议可复现的证明脚本。其推理能力还扩展到了单射函数、非交换（半）环，以及预序和有序环结构。标准库则带来了重新设计的 `String` 类型和更丰富的异步原语。请继续阅读下文了解详情！

````
## 应用 “try this” 建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Apply-___try-this___-Suggestions"
%%%

````markdown

[#10524](https://github.com/leanprover/lean4/pull/10524) 为 [#9966](https://github.com/leanprover/lean4/pull/9966) 中引入的 “try this” 消息增加了交互性（如悬停和转到定义）。同时，它把“应用建议”的链接改成了建议前方单独的 `[apply]` 按钮。

````
## Lake 的远程缓存
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Remote-Caching-with-Lake"
%%%

````markdown

[#10188](https://github.com/leanprover/lean4/pull/10188) 为 Lake 增加了远程构件缓存（例如 Reservoir）支持。作为这项支持的一部分，还引入了一组新的 `lake cache` CLI 命令，用于管理 Lake 的缓存；现有的本地缓存支持也经过了重构，以便更好地与新的远程支持协同工作。

````
## 余归纳谓词
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Coinductive-Predicates"
%%%

````markdown

[#10333](https://github.com/leanprover/lean4/pull/10333) 引入了 `coinductive` 关键字，可用与 `inductive` 关键字相同的语法来定义余归纳谓词。

例如，关系中的无限迁移序列可以通过下面的方式给出：

```lean
section
variable (α : Type)
coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/--
info: infSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) (hyp : ∀ (a : α), pred a → ∃ b, r a b ∧ pred b)
  (a✝ : α) : pred a✝ → infSeq α r a✝
-/
#guard_msgs in
#check infSeq.coinduct

/--
info: infSeq.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq α r b → infSeq α r a
-/
#guard_msgs in
#check infSeq.step
end
```

该机器还支持`mutual`块,并混合了感应和感应的上游定义:

```lean
mutual
  coinductive tick : Prop where
  | mk : ¬tock → tick

  inductive tock : Prop where
  | mk : ¬tick → tock
end

/--
info: tick.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  (pred_1 → tick) ∧ (tock → pred_2)
-/
#guard_msgs in
#check tick.mutual_induct
```

````
## `mvcgen` 不变式建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Mvcgen-Invariants-Suggestions"
%%%

````markdown

[#10456](https://github.com/leanprover/lean4/pull/10456)和[#10566](https://github.com/leanprover/lean4/pull/10566)
实现了 `mvcgen invariants?`，可根据不变式在 VC 中的使用方式来建议具体不变式。
这些建议是刻意保持简单的，基本可以概括为：“这在循环开始时成立，而且在循环结束时也必须成立”：
循环 :

```lean
import Std.Tactic.Do
open Std Do

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit
```

当环形体早日返回的时候,它能建议将它当作一个骸骨。

```lean
import Std.Tactic.Do
import Std

open Std Do

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜l.Nodup ∧ (r = true ↔ l.Nodup)⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = ∅ ∨ xs.suffix = [] ∧ l.Nodup⌝)
-/
-- #guard_msgs (info) in
theorem nodup_suggest_invariant (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit
```

用户仍有责任削弱这种变数,使其能渗透到所有循环迭代中,
但它是迭代的良好起点。它也很有用,因为用户不需要记住
确切的语法。

````
## `grind`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind"
%%%

````markdown

````
### 交互模式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Interactive-mode"
%%%

````markdown

`grind` 延长了交互模式`grind => …`
[#10607](https://github.com/leanprover/lean4/pull/10607)、[#10677](https://github.com/leanprover/lean4/pull/10677)、...])

```lean
example (x y : Nat) : x ≥ y + 1 → x > 0 := by
  grind => skip; lia; done
```

交互模式配备了 _anchors_（也称稳定哈希码），用于引用 `grind` 目标中出现的术语（[#10709](https://github.com/leanprover/lean4/pull/10709)）。

在交互模式下,可以采取以下行动:

- `instantiate`全球和地方定理
[#10746](https://github.com/leanprover/lean4/pull/10746)和[#10841](https://github.com/leanprover/lean4/pull/10841));

- 检查`show_splits`和`show_state`([#10709](https://github.com/leanprover/lean4/pull/10709)),
`show_true`、`show_false`、`show_asserted`和`show_eqcs`
([#10690](https://github.com/leanprover/lean4/pull/10690));

- 检查过滤器;每种战术都可以有表格的后缀`| filter?`
([#10828](https://github.com/leanprover/lean4/pull/10828));

- 用 `have` 作出局部断言（[#10706](https://github.com/leanprover/lean4/pull/10706)）；

- 使用战术([#10731](https://github.com/leanprover/lean4/pull/10731)):

  - `focus <grind_tac_seq>`
  - `next => <grind_tac_seq>`
  - `any_goals <grind_tac_seq>`
  - `all_goals <grind_tac_seq>`
  - `grind_tac <;> grind_tac`
  - `cases <anchor>`
  - `tactic => <tac_seq>`

- 选择有 `cases?` 的锁定
([#10824](https://github.com/leanprover/lean4/pull/10824) - PR说明中有一个截图);

- 使用研磨求解器`ac`、`linarith`、`lia`、`ring`作为行动
[#10812](https://github.com/leanprover/lean4/pull/10812)和[#10834](https://github.com/leanprover/lean4/pull/10834)]);

- 在可能的情况下,利用明确的研磨策略,在可能的情况下,制作一个实际的研磨脚本,以结束目标
([#10837](https://github.com/leanprover/lean4/pull/10837)):

  ```lean
  /--
  info: Try this:
    [apply] ⏎
      cases #b0f4
      next => cases #50fc
      next => cases #50fc <;> lia
  -/
  #guard_msgs in
  example (p : Nat → Prop) (x y z w : Int) :
      (x = 1 ∨ x = 2) →
      (w = 1 ∨ w = 4) →
      (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
      (z = 1 ∨ z = 0) → x + y ≤ 6 := by
    grind => finish?
  ```

生成脚本中的锚以稳定的散列代码为基础 。
此外,用户可以盘旋在他们身上,查看案件所使用的确切术语。

````
### 非交换（半）环归一化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Non-commutative-_LPAR_semi_RPAR_ring-normalization"
%%%

````markdown

- [#10375](https://github.com/leanprover/lean4/pull/10375) 为 `grind` 增加了对非交换环归一化的支持。新的归一化器也会考虑 `IsCharP` 类型类。

  ```lean
  open Lean Grind

  variable (R : Type u) [Ring R]
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind

  variable [IsCharP R 4]
  example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
  ```

- [#10421](https://github.com/leanprover/lean4/pull/10421) 为 `grind` 增加了非交换半环的归一化器。

  ```lean
  open Lean.Grind
  variable (R : Type u) [Semiring R]

  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  ```

````
### 单射函数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Injective-functions"
%%%

````markdown

[#10445](https://github.com/leanprover/lean4/pull/10445),
[#10447](https://github.com/leanprover/lean4/pull/10447),
[#10482](https://github.com/leanprover/lean4/pull/10482),以及
[#10483](https://github.com/leanprover/lean4/pull/10483) 增加对研磨中注入功能的支持。

```lean
/-! 添加一些单射性定理。 -/

def double (x : Nat) := 2*x

@[grind inj] theorem double_inj : Function.Injective double := by
  grind [Function.Injective, double]

structure InjFn (α : Type) (β : Type) where
  f : α → β
  h : Function.Injective f

instance : CoeFun (InjFn α β) (fun _ => α → β) where
  coe s := s.f

@[grind inj] theorem fn_inj (F : InjFn α β) : Function.Injective (F : α → β) := by
  grind [Function.Injective, cases InjFn]

def toList (a : α) : List α := [a]

@[grind inj] theorem toList_inj : Function.Injective (toList : α → List α) := by
  grind [Function.Injective, toList]

/-! 示例 -/

example (x y : Nat) : toList (double x) = toList (double y) → x = y := by
  grind

example (f : InjFn (List Nat) α) (x y z : Nat)
    : f (toList (double x)) = f (toList y) →
      y = double z →
      x = z := by
  grind
```

````
### `grind order` 求解器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Grind-order-solver"
%%%

````markdown

磨磨现在可以解决预先订购和订购戒指的问题了
[#10562](https://github.com/leanprover/lean4/pull/10562)、[#10598](https://github.com/leanprover/lean4/pull/10598)和[#10600](https://github.com/leanprover/lean4/pull/10600)。
新的求解器`grind order`,支持`Nat`,并处理积极和消极的制约因素。

```lean
open Lean Grind
example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
    (a b c d : α) : a - b ≤ 5 → ¬ (c ≤ b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
  grind -linarith (splits := 0)
```

````
### 新的模式推断启发式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--New-pattern-inference-heuristic"
%%%

````markdown

[#10422](https://github.com/leanprover/lean4/pull/10422)和[#10432](https://github.com/leanprover/lean4/pull/10432)
执行新的电子匹配模式
`grind`。
新行为。

- `[grind =]`、`[grind =_]`、`[grind _=_]`、`[grind <-=]`:无变化;我们保留目前的行为。
- `[grind ->]`、`[grind <-]`、`[grind =>]`、`[grind <=]`:我们停止使用_最低可索引子表达式,而是使用第一个可索引式表达式。
- `[grind! <mod>]`:行为像`[grind <mod>]`],但使用最小可索引子表达式限制。如果用户写`[grind! =]`、`[grind! =_]`、`[grind! _=_]`或`[grind! <-=]`,则产生错误,因为这些情况下没有模式搜索。
- `[grind]`:它尝试`=`、`=_`、`<-`、`->`、`<=`、`=>`],但有且没有最低可索引子表达限制。对于起作用的,我们产生一个代码动作,鼓励用户选择他们喜欢的代码。
- `[grind!]`:它尝试`<-`、`->`、`<=`、`=>` 使用最低可索引子表达式限制。对于起作用的,我们生成代码动作,鼓励用户选择他们喜欢的代码。
- `[grind? <mod>]`:如果`<mod>`是上述修改者之一,其行为举止类似`[grind <mod>]`,但也显示模式。

示例:

```lean
/--
info: Try these:
  • [grind =] for pattern: [f (g #0)]
  • [grind =_] for pattern: [r #0 #0]
  • [grind! ←] for pattern: [g #0]
-/
#guard_msgs in
@[grind] axiom fg₇ : f (g x) = r x x
```

** 进口**:用户仍然可以使用旧模式的推断法。
通过设定:

```lean
set_option backward.grind.inferPattern true
```

````
## 规格定理派生
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Specifications-Derivation"
%%%

````markdown

Lean 现在为自定义和派生的类型类实例提供自动生成规格定理的能力：

- [#10302](https://github.com/leanprover/lean4/pull/10302) 引入`@[method_specs]`属性。可适用于
(某些)类别类型类别实例,并定义
通过采用该类的等式定理,
类型类例和类型
用超载操作来修改它们。 修补 [#5295](https://github.com/leanprover/lean4/issues/5295) 。

  ```lean
  inductive L α where
    | nil  : L α
    | cons : α → L α → L α

  def L.beqImpl [BEq α] : L α → L α → Bool
    | nil, nil           => true
    | cons x xs, cons y ys => x == y && L.beqImpl xs ys
    | _, _               => false

  @[method_specs] instance [BEq α] : BEq (L α) := ⟨L.beqImpl⟩

  /--
  info: theorem instBEqL.beq_spec_2.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (x_2 : α) (xs : L α) (y : α) (ys : L α),
    (L.cons x_2 xs == L.cons y ys) = (x_2 == y && xs == ys)
  -/
  #guard_msgs(pass trace, all) in
  #print sig instBEqL.beq_spec_2
  ```

- [#10346](https://github.com/leanprover/lean4/pull/10346) 使`deriving BEq`和`deriving Ord`使用`@[method_specs]`
[#10302](https://github.com/leanprover/lean4/pull/10302),酌情(即不使用`partial`))。

  ```lean
  inductive O (α : Type u) where
    | none
    | some : α → O α
  deriving BEq, Ord

  /--
  info: theorem instBEqO.beq_spec_2.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (a b : α), (O.some a == O.some b) = (a == b)
  -/
  #guard_msgs in #print sig instBEqO.beq_spec_2
  /--
  info: theorem instOrdO.compare_spec_2.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (x : O α),
    (x = O.none → False) → compare O.none x = Ordering.lt
  -/
  #guard_msgs in #print sig instOrdO.compare_spec_2
  ```

- [#10351](https://github.com/leanprover/lean4/pull/10351) 增加了 `deriving ReflBEq, LawfulBEq` 的能力。这两个类都必须列在 `deriving` 子句中。它原本是为了配合 `deriving BEq` 使用的（不过你也可以尝试把它用于手写的 `@[methods_specs] instance : BEq…` 实例）。不支持互递归或嵌套归纳类型。

````
## `String` 类型重构
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Overhaul-of-the-String-Type"
%%%

````markdown

- [#10304](https://github.com/leanprover/lean4/pull/10304) 将`String` 重新定义为字节数组的类型`b`
`b.IsValidUtf8`。这将字符串的数据模型更接近运行时的实际数据表示。

- [#10457](https://github.com/leanprover/lean4/pull/10457)对`String.Pos`和`Substring`引入安全替代品
只能代表有效立场/偏差。

  - 引入上游`String.Pos.IsValid`;
  - 证明`String.Pos.IsValid` 有几个非三等条件;
  - 引入`String.ValidPos`,即`String.Pos`的`IsValid` 证明;
  - 采用`String.Slice`,它类似`Substring`,但由`String.ValidPos`制成,而不是`Pos`制成;
  - 引入`String.Pos.IsValidForSlice`,它类似`String.Pos.IsValid`,但切片除外;
  - 引入`String.Slice.Pos`,它类似`String.ValidPos`,但切片除外;
  - 引入了两种职位之间转换的各种功能。

- [#10514](https://github.com/leanprover/lean4/pull/10514) 定义新的`String.Slice` API。

- [#10713](https://github.com/leanprover/lean4/pull/10713) 强化了关于 `String.Pos.Raw` 算术的规则。

  **破坏性变更：** `String.Pos.Raw` 的 `HAdd` 和 `HSub` 实例已被移除。更多信息见 PR 说明。
详情请见PR说明。

- [#10735](https://github.com/leanprover/lean4/pull/10735)将许多`String.Pos.Raw`业务转移至`String.Pos.Raw`
`String.Pos.Raw` 命名空间。

** 打破变化**:在本PR之后,`String.pos_lt_eq`不再为`simp` 列马。
如果证明破损,添加`String.Pos.Raw.lt_iff`,作为`simp` 列马。

````
## 异步框架
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Async-Framework"
%%%

````markdown

扩大了Async框架,包括:

- POSIX 信号处理器([#9258](https://github.com/leanprover/lean4/pull/9258));
- `Std.Sync.Notify`，适用于并发场景、可替代 `CondVar` 的一种结构（[#10368](https://github.com/leanprover/lean4/pull/10368)）；
- `Std.Broadcast`，加入到 `Std.Sync` 的多消费者、多生产者通道（[#10369](https://github.com/leanprover/lean4/pull/10369)）；
- `StreamMap`，一种可在异步流中实现多路复用的类型（[#10400](https://github.com/leanprover/lean4/pull/10400)）；
- `Std.CancellationToken` ([#10510](https://github.com/leanprover/lean4/pull/10510))。

````
## 迭代器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Iterators"
%%%

````markdown

- [#10686](https://github.com/leanprover/lean4/pull/10686) 采用`any`、`anyM`、`all`和`allM`
还会为它们提供润滑剂

- [#10728](https://github.com/leanprover/lean4/pull/10728) 引入 `flatMap` 迭代器组合器。它还添加了
`flatMap`至`toList`和`toArray`。

- [#10761](https://github.com/leanprover/lean4/pull/10761) 为哈希映射提供了迭代器。

````
## InfoView Trace 搜索
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--InfoView-Trace-Search"
%%%

````markdown

[#10365](https://github.com/leanprover/lean4/pull/10365) 执行服务器侧的服务器侧,以在
InfoView。 演示视频请参见 PR 描述 。

````
## 实例的线性构造
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Linear-Construction-of-Instances"
%%%

````markdown

现在提供了 `DerivingBEq`（[#10268](https://github.com/leanprover/lean4/pull/10268)）和 `Deriving Ord`（[#10270](https://github.com/leanprover/lean4/pull/10270)）的替代实现：它们基于比较 `.ctorIdx`，并使用专门的匹配器来比较相同构造子（该匹配器在 [#10152](https://github.com/leanprover/lean4/pull/10152) 中加入），以避免默认匹配实现的二次开销。新的选项 `deriving.beq.linear_construction_threshold` 和 `deriving.ord.linear_construction_threshold` 用来设置采用这一新构造的构造子数量阈值（默认值为 10）。

````
## 迁移到模块系统
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Porting-to-the-Module-System"
%%%

````markdown

[#10807](https://github.com/leanprover/lean4/pull/10807) 采用`backward.privateInPublic` 备选办法援助`backward.privateInPublic`
通过临时允许进入模块系统,将项目移植到模块系统
从公共范围,甚至从各个单元,公开发表私人声明。
此类存取器将生成警告警告,除非
`backward.privateInPublic.warn` 已禁用。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Breaking-Changes"
%%%

````markdown

- [#10714](https://github.com/leanprover/lean4/pull/10714) 删除了对可约良基递归的支持，这是一个破坏性变更。在通过良基递归定义的定义上使用 `@[semireducible]` 会打印警告，提示它已不再生效。

- [#10319](https://github.com/leanprover/lean4/pull/10319) 将结构 `Std.PRange shape α` “单态化”，用九个不同的结构 `Std.Rcc`、`Std.Rco`、`Std.Rci` 等替换它，每个结构对应一种可能的区间边界形状。这项变更是必要的，因为形状多态性不利于自动化尝试。

  **破坏性变更：** 虽然区间/切片记号本身没有变化，但除点记法（`toList`、`iter` 等）外，这实际上打破了剩余的整个（多态）区间与切片 API。由于旧声明依赖一种现已不存在的形状多态写法，因此无法对它们做弃用过渡。

- [#10645](https://github.com/leanprover/lean4/pull/10645) 将`Stream`改名为`Std.Stream`,使名称成为
在折旧周期后,数学流可用。

- [#10468](https://github.com/leanprover/lean4/pull/10468) 重构Lake对数山采用`LogConfig` 结构
当运行时( 而不是多个参数) 。 此断开更改应该
帮助最小化由于配置选项改变而导致的未来断裂。

- [#10660](https://github.com/leanprover/lean4/pull/10660) 在 `end` 之后为标识符添加了自动补全。它还修复了一个错误：在 `set_option` 后的空白处补全时，无法给出完整的选项列表。

断开更改:调整`«end»` 语法以取一个`identWithPartialTrailingDot`,而不是取一个`ident`。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Language"
%%%

````markdown

* [#7844](https://github.com/leanprover/lean4/pull/7844) 添加一个简单的执行MEPO的简单内容,来自“轻重量”
用于机器产生的解析问题的关联过滤”由Meng著
还有保尔森

* [#10158](https://github.com/leanprover/lean4/pull/10158) 补充关于无法通过
输入 defeq 错误的模块系统 。

* [#10268](https://github.com/leanprover/lean4/pull/10268) 为 `DerivingBEq` 添加了另一种实现：它基于比较 `.ctorIdx`，并使用专门的匹配器来比较相同构造子（见 #10152），以避免默认匹配实现的二次开销。新的选项 `deriving.beq.linear_construction_threshold` 用来设置采用这一新构造的构造子数量阈值（默认值为 10）。这类实例也允许 `deriving ReflBEq, LawfulBeq`，不过这些性质的证明目前仍是二次复杂度的。

* [#10270](https://github.com/leanprover/lean4/pull/10270) 为 `Deriving Ord` 添加了另一种实现：它基于比较 `.ctorIdx`，并使用专门的匹配器来比较相同构造子（见 #10152）。新的选项 `deriving.ord.linear_construction_threshold` 用来设置采用这一新构造的构造子数量阈值（默认值为 10）。

* [#10302](https://github.com/leanprover/lean4/pull/10302) 引入了 `@[specs]` 属性。它可以应用到（某些）类型类实例上，通过提取该类型类实例中所引用实现函数的等式定理，并将其改写成以重载操作表达的形式，为该类的操作定义“规格定理”。修复了 #5295。

* [#10333](https://github.com/leanprover/lean4/pull/10333) 引入了 `coinductive` 关键字，可用与 `inductive` 关键字相同的语法来定义余归纳谓词。这套机制依赖归纳类型精化的实现，并从定义中提取谓词所在适当空间上的一个自映射，再将其交给 `PartialFixpoint`。在精化这些定义时，所有构造子都会通过自动生成的引理来声明。

* [#10346](https://github.com/leanprover/lean4/pull/10346) 使`deriving BEq`和`deriving Ord`使用`@[method_specs]`
酌情取自#10302(即未使用`partial`)。

* [#10351](https://github.com/leanprover/lean4/pull/10351) 增加了 `deriving ReflBEq, LawfulBEq` 的能力。这两个类都必须列在 `deriving` 子句中。对于 `ReflBEq`，使用基于 `simp` 的简单证明。对于 `LawfulBEq`，使用专门的、按语法引导的策略，它应当能适用于派生得到的 `BEq` 实例。它原本是为了配合 `deriving BEq` 使用的（不过你也可以尝试把它用于手写的 `@[methods_specs] instance : BEq…` 实例）。不支持互递归或嵌套归纳类型。

* [#10375](https://github.com/leanprover/lean4/pull/10375) 为 `grind` 增加了对非交换环归一化的支持。新的归一化器也会考虑 `IsCharP` 类型类。示例：
  ```lean
  open Lean Grind

  variable (R : Type u) [Ring R]
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-4) * a - 2*b*a + 4 * b^2 := by grind

  variable [IsCharP R 4]
  example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
  example (a b : R) : (a - b)^2 = 13*a^2 - a * b - b * 5 * a + b*3*b*3 := by grind
  ```

* [#10377](https://github.com/leanprover/lean4/pull/10377) 修复了一个问题：app elaborator 中的“eta feature”会在因命名参数而跳过位置参数时被触发，并可能生成会被这些命名参数捕获的变量。现在，实现该特性的临时局部变量会获得新鲜名字。闭合 lambda 表达式所用的名字仍然使用原始参数名。

* [#10378](https://github.com/leanprover/lean4/pull/10378) 允许在 `infix` / `infixl` / `infixr` / `prefix` / `postfix` 中使用 `notation` 项。这样做的动机是允许使用感知 `pp.unicode` 的解析器。后续 PR 可以按如下方式组合核心解析器：
  ```lean
  infixr:30 unicode(" ∨ ", " \\/ ") => Or
  ```

* [#10379](https://github.com/leanprover/lean4/pull/10379) 修改了策略配置的语法。此前仅仅写 `(ident` 就会提交到策略配置项解析，而现在必须写成 `(ident :=`。这使得在 `term` 类别之前可靠地使用策略配置成为可能。例如，给定 `syntax "my_tac" optConfig term : tactic`，过去 `my_tac (x + y)` 会在 `+` 处报出“expected `:=`”，而现在它会正确地把后面的内容解析为项。

* [#10380](https://github.com/leanprover/lean4/pull/10380) 在 `grind ring` 模块中实现了健全性检查，以确保类型类解析合成出的实例在定义上等于 `grind` 核心类中的相应实例。进行定义相等性测试时，归约仅限于可约定义和实例。

* [#10382](https://github.com/leanprover/lean4/pull/10382) 使内置的 Verso docstring elaborator 能够正确自举，新增了延后检查的能力（这对于解析前向引用和解决自举问题是必需的），并修复了一个轻微的 parser 错误。

* [#10388](https://github.com/leanprover/lean4/pull/10388) 修复了一个错误：如果某个定义中的嵌套证明含有 `sorry`，且该证明与前一个声明中的另一个嵌套证明具有相同类型，则它可能不会报告 “warning: declaration uses 'sorry'”。该错误只影响日志消息；`#print axioms` 仍会正确报告 `sorryAx` 的使用。

* [#10391](https://github.com/leanprover/lean4/pull/10391) 为匿名构造子记号（`⟨x,y⟩`）加入了错误恢复机制：如果参数不足，就会为缺失参数插入 synthetic sorries 并记录一条错误，而不是直接失败。

* [#10392](https://github.com/leanprover/lean4/pull/10392) 修复了 `if` 策略中的一个问题：错误不会放到正确的源码范围上。它还加入了一些错误恢复，以避免在策略语法不完整时，在 `if` 标记上额外报出关于未解决目标的错误。

* [#10394](https://github.com/leanprover/lean4/pull/10394) 添加了 `reduceBEq` 和 `reduceOrd` simproc。若两个参数都是构造子，且相应实例已标记为 `@[method_specs]`（见 #10302；现在对派生实例默认如此），它们就会分别改写 `_ == _` 和 `Ord.compare _ _` 的出现位置。

* [#10406](https://github.com/leanprover/lean4/pull/10406) 在 #10302 的基础上进一步改进：当实现函数未暴露时，能正确地把 method spec 定理设为 private。

* [#10415](https://github.com/leanprover/lean4/pull/10415) 修改了为结构递归证明方程定理时尝试的步骤顺序。为了避免产生 `split` 无法处理的目标，在 RHS 尚未拆成最终分支前，不再把方程 LHS 展开到 `.brecOn` 和 `.rec`。

* [#10417](https://github.com/leanprover/lean4/pull/10417) 修改了 `deriving_LawfulEq_tactic_step` 中的自动化：在用 `change` 断言目标形状时改用 `with_reducible`，从而避免在这里意外展开 `x == x'` 调用。修复了 #10416。

* [#10419](https://github.com/leanprover/lean4/pull/10419) 添加了辅助定理 `eq_normS_nc`，用于归一化非交换半环。我们将用它来为 `grind ring` 模块中的归一化步骤提供依据。

* [#10421](https://github.com/leanprover/lean4/pull/10421) 为 `grind` 增加了非交换半环的归一化器。示例：
  ```lean
  open Lean.Grind
  variable (R : Type u) [Semiring R]

  example (a b c : R) : a * (b + c) = a * c + a * b := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * (1+1) * a * 1 + 5 * b^2 := by grind
  example (a b : R) : a^3 + a^2*b + a*b*a + b*a^2 + a*b^2 + b*a*b + b^2*a + b^3 = (a+b)^3 := by grind
  ```

* [#10422](https://github.com/leanprover/lean4/pull/10422) 为 `grind` 实现了新的 E-matching 模式推断启发式。它目前尚未启用。你可以使用 `set_option backward.grind.inferPattern false` 来启用这一新行为。下面是对新行为的摘要。

* [#10425](https://github.com/leanprover/lean4/pull/10425) 允许 `split` 策略用 `generalize` 来泛化那些不是自由变量、也不是证明的判别式。若唯一的非 fvar 判别式都是证明，那么这样可以避免 `split` 更复杂的泛化策略；后者在依赖动机下可能失败，从而缓解了 #10424。

* [#10428](https://github.com/leanprover/lean4/pull/10428) 使缺失的 `grind` 修饰符显式化，并确保 `grind` 对局部定理使用 “minIndexable”。

* [#10430](https://github.com/leanprover/lean4/pull/10430) 确保用户可以在 `grind` 参数中选择“最小可索引子表达式”条件。例如，他们现在可以写 `grind [! -> thmName]`。`grind?` 会在用户使用过 `@[grind!]` 时包含 `!` 修饰符。该 PR 还修复了新模式推断过程中的一个缺失分支，并调整了一些 `grind` 标注和测试，为将新的模式推断启发式设为默认值做准备。

* [#10432](https://github.com/leanprover/lean4/pull/10432) 使新的电子对齐模式的推导法
`grind`,在PR#10422中执行。
** 进口**:用户仍然可以使用旧模式的推断法。
通过设定:

  ```lean
  set_option backward.grind.inferPattern true
  ```

* [#10434](https://github.com/leanprover/lean4/pull/10434) 加`reprove N by T`,该`reprove N by T`有效阐述了`例如
N 类型类型%%% N:= by T' =。它支持多个标识符。这有用
测试战术。

* [#10438](https://github.com/leanprover/lean4/pull/10438) 确定一个问题,说明和其他超载问题
即使存在成功的信号内核错误, 信号内核错误
解释。

* [#10440](https://github.com/leanprover/lean4/pull/10440)增加`reduceCtorIdx` 承认和减少的`reduceCtorIdx`
`ctorIdx` 应用程序。 这一点尚未默认, 因为它确实存在
不使用歧视树(尚未使用)。

* [#10453](https://github.com/leanprover/lean4/pull/10453) 通过`let` 进行`mvcgen` 减少`mvcgen`
`(have t := 42; fun _ => foo t) 23` 减为`有:=42; foo
t` and then introducing `t`。

* [#10456](https://github.com/leanprover/lean4/pull/10456) 执行`mvcgen invariants?`,提供初始变量
供用户使用。 当循环体早于时 。
本会议将建议`Invariant.withEarlyReturn ...`作为
骨骼。

* [#10479](https://github.com/leanprover/lean4/pull/10479) 实现了 Verso 语法的模块 docstring，并为 Verso docstring 整体加入了多项改进和修复。特别是，它们现在获得了语言服务器支持，并且会在解析阶段而不是精化阶段完成解析，因此快照的语法树会包含解析后的文档。

* [#10506](https://github.com/leanprover/lean4/pull/10506) 注意到`bv_decide` 的影子主要定义,
`mvcgen` 和`Std` 与较富裕的语义中的类似战术
`tactic_alt` 属性,以便`verso` 不警告超载。

* [#10507](https://github.com/leanprover/lean4/pull/10507) 使失踪的医生能够知道`tactic_alt` 。

* [#10508](https://github.com/leanprover/lean4/pull/10508) 允许不仅为`.congr_simp`
这对建立这个机制很重要。
跨模块边界的工作。

* [#10512](https://github.com/leanprover/lean4/pull/10512)为前期选择 API增加一些辅助功能,以便
协助执行者。

* [#10533](https://github.com/leanprover/lean4/pull/10533)为模块名称添加一个划线作用,称为`module`。
改进为守则要素提供的建议,使其更完善
并提议`lit`。

* [#10535](https://github.com/leanprover/lean4/pull/10535)确保`#guard`可调用模块系统下的`#guard`
没有任何问题。

* [#10536](https://github.com/leanprover/lean4/pull/10536) 用`-zeta -zetaUnused` 方式固定`simp`
如果在 `have` 望远镜中的变量发生于
仅中转的体型类型 。 固定 # 10353 。

* [#10543](https://github.com/leanprover/lean4/pull/10543)]让我们`#print T.rec`显示更多关于递归器的信息,以
特别是其削减规则。

* [#10560](https://github.com/leanprover/lean4/pull/10560) 将突出的利值代码添加到 Verso 码和小修
生活质量问题。

* [#10563](https://github.com/leanprover/lean4/pull/10563) 将一些关于基本类型的 `ReduceEval` 实例从 `quote4` 库提升到了上层。

* [#10566](https://github.com/leanprover/lean4/pull/10566) 改进了 `mvcgen invariants?`，使其可根据不变式在 VC 中的使用方式建议具体不变式。这些建议是刻意保持简单的，基本可以概括为：
循环起始处的挂着点, 且此挂着点必须保持在循环的结尾处
循环 :

  ```lean
  def mySum (l : List Nat) : Nat := Id.run do
    let mut acc := 0
    for x in l do
      acc := acc + x
    return acc

  /--
  info: Try this:
    invariants
      · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
  -/
  #guard_msgs (info) in
  theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
    generalize h : mySum l = r
    apply Id.of_wp_run_eq h
    mvcgen invariants?
    all_goals admit
  ```

* [#10567](https://github.com/leanprover/lean4/pull/10567) 将参数指数计算固定在`Lean.Expr.getArg!'`。

* [#10570](https://github.com/leanprover/lean4/pull/10570) 在 `mvcgen invariants` 中增加对像语法一样的立体标签的支持 `mvcgen invariants`
以引用不可访问的名称。 例如 :

  ```lean
  def copy (l : List Nat) : Id (Array Nat) := do
    let mut acc := #[]
    for x in l do
      acc := acc.push x
    return acc

  theorem copy_labelled_invariants (l : List Nat) : ⦃⌜True⌝⦄ copy l ⦃⇓ r => ⌜r = l.toArray⌝⦄ := by
    mvcgen [copy] invariants
    | inv1 acc => ⇓ ⟨xs, letMuts⟩ => ⌜acc = l.toArray⌝
    with admit
  ```

* [#10571](https://github.com/leanprover/lean4/pull/10571) 确保`SPred` 验证模式战术,如`mspec`,
`mintro`等,在输入证明时立即替换主要目标
模式。此模式防止 `No goals to be solved` 错误。

* [#10612](https://github.com/leanprover/lean4/pull/10612) 修复了[Zulip](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/.60abstractMVars.60.20not.20instantiating.20level.20mvars/near/541918246) 上报告的问题：`abstractMVars`（用于类型类推断和 `simp` 参数精化）不会实例化 metavariable 的类型中的 metavariable，导致它会把已经赋值的 metavariable 也抽象掉。

* [#10618](https://github.com/leanprover/lean4/pull/10618) 从 `MonadExceptOf` 提升框架的规格引理中移除了多余的 `Monad` 实例。

* [#10638](https://github.com/leanprover/lean4/pull/10638) 更改`mvcgen` 的“实验性”警告,从而禁用其“实验性”警告 `mvcgen`
默认。

* [#10639](https://github.com/leanprover/lean4/pull/10639) 使当地环境卫生符合
`mvcgen`,不只是那些得到一个新的MVAR像9781年那样。

* [#10641](https://github.com/leanprover/lean4/pull/10641) 确保`mspec`和`mvcgen`战术不再
由`rfl` 产生的具有虚假动机的即时循环变异。

* [#10644](https://github.com/leanprover/lean4/pull/10644) 明确试图在`mspec`中合成机动车辆合成合成。
从而解决一个因使用循环变异性 Lemma 来触发的错误。
`Std.PRange`。

* [#10650](https://github.com/leanprover/lean4/pull/10650)当目标不是目标时改进 `mstart` 的错误信息
`Prop`。

* [#10654](https://github.com/leanprover/lean4/pull/10654) 避免在方程定理方面完全减少透明度
修复10651。

* [#10663](https://github.com/leanprover/lean4/pull/10663) 禁用`{name}`关于`.anonymous`的建议,并添加语法
建议。

* [#10682](https://github.com/leanprover/lean4/pull/10682)更改 `deriving ToExpr` 的示例名称,以保持一致
自#10271以来, 其它衍生实例。 fixs# 10678 。

* [#10697](https://github.com/leanprover/lean4/pull/10697))如果在[`induction`
`using` 条款是普遍性的,固定了10683号。

* [#10712](https://github.com/leanprover/lean4/pull/10712)让我们追寻当地的声明(有点像它们
(b) 确定:#10710。

* [#10714](https://github.com/leanprover/lean4/pull/10714) 删除了对可约良基递归的支持，这是一个破坏性变更。在通过良基递归定义的定义上使用 `@[semireducible]` 会打印警告，提示它已不再生效。

* [#10716](https://github.com/leanprover/lean4/pull/10716) 添加了一个新的辅助解析器，用于实现包含十六进制数字的解析器。我们将用它来在 `grind` 交互模式中实现 anchors。

* [#10720](https://github.com/leanprover/lean4/pull/10720) 通过改回默认值，重新启用了 `mvcgen` 的“experimental”警告。为便于在不久的将来对语义基础做小的破坏性调整，正式发布已被推迟。

* [#10722](https://github.com/leanprover/lean4/pull/10722) 更改了在尝试把 `coinductive` 关键字用于不居于 `Prop` 的目标时的报错位置。错误现在会显示在出错定义上方，而不是互递归块第一个元素的上方。

* [#10733](https://github.com/leanprover/lean4/pull/10733) 在终止性检查期间更积极地展开辅助定理。修复了 #10721。

* [#10734](https://github.com/leanprover/lean4/pull/10734) 承接 #10606，统一从 unfold theorem 创建方程定理，因此 `registerGetEqnsFn` 中只需注册一个处理器。

* [#10780](https://github.com/leanprover/lean4/pull/10780) 改进了 `decide +kernel` 在内核中失败但在 elaborator 中不失败时的错误信息。修复了 #10766。

* [#10782](https://github.com/leanprover/lean4/pull/10782) 实现了提示策略 `mvcgen?`，它会展开为 `mvcgen invariants?`

* [#10783](https://github.com/leanprover/lean4/pull/10783) 确保诸如 “redundant alternative” 之类的错误消息即使在各分支共享 RHS 时也具有正确的错误位置。修复了 #10781。

* [#10793](https://github.com/leanprover/lean4/pull/10793) 修复#10792。

* [#10796](https://github.com/leanprover/lean4/pull/10796) 修改了 match compilation，会拒绝某些此前由于 inaccessible pattern 有时被当成 accessible pattern 而被接受的模式匹配。修复了 #10794。

* [#10807](https://github.com/leanprover/lean4/pull/10807) 引入了 `backward.privateInPublic` 选项，以帮助项目迁移到模块系统：它会临时允许从公共作用域访问 private 声明，甚至允许跨模块访问。除非禁用 `backward.privateInPublic.warn`，否则此类访问会产生警告。

* [#10839](https://github.com/leanprover/lean4/pull/10839) 暴露了用于实现 `set_option` 记号的 `optionValue` 解析器。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Library"
%%%

````markdown

* [#9258](https://github.com/leanprover/lean4/pull/9258) 向利恩标准库增加对信号处理器的支持。

* [#9298](https://github.com/leanprover/lean4/pull/9298) 为位向量库以及 `bv_decide` 增加了对尾随零计数操作 `BitVec.ctz` 的支持，并依赖已有的 `clz` 电路。我们也围绕 `BitVec.ctz` 构建了一些理论（与 `BitVec.clz` 已有的理论类似），并引入了引理 `BitVec.[ctz_eq_reverse_clz, clz_eq_reverse_ctz, ctz_lt_iff_ne_zero, getLsbD_false_of_lt_ctz, getLsbD_true_ctz_of_ne_zero, two_pow_ctz_le_toNat_of_ne_zero, reverse_reverse_eq, reverse_eq_zero_iff]`。

* [#9932](https://github.com/leanprover/lean4/pull/9932) 为 `Option` 和 `OptionT` 添加了 `LawfulMonad` 与 `WPMonad` 实例。

* [#10304](https://github.com/leanprover/lean4/pull/10304) 将 `String` 重新定义为满足 `b.IsValidUtf8` 的字节数组 `b` 的类型。

* [#10319](https://github.com/leanprover/lean4/pull/10319) 将结构 `Std.PRange shape α` “单态化”，用九个不同的结构 `Std.Rcc`、`Std.Rco`、`Std.Rci` 等替换它，每个结构对应一种可能的区间边界形状。这项变更是必要的，因为形状多态性不利于自动化尝试。

* [#10366](https://github.com/leanprover/lean4/pull/10366) 重构了 Async 模块，使所有 `Async` 文件都使用 `Async` 类型。

* [#10367](https://github.com/leanprover/lean4/pull/10367) 为 TCP 和 UDP 添加了 vectored write（这大大减少了反复复制数组），并修复了 TCP 与 UDP cancel 函数中的一个 RC 问题，涉及 `lean_dec((lean_object*)udp_socket);` 这一行，以及一个类似的、试图递减 `socket` 内部对象的语句。

* [#10368](https://github.com/leanprover/lean4/pull/10368) 添加了 `Notify`，这是一个类似 `CondVar` 的结构，但用于并发。`Std.Sync.Notify` 与 `Std.Condvar` 的主要区别在于后者依赖 `Std.Mutex`，并且在等待时会阻塞 `Task` 所使用的整个线程。

* [#10369](https://github.com/leanprover/lean4/pull/10369) 向 `Std.Sync` 添加了多消费者、多生产者通道。

* [#10370](https://github.com/leanprover/lean4/pull/10370) 为流添加了异步类型类。

* [#10400](https://github.com/leanprover/lean4/pull/10400) 添加了 `StreamMap` 类型，使异步流能够进行多路复用。

* [#10407](https://github.com/leanprover/lean4/pull/10407) 在 `Init` 中为 `HAppend` 之类的类型类添加了 `@[method_specs_simp]`。

* [#10457](https://github.com/leanprover/lean4/pull/10457) 为 `String.Pos` 和 `Substring` 引入了安全替代类型，它们只能表示有效的位置/切片。

* [#10487](https://github.com/leanprover/lean4/pull/10487) 为 tcp 和 udp cancel 函数添加了 vectored write，并修复了 rc 问题。

* [#10510](https://github.com/leanprover/lean4/pull/10510) 添加了 `Std.CancellationToken` 类型。

* [#10514](https://github.com/leanprover/lean4/pull/10514) 定义了新的 `String.Slice` API。

* [#10552](https://github.com/leanprover/lean4/pull/10552) 确保 `Substring.beq` 具有自反性，尤其满足等价式 `ss1 == ss2 <-> ss1.toString = ss2.toString`。

* [#10611](https://github.com/leanprover/lean4/pull/10611) 为 `DHashMap` / `HashMap` / `HashSet` 及其 raw 变体添加了 union 操作，并给出了有关 union 操作的引理。

* [#10618](https://github.com/leanprover/lean4/pull/10618) 从 `MonadExceptOf` 提升框架的规格引理中移除了多余的 `Monad` 实例。

* [#10624](https://github.com/leanprover/lean4/pull/10624) 将 `String.Pos` 重命名为 `String.Pos.Raw`。

* [#10627](https://github.com/leanprover/lean4/pull/10627) 添加了引理 `forall_fin_zero` 和 `exists_fin_zero`。它还为 `forall_fin_zero`、`forall_fin_one`、`forall_fin_two`、`exists_fin_zero`、`exists_fin_one`、`exists_fin_two` 添加了 `simp` 属性。

* [#10630](https://github.com/leanprover/lean4/pull/10630) 旨在修复 Timer API 的 selector，使其在注销后尽快结束。这项改动让 `Selectable.one` 函数尽快释放 `selectables` 数组，因此与带有某些副作用的 finalizer（例如 TCP socket finalizer）组合时，也会尽快运行它。

* [#10631](https://github.com/leanprover/lean4/pull/10631) 暴露了有关 `Int*` 的定义。这样做的主要原因是 `SInt` simproc 需要暴露其中许多定义。此外，`decide` 现在也能处理 `Int*` 操作。修复了 #10631。

* [#10633](https://github.com/leanprover/lean4/pull/10633) 为有符号有限数类型 `Int{8,16,32,64}` 和 `ISize` 提供了 range 支持。相关证明义务通过把它们全部归约为关于内部 `UpwardEnumerable` 实例的证明来处理，其中 `BitVec` 被解释为有符号数。

* [#10634](https://github.com/leanprover/lean4/pull/10634) 定义了 `ByteArray.validateUTF8`，并用它证明 `ByteArray.IsValidUtf8` 是可判定的，同时将 `String.fromUTF8` 及相关函数重定义为使用它。

* [#10636](https://github.com/leanprover/lean4/pull/10636) 将 `String.getUtf8Byte` 重命名为 `String.getUTF8Byte`，以遵循标准库命名约定。

* [#10642](https://github.com/leanprover/lean4/pull/10642) 引入 `List.Cursor.pos` 作为 `prefix.length` 的缩写。

* [#10645](https://github.com/leanprover/lean4/pull/10645) 将 `Stream` 重命名为 `Std.Stream`，以便在经历弃用周期后把该名称留给 mathlib。

* [#10649](https://github.com/leanprover/lean4/pull/10649) 将 `Nat.and_distrib_right` 重命名为 `Nat.and_or_distrib_right`。这是为了让名称与同一文件中的其他定理保持一致（例如 `Nat.and_or_distrib_left`）。

* [#10653](https://github.com/leanprover/lean4/pull/10653) 为（过滤）映射后再折叠的迭代器添加了方程引理。

* [#10667](https://github.com/leanprover/lean4/pull/10667) 为 TCP 和 Signals 添加了更多 selector。

* [#10676](https://github.com/leanprover/lean4/pull/10676) 添加了 `IO.FS.hardLink` 函数，可用于创建硬链接。

* [#10685](https://github.com/leanprover/lean4/pull/10685) 为 `String.ValidPos` 和 `String.Slice.Pos` 引入了 `LT` 与 `LE` 实例。

* [#10686](https://github.com/leanprover/lean4/pull/10686) 为纯迭代器和 monadic 迭代器引入了 `any`、`anyM`、`all` 和 `allM`，并给出了相关引理。

* [#10713](https://github.com/leanprover/lean4/pull/10713) 强化了关于 `String.Pos.Raw` 算术的规则。

* [#10728](https://github.com/leanprover/lean4/pull/10728) 引入了 `flatMap` 迭代器组合子。它还添加了把 `flatMap` 与 `toList` 和 `toArray` 联系起来的引理。

* [#10735](https://github.com/leanprover/lean4/pull/10735) 将许多涉及 `String.Pos.Raw` 的操作移入 `String.Pos.Raw` 命名空间，最终目标是腾出 `String` 命名空间，用于容纳使用 `String.ValidPos`（之后将重命名为 `String.Pos`）的操作。

* [#10761](https://github.com/leanprover/lean4/pull/10761) 为哈希映射提供了迭代器。

````
# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Tactics"
%%%

````markdown

* [#10445](https://github.com/leanprover/lean4/pull/10445) 添加了辅助定义，为即将在 `grind` 中加入的单射函数支持做准备。

* [#10447](https://github.com/leanprover/lean4/pull/10447) 添加了 `[grind inj]` 属性，用于为 `grind` 标记单射性定理。

* [#10448](https://github.com/leanprover/lean4/pull/10448) 修改了 `grind` 中 “issues” 诊断的输出。此前它只会描述合成失败；这对用户来说很容易造成困惑，因为实际上 linarith 模块仍然会继续工作，只是能力有所下降。对于大多数问题，它现在会解释由此带来的行为变化。不过，对于 `IsOrderedRing` 不可用时的变化，仍有待进一步说明。

* [#10449](https://github.com/leanprover/lean4/pull/10449) 确保 E-matching 模块报告的问题只会在启用 `set_option grind.debug true` 时显示。用户反馈这些信息过于分散注意力且帮助不大；它们对给库打注解的库开发者更有价值。

* [#10461](https://github.com/leanprover/lean4/pull/10461) 修复了 `grind mbtc` 模块产生不必要 case split 的问题。这里的 `mbtc` 指的是 model-based theory combination。

* [#10463](https://github.com/leanprover/lean4/pull/10463) 将 `Nat.sub_zero` 加入 `grind` 的归一化规则。

* [#10465](https://github.com/leanprover/lean4/pull/10465) 在 `grind mbtc` 期间跳过类似强制转换的辅助 `grind` 函数。

* [#10466](https://github.com/leanprover/lean4/pull/10466) 减少了 `grind` 诊断中 “Equivalence classes” 一节的噪音。它现在使用 *support expressions* 的概念。目前这是硬编码的，但将来很可能会做成可扩展形式。当前定义如下：

* [#10469](https://github.com/leanprover/lean4/pull/10469) 修复了 `grind` canonicalizer 中一处不正确的优化。可参见新增测试中暴露该问题的示例。

* [#10472](https://github.com/leanprover/lean4/pull/10472) 为 `grind` 参数添加了代码动作。要启用该选项，需要使用 `set_option grind.param.codeAction true`。该 PR 还添加了一个修饰符，用于指示 `grind` 使用 “default” 模式推断策略。

* [#10473](https://github.com/leanprover/lean4/pull/10473) 确保 `grind` 产生的代码动作消息包含完整上下文。

* [#10474](https://github.com/leanprover/lean4/pull/10474) 为 `grind` 中 `!` 参数修饰符添加了文档字符串。

* [#10477](https://github.com/leanprover/lean4/pull/10477) 确保 `grind` 会把 sort 内化。

* [#10480](https://github.com/leanprover/lean4/pull/10480) 修复了 `grind` 中使用的 equality resolution 前端中的错误。

* [#10481](https://github.com/leanprover/lean4/pull/10481) 泛化了 `grind` 中使用的定理激活函数，目标是复用它来实现单射函数模块。

* [#10482](https://github.com/leanprover/lean4/pull/10482) 修复了 `@[grind inj]` 属性的符号收集。

* [#10483](https://github.com/leanprover/lean4/pull/10483) 完成了 `grind` 中对单射函数的支持。示例：
  ```lean
  /-! Add some injectivity theorems. -/

  def double (x : Nat) := 2*x

  @[grind inj] theorem double_inj : Function.Injective double := by
    grind [Function.Injective, double]

  structure InjFn (α : Type) (β : Type) where
    f : α → β
    h : Function.Injective f

  instance : CoeFun (InjFn α β) (fun _ => α → β) where
    coe s := s.f

  @[grind inj] theorem fn_inj (F : InjFn α β) : Function.Injective (F : α → β) := by
    grind [Function.Injective, cases InjFn]

  def toList (a : α) : List α := [a]

  @[grind inj] theorem toList_inj : Function.Injective (toList : α → List α) := by
    grind [Function.Injective, toList]

  /-! Examples -/

  example (x y : Nat) : toList (double x) = toList (double y) → x = y := by
    grind

  example (f : InjFn (List Nat) α) (x y z : Nat)
      : f (toList (double x)) = f (toList y) →
        y = double z →
        x = z := by
    grind
  ```

* [#10486](https://github.com/leanprover/lean4/pull/10486) 增补并扩展了与 `grind` 相关的文档字符串。

* [#10529](https://github.com/leanprover/lean4/pull/10529) 为即将到来的 `grind order` 求解器添加了一些辅助定理。

* [#10553](https://github.com/leanprover/lean4/pull/10553) 为新的 `grind order` 模块实现了基础设施。

* [#10562](https://github.com/leanprover/lean4/pull/10562) 简化了 `grind order` 模块，并把顺序约束内化。它移除了 `Offset` 类型类，因为它引入了过多复杂性。现在我们用更简单的方法覆盖相同用例：
  - 任何至少实现了 `Std.IsPreorder` 的类型；
  - 任意有序环；
  - 通过 `Nat.ToInt` 适配器处理的 `Nat`。

* [#10583](https://github.com/leanprover/lean4/pull/10583) 允许用户为 core 中已包含传播器的声明再声明额外的 `grind` 约束传播器。

* [#10589](https://github.com/leanprover/lean4/pull/10589) 为实现 `grind order` 添加了辅助定理。

* [#10590](https://github.com/leanprover/lean4/pull/10590) 实现了 `grind order` 的证明项构造。

* [#10594](https://github.com/leanprover/lean4/pull/10594) 实现了 `grind order` 中理论传播的证明构造。

* [#10596](https://github.com/leanprover/lean4/pull/10596) 实现了向 `grind order` 所用图中加入新边的函数。该图维护了所有已断言约束的传递闭包。

* [#10598](https://github.com/leanprover/lean4/pull/10598) 在 `grind order` 中实现了对正约束的支持。这个新模块已经能够求解如下问题：

  ```lean
  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
      (a b c : α) : a ≤ b → b ≤ c → c < a → False := by
    grind

  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
      (a b c d : α) : a ≤ b → b ≤ c → c < d → d ≤ a → False := by
    grind

  example [LE α] [Std.IsPreorder α]
      (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
    grind

  example [LE α] [Std.IsPreorder α]
      (a b c d : α) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
    grind
  ```

* [#10599](https://github.com/leanprover/lean4/pull/10599) 修复了 `grind order` 中对 `Nat` 的支持。该模块使用 `Nat.ToInt` 适配器。

* [#10600](https://github.com/leanprover/lean4/pull/10600) 在 `grind order` 中实现了对负约束的支持。示例：

  ```lean
  open Lean Grind
  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α]
      (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → d < a → False := by
    grind -linarith (splits := 0)

  example [LE α] [Std.IsLinearPreorder α]
      (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → ¬ (a ≤ d) → False := by
    grind -linarith (splits := 0)

  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
      (a b c d : α) : a - b ≤ 5 → ¬ (c ≤ b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
    grind -linarith (splits := 0)
  ```

* [#10601](https://github.com/leanprover/lean4/pull/10601) 修复了 `grind order` 在顺序不是偏序时发生 panic 的问题。

* [#10604](https://github.com/leanprover/lean4/pull/10604) 在 `grind order` 中实现了 `processNewEq` 方法。它负责处理由 `grind` E-graph 传播出来的等式。

* [#10607](https://github.com/leanprover/lean4/pull/10607) 为即将到来的 `grind` 策略模式添加了基础设施；这种模式将类似于 `conv` 模式。目标是把 `grind` 从终结策略扩展为交互模式：`grind => …`。

* [#10677](https://github.com/leanprover/lean4/pull/10677) 为新的 `grind` 交互模式实现了基础策略。虽然之后还会加入许多额外的 `grind` 策略，但基础框架已经可用。目前实现的 `grind` 策略有：`skip`、`done`、`finish`、`lia` 和 `ring`。它还移除了 `grind` fallback procedure 这一概念，因为它已被新框架吸收。示例：
  ```lean
  example (x y : Nat) : x ≥ y + 1 → x > 0 := by
    grind => skip; lia; done
  ```

* [#10679](https://github.com/leanprover/lean4/pull/10679) 确定一个问题,即“无效的替代名称”错误来自
`induction`在删除了违规的替代物后,留在原地。

* [#10690](https://github.com/leanprover/lean4/pull/10690) 加上`instantiate`、`show_true`、`show_false`、
`show_asserted`和`show_eqcs`交互式`grind`
模式。[`show`策略采用可选的“过滤器”,用于探测
`grind` 状态。示例:
  ```lean
  example (as bs cs : Array α) (v₁ v₂ : α)
          (i₁ i₂ j : Nat)
          (h₁ : i₁ < as.size)
          (h₂ : bs = as.set i₁ v₁)
          (h₃ : i₂ < bs.size)
          (h₃ : cs = bs.set i₂ v₂)
          (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
          (h₅ : j < cs.size)
          (h₆ : j < as.size)
          : cs[j] = as[j] := by
    grind =>
      instantiate
      -- Display asserted facts with `generation > 0`
      show_asserted gen > 0
      -- Display propositions known to be `True`, containing `j`, and `generation > 0`
      show_true j && gen > 0
      -- Display equivalence classes with terms that contain `as` or `bs`
      show_eqcs as || bs
      instantiate
  ```

* [#10695](https://github.com/leanprover/lean4/pull/10695) 修复了一个问题：如果 `mutual` 块中至少有一个宏存在，则其中非 `macro` 的成员会被丢弃。

* [#10706](https://github.com/leanprover/lean4/pull/10706) 为 `grind` 交互模式添加了 `have` 策略。示例：
  ```lean
  example {a b c d e : Nat}
      : a > 0 → b > 0 → 2*c + e <= 2 → e = d + 1 → a*b + 2 > 2*c + d := by
    grind =>
      have : a*b > 0 := Nat.mul_pos h h_1
      lia
  ```

* [#10707](https://github.com/leanprover/lean4/pull/10707) 确保 `grind` 交互模式中的 `finish` 策略在目标未关闭时会失败并报告诊断信息。

* [#10709](https://github.com/leanprover/lean4/pull/10709) 实现了 *anchors*（也称稳定哈希码），用于引用 `grind` 目标中出现的术语。它还引入了 `show_splits` 和 `show_state` 命令；前者会显示当前 `grind` 目标中候选 case split 的 anchors。

* [#10715](https://github.com/leanprover/lean4/pull/10715) 改进了用于引用 `grind` 目标中术语的 anchor 稳定性（也即稳定哈希码）。

* [#10731](https://github.com/leanprover/lean4/pull/10731) 在 `grind` 交互模式中增加了以下策略：
  - `focus <grind_tac_seq>`
  - `next => <grind_tac_seq>`
  - `any_goals <grind_tac_seq>`
  - `all_goals <grind_tac_seq>`
  - `grind_tac <;> grind_tac`
  - `cases <anchor>`
  - `tactic => <tac_seq>`

* [#10737](https://github.com/leanprover/lean4/pull/10737) 为 `grind` 交互模式加入了 `linarith`、`ac`、`fail`、`first`、`try`、`fail_if_success` 和 `admit` 策略。

* [#10740](https://github.com/leanprover/lean4/pull/10740) 改进了 `grind` 交互模式中的 `ac`、`linarith`、`lia`、`ring` 策略。如果没有取得进展，它们现在会失败；如果目标未关闭，还会生成带有反例/基的提示信息。

* [#10746](https://github.com/leanprover/lean4/pull/10746) 为 `grind` 交互模式中的 `instantiate` 策略实现了参数。用户现在可以同时选择全局和局部定理；局部定理通过 anchors 选择。它还添加了 `show_thms` 策略，用于显示局部定理。示例：

  ```lean
  example (as bs cs : Array α) (v₁ v₂ : α)
          (i₁ i₂ j : Nat)
          (h₁ : i₁ < as.size)
          (h₂ : bs = as.set i₁ v₁)
          (h₃ : i₂ < bs.size)
          (h₃ : cs = bs.set i₂ v₂)
          (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
          (h₅ : j < cs.size)
          (h₆ : j < as.size)
          : cs[j] = as[j] := by
    grind =>
      instantiate = Array.getElem_set
      instantiate Array.getElem_set
  ```

* [#10747](https://github.com/leanprover/lean4/pull/10747) 实现了 `finish?` 和 `grind?` 策略的基础设施。

* [#10748](https://github.com/leanprover/lean4/pull/10748) 为 `grind` 交互模式实现了 `repeat` tactical。

* [#10767](https://github.com/leanprover/lean4/pull/10767) 实现了用于实现 `grind` 搜索策略的新控制接口。它将取代 `SearchM` 框架。

* [#10778](https://github.com/leanprover/lean4/pull/10778) 确保 `grind` 交互模式是卫生的。它还添加了用于重命名不可访问名称的策略：`rename_i h_1 ... h_n`、`next h_1 ... h_n => ..`，以及供自动生成的策略脚本使用的 `expose_names`。该 PR 还增加了实现个案拆分动作所需的辅助函数。

* [#10779](https://github.com/leanprover/lean4/pull/10779) 为 `grind` anchors 实现了悬停信息。anchors 是用于引用 grind 状态中术语的稳定哈希码；它们将用于自动生成策略脚本。

* [#10791](https://github.com/leanprover/lean4/pull/10791) 在 `grind` 交互模式中加入了一条静默信息消息，其中包含 `grind` 状态。该消息只会在 `grind` 交互模式下恰好有一个目标时显示；这一条件是对当前 `InfoTree` 局限性的权宜处理。

* [#10798](https://github.com/leanprover/lean4/pull/10798) 为 `grind` 实现了 `intro`、`intros`、`assertNext` 和 `assertAll` 动作。

* [#10801](https://github.com/leanprover/lean4/pull/10801) 为 `grind` 实现了 `splitNext` 动作。

* [#10808](https://github.com/leanprover/lean4/pull/10808) 支持压缩自动生成的 `grind` 策略序列。

* [#10811](https://github.com/leanprover/lean4/pull/10811) 在 `splitNext` 动作中实现了正确的 case-split 锚点生成，这将用于实现 `grind?` 和 `finish?`。

* [#10812](https://github.com/leanprover/lean4/pull/10812) 为 `grind` 交互模式实现了 `lia`、`linarith` 和 `ac` 动作。

* [#10824](https://github.com/leanprover/lean4/pull/10824) 为 `grind` 交互模式实现了 `cases?` 策略。它提供了一种便捷方式来选择 anchors；用户可以使用筛选语言过滤候选项。

* [#10828](https://github.com/leanprover/lean4/pull/10828) 在交互模式中实现了一种紧凑记法，用于检查 `grind` 状态。在 `grind` 策略块中，每个策略都可以可选地带上形如 `| filter?` 的后缀。

* [#10833](https://github.com/leanprover/lean4/pull/10833) 实现了在 `GrindM` monad 中求值 `grind` 策略的基础设施。我们将用它来检查自动生成的策略是否能有效关闭原始目标。

* [#10834](https://github.com/leanprover/lean4/pull/10834) 执行`ring` 行动`grind`。

* [#10836](https://github.com/leanprover/lean4/pull/10836) 在 `grind` 求解器扩展（`SolverExtension`）中加入了对 `Action` 的支持。它还提供了 `Solvers.mkAction` 函数，用所有已注册的求解器构造一个 `Action`。生成出的动作是“公平”的，也就是说，一个求解器不能阻止其他求解器取得进展。

* [#10837](https://github.com/leanprover/lean4/pull/10837) 在 `grind` 交互模式中实现了 `finish?` 策略。当它成功关闭目标时，会生成一个代码动作，使用户能够用显式的 `grind` 策略步骤关闭目标，也就是不再依赖任何搜索。它还会明确指出用了哪些求解器。

* [#10841](https://github.com/leanprover/lean4/pull/10841) 改进了 tracing 模式下由 `instantiate` 动作生成的 `grind` 策略。它还更新了 `instantiate` 策略的语法，使之更像 `simp`。例如：

  * `instantiate only [thm1, thm2]` 只会实例化定理 `thm1` 和 `thm2`。
  * `instantiate [thm1, thm2]` 会实例化带有 `@[grind]` 属性的定理，**以及** 定理 `thm1` 和 `thm2`。

* [#10843](https://github.com/leanprover/lean4/pull/10843) 在 `grind` 交互模式中实现了 `set_option` 策略。

* [#10846](https://github.com/leanprover/lean4/pull/10846) 修复了 `finish?` 中 `instance only [...]` 策略生成的几个问题。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Compiler"
%%%

````markdown

* [#10429](https://github.com/leanprover/lean4/pull/10429) 代码中专门化的修补和过于谨慎的再利用
发电机。

* [#10444](https://github.com/leanprover/lean4/pull/10444) 固定大型昆虫的`inc` 操作插入过重
常数。

* [#10488](https://github.com/leanprover/lean4/pull/10488) 改变科学数字的解析方式,以便
为(无效的)语法提供更好的错误信息,如 `32.succ` 。

* [#10495](https://github.com/leanprover/lean4/pull/10495) 修正代码生成器中 UIntX 的恒定折叠。 此选项
由于昆特的死法 最优化以前只是死代码
字数已编码 。

* [#10610](https://github.com/leanprover/lean4/pull/10610)确保即使某一类型被标为`irreducible`
编译器可以通过
以查找类型别名背后隐藏的函数。

* [#10626](https://github.com/leanprover/lean4/pull/10626) 降低死者的侵略性,让我们从
兰巴达·RC

* [#10689](https://github.com/leanprover/lean4/pull/10689) 规定对守则中驻地协调员插入阶段的监督
发电机。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Pretty-Printing"
%%%

````markdown

* [#10376](https://github.com/leanprover/lean4/pull/10376) 修改了 `fun` binder 的 pretty printing，抑制了同一个 `fun` 内 binder 之间的安全遮蔽特性。例如，现在我们会看到 `fun x x_1 => 0`，而不是把它打印成 `fun x x => 0`。这个计算是按每个 `fun` 单独进行的，因此例如 `fun x => id fun x => 0` 仍会保持原样打印，从而继续利用安全遮蔽。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Documentation"
%%%

````markdown

* [#10632](https://github.com/leanprover/lean4/pull/10632)为位数阵列添加缺失的文档字符串,并制作已有的
符合我们的风格

* [#10640](https://github.com/leanprover/lean4/pull/10640) 添加了一个缺失的文档字符串，并将我们的风格指南应用到 `String` API 的一部分上。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Server"
%%%

````markdown

* [#10365](https://github.com/leanprover/lean4/pull/10365) 执行服务器侧的服务器侧,以在
信息查看。

* [#10442](https://github.com/leanprover/lean4/pull/10442)确保提供不明身份识别代码行动
自动隐含。

* [#10524](https://github.com/leanprover/lean4/pull/10524)在合并的“尝试此”中增加对交互性的支持
在 # 9966 中引入的信息。 在此过程中, 它移动链接
将建议应用到 `[apply]` 在
建议. 带有异差的提示保持不变,因为它们没有
之前支持使用 diff 中的条件进行交互 。

* [#10538](https://github.com/leanprover/lean4/pull/10538) 解决语言服务器中`exit` 调用的僵局。

* [#10584](https://github.com/leanprover/lean4/pull/10584) 让 Verso docstring 会在环境中搜索长度至少与当前名称一样长的名称，并将其作为建议给出。

* [#10609](https://github.com/leanprover/lean4/pull/10609) 修复了 #925 中引入的 `FileSystemWatcher` 与 LSP 不兼容的问题。

* [#10619](https://github.com/leanprover/lean4/pull/10619) 修复了未知标识符代码动作中的一个错误：对于诸如 `open Foo.Bar` 这样的嵌套 `open` 声明，它此前会给出没有意义的建议。

* [#10660](https://github.com/leanprover/lean4/pull/10660) 在 `end` 之后为标识符添加了自动补全。它还修复了一个错误：在 `set_option` 后的空白处补全时，无法给出完整的选项列表。

* [#10662](https://github.com/leanprover/lean4/pull/10662) 重新启用了 Verso docstring 的 semantic tokens；此前的一次改动意外将其禁用。它还添加了测试，以防此问题再次发生。

* [#10738](https://github.com/leanprover/lean4/pull/10738) 修正由#10307 引入的回归, 在此悬停名称
一种感应型的类型或在其自己的声明中的建造者没有显示
文档字符串 。 在此过程中, 一个在文档字符串中处理的错误 。
发现并固定了硬币类型。
防止倒退在未来重演。

* [#10757](https://github.com/leanprover/lean4/pull/10757) 将错误与 VS 代码结合处理,其中Lian 代码
看起来像 CSS 颜色代码将显示颜色摘取器装饰 。

* [#10797](https://github.com/leanprover/lean4/pull/10797)]在未知的标识代码动作中,在
在嵌套命名空间中无法正确最小化标识符 。
还可以修补错误, 其中标识符有时会最小化到
`[anonymous]`。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Lake"
%%%

````markdown

* [#9855](https://github.com/leanprover/lean4/pull/9855) 为包和库添加了新的 `allowImportAll` 配置选项。上游包或库启用后，下游包就能 `import all` 该包或库的所有模块。这使包作者可以有选择地决定下游包是否能访问某些 `private` 元素。

* [#10188](https://github.com/leanprover/lean4/pull/10188) 增加对远程文物藏匿处(如储藏库)的支持
作为这种支持的一部分,LakeLake中心指挥的一套`lake cache` 新的新套件(CLI命令)
为了帮助管理LakeLake的缓存,已经引入了帮助管理Lake的缓存。
已经对当地缓存支持进行了全面改革,以更好地与
新远程支持 。

* [#10452](https://github.com/leanprover/lean4/pull/10452)] 重构因素Lake的整套命名程序允许包件
由消费者重新命名。 有了这个, 用户现在可以需要一个软件包
使用与所定义的名称不同的名称。

* [#10459](https://github.com/leanprover/lean4/pull/10459) 在生成的 GitHub Action 模板中修正有条件检查
Lake边的Lake边

* [#10468](https://github.com/leanprover/lean4/pull/10468) 重构Lake对数山采用`LogConfig` 结构
当运行时( 而不是多个参数) 。 此断开更改应该
帮助最小化由于配置选项改变而导致的未来断裂。

* [#10551](https://github.com/leanprover/lean4/pull/10551) 能够要求作为依附地的储备包包
特定包件版本(即包件中指定的`version`)
配置文件) )

* [#10576](https://github.com/leanprover/lean4/pull/10576) 添加了新的包配置选项：`restoreAllArtifacts`。当它被设为 `true` 且启用了 Lake 的本地制品缓存时，Lake 会把所有缓存制品复制到构建目录中。这可以确保那些期望在构建目录中获取构建结果的外部消费者能够使用它们。

* [#10578](https://github.com/leanprover/lean4/pull/10578) 为 Lake 的 `buildType` 配置选项增加了对 CMake 风格构建类型拼写（即首字母大写形式）的支持。

* [#10579](https://github.com/leanprover/lean4/pull/10579)改变行为`libPrefixOnWindows`,添加`lib`前缀
库库是 `libName` ,而不仅仅是文件路径。这意味着
Lake的 `-l` 现在 Windows 上将会有前缀。 虽然这不应该
MSYS2 结构(该结构既接受`lib`,又接受`lib`预 和
它应当确保与MSVC的兼容性(如果
这个问题始终是一个问题)。

* [#10730](https://github.com/leanprover/lean4/pull/10730) 将Lake边的远程缓存界面更改为范围缓存输出
使用工具链和/或平台是有用的。

* [#10741](https://github.com/leanprover/lean4/pull/10741) 修正以 `--old` 建立的部分更新文件的错误
可在缓存中存储全部最新文件。
此外,无痕迹的建筑现在只进行
与 `--old` 进行时间修改检查。
过时了

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Other"
%%%

````markdown

* [#10383](https://github.com/leanprover/lean4/pull/10383)包括发布过程的一些改进,使发布过程
更新`stable`事务组,使之更加稳健,并将`cslib`纳入`cslib`
发布清单。

* [#10389](https://github.com/leanprover/lean4/pull/10389) 修正一个错误, 其中字符串字串解析忽略其尾随的错误
白空间设置。

* [#10460](https://github.com/leanprover/lean4/pull/10460)] 引入一个简单的脚本,在
用于模块系统使用的软件包包软件包,不进一步最小化导入
或说明使用。

* [#10476](https://github.com/leanprover/lean4/pull/10476) 修复内核中的清除代码
`infer_let` 功能。

* [#10575](https://github.com/leanprover/lean4/pull/10575) 增加记录详细拟订工作的必要基础设施
由此产生的环境可能不明显看出的相互依存关系
调整后的`shake`
从 Mathlib 添加到 `script/` 中, 但可以移动到另一个位置
或未来回购。

* [#10777](https://github.com/leanprover/lean4/pull/10777) 改进了有助于削减利豆排放的脚本(按
并增加文件),并增加
`.claude/commands/release.md` 即时文件,这样Claude可以提供帮助。

````
