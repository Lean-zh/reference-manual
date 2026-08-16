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

## 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights"
%%%

Lean v4.25.0 带来了多项令人兴奋的新特性。编辑器集成为 “try this” 建议增加了交互性，Lake 增加了远程缓存支持。新的语言特性包括：自动为类型类方法生成规格定理、余归纳谓词，以及 `mvcgen` 中的不变式建议。`grind` 获得了一个交互模式，允许用户控制证明搜索，并可建议可复现的证明脚本。其推理能力还扩展到了单射函数、非交换（半）环，以及预序和有序环结构。标准库则带来了重新设计的 `String` 类型和更丰富的异步原语。请继续阅读下文了解详情！

### 应用 “try this” 建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Apply-___try-this___-Suggestions"
%%%

[#10524](https://github.com/leanprover/lean4/pull/10524) 为 [#9966](https://github.com/leanprover/lean4/pull/9966) 中引入的 “try this” 消息增加了交互性（如 hover 和 go-to-definition）。同时，它把“应用建议”的链接改成了建议前方单独的 `[apply]` 按钮。

### Lake 的远程缓存
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Remote-Caching-with-Lake"
%%%

[#10188](https://github.com/leanprover/lean4/pull/10188) 为 Lake 增加了远程构件缓存（例如 Reservoir）支持。作为这项支持的一部分，还引入了一组新的 `lake cache` CLI 命令，用于管理 Lake 的缓存；现有的本地缓存支持也经过了重构，以便更好地与新的远程支持协同工作。

### 余归纳谓词
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Coinductive-Predicates"
%%%

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

### `mvcgen` 不变式建议
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Mvcgen-Invariants-Suggestions"
%%%

[#10456](https://github.com/leanprover/lean4/pull/10456)和[#10566](https://github.com/leanprover/lean4/pull/10566)
执行`mvcgen invariants?` 提出具体的变异物建议
依据变量是如何在 VC 中使用的。
这些建议是有意简单简单化的,归结为:
循环起始处的挂着点, 且此挂着点必须保持在循环的结尾处
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

### `grind`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind"
%%%

#### 交互模式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Interactive-mode"
%%%

`grind` 延长了交互模式`grind => …`
[#10607](https://github.com/leanprover/lean4/pull/10607)、[#10677](https://github.com/leanprover/lean4/pull/10677)、...])

```lean
example (x y : Nat) : x ≥ y + 1 → x > 0 := by
  grind => skip; lia; done
```

交互式模式与_anchors_(又称稳定散列代码)相配,用于查找`grind`目标中出现的术语
([#10709](https://github.com/leanprover/lean4/pull/10709)))。

在交互模式下,可以采取以下行动:

- `instantiate`全球和地方定理
[#10746](https://github.com/leanprover/lean4/pull/10746)和[#10841](https://github.com/leanprover/lean4/pull/10841));

- 检查`show_splits`和`show_state`([#10709](https://github.com/leanprover/lean4/pull/10709)),
`show_true`、`show_false`、`show_asserted`和`show_eqcs`
([#10690](https://github.com/leanprover/lean4/pull/10690));

- 检查过滤器;每种战术都可以有表格的后缀`| filter?`
([#10828](https://github.com/leanprover/lean4/pull/10828));

- ([#10706](https://github.com/leanprover/lean4/pull/10706))作出`have`([#10706](https://github.com/leanprover/lean4/pull/10706))当地主张;

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

#### 非交换（半）环归一化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Non-commutative-_LPAR_semi_RPAR_ring-normalization"
%%%

- [#10375](https://github.com/leanprover/lean4/pull/10375) 在`grind` 中增加支持非和解性戒指正常化。
新的归并器也算作`IsCharP` 类类。

  ```lean
  open Lean Grind

  variable (R : Type u) [Ring R]
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind

  variable [IsCharP R 4]
  example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
  ```

- [#10421](https://github.com/leanprover/lean4/pull/10421) 在`grind` 中加上非混合半衰期的正常化标准。

  ```lean
  open Lean.Grind
  variable (R : Type u) [Semiring R]

  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  ```

#### 单射函数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Injective-functions"
%%%

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

#### `grind order` 求解器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Grind-order-solver"
%%%

磨磨现在可以解决预先订购和订购戒指的问题了
[#10562](https://github.com/leanprover/lean4/pull/10562)、[#10598](https://github.com/leanprover/lean4/pull/10598)和[#10600](https://github.com/leanprover/lean4/pull/10600)。
新的求解器`grind order`,支持`Nat`,并处理积极和消极的制约因素。

```lean
open Lean Grind
example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
    (a b c d : α) : a - b ≤ 5 → ¬ (c ≤ b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
  grind -linarith (splits := 0)
```

#### 新的模式推断启发式
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--New-pattern-inference-heuristic"
%%%

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

### 规格定理派生
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Specifications-Derivation"
%%%

Lean现在为定制和衍生型类实例提供自动生成规格定理:

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

- [#10351](https://github.com/leanprover/lean4/pull/10351)增加了做`deriving ReflBEq, LawfulBEq`的能力。
类别必须列在`deriving`条款中。
这是用来与 `deriving BEq` 合作的(但你可以尝试
使用它来用手挂(plex-product)形形形形形形形形形形形形形形形形形形形形形形色色。
不支持相互或嵌套的感官。

### `String` 类型重构
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Overhaul-of-the-String-Type"
%%%

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

- [#10713](https://github.com/leanprover/lean4/pull/10713) 强制执行关于`String.Pos.Raw`算术的规则。

** 减少变化**:删除了`HAdd`和`HSub`实例`String.Pos.Raw`。
详情请见PR说明。

- [#10735](https://github.com/leanprover/lean4/pull/10735)将许多`String.Pos.Raw`业务转移至`String.Pos.Raw`
`String.Pos.Raw` 命名空间。

** 打破变化**:在本PR之后,`String.pos_lt_eq`不再为`simp` 列马。
如果证明破损,添加`String.Pos.Raw.lt_iff`,作为`simp` 列马。

### 异步框架
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Async-Framework"
%%%

扩大了Async框架,包括:

- POSIX 信号处理器([#9258](https://github.com/leanprover/lean4/pull/9258));
- `Std.Sync.Notify`,`CondVar` 适合同价的[#10368](https://github.com/leanprover/lean4/pull/10368)]替代`CondVar`;
- `Std.Broadcast`,向`Std.Sync`([#10369](https://github.com/leanprover/lean4/pull/10369))提供多消费、多生产渠道;
- `StreamMap`,一种在无同步流中允许多x化的类型([#10400](https://github.com/leanprover/lean4/pull/10400));
- `Std.CancellationToken` ([#10510](https://github.com/leanprover/lean4/pull/10510))。

### 迭代器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Iterators"
%%%

- [#10686](https://github.com/leanprover/lean4/pull/10686) 采用`any`、`anyM`、`all`和`allM`
还会为它们提供润滑剂

- [#10728](https://github.com/leanprover/lean4/pull/10728) 引入 `flatMap` 迭代器组合器。它还添加了
`flatMap`至`toList`和`toArray`。

- [#10761](https://github.com/leanprover/lean4/pull/10761) 在散列图上提供迭代器。

### InfoView Trace 搜索
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--InfoView-Trace-Search"
%%%

[#10365](https://github.com/leanprover/lean4/pull/10365) 执行服务器侧的服务器侧,以在
InfoView。 演示视频请参见 PR 描述 。

### 实例的线性构造
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Linear-Construction-of-Instances"
%%%

`DerivingBEq` ([#10268](https://github.com/leanprover/lean4/pull/10268))的`DerivingBEq`([#10268](https://github.com/leanprover/lean4/pull/10268))的替代实施
`Deriving Ord` ([#10270](https://github.com/leanprover/lean4/pull/10270))
基于比较`.ctorIdx`,并使用专用匹配器比较同一建构体
),以避免在[[[ ]]项中增加“),
默认匹配执行 。
`deriving.beq.linear_construction_threshold`和`deriving.ord.linear_construction_threshold`
设置使用新建筑的建筑师计数阈值(默认为10)。

### 迁移到模块系统
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Porting-to-the-Module-System"
%%%

[#10807](https://github.com/leanprover/lean4/pull/10807) 采用`backward.privateInPublic` 备选办法援助`backward.privateInPublic`
通过临时允许进入模块系统,将项目移植到模块系统
从公共范围,甚至从各个单元,公开发表私人声明。
此类存取器将生成警告警告,除非
`backward.privateInPublic.warn` 已禁用。

### 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Breaking-Changes"
%%%

- [#10714](https://github.com/leanprover/lean4/pull/10714) 取消对可减少的有充分证明的重复、断开的支持
在定义上使用`@[semireducible]`
重复打印打印警告说这不再有效。

- [#10319](https://github.com/leanprover/lean4/pull/10319) 结构`Std.PRange shape α`的“元形形化”将其替换
`Std.Rcc`、`Std.Rco`、`Std.Rci`等九个不同结构`Std.Rcc`、`Std.Rco`、`Std.Rci`等,一个
对于范围界限的每一种可能的形状。这种改变是必要的
因为形状多形态 不利于自动化的尝试

** 范围/切片标记本身没有变化,但以下部分没有变化。
基本上折断全部剩余(多变性)和切片 API
除了点注(`toList`、`iter`、...]].。
声明是以形形多变方式提具的,而这种形态多变方式已不再存在。

- [#10645](https://github.com/leanprover/lean4/pull/10645) 将`Stream`改名为`Std.Stream`,使名称成为
在折旧周期后,数学流可用。

- [#10468](https://github.com/leanprover/lean4/pull/10468) 重构Lake对数山采用`LogConfig` 结构
当运行时( 而不是多个参数) 。 此断开更改应该
帮助最小化由于配置选项改变而导致的未来断裂。

- [#10660](https://github.com/leanprover/lean4/pull/10660)在`end`后添加识别符号自动补全。
`set_option` 后白色空格中的补全无法完成的错误
产生完整选项列表。

断开更改:调整`«end»` 语法以取一个`identWithPartialTrailingDot`,而不是取一个`ident`。

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Language"
%%%

* [#7844](https://github.com/leanprover/lean4/pull/7844) 添加一个简单的执行MEPO的简单内容,来自“轻重量”
用于机器产生的解析问题的关联过滤”由Meng著
还有保尔森

* [#10158](https://github.com/leanprover/lean4/pull/10158) 补充关于无法通过
输入 defeq 错误的模块系统 。

* [#10268](https://github.com/leanprover/lean4/pull/10268)添加了基于`DerivingBEq`的`DerivingBEq`的替代实施`DerivingBEq`的替代实施`DerivingBEq`
比较 `.ctorIdx`,并使用专用匹配器比较
设计体(在#10152中添加),以避免
默认匹配执行。新选项
`deriving.beq.linear_construction_threshold` 设置构建器计数
使用新建筑(默认为10个阈值)使用新建筑。
也允许`deriving ReflBEq, LawfulBeq`,尽管这些证明
这些属性仍然是二次形的。

* [#10270](https://github.com/leanprover/lean4/pull/10270)添加了基于`Deriving Ord`的`Deriving Ord`的替代实施`Deriving Ord`的替代实施`Deriving Ord`
比较 `.ctorIdx`,并使用专用匹配器比较
新选项
`deriving.ord.linear_construction_threshold` 设置构建器计数
使用新建筑的阈值(默认为10个)。

* [#10302](https://github.com/leanprover/lean4/pull/10302) 引入`@[specs]`属性。可适用于
(某些)类别类型类别实例,并定义
通过采用该类的等式定理,
类型类例和类型
从超载操作的角度来修改它们。 修复# 5295。

* [#10333](https://github.com/leanprover/lean4/pull/10333) 引入一个`coinductive`关键字,用于定义
通过与 `inductive` 相同语法的语法
关键关键关键词. 该机构依靠执行详细拟订
电导类型,并提取在适当空间上的内分形
从定义的上游情况,然后输入
`PartialFixpoint`. 在拟订定义时,所有建构人
通过自动生成的 Lemmas 声明。

* [#10346](https://github.com/leanprover/lean4/pull/10346) 使`deriving BEq`和`deriving Ord`使用`@[method_specs]`
酌情取自#10302(即未使用`partial`)。

* [#10351](https://github.com/leanprover/lean4/pull/10351)增加了做`deriving ReflBEq, LawfulBEq`的能力。
`deriving`条款中必须列出的类别。对于`ReflBEq`,简单
`simp` 使用基于`simp`的证明。`LawfulBEq` 对于`LawfulBEq`,是专用的,
使用语法引导的战术,这种战术应有利于衍生`BEq`
示例。这意在与 `deriving BEq` 合作(但您可以尝试
使用它来用手挂(plex-product)形形形形形形形形形形形形形形形形形形形形形形色色。
不支持相互或嵌套的感官。

* [#10375](https://github.com/leanprover/lean4/pull/10375) 在`grind` 中增加支持非和解性戒指正常化。
新的归并器也计算 `IsCharP` 类类。 例如 :
  ```lean
  open Lean Grind

  variable (R : Type u) [Ring R]
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-4) * a - 2*b*a + 4 * b^2 := by grind

  variable [IsCharP R 4]
  example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
  example (a b : R) : (a - b)^2 = 13*a^2 - a * b - b * 5 * a + b*3*b*3 := by grind
  ```

* [#10377](https://github.com/leanprover/lean4/pull/10377) 确定一个问题, 即 app Experator 中的“ eta 特征 ” ,
当定位参数因指定而跳过时,该参数被引用
参数,结果产生变量,这些变量可以由被点名的
参数。现在执行此特性的临时本地变量
获取新名称。关闭 ambda 表达式所使用的名称仍然可用
使用原始参数名称。

* [#10378](https://github.com/leanprover/lean4/pull/10378) 能够使用`notation`项
`infix` /`infixl` /`infixr` /`prefix` /`postfix`。
能够使用`pp.unicode`注意到的剖析器。
可将核心解析器组合在一起:
  ```lean
  infixr:30 unicode(" ∨ ", " \\/ ") => Or
  ```

* [#10379](https://github.com/leanprover/lean4/pull/10379) 更改战术配置的语法语法。
`(ident`将致力于战术配置项目分割,但现在
`(ident :=`。这样可以可靠地使用战术
`term` 类别之前的配置。例如,给定的“语法”
“我的_tac”选择 Config 术语:战术`, it used to be that ` 我的_tac (x + y) `
如果有误差,那末,`+`在“预期`:=`中”中将出现误差,但现在它能剖析。
术语。

* [#10380](https://github.com/leanprover/lean4/pull/10380)在`grind ring`模块中实施`grind ring` 无害度检查,以确保
以类别分辨率类型合成的示例按定义
等于 `grind` 核心类中相应类中的对应类。
进行平等定义性平等测试时的削减仅限于:
可减少的定义和实例。

* [#10382](https://github.com/leanprover/lean4/pull/10382) 制造内置的Verso docstring 逃兵靴
正确, 添加推迟检查的能力( 这是
解决前方参考资料和靴靴问题),并
微小采集器错误 。

* [#10388](https://github.com/leanprover/lean4/pull/10388) 修正含有嵌套证明定义的错误
`sorry` 可能不报告“警告:如果
与前一文档中另一个嵌套的证明相同类型
声明。 错误仅影响日志消息; `#print axioms` 将会
仍然正确报告`sorryAx`的使用情况。

* [#10391](https://github.com/leanprover/lean4/pull/10391) 给匿名建构符记号(`⟨x,y⟩`))错误回收
如果参数不足,则合成的杂类
插入为缺失的参数插入,错误被登录,而不是
绝对失败。

* [#10392](https://github.com/leanprover/lean4/pull/10392) 将问题与`if` 策略中未设置错误的`if` 方法固定在一起
中添加一些错误回收,以避免
战术时 `if` 符号上的未解决目标的额外错误
语法不完整 。

* [#10394](https://github.com/leanprover/lean4/pull/10394) 加 `reduceBEq` 和`reduceOrd` ,以补 ,并改写
`_ == _` 复`Ord.compare _ _`的[[]]发生时,如果两个参数都是
和相应实例的构建符和对应实例的符号
`@[method_specs]`(在#103002中引入),现在默认为
衍生实例。

* [#10406](https://github.com/leanprover/lean4/pull/10406) 改进于#103002, 以适当制作方法的分解定理
如果执行功能未曝光, 则该执行功能为私有 。

* [#10415](https://github.com/leanprover/lean4/pull/10415)在证明等式时修改所尝试的步骤顺序
为避免达到`split`
无法处理, 避免将方程的LHS显示为 `.brecOn` 和
`.rec` 直至RHS被分为最后案件之后。

* [#10417](https://github.com/leanprover/lean4/pull/10417)更改`deriving_LawfulEq_tactic_step`的自动化,以便使用
`with_reducible` 使用`change`表示目标形状时
我们不会在这里不小心打来电话 解决了10416号电话

* [#10419](https://github.com/leanprover/lean4/pull/10419)增加帮助者定理`eq_normS_nc`,以便实现正常化
非混合半质。 我们将使用此理论来解释
`grind ring`模块中的正常化步骤。

* [#10421](https://github.com/leanprover/lean4/pull/10421) 在`grind` 中加上非混合半衰期的正常化标准。
实例:
  ```lean
  open Lean.Grind
  variable (R : Type u) [Semiring R]

  example (a b c : R) : a * (b + c) = a * c + a * b := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * (1+1) * a * 1 + 5 * b^2 := by grind
  example (a b : R) : a^3 + a^2*b + a*b*a + b*a^2 + a*b^2 + b*a*b + b^2*a + b^3 = (a+b)^3 := by grind
  ```

* [#10422](https://github.com/leanprover/lean4/pull/10422) 实施新的电子匹配模式
`grind`。它尚未启用。 您可以使用
`set_option backward.grind.inferPattern false`。
新行为。

* [#10425](https://github.com/leanprover/lean4/pull/10425)让`split` 策略将非`split` 的持不同政
使用 `generalize` 的自定义变量和校对。如果
非fvar-discriminants 是证明, 然后这避免了 更精细的
`split`的概括化战略,可不具有依赖性
因此,减轻问题10424。

* [#10428](https://github.com/leanprover/lean4/pull/10428) 将`grind` 修饰剂明确删除,并确保`grind`
对本地定理使用“ mindableable” 。

* [#10430](https://github.com/leanprover/lean4/pull/10430)确保用户能够选择“最小可索引化子表达式”
以 `grind` 参数为条件。示例:它们现在可以写“grind [!] !
- >thmName `. `grind?` will include the `!
使用 `@[grind!]` 。 也用新模式修正一个失踪案件
推断程序。
它还调整了一些[[ 说明和测试,以准备
设置新的模式推论为新默认值。

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

* [#10479](https://github.com/leanprover/lean4/pull/10479) 在 Verso 语法中执行模块符号, 并添加
对一般Verso 语句的修改和修正。
特别是,他们现在有语言服务器支持,在
分析时间而不是编译时间, 所以快照的语法树
包括解析文档。

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

* [#10563](https://github.com/leanprover/lean4/pull/10563)将一些关于基本类型的`ReduceEval` 实例从
`quote4` 库。

* [#10566](https://github.com/leanprover/lean4/pull/10566) 改进`mvcgen invariants?`,以提出具体的变异物
依据变量是如何在 VC 中使用的。
这些建议是有意简单简单化的,归结为:
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

* [#10612](https://github.com/leanprover/lean4/pull/10612) 确定所报问题[
Zulip](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/.60abstractMVars.60.20not.20instantiating.20level.20mvars/near/541918246)
`abstractMVars` [(用于类别类类型推断和`simp`]]
(a) 类别中的可即时变乘数
导致它产生抽象的已分配的可变变量。

* [#10618](https://github.com/leanprover/lean4/pull/10618) 将多余的`Monad`例从
`MonadExceptOf` 取消框架。

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

* [#10714](https://github.com/leanprover/lean4/pull/10714) 取消对可减少的有充分证明的重复、断开的支持
在定义上使用`@[semireducible]`
重复打印打印警告说这不再有效。

* [#10716](https://github.com/leanprover/lean4/pull/10716)为执行含有
十六进制数 。 我们将用它来在
`grind` 交互模式。

* [#10720](https://github.com/leanprover/lean4/pull/10720) 更改`mvcgen` 的“实验性”警告
默认的默认值。 正式发布已被推迟, 以证明小
在最近的将来,语义基础的变化将打破。

* [#10722](https://github.com/leanprover/lean4/pull/10722) 试图使用时显示错误时的更改 [#10722](https://github.com/leanprover/lean4/pull/10722)
`coinductive`关键词指向非活在`Prop` 中的东西。
而不是在彼此的第一个元素上方显示错误
区块,它显示在错误定义上方。

* [#10733](https://github.com/leanprover/lean4/pull/10733) 在终止期间,演示的辅助定理更加激烈
正在检查。 此修正为# 10721 。

* [#10734](https://github.com/leanprover/lean4/pull/10734) 跟随#10606, 并统一创建方程定理
只有一个操作者注册在
`registerGetEqnsFn`。

* [#10780](https://github.com/leanprover/lean4/pull/10780)当`decide +kernel`在
内核 但不是精灵 修复了10766号

* [#10782](https://github.com/leanprover/lean4/pull/10782) 实施一种暗示战术`mvcgen?`,扩大至`mvcgen
变数?

* [#10783](https://github.com/leanprover/lean4/pull/10783)确保诸如“冗余替代方法”等错误电文
正确的误差位置,即使武器分享他们的RHS。 修复#10781。

* [#10793](https://github.com/leanprover/lean4/pull/10793) 修复#10792。

* [#10796](https://github.com/leanprover/lean4/pull/10796) 更改与编译匹配,以拒绝某些符合
先前由于无法进入的形态而被接受,有时得到治疗
修复了10794号

* [#10807](https://github.com/leanprover/lean4/pull/10807) 采用`backward.privateInPublic` 备选办法援助`backward.privateInPublic`
通过临时允许进入模块系统,将项目移植到模块系统
从公共范围,甚至从各个单元,公开发表私人声明。
此类存取器将生成警告警告,除非
`backward.privateInPublic.warn` 已禁用。

* [#10839](https://github.com/leanprover/lean4/pull/10839) 暴露了用于执行`optionValue`
`set_option`编号。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Library"
%%%

* [#9258](https://github.com/leanprover/lean4/pull/9258) 向利恩标准库增加对信号处理器的支持。

* [#9298](https://github.com/leanprover/lean4/pull/9298) 进一步支持 " 零点数 " 行动`BitVec.ctz`
和 `bv_decide`,依靠现有的`clz`
我们还围绕[[]](与[[[]]]和[[[[[]]]]]
`BitVec.clz` 现有理论理论,并引入 lemmas
`BitVec. [ctz_eq_reverse_clz, clz_eq_reverse_ctz, ctz_lt_iff_ne_zero, [ctz_eq_reverse_clz, clz_eq_reverse_ctz, ctz_lt_iff_ne_zero,]
获取LsbD_false_of_lt_ctz,获得LsbD_ true_ctz_of_ne_zero,获得LsbD_ true_ctz_of_ne_zero,
2_pow_ctz_le_toNat_of_ne_0,逆向_eq,
eq_eq_eq_0_iff] ' 。

* [#9932](https://github.com/leanprover/lean4/pull/9932) 添加`LawfulMonad`和`WPMonad`例`Option`的`LawfulMonad`和`WPMonad`例]
`OptionT`。

* [#10304](https://github.com/leanprover/lean4/pull/10304) 将`String` 重新定义为`b`
`b.IsValidUtf8`。

* [#10319](https://github.com/leanprover/lean4/pull/10319) 结构`Std.PRange shape α`的“元形形化”将其替换
`Std.Rcc`、`Std.Rco`、`Std.Rci`等九个不同结构`Std.Rcc`、`Std.Rco`、`Std.Rci`等,一个
对于范围界限的每一种可能的形状。这种改变是必要的
因为形状多形态 不利于自动化的尝试

* [#10366](https://github.com/leanprover/lean4/pull/10366) 重构 Async 模块，将 `Async` 类型用于所有
`Async` 档案。

* [#10367](https://github.com/leanprover/lean4/pull/10367) 为 TCP 和 UDP 添加矢量写入 [#10367](https://github.com/leanprover/lean4/pull/10367) 。
在TCP和UDP中确定驻地协调员问题
以行 `lean_dec((lean_object*)udp_socket);` 和
a 试图使`socket`内物体衰减的类似物体。

* [#10368](https://github.com/leanprover/lean4/pull/10368)添加`Notify`类似`CondVar`的结构的`Notify`
但它是用来计算货币的。
`Std.Sync.Notify`和`Std.Condvar`取决于`Std.Mutex`和`Std.Condvar`
将`Task` 等待时所用的整个线条填充。

* [#10369](https://github.com/leanprover/lean4/pull/10369) 向Std.Sync增加一个多消费、多生产渠道。

* [#10370](https://github.com/leanprover/lean4/pull/10370) 增加流的单类型类 。

* [#10400](https://github.com/leanprover/lean4/pull/10400) 添加可允许多x化的串流映图类型
支离破碎的溪流

* [#10407](https://github.com/leanprover/lean4/pull/10407)在`Init`中为类似类型类添加`@[method_specs_simp]`
`HAppend`。

* [#10457](https://github.com/leanprover/lean4/pull/10457)对`String.Pos`和`Substring`引入安全替代品
只能代表有效位置/偏差。

* [#10487](https://github.com/leanprover/lean4/pull/10487) 在 tcp 和 upp 取消时添加矢量写入和修正 rc 问题
功能。

* [#10510](https://github.com/leanprover/lean4/pull/10510)增加`Std.CancellationToken`类型

* [#10514](https://github.com/leanprover/lean4/pull/10514) 定义新的`String.Slice` API。

* [#10552](https://github.com/leanprover/lean4/pull/10552) 确保`Substring.beq`具有反射性,特别是
满足等同`ss1 == ss2 <-> ss1.toString = ss2.toString`。

* [#10611](https://github.com/leanprover/lean4/pull/10611)在`DHashMap`/`HashMap`/`HashSet`上增加一个工会行动
其原始变体,并提供有关工会业务的礼仪。

* [#10618](https://github.com/leanprover/lean4/pull/10618) 将多余的`Monad`例从
`MonadExceptOf` 取消框架。

* [#10624](https://github.com/leanprover/lean4/pull/10624) 将`String.Pos`改名为`String.Pos.Raw`。

* [#10627](https://github.com/leanprover/lean4/pull/10627) 加上`forall_fin_zero`和`exists_fin_zero`。
`forall_fin_zero`、`forall_fin_one`、`forall_fin_two`、
`exists_fin_zero`、`exists_fin_one`、`exists_fin_two`和`simp`
属性。

* [#10630](https://github.com/leanprover/lean4/pull/10630) 旨在固定计时器 API选择器,以便一旦完成
这一修改使`Selectable.one`成为了`Selectable.one`
函数将 [`selectables` 数组尽快下调 `selectables` 数组,因此当
与具有诸如 TCP socket 等某些效果的终端加在一起
最终定本,它会尽快运行

* [#10631](https://github.com/leanprover/lean4/pull/10631) 暴露了有关`Int*`的定义。
善事要求他们中的许多人暴露出来,此外,
`decide` 现在与`Int*` 操作合作。 这固定了# 10631 。

* [#10633](https://github.com/leanprover/lean4/pull/10633)为已签名的有限数量类型提供范围范围支持
`Int{8,16,32,64}`和`ISize`。
将全部减少为关于一个内部的证明 `UpwardEnumerable`
例如,`BitVec` 被解释为符号编号。

* [#10634](https://github.com/leanprover/lean4/pull/10634) 定义`ByteArray.validateUTF8`,使用`ByteArray.validateUTF8`来表明
`ByteArray.IsValidUtf8`是可调整和重新定义`String.fromUTF8`和]
朋友使用它。

* [#10636](https://github.com/leanprover/lean4/pull/10636)将`String.getUtf8Byte`改名为`String.getUTF8Byte`
遵守标准的库命名公约。

* [#10642](https://github.com/leanprover/lean4/pull/10642) 将`List.Cursor.pos`
`prefix.length`。

* [#10645](https://github.com/leanprover/lean4/pull/10645) 将`Stream`改名为`Std.Stream`,使名称成为
在折旧周期后,数学流可用。

* [#10649](https://github.com/leanprover/lean4/pull/10649) 将`Nat.and_distrib_right`改名为`Nat.and_or_distrib_right`。
这是要让名称与同一文件中的其他定理一致
(例如`Nat.and_or_distrib_left`))。

* [#10653](https://github.com/leanprover/lean4/pull/10653) 添加方程 Lemmas 有关( 过滤器- ) 绘图和折叠
自动自动升压器

* [#10667](https://github.com/leanprover/lean4/pull/10667)为TCP和信号添加更多的选择器。

* [#10676](https://github.com/leanprover/lean4/pull/10676)添加`IO.FS.hardLink`函数,用于创建
硬链接。

* [#10685](https://github.com/leanprover/lean4/pull/10685) 采用`LT`和`LE`例`String.ValidPos`的`LT`和`LE`例]
`String.Slice.Pos`。

* [#10686](https://github.com/leanprover/lean4/pull/10686) 采用`any`、`anyM`、`all`和`allM`
还会为它们提供润滑剂

* [#10713](https://github.com/leanprover/lean4/pull/10713) 强制执行关于`String.Pos.Raw`算术的规则。

* [#10728](https://github.com/leanprover/lean4/pull/10728) 引入 `flatMap` 迭代器组合器。它还添加了
`flatMap`至`toList`和`toArray`。

* [#10735](https://github.com/leanprover/lean4/pull/10735)将许多`String.Pos.Raw`业务转移至`String.Pos.Raw`
`String.Pos.Raw` 命名空间,最终目的是发布
`String` 名称空间以包含使用 `String.ValidPos` (待
改为`String.Pos`。

* [#10761](https://github.com/leanprover/lean4/pull/10761) 在散列图上提供迭代器。

## 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Tactics"
%%%

* [#10445](https://github.com/leanprover/lean4/pull/10445) 增加帮助者的定义,为即将到来的准备
`grind`中的投影功能支持。

* [#10447](https://github.com/leanprover/lean4/pull/10447)添加`[grind inj]`属性,用于标识喷射
`grind` 的定理。

* [#10448](https://github.com/leanprover/lean4/pull/10448) 修改“问题”的研磨诊断指纹。
这些讯息混淆了
用户,因为事实上linarith 模块继续工作,但较少
对于大多数问题,我们现在解释一下,在解决气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化、气候变化
行为时,仍然有一个待处理文件来解释变化。
`IsOrderedRing` 不详。

* [#10449](https://github.com/leanprover/lean4/pull/10449)确保电子对称模块报告的问题
仅在启用 `set_option grind.debug true` 时才显示。用户
报告说,这些信息过于分散注意力,用处不大。
它们对库开发者在说明其
库。

* [#10461](https://github.com/leanprover/lean4/pull/10461)修正`grind mbtc`产生的不必要的案件拆分
这里, `mbtc` 表示基于模型的理论组合。

* [#10463](https://github.com/leanprover/lean4/pull/10463) 加上`Nat.sub_zero`,作为`grind` 正常化规则。

* [#10465](https://github.com/leanprover/lean4/pull/10465)在 `grind mbtc` 期间跳过类似投手的`grind` 函数

* [#10466](https://github.com/leanprover/lean4/pull/10466) 减少《公约》“等效类”一节中的噪音
`grind` 诊断。它现在使用了 * 支持表达式* 的概念。
现在,它是硬编码的, 但我们可能会让它在
目前的定义是:

* [#10469](https://github.com/leanprover/lean4/pull/10469) 修正`grind` 罐体的不正确优化。
对暴露问题的例子,请看新的测试。

* [#10472](https://github.com/leanprover/lean4/pull/10472)为`grind`参数添加一个代码动作。我们需要使用
`set_option grind.param.codeAction true` 使该选项成为可能。
还添加一个修饰符,以指示 `grind` 使用“默认”模式
推断策略。

* [#10473](https://github.com/leanprover/lean4/pull/10473)确保`grind`产生的守则行动信息包括:
全面背景情况

* [#10474](https://github.com/leanprover/lean4/pull/10474)在 `grind` 中为`!` 参数修饰器添加一个 doc字符串。

* [#10477](https://github.com/leanprover/lean4/pull/10477)确保`grind`将种类内化。

* [#10480](https://github.com/leanprover/lean4/pull/10480) 修正 `grind` 中使用的平等分辨率前端中的错误。

* [#10481](https://github.com/leanprover/lean4/pull/10481) 将`grind` 中使用的定理激活功能概括化。
目标是再利用它来实施注射功能模块。

* [#10482](https://github.com/leanprover/lean4/pull/10482) 固定`@[grind inj]` 属性的符号收藏。

* [#10483](https://github.com/leanprover/lean4/pull/10483) 完成对研磨中注入函数的支持。 见
实例:
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

* [#10486](https://github.com/leanprover/lean4/pull/10486) 增加和扩充`grind` 相关文件号。

* [#10529](https://github.com/leanprover/lean4/pull/10529)为未来的`grind order`求解器添加一些帮助者定理。

* [#10553](https://github.com/leanprover/lean4/pull/10553)为新的`grind order`模块安装基础设施。

* [#10562](https://github.com/leanprover/lean4/pull/10562)简化`grind order`模块,内部化顺序
由于引入了`Offset`类型类别,它取消了`Offset`类型类别,因为它引入了
过于复杂。我们现在用更简单的
方针:
  - 至少执行 `Std.IsPreorder` 的任何类型
  - 任意订购戒指。
  - `Nat.ToInt` 适配器的`Nat`。

* [#10583](https://github.com/leanprover/lean4/pull/10583)允许用户声明附加`grind`限制
已经包括核心传播器的声明的促进者。

* [#10589](https://github.com/leanprover/lean4/pull/10589)为实施`grind order`增加帮助者定理

* [#10590](https://github.com/leanprover/lean4/pull/10590) 执行`grind order` 的证明术语工程。

* [#10594](https://github.com/leanprover/lean4/pull/10594) 在`农业'中进行理论传播的证明构建
" 顺序 " 。

* [#10596](https://github.com/leanprover/lean4/pull/10596) 执行函数,在使用的图表中添加新边边
`grind order`。 图表维持了所有
所声称的限制。

* [#10598](https://github.com/leanprover/lean4/pull/10598)在`grind order`中支持积极制约因素。
新模块已经可以解决各种问题,例如:

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

* [#10599](https://github.com/leanprover/lean4/pull/10599) 修正 `grind order` 中 `Nat` 的`Nat` 支持。本模块使用
`Nat.ToInt` 适配器。

* [#10600](https://github.com/leanprover/lean4/pull/10600)在`grind order`中支持消极制约。
实例:

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

* [#10601](https://github.com/leanprover/lean4/pull/10601)当秩序不是部分秩序时, `grind order` 将恐慌固定在 `grind order` 中
顺序。

* [#10604](https://github.com/leanprover/lean4/pull/10604) 在`grind order` 中实施`processNewEq`方法。
负责处理`grind` 电子电报所宣传的平等。

* [#10607](https://github.com/leanprover/lean4/pull/10607)为即将到来的`grind`战术模式增加基础设施,这种战术模式
将与 `conv` 模式相似。目标是从 a 扩展 `grind`
进入交互模式的终端策略:`grind => …`。

* [#10677](https://github.com/leanprover/lean4/pull/10677) 执行新的`grind`交互式`grind`
模式。虽然以后将添加许多额外的`grind`战术,但
基本框架已经投入运行。以下`grind`:
`skip`、`done`、`finish`、`lia`和
`ring`。
并删除`grind` 后退程序的概念,因其
由新框架纳入。例如:
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

* [#10695](https://github.com/leanprover/lean4/pull/10695) 确定`mutual` 区块非`macro`成员的问题
如果至少有一个宏存在,则被丢弃。

* [#10706](https://github.com/leanprover/lean4/pull/10706) 添加`have` 交互模式的`grind` 策略。
示例:
  ```lean
  example {a b c d e : Nat}
      : a > 0 → b > 0 → 2*c + e <= 2 → e = d + 1 → a*b + 2 > 2*c + d := by
    grind =>
      have : a*b > 0 := Nat.mul_pos h h_1
      lia
  ```

* [#10707](https://github.com/leanprover/lean4/pull/10707)确保`grind`交互模式中的`finish`策略失败
并报告目标未结束时的诊断。

* [#10709](https://github.com/leanprover/lean4/pull/10709) 执行 * 锚 * (也称为稳定的散列编码)
本节还介绍`grind`目标中出现的参考术语。
命令 `show_splits` 和 `show_state`。前一种显示锚
用于当前目标`grind`的候选情况拆分。

* [#10715](https://github.com/leanprover/lean4/pull/10715) 提高固定锚定稳定性(又包括稳定的散列码)
目标`grind`中的参考术语。

* [#10731](https://github.com/leanprover/lean4/pull/10731) 在`grind`交互模式中增加以下战术:
  - `focus <grind_tac_seq>`
  - `next => <grind_tac_seq>`
  - `any_goals <grind_tac_seq>`
  - `all_goals <grind_tac_seq>`
  - `grind_tac <;> grind_tac`
  - `cases <anchor>`
  - `tactic => <tac_seq>`

* [#10737](https://github.com/leanprover/lean4/pull/10737) 增加战术`linarith`、`ac`、`fail`、`first`、`try`,
`fail_if_success`和`admit`至`grind`交互模式。

* [#10740](https://github.com/leanprover/lean4/pull/10740) 改进战术`ac`、`linarith`、`lia`、`ring`
`grind` 交互模式。如果没有取得进展,这些模式现在失效。
它们还产生信息信息信息信息,如果目标
未关闭 。

* [#10746](https://github.com/leanprover/lean4/pull/10746) 执行`instantiate` 战术在`instantiate`
`grind`交互模式。用户现在可以选择全球和本地
点数。 使用锚点选择本地定理。 它还添加了
`show_thms` 显示本地定理的策略。 例如 :

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

* [#10747](https://github.com/leanprover/lean4/pull/10747) 实施`finish?`和`grind?`战术的基础设施。

* [#10748](https://github.com/leanprover/lean4/pull/10748) 执行`repeat` 交互式`grind`
模式。

* [#10767](https://github.com/leanprover/lean4/pull/10767) 执行`grind` 执行新的控制接口`grind`
将取代`SearchM` 框架。

* [#10778](https://github.com/leanprover/lean4/pull/10778) 确保`grind`交互模式是卫生的。
用于重命名无法取用名称的战术:`rename_i h_1 ... h_n`和
`next h_1 ... h_n => ..`和`expose_names`自动生成的`next h_1 ... h_n => ..`和`expose_names`
《公共关系法》还增加了用于执行
个案行动。

* [#10779](https://github.com/leanprover/lean4/pull/10779) 执行 `grind` 锚的悬停信息。
以研磨状态为参考术语的稳定的散列值代码。 锚
将被用于自动生成战术脚本 。

* [#10791](https://github.com/leanprover/lean4/pull/10791)在其`grind`项]中添加一个无声信息电文
交互式模式。只有在有
在 研磨交互式模式中,该条件为
目前我们`InfoTree`的局限性。

* [#10798](https://github.com/leanprover/lean4/pull/10798) 执行`grind` 行动`intro`、`intros`、`assertNext`,
`assertAll`。

* [#10801](https://github.com/leanprover/lean4/pull/10801) 执行`splitNext` 行动`grind`。

* [#10808](https://github.com/leanprover/lean4/pull/10808) 支持压缩自动产生的`grind`战术
序列。

* [[]]在[[[]]][[[]]][[[]]][[[]]][[[]]][[[[]]][[[]]][[[]]]][[[[]]][[[[]]][[[[]]]][[[[[]]]][[[[[]]]][[[[[]]]][[[[[[]]]][[[[[[]]]][[`splitNext`行动,用于执行`grind?`和
`finish?`。

* [#10812](https://github.com/leanprover/lean4/pull/10812) 执行`lia`、`linarith`和`ac` 行动`grind`
交互模式。

* [#10824](https://github.com/leanprover/lean4/pull/10824) 实施`grind`交互模式的`cases?` 策略。
它为选择锚锚提供了一个方便的方式。用户可以过滤
使用筛选语言的候选人。

* [#10828](https://github.com/leanprover/lean4/pull/10828) 执行检查`grind` 状态的符号符号符号
在`grind`战术中,每一种战术都可能
可选有表`| filter?` 的后缀。

* [#10833](https://github.com/leanprover/lean4/pull/10833) 实施评估`grind`战术的基础设施
`GrindM` monad。 我们将使用它来检查是否自动生成
战术可以有效地完成最初的目标。

* [#10834](https://github.com/leanprover/lean4/pull/10834) 执行`ring` 行动`grind`。

* [#10836](https://github.com/leanprover/lean4/pull/10836)在`grind` 求解器延期中为`Action`提供支持
[[[[[[]]]]]它也规定了`Solvers.mkAction`职能
使用所有注册的求解器构造 `Action`。生成的
动作是“公平”,也就是说,求解器无法阻止其他求解器
正在取得进展。

* [#10837](https://github.com/leanprover/lean4/pull/10837) 执行`finish?` 交互式`grind`
模式模式。当它成功关闭目标时,它会生成一个代码动作
使用户能够使用明确的研磨策略完成目标
步骤,即不作任何搜索。它还明确说明了哪些解决者
已经使用。

* [#10841](https://github.com/leanprover/lean4/pull/10841) 改进了`instantiate` 产生的`grind`战术
跟踪模式中的跟踪模式中的动作。它也更新 `instantiate` 的语法
战术,使其类似于`simp`。例如:

  * `instantiate only [thm1, thm2]` 即时仅满足定理`thm1` 和
`thm2`。
  * `instantiate [thm1, thm2]` 即时定理标有:
`@[grind]` 属性**和**定理`thm1`和`thm2`。

* [#10843](https://github.com/leanprover/lean4/pull/10843) 在`grind`交互模式中实施`set_option` 战术。

* [#10846](https://github.com/leanprover/lean4/pull/10846)对`instance only [...]`战术的代代
`finish?`。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Compiler"
%%%

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

## 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Pretty-Printing"
%%%

* [#10376](https://github.com/leanprover/lean4/pull/10376)修改`fun` 夹的漂亮印刷,压缩保险箱
同一`fun` 内捆绑物之间的阴影特征。例如,
现在我们看到`fun x x_1 ' ,而不是像`fun x x => 0` 那样漂亮的印刷,我们可以看到`fun x x x_1 ' 。
0`. The calculation is done per ` fun`, so for example ` fun x  id fun x
利用安全影子的优势,

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Documentation"
%%%

* [#10632](https://github.com/leanprover/lean4/pull/10632)为位数阵列添加缺失的文档字符串,并制作已有的
符合我们的风格

* [#10640](https://github.com/leanprover/lean4/pull/10640) 添加一个缺失的 docstrit 并应用我们的风格指南
字符串API。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Server"
%%%

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

* [#10584](https://github.com/leanprover/lean4/pull/10584) 导致Verso docstrings 在环境中搜索名称
提供当前名称作为
建议。

* [#10609](https://github.com/leanprover/lean4/pull/10609) 将`FileSystemWatcher` `FileSystemWatcher` `FileSystemWatcher` `FileSystemWatcher` `FileSystemWatcher``FileSystemWatcher``FileSystemWatcher``FileSystemWatcher``FileSystemWatcher`]`FileSystemWatcher``FileSystemWatcher``FileSystemWatcher`[`FileSystemWatcher`[`FileSystemWatcher`][`FileSystemWatcher`[[`FileSystemWatcher`][[[[[]]]][[[[[
在#925中引入。

* [#10619](https://github.com/leanprover/lean4/pull/10619) 修正未知标识代码动作中的错误
对于诸如`open`类筑巢式声明之类的声明,将产生非敏感建议
`open Foo.Bar`。

* [#10660](https://github.com/leanprover/lean4/pull/10660)在`end`后添加识别符号自动补全。
`set_option` 后白色空格中的补全无法完成的错误
产生完整选项列表。

* [#10662](https://github.com/leanprover/lean4/pull/10662) 用于Verso docstrings 的重新加密的语义符号符号, 之前的
更改不意外禁用它们。它还添加了一种测试来防止此操作
不再发生。

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

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Lake"
%%%

* [#9855](https://github.com/leanprover/lean4/pull/9855)为包件添加一个新的`allowImportAll`配置选项
和库。如果由上游包件或库提供,
下下游包件将能够使用该包件`import all`模块
或库库。这使软件包作者能够有选择地选择
`private` 要素,如果有任何下游货包,可以进入。

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

* [#10576](https://github.com/leanprover/lean4/pull/10576) 增加一个新的包件配置选项:`restoreAllArtifacts`。
当设定为 `true` 并启用Lake中本地文物藏匿处时, Lake
这将将所有隐藏的文物复制到构建目录中。 这样可以确保
供外部消费者使用,这些消费者期望取得结果
在构建目录中。

* [#10578](https://github.com/leanprover/lean4/pull/10578) 增加支持建筑型号的 CMake 拼写(即,
至 Lake `buildType` 配置选项。

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

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Other"
%%%

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
