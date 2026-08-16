/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Std.Data.Iterators
import Std.Data.TreeMap
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Iterators

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w u₁ u₂ w₁ w₂

open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

/-!
本模块为参考手册动态 API 文档提供中文载体。每个载体都直接转发到对应的真实声明，
因此不会重新实现运行时行为。结构体、类型类与归纳类型在后续形状审计中按真实声明镜像。
-/

/-- 保存迭代器内部状态的纯迭代器。 -/
structure c001 {α : Type w} (β : Type w) where
  /-- 当前内部状态。 -/
  internalState : α

/-- 在单子 `m` 中逐步运行、保存内部状态的迭代器。 -/
structure c002 {α : Type w} (m : Type w → Type v) (β : Type w) where
  /-- 当前内部状态。 -/
  internalState : α

/-- 一次迭代步骤：产出值、跳过产出，或结束。 -/
inductive c003 : Sort u → Sort v → Sort (max (max 1 u) v) where
  /-- 产出一个值并进入新状态。 -/
  | yield : α → β → c003 α β
  /-- 不产出值而进入新状态。 -/
  | skip : α → c003 α β
  /-- 迭代结束。 -/
  | done : c003 α β

/-- `Iter.Step` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c004 := @Iter.Step

/-- `IterM.Step` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c005 := @IterM.Step

/-- 迭代器实现：说明哪些步骤可信，并执行一步。 -/
class c006 (α : Type w) (m : Type w → Type v) (β : outParam (Type w)) where
  /-- 某一步骤是否可能发生。 -/
  IsPlausibleStep : @Std.IterM α m β → Std.IterStep (@Std.IterM α m β) β → Prop
  /-- 执行一步并附带可信性证据。 -/
  step : (it : @Std.IterM α m β) → m (Std.Shrink (@Std.PlausibleIterStep (@Std.IterM α m β) β (IsPlausibleStep it)))

/-- `PlausibleIterStep` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c007 := @PlausibleIterStep

/-- `PlausibleIterStep.yield` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c008 := @PlausibleIterStep.yield

/-- `PlausibleIterStep.skip` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c009 := @PlausibleIterStep.skip

/-- `PlausibleIterStep.done` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c010 := @PlausibleIterStep.done

/-- 迭代器不会无限执行步骤的良基性证据。 -/
class c011 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] : Prop where
  /-- 可信后继关系良基。 -/
  wf : WellFounded (@Std.IterM.IsPlausibleSuccessorOf α m β inferInstance)

/-- 迭代器不会无限跳过而不产出值的良基性证据。 -/
class c012 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] : Prop where
  /-- 可信跳过后继关系良基。 -/
  wf : WellFounded (@Std.IterM.IsPlausibleSkipSuccessorOf α m β inferInstance)

/-- `Iter.ensureTermination` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c013 := @Iter.ensureTermination

/-- `IterM.ensureTermination` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c014 := @IterM.ensureTermination

/-- 支持按输出索引访问迭代器的接口。 -/
class c015 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- 取得第 `n` 个可能输出及其证据。 -/
  nextAtIdx? : (it : @Std.IterM α m β) → (n : Nat) → m (@Std.PlausibleIterStep (@Std.IterM α m β) β (@Std.IterM.IsPlausibleNthOutputStep α β m inferInstance n it))

/-- `IterM.nextAtIdx?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c016 := @IterM.nextAtIdx?

/-- 为迭代器提供通用 `forIn` 循环实现。 -/
class c017 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β]
    (n : Type u → Type u₁) where
  /-- 执行迭代循环。 -/
  forIn : ((γ : Type w) → (δ : Type u) → (γ → n δ) → m γ → n δ) →
    (γ : Type u) → (plausible : β → γ → ForInStep γ → Prop) →
    (it : @Std.IterM α m β) → γ →
    ((b : β) → @Std.IterM.IsPlausibleIndirectOutput α β m inferInstance it b →
      (c : γ) → n {s : ForInStep γ // plausible b c s}) → n γ

/-- `IteratorLoop.defaultImplementation` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c018 := @IteratorLoop.defaultImplementation

/-- `IteratorLoop` 实现与默认实现一致的合法性证据。 -/
class c019 {β : Type w} (α : Type w) (m : Type w → Type v) (n : Type u → Type u₁)
    [Monad m] [Monad n] [Std.Iterator α m β] [Std.IteratorLoop α m n] : Prop where
  /-- 循环实现满足默认语义。 -/
  lawful : Nonempty (@Std.LawfulIteratorLoop β α m n inferInstance inferInstance inferInstance inferInstance)

/-- `Std.Shrink` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c020 := @Std.Shrink

/-- `Std.Shrink.inflate` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c021 := @Std.Shrink.inflate

/-- `Std.Shrink.deflate` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c022 := @Std.Shrink.deflate

/-- `Iter.empty` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c023 := @Iter.empty

/-- `IterM.empty` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c024 := @IterM.empty

/-- `Iter.repeat` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c025 := @Iter.repeat

/-- `Iter.step` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c026 := @Iter.step

/-- `IterM.step` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c027 := @IterM.step

/-- `Iter.finitelyManySteps` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c028 := @Iter.finitelyManySteps

/-- `IterM.finitelyManySteps` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c029 := @IterM.finitelyManySteps

/-- 用于证明有限迭代的终止度量包装。 -/
structure c030 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- 被包装的迭代器。 -/
  it : @Std.IterM α m β

/-- `Iter.finitelyManySkips` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c031 := @Iter.finitelyManySkips

/-- `IterM.finitelyManySkips` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c032 := @IterM.finitelyManySkips

/-- 用于证明迭代器生产性的终止度量包装。 -/
structure c033 (α : Type w) (m : Type w → Type v) {β : Type w} [Std.Iterator α m β] where
  /-- 被包装的迭代器。 -/
  it : @Std.IterM α m β

/-- `Iter.fold` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c034 := @Iter.fold

/-- `Iter.foldM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c035 := @Iter.foldM

/-- `Iter.length` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c036 := @Iter.length

/-- `Iter.any` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c037 := @Iter.any

/-- `Iter.anyM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c038 := @Iter.anyM

/-- `Iter.all` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c039 := @Iter.all

/-- `Iter.allM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c040 := @Iter.allM

/-- `Iter.find?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c041 := @Iter.find?

/-- `Iter.findM?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c042 := @Iter.findM?

/-- `Iter.findSome?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c043 := @Iter.findSome?

/-- `Iter.findSomeM?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c044 := @Iter.findSomeM?

/-- `Iter.atIdx?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c045 := @Iter.atIdx?

/-- `Iter.atIdxSlow?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c046 := @Iter.atIdxSlow?

/-- `IterM.drain` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c047 := @IterM.drain

/-- `IterM.fold` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c048 := @IterM.fold

/-- `IterM.foldM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c049 := @IterM.foldM

/-- `IterM.length` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c050 := @IterM.length

/-- `IterM.any` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c051 := @IterM.any

/-- `IterM.anyM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c052 := @IterM.anyM

/-- `IterM.all` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c053 := @IterM.all

/-- `IterM.allM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c054 := @IterM.allM

/-- `IterM.find?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c055 := @IterM.find?

/-- `IterM.findM?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c056 := @IterM.findM?

/-- `IterM.findSome?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c057 := @IterM.findSome?

/-- `IterM.findSomeM?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c058 := @IterM.findSomeM?

/-- `IterM.atIdx?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c059 := @IterM.atIdx?

/-- `Iter.toArray` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c060 := @Iter.toArray

/-- `IterM.toArray` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c061 := @IterM.toArray

/-- `Iter.toList` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c062 := @Iter.toList

/-- `IterM.toList` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c063 := @IterM.toList

/-- `Iter.toListRev` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c064 := @Iter.toListRev

/-- `IterM.toListRev` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c065 := @IterM.toListRev

/-- `IterM.mk` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c066 := @IterM.mk

/-- `Iter.toIterM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c067 := @Iter.toIterM

/-- `Iter.take` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c068 := @Iter.take

/-- `Iter.takeWhile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c069 := @Iter.takeWhile

/-- `Iter.toTake` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c070 := @Iter.toTake

/-- `Iter.drop` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c071 := @Iter.drop

/-- `Iter.dropWhile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c072 := @Iter.dropWhile

/-- `Iter.stepSize` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c073 := @Iter.stepSize

/-- `Iter.map` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c074 := @Iter.map

/-- `Iter.mapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c075 := @Iter.mapM

/-- `Iter.mapWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c076 := @Iter.mapWithPostcondition

/-- `Iter.uLift` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c077 := @Iter.uLift

/-- `Iter.flatMap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c078 := @Iter.flatMap

/-- `Iter.flatMapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c079 := @Iter.flatMapM

/-- `Iter.flatMapAfter` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c080 := @Iter.flatMapAfter

/-- `Iter.flatMapAfterM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c081 := @Iter.flatMapAfterM

/-- `Iter.filter` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c082 := @Iter.filter

/-- `Iter.filterM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c083 := @Iter.filterM

/-- `Iter.filterWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c084 := @Iter.filterWithPostcondition

/-- `Iter.filterMap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c085 := @Iter.filterMap

/-- `Iter.filterMapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c086 := @Iter.filterMapM

/-- `Iter.filterMapWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c087 := @Iter.filterMapWithPostcondition

/-- `Iter.zip` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c088 := @Iter.zip

/-- `Iter.attachWith` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c089 := @Iter.attachWith

/-- `IterM.toIter` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c090 := @IterM.toIter

/-- `IterM.take` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c091 := @IterM.take

/-- `IterM.takeWhile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c092 := @IterM.takeWhile

/-- `IterM.takeWhileM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c093 := @IterM.takeWhileM

/-- `IterM.takeWhileWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c094 := @IterM.takeWhileWithPostcondition

/-- `IterM.toTake` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c095 := @IterM.toTake

/-- `IterM.drop` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c096 := @IterM.drop

/-- `IterM.dropWhile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c097 := @IterM.dropWhile

/-- `IterM.dropWhileM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c098 := @IterM.dropWhileM

/-- `IterM.dropWhileWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c099 := @IterM.dropWhileWithPostcondition

/-- `IterM.stepSize` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c100 := @IterM.stepSize

/-- `IterM.map` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c101 := @IterM.map

/-- `IterM.mapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c102 := @IterM.mapM

/-- `IterM.mapWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c103 := @IterM.mapWithPostcondition

/-- `IterM.uLift` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c104 := @IterM.uLift

/-- `IterM.flatMap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c105 := @IterM.flatMap

/-- `IterM.flatMapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c106 := @IterM.flatMapM

/-- `IterM.flatMapAfter` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c107 := @IterM.flatMapAfter

/-- `IterM.flatMapAfterM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c108 := @IterM.flatMapAfterM

/-- `IterM.filter` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c109 := @IterM.filter

/-- `IterM.filterM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c110 := @IterM.filterM

/-- `IterM.filterWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c111 := @IterM.filterWithPostcondition

/-- `IterM.filterMap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c112 := @IterM.filterMap

/-- `IterM.filterMapM` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c113 := @IterM.filterMapM

/-- `IterM.filterMapWithPostcondition` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c114 := @IterM.filterMapWithPostcondition

/-- `IterM.zip` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c115 := @IterM.zip

/-- `IterM.attachWith` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c116 := @IterM.attachWith

/-- `Iter.inductSkips` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c117 := @Iter.inductSkips

/-- `IterM.inductSkips` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c118 := @IterM.inductSkips

/-- `Iter.inductSteps` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c119 := @Iter.inductSteps

/-- `IterM.inductSteps` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c120 := @IterM.inductSteps

/-- 运行单子动作并在结果上携带后置条件。 -/
structure c121 (m : Type w → Type v) (α : Type w) where
  /-- 结果应满足的性质。 -/
  Property : α → Prop
  /-- 返回满足该性质的结果。 -/
  operation : m {x : α // Property x}

/-- `Std.Iterators.PostconditionT.run` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c122 := @Std.Iterators.PostconditionT.run

/-- `Std.Iterators.PostconditionT.lift` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c123 := @Std.Iterators.PostconditionT.lift

/-- `Std.Iterators.PostconditionT.liftWithProperty` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c124 := @Std.Iterators.PostconditionT.liftWithProperty

/-- 一个值是迭代器可信的直接或间接输出。 -/
inductive c125 : {α β : Type w} → [Std.Iterator α Id β] → @Std.Iter α β → β → Prop where
  /-- 该值是当前迭代器的直接可信输出。 -/
  | direct {α β : Type w} [inst : Std.Iterator α Id β] {it : @Std.Iter α β} {out : β} :
      @Std.Iter.IsPlausibleOutput α β inst it out → @c125 α β inst it out
  /-- 经过可信后继迭代器间接得到该输出。 -/
  | indirect {α β : Type w} [inst : Std.Iterator α Id β]
      {it it' : @Std.Iter α β} {out : β} :
      @Std.Iter.IsPlausibleSuccessorOf α β inst it' it →
      @c125 α β inst it' out → @c125 α β inst it out

/-- 跨宇宙封装带有结果性质的单子动作。 -/
structure c126 (m : Type w → Type v) (α : Type u) where
  /-- 结果应满足的性质。 -/
  Property : α → Prop
  /-- 该子类型在单子宇宙中足够小的证据。 -/
  small : Std.Internal.Small {x : α // Property x}
  /-- 被封装的动作。 -/
  operation : m (@Std.Internal.USquash.{w, u} {x : α // Property x} small)

/-- `IterM.stepAsHetT` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c127 := @IterM.stepAsHetT

/-- `HetT.lift` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c128 := @HetT.lift

/-- `HetT.prun` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c129 := @HetT.prun

/-- `HetT.pure` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c130 := @HetT.pure

/-- `HetT.map` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c131 := @HetT.map

/-- `HetT.pmap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c132 := @HetT.pmap

/-- `HetT.bind` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c133 := @HetT.bind

/-- `HetT.pbind` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
noncomputable def c134 := @HetT.pbind

/-- `Iter.Equiv` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c135 := @Iter.Equiv

/-- `IterM.Equiv` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c136 := @IterM.Equiv

end Manual.ZhDocString.Iterators
