/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

section

open Lean Elab Command

/- 此处示例中的实例引用会产生很大的信息树，因此需要此设置 -/
set_option maxRecDepth 1024
set_option maxHeartbeats 650_000

/-- 手册自身所用、无需显示的类 -/
-- TODO：迁移到 v4.26.0-rc1 时，@kim-em 从此列表中移除了 `Plausible.Arbitrary`。
-- 是否应当恢复？
private def hiddenDerivable : Array Name := #[``Manual.Toml.Test]

private def derivableClasses : IO (Array Name) := do
  let handlers ← derivingHandlersRef.get
  let derivable :=
    handlers.toList.map (·.fst)
      |>.toArray
      |>.filter (fun x => !hiddenDerivable.contains x && !(`Lean).isPrefixOf x)
      |>.qsort (·.toString < ·.toString)
  pure derivable

private def checkDerivable (expected : Array Name) : CommandElabM Unit := do
  let classes ← derivableClasses
  let extra := classes.filter (· ∉ expected)
  let missing := expected.filter (· ∉ classes)
  if extra.isEmpty && missing.isEmpty then
    Verso.Log.logSilentInfo m!"Derivable classes match!"
  else
    unless extra.isEmpty do
      logError
        m!"These classes were not expected. If they should appear in the list here, \
           then add them to the call; otherwise, add them to `{.ofConstName ``hiddenDerivable}`: \
           {.andList <| extra.toList.map (.ofConstName ·)}"
    unless missing.isEmpty do
      logError
        m!"These classes were expected but not present. Check whether the text needs updating, then \
           then remove them from the call."

end


#eval checkDerivable #[``BEq, ``DecidableEq, ``Hashable, ``Inhabited, ``Nonempty, ``Ord, ``Repr, ``SizeOf, ``TypeName, ``LawfulBEq, ``ReflBEq]

open Verso Doc Elab ArgParse in
open Lean in
open SubVerso Highlighting in
@[directive_expander derivableClassList]
def derivableClassList : DirectiveExpander
  | args, contents => do
    -- 不接受参数！
    ArgParse.done.run args
    if contents.size > 0 then throwError "Expected empty directive"
    let classNames ← derivableClasses
    let itemStx ← classNames.mapM fun n => do
      let hl : Highlighted ← constTok n n.toString
      `(Inline.other {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote n.toString)])
    let theList ← `(Verso.Doc.Block.ul #[$[⟨#[Verso.Doc.Block.para #[$itemStx]]⟩],*])
    return #[theList]

open Lean Elab Command

#doc (Manual) "派生处理器" =>
%%%
tag := "deriving-handlers"
%%%

实例派生使用一张将类型类名称映射到元程序的{deftech (key := "deriving handlers")}_派生处理器_表；这些元程序为相应类型类派生实例。
可以使用 {lean}`registerDerivingHandler` 将派生处理器添加到表中；应当在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中调用它。
每个派生处理器都应具有类型 {lean}`Array Name → CommandElabM Bool`。
当用户请求派生某个类的实例时，其已注册的处理器会被逐一调用。
处理器会收到互递归块中所有需要派生该实例的名称，并且应当要么正确派生一个实例并返回 {lean}`true`，要么不产生任何效果并返回 {lean}`false`。
一旦某个处理器返回 {lean}`true`，便不会再调用后续处理器。

Lean 为以下类内置了派生处理器：

:::derivableClassList
:::

{docstring Lean.Elab.registerDerivingHandler}


::::keepEnv
:::example "派生处理器"

```imports -show
import Lean.Elab
```

{name}`IsEnum` 类的实例通过给出该类型与大小适当的 {name}`Fin` 之间的双射，表明该类型是有限枚举：
```lean
class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x
```

对于没有任何构造器接受参数、因而只是平凡枚举的归纳类型，该类的实例会非常重复。
`Bool` 的实例就是一个典型例子：
```lean
instance : IsEnum Bool where
  size := 2
  toIdx
    | false => 0
    | true => 1
  fromIdx
    | 0 => false
    | 1 => true
  to_from_id
    | 0 => rfl
    | 1 => rfl
  from_to_id
    | false => rfl
    | true => rfl
```

派生处理器参照 {lean}`IsEnum Bool` 的实现，以编程方式构造每个模式分支：
```lean
open Lean Elab Parser Term Command

def deriveIsEnum (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size = 1 then
    let env ← getEnv
    if let some (.inductInfo ind) := env.find? declNames[0] then
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for ctorName in ind.ctors do
        let c := mkIdent ctorName
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (← `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (← `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (← `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (← `(matchAltExpr| | $n => rfl))

        i := i + 1

      let cmd ← `(instance : IsEnum $(mkIdent declNames[0]) where
                    size := $(quote ind.ctors.length)
                    toIdx $tos:matchAlt*
                    fromIdx $froms:matchAlt*
                    to_from_id $to_froms:matchAlt*
                    from_to_id $from_tos:matchAlt*)
      elabCommand cmd

      return true
  return false

initialize
  registerDerivingHandler ``IsEnum deriveIsEnum
```
:::
::::
