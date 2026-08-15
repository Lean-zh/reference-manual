/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.NotationsMacros.Do

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Term (doSeq)

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean

#doc (Manual) "扩展 `do` 记法" =>
%%%
tag := "do-elab"
file := "Extending--do--Notation"
%%%

宏与精译器可以用来通过新命令和新项扩展 Lean。
除此之外，{keywordOf Lean.Parser.Term.do}`do` 记法本身也可以扩展。
对 {keywordOf Lean.Parser.Term.do}`do` 记法的扩展会定义新的 {keywordOf Lean.Parser.Term.do}`do` 元素种类。
宏会把新的 {keywordOf Lean.Parser.Term.do}`do` 元素翻译成既有的 {keywordOf Lean.Parser.Term.do}`do` 元素，而精译器则能访问更多信息，并在 Lean 的类型论中构造任意项。

:::paragraph
本章介绍可用于扩展 {keywordOf Lean.Parser.Term.do}`do` 记法的机制。
可扩展的 {keywordOf Lean.Parser.Term.do}`do` 记法是在 Lean 4.29.0 版本中引入的；在此之前，它并不可扩展。
可扩展的 {keywordOf Lean.Parser.Term.do}`do` 精译器受选项 {option}`backward.do.legacy` 控制，其默认值为 {name}`false`：

{zhOptionDocs backward.do.legacy ZhDoc.NotationsMacros.Do.backwardDoLegacy}

当 {option}`backward.do.legacy` 为 {name}`false` 时，可扩展精译器会启用。
自定义 {keywordOf Lean.Parser.Term.do}`do` 元素精译器会扩展 {ref "do-notation"}[关于单子语法的小节]中描述的脱糖过程。
:::

# 精译概览
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Elaboration-Overview"
%%%

{tech (key := "syntax kind")}[语法种类] `doElem` 表示单个 {tech (key := "do-elements")}[`do` 元素]。
由这些元素构成的序列则由语法种类 {name}`doSeq` 表示，它构成了 {keywordOf Lean.Parser.Term.do}`do` 块的主体。
{keywordOf Lean.Parser.Term.do}`do` 的精译器会对其主体中的 {name}`doSeq` 调用一个专门的精译框架，依次精译每个 `doElem`。
这个专门框架允许序列中的每个元素修改后续元素的精译方式，也能跟踪诸如外围循环（供 {keywordOf Lean.Parser.Term.doBreak}`break` 与 {keywordOf Lean.Parser.Term.doContinue}`continue` 使用）、通过 {keywordOf Lean.Parser.Term.doReturn}`return` 逃离的方式，以及可变变量集合等信息。

{keywordOf Lean.Parser.Term.do}`do` 元素的精译与项的精译非常相似。
首先，如果相关语法是一个 {tech (key := "macro")}[宏]，那么它会被展开。
这一过程会反复进行，直到宏展开的结果不再是宏为止。
接着，系统会查询一张内部表，找到与该 {keywordOf Lean.Parser.Term.do}`do` 元素语法种类相关联的精译过程。
这张表与项精译器表分开维护，因为 {keywordOf Lean.Parser.Term.do}`do` 元素精译器的类型不同。
如果某个 {keywordOf Lean.Parser.Term.do}`do` 元素仅由一个项组成，那么 Lean 解析器会把它包裹在语法种类 {name Lean.Parser.Term.doExpr}`doExpr` 中；它的精译器会调用项精译器，并确保该项具有适合当前 {keywordOf Lean.Parser.Term.do}`do` 块的正确类型。

# `do` 记法中的宏
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Macros-in--do--Notation"
%%%

宏展开发生在 {keywordOf Lean.Parser.Term.do}`do` 元素的精译期间。
{keywordOf Lean.Parser.Term.do}`do` 元素宏与项宏或命令宏在本质上并无区别；它们的差别只在于：它们是为 `doElem` 语法类别中的语法而定义的。

::::example "多路 `if`" (file := "Multi-Way if")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
open Lean.Parser.Term (doSeq)
```
作为嵌套 {keywordOf Lean.Parser.Term.doIf}`if` 项序列的一种替代，这种“多路 {keywordOf Lean.Parser.Term.doIf}`if`”把每个条件都放在同一语法层级：
```lean
syntax (name := multiIfTerm)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " term)+
    colGe "|" " else " " => " term
  ) : term
```
它是 {ref "syntax-indentation"}[缩进敏感] 的。
它可以实现为一个递归宏，产出预期的嵌套 {keywordOf Lean.Parser.Term.if}`if`：
```lean
def mkTermIf (h? : Option Ident) (g b e : Term) : MacroM Term :=
  match h? with
  | some h => `(if $h:ident : $g then $b else $e)
  | none => `(if $g then $b else $e)

macro_rules
  | `(if | $[$h?:ident :]? $g:term => $b:term | else => $e:term) =>
      mkTermIf h? g b e
  | `(if | $[$h?:ident :]? $g:term => $b:term
         | $[$h2?:ident :]? $g2:term => $b2:term
         $[| $[$hs?:ident :]? $gs:term => $bs:term]*
         | else => $e:term) => do
      mkTermIf h? g b
        (← `(if | $[$h2?:ident :]? $g2 => $b2
                $[| $[$hs?:ident :]? $gs => $bs]*
                | else => $e))
```

它可以像任何其他项一样使用：
```lean (name := multiDemo)
#eval
  let sign : Int → String := fun n =>
    if
      | n < 0 => "neg"
      | n = 0 => "zero"
      | else => "pos"
  (sign (-2), sign 0, sign 5)
```
```leanOutput multiDemo
("neg", "zero", "pos")
```

只要把这个宏放进 `doElem` 语法类别，并把多路 {keywordOf Lean.Parser.Term.doIf}`if` 的每个分支从 {name}`Term` 换成 {name}`doSeq`，它就可以改造成 {keywordOf Lean.Parser.Term.do}`do` 元素。
语法定义几乎完全一样；不过，{keywordOf Lean.Parser.Term.doIf}`else` 分支变成可选的了：
```lean
syntax (name := multiIf)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " doSeq)+
    (colGe "|" " else " " => " doSeq)?
  ) : doElem
```
同样，提供一个辅助函数，把可选的条件假设名称附加到 {keywordOf Lean.Parser.Term.doIf}`if` 上会很方便：
```lean
def mkDoIf (h? : Option Ident) (g : Term) (b : TSyntax ``doSeq)
    (els? : Option (TSyntax ``doSeq)) : MacroM (TSyntax `doElem) :=
  match h? with
  | some h =>
    `(doElem| if $h : $g then $b $[else $els?]?)
  | none =>
    `(doElem| if $g then $b $[else $els?]?)
```
其递归宏实现也几乎完全一样：
```lean
macro_rules
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                   $[| else => $e:doSeq]?) =>
      mkDoIf h? g b e
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                 | $[$h2?:ident :]? $g2:term => $b2:doSeq
                 $[| $[$hs?:ident :]? $gs:term => $bs:doSeq]*
                 $[| else => $e:doSeq]?) => do
      mkDoIf h? g b <| some
        (← `(doSeq| if | $[$h2?:ident :]? $g2 => $b2
                       $[| $[$hs?:ident :]? $gs => $bs]*
                       $[| else => $e]?))
```

它可以在 {keywordOf Lean.Parser.Term.do}`do` 中使用：
```lean
def getEven : IO { n : Nat // n % 2 = 0 ∨ n % 3 = 0} := do
  let n ← (← IO.getStdin).getLine
  let some n := n.toNat?
    | throw <| IO.userError s!"Not a Nat: {n}"
  if
    | h : n % 2 = 0 =>
      IO.println s!"{n} is even."
      return ⟨n, .inl h⟩
    | h : n % 3 = 0 =>
      IO.println s!"{n} is divisible by 3."
      return ⟨n, .inr h⟩
    | else =>
      throw <| IO.userError s!"Invalid input {n}"
```
::::

## 局限性
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Macros-in--do--Notation--Limitations"
%%%

:::paragraph
当某个扩展可以实现成宏时，通常最好就这么做。
宏维护起来简单得多，而且它们还能自动继承所展开到的目标语法实现中的缺陷修复。
不过，宏并不能实现所有可能的扩展：
 * 宏无法访问可变变量集合的信息，也无法覆写它。
 * 宏无法实现那些不能用内建控制结构表达出来的新型控制结构。
 * 宏无法把某个 {keywordOf Lean.Parser.Term.do}`do` 序列放进新的上下文（例如绑定器之下），同时仍然让它在提前返回和可变变量这两方面保持为外围 {keywordOf Lean.Parser.Term.do}`do` 块的一部分。

在这些情况下，就可能需要定义精译器。
:::

::::example "用宏冻结可变变量" (file := "Freezing Mutable Variables with a Macro")
在 {keywordOf Lean.Parser.Term.do}`do` 块内部，新的 {keywordOf Lean.Parser.Term.doLet}`let` 绑定不能遮蔽已有的 {keywordOf Lean.Parser.Term.doLet}`let mut` 绑定。
不过，许多可变变量在初始化之后其实并不会再被修改。
如果能通过去掉它们的可变性来表明这一点，往往会更方便。

目前并不存在一种现成的方式，能把某个可变变量替换成不可变变量，因此这个特性无法通过展开到某个现有 {keywordOf Lean.Parser.Term.do}`do` 元素的宏来实现——因为那样的元素并不能让该变量在后续块中变为不可变。
不过，可以把这个操作符设计成通过展开为函数调用来引入一个作用域，在这个作用域里，可变变量是不可变的：
```lean
macro "freeze " x:ident " in " body:doSeq : doElem =>
  `(doElem| (fun $x => do $body) $x)
```


虽然这看起来颇有希望，但这种基于宏的方案有严重缺点。
首先，得到的函数体会形成一个新的 {keywordOf Lean.Parser.Term.do}`do` 块。
这意味着外围块中的可变变量无法被修改：
```lean +error (name := noMutFreeze)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    y := 2 * x
  return y
```
```leanOutput noMutFreeze
Variable `y` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `y`, consider using `let y` instead
```
此外，提前出现的 {keywordOf Lean.Parser.Term.doReturn}`return` 只会退出内部的 {keywordOf Lean.Parser.Term.do}`do`，而不是外围那个；其依据是它被期望返回一个 {lean}`Unit`（这里是宇宙多态的 {name}`PUnit`）：
```lean +error (name := noInnerReturn)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    return x
  return y
```
```leanOutput noInnerReturn
Type mismatch
  x
has type
  Nat
but is expected to have type
  PUnit
```
::::

# 精译
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Elaboration"
%%%


{keywordOf Lean.Parser.Term.do}`do` 元素的精译发生在 {name Lean.Elab.Do.DoElabM}`DoElabM` 单子中。
这个单子是对 {name Lean.Elab.Term.TermElabM}`TermElabM` 的封装，并额外提供了一个 {ref "reader-monad"}[读取器] 值：{keywordOf Lean.Parser.Term.do}`do` 精译上下文。
精译器还会接收一个额外参数：描述精译 {deftech (key := "continuation")}_续延_ 的信息。
这个续延表示当前元素之后，整个 {keywordOf Lean.Parser.Term.do}`do` 块剩余的部分；其中既包含一个会精译该块剩余部分的 {name Lean.Elab.Do.DoElabM}`DoElabM` 动作，也包含该项用来引用当前精译步骤结果的名字。
与把精译后项返回给外围精译上下文的项精译器不同，{keywordOf Lean.Parser.Term.do}`do` 元素精译器会调用所提供的续延，以安排该 {keywordOf Lean.Parser.Term.do}`do` 块其余部分的精译。


{zhdocstring Lean.Elab.Do.Context ZhDoc.NotationsMacros.Do.Context}

{zhdocstring Lean.Elab.Do.MonadInfo ZhDoc.NotationsMacros.Do.MonadInfo}

{zhdocstring Lean.Elab.Do.CodeLiveness ZhDoc.NotationsMacros.Do.CodeLiveness}

为避免实现中的循环依赖，{name Lean.Elab.Do.Context.contInfo}`Context.contInfo` 与 {name Lean.Elab.Do.Context.ops}`Context.ops` 字段都是在构造后再填入内容的引用。
可以使用 {name Lean.Elab.Do.ContInfoRef.toContInfo}`ContInfoRef.toContInfo` 与 {name Lean.Elab.Do.DoOpsRef.toDoOps}`DoOpsRef.toDoOps` 取回底层数据：

{zhdocstring Lean.Elab.Do.ContInfoRef.toContInfo ZhDoc.NotationsMacros.Do.ContInfoRef.toContInfo}

{zhdocstring Lean.Elab.Do.ContInfo ZhDoc.NotationsMacros.Do.ContInfo}

{zhdocstring Lean.Elab.Do.DoOpsRef.toDoOps ZhDoc.NotationsMacros.Do.DoOpsRef.toDoOps}

{zhdocstring Lean.Elab.Do.DoOps ZhDoc.NotationsMacros.Do.DoOps}

精译器通过 {attr}`doElem_elab` 属性与语法种类关联。
它们应当具有类型 {name Lean.Elab.Do.DoElab}`DoElab`。
除了精译器之外，每个通过精译器实现的自定义 {keywordOf Lean.Parser.Term.do}`do` 元素还必须提供 {ref "do-elab-control-info"}[控制信息]。

{zhdocstring Lean.Elab.Do.DoElab ZhDoc.NotationsMacros.Do.DoElab}

:::syntax attr (title := "do 元素精译器")
```grammar
doElem_elab
```
{zhincludeDocstring Lean.Elab.Do.doElemElabAttribute ZhDoc.NotationsMacros.Do.doElemElabAttribute}
:::

此外，也可以使用 {keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules` 来同时定义精译器并把它关联到语法上。
正如 `elab_rules : term <= ty` 会把期望类型绑定到 `ty` 一样，`elab_rules : doElem <= dec` 会把续延绑定到 `dec`。

正如项精译器可以通过调用 {name Lean.Elab.Term.elabTerm}`elabTerm` 等函数，递归地对其子项再次调用精译一样，{keywordOf Lean.Parser.Term.do}`do` 元素精译器也可以精译嵌套的 {keywordOf Lean.Parser.Term.do}`do` 元素或由 {keywordOf Lean.Parser.Term.do}`do` 元素组成的序列。
要精译单个 {keywordOf Lean.Parser.Term.do}`do` 元素，请调用 {name Lean.Elab.Do.elabDoElem}`elabDoElem`。
要精译非空数组中的一组 {keywordOf Lean.Parser.Term.do}`do` 元素，请调用 {name Lean.Elab.Do.elabDoElems1}`elabDoElems1`。
要精译一整个 {keywordOf Lean.Parser.Term.do}`do` 元素序列，请调用 {name Lean.Elab.Do.elabDoSeq}`elabDoSeq`。

{zhdocstring Lean.Elab.Do.elabDoElem ZhDoc.NotationsMacros.Do.elabDoElem}

{zhdocstring Lean.Elab.Do.elabDoSeq ZhDoc.NotationsMacros.Do.elabDoSeq}

{zhdocstring Lean.Elab.Do.elabDoElems1 ZhDoc.NotationsMacros.Do.elabDoElems1}

## 单子操作
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Elaboration--Monad-Operations"
%%%

精译框架提供了若干辅助函数，让构造当前单子及其操作的应用变得更方便也更高效。

{zhdocstring Lean.Elab.Do.mkMonadApp ZhDoc.NotationsMacros.Do.mkMonadApp}

{zhdocstring Lean.Elab.Do.mkPureApp ZhDoc.NotationsMacros.Do.mkPureApp}

{zhdocstring Lean.Elab.Do.mkBindApp ZhDoc.NotationsMacros.Do.mkBindApp}

{zhdocstring Lean.Elab.Do.mkPUnitUnit ZhDoc.NotationsMacros.Do.mkPUnitUnit}

## 续延
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Elaboration--Continuations"
%%%

{keywordOf Lean.Parser.Term.do}`do` 精译续延由一个等待当前元素结果的精译器，以及若干元数据（例如该结果期望具有的类型）共同组成。

{zhdocstring Lean.Elab.Do.DoElemCont ZhDoc.NotationsMacros.Do.DoElemCont}

{zhdocstring Lean.Elab.Do.DoElemContKind ZhDoc.NotationsMacros.Do.DoElemContKind}

许多精译器都要求续延对其结果期待某个特定类型。
例如，精译器在不返回结果时，其结果类型往往应为 {name}`Unit`。
尽早检查这一类型，通常能得到更好的错误信息：

{zhdocstring Lean.Elab.Do.DoElemCont.ensureUnit ZhDoc.NotationsMacros.Do.DoElemCont.ensureUnit}

{zhdocstring Lean.Elab.Do.DoElemCont.ensureUnitAt ZhDoc.NotationsMacros.Do.DoElemCont.ensureUnitAt}

{zhdocstring Lean.Elab.Do.DoElemCont.ensureHasTypeAt ZhDoc.NotationsMacros.Do.DoElemCont.ensureHasTypeAt}

调用续延，就是向它提供当前 {keywordOf Lean.Parser.Term.do}`do` 元素的结果。
主要有三种方式可以做到这一点。
{name Lean.Elab.Do.DoElemCont.continueWithUnit}`DoElemCont.continueWithUnit` 会确保续延期待的是 {name}`Unit`，然后再调用它。
{name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` 会在一个断言代码不可达的上下文中调用续延，这通常会导致续延不生成任何代码；如果那里确实有代码，还会向用户发出警告。
{name Lean.Elab.Do.DoElemCont.mkBindUnlessPure}`DoElemCont.mkBindUnlessPure` 负责把 {keywordOf Lean.Parser.Term.do}`do` 记法标准地脱糖为对 {name}`bind` 的应用；当某个 {keywordOf Lean.Parser.Term.do}`do` 元素只是一项且该项具有单子类型时，它就用来在精译后调用续延；其中还包含一项优化：会把包裹在 {name}`pure` 外面的 {name}`bind` 替换为 {keywordOf Lean.Parser.Term.«let»}`let` 绑定。

{zhdocstring Lean.Elab.Do.DoElemCont.continueWithUnit ZhDoc.NotationsMacros.Do.DoElemCont.continueWithUnit}

{zhdocstring Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode ZhDoc.NotationsMacros.Do.DoElemCont.elabAsSyntacticallyDeadCode}

{zhdocstring Lean.Elab.Do.DoElemCont.mkBindUnlessPure ZhDoc.NotationsMacros.Do.DoElemCont.mkBindUnlessPure}

:::example "调用续延" (file := "Invoking Continuations")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
```
一种内建语法 {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip` 的变体——它等价于 {lean (type := "Option Unit")}`pure ()`——可以用一个精译器来实现：它立即用 {name}`Unit` 调用自己的续延。
为了得到更好的错误信息，它还会断言该续延期望的结果类型是 {name}`Unit`。
```lean
syntax (name := doNothing) "nothing" : doElem

@[doElem_elab doNothing]
def elabDoNothing : DoElab := fun stx dec => do
  let dec ← dec.ensureUnitAt stx
  dec.continueWithUnit
```
为了给控制结构生成代码，{keywordOf Lean.Parser.Term.do}`do` 元素精译框架需要知道每个元素可能执行哪些副作用。
这些 {ref "do-elab-control-info"}[控制信息] 通过 {attr}`doElem_control_info` 属性注册。
由于 {keywordOf doNothing}`nothing` 既不会修改可变变量，也不会抛出异常、提前终止循环，或做出任何其他动作，因此它的控制信息就是 {name}`ControlInfo.pure`。
```lean
@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

它确实等价于 {lean (type := "Option Unit")}`pure ()`：
```lean (name := doNothing)
#eval show Option Unit from do nothing
```
```leanOutput doNothing
some ()
```
:::

:::example "用 `elab_rules` 精译 `do` 元素" (file := "Elaborating do-elements with elab_rules")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
```
作为 {keywordOf doNothing}`nothing` 的另一种实现版本——它等价于内建语法 {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip`——可以使用 {keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules`，作为带 {attr}`doElem_elab` 属性的显式精译器的替代方案。
```lean
syntax (name := doNothing) "nothing" : doElem

elab_rules : doElem <= dec
  | `(doElem|nothing%$tk) => do
    let dec ← dec.ensureUnitAt tk
    dec.continueWithUnit

@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

它等价于 {lean (type := "Option Unit")}`pure ()`：
```lean (name := doNothing')
#eval show Option Unit from do nothing
```
```leanOutput doNothing'
some ()
```
:::

由于精译器是显式调用其续延，而不是简单返回一个值，因此它可以控制精译的上下文。
尤其是，它可以使用 {name}`withReader` 修改上下文，也可以多次调用续延，以支持带分支的控制结构。
为了防止代码大小爆炸，续延会在 {name Lean.Elab.Do.DoElemCont.kind}`DoElemCont.kind` 中跟踪自己是否可能被精译多次。
如果一个续延可能被多次调用，那么它就是 {deftech (key := "duplicable")}_可复制_ 的；否则它就是 {deftech (key := "nonduplicable")}_不可复制_ 的。
不可复制的续延可以通过 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont` 转换成可复制的续延。

{zhdocstring Lean.Elab.Do.DoElemCont.withDuplicableCont ZhDoc.NotationsMacros.Do.DoElemCont.withDuplicableCont}

不可达代码无需精译。
当某个 {keywordOf Lean.Parser.Term.do}`do` 元素的精译器已经检测到续延精译的结果不可达时，它可以直接返回自己的结果项，而不是把它交给精译续延。
它应当构造一个足以证明程序可以在此放弃执行的项，例如对 {name}`False.elim` 的调用。
在返回这个项之前，它应当对续延调用 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode`，以警告用户：续延原本会精译的那段代码是不可达的。

:::example "不可达代码" (file := "Unreachable Code")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
```

操作符 {keywordOf doAbsurd}`absurd` 在给出 {name}`False` 的证明时，会把代码标记为不可达；这说明当前局部上下文在逻辑上是不一致的。
如果传入了证明，它就使用该证明；否则，它会尝试一些自动化手段。
```lean
syntax (name := doAbsurd) "absurd" (" by " tacticSeq)? : doElem
```

由于 {keywordOf doAbsurd}`absurd` 永远不会返回，而且控制流也不可能越过它继续执行，因此它的控制信息会把 {name Lean.Elab.Do.ControlInfo.numRegularExits}`numRegularExits` 设为 {lean}`0`，并把 {name Lean.Elab.Do.ControlInfo.noFallthrough}`noFallthrough` 设为 {lean}`true`：
```lean
@[doElem_control_info doAbsurd]
def inferAbsurd : ControlInfoHandler := fun _ =>
  return { numRegularExits := 0, noFallthrough := true }
```

精译器首先提取证明语法；如果未提供，就回退到默认值。
然后，它会把该证明精译为 False 的一个证明。
如果成功，它就会用 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` 把剩余的 {keywordOf Lean.Parser.Term.do}`do` 序列标记为死代码，并把 {name}`False.elim` 作为结果项直接返回，而不是交给续延。
{name}`False.elim` 会接收该项所期望具有的类型；这个类型通过 {name}`Lean.Elab.Do.mkMonadApp` 与结果类型共同确定。
这里必须使用 {name Lean.Elab.Do.Context.doBlockResultType}`Do.Context.doBlockResultType`，而不是续延的结果类型，因为 {ref "do-elab-effect-lift"}[效应提升] 可能已经在局部修改了该类型。
```lean
@[doElem_elab doAbsurd]
def elabAbsurd : DoElab := fun stx dec => do
  let `(doElem| absurd $[by $tac?]?) := stx
    | throwUnsupportedSyntax
  let proofStx : Term ←
    if let some tac := tac? then
      `(by $tac)
    else
      `(by first | contradiction | grind)
  let proof ← elabTermEnsuringType proofStx (mkConst ``False)
  dec.elabAsSyntacticallyDeadCode
  let ty ← mkMonadApp (← read).doBlockResultType
  return (← Meta.mkAppOptM ``False.elim #[some ty, some proof])
```

{keywordOf doAbsurd}`absurd` 可以利用嵌套条件分支中积累的信息，断定 {keywordOf Lean.Parser.Term.doIf}`else` 子句不可达：
```lean
#eval show Id (String × String × String) from do
  let classify : Nat → String := fun n => Id.run do
    if n < 3 then return "small"
    else if h1 : n < 10 then return "medium"
    else if h2 : n ≥ 10 then return "large"
    else absurd
  return (classify 1, classify 5, classify 99)
```

由于调用了 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode`，位于 {keywordOf doAbsurd}`absurd` 之后的步骤会收到死代码警告：
```lean (name := absurdOut)
def xs := #[1, 3, 5]
theorem xs_all_odd : ∀ x, x ∈ xs → x % 2 = 1 := by
  simp [xs]

#eval show Id Nat from do
  for h : n in 0...5 do
    let k := n * 2
    if h' : k ∈ xs then
      absurd by grind [xs_all_odd]
      return k
  pure 100
```
```leanOutput absurdOut
This `do` element and its control-flow region are dead code. Consider removing it.
```
不过，它确实可以成功运行：
```leanOutput absurdOut
100
```
:::

## 控制流：`return`、`break` 与 `continue`
%%%
tag := "do-elab-return-continue-break"
%%%

{keywordOf Lean.Parser.Term.do}`do` 记法支持三种非局部跳转指令：{keywordOf Lean.Parser.Term.doReturn}`return` 用于提前终止整个 {keywordOf Lean.Parser.Term.do}`do` 块；{keywordOf Lean.Parser.Term.doBreak}`break` 用于提前终止循环；{keywordOf Lean.Parser.Term.doContinue}`continue` 用于提前终止循环中的单次迭代。
{keywordOf Lean.Parser.Term.doReturn}`return` 总是允许出现，而 {keywordOf Lean.Parser.Term.doBreak}`break` 与 {keywordOf Lean.Parser.Term.doContinue}`continue` 只在循环体内部合法。
在精译过程中，这三种跳转都由续延来表示。

{zhdocstring Lean.Elab.Do.getReturnCont ZhDoc.NotationsMacros.Do.getReturnCont}

{zhdocstring Lean.Elab.Do.getBreakCont ZhDoc.NotationsMacros.Do.getBreakCont}

{zhdocstring Lean.Elab.Do.getContinueCont ZhDoc.NotationsMacros.Do.getContinueCont}

这三个续延会借助辅助函数 {name Lean.Elab.Do.enterLoopBody}`enterLoopBody` 安装到上下文中。

{zhdocstring Lean.Elab.Do.enterLoopBody ZhDoc.NotationsMacros.Do.enterLoopBody}

:::example "单次迭代循环" (file := "Single-Iteration Loop")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
```
单次迭代循环 {keywordOf doOnce}`once` 会执行其主体一次；如果在主体中遇到 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doContinue}`continue`，就会跳到循环末尾：
```lean
syntax (name := doOnce) "once " doSeq : doElem
```
它的控制信息基于其主体的控制信息。
{keywordOf doOnce}`once` 自身永远不会再向外 break 或 continue，因为它会在自己的主体内部处理 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue`；因此它会把 {name ControlInfo.breaks}`breaks` 和 {name ControlInfo.continues}`continues` 设为 {lean}`false`。
{name ControlInfo.numRegularExits}`numRegularExits` 表示控制流到达 {keywordOf doOnce}`once` 之后那段代码的次数。
主体的正常落空、{keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 都会把控制流转移到循环末尾，因此控制流离开一个 {keywordOf doOnce}`once` 的次数至多为一次。
因此，只要主体能以这些方式中的任意一种退出，{name ControlInfo.numRegularExits}`numRegularExits` 就是 {lean}`1`；否则就是 {lean}`0`，此时还会设置 {name ControlInfo.noFallthrough}`noFallthrough`。
```lean
@[doElem_control_info doOnce]
def inferOnce : ControlInfoHandler := fun stx => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  let exits :=
    bodyInfo.numRegularExits > 0 ||
    bodyInfo.breaks ||
    bodyInfo.continues
  return { bodyInfo with
    breaks := false
    continues := false
    numRegularExits := if exits then 1 else 0
    noFallthrough := !exits
  }
```
{keywordOf doOnce}`once` 的实际精译器使用 {name Lean.Elab.Do.enterLoopBody}`enterLoopBody`，把该精译器的整体续延与主体内部的 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 续延关联起来。
由于精译后的主体可能从多个位置抵达该续延，精译器会对这些使用进行计数。
主体的控制信息并不说明 {keywordOf Lean.Parser.Term.doBreak}`break` 与 {keywordOf Lean.Parser.Term.doContinue}`continue` 可能被调用多少次，因此这里把它们都安全地近似为两个出口，以确保只要二者之一被使用，续延就会被复制。
近似后的总使用次数会传给 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont`；当使用次数大于一时，它会共享续延而不是在每次使用处都复制它，从而避免代码爆炸。
这里直接根据主体计算这个次数，因为控制信息处理器报告的值最多只有 {lean}`1`，并不能反映内部的实际使用次数。
```lean
@[doElem_elab doOnce]
def elabOnce : DoElab := fun stx dec => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let dec ← dec.ensureUnit
  let bodyInfo ← InferControlInfo.ofSeq body
  let numRegularExits :=
    bodyInfo.numRegularExits +
    (if bodyInfo.breaks then 2 else 0) +
    (if bodyInfo.continues then 2 else 0)
  dec.withDuplicableCont { bodyInfo with numRegularExits } fun dec => do
    let returnCont ← getReturnCont
    let exitCont := dec.continueWithUnit
    enterLoopBody exitCont exitCont returnCont do
      elabDoSeq body dec
```

{keywordOf doOnce}`once` 可用于终止某个计算片段，而不会像 {keywordOf Lean.Parser.Term.doReturn}`return` 那样终止整个 {keywordOf Lean.Parser.Term.do}`do` 块：
```lean (name := once)
#eval show Id Nat from do
  let mut x := 0
  once
    x := x + 2
    if x % 2 = 0 then break
    x := 0
  return x
```
```leanOutput once
2
```
:::

## 控制信息
%%%
tag := "do-elab-control-info"
%%%

除了精译器之外，自定义 {keywordOf Lean.Parser.Term.do}`do` 元素还必须提供 {deftech (key := "control information")}_控制信息_。
这描述了自定义元素如何与外围控制结构和可变变量交互。
控制信息使 Lean 能够生成合适的代码；特别是，它让 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont` 能分析续延将要精译的代码，从而改进生成结果。
控制信息之所以与精译器分离，是因为精译器需要在真正精译之前分析子元素的_语法_，才能知道应当如何组织自己的续延。
*自定义 {keywordOf Lean.Parser.Term.do}`do` 元素必须提供准确的控制信息。错误的控制信息可能导致错误的代码生成。*

:::syntax attr (title := "do 元素控制信息")
```grammar
doElem_control_info
```
{zhincludeDocstring Lean.Elab.Do.controlInfoElemAttribute ZhDoc.NotationsMacros.Do.controlInfoElemAttribute}
:::

{zhdocstring Lean.Elab.Do.ControlInfoHandler ZhDoc.NotationsMacros.Do.ControlInfoHandler}

如果某个 {keywordOf Lean.Parser.Term.do}`do` 元素既不重新赋值变量，也不会提前返回或终止执行，那么处理器可以返回 {name Lean.Elab.Do.ControlInfo.pure}`ControlInfo.pure`。
如果它表示一段没有常规出口且也没有其他控制效应的代码，那么处理器可以返回 {name Lean.Elab.Do.ControlInfo.empty}`ControlInfo.empty`；否则，应把 {name Lean.Elab.Do.ControlInfo.numRegularExits}`ControlInfo.numRegularExits` 设为 {lean}`0`，把 {name Lean.Elab.Do.ControlInfo.noFallthrough}`ControlInfo.noFallthrough` 设为 {lean}`true`，同时记录任何提前返回、重新赋值或循环终止行为。


{zhdocstring Lean.Elab.Do.ControlInfo ZhDoc.NotationsMacros.Do.ControlInfo}

{zhdocstring Lean.Elab.Do.ControlInfo.pure ZhDoc.NotationsMacros.Do.ControlInfo.pure}

{zhdocstring Lean.Elab.Do.ControlInfo.empty ZhDoc.NotationsMacros.Do.ControlInfo.empty}

如果某个 {keywordOf Lean.Parser.Term.do}`do` 元素自身又包含其他 {keywordOf Lean.Parser.Term.do}`do` 元素，那么它可以使用组合子 {name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` 和 {name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` 来合并其子元素的控制信息。
{name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` 用于顺序步骤，{name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` 用于合并控制流分支。

{zhdocstring Lean.Elab.Do.ControlInfo.sequence ZhDoc.NotationsMacros.Do.ControlInfo.sequence}

{zhdocstring Lean.Elab.Do.ControlInfo.alternative ZhDoc.NotationsMacros.Do.ControlInfo.alternative}

一般来说，应当使用 {name Lean.Elab.Do.inferControlInfoElem}`inferControlInfoElem` 或 {name Lean.Elab.Do.inferControlInfoSeq}`inferControlInfoSeq` 来计算控制信息。

{zhdocstring Lean.Elab.Do.inferControlInfoElem ZhDoc.NotationsMacros.Do.inferControlInfoElem}

{zhdocstring Lean.Elab.Do.inferControlInfoSeq ZhDoc.NotationsMacros.Do.inferControlInfoSeq}

在某些高级情形下，可能需要使用 {namespace}`Lean.Elab.Do.InferControlInfo` 中的某个函数：

{zhdocstring Lean.Elab.Do.InferControlInfo.ofElem ZhDoc.NotationsMacros.Do.InferControlInfo.ofElem}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofSeq ZhDoc.NotationsMacros.Do.InferControlInfo.ofSeq}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofOptionSeq ZhDoc.NotationsMacros.Do.InferControlInfo.ofOptionSeq}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofLetOrReassign ZhDoc.NotationsMacros.Do.InferControlInfo.ofLetOrReassign}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow ZhDoc.NotationsMacros.Do.InferControlInfo.ofLetOrReassignArrow}

## 可变变量
%%%
tag := "The-Lean-Language-Reference--Notations-and-Macros--Extending--do--Notation--Elaboration--Mutable-Variables"
%%%

上下文中的一个重要组成部分，是当前正在精译的 {keywordOf Lean.Parser.Term.do}`do` 元素可用的那组可变变量。
这组信息存放在两个字段中：{name Lean.Elab.Do.Context.mutVars}`mutVars` 给出最初绑定这些变量的标识符，而 {name Lean.Elab.Do.Context.mutVarDefs}`mutVarDefs` 则把它们的名字映射到表示这些变量的局部变量上。
由于 {tech (key := "hygiene")}[卫生] 机制，{name Lean.Elab.Do.Context.mutVars}`mutVars` 中的标识符带有 {tech (key := "macro scopes")}[宏作用域]；不过，{inst}`ToMessageData MutVar` 实例会自动将其移除。
如果以其他方式显示这些名字，那么在构造面向用户的错误信息之前，应先使用 {name}`Name.simpMacroScopes` 去除宏作用域。

{zhdocstring Lean.Elab.Do.MutVar ZhDoc.NotationsMacros.Do.MutVar}

每个可变变量都至少对应一个精译后的变量（{name}`Expr.fvar`）。
这些精译后的变量存在于一个跟踪其用户可见名称的局部上下文中。
变量修改通过一个遮蔽性的 {keywordOf Lean.Parser.Term.«let»}`let` 绑定来实现，随后 {keywordOf Lean.Parser.Term.do}`do` 块中的步骤会在这样一个上下文中被精译：在该上下文里，这个遮蔽性的 {keywordOf Lean.Parser.Term.«let»}`let` 就是该变量用户可见名称所对应的绑定。
使用标准精译辅助函数 {name}`Lean.Meta.getFVarFromUserName` 和 {name}`Lean.Meta.getLocalDeclFromUserName`，可以取回与某个用户名关联的局部变量；使用 {name}`TSyntax.getId` 则可把 {name}`Ident` 转换成可供查找的用户名。

当某个可变变量通过 {keywordOf Lean.Parser.Term.doLet}`let mut` 建立时，会创建一个 {keywordOf Lean.Parser.Term.«let»}`let` 绑定来表示它，并把初始变量的绑定标识符与 {name}`Expr.fvar` 加入围绕续延所使用的上下文；这个续延会在 {name}`withReader` 下被调用，以便加入新变量。
在建立该 {keywordOf Lean.Parser.Term.«let»}`let` 绑定之后，使用 {name Lean.Elab.Do.declareMutVar}`declareMutVar` 来注册一个可变变量，或注册它们组成的数组。

{zhdocstring Lean.Elab.Do.declareMutVar ZhDoc.NotationsMacros.Do.declareMutVar}

{zhdocstring Lean.Elab.Do.declareMutVars ZhDoc.NotationsMacros.Do.declareMutVars}

若要确保某个标识符指向的是可变变量，请使用 {name Lean.Elab.Do.throwUnlessMutVarDeclared}`throwUnlessMutVarDeclared`：

{zhdocstring Lean.Elab.Do.throwUnlessMutVarDeclared ZhDoc.NotationsMacros.Do.throwUnlessMutVarDeclared}

{zhdocstring Lean.Elab.Do.throwUnlessMutVarsDeclared ZhDoc.NotationsMacros.Do.throwUnlessMutVarsDeclared}

::::example "跟踪可变变量" (file := "Tracing Mutable Variables")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
```
新语法 {keywordOf dbgMut}`dbg_mut` 会跟踪所有可变变量的当前值。

```lean
syntax (name := dbgMut) "dbg_mut" : doElem

@[doElem_elab dbgMut] def elabDbgMut : DoElab := fun _stx cont => do
  let ctx ← readThe Do.Context
  let parts : Array Term ← ctx.mutVars.mapM fun (x : MutVar) => do
    let nameLit := x.getId.simpMacroScopes.toString
    `(term| s!"{$(quote nameLit)} = {repr $(x.ident)}")
  let msg ← `(term| String.intercalate ", " [$parts,*])
  elabDoElem (← `(doElem| dbg_trace $msg)) cont
```

{keywordOf dbgMut}`dbg_mut` 没有任何值得特别记录的控制信息。
```lean
@[doElem_control_info dbgMut]
def dbgMut.control : ControlInfoHandler := fun _ => do return .pure
```

跟踪一个计算 Fibonacci 数的循环，可以显示所有中间状态：
```lean (name := mutDbg)
#eval show IO Unit from do
  let mut x := 1
  let mut y := 1
  for _ in 0...5 do
    let z := y
    dbg_mut
    y := x + y
    x := z
```
```leanOutput mutDbg
x = 1, y = 1
x = 1, y = 2
x = 2, y = 3
x = 3, y = 5
x = 5, y = 8
```
::::

用于可变变量的内建精译器会处理许多细微细节，例如把生成出的每一个可变变量 {keywordOf Lean.Parser.Term.«let»}`let` 绑定注册为别名，以便 IDE 能提供合适的反馈。
只要可能，最好复用这些内建精译器：要么通过宏，要么通过在适当语法上调用 {name Lean.Elab.Do.elabDoElem}`elabDoElem`。

:::example "修改变量" (file := "Mutating Variables")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
```
操作符 {keywordOf doCensor}`censor` 会把所有可变变量替换成其类型的 {name}`Inhabited` 实例所定义的默认值。

```lean
syntax (name := doCensor) "censor" : doElem

@[doElem_elab doCensor]
def elabCensor : DoElab := fun stx dec => do
  let vars := (← readThe Do.Context).mutVars
  let dec ← dec.ensureUnitAt stx
  if h : vars.size = 0 then
    logErrorAt stx "There are no mutable variables to censor."
    dec.continueWithUnit
  else
    let assigns ← vars.mapM fun v =>
      `(doElem| $(v.ident):ident := Inhabited.default)
    elabDoElems1 assigns dec
```

{keywordOf Lean.Parser.Term.do}`do` 精译上下文在控制信息处理器中不可用，因此无法精确返回“所有被修改的可变变量集合”。
不过，把所有局部变量的用户名称作为一个过近似是合适的：
```lean
@[doElem_control_info doCensor]
def doCensor.control : ControlInfoHandler := fun _ => do
  return { ControlInfo.pure with
      reassigns := (← getLCtx).decls.map (·.map (·.userName))
        |>.foldl (init := .empty) fun
          | names, some n => names.insert n
          | names, none => names
    }
```

使用 {keywordOf doCensor}`censor` 之后，所有可变变量都会被重置为各自类型的默认值：
```lean (name := censor)
#eval show IO Unit from do
  let mut x := 0
  let mut c := 'm'
  x := x + 1
  IO.println s!"x: {x}, c: {c}"
  c := 'f'
  IO.println s!"x: {x}, c: {c}"
  censor
  IO.println s!"x: {x}, c: {c}"
```
```leanOutput censor
x: 1, c: m
x: 1, c: f
x: 0, c: A
```

:::

## 效应提升
%%%
tag := "do-elab-effect-lift"
%%%

许多有用的单子运算符都接受一个返回类型位于该单子中的函数，并以某种修改过的方式运行这个函数。
例如 {name}`withReader`、{name}`tryCatch` 与 {name}`IO.FS.withFile`。
像 {name}`tryCatch` 这样的函数拥有专门语法，可以让“可能抛出异常的代码”和“处理该异常的代码”都成为外围 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，因此它们也就可以重新赋值可变变量，或提前返回等。
这些其他运算符则没有这样的语法。

{keywordOf Lean.Parser.Term.do}`do` 元素精译器可以安排：在精译后表达式中传给这些运算符的那个函数，其函数体仍被当作源 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，就像异常处理语法那样。
这借助 {name Lean.Elab.Do.EffectForwarder}`EffectForwarder` 完成；它会围绕内部的 {keywordOf Lean.Parser.Term.do}`do` 元素序列和函数本身生成合适的包装代码。
分三步进行：
1. 根据内部序列的控制信息与当前元素的续延，用 {name Lean.Elab.Do.EffectForwarder.ofCont}`EffectForwarder.ofCont` 为该内部序列创建一个 {name Lean.Elab.Do.EffectForwarder}`EffectForwarder`。
2. 使用 {name Lean.Elab.Do.EffectForwarder.lift}`EffectForwarder.lift` 精译内部序列；它会向内部精译器提供一个合适的续延，用来生成包装代码。
3. 精译器不会调用原始续延，而是调用由 {name Lean.Elab.Do.EffectForwarder.restoreCont}`EffectForwarder.restoreCont` 生成的续延；这个续延会为结果添加合适的解包代码。

这些提升代码与 Lean 内建 {ref "monad-transformers"}[单子变换器] 的实现很相似。
例如，如果内部的 {keywordOf Lean.Parser.Term.do}`do` 序列修改了某个变量，那么包装与解包代码就会像 {name}`StateT` 那样，安排把该变量传入被提升的代码并以元组形式返回。
如果内部的 {keywordOf Lean.Parser.Term.do}`do` 序列可能抛出异常，那么提升后的版本就类似于一次对 {name}`ExceptT` 的使用。

{zhdocstring Lean.Elab.Do.EffectForwarder ZhDoc.NotationsMacros.Do.EffectForwarder}

{zhdocstring Lean.Elab.Do.EffectForwarder.ofCont ZhDoc.NotationsMacros.Do.EffectForwarder.ofCont}

{zhdocstring Lean.Elab.Do.EffectForwarder.lift ZhDoc.NotationsMacros.Do.EffectForwarder.lift}

{zhdocstring Lean.Elab.Do.EffectForwarder.restoreCont ZhDoc.NotationsMacros.Do.EffectForwarder.restoreCont}

:::example "{name}`withReader` 的语法" (file := "Syntax for withReader")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term
```

在 {keywordOf Lean.Parser.Term.do}`do` 块中，{keywordOf doLocally}`locally` 允许在修改过的 {name}`MonadReader` 上下文中运行一段 {keywordOf Lean.Parser.Term.do}`do` 元素序列：

```lean
syntax (name := doLocally)
  "locally " ident " => " termBeforeDo " do " doSeq : doElem
```

{name Lean.Parser.Term.termBeforeDo}`termBeforeDo` 解析器会匹配那些自身不包含括号或方括号之外的 {keywordOf Lean.Parser.Term.do}`do` 的 Lean 项。
由于这个新语法包含一段 {keywordOf Lean.Parser.Term.do}`do` 元素序列，因此它的控制信息必须从这些元素计算出来：
```lean
@[doElem_control_info doLocally]
def inferLocally : ControlInfoHandler := fun stx => do
  let `(doElem| locally $_:ident => $_ do $seq) := stx
    | throwUnsupportedSyntax
  InferControlInfo.ofSeq seq
```

实际的精译器首先会计算主体的控制信息，然后根据该控制信息和原始续延导出一个控制提升器。
这个控制提升器可以精译主体；它会向精译器提供自己的续延。
构造 {name}`withReader` 的应用时，使用的是常规项精译技术；其中要特别注意，函数参数必须以适用于该单子的正确宇宙层级上的非依赖函数类型来精译（这个宇宙可在 {name}`Context.monadInfo` 的 {name}`MonadInfo.u` 中取得）。
最后，还会再次使用控制提升器，为完整精译结果重建一个合适的续延：
```lean
@[doElem_elab doLocally] def elabDoLocally : DoElab := fun stx dec => do
  let `(doElem| locally $x:ident => $e do $seq) := stx
    | throwUnsupportedSyntax
  let lifter ← EffectForwarder.ofCont (← inferControlInfoElem stx) dec
  let body ← lifter.lift (elabDoSeq seq)
  let ρ ← Meta.mkFreshExprMVar (mkSort (.succ (← read).monadInfo.u))
  let f ← Term.elabTermEnsuringType (← `(fun $x => $e)) (← mkArrow ρ ρ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrapped ← Meta.mkAppM ``MonadWithReaderOf.withReader #[f, body]
  (← lifter.restoreCont).mkBindUnlessPure wrapped
```

有了这个精译器之后，即便某个值由 {name}`ReaderT` 提供，也可以在局部覆写它，同时依然允许那些与外围 {keywordOf Lean.Parser.Term.do}`do` 块绑定在一起的效应继续工作：
```lean (name := locallyDemo)
abbrev App := ReaderT Nat Id

#eval show Id Nat from do
  Id.run <| (·.run 5) <| show App Nat from do
    let mut total := 0
    total := total + (← read)
    locally r => r + 100 do
      -- 修改外层变量
      total := total + (← read)
      if (← read) > 1000 then
        -- 从外层块提前返回
        return 999
    return total
```
```leanOutput locallyDemo
110
```
:::

:::example "局部破坏不变式" (file := "Locally Violating Invariants")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term Meta
open Lean.Parser.Term (doSeq)
```
当某个可变变量需要维持某种不变式时，通常最方便的做法是使用子类型。
不过，子类型的缺点在于：这个不变式必须_始终_成立；你不能在局部打破它，再在稍后重新建立。
虽然也可以为此使用第二个可变变量，但那样会让代码变得杂乱且容易出错。
借助对 {keywordOf Lean.Parser.Term.do}`do` 记法的适当扩展，就可以很方便地在局部打破并重新建立不变式。

第一步是为这个操作建立语法。
{keywordOf openMutPure}`open mut` 会把该子类型“打开”，使其中包含的数据在嵌套块中摆脱谓词约束。
当该块结束后，用户必须证明或检查该不变式成立；如果在 {keywordOf openMutPure}`invariant` 部分放置一个 {keywordOf Lean.Parser.Term.do}`do` 块，就表示应当执行一次动态检查。
第二个语法定义显式给出了高优先权以避免歧义，从而确保只要出现 {keywordOf Lean.Parser.Term.do}`do` 块，就会优先使用它。
```lean
syntax (name := openMutPure)
  "open" "mut" ident "do" doSeq "invariant" term : doElem

syntax (name := openMutMon) (priority := high)
  "open" "mut" ident "do" doSeq "invariant" "do" doSeq : doElem
```

这些操作的控制信息处理器是嵌入其中的 {name}`doSeq` 语法的函数：
```lean
@[doElem_control_info openMutPure, doElem_control_info openMutMon]
def openMutInfo : ControlInfoHandler := fun
  | `(doElem|open mut $x do $steps invariant do $steps') => do
    let info ← inferControlInfoSeq steps
    let info' ← inferControlInfoSeq steps'
    return info.sequence info'
  | `(doElem|open mut $x do $steps invariant $tm:term) =>
    inferControlInfoSeq steps
  | _ => throwUnsupportedSyntax
```

这个精译器的核心是一个辅助函数，它会做如下几件事：
1. 确保给定名称确实引用了一个子类型变量，并提取其底层类型与谓词。
2. 从该子类型中取出内部值。
3. 用 {keywordOf Lean.Parser.Term.«let»}`let` 绑定这个内部值，把这个 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量建立为别名，并把它安排成可变变量。
4. 用一个会调用“关闭”该子类型、重新建立不变式的精译器的续延来精译主体。
```lean
def openMutBody (x : Ident) (seq : TSyntax ``doSeq)
    (mkClose : (p outerTy : Expr) → (base : FVarId) → DoElabM Expr) :
    DoElabM Expr := do
  -- 确保它是可变变量
  throwUnlessMutVarDeclared x
  -- 确保它是子类型
  let outerDecl ← getLocalDeclFromUserName x.getId
  let ty ← whnf outerDecl.type
  let (``Subtype, #[α, p]) := ty.getAppFnArgs
    | throwError "`open mut`: `{x}` is not a subtype, but is a `{ty}`"

  -- 从子类型中取出值
  let base := outerDecl.fvarId
  let init ← mkAppM ``Subtype.val #[outerDecl.toExpr]

  -- 建立 let 绑定并继续
  withLetDecl x.getId α init (nondep := false) fun innerX => do
    addLocalVarInfo x innerX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := innerX.fvarId!, baseId := base
    }
    let bodyCont : DoElemCont := {
      resultName := ← mkFreshUserName `__r, resultType := ← mkPUnit
      k := mkClose p outerDecl.type base
    }
    mkLetFVars #[innerX] (← declareMutVar x do elabDoSeq seq bodyCont)
```

调用 {name}`addLocalVarInfo` 会把精译后 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量与源码中的标识符之间的联系告知语言服务器，从而支持例如悬停显示类型信息等特性。
{name}`pushInfoLeaf` 与 {name}`Info.ofFVarAliasInfo` 联合使用时，会把这个 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量注册为已有绑定的别名。

关闭纯版本时，需要引入一个新的 {keywordOf Lean.Parser.Term.«let»}`let` 绑定，用更新后的值和证明来遮蔽并别名化这个可变变量。
```lean
def rebindMut (x : Ident) (outerTy repacked : Expr) (base : FVarId)
    (dec : DoElemCont) : DoElabM Expr :=
  withLetDecl x.getId outerTy repacked (nondep := false) fun newX => do
    addLocalVarInfo x newX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := newX.fvarId!, baseId := base
    }
    mkLetFVars #[newX] (← dec.continueWithUnit)

```

纯版本的精译器把上述两个部分连接起来：
```lean
@[doElem_elab openMutPure]
def elabOpenMutPure : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant $prf:term) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let proof ← Term.elabTermEnsuringType prf (mkApp p cur)
    rebindMut x outerTy (← mkAppM ``Subtype.mk #[cur, proof]) base dec
```

为了演示这个特性的实际效果，考虑非零自然数类型 {name}`Pos`：
```lean
abbrev Pos := { n : Nat // 0 < n }
```

在 {keywordOf openMutPure}`open` 块内部，`x` 的类型是 {name}`Nat`。
它和其他可变变量都可以被重新赋值：
```lean (name := openDemo)
#eval show Id (Pos × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    x := x + 1
  invariant by grind
  return (x, other)
```
```leanOutput openDemo
(21, 120)
```

同样，内部块也可以从外层 {keywordOf Lean.Parser.Term.do}`do` 块中 {keywordOf Lean.Parser.Term.doReturn}`return`：
```lean (name := openDemo2)
#eval show Id (Nat × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    if other > 0 then return (0, other)
    x := x + 1
  invariant by grind
  return (x.val, other)
```
```leanOutput openDemo2
(0, 120)
```

对于无法证明返回值满足该谓词的情形，_检查_ 它是否满足仍然可能很有用。
单子版本的精译器期望返回一个经过 {name}`PLift` 提升的证明：
```lean
def closeInvariant {α : Type} {P : α → Prop} [Monad m]
    (val : α) (act : m (PLift (P val))) : m (Subtype P) :=
  return ⟨val, (← act).down⟩

@[doElem_elab openMutMon]
def elabOpenMutMon : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant do $invSeq) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun _p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let actionStx ←
      ``(closeInvariant $(← Term.exprToSyntax cur) (do $invSeq))
    let action ← elabTermEnsuringType actionStx (← mkMonadApp outerTy)
    let rn ← mkFreshUserName `__repacked
    let closeCont : DoElemCont := {
      resultName := rn, resultType := outerTy
      k := do
        let d ← getLocalDeclFromUserName rn
        rebindMut x outerTy d.toExpr base dec
    }
    closeCont.mkBindUnlessPure action
```

现在，运行时检查可以确保该不变式成立；如果不成立，就抛出异常：
```lean
def trySub3 (x : Pos) : IO Pos := do
  let mut x := x
  open mut x do
    x := x - 3
  invariant do
    if h : 0 < x then pure ⟨h⟩
    else throw (IO.userError s!"Not positive: x = {x}")
  return x
```
```lean (name := openMutMon1)
#eval trySub3 ⟨10, by grind⟩
```
```leanOutput openMutMon1
7
```
```lean +error  (name := openMutMon2)
#eval trySub3 ⟨3, by grind⟩
```
```leanOutput openMutMon2
Not positive: x = 0
```

:::
