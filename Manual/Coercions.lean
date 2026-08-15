/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean (Syntax SourceInfo)

open Illuminate in
def coeChainDiagram : Diagram SVG :=
  let spacing := 16
  -- Build from inside out: hcat items spanned by each brace, then vsep brace below
  -- Level 1: Coe* with CoeTC brace
  let level1 := Diagram.braceBelow (mono "Coe*") (mono "CoeTC")
  -- Level 2: add CoeOut* on the left, CoeOTC brace below
  let level2 := Diagram.braceBelow
    (Diagram.hsep spacing [mono "CoeOut*", level1] (align := .top))
    (mono "CoeOTC")
  -- Level 3: add CoeHead? on the left, CoeHTC brace below
  let level3 := Diagram.braceBelow
    (Diagram.hsep spacing [mono "CoeHead?", level2] (align := .top))
    (mono "CoeHTC")
  -- Level 4: add CoeTail? on the right, CoeHTCT brace below (named)
  let level4 := Diagram.braceBelow
    (Diagram.hsep spacing [level3, mono "CoeTail?"] (align := .top))
    (mono "CoeHTCT" |>.padBottom 3 |>.namedWithAnchors `CoeHTCT)
  -- CoeDep at same level as CoeHTCT label (bottom-aligned, named)
  let withCoeDep := Diagram.hsep 30
    [level4, mono "CoeDep" |>.padBottom 3 |>.namedWithAnchors `CoeDep] (align := .bottom)
  -- "or" and CoeT below, named for anchor resolution
  let orLabel : Diagram SVG :=
    Diagram.text "or" { fontSize := 10, italic := true } |>.pad 3 |>.namedWithAnchors `or
  let coeTLabel : Diagram SVG := mono "CoeT" (name := `CoeT)
  let lineStroke : Stroke := .ofWidth 1
  Diagram.vsep 12 [withCoeDep, orLabel, coeTLabel]
    |>.connectL `CoeHTCT.south `or.west (stroke := lineStroke)
    |>.connectL `CoeDep.south `or.east (stroke := lineStroke)
    |>.connectL `or.south `CoeT.north (stroke := lineStroke)
where
  mono (s : String) (name : Option Lean.Name := none) : Diagram SVG :=
    .text s { fontSize := 10, fontFamily := "monospace" } (name := name)


#doc (Manual) "强制转换" =>
%%%
file := some "Coercions"
tag := "coercions"
%%%

```lean -show
section
open Lean (TSyntax Name)
variable {c1 c2 : Name} {α : Type u}
```


当 Lean 精译器期望某种类型，却产生了另一类型的项时，它会尝试自动插入{deftech (key := "coercion")}_强制转换_。强制转换是从该项的类型到期望类型的特别指定函数。
强制转换使得我们可以用具体类型表示数据，同时与那些期望信息较少类型的 API 交互。
它们也让数学形式化能够沿用通常的“一符多义”惯例：同一个符号既可表示代数结构，也可表示其载体集合，确切含义由上下文决定。


:::paragraph
Lean 的标准库和元编程 API 定义了许多强制转换。
例如：

 * 可在期望 {name}`Int` 之处使用 {name}`Nat`。
 * 可在期望 {name}`Nat` 之处使用 {name}`Fin`。
 * 可在期望 {lean}`Option α` 之处使用 {lean}`α`。该强制转换用 {name}`some` 包装此值。
 * 可在期望 {lean}`Thunk α` 之处使用 {lean}`α`。该强制转换将此项包装在函数中，以延迟其求值。
 * 当语法类别 {lean}`c1` 嵌入另一类别 {lean}`c2` 时，从 {lean}`TSyntax c1` 到 {lean}`TSyntax c2` 的强制转换会执行构造有效语法树所需的包装。

强制转换通过{tech (key := "synthesis")}[类型类合成]来查找。
可以为适当的类型类添加更多实例，从而扩展强制转换集合。
:::

```lean -show
end
```

:::example "强制转换"

以下示例全都依赖强制转换：

```lean
example (n : Nat) : Int := n
example (n : Fin k) : Nat := n
example (x : α) : Option α := x

def th (f : Int → String) (x : Nat) : Thunk String := f x

open Lean in
example (n : Ident) : Term := n
```

对于 {name}`th`，使用 {keywordOf Lean.Parser.Command.print}`#print` 可以看到，函数应用的求值会延迟到请求该延迟计算的值时：
```lean (name := thunkEval)
#print th
```
```leanOutput thunkEval
def th : (Int → String) → Nat → Thunk String :=
fun f x => { fn := fun x_1 => f ↑x }
```
:::


```lean -show
section
variable {α : Type u}
```

强制转换不会用于解析{tech (key := "generalized field notation")}[广义字段记法]：此时只考虑项的推断类型。
不过，可以使用{tech (key := "type ascription")}[类型标注]触发到具有所需广义字段之类型的强制转换。
强制转换也不会用于解析 {name}`OfNat` 实例：即使 {lean}`OfNat Nat` 有默认实例，从 {lean}`Nat` 到 {lean}`α` 的强制转换也不能让自然数字面量用于 {lean}`α`。

```lean -show
end
```

```lean -show
-- Test comment about field notation
/-- error: Unknown constant `Nat.bdiv` -/
#check_msgs in
#check Nat.bdiv

/-- info: Int.bdiv (x : Int) (m : Nat) : Int -/
#check_msgs in
#check Int.bdiv

/--
error: Invalid field `bdiv`: The environment does not contain `Nat.bdiv`, so it is not possible to project the field `bdiv` from an expression
  n
of type `Nat`
-/
#check_msgs in
example (n : Nat) := n.bdiv 2

#check_msgs in
example (n : Nat) := (n : Int).bdiv 2
```

:::example "强制转换与广义字段记法"

名称 {lean +error}`Nat.bdiv` 未定义，但 {lean}`Int.bdiv` 存在。
查找字段 `bdiv` 时，不会考虑从 {lean}`Nat` 到 {lean}`Int` 的强制转换：

```lean +error (name := natBdiv)
example (n : Nat) := n.bdiv 2
```
```leanOutput natBdiv
Invalid field `bdiv`: The environment does not contain `Nat.bdiv`, so it is not possible to project the field `bdiv` from an expression
  n
of type `Nat`
```

这是因为只有当期望类型与推断类型不同时才会插入强制转换，而广义字段是根据点号前项的推断类型解析的。
添加类型标注可以触发强制转换；此外，它还会使整个标注项的推断类型成为 {lean}`Int`，从而找到函数 {name}`Int.bdiv`。
```lean
example (n : Nat) := (n : Int).bdiv 2
```
:::

::::example "强制转换与 `OfNat`"
{lean}`Bin` 是表示二进制数的归纳类型。
```lean
inductive Bin where
  | done
  | zero : Bin → Bin
  | one : Bin → Bin

def Bin.toString : Bin → String
  | .done => ""
  | .one b => b.toString ++ "1"
  | .zero b => b.toString ++ "0"

instance : ToString Bin where
  toString
    | .done => "0"
    | b => Bin.toString b
```

反复应用 {lean}`Bin.succ` 可以将二进制数转换为自然数：
```lean
def Bin.succ (b : Bin) : Bin :=
  match b with
  | .done => Bin.done.one
  | .zero b => .one b
  | .one b => .zero b.succ

def Bin.ofNat (n : Nat) : Bin :=
  match n with
  | 0 => .done
  | n + 1 => (Bin.ofNat n).succ
```

```lean -show -keep
--- Internal tests
/-- info: [0, 1, 10, 11, 100, 101, 110, 111, 1000] -/
#check_msgs in
#eval [
  Bin.done,
  Bin.done.succ,
  Bin.done.succ.succ,
  Bin.done.succ.succ.succ,
  Bin.done.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ.succ]
```
```lean -show
def Bin.toNat : Bin → Nat
  | .done => 0
  | .zero b => 2 * b.toNat
  | .one b => 2 * b.toNat + 1

def Bin.double : Bin → Bin
  | .done => .done
  | other => .zero other

theorem Bin.toNat_succ_eq_succ {b : Bin} : b.toNat = n → b.succ.toNat = n + 1 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.succ]

theorem Bin.toNat_double_eq_double {b : Bin} : b.toNat = n → b.double.toNat = n * 2 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.double]

theorem Bin.ofNat_toNat_eq {n : Nat} : (Bin.ofNat n).toNat = n := by
  induction n <;> simp_all [Bin.ofNat, Bin.toNat, Bin.toNat_succ_eq_succ]
```


即使将 {lean}`Bin.ofNat` 注册为强制转换，自然数字面量也不能用于 {lean}`Bin`：
```lean
attribute [coe] Bin.ofNat

instance : Coe Nat Bin where
  coe := Bin.ofNat
```
``` lean (name := nineFail) +error
#eval (9 : Bin)
```
```leanOutput nineFail
failed to synthesize instance of type class
  OfNat Bin 9
numerals are polymorphic in Lean, but the numeral `9` cannot be used in a context where the expected type is
  Bin
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
这是因为强制转换会在类型不匹配时插入，但无法合成 {name}`OfNat` 实例并不是类型不匹配。


可以在 {lean}`OfNat Bin` 实例的定义中使用该强制转换：
```lean (name := ten)
instance : OfNat Bin n where
  ofNat := n

#eval (10 : Bin)
```
```leanOutput ten
1010
```
::::

大多数新的强制转换都可以这样定义：声明 {name}`Coe` {tech (key := "type class")}[类型类]的实例，并将 {attr}`coe` 属性应用于执行强制转换的函数。
为了更精细地控制强制转换，或使其能用于更多上下文，Lean 还提供了其他可实现的类，本章其余部分将对此加以介绍。

:::example "定义强制转换：十进制数"
十进制数可以定义为数位数组。

```lean
structure Decimal where
  digits : Array (Fin 10)
```

添加强制转换后，它们不仅可用于期望 {lean}`Nat` 的上下文，也可用于期望任何 {lean}`Nat` 可强制转换至的类型的上下文。

```lean
@[coe]
def Decimal.toNat (d : Decimal) : Nat :=
  d.digits.foldl (init := 0) fun n d => n * 10 + d.val

instance : Coe Decimal Nat where
  coe := Decimal.toNat
```

下面将 {lean}`Decimal` 同时视为 {lean}`Int` 和 {lean}`Nat`，以展示这一点：
```lean (name := digival)
def twoHundredThirteen : Decimal where
  digits := #[2, 1, 3]

def one : Decimal where
  digits := #[1]

#eval (one : Int) - (twoHundredThirteen : Nat)
```
```leanOutput digival
-212
```

:::

{docstring Coe}



# 强制转换插入
%%%
file := some "Coercion-Insertion"
tag := "coercion-insertion"
%%%

:::paragraph
从一种类型搜索到另一种类型的强制转换这一过程称为{deftech (key := "coercion insertion")}_强制转换插入_。
在以下原本会发生错误的情形中，会尝试进行强制转换插入：

 * 项的期望类型不等于为该项找到的类型。

 * 期望得到类型或命题，但该项的类型不是{tech (key := "universe")}[宇宙]。

 * 某项像函数一样被应用，但其类型不是函数类型。

显式请求强制转换时，也会插入强制转换。
强制转换可能插入的每种情形都有对应的前缀运算符，用来触发相应的插入。
:::

```lean -show
section
variable {α : Type u} {α' : Type u'} {β : Type u} [Coe α α'] [Coe α' β] (e : α)
```

由于强制转换会自动插入，嵌套的{tech (key := "type ascriptions")}[类型标注]提供了一种精确控制强制转换所涉及类型的方法。
如果 {lean}`α` 与 {lean}`β` 不是同一类型，{lean}`((e : α) : β)` 会先令 {lean}`e` 具有类型 {lean}`α`，再插入从 {lean}`α` 到 {lean}`β` 的强制转换。

```lean -show
end
```

发现强制转换后，用于找到它的实例会被展开，并从结果项中移除。
在可能的范围内，最终项中不会出现对 {name}`Coe.coe` 及相关函数的调用。
这一展开过程使项更易读。
更重要的是，这意味着强制转换可以将被转换的项包装在函数中，从而控制其求值。

:::example "用强制转换控制求值"

结构体 {name}`Later` 表示一个可在将来通过调用其所含函数来求值的项。

```lean
structure Later (α : Type u) where
  get : Unit → α
```

从任意值到延迟值的强制转换，是通过创建函数将其包装起来实现的。
```lean
instance : CoeTail α (Later α) where
  coe x := { get := fun () => x }
```

然而，如果强制转换插入产生的是对 {name}`CoeTail.coe` 的应用，那么该强制转换在运行时不会产生预期效果，因为被转换的值会先求值，再保存在函数的闭包中。
不过，由于强制转换的实现会被展开，这个实例仍然有用。

```lean
def tomorrow : Later String :=
  (Nat.fold 10000
    (init := "")
    (fun _ _ s => s ++ "tomorrow") : String)
```
打印所得定义可以看到，计算位于函数体内：
```lean (name := tomorrow)
#print tomorrow
```
```leanOutput tomorrow
def tomorrow : Later String :=
{ get := fun x => Nat.fold 10000 (fun x x_1 s => s ++ "tomorrow") "" }
```
:::

```lean -show
section
variable {α : Type u}
```
::::example "强制转换中的重复求值"
由于 {lean}`Coe` 实例的内容会在强制转换插入期间展开，多次使用其实参的强制转换应当谨慎确保只进行一次求值。
为此，可以使用不属于该实例的辅助函数，也可以使用 {keywordOf Lean.Parser.Term.let}`let` 对被转换的项求值，然后复用所得值。

结构体 {name}`Twice` 要求两个字段具有相同的值：
```lean
structure Twice (α : Type u) where
  first : α
  second : α
  first_eq_second : first = second
```

定义从 {lean}`α` 到 {lean}`Twice α` 的强制转换的一种方式，是使用辅助函数 {name}`twice`。
{attr}`coe` 属性将其标记为强制转换，使其能在证明目标和错误消息中正确显示。
```lean
@[coe]
def twice (x : α) : Twice α where
  first := x
  second := x
  first_eq_second := rfl

instance : Coe α (Twice α) := ⟨twice⟩
```
展开 {name}`Coe` 实例时，对 {name}`twice` 的调用会保留下来，使其实参在执行函数体之前求值。
因此，所得项中只包含一次 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace`：
```lean (name := eval1)
#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
下面用它来展示效果：
```leanOutput eval1
hello
```

将辅助函数内联到 {name}`Coe` 实例中，会得到一个重复 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 的项：
```lean (name := eval2)
instance : Coe α (Twice α) where
  coe x := ⟨x, x, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval2
hello
hello
```

为求值结果引入一个中间名称，可以避免重复 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace`：
```lean (name := eval3)
instance : Coe α (Twice α) where
  coe x := let y := x; ⟨y, y, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval3
hello
```

::::
```lean -show
end
```


# 类型间强制转换
%%%
file := some "Coercing-Between-Types"
tag := "coercing-between-types"
%%%

:::paragraph
当 Lean 精译器成功构造出一个项并推断出其类型，而所在上下文却期望另一种类型的项时，就会插入类型间强制转换。
在报告错误之前，精译器会尝试合成 {lean}`CoeT` 的实例，从而插入从推断类型到预期类型的强制转换。
这一尝试可能通过两种方式成功：
 1. 可以存在一条经过若干中间类型、从推断类型到预期类型的强制转换链。
    这些成链的强制转换根据推断类型和预期类型来选择，而不考虑被强制转换的项。
 2. 可以存在一个从推断类型到预期类型的依赖强制转换。
    依赖强制转换除推断类型和预期类型外，还会考虑被强制转换的项，但它们不能成链。
:::

定义非依赖强制转换最简单的方式是实现一个 {name}`Coe` 实例，这足以合成一个 {name}`CoeT` 实例。
此实例会参与成链，并且可以应用任意多次。
合成 {name}`Coe` 实例由表达式的预期类型而非推断类型驱动。
对于至多只能使用一次的实例，或应由推断类型驱动合成的实例，可能需要使用其他强制转换类之一。

:::example "定义强制转换"
类型 {lean}`Even` 表示偶自然数。

```lean
structure Even where
  number : Nat
  isEven : number % 2 = 0
```

强制转换使偶数可用于期望自然数的位置。
{attr}`coe` 属性将该投影标记为强制转换，使其能在证明状态和错误消息中相应显示，具体见{ref "coercion-impl"}[实现强制转换一节]。
```lean
attribute [coe] Even.number

instance : Coe Even Nat where
  coe := Even.number
```
有了这个强制转换，就可以在期望自然数的位置使用偶数。
```lean (name := four)
def four : Even := ⟨4, by omega⟩

#eval (four : Nat) + 1
```
```leanOutput four
5
```

由于强制转换可以成链，将 {inst}`Coe Even Nat` 实例与已有的从 {name}`Nat` 到 {name}`Int` 的强制转换连接起来，还会形成一个从 {name}`Even` 到 {name}`Int` 的强制转换：
```lean (name := four')
#eval (four : Int) - 5
```
```leanOutput four'
-1
```
:::

{deftech (key := "Dependent coercions")}[依赖强制转换]用于必须根据被强制转换的具体项来确定能否或如何转换该项的情况：例如，只有可判定命题才能强制转换为 {name}`Bool`，所以相关命题必须出现在实例类型中，以便该类型能够要求 {name}`Decidable` 实例。
只要推断类型的所有值都能强制转换为目标类型，就使用非依赖强制转换。

:::example "定义依赖强制转换"
通过以下实例声明，可将字符串 {lean}`"four"` 强制转换为自然数 {lean  (type := "Nat")}`4`：
```lean (name := fourCoe)
instance : CoeDep String "four" Nat where
  coe := 4

#eval ("four" : Nat)
```
```leanOutput fourCoe
4
```

其他字符串会产生普通的类型错误：
```lean +error (name := threeCoe)
#eval ("three" : Nat)
```
```leanOutput threeCoe
Type mismatch
  "three"
has type
  String
but is expected to have type
  Nat
```

:::


```lean -show
section
variable {α α' α'' β β' «…» γ: Sort _}

macro "…":term => Lean.mkIdentFromRef `«…»

variable [CoeHead α α'] [CoeOut α' …] [CoeOut … α''] [Coe α'' …] [Coe … β'] [CoeTail β' γ]


```

:::paragraph
非依赖强制转换可以成链：如果存在从 {lean}`α` 到 {lean}`β` 的强制转换以及从 {lean}`β` 到 {lean}`γ` 的强制转换，那么也存在从 {lean}`α` 到 {lean}`γ` 的强制转换。
{index (subterm:="强制转换的")}[链]
强制转换链应具有 {name}`CoeHead`$`?`{name}`CoeOut`$`*`{name}`Coe`$`*`{name}`CoeTail`$`?` 的形式，也就是说，它可以由以下部分组成：

 * 一个可选的 {inst}`CoeHead α α'` 实例，之后是
 * 零个或多个 {inst}`CoeOut α' …`、…、{inst}`CoeOut … α''` 实例，之后是
 * 零个或多个 {inst}`Coe α'' …`、…、{inst}`Coe … β'` 实例，之后是
 * 一个可选的 {inst}`CoeTail β' γ` 实例

大多数强制转换都可以实现为 {name}`Coe` 的实例。
某些特殊情况下则需要 {name}`CoeHead`、{name}`CoeOut` 和 {name}`CoeTail`。

:::



{name}`CoeHead` 和 {name}`CoeOut` 实例从推断类型朝预期类型方向成链。
换言之，会使用为该项得到的类型中的信息来解析实例链。
{name}`Coe` 和 {name}`CoeTail` 实例从预期类型朝推断类型方向成链，因此会使用预期类型中的信息来解析实例链。
如果这些链在中间相遇，就找到了一个强制转换。
这体现在它们的类型签名中：{name}`CoeHead` 和 {name}`CoeOut` 将{tech (key := "semi-output parameters")}[半输出参数]用于强制转换的目标，而 {name}`Coe` 和 {name}`CoeTail` 将{tech (key := "semi-output parameters")}[半输出参数]用于强制转换的源。

当实例为{tech (key := "semi-output parameter")}[半输出参数]提供值时，该值会在实例合成期间使用。
但是，如果没有提供值，则合成算法可以为其赋值。
因此，选择实例时，应为每个半输出参数指派一个类型。
这意味着，当强制转换输出中出现的变量是输入中变量的子集时，应使用 {name}`CoeOut`；当输入中的变量是输出中变量的子集时，则应使用 {name}`Coe`。

:::example "`CoeOut` 与 `Coe` 实例"
{name}`Truthy` 值由一个值和一个指示该值应视为真还是假的标志配对组成。
{name}`Decision` 可以是 {name Decision.yes}`yes`、{name Decision.no}`no` 或 {name Decision.maybe}`maybe`，其中最后一种还包含需要考虑的其他数据。

```lean
structure Truthy (α : Type) where
  val : α
  isTrue : Bool

inductive Decision (α : Type) where
  | yes
  | maybe (val : α)
  | no
```

{noVale "为示例编造的词语"}[“Truthy”] 值可以通过忽略其中包含的值转换为 {name}`Bool`。
{name}`Bool` 可以通过排除 {name Decision.maybe}`maybe` 情况转换为 {name}`Decision`。
```lean
@[coe]
def Truthy.toBool : Truthy α → Bool :=
  Truthy.isTrue

@[coe]
def Decision.ofBool : Bool → Decision α
  | true => .yes
  | false => .no
```

{name}`Truthy.toBool` 必须是 {name}`CoeOut` 实例，因为强制转换的目标比源包含更少的未知类型变量；而 {name}`Decision.ofBool` 必须是 {name}`Coe` 实例，因为强制转换的源比目标包含更少的变量：
```lean
instance : CoeOut (Truthy α) Bool := ⟨Truthy.isTrue⟩

instance : Coe Bool (Decision α) := ⟨Decision.ofBool⟩
```

有了这些实例，强制转换就可以成链：
```lean (name := chainTruthiness)
#eval ({ val := 1, isTrue := true : Truthy Nat } : Decision String)
```
```leanOutput chainTruthiness
Decision.yes
```

尝试使用错误的类会导致错误：
```lean (name := coeOutErr) +error
instance : Coe (Truthy α) Bool := ⟨Truthy.isTrue⟩
```
```leanOutput coeOutErr
instance does not provide concrete values for (semi-)out-params
  Coe (Truthy ?α) Bool
```

:::


```lean -show
end
```

{docstring CoeHead}

{docstring CoeOut}

{docstring CoeTail}

存在适当的实例链或单个适用的 {name}`CoeDep` 实例时，可以合成 {name}`CoeT` 的实例。{margin}[从 {lean}`Nat` 强制转换到另一类型时，{name}`NatCast` 实例也足够。]
如果二者都存在，则优先使用 {name}`CoeDep` 实例。

{docstring CoeT}

```lean -show
section
variable {α β : Sort _} {e : α} [CoeDep α e β]
```

依赖强制转换不能成链。
作为强制转换链的替代方案，可以使用 {inst}`CoeDep α e β` 实例将类型为 {lean}`α` 的项 {lean}`e` 强制转换为 {lean}`β`。
依赖强制转换适用于只有部分值可以强制转换的情况；这一机制用于仅将可判定命题强制转换为 {lean}`Bool`。
当值本身出现在强制转换的目标类型中时，它们也很有用。

```lean -show
end
```

{docstring CoeDep}

:::example "依赖强制转换"
```lean -show
universe u
```

非空列表类型可以定义为一个列表与其非空证明组成的二元组。
通过应用投影，可以将此类型强制转换为普通列表：

```lean
structure NonEmptyList (α : Type u) : Type u where
  contents : List α
  non_empty : contents ≠ []

instance : Coe (NonEmptyList α) (List α) where
  coe xs := xs.contents
```

该强制转换如预期般工作：
```lean
def oneTwoThree : NonEmptyList Nat := ⟨[1, 2, 3], by simp⟩

#eval (oneTwoThree : List Nat) ++ [4]
```

然而，任意列表不能强制转换为非空列表，因为任意选取的某些列表确实可能为空：

```lean +error (name := coeFail) -keep
instance : Coe (List α) (NonEmptyList α) where
  coe xs := ⟨xs, _⟩
```
```leanOutput coeFail
don't know how to synthesize placeholder for argument `non_empty`
context:
α : Type u_1
xs : List α
⊢ xs ≠ []
```

依赖强制转换可以把强制转换的定义域限制为非空列表：
```lean (name := coeOk)
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨x :: xs, by simp⟩

#eval ([1, 2, 3] : NonEmptyList Nat)
```
```leanOutput coeOk
{ contents := [1, 2, 3], non_empty := _ }
```


插入依赖强制转换要求被转换的项在语法上与实例头中的项匹配。
已知非空、但在语法上不是 {lean  (type := "{α : Type u} → α → List α → List α")}`(· :: ·)` 实例的列表，无法使用此实例进行强制转换。
```lean +error (name := coeFailDep)
#check
  fun (xs : List Nat) =>
    let ys : List Nat := xs ++ [4]
    (ys : NonEmptyList Nat)
```
强制转换插入失败时，会报告原始类型错误：
```leanOutput coeFailDep
Type mismatch
  ys
has type
  List Nat
but is expected to have type
  NonEmptyList Nat
```

:::

:::syntax term (title := "强制转换")
```grammar
↑$_:term
```

可以使用前缀运算符 {keywordOf coeNotation}`↑` 显式放置强制转换。
:::

与使用嵌套的{tech (key := "type ascriptions")}[类型标注]不同，用于放置强制转换的 {keywordOf coeNotation}`↑` 语法不要求显式写出所涉及的类型。

:::example "控制强制转换插入"

实例合成与强制转换插入会相互作用。
合成实例可能会使类型信息变为已知，随后触发强制转换插入。
强制转换的具体放置位置可能会影响结果。

在 {lean}`sub` 的这个定义中，会根据函数的返回类型合成 {inst}`Sub Int` 实例。
此实例要求两个参数也为 {lean}`Int`，但它们是 {lean}`Nat`。
减法运算符的每个实参外都会插入强制转换。
这可以从 {keywordOf Lean.Parser.Command.print}`#print` 的输出中看出。

```lean (name := subThenCoe)
def sub (n k : Nat) : Int := n - k

#print sub
```
```leanOutput subThenCoe
def sub : Nat → Nat → Int :=
fun n k => ↑n - ↑k
```

将强制转换运算符放在减法外部，会使精译器先尝试推断减法的类型，再插入强制转换。
因为实参都是 {lean}`Nat`，所以会选择 {inst}`Sub Nat` 实例，从而使差值成为 {lean}`Nat`。
然后再将该差值强制转换为 {lean}`Int`。
```lean (name:=coeThenSub)
def sub' (n k : Nat) : Int := ↑ (n - k)

#print sub'
```

这两个函数并不等价，因为自然数减法会在零处截断：
```lean (name := subRes)
#eval sub 4 8
```
```leanOutput subRes
-4
```
```lean (name := subMark)
#eval sub' 4 8
```
```leanOutput subMark
0
```

:::


## 实现强制转换
%%%
tag := "coercion-impl"
%%%

适当的 {name}`CoeHead`、{name}`CoeOut`、{name}`Coe` 或 {name}`CoeTail` 实例足以使所需的强制转换得以插入。
不过，强制转换的实现应使用 {attr}`coe` 属性注册为强制转换。
这会使 Lean 使用 {keywordOf coeNotation}`↑` 运算符显示强制转换的使用。
这也会使 {tactic}`norm_cast` 策略将该强制转换视为数值转换，而不是普通函数。

:::syntax attr (title := "强制转换声明")
```grammar
coe
```

{includeDocstring Lean.Attr.coe}

:::

:::example "实现强制转换"
{tech (key := "enum inductive")}[枚举归纳]类型 {lean}`Weekday` 表示一周中的各天：
```lean
inductive Weekday where
  | mo | tu | we | th | fr | sa | su
```

作为一个七元素类型，它与 {lean}`Fin 7` 包含相同的信息。
二者之间存在双射：
```lean
def Weekday.toFin : Weekday → Fin 7
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

def Weekday.fromFin : Fin 7 → Weekday
  | 0 => mo
  | 1 => tu
  | 2 => we
  | 3 => th
  | 4 => fr
  | 5 => sa
  | 6 => su
```

```lean -show
theorem Weekday.toFin_fromFin_id : Weekday.toFin (Weekday.fromFin n) = n := by
  repeat (cases ‹Fin (_ + 1)› using Fin.cases; case zero => rfl)
  apply Fin.elim0; assumption

theorem Weekday.fromFin_toFin_id : Weekday.fromFin (Weekday.toFin w) = w := by
  cases w <;> rfl
```

每种类型都可以强制转换为另一种：
```lean
instance : Coe Weekday (Fin 7) where
  coe := Weekday.toFin

instance : Coe (Fin 7) Weekday where
  coe := Weekday.fromFin
```

虽然这样可以工作，但 Lean 输出中出现的强制转换实例并未按 Lean 用户所期望的方式使用强制转换运算符呈现。
相反，其中显式使用了名称 {lean}`Weekday.fromFin`：
```lean (name := wednesday)
def wednesday : Weekday := (2 : Fin 7)

#print wednesday
```
```leanOutput wednesday
def wednesday : Weekday :=
Weekday.fromFin 2
```


为强制转换的定义添加 {attr}`coe` 属性，会使其使用强制转换运算符显示：
```lean (name := friday)
attribute [coe] Weekday.fromFin
attribute [coe] Weekday.toFin

def friday : Weekday := (5 : Fin 7)

#print friday
```
```leanOutput friday
def friday : Weekday :=
↑5
```

:::

## 自然数与整数的强制转换
%%%
tag := "nat-api-cast"
%%%

类型类 {name}`NatCast` 和 {name}`IntCast` 是 {name}`Coe` 的特殊情况，用于定义从 {lean}`Nat` 或 {lean}`Int` 到某种在一定意义上具有典范性的其他类型的强制转换。
它们的存在是为了更好地集成大型数学库，例如 [Mathlib](https://github.com/leanprover-community/mathlib4)；这类库大量使用强制转换，将自然数或整数映射到其他结构（通常是环）。
理想情况下，将自然数或整数强制转换到这些结构所得的形式应为{tech (key := "simp normal form")}[simp 规范形]，因为这是一种方便的表示方式。

当强制转换的应用预期成为某类型的{tech (key := "simp normal form")}[simp 规范形]时，重要的是实践中_所有_这类强制转换都应{tech (key := "definitional equality")}[定义相等]。
否则，{tech (key := "simp normal form")}[simp 规范形]就必须选择唯一一条成链的强制转换路径，但引理却可能不慎使用另一条路径来陈述。
由于 {tactic}`simp` 的内部索引基于项的底层结构，而不是项在表层语法中的呈现方式，这些差异会使引理无法在预期位置应用。
另一方面，{lean}`NatCast` 和 {lean}`IntCast` 实例应定义成始终{tech (key := "definitional equality")}[定义相等]，从而避免这个问题。
Lean 标准库对实例的安排使得插入强制转换时，会优先选择 {name}`NatCast` 或 {name}`IntCast` 实例，而不是强制转换实例链。
它们也可以用作 {name}`CoeOut` 实例，从而在需要时平稳回退到强制转换链。

{docstring NatCast}

{docstring Nat.cast}

{docstring IntCast}

{docstring Int.cast}


# 强制转换为 Sort
%%%
file := "Coercing-to-Sorts"
tag := "coercing-to-sorts"
%%%

Lean 精译器会在某些位置期待类型，却未必能预先确定该类型的{tech (key := "universe")}[宇宙]。
例如，定义头中冒号后的项可能是命题，也可能是类型。
普通的强制转换机制并不适用，因为它要求有具体的预期类型，而 {name}`Coe` 类无法表达预期类型可以是_任意_宇宙。

当某个位置预期命题或类型，而在该位置精译出的项的推断类型并非命题或类型时，Lean 会尝试合成 {name}`CoeSort` 实例来从错误中恢复。
如果找到了实例，且结果类型本身是一个类型，就会插入并展开该强制转换。

并非精译器期待宇宙的所有情形都需要 {name}`CoeSort`。
在某些情况下，可以取得某个特定宇宙作为预期类型。
此时会使用 {name}`CoeT` 进行普通的强制转换插入。
{lean}`CoeSort` 的实例可用于合成 {lean}`CoeOut` 实例，因此无需单独的实例来支持这种用法。
一般而言，强制转换为类型应实现为 {name}`CoeSort`。

{docstring CoeSort}


:::syntax term (title := "显式强制转换为 Sort")
```grammar
↥ $_:term
```

可使用前缀运算符 {keyword}`↥` 显式触发强制转换为 Sort。
:::

::: example "Sort 强制转换"

幺半群是配备了结合二元运算和单位元的类型。
幺半群结构可以定义为类型类，也可以定义为将结构与类型“捆绑”在一起的结构体：
```lean
structure Monoid where
  Carrier : Type u
  op : Carrier → Carrier → Carrier
  id : Carrier
  op_assoc :
    ∀ (x y z : Carrier), op x (op y z) = op (op x y) z
  id_op_identity : ∀ (x : Carrier), op id x = x
  op_id_identity : ∀ (x : Carrier), op x id = x
```

类型 {lean  (type := "Type 1")}`Monoid` 并不指明载体：
```lean
def StringMonoid : Monoid where
  Carrier := String
  op := (· ++ ·)
  id := ""
  op_assoc := by intros; simp [String.append_assoc]
  id_op_identity := by intros; simp
  op_id_identity := by intros; simp
```

不过，可以实现一个 {name}`CoeSort` 实例：当幺半群出现在 Lean 期待类型的位置时，该实例应用 {name}`Monoid.Carrier` 投影：
```lean
instance : CoeSort Monoid (Type u) where
  coe m := m.Carrier

example : StringMonoid := "hello"
```
:::

:::example "将 Sort 强制转换用作普通强制转换"
{tech (key := "inductive type")}[归纳类型] {name}`NatOrBool` 表示类型 {name}`Nat` 和 {name}`Bool`。
它的值可以强制转换为实际类型 {name}`Nat` 和 {name}`Bool`：
```lean
inductive NatOrBool where
  | nat | bool

@[coe]
abbrev NatOrBool.asType : NatOrBool → Type
  | .nat => Nat
  | .bool => Bool

instance : CoeSort NatOrBool Type where
  coe := NatOrBool.asType

open NatOrBool
```

当 {lean}`nat` 出现在冒号右侧时，会使用 {name}`CoeSort` 实例：
```lean
def x : nat := 5
```

有预期类型时，会使用普通的强制转换插入。
在此例中，{name}`CoeSort` 实例用于合成 {lean}`CoeOut NatOrBool Type` 实例；后者与 {inst}`Coe Type (Option Type)` 实例链接，以从类型错误中恢复。
```lean
def y : Option Type := bool
```
:::

# 强制转换为函数类型
%%%
file := "Coercing-to-Function-Types"
tag := "coercing-to-function-types"
%%%

另一个通常无法取得预期类型的情形，是函数应用项中的函数位置。
依赖函数类型很常见；它们与{tech (key := "implicit")}[隐式]参数一起，使信息从一个实参的精译流向其他实参的精译。
试图根据整个应用项的预期类型以及各实参独立推断出的类型来推导函数所需的类型，往往会失败。
在这些情形下，Lean 使用 {name}`CoeFun` 类型类，将应用位置中的非函数强制转换为函数。
与 {name}`CoeSort` 一样，插入函数强制转换时，{name}`CoeFun` 实例不会与其他强制转换链接；但在普通的强制转换插入期间，它们可以用作 {name}`CoeOut` 实例。

{name}`CoeFun` 的第二个参数是一个输出参数，用于确定结果函数类型。
这个输出参数是根据被强制转换的项计算函数类型的函数，而不是函数类型本身。
与 {name}`CoeDep` 不同，实例合成期间不会考虑项本身；不过，可以用它创建依赖类型的强制转换，使函数类型由该项确定。


{docstring CoeFun}

:::syntax term (title := "显式强制转换为函数")
```grammar
⇑ $_:term
```
:::

```lean -show
section
variable {α : Type u} {β : Type v}
```
:::example "将带说明的函数强制转换为函数类型"
结构体 {lean}`NamedFun α β` 将一个从 {lean}`α` 到 {lean}`β` 的函数与一个名称配成一对。

```lean
structure NamedFun (α : Type u) (β : Type v) where
  function : α → β
  name : String
```

可以给已有函数命名：
```lean
def succ : NamedFun Nat Nat where
  function n := n + 1
  name := "succ"

def asString [ToString α] : NamedFun α String where
  function := ToString.toString
  name := "asString"

def append : NamedFun (List α) (List α → List α) where
  function := (· ++ ·)
  name := "append"
```

命名函数也可以组合：
```lean
def NamedFun.comp
    (f : NamedFun β γ)
    (g : NamedFun α β) :
    NamedFun α γ where
  function := f.function ∘ g.function
  name := f.name ++ " ∘ " ++ g.name
```


与普通函数不同，命名函数可以合理地表示为字符串：
```lean
instance : ToString (NamedFun α α'') where
  toString f := s!"#<{f.name}>"
```
```lean (name := compDemo)
#eval asString.comp succ
```
```leanOutput compDemo
#<asString ∘ succ>
```

{name}`CoeFun` 实例使它们可以像普通函数一样应用：
```lean
instance : CoeFun (NamedFun α α'') (fun _ => α → α'') where
  coe | ⟨f, _⟩ => f
```
```lean (name := appendDemo)
#eval append [1, 2, 3] [4, 5, 6]
```
```leanOutput appendDemo
[1, 2, 3, 4, 5, 6]
```
:::
```lean -show
end
```

:::example "依赖的函数强制转换"
有时，结果函数的类型取决于被强制转换的具体值。
{lean}`Writer` 表示将某个值的表示追加到字符串的一种方式：
```lean
structure Writer where
  Writes : Type u
  write : Writes → String → String

def natWriter : Writer where
  Writes := Nat
  write n out := out ++ toString n

def stringWriter : Writer where
  Writes := String
  write s out := out ++ s
```

由于内层函数所期待的参数类型取决于 {lean}`Writer.Writes` 字段，{name}`CoeFun` 实例会提取该字段：
```lean
instance :
    CoeFun Writer (·.Writes → String → String) where
  coe w := w.write
```

有了这个实例，具体的 {name}`Writer` 就可以用作函数：
```lean (name := writeTwice)
#eval "" |> natWriter (5 : Nat) |> stringWriter " hello"
```
```leanOutput writeTwice
"5 hello"
```
:::

:::example "强制转换为函数类型"

良类型解释器是一种编程语言解释器，它使用索引族排除运行时类型错误。
在被解释语言中编写的函数可以解释为 Lean 函数，同时也可以检查其底层源代码。

良类型解释器的第一步，是选出可以使用的 Lean 类型子集。
这些类型由代码的{tech (key := "inductive type")}[归纳类型] {name}`Ty` 表示，并由一个函数将这些代码映射到实际类型。
```lean
inductive Ty where
  | nat
  | arr (dom cod : Ty)

abbrev Ty.interp : Ty → Type
  | .nat => Nat
  | .arr t t' => t.interp → t'.interp
```

语言本身表示为一个以变量上下文和结果类型为索引的{tech (key := "indexed family")}[索引族]。
变量使用 [de Bruijn 索引](https://en.wikipedia.org/wiki/De_Bruijn_index)表示。
```lean
inductive Tm : List Ty → Ty → Type where
  | zero : Tm Γ .nat
  | succ (n : Tm Γ .nat) : Tm Γ .nat
  | rep (n : Tm Γ .nat)
    (start : Tm Γ t)
    (f : Tm Γ (.arr .nat (.arr t t))) :
    Tm Γ t
  | lam (body : Tm (t :: Γ) t') : Tm Γ (.arr t t')
  | app (f : Tm Γ (.arr t t')) (arg : Tm Γ t) : Tm Γ t'
  | var (i : Fin Γ.length) : Tm Γ Γ[i]
deriving Repr
```


由于 {name}`Fin` 的 {name}`OfNat` 实例要求上界非零，因此将 {name}`Tm.var` 与数值字面量一起使用可能不方便。
辅助函数 {name}`Tm.v` 可在这些情况下避免类型标注。
```lean
def Tm.v
    (i : Fin (Γ.length + 1)) :
    Tm (t :: Γ) (t :: Γ)[i] :=
  .var (Γ := t :: Γ) i
```

将两个自然数相加的函数使用 {name Tm.rep}`rep` 运算重复应用后继 {name}`Tm.succ`。
```lean
def plus : Tm [] (.arr .nat (.arr .nat .nat)) :=
  .lam <| .lam <| .rep (.v 1) (.v 0) (.lam (.lam (.succ (.v 0))))
```


每个类型上下文都可以解释为一种运行时环境类型，为上下文中的每个变量提供值：
```lean
def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => t.interp × Env Γ

def Env.empty : Env [] := ()

def Env.extend (ρ : Env Γ) (v : t.interp) : Env (t :: Γ) :=
  (v, ρ)

def Env.get (i : Fin Γ.length) (ρ : Env Γ) : Γ[i].interp :=
  match Γ, ρ, i with
  | _::_, (v, _), ⟨0, _⟩ => v
  | _::_, (_, ρ'), ⟨i+1, _⟩ => ρ'.get ⟨i, by simp_all⟩
```

最后，解释器是关于项的递归函数：
```lean
def Tm.interp (ρ : Env α'') : Tm α'' t → t.interp
  | .zero => 0
  | .succ n => n.interp ρ + 1
  | .rep n start f =>
    let f' := f.interp ρ
    (n.interp ρ).fold (fun n _ x => f' n x) (start.interp ρ)
  | .lam body => fun x => body.interp (ρ.extend x)
  | .app f arg => f.interp ρ (arg.interp ρ)
  | .var i => ρ.get i
```

将 {name}`Tm` 强制转换为函数，就是调用解释器。

```lean
instance : CoeFun (Tm [] α'') (fun _ => α''.interp) where
  coe f := f.interp .empty
```

由于函数由一阶归纳类型表示，可以检查其代码：
```lean (name := evalPlus)
#eval plus
```
```leanOutput evalPlus
Tm.lam (Tm.lam (Tm.rep (Tm.var 1) (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0))))))
```

与此同时，凭借强制转换，它们可以像原生 Lean 函数一样应用：
```lean (name := eight)
#eval plus 3 5
```
```leanOutput eight
8
```

:::



# 实现细节
%%%
file := "Implementation-Details"
tag := "implementation-details"
%%%


只有普通强制转换插入会使用强制转换链。
插入强制转换为 {ref "coercing-to-sorts"}[Sort] 或{ref "coercing-to-function-types"}[函数类型]时，使用普通实例合成。
同样，{tech (key := "dependent coercions")}[依赖强制转换]不会链接。

## 展开强制转换
%%%
tag := "coercion-unfold-impl"
%%%

强制转换插入机制会展开强制转换的应用，从而可以控制结果项的具体形状。
这既是为了确保可读的证明目标，也是为了控制编译后代码中被强制转换项的求值。
强制转换的展开由 {attr}`coe_decl` 属性控制，该属性应用于每个强制转换方法（例如 {name}`Coe.coe`）。
该属性应视为强制转换机制的内部组成部分，而不是公开强制转换 API 的一部分。


## 强制转换链
%%%
tag := "coercion-chain-impl"
%%%

:::paragraph

强制转换链通过一组辅助类型类实现。
用户不应直接编写这些类的实例，但在诊断为何没有按预期插入强制转换时，了解其结构会很有用。
控制链中实例顺序的具体规则（即应匹配 {name}`CoeHead`﻿`?`{name}`CoeOut`﻿`*`{name}`Coe`﻿`*`{name}`CoeTail`﻿`?`）由以下类型类实现：

 * {name}`CoeTC` 是 {name}`Coe` 实例的传递闭包。

 * {name}`CoeOTC` 是链的中部，由 {name}`CoeOut` 实例的传递闭包后接 {name}`CoeTC` 构成。

 * {name}`CoeHTC` 是链的开头，由至多一个 {name}`CoeHead` 实例后接 {name}`CoeOTC` 构成。

 * {name}`CoeHTCT` 是完整的链，由 `CoeHTC` 后接至多一个 {name}`CoeTail` 实例构成。另一种可能是 {name}`NatCast` 实例。

 * {name}`CoeT` 表示整个链：它或者是 {name}`CoeHTCT` 链，或者是单个 {name}`CoeDep` 实例。

:::

:::figure "强制转换的辅助类" (tag := "coe-aux-classes")
```diagram
coeChainDiagram
```
:::

{docstring CoeHTCT}

{docstring CoeHTC}

{docstring CoeOTC}

{docstring CoeTC}
