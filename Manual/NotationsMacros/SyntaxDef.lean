/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "定义新语法" =>
%%%
tag := "syntax-ext"
%%%

Lean 对语法的统一表示非常一般且灵活。
这意味着，对 Lean 解析器的扩展并不需要同时扩展已解析语法的表示方式。

# 语法模型
%%%
tag := "syntax-data"
%%%

Lean 的解析器会产生一棵具体语法树，其类型为 {name}`Lean.Syntax`。
{name}`Lean.Syntax` 是一个归纳类型，用来表示 Lean 的全部语法，包括命令、项、策略以及任何自定义扩展。
所有这些都由少数几种基本构件来表示：

: {deftech (key := "Atoms")}[原子]

  原子是语法中的基本终结符，包括字面量（例如字符和数字的字面量）、括号、运算符和关键字。

: {deftech (key := "Identifiers")}[标识符]

  :::keepEnv
  ```lean -show
  variable {α : Type u}
  variable {x : α}
  ```
  标识符表示名字，例如 {lean}`x`、{lean}`Nat` 或 {lean}`Nat.add`。
  标识符语法中包含一个预解析名称列表，记录该标识符可能指向哪些名字。
  :::

: {deftech (key := "Nodes")}[节点]

  节点表示对非终结符的解析结果。
  节点包含一个 {deftech (key := "syntax kind")}_语法种类_，用于标识该节点来自哪条语法规则；它还包含一个由子 {name Lean.Syntax}`Syntax` 值组成的数组。

: 缺失语法

  当解析器遇到错误时，它会返回部分结果，这样 Lean 就能对尚未写完的程序或包含错误的程序提供一些反馈。
  部分结果中会包含一个或多个缺失语法的位置。

原子与标识符统称为 {deftech (key := "tokens")}_记号_。

{docstring Lean.Syntax}

{docstring Lean.Syntax.Preresolved}

# 语法节点种类

语法节点种类通常用来标识产生该节点的解析器。
运算符或记法被赋予的名称（以及它们自动生成的内部名称）就会出现在这里。
虽然只有节点本身包含标识其种类的字段，但按照约定，标识符的种类是 {name Lean.identKind}`identKind`，而原子的种类则按照约定就是它们内部保存的字符串。
Lean 的解析器会把每个关键字原子 `KW` 包装进一个单元素节点，其种类为 `` `token.KW ``。
语法值的种类可以通过 {name Lean.Syntax.getKind}`Syntax.getKind` 提取出来。

{docstring Lean.SyntaxNodeKind}

{docstring Lean.Syntax.isOfKind}

{docstring Lean.Syntax.getKind}

{docstring Lean.Syntax.setKind}

# 记号与字面量种类

解析器生成的基本记号都关联着若干具名种类。
通常，单记号语法产生式由一个包含单个 {name Lean.Syntax.atom}`atom` 的 {name Lean.Syntax.node}`node` 构成；保存在节点中的种类使得这个值能够被识别。
解析器不会解释字面量原子：字符串原子会连同前后的双引号以及其中包含的任何转义序列一起保存，而十六进制数字则会被保存为一个以 {lean}`"0x"` 开头的字符串。
提供了 {ref "typed-syntax-helpers"}[辅助函数]（例如 {name}`Lean.TSyntax.getString`）来按需执行这些解码操作。

```lean -show -keep
-- 验证关于原子与节点的说法
open Lean in
partial def noInfo : Syntax → Syntax
  | .node _ k children => .node .none k (children.map noInfo)
  | .ident _ s x pre => .ident .none s x pre
  | .atom _ s => .atom .none s
  | .missing => .missing
/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "0xabc123"]
-/
#check_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#check_msgs in
#eval noInfo <$> `(term|"ab\tc")
```

{docstring Lean.identKind}

{docstring Lean.strLitKind}

{docstring Lean.interpolatedStrKind}

{docstring Lean.interpolatedStrLitKind}

{docstring Lean.charLitKind}

{docstring Lean.numLitKind}

{docstring Lean.scientificLitKind}

{docstring Lean.nameLitKind}

{docstring Lean.fieldIdxKind}

# 内部种类

{docstring Lean.groupKind}

{docstring Lean.nullKind}

{docstring Lean.choiceKind}

{docstring Lean.hygieneInfoKind}

# 源位置
%%%
tag := "source-info"
%%%

原子、标识符和节点可以选择性地包含 {deftech (key := "source information")}[源信息]，用来跟踪它们与原始文件的对应关系。
解析器会为所有记号保存源信息，但不会为节点保存；已解析节点的位置信息是由其首尾记号重建出来的。
并非所有 {name Lean.Syntax}`Syntax` 数据都来自解析器：它也可能是 {tech (key := "macro expansion")}[宏展开] 的结果，这时它通常同时混有生成出来的语法和解析得到的语法；或者也可能是对内部项进行 {tech (key := "delaborator")}[反精译] 以展示给用户的结果。
在这些使用场景中，节点自身也可能包含源信息。

源信息分为两种：

: {deftech (key := "Original")}[原始]

  原始源信息来自解析器。
  除了原始源位置之外，它还包含被解析器跳过的前导和尾随空白，因此原始字符串可以被重建出来。
  为了避免分配子串副本，这些空白会保存为原始源码字符串表示中的偏移量（也就是 {name}`Substring`）。

: {deftech (key := "Synthetic")}[合成]

  合成源信息来自元程序（包括宏）或 Lean 内部。
  由于没有需要重建的原始字符串，因此它不会保存前导和尾随空白。
  合成源位置用于在项被自动转换后依然提供准确反馈，也用于跟踪精译后表达式与其在 Lean 输出中的呈现之间的对应关系。
  合成位置可以被标记为 {deftech (key := "canonical")}_规范_；在这种情况下，一些通常会忽略合成位置的操作会把它当作非合成位置来处理。

{docstring Lean.SourceInfo}

# 检查语法

```lean -show
section Inspecting
open Lean
```

检查 {lean}`Syntax` 值主要有三种方式：

 : {lean}`Repr` 实例

  {lean}`Repr Syntax` 实例会用 {lean}`Syntax` 类型的各个构造子给出非常详细的语法表示。

 : {lean}`ToString` 实例

  {lean}`ToString Syntax` 实例会生成一种紧凑视图，用特定约定来表示某些语法种类，从而更便于快速阅读。
  这个实例会省略源位置信息。

 : 美化器

  Lean 的美化器会尝试把语法渲染成它在源文件中的样子；但如果语法的嵌套结构与预期形状不符，它就会失败。

::::keepEnv
:::example "将语法表示为构造子" (file := "Representing Syntax as Constructors")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

可以在 {keywordOf Lean.Parser.Command.eval}`#eval` 的上下文中对语法进行引用，从而查看 {name}`Repr` 实例对它的表示；后者能在命令精译单子 {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行动作。
为了减小示例输出的体积，这里使用辅助函数 {lean}`removeSourceInfo` 在显示前移除源信息。
```lean
partial def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing
```

```lean (name := reprStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```

在第二个示例中，由引用插入的 {tech (key := "macro scopes")}[宏作用域] 可以在对 {name}`List.length` 的调用上看到。
```lean (name := reprStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (repr (removeSourceInfo stx.raw))
```
这里可以看到 {tech (key := "pre-resolved identifier")}[预解析标识符] {name}`List.length` 的内容：
```leanOutput reprStx2 (allowDiff := 2)
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toRawSubstring
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `List.length.«_@».Manual.NotationsMacros.SyntaxDef 1704743902) "_hygCtx") "_hyg") 2)
      [Lean.Syntax.Preresolved.decl `List.length []],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
:::
::::

{name}`ToString` 实例对 {name}`Syntax` 各构造子的表示如下：

 * {name Syntax.ident}`ident` 构造子会被表示为其底层名称。源信息和预解析名称不会显示。
 * {name Syntax.atom}`atom` 构造子会被表示为字符串。
 * {name Syntax.missing}`missing` 构造子会被表示为 `<missing>`。
 * {name Syntax.node}`node` 构造子的表示取决于它的种类。
   如果种类是 {lean}`` `null ``，那么该节点会按其子节点顺序用方括号表示。
   否则，该节点会表示为其种类，后跟子节点，两者都包在圆括号中。

:::example "将语法表示为字符串" (file := "Syntax as Strings")
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```
可以在 {keywordOf Lean.Parser.Command.eval}`#eval` 的上下文中对语法进行引用，从而查看其字符串表示；后者能在命令精译单子 {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行动作。

```lean (name := toStringStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (toString stx)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```

在第二个示例中，由引用插入的 {tech (key := "macro scopes")}[宏作用域] 可以在对 {name}`List.length` 的调用上看到。
```lean (name := toStringStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (toString stx)
```
```leanOutput toStringStx2 (allowDiff := 2)
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef.3168789510._hygCtx._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
:::

把语法做美化打印，通常在需要把它包含进面向用户的消息时最有用。
通常，Lean 会在需要时自动调用美化器。
不过，如果有需要，也可以显式调用 {name}`ppTerm`。

::::keepEnv
:::example "美化打印后的语法" (file := "Pretty-Printed Syntax")
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Command
```

可以在 {keywordOf Lean.Parser.Command.eval}`#eval` 的上下文中对语法进行引用，从而查看它的字符串表示；后者能在命令精译单子 {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行动作。
由于新的语法声明也会给美化器提供如何显示它们的说明，因此美化器需要一个配置对象。
这个上下文可以用一个辅助函数来构造：
```lean
def getPPContext : CommandElabM PPContext := do
  return {
    env := (← getEnv),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
```

```lean (name := ppStx1)
#eval show CommandElabM Unit from do
  let stx ← `(2 + 5)
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx1
2 + 5
```

在第二个示例中，由引用插入到 {name}`List.length` 上的 {tech (key := "macro scopes")}[宏作用域] 会让它显示成带匕首符号（`✝`）的形式。
```lean (name := ppStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```

美化打印会自动换行并插入缩进。
通常会有一个 {tech (key := "coercion")}[强制转换] 把美化器的输出转为 {name}`logInfo` 所期望的类型，并使用默认的布局宽度。
如果显式调用 {name Std.Format.pretty}`pretty` 并传入具名参数，就可以控制这个宽度。
```lean (name := ppStx3)
#eval do
  let flowers := #["Rose", "Daffodil", "Lily"]
  let manyFlowers := flowers ++ flowers ++ flowers
  let stx ← `(List.length [$(manyFlowers.map (quote (k := `term))),*])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo (fmt.pretty (width := 40))
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
:::


::::

```lean -show
end Inspecting
```

# 带类型的语法
%%%
tag := "typed-syntax"
%%%

语法还可以额外带上一个类型注解，用来指明它属于哪个 {tech (key := "syntax category")}[语法类别]。
{TODO}[在这里描述这个问题——复杂而不可见的内部不变量会导致奇怪的错误消息]
{name Lean.TSyntax}`TSyntax` 结构包含一个类型层面的语法类别列表，以及一棵语法树。
这个语法类别列表通常恰好只包含一个元素；在这种情况下，列表结构本身不会显示出来。

{docstring Lean.TSyntax}

{docstring Lean.SyntaxNodeKinds}

{tech (key := "Quasiquotations")}[准引用] 会阻止替换那些并非来自正确语法类别的带类型语法。
对于 Lean 的许多内建语法类别，都有一组 {tech (key := "coercions")}[强制转换]，可以把某一类语法适当地包装成另一类别的语法，例如从字符串字面量语法到项语法的强制转换。
此外，许多只对某些语法类别有效的辅助函数，也只会为相应的带类型语法定义。

```lean -show
/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```

{name Lean.TSyntax}`TSyntax` 的构造子是公开的，因此并没有机制阻止用户构造出破坏内部不变量的值。
使用 {name Lean.TSyntax}`TSyntax` 应被视为减少常见错误的一种方式，而不是彻底杜绝错误。


:::leanSection
```lean -show
open Lean Syntax
variable {ks : SyntaxNodeKinds} {sep : String}
```
除了 {name Lean.TSyntax}`TSyntax` 之外，还有一些类型表示语法数组，既有带分隔符的，也有不带分隔符的。
这些对应于语法声明或反引用中的 {TODO}[xref] 重复元素。
{lean}`TSyntaxArray ks` 是 {lean}`Array (TSyntax ks)` 的一个 {tech (key := "abbreviation")}[缩写]，而 {lean}`TSepArray ks sep` 是一个结构；这意味着可以用 {tech (key := "generalized field notation")}[广义字段记法] 将数组函数应用于 {name}`TSyntaxArray`，但不能应用于 {name}`TSepArray`。
{lean}`TSepArray ks` 和 {lean}`TSyntaxArray ks` 之间既有 {tech (key := "coercion")}[强制转换]，也有显式转换函数。
这种转换会在底层数组中插入或移除分隔符元素，其耗时与元素个数成线性关系。
:::

{docstring Lean.TSyntaxArray}

{docstring Lean.TSyntaxArray.raw}

{docstring Lean.Syntax.TSepArray}

{docstring Lean.Syntax.TSepArray.getElems +allowMissing}

{docstring Lean.Syntax.TSepArray.elemsAndSeps}

{docstring Lean.Syntax.TSepArray.ofElems}

{docstring Lean.Syntax.TSepArray.push +allowMissing}


# 别名

为常用的带类型语法形式提供了若干别名。
这些别名使代码可以在更高的抽象层次上书写。

{docstring Lean.Term}

{docstring Lean.Command}

{docstring Lean.Syntax.Level}

{docstring Lean.Syntax.Tactic}

{docstring Lean.Prec}

{docstring Lean.Prio}

{docstring Lean.Ident}

{docstring Lean.StrLit}

{docstring Lean.CharLit}

{docstring Lean.NameLit}

{docstring Lean.NumLit}

{docstring Lean.ScientificLit}

{docstring Lean.HygieneInfo}

# 构造语法的辅助函数
%%%
tag := "syntax-construction-helpers"
%%%

{docstring Lean.mkIdent +allowMissing}

{docstring Lean.mkIdentFrom}

{docstring Lean.mkIdentFromRef +allowMissing}

{docstring Lean.mkCIdent +allowMissing}

{docstring Lean.mkCIdentFrom}

{docstring Lean.mkCIdentFromRef +allowMissing}

{docstring Lean.Syntax.mkApp}

{docstring Lean.Syntax.mkCApp +allowMissing}

{docstring Lean.Syntax.mkLit +allowMissing}

{docstring Lean.Syntax.mkCharLit +allowMissing}

{docstring Lean.Syntax.mkStrLit +allowMissing}

{docstring Lean.Syntax.mkNumLit +allowMissing}

{docstring Lean.Syntax.mkNatLit +allowMissing}

{docstring Lean.Syntax.mkScientificLit +allowMissing}

{docstring Lean.Syntax.mkNameLit +allowMissing}

{docstring Lean.mkOptionalNode +allowMissing}

{docstring Lean.mkGroupNode +allowMissing}

{docstring Lean.mkHole +allowMissing}

## 引用数据
%%%
tag := "quote-class"
%%%

:::leanSection
```lean -show
open Lean
```
{name Lean.Quote}`Quote` 类型类允许把值转换成表示它们的带类型语法。
例如，{lean (type:="Term")}`quote 5` 表示 {lean (type := "Term")}``⟨.node .none `num #[.atom .none "5"]⟩``。
这个类型类按语法种类参数化；这使得同一个值可以在不同种类下得到合适的表示。
{name}`Quote` 的实例解析会将带类型语法的 {tech (key := "coercions")}[强制转换] 考虑在内。
语法种类的默认值是 {lean}`` `term ``。
```lean -show
/--
info: { raw := Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "5"] }
-/
#guard_msgs in
#eval (quote 5 : Term)
```
:::

:::paragraph
{name Lean.Quote.quote}`Quote.quote` 的结果并不保证一定能够成功精译。
一般来说，生成的语法会包含所有显式参数的引用形式，而省略隐式参数。

{docstring Lean.Quote +allowMissing}

定义 {name Lean.Quote}`Quote` 的实例时，应使用 {name Lean.mkCIdent}`mkCIdent` 和 {name Lean.Syntax.mkCApp}`mkCApp`，以避免生成的语法中发生变量捕获。
:::

:::example "定义 `Quote` 实例" (file := "Defining Quote Instances")
```lean -show
open Lean Syntax
```

为了引用一个类型为 {name}`Tree` 的树，这里使用 {name}`mkCIdent` 和 {name}`mkCApp` 来确保名字相近的局部绑定不会造成干扰。
使用双反引号可以确保构造子名称没有拼写错误，并且能够被正确解析。
```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

instance [Quote α] : Quote (Tree α) where
  quote := quoteTree
where
  quoteTree
    | .leaf =>
      mkCIdent ``Tree.leaf
    | .branch l v r =>
      mkCApp ``Tree.branch #[quoteTree l, quote v, quoteTree r]
```

:::

# 解码带类型语法
%%%
tag := "typed-syntax-helpers"
%%%

对于字面量，Lean 的解析器会生成一个只包含单个 {name Lean.Syntax.atom}`atom` 的节点。
内部原子保存着带源信息的字符串，而节点的种类则指定了应如何解释该原子。
这可能涉及解码字符串转义序列，或解释十六进制数字字面量。
本节中的辅助函数会执行正确的解释。

{docstring Lean.TSyntax.getId}

{docstring Lean.TSyntax.getName}

{docstring Lean.TSyntax.getNat}

{docstring Lean.TSyntax.getScientific}

{docstring Lean.TSyntax.getString}

{docstring Lean.TSyntax.getChar}

{docstring Lean.TSyntax.getHygieneInfo}

# 语法类别
%%%
tag := "syntax-categories"
%%%

Lean 的解析器中包含一张 {deftech (key := "syntax categories")}_语法类别_ 表，它们对应于上下文无关文法中的非终结符。
其中一些最重要的类别包括项、命令、宇宙层级、优先权、优先级，以及表示字面量等记号的那些类别。
通常，每个 {tech (key := "syntax kind")}[语法种类] 都对应一个类别。
可以使用 {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat` 来声明新类别。

:::syntax command (title := "声明语法类别")
声明一个新的语法类别。

```grammar
$[$_:docComment]?
declare_syntax_cat $_ $[(behavior := $_)]?
```
:::

前导标识符行为是一项高级特性，通常不需要修改。
它控制解析器在遇到标识符时的行为，有时会让该标识符被当作一个非保留关键字处理。
这用于避免把每个 {ref "tactics"}[策略] 的名字都变成保留关键字。

{docstring Lean.Parser.LeadingIdentBehavior}

# 语法规则
%%%
tag := "syntax-rules"
%%%

每个 {tech (key := "syntax category")}[语法类别] 都关联着一组 {deftech (key := "syntax rules")}_语法规则_，它们对应于上下文无关文法中的产生式。
语法规则可以使用 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令来定义。

:::syntax command (title := "语法规则")
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind
syntax$[:$p]? $[(name := $x)]? $[(priority := $p)]? $_* : $c
```
:::

与运算符和记法声明一样，文档注释的内容会在用户与新语法交互时显示给他们。
还可以添加属性，以便在生成的定义上调用编译期元程序。

语法规则与 {tech (key := "section scopes")}[节作用域] 的交互方式和属性、运算符、记法相同。
默认情况下，语法规则在任何传递导入了其定义所在模块的模块中都可供解析器使用；但也可以将其声明为 `scoped` 或 `local`，分别把可用范围限制为当前命名空间已被打开的上下文，或者当前的 {tech (key := "section scope")}[节作用域]。

当某个类别的多条语法规则都能匹配当前输入时，会使用 {tech (key := "local longest-match rule")}[局部最长匹配规则] 来从中选择一条。
与记法和运算符一样，如果最长匹配并列，就使用声明的优先级来决定采用哪个解析结果。
如果这样仍不能消除歧义，那么所有并列结果都会被保留下来。
精译器预计会尝试它们全部；当且仅当恰好有一个能够成功精译时，整体才算成功。

语法规则的优先级紧跟在 {keywordOf Lean.Parser.Command.syntax}`syntax` 关键字之后，它会限制解析器：只有当前优先级上下文至少达到所给值时，才使用这条新语法。
{TODO}[默认优先级]
与运算符和记法一样，语法规则也可以手动指定名字；如果没有指定，就会生成一个原本未使用的名字。
无论是手动提供还是自动生成，这个名字都会作为生成的 {name Lean.Syntax.node}`node` 的语法种类。

语法声明的主体比记法的主体更加灵活。
字符串字面量指定要匹配的原子。
子项可以来自任意语法类别，而不只是项；它们还可以是可选的，或可重复的，并且可以带或不带逗号分隔符。
语法规则中的标识符表示语法类别，而不像在记法中那样为子项命名。


最后，语法规则还要指明它扩展的是哪个语法类别。
在不存在的类别中声明语法规则会报错。

```lean -show
-- 验证前一段
/-- error: unknown category `nuhUh` -/
#check_msgs in
syntax "blah" : nuhUh
```


:::syntax stx -open (title := "语法说明符")
语法类别 `stx` 是可出现在 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令主体中的说明符语法。

字符串字面量会被解析为 {tech (key := "atoms")}[原子]（包括 `if`、`#eval`、`where` 等关键字）：
```grammar
$s:str
```
字符串中的前导和尾随空格不会影响解析，但在 Lean 的 {tech (key := "proof states")}[证明状态] 和错误消息中显示该语法时，它们会使 Lean 在相应位置插入空格。
通常，在语法规则中作为原子出现的合法标识符会变成保留关键字。
如果在字符串字面量前加上一个和号（`&`），就会抑制这一行为：
```grammar
&$s:str
```

标识符指定给定位置上期望的语法类别，并且可以选择性地提供一个优先级：{TODO}[这里的默认优先级？]
```grammar
$x:ident$[:$p]?
```

`*` 修饰符是克林星号，用于匹配前述语法的零次或多次重复。
它也可以写作 `many`。
```grammar
$s:stx *
```
`+` 修饰符匹配前述语法的一次或多次重复。
它也可以写作 `many1`。
```grammar
$s:stx +
```
`?` 修饰符会让子项变为可选，它匹配前述语法的零次或一次重复，但不能更多。
它也可以写作 `optional`。
```grammar
$s:stx ?
```
```grammar
optional($s:stx)
```

`,*` 修饰符匹配前述语法的零次或多次重复，并在其间穿插逗号。
它也可以写作 `sepBy`。
```grammar
$_:stx ,*
```

`,+` 修饰符匹配前述语法的一次或多次重复，并在其间穿插逗号。
它也可以写作 `sepBy1`。
```grammar
$_:stx ,+
```

`,*,?` 修饰符匹配前述语法的零次或多次重复，并在其间穿插逗号，同时允许在最后一次重复后再跟一个可选尾随逗号。
它也可以通过带 `allowTrailingSep` 修饰符的 `sepBy` 来书写。
```grammar
$_:stx ,*,?
```

`,+,?` 修饰符匹配前述语法的一次或多次重复，并在其间穿插逗号，同时允许在最后一次重复后再跟一个可选尾随逗号。
它也可以通过带 `allowTrailingSep` 修饰符的 `sepBy1` 来书写。
```grammar
$_:stx ,+,?
```

`<|>` 运算符也可以写作 `orelse`，它匹配两边任一语法。
不过，如果第一条分支消耗了任何记号，那么解析就会提交到这条分支，之后失败也不会回溯：
```grammar
$_:stx <|> $_:stx
```
```grammar
orelse($_:stx, $_:stx)
```

`!` 运算符匹配其参数的补集。
如果它的参数匹配失败，那么它就会成功，并重置解析状态。
```grammar
! $_:stx
```

语法说明符可以用括号分组。
```grammar
($_:stx)
```

重复也可以用 `many` 和 `many1` 来定义。
后者要求重复的语法至少出现一次。
```grammar
many($_:stx)
```
```grammar
many1($_:stx)
```

带分隔符的重复可以用 `sepBy` 和 `sepBy1` 来定义；它们分别匹配零次或多次出现，以及一次或多次出现，并由某种其他语法分隔。
它们有三种形式：
 * 两参数版本使用字符串字面量中给出的原子来解析分隔符，并且不允许尾随分隔符。
 * 三参数版本使用第三个参数来解析分隔符，而字符串原子只用于美化打印。
 * 四参数版本可以选择性地允许分隔符在序列末尾额外再出现一次。
    第四个参数必须字面上就是关键字 `allowTrailingSep`。

```grammar
sepBy($_:stx, $_:str)
```
```grammar
sepBy($_:stx, $_:str, $_:stx)
```
```grammar
sepBy($_:stx, $_:str, $_:stx, allowTrailingSep)
```
```grammar
sepBy1($_:stx, $_:str)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx, allowTrailingSep)
```
:::

::::keepEnv
:::example "解析配对的圆括号与方括号" (file := "Parsing Matched Parentheses and Brackets")

可以使用语法规则来定义一种只由配对圆括号和方括号组成的语言。
第一步是声明一个新的 {tech (key := "syntax category")}[语法类别]：
```lean
declare_syntax_cat balanced
```
接下来，可以为圆括号和方括号添加规则。
为了排除空字符串，基例由空的括号对构成。
```lean
syntax "(" ")" : balanced
syntax "[" "]" : balanced
syntax "(" balanced ")" : balanced
syntax "[" balanced "]" : balanced
syntax balanced balanced : balanced
```

为了让 Lean 的解析器能够在这些规则上工作，还必须把这个新语法类别嵌入到某个已经可解析的类别中：
```lean
syntax (name := termBalanced) "balanced " balanced : term
```

这些项无法被精译，但如果到达精译错误，就说明解析已经成功：
```lean
/--
error: elaboration function for `termBalanced` has not been implemented
  balanced ()
-/
#guard_msgs in
example := balanced ()

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced []
-/
#guard_msgs in
example := balanced []

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced [[]()([])]
-/
#guard_msgs in
example := balanced [[] () ([])]
```

同样地，如果括号不匹配，解析就会失败：
```syntaxError mismatch
example := balanced [() (]]
```
```leanOutput mismatch
<example>:1:25-1:26: unexpected token ']'; expected ')' or balanced
```
:::
::::

::::keepEnv
:::example "解析逗号分隔的重复" (file := "Parsing Comma-Separated Repetitions")
下面这条语法可以添加一种列表字面量变体：它要求使用双层方括号，并允许尾随逗号：
```lean
syntax "[[" term,*,? "]]" : term
```

再加上一条说明如何把它翻译成普通列表字面量的 {tech (key := "macro")}[宏]，就可以在测试中使用它。
```lean
macro_rules
  | `(term|[[$e:term,*]]) => `([$e,*])
```

```lean (name := evFunnyList)
#eval [["Dandelion", "Thistle",]]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```

:::
::::

# 缩进
%%%
tag := "syntax-indentation"
%%%

在内部，解析器会维护一个已保存的源位置。
语法规则可以包含与这些已保存位置交互的指令；当条件不满足时，这会导致解析失败。
像 {keywordOf Lean.Parser.Term.do}`do` 这样的缩进敏感构造会先保存一个源位置，在把这个已保存位置纳入考虑的同时解析其组成部分，然后再恢复原来的位置。

具体来说，缩进敏感性是通过把 {name Lean.Parser.withPosition}`withPosition` 或 {name Lean.Parser.withPositionAfterLinebreak}`withPositionAfterLinebreak`（它们会在开始解析某段其他语法时保存源位置）与 {name Lean.Parser.checkColGt}`colGt`、{name Lean.Parser.checkColGe}`colGe`、{name Lean.Parser.checkColEq}`colEq` 组合起来指定的；后者会将当前列与最近一次保存位置的列进行比较。
{name Lean.Parser.checkLineEq}`lineEq` 也可用于确保两个位置位于源文件的同一行上。

:::parserAlias withPosition
:::

:::parserAlias withoutPosition
:::

:::parserAlias withPositionAfterLinebreak
:::

:::parserAlias colGt
:::

:::parserAlias colGe
:::

:::parserAlias colEq
:::

:::parserAlias lineEq
:::


::::keepEnv
:::example "对齐的列" (file := "Aligned Columns")
这个用于记录笔记的语法接受一个项目符号列表，其中每一项都必须在同一列对齐。
```lean
syntax "note " ppLine withPosition((colEq "◦ " str ppLine)+) : term
```

这个语法没有关联的精译器或宏，但下面的示例可以被解析器接受：
```lean +error (name := noteEx1)
#check
  note
    ◦ "One"
    ◦ "Two"
```
```leanOutput noteEx1
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```

这条语法并不要求列表相对于起始记号缩进；若要提出这一要求，则需要额外的 `withPosition` 和 `colGt`。
```lean +error (name := noteEx15)
#check
  note
◦ "One"
◦ "Two"
```
```leanOutput noteEx15
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```


下面这些示例在语法上无效，因为项目符号所在的列并不一致。
```syntaxError noteEx2
#check
  note
    ◦ "One"
   ◦ "Two"
```
```leanOutput noteEx2
<example>:4:3-4:4: expected end of input
```

```syntaxError noteEx2
#check
  note
   ◦ "One"
     ◦ "Two"
```
```leanOutput noteEx2
<example>:4:5-4:6: expected end of input
```
:::
::::
