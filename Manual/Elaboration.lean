/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers
import Manual.ZhDocString.ZhDocString
import Manual.ZhDocString.Elaboration

import Manual.ValidatingProofs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Lean (Syntax SourceInfo)

open Illuminate in
def pipelineDiagram : Diagram SVG :=
  let resultStyle : TextStyle := { fontSize := 20, bold := true }
  let result :=
    Diagram.hsep (align := .bottom) 8
      [.text "✔" { resultStyle with color := Color.green }, .text "/" resultStyle, .text "✖" resultStyle]
      |>.pad 8
      |>.namedWithAnchors `result
  let codeLabel :=
    Diagram.text "Code.lean"
      (style := { fontFamily := "monospace", fontSize := 12 })
      |>.pad 12
  let code :=
    Diagram.paper
      (name := `source)
      (label := some codeLabel)
      (width := some 80)
      (height := some 100)
      (fill := Color.white)
  Diagram.grid (hSpacing := 70) (vSpacing := 50) #[
    #[some code,                            none],
    #[some (box `stx "Syntax\nTree"),        none],
    #[some (box `core "Core Type\nTheory"), some (box `kernel "Core Type\nTheory\n(no recursion)")],
    #[some (box `exe "Executable"),         some result]
  ]
  -- Arrows with stealth arrowheads and upright labels
    |>.connect `source.south `stx.north
      (label := lbl "Parsing") (arrowhead := ah)
    |>.connect `stx.south `core.north
      (label := lbl "Elaboration") (arrowhead := ah)
    |>.connect `core.south `exe.north
      (label := lbl "Compilation") (arrowhead := ah)
    |>.connect `core.east `kernel.west
      (label := lbl "Recursion\nElimination") (arrowhead := ah)
  -- Self-loop on Syntax Tree for macro expansion (left side)
    |>.connect
      { point := `stx.west, shift := ⟨0, -10⟩, angle := some (pi + pi / 7), pull := 3.5 }
      { point := `stx.west, shift := ⟨0, 10⟩, angle := some (0 - pi / 7), pull := 3.5 }
      (label := lbl "Macro\nExpansion") (arrowhead := ah)
  -- Kernel check arrow
    |>.connect `kernel.south `result.north
      (label := lbl "Kernel\nCheck") (arrowhead := ah)
where
  ah : Arrowhead := { type := .stealth }
  lbl (s : String) : Option (Label SVG) :=
    some { label := .text s { fontSize := 10 }, upright := true }
  box (name : Lean.Name) (label : String) (fontFamily := "sans-serif") : Diagram SVG :=
    Diagram.text label { fontSize := 12, fontFamily }
      |>.pad 12
      |>.filledFrame
        (fill := Color.white)
        (stroke := { color := Color.black, width := 1 })
        (cornerRadius := 6)
      |>.namedWithAnchors name



/-
#doc (Manual) "Elaboration and Compilation" =>
-/

#doc (Manual) "精译与编译" =>
%%%
file := "Elaboration and Compilation"
htmlSplit := .never
tag := "elaboration-and-compilation"
%%%

粗略地说，Lean 对源文件的处理可以分为如下几个阶段：


: 解析(Parsing)

  解析器将字符序列转换为 {lean}`Syntax` 类型的语法树。
  Lean 的解析器是可扩展的，因此 {lean}`Syntax` 类型非常通用。


: 宏(Macro)展开

  宏是一种替代变换，它用更基础的语法替换语法糖。
  宏展开的输入与输出均为 {lean}`Syntax` 类型。


: 精译(Elaboration)

  {deftech (key := "Lean elaborator") -normalize}[精译] 是将 Lean 用户层语法转换为其核心类型理论的过程。
  这个核心理论要简单得多，因此可信内核可以非常精简。
  精译还会产生元数据，如证明状态或表达式类型，这些元数据被用于 Lean 的交互特性，并存储于辅助表中。


: 内核检查

  Lean 的可信内核会检查精译器的输出，以保证其符合类型理论的规则。


: 编译(Compilation)

  编译器将精译后的 Lean 代码转换为可执行文件。

:::figure "Lean 精译与编译流程" (tag := "pipeline-overview")
```diagram
pipelineDiagram
```
:::


实际上，上述阶段并非严格依次发生。
Lean 解析一条 {tech (key := "command")}[命令]（顶层声明）、对其进行精译，并执行必要的内核检查。
宏展开属于精译的一部分；在转化某段语法之前，精译器会首先展开外层的宏。更深层的宏语法可能暂时保留，直到精译器处理到它们时才展开。
精译分为多类型：命令精译负责实现每条顶层命令的实际效果（如声明 {tech (key := "inductive types")}[归纳类型]、保存定义、表达式求值），而项(term)精译负责构造多种命令中所涉及的项（如类型签名、定义的右侧或需要求值的表达式）。策略执行是项精译的特例。


每当对一个命令进行精译时，Lean 的状态都会改变。
新定义或类型会被保存以备后续使用，语法也可能被扩展，或者无需显式限定即可引用的名称集合可能发生变化。
下一个命令会在状态更新后被解析与精译，并为后续命令更新状态。


# 解析
%%%
tag := "parser"
%%%


Lean 的解析器是个递归下降解析器，通过基于 Pratt 解析{citep pratt73}[] 的动态表来解决操作符的优先级与结合律问题。
在文法无歧义时解析器无需回溯；而对于有歧义的文法则用类似 Packrat 解析的记忆化表避免指数级的性能爆炸。
解析器可高度扩展：用户可在任何命令中新增语法，并立刻在下一条命令中可用。
当前{tech (key := "section scope")}[区段作用域]中的被打开的命名空间也会影响解析规则，因为解析器扩展可以被设置为仅在某给定命名空间开放时生效。


解析器在遇到歧义时会选择最长匹配。
如果不存在唯一的最长匹配，则两个匹配会都被保存在语法树的{deftech (key := "choice node")}[备选结点]中，等待精译器后续选择。
解析器失败时会返回 {lean}`Syntax.missing` 节点，以实现错误恢复。


解析成功后，解析器会保存足够信息以重建源文件。
解析失败时，无法解析的部分可能遗漏信息。
{lean}`SourceInfo` 记录了一段语法的来源信息，包括其在源文件的位置及其周围空白。
依据 {lean}`SourceInfo` 字段，{lean}`Syntax` 与源文件有三种关系：
 * {lean}`SourceInfo.original` 表示该语法值直接由解析器生成。
 * {lean}`SourceInfo.synthetic` 表示该语法值是编程产生的，例如由宏展开器生成。合成语法可以被标记为 _canonical_，此时 Lean 用户界面会将其视为用户所写。合成语法带有源文件中的位置，但不含首尾空白。
 * {lean}`SourceInfo.none` 表示与文件无对应关系。


解析器维护了一个 token 表，记录当前被视为保留字的单词。
定义新语法或打开命名空间可能会导致原本合法的标识符变为关键字。


Lean 文法中的每个产生式都会被命名，称为它的 {deftech (key := "kind")}_类别_(kind)。
这些语法类别很重要，因为它们是精译器查找语法解释的关键索引。


语法扩展将在{ref "language-extension"}[专门的章节]中详细介绍。


# 宏展开与精译
%%%
tag := "macro-and-elab"
%%%


在解析之后会进行精译。
_精译_的确切含义取决于被精译的对象：命令精译会对 Lean 状态产生副作用，而项精译则产生 Lean 核心依值类型理论中的项。
命令与项的精译都可能是递归的，这既由于命令组合子（如 {keywordOf Lean.Parser.Command.in}`in`），也因为项内部可能嵌套其它项。


命令与项精译具有不同的能力。
命令精译可以对环境产生副作用，并可在 {lean}`IO` 中执行任意计算。
Lean {deftech (key := "environment")}[环境]不仅含有从名字到定义的映射，还包括通过 {deftech (key := "environment extensions")}[环境扩展](environment extensions) 定义的其它数据——这是一种与环境关联的附加表；环境扩展可用于追踪大多数其它 Lean 代码信息，包括 {tactic}`simp` 引理、自定义美化输出器、以及编译器中间表示等内部实现。
命令精译还维护消息日志（包含编译器输出、警告、错误）、{tech (key := "info trees")}[信息树]（info trees, 用于各种交互特性，如显示证明状态、标识符补全、显示文档）、汇集的调试追踪、打开的 {tech (key := "section scopes")}[区段作用域]，以及与宏展开有关的内部状态。
项精译可以修改除开放作用域外所有这些域。此外，它还可使用所有工具实现从简洁友好的 Lean 语法构造出完整显式核心项，包括合一、类型类实例合成、类型检查等。


项与命令的精译第一步都是宏展开。
系统有个把语法种类映射到宏实现的表；宏实现是将宏语法转化为新语法的单子函数。
所有用于项、命令、策略和 Lean 任何可宏扩展部分的宏，都保存在同一个表内，并在同一单子中执行。
如果宏返回的语法仍为宏，那么会继续展开，直到得到非宏语法或达到最大嵌套次数，后者导致报错。
典型的宏往往只处理外层语法，子项不变。
这意味着即使顶层宏展开完成，下层语法中可能还存有宏调用。
新的宏可加入宏表。
定义新宏的详细说明见{ref "macros"}[宏]。


宏展开后，项与命令精译器会查表，根据语法种类调用相应精译过程。
项精译器会利用上述单子，根据语法和可选的期望类型生成核心表达式。
命令精译器接受语法，无返回值，但可对全局命令状态产生单子副作用。
虽然命令与项精译器都可以访问 {lean}`IO`，但副作用较少，常见例外是与外部工具或求解器交互。


精译器表可扩展，以新语法支持项与命令。详见{ref "elaborators"}[精译器]。
当命令或项内部包含其它命令或项时，会递归调用合适的精译器，并在调用前展开宏。
虽然单层语法的宏展开发生在精译之前，但整个流程中宏展开与精译是交错进行的。

## 信息树


与 Lean 代码交互时，需要比仅作依赖导入更多的信息。
例如，Lean 的交互环境可用于查看选中表达式的类型、逐步查看证明过程中每一个中间状态、浏览文档、或高亮所有被绑定变量的出现。
实现这些交互特性的必需信息被保存在精译期间的一个辅助表里，称为 {deftech (key := "info trees")}_信息树_。


```lean -show
open Lean.Elab (Info)
```


信息树将元数据与用户的原始语法相关联。它们的树结构与语法树的结构密切对应，尽管语法树中的某个节点可能有许多对应的信息树节点，用于记录其不同方面的信息。
这些元数据包括 Lean 核心语言中展开器的输出、某一时刻的证明状态、交互式标识符补全的建议等。
元数据也可以任意扩展；构造子 {lean}`Info.ofCustomInfo` 接受 {lean}`Dynamic` 类型，可用于为自定义代码行为或用户界面扩展添加自定义信息。


# 内核


Lean 值得信任的 {deftech (key := "kernel")}_内核_ 是一个小型、健壮的核心类型理论类型检查器实现。
它不包括语法层面的终止性检查，也不执行合一；终止性通过将所有递归函数精译为使用原语 {tech (key := "recursors")}[归递子] 得以保证，而合一在精译器阶段已完成。
在命令或项精译器向环境中加入新的归纳类型或定义之前，必须先通过内核检查，以防止精译过程中的潜在 bug。


Lean 的内核使用 C++ 实现。
另有 [Rust](https://github.com/ammkrn/nanoda_lib) 和 [Lean](https://github.com/digama0/lean4lean) 的独立重写版本。Lean 项目鼓励具有多种实现，以便相互交叉校验。


内核实现的语言是构造演算的一个变体，这是一种依值类型论，具备如下特性：
 * 完整依值类型
 * 可互递归且可嵌套递归的归纳类型
 * 一个 {tech (key := "impredicative")}[不可谓词化]、定义上证据无关且外延的 {tech (key := "propositions")}[命题] {tech (key := "universe")}[宇宙]
 * 一个 {tech (key := "predicative")}[谓词化]、非累积的数据宇宙层级
 * 含有定义化计算规则的 {ref "quotients"}[商类型]
 * 命题的函数外延性{margin}[函数外延性可通过商类型作为定理证明，但它过于重要，以致需要特别列出。]
 * 函数与乘积的定义性 {tech (key := "η-equivalence")}[η-等价]
 * 宇宙多态定义
 * 一致性：不存在类型为 {lean}`False` 的无公理闭项


```lean -show -keep
-- Test definitional eta for structures
structure A where
  x : Nat
  y : Int
example (a : A) : ⟨a.x, a.y⟩ = a := rfl
set_option linter.unusedVariables false in
inductive B where
  | mk (x : Nat) (y : Int) : B
example (b : B) : ⟨b.1, b.2⟩ = b := rfl
/--
error: Type mismatch
  rfl
has type
  ?m.836 = ?m.836
but is expected to have type
  e1 = e2
-/
#check_msgs in
example (e1 e2 : Empty) : e1 = e2 := rfl
```

该理论足够丰富，可以表达前沿数学研究内容，又足够简单，易于实现小巧高效的实现。
显式证明项的存在使得实现独立的证明检查器变得可行，提高了可信性。
详见 {citet carneiro19}[] 和 {citet ullrich23}[]。


Lean 的类型理论不具备主题归约(subject reduction)、定义等价不保证传递性、类型检查器可能不终止。
然而，这些元理论特性在实际中不会造成问题——传递性失败极为罕见，据现有资料，不终止只会在有意为之的代码中出现。
更重要的是，逻辑一致性不受影响。
实际中，表面上的不终止很难和程序太慢进行区分——后者才是问题出现的主因。
这些元理论性质是不可谓词化、可计算的商类型、定义性证据无关和命题外延性等特性造成——这些特性对于支持数学实践与实现自动化都非常有价值。


# 精译结果
%%%
tag := "elaboration-results"
%%%


Lean 的核心类型理论不包括模式匹配与递归定义。
它只提供底层的 {tech (key := "recursors")}[归递子]，可用于实现区分情况与原语递归。
因此，精译器必须将涉及模式匹配和递归的定义转化为使用归递器的定义。{margin}[更多关于递归定义精译细节见{ref "recursive-definitions"}[递归定义章节]。]
这种转化实际上相当于证明了函数对所有参数均终止，因为只有可转化为归递器的函数才保证终止。


这种转化分为两步：首先，在项精译期间，将用到的模式匹配替换为实现代码中特定分支选择的 {deftech (key := "auxiliary matching function")}_辅助匹配函数_（也称为 {deftech (key := "matcher function")}_匹配器函数_）。
这些辅助函数自身由归递器定义，且不必真的用到归递器的递归功能。{margin}[它们会使用 {ref "recursor-elaboration-helpers"}[归递器与精译帮助章节]所述 `casesOn` 构造的变体，这些变体专门用于减小代码体积。]
项精译器最终返回的核心项中，模式匹配已被这种特殊函数替代，但仍有递归出现。尚包含递归但其它方面已精译为核心语言的定义称为 {deftech (key := "pre-definition")}[预定义]。
若需在 Lean 输出里看到辅助模式匹配函数，可设置 {option}`pp.match` 为 {lean}`false`。

{zhOptionDocs pp.match ZhDoc.Option.pp.match}


```lean -show -keep
def third_of_five : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
set_option pp.match false

/--
info: @[reducible] def third_of_five._sparseCasesOn_1.{u_1, u} : {α : Type u} →
  {motive : List α → Sort u_1} →
    (t : List α) →
      ((head : α) → (tail : List α) → motive (head :: tail)) → (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t :=
fun {α} {motive} t cons =>
  List.rec (motive := fun t => (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t) (fun «else» => «else» ⋯)
    (fun head tail tail_ih «else» => cons head tail) t
-/
#check_msgs in
#print third_of_five._sparseCasesOn_1

/--
info: third_of_five.eq_def.{u_1} {α : Type u_1} (x✝ : List α) :
  third_of_five x✝ =
    third_of_five.match_1 (fun x => Option α) x✝ (fun head head_1 x head_2 head_3 => some x) fun x => none
-/
#check_msgs in
#check third_of_five.eq_def

/--
info: @[instance_reducible] def third_of_five.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : List α → Sort u_2) →
    (x : List α) →
      ((head head_1 x head_2 head_3 : α) → motive [head, head_1, x, head_2, head_3]) →
        ((x : List α) → motive x) → motive x :=
fun {α} motive x h_1 h_2 =>
  third_of_five._sparseCasesOn_1 x
    (fun head tail =>
      third_of_five._sparseCasesOn_1 tail
        (fun head_1 tail =>
          third_of_five._sparseCasesOn_1 tail
            (fun head_2 tail =>
              third_of_five._sparseCasesOn_1 tail
                (fun head_3 tail =>
                  third_of_five._sparseCasesOn_1 tail
                    (fun head_4 tail =>
                      third_of_five._sparseCasesOn_2 tail (h_1 head head_1 head_2 head_3 head_4) fun h =>
                        h_2 (head :: head_1 :: head_2 :: head_3 :: head_4 :: tail))
                    fun h => h_2 (head :: head_1 :: head_2 :: head_3 :: tail))
                fun h => h_2 (head :: head_1 :: head_2 :: tail))
            fun h => h_2 (head :: head_1 :: tail))
        fun h => h_2 (head :: tail))
    fun h => h_2 x
-/
#check_msgs in
#print third_of_five.match_1
```

:::paragraph
预定义随后被交由编译器和内核。
编译器收到未消去递归的预定义。
发送给内核的版本则经过第二次转化，将显式递归替换为使用 {ref "structural-recursion"}[归递子]、{ref "well-founded-recursion"}[良构递归](well-founded recursion)或其它方式。
此种分工原因有三：
 * 编译器可以编译 {ref "partial-unsafe"}[`partial`（偏）函数]，对于内核而言仅当作推理的不可见常量。
 * 编译器还能编译 {ref "partial-unsafe"}[`unsafe`（不安全）函数]，直接绕过内核。
 * 转化为归递子未必保留程序的成本模型，比如惰性与严格性，但编译后代码要可预测性能。其它递归证明手段转化出的内部项与原本的程序差异更大。

编译器会将中间表示保存在环境扩展。
:::


对于结构性递归函数，转化将用其类型的归递子。
这些函数在内核中高效，其定义等式在定义上成立，也容易理解。无法用类型归递器刻画的递归则用 {tech (key := "well-founded recursion")}[良构递归]，即在每次递归调用中需有某个 {tech (key := "measure")}_度量_下降性的证明；或者采用 {ref "partial-fixpoint"}[偏不动点](partial fixpoint)，后者在逻辑上以域理论刻画函数部分规范。
Lean 可自动推导大多数终止性证明，但部分需要手工。良构递归更灵活，但其结果在内核中执行较慢（由于携带度量下降证明），其定义等式通常仅在命题层成立。
为了为结构递归与良构递归函数提供统一接口并自我校验其正确性，精译器会证明 {deftech (key := "equational lemmas")}[等式引理]，将函数与其原始定义关联。
在函数的命名空间中，`eq_unfold` 直接将函数展开为初始定义，`eq_def` 将其与显式参数实例化后的定义关联，$`N` 个 `eq_N` 引理则将每个分支的匹配关联到对应右侧，并给出足够的假设以排除其它分支。


::::keepEnv
:::example "等式引理"
{lean}`thirdOfFive`定义如下:
```lean
def thirdOfFive : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
```
Lean会自动生成如下等式引理，将 {lean}`thirdOfFive` 与其定义关联

{lean}`thirdOfFive.eq_unfold` 表明当无参数时可展开为原始定义:
```signature
thirdOfFive.eq_unfold.{u_1} :
  @thirdOfFive.{u_1} = fun {α : Type u_1} x =>
    match x with
    | [head, head_1, x, head_2, head_3] => some x
    | x => none
```

{lean}`thirdOfFive.eq_def` 表明对任意参数可展开为带参数的定义：
```signature
thirdOfFive.eq_def.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    thirdOfFive x =
      match x with
      | [head, head_1, x, head_2, head_3] => some x
      | x => none
```

{lean}`thirdOfFive.eq_1` 给出首个定义等式:
```signature
thirdOfFive.eq_1.{u} {α : Type u}
    (head head_1 x head_2 head_3 : α) :
  thirdOfFive [head, head_1, x, head_2, head_3] = some x
```

{lean}`thirdOfFive.eq_2` 给出第二个定义等式:
```signature
thirdOfFive.eq_2.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    (∀ (head head_1 x_1 head_2 head_3 : α),
      x = [head, head_1, x_1, head_2, head_3] → False) →
    thirdOfFive x = none
```
最后的 {lean}`thirdOfFive.eq_2` 包含假设：第一个分支未能匹配（即列表非恰好五个元素）
:::
::::


::::keepEnv
:::example "递归等式引理"
{lean}`everyOther` 定义如下:
```lean
def everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
```

Lean 会自动生成等式引理，将 {lean}`everyOther` 的归递器实现与其原始递归定义关联。

{lean}`everyOther.eq_unfold` 表示`everyOther`无参数时的定义:
```signature
everyOther.eq_unfold.{u} :
  @everyOther.{u} = fun {α} x =>
    match x with
    | [] => []
    | [x] => [x]
    | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_def` 表示`everyOther`有参数时的定义:
```signature
everyOther.eq_def.{u} {α : Type u} :
  ∀ (x : List α),
    everyOther x =
      match x with
      | [] => []
      | [x] => [x]
      | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_1` 首个分支:
```signature
everyOther.eq_1.{u} {α : Type u} : everyOther [] = ([] : List α)
```

{lean}`everyOther.eq_2` 第二个分支:
```signature
everyOther.eq_2.{u} {α : Type u} (x : α) : everyOther [x] = [x]
```

{lean}`everyOther.eq_3` 第三个分支:
```signature
everyOther.eq_3.{u} {α : Type u} (x y : α) (xs : List α) :
  everyOther (x :: y :: xs) = x :: everyOther xs
```

由于模式互不重叠，等式引理无需添加前置假设。
:::
::::


整个模块精译完成、每项添加都通过内核检查后，对全局环境（含扩展）的更改被序列化为 {deftech (key := ".olean file")}[`.olean` 文件]。
在这些文件中，Lean 的项与值与内存中的形式相同，因此可直接进行内存映射。
所有添加新类型或定义到环境的代码路径，都需先经过内核检查。
由于 Lean 是一个高度打开灵活的系统，为防止恶写元程序绕过检查往环境加入未验值，可使用独立工具 `lean4checker` 验证 `.olean` 文件内环境是否通过内核检验。


除 `.olean` 文件外，精译器还会生成 `.ilean` 索引文件，供语言服务器使用。
它便于无需完整加载模块即可交互使用，比如定位定义的位置等。
`.ilean` 文件内容为实现细节，不同的lean版本可能不兼容。


最后，编译器会将保存在环境扩展中的函数中间表示翻译为 C 代码。
每个 Lean 模块都会产出一个 C 文件，随后由捆绑 C 编译器编译为本地代码。
若配置文件启用 `precompileModules` 选项，则该本地代码可被 Lean 动态加载和调用；否则将使用解释器。
对于大多数场景，编译开销大于省下的执行时间，但预编译策略、语言扩展等可大幅加速某些特定任务。


# 初始化
%%%
tag := "initialization"
%%%



在启动前，精译器必须正确初始化。
Lean 本身包含一套 {deftech (key := "initialization")}[初始化] 代码，须在加载任一模块及调用精译器前运行，以正确构造编译器初始状态。
此外，各依赖项本身也可贡献初始化代码，例如启动环境扩展。
内部层面，每种环境扩展分配唯一数组索引，数组大小等于注册扩展数，因此必须事先得知扩展数量以正确分配环境结构体空间。

Lean 内建初始化器运行后，模块头部被解析，依赖的 `.olean` 文件加载入内存。
一个包含各依赖环境并集的“预环境”会被创建。
随后所有依赖项指定的初始化代码会在解释器中执行。
此时环境扩展的数量可以确定，可将预环境重分配成扩展区大小正确的环境结构体。


:::syntax command (title := "初始化块")
用  {keywordOf Lean.Parser.Command.initialize}`initialize` 块可为模块添加初始化代码。
其内容像放在 {keywordOf Lean.Parser.Term.do}`do` 块内一样，在 {lean}`IO` 单子中执行。

有时初始化仅需副作用地扩展内部数据结构，此时预期类型为 {lean}`IO Unit`：
```grammar
initialize
  $cmd*
```

有时初始化需构造包含内部状态引用的值，如底层依赖环境扩展的属性。
这类 {keywordOf Lean.Parser.Command.initialize}`initialize` 需在 {lean}`IO` 单子下返回指定类型：
```grammar
initialize $x:ident : $t:term ←
  $cmd*
```
:::


:::syntax command (title := "编译器内部初始化器")
Lean 内部也定义了一些初始化时必须运行的代码。
但由于 Lean 是自举编译器，其自带初始化器必须优先于任何模块的加载执行。
这些初始化器用 {keywordOf Lean.Parser.Command.initialize}`builtin_initialize` 指定，不应该在编译器实现之外使用。

```grammar
builtin_initialize
  $cmd*
```
```grammar
builtin_initialize $x:ident : $t:term ←
  $cmd*
```
:::
