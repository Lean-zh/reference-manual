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

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Lean (Syntax SourceInfo)

/-
#doc (Manual) "Elaboration and Compilation" =>
-/

#doc (Manual) "繁释与编译" =>
%%%
file := "Elaboration and Compilation"
htmlSplit := .never
tag := "elaboration-and-compilation"
%%%

/-
Roughly speaking, Lean's processing of a source file can be divided into the following stages:
-/
粗略地说，Lean 对源文件的处理可以分为如下几个阶段：

/-
: Parsing

  The parser transforms sequences of characters into syntax trees of type {lean}`Syntax`.
  Lean's parser is extensible, so the {lean}`Syntax` type is very general.
-/

: 解析(Parsing)

  解析器将字符序列转换为 {lean}`Syntax` 类型的语法树。
  Lean 的解析器是可扩展的，因此 {lean}`Syntax` 类型非常通用。

/-
: Macro Expansion

  Macros are transformations that replace syntactic sugar with more basic syntax.
  Both the input and output of macro expansion have type {lean}`Syntax`.
-/

: 宏(Macro)展开

  宏是一种替代变换，它用更基础的语法替换语法糖。
  宏展开的输入与输出均为 {lean}`Syntax` 类型。

/-
: Elaboration

  {deftech key:="elaborator"}[Elaboration] is the process of transforming Lean's user-facing syntax into its core type theory.
  This core theory is much simpler, enabling the trusted kernel to be very small.
  Elaboration additionally produces metadata, such as proof states or the types of expressions, used for Lean's interactive features, storing them in a side table.
-/

: 繁释(Elaboration)

  {deftech key:="elaborator"}[繁释] 是将 Lean 用户层语法转换为其核心类型理论的过程。
  这个核心理论要简单得多，因此可信内核可以非常精简。
  繁释还会产生元数据，如证明状态或表达式类型，这些元数据被用于 Lean 的交互特性，并存储于辅助表中。

/-
: Kernel Checking

  Lean's trusted kernel checks the output of the elaborator to ensure that it follows the rules of the type theory.
-/

: 内核检查

  Lean 的可信内核会检查繁释器的输出，以保证其符合类型理论的规则。

/-
: Compilation

  The compiler transforms elaborated Lean code into executables that can be run.
-/

: 编译(Compilation)

  编译器将繁释后的 Lean 代码转换为可执行文件。

:::figure "The Lean 编译流程" (tag := "pipeline-overview")
![The Lean Pipeline](/static/figures/pipeline-overview.svg)
:::

/-
In reality, the stages described above do not strictly occur one after the other.
Lean parses a single {tech}[command] (top-level declaration), elaborates it, and performs any necessary kernel checks.
Macro expansion is part of elaboration; before translating a piece of syntax, the elaborator first expands any macros present at the outermost layer.
Macro syntax may remain at deeper layers, but it will be expanded when the elaborator reaches those layers.
There are multiple kinds of elaboration: command elaboration implements the effects of each top-level command (e.g. declaring {tech}[inductive types], saving definitions, evaluating expressions), while term elaboration is responsible for constructing the terms that occur in many commands (e.g. types in signatures, the right-hand sides of definitions, or expressions to be evaluated).
Tactic execution is a specialization of term elaboration.
-/

实际上，上述阶段并非严格依次发生。
Lean 解析一条 {tech key := "command"}[命令]（顶层声明）、对其进行繁释，并执行必要的内核检查。
宏展开属于繁释的一部分；在转化某段语法之前，繁释器会首先展开外层的宏。更深层的宏语法可能暂时保留，直到繁释器处理到它们时才展开。
繁释分为多类型：命令繁释负责实现每条顶层命令的实际效果（如声明 {tech key := "inductive types"}[归纳类型]、保存定义、表达式求值），而项(term)繁释负责构造多种命令中所涉及的项（如类型签名、定义的右侧或需要求值的表达式）。策略执行是术语繁释的特例。

/-
When a command is elaborated, the state of Lean changes.
New definitions or types may have been saved for future use, the syntax may be extended, or the set of names that can be referred to without explicit qualification may have changed.
The next command is parsed and elaborated in this updated state, and itself updates the state for subsequent commands.
-/

每当对一个命令进行繁释时，Lean 的状态都会改变。
新定义或类型会被保存以备后续使用，语法也可能被扩展，或着没有显示指定的限定式的名称集合会发生变化。
下一个命令会在状态更新后被解析与繁释，并为后续命令更新状态。

/-
# Parsing
-/

# 解析
%%%
tag := "parser"
%%%

/-
Lean's parser is a recursive-descent parser that uses dynamic tables based on Pratt parsing{citep pratt73}[] to resolve operator precedence and associativity.
When grammars are unambiguous, the parser does not need to backtrack; in the case of ambiguous grammars, a memoization table similar to that used in Packrat parsing avoids exponential blowup.
Parsers are highly extensible: users may define new syntax in any command, and that syntax becomes available in the next command.
The open namespaces in the current {tech}[section scope] also influence which parsing rules are used, because parser extensions may be set to be active only when a given namespace is open.
-/

Lean 的解析器是个递归下降解析器，通过基于 Pratt 解析{citep pratt73}[] 的动态表来解决操作符的优先级与结合律问题。
在文法无歧义时解析器无需回溯；而对于有歧义的文法则用类似 Packrat 解析的记忆化表避免指数级的性能爆炸。
解析器可高度扩展：用户可在任何命令中新增语法，并立刻在下一条命令中可用。
当前{tech key := "section scope"}[区段作用域]中的被打开的命名空间也会影响解析规则，因为解析器扩展可以被设置为仅在某给定命名空间开放时生效。

/-
When ambiguity is encountered, the longest matching parse is selected.
If there is no unique longest match, then both matching parses are saved in the syntax tree in a {deftech}[choice node] to be resolved later by the elaborator.
When the parser fails, it returns a {lean}`Syntax.missing` node, allowing for error recovery.
-/

解析器在遇到歧义时会选择最长匹配。
如果不存在唯一的最长匹配，则两个匹配会都被保存在语法树的{deftech key := "choice node"}[备选结点]中，等待繁释器后续选择。
解析器失败时会返回 {lean}`Syntax.missing` 节点，以实现错误恢复。

/-
When successful, the parser saves sufficient information to reconstruct the original source file.
Unsuccessful parses may miss some information for the regions of the file that cannot be parsed.
The {lean}`SourceInfo` record type records information about the origin of a piece of syntax, including its source location and the surrounding whitespace.
Based on the {lean}`SourceInfo` field, there are three relationships that {lean}`Syntax` can have to a source file:
 * {lean}`SourceInfo.original` indicates that the syntax value was produced directly by the parser.
 * {lean}`SourceInfo.synthetic` indicates that the syntax value was produced programmatically, e.g. by the macro expander. Synthetic syntax may nonetheless be marked _canonical_, in which case the Lean user interface treats it as if the user had written it. Synthetic syntax is annotated with positions in the original file, but does not include leading or trailing whitespace.
 * {lean}`SourceInfo.none` indicates no relationship to a file.
-/

解析成功后，解析器会保存足够信息以重建源文件。
解析失败时，无法解析的部分可能遗漏信息。
{lean}`SourceInfo` 记录了一段语法的来源信息，包括其在源文件的位置及其周围空白。
依据 {lean}`SourceInfo` 字段，{lean}`Syntax` 与源文件有三种关系：
 * {lean}`SourceInfo.original` 表示该语法值直接由解析器生成。
 * {lean}`SourceInfo.synthetic` 表示该语法值是编程产生的，例如由宏展开器生成。合成语法可以被标记为 _canonical_，此时 Lean 用户界面会将其视为用户所写。合成语法带有源文件中的位置，但不含首尾空白。
 * {lean}`SourceInfo.none` 表示与文件无对应关系。

/-
The parser maintains a token table that tracks the reserved words that are currently part of the language.
Defining new syntax or opening namespaces can cause a formerly-valid identifier to become a keyword.
-/

解析器维护了一个 token 表，记录当前被视为保留字的单词。
定义新语法或打开命名空间可能会导致原本合法的标识符变为关键字。

/-
Each production in Lean's grammar is named.
The name of a production is called its {deftech}_kind_.
These syntax kinds are important, because they are the key used to look up the interpretation of the syntax in the elaborator's tables.
-/

Lean 文法中的每个产生式都会被命名，称为它的 {deftech key := "kind"}_类别_(kind)。
这些语法类别很重要，因为它们是繁释器查找语法解释的关键索引。

/-
Syntax extensions are described in more detail in {ref "language-extension"}[a dedicated chapter].
-/

语法扩展将在{ref "language-extension"}[专门的章节]中详细介绍。

/-
# Macro Expansion and Elaboration
-/

# 宏展开与繁释
%%%
tag := "macro-and-elab"
%%%

/-
Having parsed a command, the next step is to elaborate it.
The precise meaning of _elaboration_ depends on what is being elaborated: elaborating a command effects a change in the state of Lean, while elaborating a term results in a term in Lean's core type theory.
Elaboration of both commands and terms may be recursive, both because of command combinators such as {keywordOf Lean.Parser.Command.in}`in` and because terms may contain other terms.
-/

在解析之后会进行繁释。
_繁释_的确切含义取决于被繁释的对象：命令繁释会对 Lean 状态产生副作用，而项繁释则产生 Lean 核心依值类型理论中的项。
命令与项的繁释都可能是递归的，这既由于命令组合子（如 {keywordOf Lean.Parser.Command.in}`in`），也因为项内部可能嵌套其它项。

/-
Command and term elaboration have different capabilities.
Command elaboration may have side effects on an environment, and it has access to run arbitrary computations in {lean}`IO`.
Lean environments contain the usual mapping from names to definitions along with additional data defined in {deftech}[environment extensions], which are additional tables associated with an environment; environment extensions are used to track most other information about Lean code, including {tactic}`simp` lemmas, custom pretty printers, and internals such as the compiler's intermediate representations.
Command elaboration also maintains a message log with the contents of the compiler's informational output, warnings, and errors, a set of {tech}[info trees] that associate metadata with the original syntax (used for interactive features such as displaying proof states, identifier completion, and showing documentation), accumulated debugging traces, the open {tech}[section scopes], and some internal state related to macro expansion.
Term elaboration may modify all of these fields except the open scopes.
Additionally, it has access to all the machinery needed to create fully-explicit terms in the core language from Lean's terse, friendly syntax, including unification, type class instance synthesis, and type checking.
-/

命令与项繁释具有不同的能力。
命令繁释可以对环境产生副作用，并可在 {lean}`IO` 中执行任意计算。
Lean 的环境不仅含有从名字到定义的映射，还包括通过 {deftech key := "environment extensions"}[环境扩展](environment extensions) 定义的其它数据——这是一种与环境关联的附加表；环境扩展可用于追踪大多数其它 Lean 代码信息，包括 {tactic}`simp` 引理、自定义美化输出器、以及编译器中间表示等内部实现。
命令繁释还维护消息日志（包含编译器输出、警告、错误）、{tech key := "info trees"}[信息树]（info trees, 用于各种交互特性，如显示证明状态、标识符补全、显示文档）、汇集的调试追踪、打开的 {tech key := "section scopes"}[区段作用域]，以及与宏展开有关的内部状态。
项繁释可以修改除开放作用域外所有这些域。此外，它还可使用所有工具实现从简洁友好的 Lean 语法构造出完整显式核心项，包括归一、类型类实例合成、类型检查等。

/-
The first step in both term and command elaboration is macro expansion.
There is a table that maps syntax kinds to macro implementations; macro implementations are monadic functions that transform the macro syntax into new syntax.
Macros are saved in the same table and execute in the same monad for terms, commands, tactics, and any other macro-extensible part of Lean.
If the syntax returned by the macro is itself a macro, then that syntax is again expanded—this process is repeated until either a syntax whose kind is not a macro is produced, or until a maximum number of iterations is reached, at which point Lean produces an error.
Typical macros process some outer layer of their syntax, leaving some subterms untouched.
This means that even when macro expansion has been completed, there still may be macro invocations remaining in the syntax below the top level.
New macros may be added to the macro table.
Defining new macros is described in detail in {ref "macros"}[the section on macros].
-/

项与命令的繁释第一步都是宏展开。
系统有个把语法种类映射到宏实现的表；宏实现是将宏语法转化为新语法的单子函数。
所有用于项、命令、策略和 Lean 任何可宏扩展部分的宏，都保存在同一个表内，并在同一单子中执行。
如果宏返回的语法仍为宏，那么会继续展开，直到得到非宏语法或达到最大嵌套次数，后者导致报错。
典型的宏往往只处理外层语法，子项不变。
这意味着即使顶层宏展开完成，下层语法中可能还存有宏调用。
新的宏可加入宏表。
定义新宏的详细说明见{ref "macros"}[宏]。

/-
After macro expansion, both the term and command elaborators consult tables that map syntax kinds to elaboration procedures.
Term elaborators map syntax and an optional expected type to a core language expression using the very powerful monad mentioned above.
Command elaborators accept syntax and return no value, but may have monadic side effects on the global command state.
While both term and command elaborators have access to {lean}`IO`, it's unusual that they perform side effects; exceptions include interactions with external tools or solvers.
-/

宏展开后，项与命令繁释器会查表，根据语法种类调用相应繁释过程。
项繁释器会利用上述单子，根据语法和可选的期望类型生成核心表达式。
命令繁释器接受语法，无返回值，但可对全局命令状态产生单子副作用。
虽然命令与项繁释器都可以访问 {lean}`IO`，但副作用较少，常见例外是与外部工具或求解器交互。

/-
The elaborator tables may be extended to enable the use of new syntax for both terms and commands by extending the tables.
See {ref "elaborators"}[the section on elaborators] for a description of how to add additional elaborators to Lean.
When commands or terms contain further commands or terms, they recursively invoke the appropriate elaborator on the nested syntax.
This elaborator will then expand macros before invoking elaborators from the table.
While macro expansion occurs prior to elaboration for a given “layer” of the syntax, macro expansion and elaboration are interleaved in general.
-/

繁释器表可扩展，以新语法支持项与命令。详见{ref "elaborators"}[繁释器]。
当命令或项内部包含其它命令或项时，会递归调用合适的繁释器，并在调用前展开宏。
虽然单层语法的宏展开发生在繁释之前，但整个流程中宏展开与繁释是交错进行的。

/-
## Info Trees
-/
## 信息树

/-
When interacting with Lean code, much more information is needed than when simply importing it as a dependency.
For example, Lean's interactive environment can be used to view the types of selected expressions, to step through all the intermediate states of a proof, to view documentation, and highlight all occurrences of a bound variable.
The information necessary to use Lean interactively is stored in a side table called the  {deftech}_info trees_ during elaboration.
-/

与 Lean 代码交互时，需要比仅作依赖导入更多的信息。
例如，Lean 的交互环境可用于查看选中表达式的类型、逐步查看证明过程中每一个中间状态、浏览文档、或高亮所有被绑定变量的出现。
实现这些交互特性的必需信息被保存在繁释期间的一个辅助表里，称为 {deftech key := "info trees"}_信息树_。


````lean (show := false)
open Lean.Elab (Info)
deriving instance TypeName for Unit
````

/-
Info trees relate metadata to the user's original syntax.
Their tree structure corresponds closely to the tree structure of the syntax, although a given node in the syntax tree may have many corresponding info tree nodes that document different aspects of it.
This metadata includes the elaborator's output in Lean's core language, the proof state active at a given point, suggestions for interactive identifier completion, and much more.
The metadata can also be arbitrarily extended; the constructor {lean}`Info.ofCustomInfo` accepts a {lean}`Dynamic` type.
This can be used to add information to be used by custom code actions or other user interface extensions.
-/

信息树将元数据与用户的原始语法相关联。它们的树结构与语法树的结构密切对应，尽管语法树中的某个节点可能有许多对应的信息树节点，用于记录其不同方面的信息。
这些元数据包括 Lean 核心语言中展开器的输出、某一时刻的证明状态、交互式标识符补全的建议等。
元数据也可以任意扩展；构造子 {lean}`Info.ofCustomInfo` 接受 {lean}`Dynamic` 类型，可用于为自定义代码行为或用户界面扩展添加自定义信息。

/-
# The Kernel
-/

# 内核

/-
Lean's trusted {deftech}_kernel_ is a small, robust implementation of a type checker for the core type theory.
It does not include a syntactic termination checker, nor does it perform unification; termination is guaranteed by elaborating all recursive functions into uses of primitive {tech}[recursors], and unification is expected to have already been carried out by the elaborator.
Before new inductive types or definitions are added to the environment by the command or term elaborators, they must be checked by the kernel to guard against potential bugs in elaboration.
-/

Lean 值得信任的 {deftech key := "kernel"}_内核_ 是一个小型、健壮的核心类型理论类型检查器实现。
它不包括语法层面的终止性检查，也不执行归一；终止性通过将所有递归函数繁释为使用原语 {tech key:= "recursors"}[归递子] 得以保证，而归一在繁释器阶段已执行。
在命令或项繁释器向环境中加入新的归纳类型或定义之前，必须先通过内核检查，以防止繁释过程中的潜在 bug。

/-
Lean's kernel is written in C++.
There are independent re-implementations in [Rust](https://github.com/ammkrn/nanoda_lib) and [Lean](https://github.com/digama0/lean4lean), and the Lean project is interested in having as many implementations as possible so that they can be cross-checked against each other.
-/

Lean 的内核使用 C++ 实现。
另有 [Rust](https://github.com/ammkrn/nanoda_lib) 和 [Lean](https://github.com/digama0/lean4lean) 的独立重写版本。Lean 项目鼓励具有多种实现，以便相互交叉校验。

/-
The language implemented by the kernel is a version of the Calculus of Constructions, a dependent type theory with the following features:
 * Full dependent types
 * Inductively-defined types that may be mutually inductive or include recursion nested under other inductive types
 * An {tech}[impredicative], definitionally proof-irrelevant, extensional {tech}[universe] of {tech}[propositions]
 * A {tech}[predicative], non-cumulative hierarchy of universes of data
 * {ref "quotients"}[Quotient types] with a definitional computation rule
 * Propositional function extensionality{margin}[Function extensionality is a theorem that can be proved using quotient types, but it is such an important consequence that it's worth listing separately.]
 * Definitional {tech key:="η-equivalence"}[η-equality] for functions and products
 * Universe-polymorphic definitions
 * Consistency: there is no axiom-free closed term of type {lean}`False`
-/

内核实现的语言是构造演算的一个变体，这是一种依值类型论，具备如下特性(译者注: 由于下列特性有过多的专有名词，故同时列出英文以便更好理解)：
 * 完整依值类型 / Full dependent types
 * 可互递归且可嵌套递归的归纳类型 / Inductively-defined types that may be mutually inductive or include recursion nested under other inductive types
 * 一个 {tech key := "impredicative"}[不可谓词化](impredicative)、定义上证据无关(proof-irrelevant)且外延的 {tech key:= "propositions"}[命题] {tech key := "universe"}[宇宙] / An {tech}[impredicative], definitionally proof-irrelevant, extensional {tech}[universe] of {tech}[propositions]
 * 一个 {tech key := "predicative"}[谓词化]、非累积的数据宇宙层级 / A {tech}[predicative], non-cumulative hierarchy of universes of data
 * 含有定义化计算规则的 {ref "quotients"}[商类型] / {ref "quotients"}[Quotient types] with a definitional computation rule
 * 命题的函数外延性 / Propositional function extensionality{margin}[函数外延性可通过商类型作为定理证明，但它过于重要，以致需要特别列出。]
 * 函数与乘积的定义性 {tech key:="η-equivalence"}[η-等价](η-equality) / Definitional {tech key:="η-equivalence"}[η-equality] for functions and products
 * 宇宙多态定义 / Universe-polymorphic definitions
 * 一致性：不存在无公理闭项类型为 {lean}`False` 的情况 / Consistency: there is no axiom-free closed term of type {lean}`False`


```lean (show := false) (keep := false)
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
error: type mismatch
  rfl
has type
  ?m.848 = ?m.848 : Prop
but is expected to have type
  e1 = e2 : Prop
-/
#check_msgs in
example (e1 e2 : Empty) : e1 = e2 := rfl
```
/-
This theory is rich enough to express leading-edge research mathematics, and yet simple enough to admit a small, efficient implementation.
The presence of explicit proof terms makes it feasible to implement independent proof checkers, increasing our confidence.
It is described in detail by {citet carneiro19}[] and {citet ullrich23}[].
-/

该理论足够丰富，可以表达前沿数学研究内容，又足够简单，易于实现小巧高效的实现。
显式证明项的存在使得实现独立的证明检查器变得可行，提高了可信性。
详见 {citet carneiro19}[] 和 {citet ullrich23}[]。

/-
Lean's type theory does not feature subject reduction, the definitional equality is not necessarily transitive, and it is possible to make the type checker fail to terminate.
None of these metatheoretic properties cause problems in practice—failures of transitivity are exceedingly rare, and as far as we know, non-termination has not occurred except when crafting code specifically to exercise it.
Most importantly, logical soundness is not affected.
In practice, apparent non-termination is indistinguishable from sufficiently slow programs; the latter are the causes observed in the wild.
These metatheoretic properties are a result of having impredicativity, quotient types that compute, definitional proof irrelevance, and propositional extensionality; these features are immensely valuable both to support ordinary mathematical practice and to enable automation.
-/

Lean 的类型理论不具备主题归约(subject reduction)、定义等价不保证传递性、类型检查器可能不终止。
然而，这些元理论特性在实际中不会造成问题——传递性失败极为罕见，据现有资料，不终止只会在有意为之的代码中出现。
更重要的是，逻辑一致性不受影响。
实际中，表面上的不终止很难和程序太慢进行区分——后者才是问题出现的主因。
这些元理论性质瑟是不可谓词化、可计算的商类型、定义性证据无关和命题外延性等特性造成——这些特性对于支持数学实践与实现自动化都非常有价值。

/-
# Elaboration Results
-/

# 繁释结果
%%%
tag := "elaboration-results"
%%%

/-
Lean's core type theory does not include pattern matching or recursive definitions.
Instead, it provides low-level {tech}[recursors] that can be used to implement both case distinction and primitive recursion.
Thus, the elaborator must translate definitions that use pattern matching and recursion into definitions that use recursors.{margin}[More details on the elaboration of recursive definitions is available in the {ref "recursive-definitions"}[dedicated section] on the topic.]
This translation is additionally a proof that the function terminates for all potential arguments, because all functions that can be translated to recursors also terminate.
-/

Lean 的核心类型理论不包括模式匹配与递归定义。
它只提供底层的 {tech key := "recursors"}[归递子]，可用于实现区分情况与原语递归。
因此，繁释器必须将涉及模式匹配和递归的定义转化为使用归递器的定义。{margin}[更多关于递归定义繁释细节见{ref "recursive-definitions"}[递归定义章节]。]
这种转化实际上相当于证明了函数对所有参数均终止，因为只有可转化为归递器的函数才保证终止。

/-
The translation to recursors happens in two phases: during term elaboration, uses of pattern matching are replaced by appeals to {deftech}_auxiliary matching functions_ that implement the particular case distinction that occurs in the code.
These auxiliary functions are themselves defined using recursors, though they do not make use of the recursors' ability to actually implement recursive behavior.{margin}[They use the `casesOn` construction that is described in the {ref "recursor-elaboration-helpers"}[section on recursors and elaboration].]
The term elaborator thus returns core-language terms in which pattern matching has been replaced with the use of special functions that implement case distinction, but these terms may still contain recursive occurrences of the function being defined.
A definition that still includes recursion, but has otherwise been elaborated to the core language, is called a {deftech}[pre-definition].
To see auxiliary pattern matching functions in Lean's output, set the option {option}`pp.match` to {lean}`false`.
-/

这种转化分为两步：首先，在项繁释期间，将用到的模式匹配替换为实现特定区分的 {deftech key:="auxiliary matching function"}_辅助匹配函数_。
这些辅助函数自身由归递器定义，且不必真的用到归递器的递归功能。{margin}[它们会用到 `casesOn`，具体参见{ref "recursor-elaboration-helpers"}[归递器与繁释帮助章节]。]
项繁释器最终返回的核心项中，模式匹配已被这种特殊函数替代，但仍有递归出现。尚包含递归但其它方面已繁释为核心语言的定义称为 {deftech key := "pre-definition"}[预定义]。
若需在 Lean 输出里看到辅助模式匹配函数，可设置 {option}`pp.match` 为 {lean}`false`。

{zhOptionDocs pp.match ZhDoc.Option.pp.match}


```lean (show := false) (keep := false)
def third_of_five : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
set_option pp.match false
/--
info: third_of_five.eq_def.{u_1} {α : Type u_1} (x✝ : List α) :
  third_of_five x✝ = third_of_five.match_1 (fun x => Option α) x✝ (fun head head x head head => some x) fun x => none
-/
#check_msgs in
#check third_of_five.eq_def
/--
info: def third_of_five.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : List α → Sort u_2) →
    (x : List α) →
      ((head head_1 x head_2 head_3 : α) → motive [head, head_1, x, head_2, head_3]) →
        ((x : List α) → motive x) → motive x :=
fun {α} motive x h_1 h_2 =>
  List.casesOn x (h_2 []) fun head tail =>
    List.casesOn tail (h_2 [head]) fun head_1 tail =>
      List.casesOn tail (h_2 [head, head_1]) fun head_2 tail =>
        List.casesOn tail (h_2 [head, head_1, head_2]) fun head_3 tail =>
          List.casesOn tail (h_2 [head, head_1, head_2, head_3]) fun head_4 tail =>
            List.casesOn tail (h_1 head head_1 head_2 head_3 head_4) fun head_5 tail =>
              h_2 (head :: head_1 :: head_2 :: head_3 :: head_4 :: head_5 :: tail)
-/
#check_msgs in
#print third_of_five.match_1
```
/-
:::paragraph
The pre-definition is then sent to the compiler and to the kernel.
The compiler receives the pre-definition as-is, with recursion intact.
The version sent to the kernel, on the other hand, undergoes a second transformation that replaces explicit recursion with {ref "structural-recursion"}[uses of recursors], {ref "well-founded-recursion"}[well-founded recursion], or .
This split is for three reasons:
 * The compiler can compile {ref "partial-unsafe"}[`partial` functions] that the kernel treats as opaque constants for the purposes of reasoning.
 * The compiler can also compile {ref "partial-unsafe"}[`unsafe` functions] that bypass the kernel entirely.
 * Translation to recursors does not necessarily preserve the cost model expected by programmers, in particular laziness vs strictness, but compiled code must have predictable performance.
   The other strategies used to justify recursive definitions result in internal terms that are even further from the program as it was written.

The compiler stores an intermediate representation in an environment extension.
:::
-/

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

/-
For straightforwardly structurally recursive functions, the translation will use the type's recursor.
These functions tend to be relatively efficient when run in the kernel, their defining equations hold definitionally, and they are easy to understand.
Functions that use other patterns of recursion that cannot be captured by the type's recursor are translated using {deftech}[well-founded recursion], which is structural recursion on a proof that some {deftech}_measure_ decreases at each recursive call, or using {ref "partial-fixpoint"}[partial fixpoints], which logically capture at least part of a function's specification by appealing to domain-theoretic constructions.
Lean can automatically derive many of these termination proofs, but some require manual proofs.
Well-founded recursion is more flexible, but the resulting functions are often slower to execute in the kernel due to the proof terms that show that a measure decreases, and their defining equations may hold only propositionally.
To provide a uniform interface to functions defined via structural and well-founded recursion and to check its own correctness, the elaborator proves {deftech}[equational lemmas] that relate the function to its original definition.
In the function's namespace, `eq_unfold` relates the function directly to its definition, `eq_def` relates it to the definition after instantiating implicit parameters, and $`N` lemmas `eq_N` relate each case of its pattern-matching to the corresponding right-hand side, including sufficient assumptions to indicate that earlier branches were not taken.
-/

对于结构性递归函数，转化将用其类型的归递子。
这些函数在内核中高效，其定义等式在定义上成立，也容易理解。无法用类型归递器刻画的递归则用 {deftech key := "well-founded recursion"}[良构递归]，即在每次递归调用中需有某个 {deftech key := "measure"}_度量_下降性的证明；或者采用 {ref "partial-fixpoint"}[偏不动点](partial fixpoint)，后者在逻辑上以域理论刻画函数部分规范。
Lean 可自动推导大多数终止性证明，但部分需要手工。良构递归更灵活，但其结果在内核中执行较慢（由于携带度量下降证明），其定义等式通常仅在命题层成立。
为了为结构递归与良构递归函数提供统一接口并自我校验其正确性，繁释器会证明 {deftech key := "equational lemmas"}[等式引理]，将函数与其原始定义关联。
在函数的命名空间中，`eq_unfold` 直接将函数展开为初始定义，`eq_def` 将其与显式参数实例化后的定义关联，$`N` 个 `eq_N` 引理则将每个分支的匹配关联到对应右侧，并给出足够的假设以排除其它分支。

/-
::::keepEnv
:::example "Equational Lemmas"
Given the definition of {lean}`thirdOfFive`:
```lean
def thirdOfFive : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
```
equational lemmas are generated that relate {lean}`thirdOfFive` to its definition.

{lean}`thirdOfFive.eq_unfold` states that it can be unfolded to its original definition when no arguments are provided:
```signature
thirdOfFive.eq_unfold.{u_1} :
  @thirdOfFive.{u_1} = fun {α : Type u_1} x =>
    match x with
    | [head, head_1, x, head_2, head_3] => some x
    | x => none
```

{lean}`thirdOfFive.eq_def` states that it matches its definition when applied to arguments:
```signature
thirdOfFive.eq_def.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    thirdOfFive x =
      match x with
      | [head, head_1, x, head_2, head_3] => some x
      | x => none
```

{lean}`thirdOfFive.eq_1` shows that its first defining equation holds:
```signature
thirdOfFive.eq_1.{u} {α : Type u}
    (head head_1 x head_2 head_3 : α) :
  thirdOfFive [head, head_1, x, head_2, head_3] = some x
```

{lean}`thirdOfFive.eq_2` shows that its second defining equation holds:
```signature
thirdOfFive.eq_2.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    (∀ (head head_1 x_1 head_2 head_3 : α),
      x = [head, head_1, x_1, head_2, head_3] → False) →
    thirdOfFive x = none
```
The final lemma {lean}`thirdOfFive.eq_2` includes a premise that the first branch could not have matched (that is, that the list does not have exactly five elements).
:::
::::
-/

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

/-
::::keepEnv
:::example "Recursive Equational Lemmas"
Given the definition of {lean}`everyOther`:
```lean
def everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
```

equational lemmas are generated that relate {lean}`everyOther`'s recursor-based implementation to its original recursive definition.

{lean}`everyOther.eq_unfold` states that `everyOther` with no arguments is equal to its unfolding:
```signature
everyOther.eq_unfold.{u} :
  @everyOther.{u} = fun {α} x =>
    match x with
    | [] => []
    | [x] => [x]
    | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_def` states that a `everyOther` is equal to its definition when applied to arguments:
```signature
everyOther.eq_def.{u} {α : Type u} :
  ∀ (x : List α),
    everyOther x =
      match x with
      | [] => []
      | [x] => [x]
      | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_1` demonstrates its first pattern:
```signature
everyOther.eq_1.{u} {α : Type u} : everyOther [] = ([] : List α)
```

{lean}`everyOther.eq_2` demonstrates its second pattern:
```signature
everyOther.eq_2.{u} {α : Type u} (x : α) : everyOther [x] = [x]
```

{lean}`everyOther.eq_3` demonstrates its final pattern:
```signature
everyOther.eq_3.{u} {α : Type u} (x y : α) (xs : List α) :
  everyOther (x :: y :: xs) = x :: everyOther xs
```

Because the patterns do not overlap, no assumptions about prior patterns not having matched are necessary for the equational lemmas.
:::
::::
-/

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

/-
After elaborating a module, having checked each addition to the environment with the kernel, the changes that the module made to the global environment (including extensions) are serialized to a {deftech}[`.olean` file].
In these files, Lean terms and values are represented just as they are in memory; thus the file can be directly memory-mapped.
All code paths that lead to Lean adding to the environment involve the new type or definition first being checked by the kernel.
However, Lean is a very open, flexible system.
To guard against the possibility of poorly-written metaprograms jumping through hoops to add unchecked values to the environment, a separate tool `lean4checker` can be used to validate that the entire environment in a `.olean` file satisfies the kernel.
-/

整个模块繁释完成、每项添加都通过内核检查后，对全局环境（含扩展）的更改被序列化为 {deftech key := ".olean file"}[`.olean` 文件]。
在这些文件中，Lean 的项与值与内存中的形式相同，因此可直接进行内存映射。
所有添加新类型或定义到环境的代码路径，都需先经过内核检查。
由于 Lean 是一个高度打开灵活的系统，为防止恶写元程序绕过检查往环境加入未验值，可使用独立工具 `lean4checker` 验证 `.olean` 文件内环境是否通过内核检验。

/-

In addition to the `.olean` file, the elaborator produces a `.ilean` file, which is an index used by the language server.
This file contains information needed to work interactively with the module without fully loading it, such as the source positions of definitions.
The contents of `.ilean` files are an implementation detail and may change at any release.
-/

除 `.olean` 文件外，繁释器还会生成 `.ilean` 索引文件，供语言服务器使用。
它便于无需完整加载模块即可交互使用，比如定位定义的位置等。
`.ilean` 文件内容为实现细节，不同的lean版本可能不兼容。

/-
Finally, the compiler is invoked to translate the intermediate representation of functions stored in its environment extension into C code.
A C file is produced for each Lean module; these are then compiled to native code using a bundled C compiler.
If the `precompileModules` option is set in the build configuration, then this native code can be dynamically loaded and invoked by Lean; otherwise, an interpreter is used.
For most workloads, the overhead of compilation is larger than the time saved by avoiding the interpreter, but some workloads can be sped up dramatically by pre-compiling tactics, language extensions, or other extensions to Lean.
-/

最后，编译器会将保存在环境扩展中的函数中间表示翻译为 C 代码。
每个 Lean 模块都会产出一个 C 文件，随后由捆绑 C 编译器编译为本地代码。
若配置文件启用 `precompileModules` 选项，则该本地代码可被 Lean 动态加载和调用；否则将使用解释器。
对于大多数场景，编译开销大于省下的执行时间，但预编译策略、语言扩展等可大幅加速某些特定任务。

/-
# Initialization
-/

# 初始化
%%%
tag := "initialization"
%%%

/-
Before starting up, the elaborator must be correctly initialized.
Lean itself contains {deftech}[initialization] code that must be run in order to correctly construct the compiler's initial state; this code is run before loading any modules and before the elaborator is invoked.
Furthermore, each dependency may itself contribute initialization code, _e.g._ to set up environment extensions.
Internally, each environment extension is assigned a unique index into an array, and this array's size is equal to the number of registered environment extensions, so the number of extensions must be known in order to correctly allocate an environment.
-/


在启动前，繁释器必须正确初始化。
Lean 本身包含一套 {deftech key:="initialization"}[初始化] 代码，须在加载任一模块及调用繁释器前运行，以正确构造编译器初始状态。
此外，各依赖项本身也可贡献初始化代码，例如启动环境扩展。
内部层面，每种环境扩展分配唯一数组索引，数组大小等于注册扩展数，因此必须事先得知扩展数量以正确分配环境结构体空间。

/-
After running Lean's own builtin initializers, the module's header is parsed and the dependencies' `.olean` files are loaded into memory.
A “pre-environment” is constructed that contains the union of the dependencies' environments.
Next, all initialization code specified by the dependencies is executed in the interpreter.
At this point, the number of environment extensions is known, so the pre-environment can be reallocated into an environment structure with a correctly-sized extensions array.
-/
Lean 内建初始化器运行后，模块头部被解析，依赖的 `.olean` 文件加载入内存。
一个包含各依赖环境并集的“预环境”会被创建。
随后所有依赖项指定的初始化代码会在解释器中执行。
此时环境扩展的数量可以确定，可将预环境重分配成扩展区大小正确的环境结构体。

/-
:::syntax command (title := "Initialization Blocks")
An {keywordOf Lean.Parser.Command.initialize}`initialize` block adds code to the module's initializers.
The contents of an {keywordOf Lean.Parser.Command.initialize}`initialize` block are treated as the contents of a {keywordOf Lean.Parser.Term.do}`do` block in the {lean}`IO` monad.

Sometimes, initialization only needs to extend internal data structures by side effects.
In that case the contents are expected to have type {lean}`IO Unit`:
```grammar
initialize
  $cmd*
```

Initialization may also be used to construct values that contain references to internal state, such as attributes that are backed by an environment extension.
In this form of {keywordOf Lean.Parser.Command.initialize}`initialize`, initialization should return the specified type in the {lean}`IO` monad.
```grammar
initialize $x:ident : $t:term ←
  $cmd*
```
:::
-/

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

/-
:::syntax command (title := "Compiler-Internal Initializers")
Lean's internals also define code that must run during initialization.
However, because Lean is a bootstrapping compiler, special care must be taken with initializers defined as part of Lean itself, and Lean's own initializers must run prior to importing or loading _any_ modules.
These initializers are specified using {keywordOf Lean.Parser.Command.initialize}`builtin_initialize`, which should not be used outside the compiler's implementation.

```grammar
builtin_initialize
  $cmd*
```
```grammar
builtin_initialize $x:ident : $t:term ←
  $cmd*
```
:::
-/

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
