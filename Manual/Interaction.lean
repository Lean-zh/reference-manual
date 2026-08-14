/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.ZhDocString.Interaction

import Manual.Meta
import Manual.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "与 Lean 交互" =>
%%%
htmlSplit := .never
file := "Interacting-with-Lean"
tag := "interaction"
%%%

Lean 的设计目标是交互式使用，而不是采用批处理模式——在这种模式下，整个文件被一次性输入，再被转换为目标代码或错误消息。
许多为交互式使用而设计的编程语言都提供 {deftech}[REPL]，{margin}[它是 {noVale "Vale can't handle partly-bolded words"}[“*R*（读取）-*E*（求值）-*P*（打印）-*L*（循环）”]的缩写，因为代码会被解析（“读取”）、求值并显示结果，而且这一过程可以按需重复任意多次。]用户可以在其中输入并测试代码，也可以使用命令加载源文件、检查项的类型或查询环境。
Lean 的交互功能基于另一种范式。
Lean 并不在程序之外提供单独的命令提示符，而是在源文件的上下文中提供 {tech (key := "commands")}[命令]来完成相同的任务。
依照惯例，供交互使用、而非作为持久代码制品一部分的命令，都以 {keyword}`#` 为前缀。

Lean 命令产生的信息可在{deftech (key := "message log")}_消息日志_中查看；该日志会累积{tech (key := "Lean elaborator")}[精译器]的输出。
消息日志中的每个条目都与一段特定的源代码范围相关联，并具有一个{deftech (key := "severity")}_严重程度_。
严重程度共有三级：{lean  (type := "Lean.MessageSeverity")}`information` 用于不表示存在问题的消息，{lean  (type := "Lean.MessageSeverity")}`warning` 表示潜在问题，而 {lean  (type := "Lean.MessageSeverity")}`error` 表示确定存在的问题。
对于交互式命令，结果通常作为信息消息返回，并与该命令开头的关键字相关联。

# 对项求值
%%%
tag := "hash-eval"
%%%

{keywordOf Lean.Parser.Command.eval}`#eval` 命令用于将代码作为程序运行。
具体而言，它能够执行 {lean}`IO` 动作，采用按值调用的求值策略，{ref "partial-unsafe"}[会执行 {keyword}`partial` 函数]，并且类型与证明都会被擦除。
若要改用属于{tech (key := "definitional equality")}[定义相等]一部分的归约规则来归约项，请使用 {keywordOf Lean.reduceCmd}`#reduce`。

:::syntax command (title := "对项求值")

```grammar
#eval $t
```

```grammar
#eval! $t
```

{zhincludeDocstring Lean.Parser.Command.eval ZhDoc.eval}

:::

{keywordOf Lean.Parser.Command.eval}`#eval` 总会精译并编译所提供的项。
随后，它会检查该项是否传递依赖于任何 {lean}`sorry`；若存在此类依赖，除非以 {keywordOf Lean.Parser.Command.eval}`#eval!` 形式调用命令，否则求值将终止。
这是因为编译后的代码可能依赖编译期不变量（例如数组查找不能越界），而这些不变量由适当命题的证明保证；运行包含不完整证明的代码（或使用 {lean}`sorry`“证明”错误命题的代码）可能导致 Lean 自身崩溃。

```lean -show
section
variable (m : Type → Type)
open Lean.Elab.Command (CommandElabM)
```

:::paragraph

代码的运行方式取决于其类型：

 * 如果类型位于 {lean}`IO` 单子中，则会在捕获{tech (key := "standard output")}[标准输出]与{tech (key := "standard error")}[标准错误]并将其重定向到 Lean {tech (key := "message log")}[消息日志]的上下文中执行。
   如果返回值的类型不是 {lean}`Unit`，则会像显示非单子表达式的结果那样显示它。
 * 如果类型位于 Lean 内部的某个元编程单子中（{name Lean.Elab.Command.CommandElabM}`CommandElabM`、{name Lean.Elab.Term.TermElabM}`TermElabM`、{name Lean.MetaM}`MetaM` 或 {name Lean.CoreM}`CoreM`），则会在当前上下文中运行。
    例如，环境会包含调用 {keywordOf Lean.Parser.Command.eval}`#eval` 之处位于作用域内的定义。
    与 {name}`IO` 一样，所得值会像非单子表达式的结果那样显示。
    当 Lean 在 {ref "lake"}[Lake] 下运行时，其工作目录（因而也是 {name}`IO` 动作的工作目录）是当前{tech (key := "workspace")}[工作区]。
 * 如果类型位于其他某个单子 {lean}`m` 中，并且存在 {lean}`MonadLiftT m CommandElabM` 或 {lean}`MonadEvalT m CommandElabM` 实例，则会使用 {name}`MonadLiftT.monadLift` 或 {name}`MonadEvalT.monadEval` 将该单子转换为可由 {keywordOf Lean.Parser.Command.eval}`#eval` 运行的单子，之后照常运行。
 * 如果项的类型不位于任何受支持的单子中，则将它视为纯值。
  编译后的代码会被运行，并显示结果。

精译 {keywordOf Lean.Parser.Command.eval}`#eval` 中的项所产生的辅助定义或其他环境修改都会被丢弃。
如果该项是元编程单子中的动作，那么运行此单子动作对环境所做的更改会被保留。
:::

```lean -show
end
```


在{tech (key := "module")}[模块]中使用时，{keywordOf Lean.Parser.Command.eval}`#eval` 会揭示 Lean 语言服务器与 Lean 编译器处理文件方式之间的差异。
由于 {keywordOf Lean.Parser.Command.eval}`#eval` 会在编译期运行代码，因此要求其代码在{tech (key := "meta phase")}[元阶段]可用。
为便于对模块进行实验，语言服务器会让所有已导入模块在元阶段可用，而编译器则严格遵守 {keywordOf Lean.Parser.Module.import}`meta` 声明。
因此，使用 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 与 {keywordOf Lean.Parser.Command.eval}`#eval` 嵌入轻量测试的模块，可能在语言服务器中精译成功，却在构建期间失败。
要修复此问题，可以在包含测试的模块中使用 {keywordOf Lean.Parser.Module.import}`meta import` 导入这些定义：

::::example "求值与元阶段"
:::leanModules -server +error
```leanModule (moduleName := Eval.Even)
module
public section
def isEven (n : Nat) : Bool :=
  n % 2 = 0

```
```leanModule (moduleName := Eval) (name := noMetaEval)
module
import Eval.Even

/-- info: [true, false] -/
#guard_msgs in
#eval [isEven 4, isEven 5]
```
```leanOutput noMetaEval
❌️ Docstring on `#guard_msgs` does not match generated message:

- info: [true, false]
+ error: Invalid `meta` definition `_eval`, `isEven` is not accessible here; consider adding `public meta import Eval.Even`
```
:::
:::leanModules
将 {name}`isEven` 导入元阶段即可修复此问题：
```leanModule (moduleName := Eval.Even)
module
public section
def isEven (n : Nat) : Bool :=
  n % 2 = 0
```
```leanModule (moduleName := Eval) (name := metaEval)
module
meta import Eval.Even

/-- info: [true, false] -/
#guard_msgs in
#eval [isEven 4, isEven 5]
```
:::
::::


如果存在相应实例，结果会使用 {name Lean.ToExpr}`ToExpr`、{name}`ToString` 或 {name}`Repr` 实例显示。
如果不存在，而 {option}`eval.derive.repr` 为 {lean}`true`，Lean 会尝试派生合适的 {name}`Repr` 实例。
如果既找不到也无法派生合适的实例，就会报错。
将 {option}`eval.pp` 设为 {lean}`false`，可禁止 {keywordOf Lean.Parser.Command.eval}`#eval` 使用 {name Lean.ToExpr}`ToExpr` 实例。

:::example "显示输出"

{keywordOf Lean.Parser.Command.eval}`#eval` 无法显示函数：
```lean (name := funEval) +error
#eval fun x => x + 1
```
```leanOutput funEval
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
```

它能够派生实例，以显示没有 {name}`ToString` 或 {name}`Repr` 实例的输出：

```lean (name := quadEval)
inductive Quadrant where
  | nw | sw | se | ne

#eval Quadrant.nw
```
```leanOutput quadEval
Quadrant.nw
```

派生出的实例不会被保存。
禁用 {option}`eval.derive.repr` 会导致 {keywordOf Lean.Parser.Command.eval}`#eval` 失败：

```lean (name := quadEval2) +error
set_option eval.derive.repr false
#eval Quadrant.nw
```
```leanOutput quadEval2
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Quadrant
```

:::

{zhOptionDocs eval.pp ZhDoc.Option.eval.pp}

{zhOptionDocs eval.type ZhDoc.Option.eval.type}

{zhOptionDocs eval.derive.repr ZhDoc.Option.eval.derive.repr}

为单子定义合适的 {lean}`MonadLift`{margin}[{ref "lifting-monads"}[关于提升单子的章节]介绍了 {lean}`MonadLift`。]或 {lean}`MonadEval` 实例，即可使其能够在 {keywordOf Lean.Parser.Command.eval}`#eval` 中执行。
正如 {name}`MonadLiftT` 是 {name}`MonadLift` 实例的传递闭包，{name}`MonadEvalT` 也是 {name}`MonadEval` 实例的传递闭包。
与 {name}`MonadLiftT` 一样，用户不应直接定义额外的 {name}`MonadEvalT` 实例。

{zhdocstring MonadEval ZhDoc.MonadEval}

{zhdocstring MonadEvalT ZhDoc.MonadEvalT}

# 归约项
%%%
tag := "hash-reduce"
%%%

{keywordOf Lean.reduceCmd}`#reduce` 命令会反复对项应用归约，直到无法再归约为止。
归约会在绑定器下进行；但为避免意外的性能下降，除非启用了 {keywordOf Lean.reduceCmd}`#reduce` 的相应选项，否则会跳过证明和类型。
与 {keywordOf Lean.Parser.Command.eval}`#eval` 命令不同，归约不能产生副作用，并且结果会显示为项，而不是通过 {name}`ToString` 或 {name}`Repr` 实例显示。

一般而言，{keywordOf Lean.reduceCmd}`#reduce` 主要用于诊断定义相等与证明项方面的问题，而 {keywordOf Lean.Parser.Command.eval}`#eval` 更适合计算项的值。
尤其是，使用{tech (key := "well-founded recursion")}[良基递归]定义或定义为{tech (key := "partial fixpoints")}[部分不动点]的函数，使用归约引擎计算时要么非常缓慢，要么根本不会归约。

:::syntax command (title := "归约项")
```grammar
#reduce $[($ident := $tm)]* $t
```

{zhincludeDocstring Lean.reduceCmd ZhDoc.reduceCmd}

:::

:::example "归约函数"

归约一个项会得到它在 Lean 逻辑中的范式。
由于底层项先被归约再显示，因此不需要 {name}`ToString` 或 {name}`Repr` 实例。
函数也可以像其他任何项一样显示。

在某些情况下，此范式很短，并且类似于人会编写的项：
```lean (name := plusOne)
#reduce (fun x => x + 1)
```
```leanOutput plusOne
fun x => x.succ
```

在另一些情况下，则会暴露诸如加法这类函数被精译到 Lean 核心逻辑中的细节，参见{ref "elab-as-course-of-values"}[函数的精译]：
```lean (name := onePlus)
#reduce (fun x => 1 + x)
```
```leanOutput onePlus
fun x => (Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) x).1 1
```

:::

# 检查类型
%%%
tag := "hash-check"
%%%

:::syntax command (title := "检查类型")

{keyword}`#check` 可用于精译一个项并检查其类型。

```grammar
#check $t
```

如果所提供的项是一个标识符，且它是某个全局常量的名称，那么 {keyword}`#check` 会打印其签名。
否则，该项会被精译为 Lean 项，并打印其类型。
:::

{keywordOf Lean.Parser.Command.check}`#check` 对项的精译并不要求该项被完全精译；其中可以包含元变量。
只要按原样书写的项_可能_具有某个类型，精译就会成功。
如果某个必需的实例绝无可能合成，则精译失败；由元变量导致的合成问题不会阻止精译。


:::example "{keyword}`#check` 与未确定的类型"
在此示例中，列表元素的类型尚未确定，因此类型中包含一个元变量：
```lean (name := singletonList)
#check fun x => [x]
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
```

在此示例中，被相加项的类型和加法的结果类型都未知，因为 {name}`HAdd` 允许不同类型的项相加。
在幕后，一个元变量表示未知的 {name}`HAdd` 实例。
```lean (name := polyPlus)
#check fun x => x + x
```
```leanOutput polyPlus
fun x => x + x : (x : ?m.12) → ?m.19 x
```

:::

:::syntax command (title := "测试类型错误")
```grammar
#check_failure $t
```
{keywordOf Lean.Parser.Command.check}`#check` 的这一变体使用与 {keywordOf Lean.Parser.Command.check}`#check` 相同的过程来精译该项。
如果精译成功，则报错；如果精译失败，则不报错。
部分精译后的项以及所发现的任何类型信息都会添加到{tech (key := "message log")}[消息日志]中。
:::


:::example "检查类型错误"

尝试把字符串与自然数相加会如预期般失败：
```lean (name := oneOne)
#check_failure "one" + 1
```
```leanOutput oneOne
failed to synthesize instance of type class
  HAdd String Nat ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
尽管如此，仍可得到一个部分精译的项：
```leanOutput oneOne
"one" + 1 : ?m.32
```

:::

# 合成实例
%%%
tag := "hash-synth"
%%%

:::syntax command (title := "合成实例")
```grammar
#synth $t
```
:::

{keywordOf Lean.Parser.Command.synth}`#synth` 命令会调用 Lean 的{tech (key := "type class")}[类型类]解析机制，并尝试执行{ref "instance-synth"}[实例合成]，为给定类型类查找实例。
如果成功，则输出所得的实例项。

::::example "合成类型类实例"

:::paragraph
Lean 使用类型类重载加法等操作。
`+` 运算符是调用 {name}`HAdd.hAdd` 的记法，而它是 {name}`HAdd` 类型类中唯一的方法。
此示例表明，Lean 允许我们将两个整数相加，并且结果仍为整数：
```lean (name := synthInstHAddNat)
#synth HAdd Int Int Int
```
```leanOutput synthInstHAddNat
instHAdd
```
:::

:::paragraph
默认情况下，Lean 不会在输出项中显示隐式参数。
然而，实例参数本身是隐式的，这会降低此输出在理解实例合成时的实用性。
将选项 {option}`pp.explicit` 设为 {name}`true` 会使 Lean 显示隐式参数，包括实例：
```lean (name := synthInstHAddNat2)
set_option pp.explicit true in
#synth HAdd Int Int Int
```
```leanOutput synthInstHAddNat2
@instHAdd Int Int.instAdd
```
:::

:::paragraph
如下类型类实例合成失败所示，Lean 不允许把整数与字符串相加：
```lean (name := synthInstHAddNatInt) +error
#synth HAdd Int String String
```
```leanOutput synthInstHAddNatInt
failed to synthesize
  HAdd Int String String

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::


::::

# 查询上下文
%%%
tag := "hash-print"
%%%

{keyword}`#print` 命令族用于向 Lean 查询有关定义的信息。

:::syntax command (title := "打印定义")
```grammar
#print $t:ident
```

打印常量的定义。
:::

使用 {keywordOf Lean.Parser.Command.print}`#print` 打印定义时，会将定义打印为一个项。
使用{ref "tactics"}[策略]证明的定理，在打印为项时可能非常庞大。

:::syntax command (title := "打印字符串")
```grammar
#print $s:str
```

将字符串字面量添加到 Lean 的{tech (key := "message log")}[消息日志]。
:::


:::syntax command (title := "打印公理")
```grammar
#print axioms $t
```

列出该常量传递依赖的所有公理。更多信息参见{ref "print-axioms"}[公理文档]。
:::

:::example "打印公理"
```imports -show
import Std.Tactic.BVDecide
```

以下两个函数都交换一对位向量中的元素：

```lean
def swap (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  (y, x)

def swap' (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x := x ^^^ y
  let y := x ^^^ y
  let x := x ^^^ y
  (x, y)
```

可以使用{ref "function-extensionality"}[函数外延性]、{ref "the-simplifier"}[化简器]和{tactic}`bv_decide` 证明它们相等：
```lean
theorem swap_eq_swap' : swap = swap' := by
  funext x y
  simp only [swap, swap', Prod.mk.injEq]
  bv_decide
```

所得证明使用了若干公理：
```lean (name := axioms)
#print axioms swap_eq_swap'
```
```leanOutput axioms
'swap_eq_swap'' depends on axioms: [propext, Classical.choice, Quot.sound, swap_eq_swap'._native.bv_decide.ax_3]
```

公理 {name}`swap_eq_swap'._native.bv_decide.ax_3` 由{tactic}`bv_decide` 生成，这表明使用了原生代码将外部证明证书转换为 Lean 证明项。
:::

:::syntax command (title := "打印方程")
命令 {keywordOf Lean.Parser.Command.printEqns}`#print equations`（可缩写为 {keywordOf Lean.Parser.Command.printEqns}`#print eqns`）会显示函数的{tech (key := "equational lemmas")}[方程引理]。
```grammar
#print equations $t
```
```grammar
#print eqns $t
```
:::

:::example "打印方程"

```lean (name := intersperse_eqns)
def intersperse (x : α) : List α → List α
  | y :: z :: zs => y :: x :: intersperse x (z :: zs)
  | xs => xs

#print equations intersperse
```
```leanOutput intersperse_eqns
equations:
@[backward_defeq] theorem intersperse.eq_1.{u_1} : ∀ {α : Type u_1} (x y z : α) (zs : List α),
  intersperse x (y :: z :: zs) = y :: x :: intersperse x (z :: zs)
theorem intersperse.eq_2.{u_1} : ∀ {α : Type u_1} (x : α) (x_1 : List α),
  (∀ (y z : α) (zs : List α), x_1 = y :: z :: zs → False) → intersperse x x_1 = x_1
```

它不会打印定义方程，也不会打印展开方程：
```lean (name := intersperse_eq_def)
#check intersperse.eq_def
```
```leanOutput intersperse_eq_def
intersperse.eq_def.{u_1} {α : Type u_1} (x : α) (x✝ : List α) :
  intersperse x x✝ =
    match x✝ with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

```lean (name := intersperse_eq_unfold)
#check intersperse.eq_unfold
```
```leanOutput intersperse_eq_unfold
intersperse.eq_unfold.{u_1} :
  @intersperse = fun {α} x x_1 =>
    match x_1 with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

:::

:::syntax command (title := "作用域信息")

{zhincludeDocstring Lean.Parser.Command.where ZhDoc.«where»}

```grammar
#where
```
:::

:::example "作用域信息"
{keywordOf Lean.Parser.Command.where}`#where` 命令会显示对当前{tech (key := "section scope")}[节作用域]所做的全部修改，包括当前作用域与其嵌套所在的各层作用域中的修改。

```lean +fresh (name := scopeInfo)
public section
open Nat

namespace A
variable (n : Nat)
namespace B

open List
set_option pp.tagAppFns true

#where

end A.B
end
```
```leanOutput scopeInfo
public section

namespace A.B

open Nat List

variable (n : Nat)

set_option pp.tagAppFns true
```

:::

:::syntax command (title := "检查 Lean 版本")

{zhincludeDocstring Lean.Parser.Command.version ZhDoc.version}

```grammar
#version
```
:::


# 使用 {keyword}`#guard_msgs` 测试输出
%%%
tag := "hash-guard_msgs"
%%%

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可用于确保某条命令输出的消息符合预期。
配合本节中的交互命令，可以构造一个仅在输出符合预期时才会精译成功的文件；这样的文件可在 {ref "lake"}[Lake] 中用作{tech (key := "test driver")}[测试驱动程序]。

:::syntax command (title := "记录预期输出")
```grammar
$[$_:docComment]?
#guard_msgs $[($_,*)]? in
$c:command
```

{zhincludeDocstring Lean.guardMsgsCmd ZhDoc.guardMsgsCmd}

:::

:::example "测试返回值"

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可以确保一组测试用例通过：

```lean
def reverse : List α → List α := helper []
where
  helper acc
    | [] => acc
    | x :: xs => helper (x :: acc) xs

/-- info: [] -/
#guard_msgs in
#eval reverse ([] : List Nat)

/-- info: ['c', 'b', 'a'] -/
#guard_msgs in
#eval reverse "abc".toList
```

:::


:::paragraph
{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令的行为可通过三种方式指定：

 1. 提供筛选器，选择要检查的消息子集

 2. 指定空白字符比较策略

 3. 决定按消息内容排序，还是按消息产生的顺序排序

这些配置选项写在圆括号中，并以逗号分隔。
:::

::::syntax Lean.guardMsgsSpecElt (title := "指定 {keyword}`#guard_msgs` 的行为") -open

```grammar
$_:guardMsgsFilter
```
```grammar
whitespace := $_
```
```grammar
ordering := $_
```

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 有三类选项：筛选器、空白字符比较策略和排序方式。
::::

:::syntax Lean.guardMsgsFilter (title := "{keyword}`#guard_msgs` 的输出筛选器") -open
```grammar
$[drop]? all
```
```grammar
$[drop]? info
```
```grammar
$[drop]? warning
```
```grammar
$[drop]? error
```

{zhincludeDocstring Lean.guardMsgsFilter ZhDoc.guardMsgsFilter}

:::


:::syntax Lean.guardMsgsWhitespaceArg (title := "`#guard_msgs` 的空白字符比较") -open
```grammar
exact
```
```grammar
lax
```
```grammar
normalized
```


比较消息时，始终忽略开头和结尾的空白字符。在此基础上，还可使用以下设置：

 * `whitespace := exact` 要求空白字符完全匹配。

 * `whitespace := normalized` 在匹配前将所有换行符转换为空格（默认设置）。这样便可折断长行。

 * `whitespace := lax` 在匹配前将连续空白字符折叠为一个空格。

:::

选项 {option}`guard_msgs.diff` 控制当预期消息与实际产生的消息不匹配时，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 所产生错误消息的内容。
默认情况下，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 会逐行显示差异：行首的 `+` 表示来自实际产生的消息的行，行首的 `-` 表示来自预期消息的行。
当消息很大而差异很小时，这有助于发现差异所在。
将 {option}`guard_msgs.diff` 设为 `false` 后，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 将只显示实际产生的消息，可将它与源文件中的预期消息进行比较。
如果消息之间的差异令人困惑或信息过载，这样做会比较方便。

{zhOptionDocs guard_msgs.diff ZhDoc.Option.guard_msgs.diff}

:::example "显示差异"
{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可用于测试玫瑰树 {lean}`Tree` 的定义，以及创建这种树的函数 {lean}`Tree.big`：

```lean
inductive Tree (α : Type u) : Type u where
  | val : α → Tree α
  | branches : List (Tree α) → Tree α

def Tree.big (n : Nat) : Tree Nat :=
  if n < 5 then .branches [.val n, .val (n - 1), .val n, .val (n - 2)]
  else .branches [.big (n / 2),  .big (n / 3)]
```

然而，当输出很大时，可能很难看出测试失败源自何处：
```lean +error (name := bigMsg)
set_option guard_msgs.diff false
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
求值产生：
```leanOutput bigMsg (severity := information)
Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```

禁用 {option}`guard_msgs.diff` 时，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令会报告以下错误：
```leanOutput bigMsg (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```

启用 {option}`guard_msgs.diff` 后，差异会被突出显示，使错误更加明显：
```lean +error (name := bigMsg')
set_option guard_msgs.diff true in
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0,
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
```leanOutput bigMsg'  (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

  info: Tree.branches
    [Tree.branches
       [Tree.branches
          [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
-          Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0,
+          Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
        Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
     Tree.branches
       [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
        Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```
:::

{include 1 Manual.Interaction.FormatRepr}
