/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.ZhDocString.Simp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "简化器" =>
%%%
tag := "the-simplifier"
file := "The-Simplifier"
%%%

简化器是 Lean 中最常用的功能之一。
它根据简化规则数据库，从内向外重写项。
简化器具有很高的可配置性，许多策略以不同方式使用它。

# 调用简化器
%%%
file := "Invoking-the-Simplifier"
tag := "simp-tactic-naming"
%%%


Lean 的简化器可以通过多种方式调用。
一组策略涵盖了最常见的调用模式。
{ref "simp-tactics"}[策略参考]中列出了完整的简化策略。

所有简化策略的名称都包含 `simp`。
除此之外，它们还按照一套描述其功能的前缀和后缀体系来命名：

: `-!` 后缀

  将 {name Lean.Meta.Simp.Config.autoUnfold}`autoUnfold` 配置选项设为 `true`，使简化器展开所有定义

: `-?` 后缀

  使简化器记录简化期间用过哪些规则，并建议把策略脚本改为使用一个最小的 {tech (key := "simp set")}[simp 集]

: `-_arith` 后缀

  启用线性算术简化规则

: `d-` 前缀

  使简化器仅使用在定义意义下成立的重写进行简化

: `-_all` 后缀

  使简化器反复简化所有假设和目标结论，并尽可能多地考虑各项假设，直到无法继续简化为止

此外还有两个简化策略 {tactic}`simpa` 和 {tactic}`simpa!`，它们先同时简化目标以及一个证明项或假设，再完成目标。
这种同步简化使证明面对 {tech (key := "simp set")}[simp 集]的变化时更加稳健。

## 参数
%%%
tag := "simp-tactic-params"
%%%

简化策略采用以下语法：

:::syntax tactic (title := "简化策略")
```grammar
simp $_:optConfig $[only]? $[ [ $[$e],* ] ]? $[at $[$h]*]?
```
:::

换言之，调用简化策略时依次接受以下修饰项，且每一项都是可选的：
 * 一组{ref "tactic-config"}[配置选项]；根据所调用的简化器是 {tactic}`simp` 还是 {tactic}`dsimp` 的变体，其中应分别包含 {name}`Lean.Meta.Simp.Config` 或 {name}`Lean.Meta.DSimp.Config` 的字段。
 * {keywordOf Lean.Parser.Tactic.simp}`only` 修饰符排除默认 simp 集，改为从空的{margin}[严格来说，为了完成自反情形，simp 集始终包含 {name}`eq_self` 和 {name}`iff_self`。]simp 集开始。
 * 引理列表向simp 集添加引理或从中移除引理。引理列表中的引理有三种指定方式：
   * `*`，将证明状态中的所有假设添加到simp 集
   * `-` 后接一个引理，将该引理从simp 集中移除
   * 引理说明符，由以下各项依次组成：
      * 可选的 `↓` 或 `↑`，分别使引理在进入子项之前或之后应用（默认为 `↑`）。简化后的参数通常能让更多规则适用，因此简化器一般先简化子项，再尝试简化父项；`↓` 则使规则在子项简化之前先简化父项。
      * 可选的 `←`，使等式引理从右向左而非从左向右使用。
      * 必需的引理，可以是simp 集名称、引理名称或项。项会被视作具有全新名称的具名引理。
 * 位置说明符，以 {keywordOf Lean.Parser.Tactic.simp}`at` 开头，由一系列位置组成。位置可以是：

   - 假设的名称，表示应简化其类型
   - 星号 `*`，表示应简化所有假设和结论
   - 推导符号 `⊢`，表示应简化结论

  默认只简化结论。

::::example "{tactic}`simp` 的位置说明符"
:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```

在此证明状态中，
```pre
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

策略 {tacticStep}`simp +arith` 只简化目标：

```post
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

调用 {tacticStep}`simp +arith at h` 会得到一个假设 `h` 已被简化的目标：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (6 + x + 1)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

添加 `⊢` 还可同时简化结论，即使用 {tacticStep}`simp +arith at h ⊢`：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

使用 {tacticStep}`simp +arith at *` 会简化所有假设以及结论：

```post
p : Nat → Prop
x : Nat
h : p (x + 7)
h' : p (x + 12)
⊢ p (x + 7)
```
:::
::::


# 重写规则
%%%
file := "Rewrite-Rules"
tag := "simp-rewrites"
%%%

简化器有三类重写规则：

: 要展开的声明

  默认情况下，简化器只展开{tech (key := "reducible")}[可约]定义。
  不过，可以为任意{tech (key := "semireducible")}[半可约]或{tech (key := "irreducible")}[不可约]定义添加重写规则，使简化器也展开该定义。
  当简化器以定义模式（{tactic}`dsimp` 及其变体）运行时，定义展开只会用定义的值替换定义名称；否则，它还会使用等式编译器产生的等式引理。

: 等式引理

  简化器可以将相等性证明视为重写规则，此时等式左侧会被右侧替换。这些等式引理可以有任意数量的参数。简化器会实例化参数，使等式左侧与目标匹配，并通过证明搜索实例化任何额外参数。

: 简化过程

  简化器支持称为 {deftech (key := "simprocs")}_simproc（简化过程）_ 的机制，它们利用 Lean 元编程执行无法用等式高效指定的重写。Lean 为内置类型上最重要的操作提供了简化过程。

:::keepEnv
```lean -show
-- 验证上述关于可约性的说明

@[irreducible]
def foo (x : α) := x

set_option allowUnsafeReducibility true in
@[semireducible]
def foo' (x : α) := x

@[reducible]
def foo'' (x : α) := x

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp [foo]

/-- error: `simp` made no progress -/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp [foo']

/-- error: `simp` made no progress -/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp [foo'']

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp

```
:::

借助{tech (key := "propositional extensionality")}[命题外延性]，等式引理可以把命题重写为逻辑等价且更简单的命题。
当简化器把证明目标重写为 {lean}`True` 时，它会自动关闭该目标。
作为等式引理的一种特殊情形，相等性以外的命题也可以标记为重写规则。
它们会被预处理为将该命题重写成 {lean}`True` 的规则。

:::::example "重写命题"
::::tacticExample

{goal -show}`∀(α β : Type) (w y : α) (x z : β), (w, x) = (y, z)`
```setup
intro α β w y x z
```

当要求简化一个序对相等式时：
```pre
α β : Type
w y : α
x z : β
⊢ (w, x) = (y, z)
```

{tacticStep}`simp` 会得到相等式的合取：

```post
α β : Type
w y : α
x z : β
⊢ w = y ∧ x = z
```

默认 simp 集包含 {lean}`Prod.mk.injEq`，它表明这两个陈述等价：

```signature
Prod.mk.injEq.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) :
  ∀ (fst_1 : α) (snd_1 : β),
    ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
```
::::
:::::

除了重写规则，{tactic}`simp` 还有一些由 {ref "simp-config"}[`config` 参数控制]的内置归约规则。
即使simp 集为空，{tactic}`simp` 也可以用值替换 `let` 绑定的变量、归约{tech (key := "match discriminant")}[判别式]为构造器应用的 {keywordOf Lean.Parser.Term.match}`match` 表达式、归约应用于构造器的结构投影，或把匿名函数应用于其参数。

# simp 集
%%%
file := "Simp-sets"
tag := "simp-sets"
%%%

简化器使用的一组规则称为 {deftech (key := "simp set")}_simp 集_。
simp 集通过对 {deftech (key := "default simp set")}_默认 simp 集_的修改来指定。
这些修改可以包括添加规则、移除规则或添加一组规则。
{tactic}`simp` 策略的 `only` 修饰符使其从空的simp 集而不是默认集合开始。
规则通过 {attr}`simp` 属性添加到默认 simp 集。


:::syntax attr (alias := Lean.Meta.simpExtension) (title := "注册 {keyword}`simp` 引理")
{attr}`simp` 属性将声明添加到默认 simp 集。
如果该声明是定义，则将该定义标记为待展开；如果是定理，则将该定理注册为重写规则。

```grammar
simp
```


```grammar
simp ↑ $p?
```

```grammar
simp ↓ $p?
```

```grammar
simp $p:prio
```

```lean -show
-- 检查上述关于默认优先级的说法
/-- info: 1000 -/
#check_msgs in
#eval eval_prio default
```
:::

{deftech (key := "Custom simp sets")}_自定义simp 集_使用 {name Lean.Meta.registerSimpAttr}`registerSimpAttr` 创建；必须把它放在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中，使其在{tech (key := "initialization")}[初始化]期间运行。
它还会产生一项副作用：创建一个接口与 {attr}`simp` 相同的新属性，用于向自定义simp 集添加规则。
返回值是一个 {name Lean.Meta.SimpExtension}`SimpExtension`，可用于以编程方式访问自定义simp 集的内容。
在规则列表中加入该属性的名称，即可指示 {tactic}`simp` 策略使用新的simp 集。

{zhdocstring Lean.Meta.registerSimpAttr ZhDoc.registerSimpAttr}

{zhdocstring Lean.Meta.SimpExtension ZhDoc.SimpExtension}


# simp 范式
%%%
file := "Simp-Normal-Forms"
tag := "simp-normal-forms"
%%%


默认的{tech (key := "simp set")}[simp 集]包含所有以 {attr}`simp` 属性标记的定理和简化过程。
表达式的 {deftech (key := "simp normal form")}_simp 范式_，是通过 {tactic}`simp` 策略应用默认 simp 集，直至没有规则可以继续应用而得到的结果。
当表达式处于simp 范式时，它已经按照默认 simp 集尽可能充分地归约，因此通常更便于在证明中使用。

{tactic}`simp` 策略*不保证合流性*，这意味着表达式的simp 范式可能取决于默认 simp 集中各元素的应用顺序。
设置 {attr}`simp` 属性时可以指定优先级，从而改变规则的应用顺序。

设计 Lean 库时，必须考虑库中各种运算符组合应当采用哪种合适的simp 范式。
这可以指导开发者选择库应向默认 simp 集添加哪些规则。
特别是，simp 引理的右侧应当处于simp 范式；这有助于确保简化终止。
此外，即使一个概念有多种等价的陈述方式，库中也应通过一种simp 范式来表达它。
如果不同的 simp 引理以两种不同方式陈述同一概念，那么简化器可能无法把二者联系起来，致使某些预期的简化无法发生。

尽管简化不必具有合流性，力求合流仍然很有帮助，因为这会使库的行为更可预测，也往往能暴露缺失或选择不当的 simp 引理。
默认 simp 集和库所导出常量的类型签名一样，都是库接口的一部分。

库不应向默认 simp 集添加未提及该库所定义的任何常量的规则。
否则，导入一个库可能会改变 {tactic}`simp` 对某个不相关库的行为。
如果一个库依赖其他库中定义或声明的额外简化规则，请创建自定义simp 集，并指示用户使用它，或者提供专用策略。


# 终结位置与非终结位置
%%%
file := "Terminal-vs-Non-Terminal-Positions"
tag := "terminal-simp"
%%%

为了编写可维护的证明，除非 {tactic}`simp` 能关闭目标，否则应避免不带 {keywordOf Lean.Parser.Tactic.simp}`only` 使用它。
这种不关闭目标的 {tactic}`simp` 用法称为 {deftech (key := "non-terminal simps")}_非终结 simp_。
这是因为向默认 simp 集添加规则可能会增强 {tactic}`simp`，也可能只是使它选择不同的重写序列，从而得到不同的simp 范式。
指定 {keywordOf Lean.Parser.Tactic.simp}`only` 后，新增引理不会影响该次策略调用。
在实践中，{tactic}`simp` 的终结用法远不容易因新增 simp 引理而失效；即使失效，问题也更容易理解和修复。

在非终结位置工作时，可以使用 {tactic}`simp?`（或其他名称中带有 `?` 的简化策略）生成带 {keywordOf Lean.Parser.Tactic.simp}`only` 的适当调用。
正如 {tactic}`apply?` 或 {tactic}`rw?` 会建议使用相关引理，{tactic}`simp?` 会建议一次 {tactic}`simp` 调用，其中包含达到该范式所用的最小simp 集。

:::example "使用 {tactic}`simp?`"

此证明中的非终结 {tactic}`simp?` 会建议一个带 {keywordOf Lean.Parser.Tactic.simp}`only`、规模更小的 {tactic}`simp`：
```lean (name:=simpHuhDemo)
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp?
  assumption
```
建议的改写是：
```leanOutput simpHuhDemo
Try this:
  [apply] simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
```
由此得到更易维护的证明：
```lean
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp only [
    List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd
  ]
  assumption
```

:::


# 配置简化
%%%
file := "Configuring-Simplification"
tag := "simp-config"
%%%

{tactic}`simp` 主要通过配置参数来配置，该参数以名为 `config` 的具名参数传入。

{zhdocstring Lean.Meta.Simp.Config ZhDoc.Simp.Config}

{zhdocstring Lean.Meta.Simp.neutralConfig ZhDoc.Simp.neutralConfig}

{zhdocstring Lean.Meta.DSimp.Config ZhDoc.DSimp.Config}

## 选项
%%%
tag := "simp-options"
%%%

以下全局选项会影响 {tactic}`simp`：

{zhOptionDocs simprocs ZhDoc.Option.simprocs}

{zhOptionDocs tactic.simp.trace ZhDoc.Option.tactic.simp.trace}

{zhOptionDocs linter.unnecessarySimpa ZhDoc.Option.linter.unnecessarySimpa}

{zhOptionDocs trace.Meta.Tactic.simp.rewrite ZhDoc.Option.trace.Meta.Tactic.simp.rewrite}

{zhOptionDocs trace.Meta.Tactic.simp.discharge ZhDoc.Option.trace.Meta.Tactic.simp.discharge}

# 简化与重写
%%%
file := "Simplification-vs-Rewriting"
tag := "simp-vs-rw"
%%%


{tactic}`simp` 和 {tactic}`rw`/{tactic}`rewrite` 都使用等式引理，将项的一部分替换为等价形式。
不过，它们的预期用途和重写策略有所不同。
{tactic}`simp` 系列的策略主要以标准化方式重新表述问题，使问题更便于人类理解和进一步自动化。
特别是，简化绝不应使原本可证的目标变得不可证。
{tactic}`rw` 系列的策略主要用于应用人工选定的变换；这些变换不一定保持可证性，也不一定将项变为标准形式。
两类策略行为上的差异反映了各自侧重点的不同。

{tactic}`simp` 策略主要从内向外重写。
它首先简化尽可能小的表达式，从而为外围表达式带来更多简化机会。
{tactic}`rw` 策略选择与模式匹配的最左、最外层子项，并只重写一次。
两类策略都允许覆盖其默认策略：向simp 集添加引理时，`↓` 修饰符使其在简化子项之前应用；{tactic}`rw` 配置参数的 {name Lean.Meta.Rewrite.Config.occs}`occs` 字段则允许通过白名单或黑名单选择其他出现位置。
