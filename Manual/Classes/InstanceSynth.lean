/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Classes.InstanceSynth
import Manual.Papers


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "实例合成" =>
%%%
tag := "instance-synth"
file := "Instance-Synthesis"
%%%


实例合成是一种递归搜索过程：它要么为给定的类型类找到实例，要么失败。
换言之，给定一个注册为类型类的类型，实例合成会尝试构造一个具有该类型的项。
它遵循{tech (key := "reducibility")}[可约性]：{tech (key := "semireducible")}[半可约]或{tech (key := "irreducible")}[不可约]定义不会被展开，因此，除非某个定义是{tech (key := "reducible")}[可约的]，否则该定义的实例不会自动被视为其展开结果的实例。
一个给定的类可能有多个可用实例；此时依次以声明的优先级和声明顺序打破平局，同一优先级下，较新的实例优先于较早的实例。

该搜索过程在存在菱形时仍然高效，遇到循环时也不会无限循环。
当到达同一目标的路径不止一条时，就会出现{deftech (key := "diamonds")}_菱形_；而{deftech (key := "cycles")}_循环_则是两个实例各自在另一个实例得到解决后便可解决的情形。
实践中，用类型类编码数学概念时经常会出现菱形，而 Lean 的强制类型转换功能 {TODO}[链接] 会自然地产生循环，例如有限集合与有限多重集合之间的循环。

可以使用 {keywordOf Lean.Parser.Command.synth}`#synth` 命令测试实例合成。
此外，可以在需要实例本身的位置使用 {name}`inferInstance` 和 {name}`inferInstanceAs` 合成实例。
带类型标注的 {name}`inferInstance` 与 {name}`inferInstanceAs` 并不等价；{name}`inferInstanceAs` 会{ref "instance-wrapping"}[预处理合成出的实例]，以防实现细节无意间泄漏到接口中。

{zhdocstring inferInstance ZhDoc.Classes.InstanceSynth.inferInstance}

{zhdocstring inferInstanceAs ZhDoc.Classes.InstanceSynth.inferInstanceAs}

# 实例搜索概要
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Instance-Synthesis--Instance-Search-Summary"
%%%

一般而言，实例合成是一种可能任意回溯的递归搜索过程。
合成可能以一个实例项_成功_；若找不到这样的项，则会_失败_；若信息不足，则会_卡住_。
{citet tabledRes}[] 中给出了实例合成算法的详细说明。
实例搜索问题由应用于具体参数的类型类给出；这些参数值可能已知，也可能未知。
实例搜索会按优先级和定义顺序，尝试每个类型为类的局部绑定变量以及每个已注册实例。
当候选实例本身带有实例隐式参数时，它们会引入更多合成任务。

只有当类型类的所有输入参数均已知时，才会尝试解决问题。
若某个问题尚不能尝试，该分支便会卡住；其他子问题取得进展后，这个问题可能变得可解。
实例搜索开始时，输出参数或半输出参数既可以已知，也可以未知。
检查实例是否匹配问题时会忽略输出参数，但会考虑半输出参数。

给定问题的每个候选解都会保存在表中；这既能防止循环导致无限递归，也能避免菱形（即存在多条路径可达成同一目标）造成指数级搜索开销。
出现以下任一情况时，搜索分支失败：
 * 所有潜在实例均已尝试，搜索空间已耗尽。
 * 达到选项 {option}`synthInstance.maxSize` 指定的实例大小上限。
 * 输出参数的合成值与搜索问题中指定的值不匹配。
失败的分支不会重试。

若搜索原本会失败或卡住，搜索过程会按优先级尝试使用匹配的{tech (key := "default instances")}[默认实例]。
对于默认实例，输入参数不必完全已知，可以用该实例的参数值进行实例化。
默认实例可以接受实例隐式参数，这会引发进一步的递归搜索。

若成功分支中的问题已完全确定（即不存在未解决的元变量），该分支便会被剪枝，并且不再尝试其他可能成功的实例，因为后续实例不可能使先前已成功的分支转为失败。

# 实例搜索问题
%%%
tag := "instance-search"
%%%

实例搜索发生在函数应用（参数个数可能为零）的精译过程中。
某些隐式参数的值会由其他参数强制确定；例如，可以利用稍后显式提供的值参数的类型来解决一个隐式类型参数。
隐式参数也可以利用程序中该处的预期类型信息来解决。
搜索实例隐式参数时，可以利用已找到的隐式参数值，也可能顺带解决其他隐式参数。

实例合成从实例隐式参数的类型开始。
该类型必须是类型类对零个或多个参数的应用；搜索开始时，这些参数值可能已知，也可能未知。
若类的某个参数未知，搜索过程不会将其实例化，除非对应形参被{ref "class-output-parameters"}[标记为输出参数]，从而明确成为实例合成过程的输出。

搜索可能成功、失败或卡住；如果某个未知参数值变为已知后可能推动搜索进展，搜索就可能卡住。
当精译器确定了某个先前未知的隐式参数时，可能会重新调用卡住的搜索。
若未发生这种情况，卡住的搜索就会转为失败。

::::example "跟踪实例搜索"

将 {option}`trace.Meta.synthInstance` 选项设为 {lean}`true`，会让 Lean 输出合成类型类实例的过程跟踪。
该跟踪可用于理解实例合成如何成功以及为何失败。

:::paragraph
这里可以看到 Lean 为得出类型 {lean}`(Nat ⊕ Empty)` 存在元素（具体而言是元素 {lean}`Sum.inl 0`）这一结论而采取的步骤：
点击 `▶` 符号会展开跟踪中的对应分支，点击 `▼` 则会折叠已展开的分支。

```lean -show
-- 隐藏此处混入的 Lake 细节
attribute [-instance] Lake.inhabitedOfNilTrace Lake.inhabitedOfMonadCycle
```

```lean (name := trace)
set_option pp.explicit true in
set_option trace.Meta.synthInstance true in
#synth Nonempty (Nat ⊕ Empty)
```

```comment
如果下方 LEAN 输出发生变化，可能还需要更新随后对此过程的叙述
```
```leanOutput trace (expandTrace := Meta.synthInstance) (expandTrace := Meta.synthInstance.apply) (expandTrace := Meta.synthInstance.resume)
[Meta.synthInstance] ✅️ Nonempty (Sum Nat Empty)
  [Meta.synthInstance] ✅️ new goal Nonempty (Sum Nat Empty)
    [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad, @Sum.nonemptyLeft, @Sum.nonemptyRight]
  [Meta.synthInstance.apply] ✅️ apply @Sum.nonemptyRight to Nonempty (Sum Nat Empty)
    [Meta.synthInstance.tryResolve] ✅️ Nonempty (Sum Nat Empty) ≟ Nonempty (Sum Nat Empty)
    [Meta.synthInstance] ✅️ new goal Nonempty Empty
      [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instNonemptyOfMonad to Nonempty Empty
    [Meta.synthInstance.tryResolve] ❌️ Nonempty Empty ≟ Nonempty (?m.5 ?m.6)
  [Meta.synthInstance.apply] ✅️ apply @instNonemptyOfInhabited to Nonempty Empty
    [Meta.synthInstance.tryResolve] ✅️ Nonempty Empty ≟ Nonempty Empty
    [Meta.synthInstance] ✅️ new goal Inhabited Empty
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instInhabitedOfMonad to Inhabited Empty
    [Meta.synthInstance.tryResolve] ❌️ Inhabited Empty ≟ Inhabited (?m.8 ?m.7)
  [Meta.synthInstance.apply] ✅️ apply @Sum.nonemptyLeft to Nonempty (Sum Nat Empty)
    [Meta.synthInstance.tryResolve] ✅️ Nonempty (Sum Nat Empty) ≟ Nonempty (Sum Nat Empty)
    [Meta.synthInstance] ✅️ new goal Nonempty Nat
      [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instNonemptyOfMonad to Nonempty Nat
    [Meta.synthInstance.tryResolve] ❌️ Nonempty Nat ≟ Nonempty (?m.5 ?m.6)
  [Meta.synthInstance.apply] ✅️ apply @instNonemptyOfInhabited to Nonempty Nat
    [Meta.synthInstance.tryResolve] ✅️ Nonempty Nat ≟ Nonempty Nat
    [Meta.synthInstance] ✅️ new goal Inhabited Nat
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedNat]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedNat to Inhabited Nat
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Nat ≟ Inhabited Nat
    [Meta.synthInstance.answer] ✅️ Inhabited Nat
  [Meta.synthInstance.resume] ✅️ propagating Inhabited Nat to subgoal Inhabited Nat of Nonempty Nat
    [Meta.synthInstance.resume] size: 1
    [Meta.synthInstance.answer] ✅️ Nonempty Nat
  [Meta.synthInstance.resume] ✅️ propagating Nonempty Nat to subgoal Nonempty Nat of Nonempty (Sum Nat Empty)
    [Meta.synthInstance.resume] size: 2
    [Meta.synthInstance.answer] ✅️ Nonempty (Sum Nat Empty)
  [Meta.synthInstance] result @Sum.nonemptyLeft Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
:::

:::paragraph
通过查看跟踪，可以观察 Lean 在类型类实例搜索中采用的深度优先回溯搜索。
要熟悉它可能需要一些练习！
在上例中，Lean 依次执行以下步骤：

* Lean 首先考虑目标 {lean}`Nonempty (Sum Nat Empty)`。Lean 发现有四种可能满足该目标的方式：
  - {name}`Sum.nonemptyRight` 实例，它会产生子目标 {lean}`Nonempty Empty`。
  - {name}`Sum.nonemptyLeft` 实例，它会产生子目标 {lean}`Nonempty Nat`。
  - {name}`instNonemptyOfMonad` 实例，它会产生两个子目标 {lean}`Monad (Sum Nat)` 与 {lean}`Nonempty Nat`。
  - {name}`instNonemptyOfInhabited` 实例，它会产生子目标 {lean}`Inhabited (Sum Nat Empty)`。
* 它应用 {name}`Sum.nonemptyRight` 并成功，留下新目标 {lean}`Nonempty Empty`。
* 接着考虑第一个子目标 {lean}`Nonempty Empty`。Lean 发现有两种可能满足该目标的方式：
  - {name}`instNonemptyOfMonad` 实例，但它被拒绝。
    它不能使用，因为类型 {lean}`Empty` 不是某个单子对类型的应用。
  - {name}`instNonemptyOfInhabited` 实例，它会产生子目标 {lean}`Inhabited Empty`。
* 接着考虑新产生的子目标 {lean}`Inhabited Empty`。
  Lean 只发现一种可能满足该目标的方式，即 {name}`instInhabitedOfMonad`，但它被拒绝。
  原因同前：类型 {lean}`Empty` 不是某个单子对类型的应用。
* 此时，已经没有其他选项可以达成最初的第一个子目标。
  搜索于是回溯，改用 {name}`Sum.nonemptyLeft` 实例，而它需要一个 {lean}`Nonempty Nat` 实例。
  该搜索最终通过 {inst}`Inhabited Nat` 实例取得成功。
:::

最初的第三、第四个候选项从未被考虑。
一旦对 {lean}`Nonempty Nat` 的搜索成功，{keywordOf Lean.Parser.Command.synth}`#synth` 命令便会结束并输出解：
```leanOutput trace
@Sum.nonemptyLeft Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
::::

# 候选实例
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Instance-Synthesis--Candidate-Instances"
%%%

实例合成在搜索中同时使用局部实例和全局实例。
{deftech (key := "local instances")}_局部实例_是局部上下文中可用的实例；它们可以是函数的参数，也可以用 `let` 在局部定义。{TODO}[指向 `let` 文档的交叉引用]
局部实例无需特别标示；任何类型为类型类的局部变量都是实例合成的候选项。
{deftech (key := "global instances")}_全局实例_是全局环境中可用的实例；每个全局实例都是一个应用了 {attr}`instance` 属性的已定义名称。{margin}[{keywordOf Lean.Parser.Command.declaration}`instance` 声明会自动应用 {attr}`instance` 属性。]

::::keepEnv
:::example "局部实例"
在本例中，{lean}`addPairs` 包含一个局部定义的 {lean}`Add NatPair` 实例：
```lean
structure NatPair where
  x : Nat
  y : Nat

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
  p1 + p2
```
实例合成找到该局部实例，并将其用于加法。
:::
::::

::::keepEnv
:::example "局部实例优先"
这里虽然已有全局实例，{lean}`addPairs` 仍包含一个局部定义的 {lean}`Add NatPair` 实例：
```lean
structure NatPair where
  x : Nat
  y : Nat

instance : Add NatPair where
  add
    | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun _ _ => ⟨0, 0⟩⟩
  p1 + p2
```
最终选择的是局部实例，而非全局实例：
```lean (name:=addPairsOut)
#eval addPairs ⟨1, 2⟩ ⟨5, 2⟩
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
:::
::::

# 实例参数与合成
%%%
tag := "instance-synth-parameters"
%%%

实例的搜索过程主要由类参数支配。
类型类接受一定数量的参数；搜索期间，如果某个实例所选的参数与当前正在合成实例的类类型中的参数_兼容_，就会尝试该实例。

实例本身也可以接受参数，但实例的参数在实例合成中扮演的角色大不相同。
实例的参数要么表示可由实例合成实例化的变量，要么表示使用该实例前需要完成的进一步合成工作。
具体而言，实例的参数可以是显式的、隐式的或实例隐式的。
若参数是实例隐式的，就会引发进一步的递归实例搜索；而显式或隐式参数必须通过合一来解决。

::::keepEnv
:::example "实例的隐式参数与显式参数"
虽然实例通常以隐式或实例隐式方式接受参数，但在实例合成过程中，显式参数也可以像隐式参数一样被填充。
本例中，合成过程找到 {name}`aNonemptySumInstance`，并将它显式应用于 {lean}`Nat`，这是保证类型正确所必需的。
```lean
instance aNonemptySumInstance
    (α : Type) {β : Type} [inst : Nonempty α] :
    Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
```

```lean (name := instSearch)
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)
```
输出中，显式参数 {lean}`Nat` 和隐式参数 {lean}`Empty` 都是通过与搜索目标合一找到的，而 {lean}`Nonempty Nat` 实例则通过递归实例合成找到。
```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
:::
::::

# 输出参数
%%%
tag := "class-output-parameters"
%%%

默认情况下，类型类的参数被视为搜索过程的_输入_。
如果参数未知，搜索过程就会卡住，因为选择实例要求参数值与该实例中的值匹配，而依据不完整的信息无法确定这些值。
在大多数情况下，猜测实例会使实例合成变得不可预测。

然而在某些情况下，一个参数的选择应当自动决定另一个参数。
例如，重载成员关系谓词的类型类 {name}`Membership` 将数据结构中元素的类型视为输出，因此在使用位置可以由数据结构的类型确定元素类型，而无需在实例合成开始前提供足够的类型标注来同时确定_两种_类型。
仅凭某个元素属于 {lean}`List Nat`，就可以断定该元素是 {lean}`Nat`。

```signature -show
-- 测试上述说法
Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
```

可以用 {name}`outParam` 这一{tech (key := "gadget")}[小工具]包装类型类参数的类型，从而将参数声明为输出。
当类参数是{deftech (key := "output parameter")}_输出参数_时，实例合成不会要求它已知；事实上，任何已有值都会被完全忽略。
会选中第一个匹配输入参数的实例，并将该实例为输出参数指定的值作为其值。
如果原先已有值，则在合成完成后将其与指定值比较；二者不匹配即为错误。

{zhdocstring outParam ZhDoc.Classes.InstanceSynth.outParam}

::::example "输出参数与卡住的搜索"
:::keepEnv
这个序列化框架提供了将值转换为某种底层存储类型的方法：
```lean
class Serialize (input output : Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```

在本例中，输出类型未知。
```lean +error (name := noOutputType)
example := ser (2, 3)
```
实例合成无法选择 {lean}`Serialize Nat String` 实例，因而也无法选择 {lean}`Append String` 实例，因为这要求将输出类型实例化为 {lean}`String`，所以搜索会卡住：
```leanOutput noOutputType
typeclass instance problem is stuck
  Serialize (Nat × Nat) ?m.5

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Serialize` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
正如消息所示，一种修复方法是提供预期类型：
```lean
example : String := ser (2, 3)
```
:::
:::keepEnv
另一种方法是将输出类型改为输出参数：
```lean
class Serialize (input : Type) (output : outParam Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
现在，实例合成可以自由选择 {lean}`Serialize Nat String` 实例，从而解决 {name}`ser` 的未知隐式参数 `output`：
```lean
example := ser (2, 3)
```
:::
::::

::::keepEnv
:::example "已有值的输出参数"
类 {name}`OneSmaller` 表示一种转换方式：将某类型的非最大元素转换为元素数量少一个的类型中的元素。
有两个不同的实例都能匹配输入类型 {lean}`Option Bool`，但它们的输出不同：
```lean
class OneSmaller (α : Type) (β : outParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
由于实例合成会选择最近定义的实例，以下代码会报错：
```lean +error (name := nosmaller)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller
failed to synthesize instance of type class
  OneSmaller (Option Bool) Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
实例合成选择了 {lean}`OneSmaller (Option Bool) (Option Unit)` 实例，而没有考虑所提供的 `β` 值。
:::
::::

{deftech (key := "semi-output parameters")}_半输出参数_与输出参数相似，都无需在合成开始前已知；但与输出参数不同，选择实例时会考虑半输出参数的值。

{zhdocstring semiOutParam ZhDoc.Classes.InstanceSynth.semiOutParam}

半输出参数对实例施加了一项要求：带有半输出参数的类的每个实例，都应当确定其半输出参数的值。
:::TODO
如果无法确定，会出现什么问题？
:::

::::keepEnv
:::example "已有值的半输出参数"
类 {name}`OneSmaller` 表示一种转换方式：将某类型的非最大元素转换为元素数量少一个的类型中的元素。
它有两个不同的实例都能匹配输入类型 {lean}`Option Bool`，但输出不同：
```lean
class OneSmaller (α : Type) (β : semiOutParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```

由于实例合成在选择实例时会考虑半输出参数，所提供的 `β` 值使 {lean}`OneSmaller (Option Bool) (Option Unit)` 实例被跳过：
```lean (name := nosmaller2)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
```
:::
::::

# 默认实例
%%%
tag := "default-instance-synth"
%%%

当实例合成没有选中实例、原本将要失败时，会按优先级尝试使用 {attr}`default_instance` 属性指定的{deftech (key := "default instances")}_默认实例_。
优先级相同时，较新定义的默认实例先于较早定义的默认实例。
会选择第一个使搜索成功的默认实例。

如果默认实例本身带有实例隐式参数，就可能引发进一步的递归实例搜索。
若递归搜索失败，搜索过程就会回溯并尝试下一个默认实例。

# “实质上典范的”实例
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Instance-Synthesis--___Morally-Canonical___-Instances"
%%%

在实例合成期间，如果目标已完全确定（即不含元变量）且搜索成功，就不会再为同一目标尝试其他实例。
换言之，如果对某个目标的搜索成功，且后续信息增加也不可能推翻这一成功，那么即便还存在其他可能可用的实例，也不会再次尝试该目标。
这一优化可以防止实例合成搜索后续分支中的失败引发虚假回溯，避免用对巨大状态空间的缓慢探索替换先前分支中的快速解。

该优化依赖于实例是{deftech (key := "morally canonical")}_实质上典范的_这一假设。
即使给定类型类的重载操作存在多个潜在实现，或由于菱形而存在多种实例合成方式，也应认为_任何找到的实例都与其他实例同样好_。
换言之，只要保证其中一个实例可用，就无需考虑_所有_潜在实例。
可以用向后兼容选项 {option}`backward.synthInstance.canonInstances` 禁用该优化；此选项可能会在未来版本的 Lean 中移除。

使用实例隐式参数的代码应当准备好将所有实例视为等价。
换言之，它应当能够稳健应对合成实例之间的差异。
如果代码依赖实例_事实上_等价，那么它要么应显式操纵实例（例如通过局部定义、将实例保存在结构字段中，或让结构继承适当的类），要么应在类型中明确体现这一依赖，使不同的实例选择产生不兼容的类型。

# 包装合成出的实例
%%%
tag := "instance-wrapping"
%%%

在 {name}`inferInstanceAs` 或默认的 {keywordOf Lean.Parser.Command.declaration}`deriving` 处理器合成实例后，会处理实例体，以确保其实例类型和各字段类型在 {name Lean.Meta.TransparencyMode.instances}`instances` 透明度下与预期类型匹配；该透明度只展开{tech (key := "reducible")}[可约]定义和{tech (key := "implicit reducible")}[隐式可约]定义。
这一处理可以防止实例在低于{tech (key := "semireducible")}[半可约]透明度下归约时泄漏其实例定义的内部细节，因为这种泄漏可能在代码库的不同部分之间引入非预期依赖。

如果预期类型是命题，实例会被包装在一个辅助定理中。
否则，合成出的实例会在 {name Lean.Meta.TransparencyMode.instances}`instances` 透明度下归约到弱头范式。
如果结果是构造器应用，则会处理每个字段：
* 如果能为子实例字段的类型找到新合成的实例，就用该实例替换该字段。
  这可确保该实例与客户端代码自行合成实例时找到的实例相同，避免通往实例的多条路径（称为_菱形_）产生彼此并非{tech (key := "definitional equality")}[定义相等]的实例。
  如果合成没有找到实例，就用此过程递归包装该字段。
* 类型与预期类型并非定义相等的证明字段，会被包装在辅助定理中，以隐藏类型差异。
* 类型与预期类型不匹配的数据字段，会被包装在具有适当可约性的辅助定义中。

如果实例无法归约为构造器应用且其类型与预期类型不匹配，就会被包装在具有适当可约性的辅助定义中。

# 选项
%%%
tag := "The-Lean-Language-Reference--Type-Classes--Instance-Synthesis--Options"
%%%

{zhOptionDocs backward.synthInstance.canonInstances ZhDoc.Classes.InstanceSynth.Option.backward.synthInstance.canonInstances}

{zhOptionDocs synthInstance.maxHeartbeats ZhDoc.Classes.InstanceSynth.Option.synthInstance.maxHeartbeats}

{zhOptionDocs synthInstance.maxSize ZhDoc.Classes.InstanceSynth.Option.synthInstance.maxSize}

{zhOptionDocs backward.inferInstanceAs.wrap ZhDoc.Classes.InstanceSynth.Option.backward.inferInstanceAs.wrap}

{zhOptionDocs backward.inferInstanceAs.wrap.reuseSubInstances ZhDoc.Classes.InstanceSynth.Option.backward.inferInstanceAs.wrap.reuseSubInstances}

{zhOptionDocs backward.inferInstanceAs.wrap.instances ZhDoc.Classes.InstanceSynth.Option.backward.inferInstanceAs.wrap.instances}

{zhOptionDocs backward.inferInstanceAs.wrap.data ZhDoc.Classes.InstanceSynth.Option.backward.inferInstanceAs.wrap.data}
