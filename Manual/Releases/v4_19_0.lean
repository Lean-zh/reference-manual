/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: figure out why this is needed with the new compiler
set_option maxRecDepth 11000

#doc (Manual) "Lean 4.19.0 (2025-05-01)" =>
%%%
tag := "release-v4.19.0"
file := "v4.19.0"
%%%

````markdown
本次发布共合入 420 项变更。除下文列出的 164 项功能新增和 78 项修复外，还有 13 项重构、29 项文档改进、31 项性能改进、9 项测试套件改进以及 94 项其他变更。

## 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights"
%%%

Lean v4.19.0 带来了多项新特性、错误修复、性能提升和库方面的发展，并在文档、语言服务器和 Lake 等方面提供了诸多易用性改进。

### VS Code 中的新装饰
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--New-Decorations-in-VS-Code"
%%%

VS Code 中的视觉反馈得到了改进，扩展现在提供了：

* 用于错误和警告的装饰栏标记。它们能清楚展示错误/警告所覆盖的完整范围，这在相应波浪线较短时尤其有用。
* 用于 “unsolved goals” 的行尾标记。它们显示在 “unsolved goals” 错误结束的那一行，并指示证明需要从哪里继续。
* “Goals accomplished!” 消息。当某个定理或类型为 `Prop` 的 `example` 不再包含错误或 `sorry` 时，声明起始位置旁边会在装饰栏中显示两个蓝色对勾。此外，InfoView 的 “Messages” 下还会出现一条 “Goals accomplished!” 消息。

用于错误和警告的装饰栏标记适用于所有 Lean 4 版本。
“unsolved goals” 和 “goals accomplished” 的装饰依赖服务端支持，而这一支持已通过 [#7366](https://github.com/leanprover/lean4/pull/7366) 在本版本中加入。

以上所有特性都可以关闭，而 “Goals accomplished!” 图标还可以在 VS Code 扩展设置中进行配置。
详情请参见 [leanprover/vscode-lean4#585](https://github.com/leanprover/vscode-lean4/pull/585)。

### 并行精化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--Parallel-Elaboration"
%%%

* [#7084](https://github.com/leanprover/lean4/pull/7084) 允许定理体（即证明）的精化彼此并行，也可与其他精化任务并行进行。

### 语言特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--Language-Features"
%%%

* [#5182](https://github.com/leanprover/lean4/pull/5182) 让通过良基递归定义的函数默认使用 `opaque` 的良基性证明。这可以可靠地阻止内核对此类定义和证明做归约，而这种归约通常慢得难以接受（修复了 [#2171](https://github.com/leanprover/lean4/issues/2171)），并且经常导致难以调试的内核类型检查失败。该变更使 `unseal` 对这类定义不再有效。若想避免使用 opaque 证明，请为函数定义加上 `@[semireducible]` 标注。

* [#7166](https://github.com/leanprover/lean4/pull/7166) 将递归函数“固定参数”的概念扩展到位于变化函数参数之后的参数。其主要好处是我们能够得到更友好的归纳原则。

  以前，定义

  ```lean
  def app (as : List α) (bs : List α) : List α :=
    match as with
    | [] => bs
    | a::as => a :: app as bs
  ```

  会生成

  ```lean
  app.induct.{u_1} {α : Type u_1} (motive : List α → List α → Prop) (case1 : ∀ (bs : List α), motive [] bs)
    (case2 : ∀ (bs : List α) (a : α) (as : List α), motive as bs → motive (a :: as) bs) (as bs : List α) : motive as bs
  ```

  而现在你会得到

  ```lean
  app.induct.{u_1} {α : Type u_1} (motive : List α → Prop) (case1 : motive [])
    (case2 : ∀ (a : α) (as : List α), motive as → motive (a :: as)) (as : List α) : motive as
  ```

  因为 `bs` 在整个递归过程中保持不变（因此可以完全从该原则中删除）。

  当显式使用这类归纳原则时，这是一项 **破坏性变更**。使用 `fun_induction` 可以让证明策略对这一变化保持稳健。

  关于何时认为一个参数是固定的，请参见 PR 描述中的规则。

  请注意，在如下定义中

  ```lean
  def app : List α → List α → List α
    | [], bs => bs
    | a::as, bs => a :: app as bs
  ```

  `bs` 不会被视为固定参数，因为它经过了匹配器机制。

* [#7431](https://github.com/leanprover/lean4/pull/7431) 修改了 `simp`、`rw` 等策略的位置修饰符语法（例如 `simp at h ⊢`），使转门符 `⊢` 可以出现在位置序列中的任意位置。

* [#7457](https://github.com/leanprover/lean4/pull/7457) 通过引入可为异步精化任务填补空洞的 API，确保检查器和请求处理器等信息树使用方能够访问由异步精化任务创建的信息子树。

  **破坏性变更：** `Command.State.infoState` 的其他元编程使用者，可能需要手动对其调用 `InfoState.substituteLazy` 以填补所有空洞。

### 结构与类的更新
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--Updates-to-structures-and-classes"
%%%

* [#7302](https://github.com/leanprover/lean4/pull/7302) 修改了 `structure`/`class` 命令中字段的精化方式，并且在出现菱形继承时，让默认值遵循结构解析顺序。此前，子对象的细节会在精化期间暴露出来；在局部上下文中，任何来自子对象的字段都被定义为对子对象字段的投影。现在，每个字段都表示为局部变量。所有父项（而不只是子对象父项）现在都会出现在局部上下文中，并且被定义为将父构造子应用到字段变量后的局部变量（与此前的关系相反）。更多细节请参见 PR 描述。

* [#7640](https://github.com/leanprover/lean4/pull/7640) 实现了 `structure`/`class` 命令中继承与覆盖 autoParam 字段的主要逻辑，待结构体实例记法精化器启用。该 PR 还为被覆盖字段加入了术语信息，因此现在可以对它们使用悬停，且“跳转到定义”会跳到该字段最初定义所在的结构。

* [#7717](https://github.com/leanprover/lean4/pull/7717) 修改了 `{...}`/`where` 记法（“结构体实例记法”）的精化方式。该记法现在会尽可能模拟一种扁平表示，而不暴露子对象的细节。
  这是一项 **破坏性变更**；更多细节及缓解策略请参见 PR 描述。

* [#7742](https://github.com/leanprover/lean4/pull/7742) 为 `structure`/`class` 增加了一项特性：字段定义中没有类型的绑定器会被解释为覆盖该字段投影函数中类型参数的绑定器种类。更多细节请参见 PR 描述。

### 库更新
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--Library-Updates"
%%%

* 异步机制方面的发展；
* 整数除法 API 的标准化；
* 有限类型之间的转换；
* `BitVec` 和树映射的 API 扩展；
* Bitwuzla 重写规则的证明；
* 对 `List`/`Array`/`Vector` 以及 `HashMap` 和 `Int`/`Nat` 的改进。

详见下方的“库”一节。

### 其他亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Highlights--Other-Highlights"
%%%

* 文档得到了大幅扩充。详见下方的“文档”一节。

* [#7185](https://github.com/leanprover/lean4/pull/7185) 重构了 Lake 的构建内部机制，以便引入超出包、模块和库范畴的目标与构面。构面、构建键、构建信息和 CLI 命令都被泛化到了任意目标类型。

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language"
%%%

* [#5182](https://github.com/leanprover/lean4/pull/5182) 让通过良基递归定义的函数默认使用 `opaque` 的良基性证明；详见上方亮点部分。

* [#5998](https://github.com/leanprover/lean4/pull/5998) 让 `omega` 始终将自身证明抽象为辅助定义。借此，`Vector.Extract` 的 olean 大小从 20MB 降至 5MB，整个 stdlib 的 olean 总大小和构建指令数都下降了 5%。

* [#6325](https://github.com/leanprover/lean4/pull/6325) 确保环境可以被反复加载，而不会执行任意代码。

* [#7075](https://github.com/leanprover/lean4/pull/7075) 确保 `simp?` 等策略建议的名称不会被局部上下文中的辅助声明遮蔽，并确保 `let rec` 与 `where` 声明的名称在策略块中能够被正确解析。

* [#7166](https://github.com/leanprover/lean4/pull/7166) 将递归函数“固定参数”的概念扩展到位于变化函数参数之后的参数；详见上方亮点部分。

* [#7256](https://github.com/leanprover/lean4/pull/7256) 引入 `assert!` 的变体 `debug_assert!`，它会在以 `buildType` `debug` 编译时启用。

* [#7304](https://github.com/leanprover/lean4/pull/7304) 修复了一个问题：当嵌套的 `let rec` 声明位于 `match` 表达式或策略块中，并且它们自身又嵌套在一个引用了外层声明所绑定变量的 `let rec` 内、同时递归调用该 `let rec` 时，先前会编译失败。

* [#7324](https://github.com/leanprover/lean4/pull/7324) 修改了良基递归的内部构造方式，使其不会以非 defeq 的方式改变 `fix` 的归纳假设类型。

* [#7333](https://github.com/leanprover/lean4/pull/7333) 允许 decreasing_by 策略生成辅助声明（例如由 `match` 生成的那些）。

* [#7335](https://github.com/leanprover/lean4/pull/7335) 调整了 `elabTerminationByHints`：用于精化终止性度量的递归函数类型会去掉可选参数。这样可以避免为参数默认值引入依赖关系，因为这些依赖关系会导致终止性检查失败。

* [#7353](https://github.com/leanprover/lean4/pull/7353) 修改了 `abstractNestedProofs`，使其也会遍历应用头部中的子项。

* [#7362](https://github.com/leanprover/lean4/pull/7362) 允许 simp discharger 向环境添加辅助声明。这使得 `native_decide` 等策略可以在这里使用，并为 #5998 中的 omega 改进扫清了障碍。

* [#7387](https://github.com/leanprover/lean4/pull/7387) 在 `bv_omega` 中使用 `-implicitDefEqProofs`，以确保其不受 #7386 中变更的影响。

* [#7397](https://github.com/leanprover/lean4/pull/7397) 确保 `Poly.mul p 0` 总是返回 `Poly.num 0`。

* [#7409](https://github.com/leanprover/lean4/pull/7409) 允许在良基定义的预处理中使用 `dsimp`。这修复了某些回归：在使用未命名条件的 `if-then-else` 时，如果终止性证明需要用到该条件，而相关子表达式只能通过 dsimp 而不能通过 simp 到达（例如位于依赖 let 中），先前会失败。

* [#7431](https://github.com/leanprover/lean4/pull/7431) 修改了 `simp`、`rw` 等策略的位置修饰符语法（例如 `simp at h ⊢`），使转门符 `⊢` 可以出现在位置序列中的任意位置。

* [#7509](https://github.com/leanprover/lean4/pull/7509) 在 `bv_decide` 的预处理器中禁用了 `implicitDefEqProofs` simp 选项，以应对 #7387 导致的回归。

* [#7511](https://github.com/leanprover/lean4/pull/7511) 修复了 `simp +arith` 中两个 bug，这两个 bug 先前阻止了某些特定子项被规范化。

* [#7515](https://github.com/leanprover/lean4/pull/7515) 修复了 `simp +arith` 中另一个 bug。该 bug 会影响 `grind`。示例请参见新增测试。

* [#7551](https://github.com/leanprover/lean4/pull/7551) 修改了 `isNatCmp`：在检查 `Nat` 元素之间类似 `<` 的比较时，会忽略可选参数注解。此前这会导致 `guessLex` 在检查某些函数终止性时失败，因为这些函数签名中包含了 `Nat` 类型的可选参数。

* [#7560](https://github.com/leanprover/lean4/pull/7560) 确保在线性 `Int` 项与关系的规范化中使用同一种排序方式。该改动会影响 `simp +arith` 和 `grind` 规范化器。

* [#7622](https://github.com/leanprover/lean4/pull/7622) 修复了 `fun_induction` 在结构递归函数上的行为问题：当目标出现在固定参数之前时，先前会出错。

* [#7630](https://github.com/leanprover/lean4/pull/7630) 修复了 `whnfCore` 过程中的一个性能问题。

* [#7728](https://github.com/leanprover/lean4/pull/7728) 修复了 `abstractNestedProofs` 中的问题。我们还应当抽象出现在推断命题中的证明。

### 结构
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language--Structures"
%%%

* [#7302](https://github.com/leanprover/lean4/pull/7302) 修改了 `structure`/`class` 命令中字段的精化方式，并且在出现菱形继承时，让默认值遵循结构解析顺序。此前，子对象的细节会在精化期间暴露出来；在局部上下文中，任何来自子对象的字段都被定义为对子对象字段的投影。现在，每个字段都表示为局部变量。所有父项（而不只是子对象父项）现在都会出现在局部上下文中，并且被定义为将父构造子应用到字段变量后的局部变量（与此前的关系相反）。其他说明如下：
  - 现在会处理完整的父项集合，并检查所有父投影名称的一致性。每个父项现在都会出现在局部上下文中。
  - 对于类，每个父项现在都会贡献一个实例，而不只是那些表示为子对象的父项。
  - 默认值现在按父项解析顺序处理。默认值定义/覆盖的辅助定义存放在 `StructName.fieldName._default`，继承来的值存放在 `StructName.fieldName._inherited_default`。元程序在对默认值做计算时，不再需要查看父项。
  - 结构体实例记法美观打印中对默认值省略的处理也已相应更新。
  - 现在精化器会生成一个 `_flat_ctor` 构造子，用于结构体实例精化。这个构造子中的所有类型都被放入“字段规范形”（父构造子的投影会被约简，投影的父构造子会被 eta 约简），并且所有带 autoParam 的字段都会被如此标注。它并非面向普通用户，但可能对元编程有用。
  - 在精化字段时，任何类型为某个父项的元变量都会被赋值为该父项。其假设是：在精化结构字段时，父项是固定的——对于任意给定父项，当前只考虑 *一个* 实例。关于这一点为何必要，请参见 `Magma` 测试。若存在递归结构，该假设可能不成立，因为结构的不同值在父字段上可能并不一致。

* [#7314](https://github.com/leanprover/lean4/pull/7314) 修改了 `structure` 父项的精化方式，要求每个父项都必须在处理下一个父项之前被完全精化。

* [#7640](https://github.com/leanprover/lean4/pull/7640) 实现了 `structure`/`class` 命令中继承与覆盖 autoParam 字段的主要逻辑，待结构体实例记法精化器启用。该 PR 还为被覆盖字段加入了术语信息，因此现在可以对它们使用悬停，且“跳转到定义”会跳到该字段最初定义所在的结构。

* [#7652](https://github.com/leanprover/lean4/pull/7652) 让结构上的 `#print` 能够显示字段的默认值和 auto-param 策略。

* [#7717](https://github.com/leanprover/lean4/pull/7717) 修改了 `{...}`/`where` 记法（“结构体实例记法”）的精化方式。该记法现在会尽可能模拟一种扁平表示，而不暴露子对象的细节。其特性包括：
  - 在精化字段时，其期望类型现在会自动做若干约简。对结构及其父项相关的所有投影和构造子，构造子的投影会被约简，投影上的构造子会被 eta 约简；此外，在命题中还会对实现细节局部变量做 zeta 约简（因此策略证明应当不再看到它们）。另外，连续字段类型中的字段值也会自动进行 beta 约简。 [mathlib4#12129](https://github.com/leanprover-community/mathlib4/issues/12129#issuecomment-2056134533) 中的例子现在会展示目标 `0 = 0`，而不是 `{ toFun := fun x => x }.toFun 0 = 0`。
  - 现在所有父项都可以作为字段名使用，而不仅仅是子对象父项。它们类似于额外来源，但有三个限制：该值的每个字段都必须被使用，这些字段不得与其他已提供字段重叠，并且指定父项的每个字段都必须齐备。与这些额外来源类似，如果这些值本身还不是变量，就会先提升为 `let`，以避免重复求值。它们属于实现细节局部变量，因此在后续字段中会被展开。
  - 现在所有类父项都会用于填补缺失字段，而不只是子对象父项。关闭了 #6046。规则如下：(1) 只考虑其字段集合是剩余字段子集的父项；(2) 只在开始精化任何字段之前考虑父项；(3) 只考虑那些类型可以计算出来的父项（如果一个父项依赖另一个父项，这种情况就可能发生，而 #7302 之后这是可能的）。
  - 默认值和自动参数现在完全遵循解析顺序：每个字段至多只有一个默认值定义可为其提供值。此前那种通过沿子对象层级向上遍历来“解卡住”默认值的算法已经被移除。如果默认值优先级的应用场景足够多，我们也许会在未来版本中重新考虑。
  - 最终生成的构造子现在都是完全打包的。这是通过对已精化表达式执行 structure eta reduction 实现的。
  - “魔法字段定义”（如 [Zulip 上](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Where.20is.20sSup.20defined.20on.20submodules.3F/near/499578795) 报告的情况）已被移除。此前，某些字段会通过统一过程被求解，从而误导默认值系统，以为这些字段真的是用户显式提供的。现在默认值系统会跟踪它实际求解了哪些字段，以及用户没有提供哪些字段。没有任何显式值定义的显式结构字段（默认类别）会报错。如果该字段是通过统一过程求解出来的，错误消息还会包含推断出的值，例如 “field 'f' must be explicitly provided, its synthesized value is v”。
  - 当该记法用于模式时，现在不再通过类父项插入字段，也不再应用自动参数或默认值。其动机在于，人们通常期望模式只匹配给出的字段。这一点仍不完美，因为某些字段仍可能被间接求解。
  - 现在精化过程会尝试进行错误恢复。多余字段会记录错误并被忽略，缺失字段则会用 `sorry` 补上。

* [#7742](https://github.com/leanprover/lean4/pull/7742) 为 `structure`/`class` 增加了一项特性：字段定义中没有类型的绑定器会被解释为覆盖该字段投影函数中类型参数的绑定器种类。规则如下：(1) 只有绑定器的一个前缀会按此解释；(2) 允许多标识符绑定器，但它们都必须对应参数；(3) 只有声明自身中出现的参数（而不是来自 `variables` 的参数）可以被覆盖；(4) 更新会在参数绑定器种类推断完成后应用。默认值重定义中不允许做这类绑定器更新。示例应用如下：在下面的代码中，`(R p)` 会使 `R` 和 `p` 参数变为显式，而它们通常会是隐式的。
  ```
  class CharP (R : Type u) [AddMonoidWithOne R] (p : Nat) : Prop where
    cast_eq_zero_iff (R p) : ∀ x : Nat, (x : R) = 0 ↔ p ∣ x

  #guard_msgs in #check CharP.cast_eq_zero_iff
  /-
  info: CharP.cast_eq_zero_iff.{u} (R : Type u) {inst✝ : AddMonoidWithOne R} (p : Nat) [self : CharP R p] (x : Nat) :
    ↑x = 0 ↔ p ∣ x
  -/
  ```

* [#7746](https://github.com/leanprover/lean4/pull/7746) 为那些从未表示为子对象的父项复制而来的结构字段添加了声明范围，以支持“跳转到定义”。该声明范围对应 `extends` 子句中的父项。

### 并行精化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language--Parallel-Elaboration"
%%%

* [#7084](https://github.com/leanprover/lean4/pull/7084) 允许定理体（即证明）的精化彼此并行，也可与其他精化任务并行进行。

* [#7247](https://github.com/leanprover/lean4/pull/7247) 让 `match` 方程和分裂器的生成兼容并行化。

* [#7261](https://github.com/leanprover/lean4/pull/7261) 确保核心中所有方程、unfold、induction 以及 partial fixpoint 定理生成器都与并行化兼容。

* [#7348](https://github.com/leanprover/lean4/pull/7348) 确保核心中所有方程和 unfold 定理生成器都与并行化兼容。

* [#7457](https://github.com/leanprover/lean4/pull/7457) 通过引入可为异步精化任务填补空洞的 API，确保检查器和请求处理器等信息树使用方能够访问由异步精化任务创建的信息子树。

* [#8101](https://github.com/leanprover/lean4/pull/8101) 修复了一个并行化回归：诸如检查命令错误的检查器先前将无法再找到这类消息。

### bv_decide
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language--bv_decide"
%%%

* [#7298](https://github.com/leanprover/lean4/pull/7298) 向 bv_decide 的预处理中加入了若干重写，涉及 if-then-else 与乘法、取负等运算的组合。

* [#7309](https://github.com/leanprover/lean4/pull/7309) 修复了一个 bug：在 bv_decide 新增的结构支持中，如果结构 fvar 的类型是 mvar，有时不会对所有可用结构 fvar 进行分类讨论。

* [#7329](https://github.com/leanprover/lean4/pull/7329) 为 bv_decide 添加了对枚举归纳类型简单模式匹配的支持。这里的“简单”是指非依赖的 match 语句，并且所有分支都被完整写出。

* [#7347](https://github.com/leanprover/lean4/pull/7347) 将随 bv_decide 一起分发并使用的 CaDiCal 升级到 2.1.2 版。此外，由于 https://github.com/arminbiere/cadical/issues/112 已被修复，它还默认在 Windows 上启用了二进制 LRAT 证明。

* [#7381](https://github.com/leanprover/lean4/pull/7381) 重构了支撑 bv_decide 的 AIG 数据结构，以便更好地跟踪电路中的取反。这次重构有两个效果：一是为 AIG 框架加入了完整的常量折叠，二是让我们能够在未来继续加入 Brummayer/Biere 论文中的更多简化，而此前在架构上这是不可能做到的。

* [#7390](https://github.com/leanprover/lean4/pull/7390) 让 bv_decide 的预处理能够处理 cast。由于我们处在常量 BitVec 片段中，应当总能利用 `BitVec.cast_eq` 将它们移除。

* [#7407](https://github.com/leanprover/lean4/pull/7407) 将 `-1#w * a = -a` 和 `a * -1#w = -a` 两条规则加入 `bv_normalize`，对应 Bitwuzla 中的 BV_MUL_SPECIAL_CONST。

* [#7417](https://github.com/leanprover/lean4/pull/7417) 为 bv_decide 添加了对带默认分支的枚举归纳匹配的支持。

* [#7429](https://github.com/leanprover/lean4/pull/7429) 将 Bitwuzla 的 BV_EXTRACT_FULL 预处理规则加入 bv_decide。

* [#7436](https://github.com/leanprover/lean4/pull/7436) 添加了 simproc，可将按常量进行的左右移转换为 extract，再交给 bv_decide 处理。

* [#7438](https://github.com/leanprover/lean4/pull/7438) 将 EQUAL_CONST_BV_ADD 和 BV_AND_CONST 规则加入 bv_decide 的预处理器。

* [#7441](https://github.com/leanprover/lean4/pull/7441) 将 Bitwuzla 中的 BV_CONCAT_CONST、BV_CONCAT_EXTRACT 和 ELIM_ZERO_EXTEND 规则加入 bv_decide。

* [#7477](https://github.com/leanprover/lean4/pull/7477) 确保 bv_decide 不会意外操作绑定器之下的项。由于目前 bv_decide 支持的片段中并不包含绑定器构造，因此这不会改变其证明能力。

* [#7480](https://github.com/leanprover/lean4/pull/7480) 为 Bitwuzla 规则 BV_ULT_SPECIAL_CONST、BV_SIGN_EXTEND_ELIM、TODO 添加了所需重写。

* [#7486](https://github.com/leanprover/lean4/pull/7486) 将 #7481 中引入的 `BitVec.add_neg_mul` 规则加入 bv_decide 的预处理器。

* [#7491](https://github.com/leanprover/lean4/pull/7491) 通过改进输入校验，加速了 bv_decide 的 LRAT 检查器。

* [#7521](https://github.com/leanprover/lean4/pull/7521) 为 AIG 框架加入了等价于 `Array.emptyWithCapacity` 的功能，并将其应用于 `bv_decide`。这一点尤其有用，因为我们处理的容量在运行时总是已知的，因此不应当需要重新分配 `RefVec`。

* [#7527](https://github.com/leanprover/lean4/pull/7527) 将 Bitwuzla 中的 BV_EXTRACT_CONCAT_LHS_RHS、NORM_BV_ADD_MUL 和 NORM_BV_SHL_NEG 重写，以及从 getLsbD 到 extractLsb' 的化简，加入 bv_decide。

* [#7615](https://github.com/leanprover/lean4/pull/7615) 将 Bitwuzla 的 BV_EXTRACT_ADD_MUL 规则中关于 ADD 的部分加入 bv_decide 的预处理器。

* [#7617](https://github.com/leanprover/lean4/pull/7617) 将乘法电路中的 known bits 优化也加入到了加法电路中，使我们在交给 SAT 求解器之前能够发现更多潜在对称性。

* [#7636](https://github.com/leanprover/lean4/pull/7636) 确保 bv_decide 中表达式级缓存会在整个位爆破器范围内维护，而不再只是局限于单个 BitVec 表达式。

* [#7644](https://github.com/leanprover/lean4/pull/7644) 为 bv_decide 的反射过程加入了缓存。

* [#7649](https://github.com/leanprover/lean4/pull/7649) 将常量的 AIG 表示从 `const (b : Bool)` 改为单一构造子 `false`。自 #7381 起，`Ref` 含有一个 `invert` 标志，因此常量 `true` 可以表示为指向 `false` 且 `invert` 被设定的 `Ref`，不会损失表达能力。

* [#7655](https://github.com/leanprover/lean4/pull/7655) 为 bv_decide 添加了关于乘法上取位的预处理规则。

* [#7663](https://github.com/leanprover/lean4/pull/7663) 使用计算字段来存储哈希码和指针相等性，从而提升位爆破器所用核心数据结构在比较和哈希映射查找上的性能。

* [#7670](https://github.com/leanprover/lean4/pull/7670) 改进了 bv_decide 反射过程中原子赋值的缓存计算。

* [#7698](https://github.com/leanprover/lean4/pull/7698) 为 bv_decide 的反射步骤加入了更多共享与缓存过程。

* [#7720](https://github.com/leanprover/lean4/pull/7720) 通过将反相位存放在 gate descriptor 的最低位中、而不是单独存为一个 `Bool`，压缩了 AIG 表示。

* [#7727](https://github.com/leanprover/lean4/pull/7727) 避免了 CNF 到 dimacs 转换中的一些不必要分配。

* [#7733](https://github.com/leanprover/lean4/pull/7733) 确保在 AIG 中，常量电路节点总是存放在第一个位置。这样在需要常量节点时就可以跳过缓存查找。

### Grind
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language--Grind"
%%%

* [#7355](https://github.com/leanprover/lean4/pull/7355) 修复了 `grind` 策略中 `markNestedProofs` 预处理器的一个 bug。

* [#7392](https://github.com/leanprover/lean4/pull/7392) 修复了 `grind` 策略在对 if-then-else 表达式进行分类讨论时的一个问题。

* [#7510](https://github.com/leanprover/lean4/pull/7510) 确保 `grind` 可以作为更强大的 `contradiction` 策略来使用，用户不再需要输入 `exfalso; grind` 或 `intros; exfalso; grind`。

* [#7512](https://github.com/leanprover/lean4/pull/7512) 为 `grind` 策略补上了缺失的 `Nat` 除法和模运算规范化规则。

* [#7514](https://github.com/leanprover/lean4/pull/7514) 为 `grind` 补充了更多缺失的 `div` 和 `mod` 规范化规则。

* [#7532](https://github.com/leanprover/lean4/pull/7532) 修复了将新事实放入 `grind` “to-do” 列表的过程。它会确保新事实被预处理，并且也移除了 `Nat.sub` 支持中的一些杂乱内容。

* [#7540](https://github.com/leanprover/lean4/pull/7540) 为 `Subtype` 添加了 `[grind cases eager]` 属性。请参见新增测试。

* [#7553](https://github.com/leanprover/lean4/pull/7553) 移除了 `grind` 中一条有问题的规范化规则，并补上了一个缺失的 dsimproc。

* [#7641](https://github.com/leanprover/lean4/pull/7641) 在 `grind` 中实现了基础的基于模型的理论组合。`grind` 现在可以求解如下例子：
  ```lean
  example (f : Int → Int) (x : Int)
      : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
    grind
  ```

* [#7712](https://github.com/leanprover/lean4/pull/7712) 确保 `grind` 始终将自身证明抽象为辅助定义/定理。这与 #5998 类似，但适用于 `grind`。

* [#7714](https://github.com/leanprover/lean4/pull/7714) 修复了 `grind` 中基于模型的理论组合模块里的一处断言违规。

* [#7723](https://github.com/leanprover/lean4/pull/7723) 为 `grind` 添加了配置项 `zeta` 和 `zetaDelta`。二者默认都设为 `true`。

* [#7724](https://github.com/leanprover/lean4/pull/7724) 将 `dite_eq_ite` 规范化规则加入 `grind`。这条规则对调和某个定义及其函数归纳原则之间的不匹配非常重要。

* [#7726](https://github.com/leanprover/lean4/pull/7726) 修复了 `grind` 中使用的 `markNestedProofs` 过程。此前漏掉了“嵌套证明的类型中还可能包含其他嵌套证明”这一情形。

* [#7760](https://github.com/leanprover/lean4/pull/7760) 确保 `grind` 在计算辅助合同引理时使用默认透明度设置。

* [#7765](https://github.com/leanprover/lean4/pull/7765) 改进了 `grind` 在引入阶段对依赖蕴含的规范化方式。
  以前，对于形如 `.. ⊢ (h : p) → q h` 的目标，`grind` 会引入一个假设 `h : p`，然后再规范化并断言一个 `p` 的非依赖副本。结果是局部上下文中会同时包含 `h : p` 和另一个单独的 `h' : p'`，其中 `p'` 是 `p` 的规范形。而且 `q` 仍然依赖原来的 `h`。

* [#7776](https://github.com/leanprover/lean4/pull/7776) 改进了 `grind` 中 E-matching 过程使用的等式证明 discharger。

* [#7777](https://github.com/leanprover/lean4/pull/7777) 修复了 `grind` 中的引入过程。此前它没有登记那些同时也是命题的局部实例。请参见新增测试。

* [#7778](https://github.com/leanprover/lean4/pull/7778) 为 `grind` 补上了 `LawfulBEq A` 的缺失传播规则。在无法获得实例 `DecidableEq A` 的上下文中，这些规则是必需的。请参见新增测试。

* [#7781](https://github.com/leanprover/lean4/pull/7781) 为 `grind` 添加了一条新的 `Bool` 不等式传播规则。现在，它会从不等式 `x = false`（`x = true`）传播出 `x = true`（`x = false`）。这确保我们不必对 `x` 做分类讨论才能得知该事实。请参见测试。

### CutSat
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Language--CutSat"
%%%

* [#7312](https://github.com/leanprover/lean4/pull/7312) 在 cutsat 线性整数算术过程中，为 `cooper_dvd_left` 及其变体实现了证明项生成。

* [#7315](https://github.com/leanprover/lean4/pull/7315) 在 cutsat 中实现了 Cooper 冲突消解。我们仍需实现回溯和不等式情形。

* [#7339](https://github.com/leanprover/lean4/pull/7339) 在 cutsat 过程中实现了 cooper 冲突消解，同时修复了证明项构造中的若干 bug。我们仍需补充更多测试，但已经可以求解下列 `omega` 无法求解的例子：
  ```lean
  example (x y : Int) :
      27 ≤ 11*x + 13*y →
      11*x + 13*y ≤ 45 →
      -10 ≤ 7*x - 9*y →
      7*x - 9*y ≤ 4 → False := by
    grind
  ```

* [#7351](https://github.com/leanprover/lean4/pull/7351) 确保 cutsat 在一元多项式情形下不必进行分类讨论。也就是说，只要某个区间内不存在满足整除约束的解，它就可以直接关闭目标。如下定理现在可以由 cutsat 一步证明：
  ```lean
  example (x : Int) : 100 ≤ x → x ≤ 10000 → 20000 ∣ 3*x → False := by
    grind
  ```

* [#7357](https://github.com/leanprover/lean4/pull/7357) 为 cutsat 过程加入了对 `/` 和 `%` 的支持。

* [#7369](https://github.com/leanprover/lean4/pull/7369) 在 cutsat 过程生成的证明项中，为每个出现的多项式使用 `let` 声明。

* [#7370](https://github.com/leanprover/lean4/pull/7370) 简化了 cutsat 中由 Cooper 冲突消解生成的证明项。

* [#7373](https://github.com/leanprover/lean4/pull/7373) 实现了 cutsat 过程最后缺失的一种情况，并修复了一个 bug。在模型构造期间，我们可能遇到一个有界区间，其中含有满足整除约束的整数解，但这些解不满足已知的不等约束。

* [#7394](https://github.com/leanprover/lean4/pull/7394) 添加了在 cutsat 过程中支持 `Nat` 所需的基础设施，同时也让 `grind` 更稳健。

* [#7396](https://github.com/leanprover/lean4/pull/7396) 修复了 cutsat 模型构造中的一个 bug。此前它会朝错误方向搜索解。

* [#7401](https://github.com/leanprover/lean4/pull/7401) 通过利用整除约束收紧不等式，改进了 cutsat 的模型搜索过程。

* [#7494](https://github.com/leanprover/lean4/pull/7494) 在 cutsat 过程中实现了对 `Nat` 不等式的支持。

* [#7495](https://github.com/leanprover/lean4/pull/7495) 在 cutsat 过程中实现了对 `Nat` 整除约束的支持。

* [#7501](https://github.com/leanprover/lean4/pull/7501) 在 cutsat 过程中实现了对 `Nat` 等式和不等式的支持。

* [#7502](https://github.com/leanprover/lean4/pull/7502) 在 cutsat 过程中实现了对 `Nat` 除法和模运算的支持。

* [#7503](https://github.com/leanprover/lean4/pull/7503) 在 cutsat 中实现了对 `Nat.sub` 的支持。

* [#7536](https://github.com/leanprover/lean4/pull/7536) 在 cutsat 过程中实现了对 `¬ d ∣ p` 的支持。

* [#7537](https://github.com/leanprover/lean4/pull/7537) 在 cutsat 过程中实现了对 `Int.natAbs` 和 `Int.toNat` 的支持。

* [#7538](https://github.com/leanprover/lean4/pull/7538) 修复了 cutsat 模型构造中的一个 bug。此前它在搜索结束时不会重置决策栈。

* [#7561](https://github.com/leanprover/lean4/pull/7561) 修复了 cutsat 对非线性 `Nat` 项的支持。例如，cutsat 之前会在下面这个例子中失败
  ```lean
  example (i j k l : Nat) : i / j + k + l - k = i / j + l := by grind
  ```
  因为当我们把 `Nat` 表达式注入到 `Int` 时，没有加入 `i / j` 非负这一事实。

* [#7579](https://github.com/leanprover/lean4/pull/7579) 改进了 cutsat 过程生成的反例，并为 `Nat` 提供了恰当支持。在这个 PR 之前，自然数变量 `x` 的赋值会被表示为 `NatCast.natCast x`。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library"
%%%

* [#6496](https://github.com/leanprover/lean4/pull/6496) 为 bv_decide 添加了短路支持，以加速带共享系数的乘法。具体来说，`a * x = b * x` 可以扩展为 `a = b v (a * x = b * x)`。如果 `a = b` 为真，后者会更快，因为此时无需考虑乘法电路即可判断 `a = b`。另一方面，我们仍需要乘法电路，因为由于二补码回绕，`a * x = b * x -> a = b` 并不总是成立。

* [#7141](https://github.com/leanprover/lean4/pull/7141) 泛化了 `cond`，使其归纳动机可以位于 `Sort u` 中，而不只是 `Type u`。

* [#7289](https://github.com/leanprover/lean4/pull/7289) 为 hashmap API 添加了 `getKey_beq`、`getKey_congr` 及其变体。

* [#7319](https://github.com/leanprover/lean4/pull/7319) 继续对齐关于 `Int.ediv/fdiv/tdiv` 的引理，包括补充某些只在部分情形成立、因此在另一些情形“缺失”的引理说明。同时也加入了关于 `emod/fmod/tmod` 的引理。仍然还有后续工作要做。

* [#7338](https://github.com/leanprover/lean4/pull/7338) 为 `Int.neg_inj` 添加了 `@[simp]`。

* [#7341](https://github.com/leanprover/lean4/pull/7341) 为哈希映射添加了一个等价关系以及若干相关引理。

* [#7356](https://github.com/leanprover/lean4/pull/7356) 添加了一些引理，可将带 `pure` 的单子式操作归约为对应的非单子式版本。

* [#7358](https://github.com/leanprover/lean4/pull/7358) 进一步填补了整数除法 API 的空白，并在很大程度上让三种整数除法变体达到对齐。目前仍缺少一些关于 `tdiv` 和 `fdiv` 的不等式引理，不过它们的陈述会相当别扭，所以暂时应该没人会太想念它们。

* [#7378](https://github.com/leanprover/lean4/pull/7378) 添加了 #7368 所需的一些 `Int` 引理。

* [#7380](https://github.com/leanprover/lean4/pull/7380) 将 `DHashMap.Raw.foldRev(M)` 移到 `DHashMap.Raw.Internal`。

* [#7406](https://github.com/leanprover/lean4/pull/7406) 让 `Subsingleton (Squash α)` 的实例适用于 `α : Sort u`。

* [#7418](https://github.com/leanprover/lean4/pull/7418) 重命名了若干哈希映射引理（`get` -> `getElem`），并使用 `m[k]?` 代替 `get? m k`（`get!` 和 `get` 也做了类似调整）。

* [#7432](https://github.com/leanprover/lean4/pull/7432) 在带有整除假设时，添加了 `Nat.add_div` 的一个推论。

* [#7433](https://github.com/leanprover/lean4/pull/7433) 让 `simp` 能够在 `Id` 之外的单子中简化基本 `for` 循环。

* [#7435](https://github.com/leanprover/lean4/pull/7435) 审视并整理了 `Nat` 与 `Int` API，使接口更一致。

* [#7445](https://github.com/leanprover/lean4/pull/7445) 将 `Array.mkEmpty` 重命名为 `emptyWithCapacity`。（`ByteArray` 和 `FloatArray` 也做了类似调整。）

* [#7446](https://github.com/leanprover/lean4/pull/7446) 更倾向于使用 `∅`，而不是 `.empty` 函数。之后我们也许会重命名 `.empty` 函数，以避免与 `EmptyCollection` 发生命名冲突，并更准确表达那些接受可选容量参数的函数语义。

* [#7451](https://github.com/leanprover/lean4/pull/7451) 将 `LawfulSingleton` 类型类中的成员 `insert_emptyc_eq` 重命名为 `insert_empty_eq`，以符合 `∅` 推荐拼写为 `empty` 的约定。

* [#7466](https://github.com/leanprover/lean4/pull/7466) 进一步清理了 `Int` 的 simp 引理。

* [#7516](https://github.com/leanprover/lean4/pull/7516) 调整了 `List.modify` 和 `List.insertIdx` 的参数顺序，使其与 `Array` 保持一致。

* [#7522](https://github.com/leanprover/lean4/pull/7522) 将 #7484 所需的 `Nat`、`Fin` 和 `BitVec` 理论拆分出来单独提交。

* [#7529](https://github.com/leanprover/lean4/pull/7529) 将 `bind_congr` 从 Mathlib 上游同步过来，并证明有序列表的最小值就是其表头，同时弱化了 `min?_eq_some_iff` 的反对称性条件。`min?_eq_some_iff` 现在不再要求 `Std.Antisymm` 实例，而只需要一个证明，说明该关系在 *列表元素上* 是反对称的。如果省略这个新前提，自动参数会尝试从 `Std.Antisymm` 推导，因此该定理的现有用法大多仍可继续工作。

* [#7541](https://github.com/leanprover/lean4/pull/7541) 更正了一批引理名称，其中不正确的名称是由 @Rob23oba 编写的一个[工具](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/automatic.20spelling.20generation.20.26.20comparison/near/505760384)自动识别出来的。

* [#7554](https://github.com/leanprover/lean4/pull/7554) 按照 [SMTLIB 标准](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2)，为 `BitVec` 添加了用于检测溢出的 SMT-LIB 运算符 `BitVec.negOverflow`，并添加了证明其定义与 `BitVec` 库函数（`negOverflow_eq`）等价的定理。

* [#7558](https://github.com/leanprover/lean4/pull/7558) 修改了 `Nat.div` 和 `Nat.mod` 的定义，改用基于 fuel 的结构递归实现，而非良基递归。这样会让内核中的归约行为更加可预测。

* [#7565](https://github.com/leanprover/lean4/pull/7565) 添加了 `BitVec.toInt_sdiv`，以及围绕除法的大量相关位向量理论。

* [#7614](https://github.com/leanprover/lean4/pull/7614) 将 `Nat.div` 和 `Nat.modCore` 标记为 `irreducible`，以恢复 #7558 之前的行为。

* [#7672](https://github.com/leanprover/lean4/pull/7672) 审查了 List/Array/Vector 中参数的隐式性，整体上尽量在可能时将参数设为隐式；同时也修正了某些本应显式却被错误设为隐式的命题参数。

* [#7687](https://github.com/leanprover/lean4/pull/7687) 为多种类型提供了 `Inhabited`、`Ord`（若缺失）、`TransOrd`、`LawfulEqOrd` 和 `LawfulBEqOrd` 实例，包括 `Bool`、`String`、`Nat`、`Int`、`UIntX`、`Option`、`Prod` 以及日期/时间类型。它还添加了一些相关定理，尤其是关于 `Int` 的 `Ord` 实例如何与 `LE` 和 `LT` 关联。

* [#7692](https://github.com/leanprover/lean4/pull/7692) 将少量关于 `Fin` 的顺序引理从 mathlib 上游同步过来。

* [#7700](https://github.com/leanprover/lean4/pull/7700) 为 `IntX`、`Ordering`、`BitVec`、`Array`、`List` 和 `Vector` 提供了诸如 `TransOrd` 之类与 `Ord` 相关的实例。

* [#7704](https://github.com/leanprover/lean4/pull/7704) 添加了关于有符号有界整数上定义的取模运算的引理。

* [#7706](https://github.com/leanprover/lean4/pull/7706) 对 `Init/Data/UInt/*` 和 `Init/Data/SInt/*` 进行了多项清理。

* [#7729](https://github.com/leanprover/lean4/pull/7729) 用 `assertBEq` 取代 `assert!`，以修复断言位于独立任务中时不会触发 `ctest` 的问题。这是因为 panic 不会在任务中被捕获，而若通过 `block` 函数处理，IO 错误则会由 `AsyncTask` 处理。

* [#7756](https://github.com/leanprover/lean4/pull/7756) 添加了关于 `Nat.gcd` 的引理（其中一些目前已经存在于 mathlib 中）。

  **破坏性变更：** 虽然许多引理只是改名，而旧签名的引理也仅仅被弃用，但也有一些引理在未改名的情况下被更改。它们现在使用 `getElem` 变体，而不是 `get`。

### 异步
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library--Async"
%%%

* [#6683](https://github.com/leanprover/lean4/pull/6683) 使用 LibUV 引入了 TCP socket 支持，从而支持基于它的异步 I/O 操作。

* [#7571](https://github.com/leanprover/lean4/pull/7571) 通过将解析中 `number` 说明符从 `atLeast size` 改为 `flexible size`，修复了 #7478。该改动允许：
  - 重复次数为 1 时接受 1 个或更多字符
  - 重复次数大于 1 时要求恰好那么多个字符

* [#7574](https://github.com/leanprover/lean4/pull/7574) 使用 LibUV 引入了 UDP socket 支持，从而支持基于它的异步 I/O 操作。

* [#7578](https://github.com/leanprover/lean4/pull/7578) 引入了名为 `interfaceAddresses` 的函数，用于获取系统网络接口数组。

* [#7584](https://github.com/leanprover/lean4/pull/7584) 引入了名为 `FormatConfig` 的结构，它为 `GenericFormat` 提供了额外配置选项，例如解析时是否允许闰秒。默认情况下，该选项设为 `false`。

* [#7751](https://github.com/leanprover/lean4/pull/7751) 添加了 `Std.BaseMutex.tryLock` 和 `Std.Mutex.tryAtomically`，并为我们的锁与条件变量原语补上了单元测试。

* [#7755](https://github.com/leanprover/lean4/pull/7755) 添加了 `Std.RecursiveMutex`，作为 `Std.Mutex` 的递归/可重入等价物。

* [#7771](https://github.com/leanprover/lean4/pull/7771) 添加了屏障原语 `Std.Barrier`。

### 有限类型
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library--Finite-Types"
%%%

* [#7228](https://github.com/leanprover/lean4/pull/7228) 添加了用于化简含 `IntX` 表达式的 simproc。

* [#7274](https://github.com/leanprover/lean4/pull/7274) 添加了关于有限类型之间迭代转换的引理，这些转换从某个 `IntX` 类型的值开始。

* [#7340](https://github.com/leanprover/lean4/pull/7340) 添加了关于有限类型之间迭代转换的引理，这些转换从 `Nat`/`Int`/`Fin`/`BitVec` 开始，然后经过 `UIntX`。

* [#7368](https://github.com/leanprover/lean4/pull/7368) 添加了关于有限类型之间迭代转换的引理，这些转换从 `Nat`/`Int`/`Fin`/`BitVec` 开始，并经过 `IntX`。

* [#7414](https://github.com/leanprover/lean4/pull/7414) 补上了剩余关于有限类型迭代转换的引理，这些转换经过有符号或无符号有界整数。

* [#7484](https://github.com/leanprover/lean4/pull/7484) 添加了一些关于 `UIntX` 上定义运算的引理。

* [#7487](https://github.com/leanprover/lean4/pull/7487) 添加了实例 `Neg UInt8`。

* [#7592](https://github.com/leanprover/lean4/pull/7592) 添加了关于有符号有限整数的理论，涉及运算与转换函数之间的关系。

* [#7598](https://github.com/leanprover/lean4/pull/7598) 添加了若干关于 `Nat` 和 `BitVec` 的杂项结果，它们将被用于 `IntX` 理论（#7592）。

* [#7685](https://github.com/leanprover/lean4/pull/7685) 包含从 #7592 拆分出来的补充材料，涉及 `BitVec` 与 `Int`。

* [#7694](https://github.com/leanprover/lean4/pull/7694) 包含从 #7592 拆分出来的补充材料，涉及 `BitVec`、`Int` 和 `Nat`。

### 树映射
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library--Tree-Map"
%%%

* [#7270](https://github.com/leanprover/lean4/pull/7270) 为树映射函数 `foldlM`、`foldl`、`foldrM` 和 `foldr` 及其与其他已有引理支持函数之间的相互作用提供了引理。此外，它还将 `fold*`/`keys` 引理泛化到任意树映射；此前这些引理只针对 `DTreeMap α Unit` 的情形陈述。

* [#7331](https://github.com/leanprover/lean4/pull/7331) 为树映射函数 `insertMany` 及其与其他已有引理支持函数之间的相互作用提供了引理。与 `insertMany` 相关的大多数 `ofList` 引理尚未包含。

* [#7360](https://github.com/leanprover/lean4/pull/7360) 为树映射函数 `ofList` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7367](https://github.com/leanprover/lean4/pull/7367) 为树映射函数 `alter` 和 `modify` 及其与其他已有引理支持函数之间的相互作用提供了引理。

  **破坏性变更：** 所有四种哈希映射类型中 `size_alter` 的签名都已修正。我们现在不再在 if 语句中依赖布尔操作 `contains` 和 `&&`，而是改用基于 `Prop` 的 `Membership` 和 `And`。

* [#7412](https://github.com/leanprover/lean4/pull/7412) 为树映射补充了在 #7289 中为哈希映射引入的那些引理。

* [#7419](https://github.com/leanprover/lean4/pull/7419) 为树映射函数 `modify` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7437](https://github.com/leanprover/lean4/pull/7437) 为树映射函数 `minKey?` 提供了部分（但并非全部）引理。

* [#7556](https://github.com/leanprover/lean4/pull/7556) 为树映射函数 `minKey?` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7600](https://github.com/leanprover/lean4/pull/7600) 为树映射函数 `minKey!` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7626](https://github.com/leanprover/lean4/pull/7626) 为树映射函数 `minKeyD` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7657](https://github.com/leanprover/lean4/pull/7657) 为树映射函数 `maxKey?` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7660](https://github.com/leanprover/lean4/pull/7660) 为树映射函数 `minKey` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7664](https://github.com/leanprover/lean4/pull/7664) 修复了树映射函数 `maxKey` 和 `maxEntry` 定义中的一个 bug。此外，它还为该函数及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7674](https://github.com/leanprover/lean4/pull/7674) 补上了关于树映射的缺失引理：`minKey*` 各变体返回 `keys` 的表头，`keys` 与 `toList` 是有序的，以及 `getKey* t.minKey?` 等于最小值。

* [#7675](https://github.com/leanprover/lean4/pull/7675) 为树映射函数 `maxKeyD` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7686](https://github.com/leanprover/lean4/pull/7686) 为树映射函数 `maxKey!` 及其与其他已有引理支持函数之间的相互作用提供了引理。

* [#7695](https://github.com/leanprover/lean4/pull/7695) 移除了那些在判别模式头部含有元变量的树映射 simp 引理。

* [#7697](https://github.com/leanprover/lean4/pull/7697) 跟进了 #7695。此前我们从判别模式不佳的树映射引理上移除了 `simp` 属性；在这个 PR 中，我们引入了一些基于 `Ord` 的引理，它们对 simp 更友好。

### `BitVec` API
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library--BitVec-API"
%%%

* [#7104](https://github.com/leanprover/lean4/pull/7104) 添加了 `BitVec.[toNat|toFin|toInt]_[sshiftRight|sshiftRight']` 及带 `of_msb_*` 的变体。同时还加入了 `toInt_zero_length` 和 `toInt_of_zero_length`。为支撑主定理，我们还添加了 `toInt_shiftRight_lt` 和 `le_toInt_shiftRight`，从而可以通过 omega 自动推出主定理。

* [#7225](https://github.com/leanprover/lean4/pull/7225) 包含 `BitVec.(toInt, toFin)_twoPow` 定理，补全了 `BitVec.*_twoPow` 的 API。它还扩展了 `toNat_twoPow` API，加入 `toNat_twoPow_of_le`、`toNat_twoPow_of_lt` 以及 `toNat_twoPow_eq_if`，并将 `msb_twoPow` 提前，因为 `toInt_msb` 的证明会用到它。

* [#7415](https://github.com/leanprover/lean4/pull/7415) 添加了若干关于 `BitVec` 与 `Fin`、`Nat` 相互作用的引理。

* [#7420](https://github.com/leanprover/lean4/pull/7420) 将 `BitVec.toInt_[lt|le]'` 泛化为不再要求 `0 < w`。

* [#7465](https://github.com/leanprover/lean4/pull/7465) 添加了定理：
  ```lean
  theorem lt_allOnes_iff {x : BitVec w} : x < allOnes w ↔ x ≠ allOnes w
  ```
  以简化与 `-1#w` 的比较。它是现有引理
  ```lean
  theorem allOnes_le_iff {x : BitVec w} : allOnes w ≤ x ↔ x = allOnes w
  ```
  的一个推论。

* [#7599](https://github.com/leanprover/lean4/pull/7599) 按照 [SMTLIB 标准](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2)，添加了用于检测溢出的 SMT-LIB 运算符 `BitVec.(usubOverflow, ssubOverflow)`，并添加了证明这些定义与 `BitVec` 库函数 `BittVec.(usubOverflow_eq, ssubOverflow_eq)` 等价的定理。

* [#7604](https://github.com/leanprover/lean4/pull/7604) 添加了将否定推进到其他运算中的位向量定理，遵循 Hacker's Delight 第 2.1 章。

* [#7605](https://github.com/leanprover/lean4/pull/7605) 添加了定理 `BitVec.[(toInt, toFin)_(extractLsb, extractLsb')]`，补全了 `BitVec.(extractLsb, extractLsb')` 的 API。

* [#7616](https://github.com/leanprover/lean4/pull/7616) 引入了 `BitVec.(toInt, toFin)_rotate(Left, Right)`，补全了 `BitVec.rotate(Left, Right)` 的 API。

* [#7658](https://github.com/leanprover/lean4/pull/7658) 引入了 `BitVec.(toFin_signExtend_of_le, toFin_signExtend)`，补全了 `BitVec.signExtend` 的 API。

* [#7661](https://github.com/leanprover/lean4/pull/7661) 添加了定理 `BitVec.[(toFin, toInt)_setWidth', msb_setWidth'_of_lt, toNat_lt_twoPow_of_le, toInt_setWidth'_of_lt]`，补全了 `BitVec.setWidth'` 的 API。

* [#7699](https://github.com/leanprover/lean4/pull/7699) 添加了 `BitVec.toInt_srem` 引理，将 `BitVec.srem` 与 `Int.tmod` 联系起来。

### Bitwuzla 重写规则
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Library--Bitwuzla-Rewrite-Rules"
%%%

* [#7424](https://github.com/leanprover/lean4/pull/7424) 证明了 Bitwuzla 的规则 [`BV_ZERO_EXTEND_ELIM`](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L4021-L4033)：

  ```lean
  theorem setWidth_eq_append {v : Nat} {x : BitVec v} {w : Nat} (h : v ≤ w) :
      x.setWidth w = ((0#(w - v)) ++ x).cast (by omega) := by
  ```

* [#7426](https://github.com/leanprover/lean4/pull/7426) 加入了 Bitwuzla 的重写规则 [`BV_EXTRACT_FULL`](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L1236-L1253)，它对位爆破器简化基于 `extractLsb'` 的表达式很有用。

* [#7427](https://github.com/leanprover/lean4/pull/7427) 实现了 Bitwuzla 规则 [`BV_CONCAT_EXTRACT`](https://github.com/bitwuzla/bitwuzla/blob/main/src/rewrite/rewrites_bv.cpp#L1146-L1176)。它会被位爆破器用来将相邻的 `extract` 简化为单个 `extract`。

* [#7454](https://github.com/leanprover/lean4/pull/7454) 实现了 Bitwuzla 规则 [BV_SIGN_EXTEND_ELIM](https://github.com/bitwuzla/bitwuzla/blob/main/src/rewrite/rewrites_bv.cpp#L3638-L3663)，它会把 `signExtend x` 重写为适当符号位的 `append`，后面再接上 `x` 的位。

* [#7461](https://github.com/leanprover/lean4/pull/7461) 在形如 `(a * b) = (c * d)` 的位向量项上引入了一种结合律/交换律规范化，其中 `a, b, c, d` 都是位向量。这与 Bitwuzla 的 `PassNormalize::process` 中的 `PassNormalize::normalize_eq_add_mul` 相对应。

* [#7481](https://github.com/leanprover/lean4/pull/7481) 实现了 Bitwuzla 的重写 [BV_ADD_NEG_MUL]()，并添加了相关引理以简化证明流程。即 ```bvneg (bvadd a (bvmul a b)) = (bvmul a (bvnot b))```，用 Lean 表示为：

  ```lean
  theorem neg_add_mul_eq_mul_not {x y : BitVec w} :
      - (x + x * y) = (x * ~~~ y)
  ```

* [#7482](https://github.com/leanprover/lean4/pull/7482) 实现了 Bitwuzla 中的 [BV_EXTRACT_CONCAT](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L1264) 规则，说明如何从 append 中提取位。我们首先证明了一个带完整分类讨论的“主定理”，然后由它快速推出所需的 `BV_EXTRACT_CONCAT` 定理：

  ```lean
  theorem extractLsb'_append_eq_ite {v w} {xhi : BitVec v} {xlo : BitVec w} {start len : Nat} :
      extractLsb' start len (xhi ++ xlo) =
      if hstart : start < w
      then
        if hlen : start + len < w
        then extractLsb' start len xlo
        else
          (((extractLsb' (start - w) (len - (w - start)) xhi) ++
              extractLsb' start (w - start) xlo)).cast (by omega)
      else
        extractLsb' (start - w) len xhi

* [#7493](https://github.com/leanprover/lean4/pull/7493) 实现了 Bitwuzla 的重写规则 [NORM_BV_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv_norm.cpp#L19-L23)，并添加了相关引理以便高效重写：

  ```lean
  theorem neg_add_mul_eq_mul_not {x y : BitVec w} : - (x + x * y) = x * ~~~ y
  ```

* [#7508](https://github.com/leanprover/lean4/pull/7508) 证明了取负与左移可交换，这对应 Bitwuzla 的重写 [NORM_BV_SHL_NEG](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv_norm.cpp#L142-L148)。

* [#7594](https://github.com/leanprover/lean4/pull/7594) 实现了 Bitwuzla 的重写 [BV_EXTRACT_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510)，说明当 `i >= len` 时，高位不会影响乘积在 `len` 以内的位。

* [#7595](https://github.com/leanprover/lean4/pull/7595) 实现了来自 Bitwuzla 重写 [BV_EXTRACT_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510) 的加法重写，说明当 `i >= len` 时，高位不会影响和在 `len` 以内的位：

  ```lean
  theorem extractLsb'_add {w len} {x y : BitVec w} (hlen : len ≤ w) :
      (x + y).extractLsb' 0 len = x.extractLsb' 0 len + y.extractLsb' 0 len
  ```

* [#7757](https://github.com/leanprover/lean4/pull/7757) 添加了 Bitwuzla 重写 `NORM_BV_ADD_CONCAT`，用于对 append 上的加法做符号化简。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Compiler"
%%%

* [#7398](https://github.com/leanprover/lean4/pull/7398) 修复了旧代码生成器 cce（Common Case Elimination）阶段中的一个作用域错误。该阶段先前会为公共的次要前提创建连接点，即使其中一些前提位于局部定义函数的函数体中，结果导致对连接点的引用作用域不正确。修复方式是在访问 lambda 时保存/恢复候选项。

* [#7710](https://github.com/leanprover/lean4/pull/7710) 改进了 Lean 的内存使用情况，尤其是对长时间运行的服务器进程，最多可降低 60%。

## 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Pretty-Printing"
%%%

* [#7589](https://github.com/leanprover/lean4/pull/7589) 修改了结构体实例记法的美观打印器：如果某个字段的值与该字段默认值在定义上相等（在可约透明度范围内），则该字段会被省略。将 `pp.structureInstances.defaults` 设为 true，可强制仍然打印这类字段。

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Documentation"
%%%

* [#7198](https://github.com/leanprover/lean4/pull/7198) 让 `Char` 命名空间中的文档字符串符合文档约定。

* [#7204](https://github.com/leanprover/lean4/pull/7204) 为 `Id` 单子添加了文档字符串。

* [#7246](https://github.com/leanprover/lean4/pull/7246) 更新了现有 Bool 文档字符串，并补上了缺失的部分。

* [#7288](https://github.com/leanprover/lean4/pull/7288) 修复了 `List.removeAll` 的文档。

* [#7365](https://github.com/leanprover/lean4/pull/7365) 更新了一些文档字符串，并补充了若干缺失项。

* [#7452](https://github.com/leanprover/lean4/pull/7452) 让所有出现在语言参考中的 `List` 文档字符串风格保持一致。

* [#7476](https://github.com/leanprover/lean4/pull/7476) 为 `IO` 及相关代码补上缺失的文档字符串，并统一现有文档字符串的风格。

* [#7492](https://github.com/leanprover/lean4/pull/7492) 为 `Array` 补上缺失的文档字符串，并统一其风格。

* [#7506](https://github.com/leanprover/lean4/pull/7506) 为 `String` 补上缺失的文档字符串，并统一现有文档字符串的风格。

* [#7523](https://github.com/leanprover/lean4/pull/7523) 为 `System` 和 `System.FilePath` 补上缺失文档字符串，并统一文档字符串风格。

* [#7528](https://github.com/leanprover/lean4/pull/7528) 让 `Thunk` 的文档字符串与其他部分的风格保持一致。

* [#7534](https://github.com/leanprover/lean4/pull/7534) 为与 `Syntax` 相关的内容补上缺失文档字符串，并让现有文档字符串的风格与其他部分保持一致。

* [#7535](https://github.com/leanprover/lean4/pull/7535) 修订了 `funext` 的文档字符串，使其更简洁，并添加了指向手册的引用以供查看更多细节。

* [#7548](https://github.com/leanprover/lean4/pull/7548) 为单子变换器补上缺失文档字符串，并统一其风格。

* [#7552](https://github.com/leanprover/lean4/pull/7552) 为 `Nat` 补上缺失文档字符串，并统一其风格。

* [#7564](https://github.com/leanprover/lean4/pull/7564) 更新了 `ULift` 和 `PLift` 的文档字符串，使其风格与其他部分保持一致。

* [#7568](https://github.com/leanprover/lean4/pull/7568) 为 `Int` 补上缺失文档字符串，并统一它们的风格。

* [#7602](https://github.com/leanprover/lean4/pull/7602) 为定宽整数操作补上缺失文档字符串，并统一其风格。

* [#7607](https://github.com/leanprover/lean4/pull/7607) 为 `String.drop` 和 `String.dropRight` 添加了文档字符串。

* [#7613](https://github.com/leanprover/lean4/pull/7613) 为手册中出现的一批名称添加了文档字符串。

* [#7635](https://github.com/leanprover/lean4/pull/7635) 为 `Substring` 补上缺失文档字符串，并统一 `Substring` 文档字符串的风格。

* [#7642](https://github.com/leanprover/lean4/pull/7642) 审查了 `Float` 和 `Float32` 的文档字符串，补上缺失项并统一其格式。

* [#7645](https://github.com/leanprover/lean4/pull/7645) 为 `ForM`、`ForIn`、`ForIn'`、`ForInStep`、`IntCast` 和 `NatCast` 补上缺失文档字符串，并统一文档字符串风格。

* [#7711](https://github.com/leanprover/lean4/pull/7711) 补上了手册中出现的最后几条缺失文档字符串。

* [#7713](https://github.com/leanprover/lean4/pull/7713) 让 BitVec 文档字符串彼此之间以及与其余 API 的风格保持一致。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Server"
%%%

* [#7178](https://github.com/leanprover/lean4/pull/7178) 修复了语言服务器中的一个竞争条件：在编辑文件头部时，它有时会丢弃请求并永远不作回应。这会导致 VS Code 中的语义高亮停止工作，因为一旦先前请求被丢弃，VS Code 就会停止继续发送请求；同时也会使 InfoView 出现异常。导入自动补全也会因此显得有些怪异，因为这些请求有时也会被丢弃。这个竞争条件自 2020 年语言服务器第一版以来就一直存在。

* [#7223](https://github.com/leanprover/lean4/pull/7223) 实现了看门狗请求处理的并行化，因此由看门狗处理的请求再也不会阻塞看门狗的主线程。

* [#7240](https://github.com/leanprover/lean4/pull/7240) 为链接到语言参考中的章节添加了规范语法，并按照文档字符串风格指南对文档字符串中的示例进行格式化。

* [#7343](https://github.com/leanprover/lean4/pull/7343) 缓解了这样一个问题：在 VS Code 中双击插入嵌入提示时，紧接一次编辑之后该嵌入提示可能被插入到错误位置。

* [#7344](https://github.com/leanprover/lean4/pull/7344) 将自动隐式嵌入提示的工具提示合并为单个工具提示。这是为了绕过 VS Code 中的一个问题：当鼠标移动到相邻嵌入提示部分时，VS Code 无法正确更新其悬停提示。

* [#7346](https://github.com/leanprover/lean4/pull/7346) 修复了这样一个问题：当删除一个仍在语言服务器中打开的文件时，语言服务器会触发嵌入提示断言违规。

* [#7366](https://github.com/leanprover/lean4/pull/7366) 在服务端加入了对专门的 “unsolved goals” 和 “goals accomplished” 诊断的支持，Lean 4 VS Code 扩展会对它们提供专门支持。特殊的 “unsolved goals” 诊断改编自 “unsolved goals” 错误诊断；而当某个 `theorem` 或类型为 `Prop` 的 `example` 不再含有错误或 `sorry` 时，就会发出 “goals accomplished” 诊断。Lean 4 VS Code 扩展的配套 PR 位于 leanprover/vscode-lean4#585。

* [#7376](https://github.com/leanprover/lean4/pull/7376) 确保 `weak` 选项不必同时在 Lake 的 `leanOptions` 和 `moreServerOptions` 中重复填写。

* [#7882](https://github.com/leanprover/lean4/pull/7882) 修复了一个回归：当文档发生变化时，先前版本文档的精化不会被取消。

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Lake"
%%%

* [#7185](https://github.com/leanprover/lean4/pull/7185) 重构了 Lake 的构建内部机制，以便引入超出包、模块和库范畴的目标与构面。构面、构建键、构建信息和 CLI 命令都被泛化到了任意目标类型。

* [#7393](https://github.com/leanprover/lean4/pull/7393) 为 Lean DSL 中的 Lake 配置字段添加了自动补全支持：当光标位于某个现有字段之后的缩进空白处时可以触发。目前，如果完全没有任何字段，仍不支持自动补全。

  **破坏性变更：** 非标准的大括号配置语法现在使用分号 `;` 而不是逗号 `,` 作为分隔符。缩进仍然可以作为分隔符的替代方案。

* [#7399](https://github.com/leanprover/lean4/pull/7399) 将 Lake 中新的内建 initializer、elaborator 和 macro 回退为非内建实现。

* [#7504](https://github.com/leanprover/lean4/pull/7504) 扩充了 Lake 配置数据结构声明（如 `PackageConfig`、`LeanLibConfig`），使其生成额外元数据，随后通过元程序自动生成 Lean 与 TOML 的编码器和解码器。

* [#7543](https://github.com/leanprover/lean4/pull/7543) 将动态目标、外部库、Lean 库和 Lean 可执行文件的配置声明统一为单一数据类型，并存放在包内部的统一映射中。

  **破坏性变更：** 用户现在不能再定义多个名称相同但种类不同的目标（例如同时定义一个名为 `foo` 的 Lean 可执行文件和一个名为 `foo` 的 Lean 库）。这应当不会影响大多数用户，因为 Lake DSL 原本就不鼓励这样做。

* [#7576](https://github.com/leanprover/lean4/pull/7576) 修改了 Lake：在 Windows 上构建可执行文件和库（静态库与共享库）时，会生成并使用响应文件。这是为了避免可能超过 Windows 命令行长度限制。

* [#7586](https://github.com/leanprover/lean4/pull/7586) 修改了 Lean 库的 `static.export` 构面，使其生成精简静态库。

* [#7608](https://github.com/leanprover/lean4/pull/7608) 移除了 Lake 构建和配置文件中对 Lake 插件的使用。

* [#7667](https://github.com/leanprover/lean4/pull/7667) 修改了 Lake 记录 Lean 配置消息的方式，使其与记录 Lean 构建消息的方式一致。这样例如就去除了冗余的严重级别标题。

* [#7703](https://github.com/leanprover/lean4/pull/7703) 添加了 `input_file` 和 `input_dir` 两种新目标类型，同时为 Lean 库和可执行文件添加了 `needs` 配置项。该选项泛化了 `extraDepTargets`（它未来将被弃用），从而为跨包和跨目标类型边界声明依赖提供了更丰富的支持。

* [#7716](https://github.com/leanprover/lean4/pull/7716) 为 Lean 包、库和可执行文件添加了 `moreLinkObjs` 与 `moreLinkLibs` 选项。它们作为 `extern_lib` 的功能性替代，同时提供了更大的灵活性。

  **破坏性变更：** `precompileModules` 现在只会单独加载当前库的模块。其他库的模块将通过该库的共享库一起加载。

* [#7732](https://github.com/leanprover/lean4/pull/7732) 弃用了 `extraDepTargets`，并修复了由配置重构引发的一个 bug。

* [#7758](https://github.com/leanprover/lean4/pull/7758) 从 FFI 示例中移除了额外的链接参数 `-lstdcpp`。事实上并不需要它。

* [#7763](https://github.com/leanprover/lean4/pull/7763) 更正了构建键获取逻辑，使其能够生成具有正确数据种类的作业，并修复了从键字面量到目标的一次失败强制转换。

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___19___0-_LPAR_2025-05-01_RPAR_--Other"
%%%

* [#7326](https://github.com/leanprover/lean4/pull/7326) 更新了发布说明脚本，以更好地缩进 PR 描述。

* [#7453](https://github.com/leanprover/lean4/pull/7453) 在内核级应用类型不匹配错误的消息中加入了 “(kernel)”。

* [#7769](https://github.com/leanprover/lean4/pull/7769) 修复了发布自动化脚本中的若干 bug，新增了一个将 tag 合并到远端 `stable` 分支的脚本，并让主 `release_checklist.py` 脚本在需要时提示调用 `merge_remote.py` 与 `release_steps.py`。


````
