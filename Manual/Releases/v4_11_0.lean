/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.11.0 (2024-09-02)" =>
%%%
tag := "release-v4.11.0"
file := "v4.11.0"
%%%

````markdown
````
# 语言特性、策略与元程序
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Language-features___-tactics___-and-metaprograms"
%%%

````markdown

* 变量引入机制已经改变。和以前一样，当某个定义引用了变量时，Lean 会将该变量作为定义的参数加入；但现在在定理体中，不再根据使用情况自动引入变量，以确保对证明的修改不会改变整个定理的陈述。取而代之的是，只有当变量出现在定理头部、出现在 **`include` 命令** 中，或者是仅依赖这些变量的实例隐式参数时，它们才会在证明中可用。可以使用 **`omit` 命令** 省略已引入的变量。

  见下方的破坏性变更。

  PR：[#4883](https://github.com/leanprover/lean4/pull/4883)、[#4814](https://github.com/leanprover/lean4/pull/4814)、[#5000](https://github.com/leanprover/lean4/pull/5000)、[#5036](https://github.com/leanprover/lean4/pull/5036)、[#5138](https://github.com/leanprover/lean4/pull/5138)、[0edf1b](https://github.com/leanprover/lean4/commit/0edf1bac392f7e2fe0266b28b51c498306363a84)。

* **递归定义**
  * 现在可以显式请求结构化递归，写法如下：
    ```
    termination_by structural x
    ```
    这与现有的 `termination_by x` 语法相对应，后者会使用良基递归。
    [#4542](https://github.com/leanprover/lean4/pull/4542)
  * [#4672](https://github.com/leanprover/lean4/pull/4672) 修复了一个可能导致病态类型项的 bug。
  * `termination_by?` 语法不再强制使用良基递归；当推断出结构化递归时，它会使用 `termination_by structural` 语法打印结果。
  * 现在支持**互相结构化递归**。该特性既支持在非互递归数据类型上做互递归，也支持对互递归或嵌套数据类型进行递归：

    ```lean
    mutual
    def Even : Nat → Prop
      | 0 => True
      | n+1 => Odd n

    def Odd : Nat → Prop
      | 0 => False
      | n+1 => Even n
    end

    mutual
    inductive A
    | other : B → A
    | empty
    inductive B
    | other : A → B
    | empty
    end

    mutual
    def A.size : A → Nat
    | .other b => b.size + 1
    | .empty => 0

    def B.size : B → Nat
    | .other a => a.size + 1
    | .empty => 0
    end

    inductive Tree where | node : List Tree → Tree

    mutual
    def Tree.size : Tree → Nat
    | node ts => Tree.list_size ts

    def Tree.list_size : List Tree → Nat
    | [] => 0
    | t::ts => Tree.size t + Tree.list_size ts
    end
    ```

    这些函数也会生成函数式归纳原理（`A.size.induct`、`A.size.mutual_induct`）。

    目前仍不支持嵌套结构化递归。

    PR：[#4639](https://github.com/leanprover/lean4/pull/4639)、[#4715](https://github.com/leanprover/lean4/pull/4715)、[#4642](https://github.com/leanprover/lean4/pull/4642)、[#4656](https://github.com/leanprover/lean4/pull/4656)、[#4684](https://github.com/leanprover/lean4/pull/4684)、[#4715](https://github.com/leanprover/lean4/pull/4715)、[#4728](https://github.com/leanprover/lean4/pull/4728)、[#4575](https://github.com/leanprover/lean4/pull/4575)、[#4731](https://github.com/leanprover/lean4/pull/4731)、[#4658](https://github.com/leanprover/lean4/pull/4658)、[#4734](https://github.com/leanprover/lean4/pull/4734)、[#4738](https://github.com/leanprover/lean4/pull/4738)、[#4718](https://github.com/leanprover/lean4/pull/4718)、[#4733](https://github.com/leanprover/lean4/pull/4733)、[#4787](https://github.com/leanprover/lean4/pull/4787)、[#4788](https://github.com/leanprover/lean4/pull/4788)、[#4789](https://github.com/leanprover/lean4/pull/4789)、[#4807](https://github.com/leanprover/lean4/pull/4807)、[#4772](https://github.com/leanprover/lean4/pull/4772)
  * [#4809](https://github.com/leanprover/lean4/pull/4809) 让不必要的 `termination_by` 子句产生警告而不是错误。
  * [#4831](https://github.com/leanprover/lean4/pull/4831) 改进了通过非递归类型进行嵌套结构化递归的处理。
  * [#4839](https://github.com/leanprover/lean4/pull/4839) 在存在自反参数时，改进了对归纳谓词进行结构化递归的支持。
* `simp` 策略
  * [#4784](https://github.com/leanprover/lean4/pull/4784) 将配置 `Simp.Config.implicitDefEqProofs` 的默认值设为 `true`。

* `omega` 策略
  * [#4612](https://github.com/leanprover/lean4/pull/4612) 规范化了错误消息中约束出现的顺序。
  * [#4695](https://github.com/leanprover/lean4/pull/4695) 除非能产生非平凡线性组合，否则不再将类型转换推进到乘法中。
  * [#4989](https://github.com/leanprover/lean4/pull/4989) 修复了一个回归。

* `decide` 策略
  * [#4711](https://github.com/leanprover/lean4/pull/4711) 在规约 `Decidable` 实例时，从“默认透明度”切换为“至少默认透明度”。
  * [#4674](https://github.com/leanprover/lean4/pull/4674) 为 `decide` 策略失败提供详细反馈。它会告诉你展开了哪些 `Decidable` 实例；如果卡在 `Eq.rec`，则会提示定义 `Decidable` 实例时避免使用策略；如果卡在 `Classical.choice`，则会提示当前作用域中引入了经典实例。在此过程中，它会处理 `Decidable.rec` 和 match，以把责任定位到没有规约的实例上。

* `@[ext]` attribute
  * [#4543](https://github.com/leanprover/lean4/pull/4543) 和 [#4762](https://github.com/leanprover/lean4/pull/4762) 让 `@[ext]` 能从用户自定义的 `ext` 定理生成 `ext_iff` 定理。同时修复了该 attribute，使 `@[local ext]` 和 `@[scoped ext]` 可用。可以使用 `@[ext (iff := false)]` 关闭 `ext_iff` 生成。
  * [#4694](https://github.com/leanprover/lean4/pull/4694) 让生成的引理支持“跳转到定义”。同时调整了核心库以利用 `ext_iff` 生成。
  * [#4710](https://github.com/leanprover/lean4/pull/4710) 让 `ext_iff` 定理保留实例隐式 binder 的类型，而不是把所有 binder 类型都变成隐式。

* `#eval` 命令
  * [#4810](https://github.com/leanprover/lean4/pull/4810) 引入了一个更安全的 `#eval` 命令，防止求值包含 `sorry` 的项。其动机在于：失败的策略配合数组访问等操作可能导致 Lean 进程崩溃。用户可以使用新的 `#eval!` 命令来恢复之前的不安全行为。（[#4829](https://github.com/leanprover/lean4/pull/4829) 对一个测试做了调整。）

* [#4447](https://github.com/leanprover/lean4/pull/4447) 添加了 `#discr_tree_key` 和 `#discr_tree_simp_key` 命令，用于辅助调试 discrimination tree 失败。`#discr_tree_key t` 会打印项 `t` 的 discrimination tree 键（如果它只是一个标识符，则打印该常量的类型）。它使用默认配置来生成键。`#discr_tree_simp_key` 与 `#discr_tree_key` 类似，但会将底层类型视作 simp 引理的类型，也就是说它会把该类型变换为一个等式，并生成其左侧的键。

  例如，
  ```
  #discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
  -- bar _ (@OfNat.ofNat Nat _ _)

  #discr_tree_simp_key Nat.add_assoc
  -- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
  ```

* [#4741](https://github.com/leanprover/lean4/pull/4741) 修改了选项解析，使其允许从命令行为用户自定义选项赋值。初始选项现在会在导入之后重新解析并验证。带 `weak.` 前缀的命令行选项赋值若去掉前缀后的选项名不存在，则会被静默丢弃。

* **deriving 处理器**
  * [7253ef](https://github.com/leanprover/lean4/commit/7253ef8751f76bcbe0e6f46dcfa8069699a2bac7) 和 [a04f3c](https://github.com/leanprover/lean4/commit/a04f3cab5a9fe2870825af6544ca13c5bb766706) 改进了 `BEq` deriving 处理器的构造过程。
  * [86af04](https://github.com/leanprover/lean4/commit/86af04cc08c0dbbe0e735ea13d16edea3465f850) 让 `BEq` deriving 处理器在存在依赖类型字段时也能工作。
  * [#4826](https://github.com/leanprover/lean4/pull/4826) 重构了 `DecidableEq` deriving 处理器，使其使用 `termination_by structural`。

* **元编程**
  * [#4593](https://github.com/leanprover/lean4/pull/4593) 添加了 `unresolveNameGlobalAvoidingLocals`。
  * [#4618](https://github.com/leanprover/lean4/pull/4618) 删除了 2022 年起已弃用的函数。
  * [#4642](https://github.com/leanprover/lean4/pull/4642) 添加了 `Meta.lambdaBoundedTelescope`。
  * [#4731](https://github.com/leanprover/lean4/pull/4731) 添加了 `Meta.withErasedFVars`，用于进入一个从局部上下文中擦除某些 fvar 的上下文。
  * [#4777](https://github.com/leanprover/lean4/pull/4777) 在 `closeMainGoal` 中加入赋值验证，防止用户绕过 occurs check，例如通过 `exact` 之类的策略。
  * [#4807](https://github.com/leanprover/lean4/pull/4807) 引入了 `Lean.Meta.PProdN` 模块，用于打包和投影嵌套的 `PProd`。
  * [#5170](https://github.com/leanprover/lean4/pull/5170) 修复了 `Syntax.unsetTrailing`。因此，在 `import` 块中最后一个模块名上，“跳转到定义”现在可以正常工作了（问题 [#4958](https://github.com/leanprover/lean4/issues/4958)）。

````
# 语言服务器、组件与 IDE 扩展
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Language-server___-widgets___-and-IDE-extensions"
%%%

````markdown

* [#4727](https://github.com/leanprover/lean4/pull/4727) 让信息视图请求的响应在相关策略执行完成后立刻返回。
* [#4580](https://github.com/leanprover/lean4/pull/4580) 让空白变动不再使导入失效，因此在导入后开始输入第一个声明也不应再触发重新加载。
* [#4780](https://github.com/leanprover/lean4/pull/4780) 修复了一个问题：悬停在未导入的内建名称上可能导致 panic。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Pretty-printing"
%%%

````markdown

* [#4558](https://github.com/leanprover/lean4/pull/4558) 修复了 `pp.instantiateMVars` 设置，并将默认值改为 `true`。
* [#4631](https://github.com/leanprover/lean4/pull/4631) 确保语法节点总会运行自己的格式化器。修复了一个问题：若 `ppSpace` 出现在 `macro` 或 `elab` 命令中，它不会按带空格的形式格式化。
* [#4665](https://github.com/leanprover/lean4/pull/4665) 修复了一个 bug：由于设置了 `pp.tagAppFns`，美观打印的签名（例如在 `#check` 中）此前过于可悬停。
* [#4724](https://github.com/leanprover/lean4/pull/4724) 让 `match` 美观打印器对 `pp.explicit` 敏感，因此在 Infoview 中悬停于 `match` 时会显示底层项。
* [#4764](https://github.com/leanprover/lean4/pull/4764) 记录了为什么匿名构造子记法在美观打印时不会做扁平化。
* [#4786](https://github.com/leanprover/lean4/pull/4786) 调整了加括号器，使只有括号本身可悬停；其实现方式是让括号“窃取”被括起来表达式的项信息。
* [#4854](https://github.com/leanprover/lean4/pull/4854) 允许省略应用末尾任意长的一串可选参数，而此前保守的行为至多只省略一个可选参数。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Library"
%%%

````markdown

* `Nat`
  * [#4597](https://github.com/leanprover/lean4/pull/4597) 添加了按位运算引理 `Nat.and_le_(left|right)`。
  * [#4874](https://github.com/leanprover/lean4/pull/4874) 添加了用于简化位表达式的 simproc。
* `Int`
  * [#4903](https://github.com/leanprover/lean4/pull/4903) 通过将 `HPow Int Nat Int` 合成重写为 `NatPow Int` 实例，修复了其性能问题。
* `UInt*` 与 `Fin`
  * [#4605](https://github.com/leanprover/lean4/pull/4605) 添加了引理。
  * [#4629](https://github.com/leanprover/lean4/pull/4629) 添加了 `*.and_toNat`。
* `Option`
  * [#4599](https://github.com/leanprover/lean4/pull/4599) 添加了 `get` 引理。
  * [#4600](https://github.com/leanprover/lean4/pull/4600) 添加了 `Option.or`，这是一个对第二个参数严格求值的 `Option.orElse` 版本。
* `GetElem`
  * [#4603](https://github.com/leanprover/lean4/pull/4603) 添加了 `getElem_congr`，以帮助重写索引。
* `List` 与 `Array`
  * 从 Batteries 上游合入：[#4586](https://github.com/leanprover/lean4/pull/4586) 上游合入了 `List.attach` 和 `Array.attach`，[#4697](https://github.com/leanprover/lean4/pull/4697) 上游合入了 `List.Subset`、`List.Sublist` 及其 API，[#4706](https://github.com/leanprover/lean4/pull/4706) 上游合入了 `List.Pairwise` 和 `List.Nodup` 的基础内容，[#4720](https://github.com/leanprover/lean4/pull/4720) 上游合入了更多 `List.erase` API，[#4836](https://github.com/leanprover/lean4/pull/4836) 和 [#4837](https://github.com/leanprover/lean4/pull/4837) 上游合入了 `List.IsPrefix`/`List.IsSuffix`/`List.IsInfix` 并添加了 `Decidable` 实例，[#4855](https://github.com/leanprover/lean4/pull/4855) 上游合入了 `List.tail`、`List.findIdx`、`List.indexOf`、`List.countP`、`List.count` 和 `List.range'`，[#4856](https://github.com/leanprover/lean4/pull/4856) 上游合入了更多 List 引理，[#4866](https://github.com/leanprover/lean4/pull/4866) 上游合入了 `List.pairwise_iff_getElem`，[#4865](https://github.com/leanprover/lean4/pull/4865) 上游合入了 `List.eraseIdx` 引理。
  * [#4687](https://github.com/leanprover/lean4/pull/4687) 调整了 `List.replicate` 的 simp 引理和 simproc。
  * [#4704](https://github.com/leanprover/lean4/pull/4704) 添加了 `List.Sublist` 的刻画。
  * [#4707](https://github.com/leanprover/lean4/pull/4707) 为 `List.Pairwise` 和 `List.Nodup` 添加了 simp 范式测试。
  * [#4708](https://github.com/leanprover/lean4/pull/4708) 和 [#4815](https://github.com/leanprover/lean4/pull/4815) 重组了列表 getter 上的引理。
  * [#4765](https://github.com/leanprover/lean4/pull/4765) 为字面量数组访问（如 `#[1,2,3,4,5][2]`）添加了 simproc。
  * [#4790](https://github.com/leanprover/lean4/pull/4790) 移除了 `List.Nodup.eraseP` 的类型类假设。
  * [#4801](https://github.com/leanprover/lean4/pull/4801) 为数组类型添加了高效的 `usize` 函数。
  * [#4820](https://github.com/leanprover/lean4/pull/4820) 将 `List.filterMapM` 改为从左到右执行。
  * [#4835](https://github.com/leanprover/lean4/pull/4835) 补齐并清理了 List API 中的空缺。
  * [#4843](https://github.com/leanprover/lean4/pull/4843)、[#4868](https://github.com/leanprover/lean4/pull/4868) 和 [#4877](https://github.com/leanprover/lean4/pull/4877) 修正了 `List.Subset` 引理。
  * [#4863](https://github.com/leanprover/lean4/pull/4863) 将 `Init.Data.List.Lemmas` 拆分为按函数划分的文件。
  * [#4875](https://github.com/leanprover/lean4/pull/4875) 修复了 `List.take_takeWhile` 的陈述。
  * 引理：[#4602](https://github.com/leanprover/lean4/pull/4602)、[#4627](https://github.com/leanprover/lean4/pull/4627)、[#4678](https://github.com/leanprover/lean4/pull/4678) 针对 `List.head` 和 `list.getLast`，[#4723](https://github.com/leanprover/lean4/pull/4723) 针对 `List.erase`，[#4742](https://github.com/leanprover/lean4/pull/4742)
* `ByteArray`
  * [#4582](https://github.com/leanprover/lean4/pull/4582) 从 `ByteArray.toList` 和 `ByteArray.findIdx?` 中消除了 `partial`。
* `BitVec`
  * [#4568](https://github.com/leanprover/lean4/pull/4568) 添加了用于 bitblasting 乘法的递推定理。
  * [#4571](https://github.com/leanprover/lean4/pull/4571) 添加了 `shiftLeftRec` 引理。
  * [#4872](https://github.com/leanprover/lean4/pull/4872) 添加了 `ushiftRightRec` 及其引理。
  * [#4873](https://github.com/leanprover/lean4/pull/4873) 添加了 `getLsb_replicate`。
* 新增 `Std.HashMap`：
  * [#4583](https://github.com/leanprover/lean4/pull/4583) **添加了 `Std.HashMap`**，作为 `Lean.HashMap` 的经验证替代。命名差异请参见该 PR；不过 [#4725](https://github.com/leanprover/lean4/pull/4725) 已将 `HashMap.remove` 重命名为 `HashMap.erase`。
  * [#4682](https://github.com/leanprover/lean4/pull/4682) 添加了 `Inhabited` 实例。
  * [#4732](https://github.com/leanprover/lean4/pull/4732) 改进了哈希映射引理中 `BEq` 参数的顺序。
  * [#4759](https://github.com/leanprover/lean4/pull/4759) 让引理通过统一来解析实例。
  * [#4771](https://github.com/leanprover/lean4/pull/4771) 记录了应以线性方式使用哈希映射，以避免昂贵拷贝。
  * [#4791](https://github.com/leanprover/lean4/pull/4791) 从哈希映射引理中移除了 `bif`，因为它在实践中不便使用。
  * [#4803](https://github.com/leanprover/lean4/pull/4803) 添加了更多引理。
* `SMap`
  * [#4690](https://github.com/leanprover/lean4/pull/4690) 上游合入了 `SMap.foldM`。
* `BEq`
  * [#4607](https://github.com/leanprover/lean4/pull/4607) 添加了 `PartialEquivBEq`、`ReflBEq`、`EquivBEq` 和 `LawfulHashable` 类。
* `IO`
  * [#4660](https://github.com/leanprover/lean4/pull/4660) 添加了 `IO.Process.Child.tryWait`。
* [#4747](https://github.com/leanprover/lean4/pull/4747)、[#4730](https://github.com/leanprover/lean4/pull/4730) 和 [#4756](https://github.com/leanprover/lean4/pull/4756) 为 `PProd` 添加了 `×'` 语法。还为 `PProd` 和 `MProd` 值添加了反精译器，以便将其美观打印为扁平的尖括号元组。
* **其他修复或改进**
  * [#4604](https://github.com/leanprover/lean4/pull/4604) 添加了关于 cond 的引理。
  * [#4619](https://github.com/leanprover/lean4/pull/4619) 将一些定义改成了定理。
  * [#4616](https://github.com/leanprover/lean4/pull/4616) 修复了一些命名空间重复的名称。
  * [#4620](https://github.com/leanprover/lean4/pull/4620) 修复了被 simpNF linter 标记的 simp 引理。
  * [#4666](https://github.com/leanprover/lean4/pull/4666) 让 `Antisymm` 类成为 `Prop`。
  * [#4621](https://github.com/leanprover/lean4/pull/4621) 清理了 linter 标出的未使用参数。
  * [#4680](https://github.com/leanprover/lean4/pull/4680) 为孤立的 `Init` 模块添加了导入。
  * [#4679](https://github.com/leanprover/lean4/pull/4679) 为孤立的 `Std.Data` 模块添加了导入。
  * [#4688](https://github.com/leanprover/lean4/pull/4688) 添加了 `not_exists` 的正向与反向形式。
  * [#4689](https://github.com/leanprover/lean4/pull/4689) 上游合入了 `eq_iff_true_of_subsingleton`。
  * [#4709](https://github.com/leanprover/lean4/pull/4709) 修复了 `Int` 与 `Float` 中负数 `Repr` 实例的优先级处理。
  * [#4760](https://github.com/leanprover/lean4/pull/4760) 将 `TC`（“transitive closure”）重命名为 `Relation.TransGen`。
  * [#4842](https://github.com/leanprover/lean4/pull/4842) 修复了 `List` 弃用项。
  * [#4852](https://github.com/leanprover/lean4/pull/4852) 上游合入了一些应用于引理的 Mathlib attribute。
  * [93ac63](https://github.com/leanprover/lean4/commit/93ac635a89daa5a8e8ef33ec96b0bcbb5d7ec1ea) 改进了证明。
  * [#4862](https://github.com/leanprover/lean4/pull/4862) 和 [#4878](https://github.com/leanprover/lean4/pull/4878) 泛化了 `PSigma.exists` 的宇宙，并将其重命名为 `Exists.of_psigma_prop`。
  * 拼写修复：[#4737](https://github.com/leanprover/lean4/pull/4737)、[7d2155](https://github.com/leanprover/lean4/commit/7d2155943c67c743409420b4546d47fadf73af1c)
  * 文档：[#4782](https://github.com/leanprover/lean4/pull/4782)、[#4869](https://github.com/leanprover/lean4/pull/4869)、[#4648](https://github.com/leanprover/lean4/pull/4648)

````
# Lean 内部实现
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Lean-internals"
%%%

````markdown
* **精译**
  * [#4596](https://github.com/leanprover/lean4/pull/4596) 在 `unstuckMVar` 过程中强制执行 `isDefEqStuckEx`：如果元变量是在先前层级中创建的，isDefEq 会抛出 stuck defeq 异常。这会带来更好的错误消息，并有助于 `rw` 成功合成实例（见问题 [#2736](https://github.com/leanprover/lean4/issues/2736)）。
  * [#4713](https://github.com/leanprover/lean4/pull/4713) 修复了在存在重载符号时的弃用警告。
  * `elab_as_elim` 算法：
    * [#4722](https://github.com/leanprover/lean4/pull/4722) 增加了对推断出的 motive 是否类型正确的检查。
    * [#4800](https://github.com/leanprover/lean4/pull/4800) 对出现在目标类型中的参数进行参数精译。
    * [#4817](https://github.com/leanprover/lean4/pull/4817) 让该算法正确处理具有显式 motive 参数的消去子。
  * [#4792](https://github.com/leanprover/lean4/pull/4792) 为 `Lean.Parser.Term.namedPattern`（例如 `n@(n' + 1)`）添加了项精译器，以便在非模式匹配上下文中使用时报告错误。
  * [#4818](https://github.com/leanprover/lean4/pull/4818) 让匿名点记法在期望类型是值为 pi 类型的类型同义词时也能工作。
* **类型类推断**
  * [#4646](https://github.com/leanprover/lean4/pull/4646) 改进了 `synthAppInstances`，这是负责为 `rw` 和 `apply` 策略合成实例的函数。它新增了一个合成循环，以处理实例需要按复杂顺序合成的函数。
* **归纳类型**
  * [#4684](https://github.com/leanprover/lean4/pull/4684)（回移植为 [98ee78](https://github.com/leanprover/lean4/commit/98ee789990f91ff5935627787b537911ef8773c4)）将 `InductiveVal` 中的 `isNested : Bool` 字段重构为 `numNested : Nat` 字段。这修改了内核。
* **定义**
  * [#4776](https://github.com/leanprover/lean4/pull/4776) 改进了 `Replacement.apply` 的性能。
  * [#4712](https://github.com/leanprover/lean4/pull/4712) 修复了宇宙较混乱时 `.eq_def` 定理的生成。
  * [#4841](https://github.com/leanprover/lean4/pull/4841) 在为 `IndPredBelow` 转换 `match` 语句时，改进了查找 `T.below x` 假设的成功率。
* **诊断与性能分析**
  * [#4611](https://github.com/leanprover/lean4/pull/4611) 让内核诊断在启用 `diagnostics` 时显示，即使它是唯一的 section 也是如此。
  * [#4753](https://github.com/leanprover/lean4/pull/4753) 添加了缺失的 `profileitM` 函数。
  * [#4754](https://github.com/leanprover/lean4/pull/4754) 添加了 `Lean.Expr.numObjs`，用于计算给定表达式中已分配子表达式的数量，主要用于诊断性能问题。
  * [#4769](https://github.com/leanprover/lean4/pull/4769) 添加了缺失的 `withTraceNode`，以改进 `trace.profiler` 输出。
  * [#4781](https://github.com/leanprover/lean4/pull/4781) 和 [#4882](https://github.com/leanprover/lean4/pull/4882) 让 “use `set_option diagnostics true`” 消息是否出现取决于当前 `diagnostics` 设置。
* **性能**
  * [#4767](https://github.com/leanprover/lean4/pull/4767)、[#4775](https://github.com/leanprover/lean4/pull/4775) 和 [#4887](https://github.com/leanprover/lean4/pull/4887) 添加了 `ShareCommon.shareCommon'` 用于共享公共项。在一个包含 1600 万子项的示例中，它比旧的 `shareCommon` 过程快 20 倍。
  * [#4779](https://github.com/leanprover/lean4/pull/4779) 确保 `Expr.replaceExpr` 在 `Expr` 中保留 DAG 结构。
  * [#4783](https://github.com/leanprover/lean4/pull/4783) 记录了 `Expr.replaceExpr` 中的性能问题。
  * [#4794](https://github.com/leanprover/lean4/pull/4794)、[#4797](https://github.com/leanprover/lean4/pull/4797)、[#4798](https://github.com/leanprover/lean4/pull/4798) 让 `for_each` 使用精确缓存。
  * [#4795](https://github.com/leanprover/lean4/pull/4795) 让 `Expr.find?` 和 `Expr.findExt?` 使用内核实现。
  * [#4799](https://github.com/leanprover/lean4/pull/4799) 让 `Expr.replace` 使用内核实现。
  * [#4871](https://github.com/leanprover/lean4/pull/4871) 让 `Expr.foldConsts` 使用精确缓存。
  * [#4890](https://github.com/leanprover/lean4/pull/4890) 让 `expr_eq_fn` 使用精确缓存。
* **工具**
  * [#4453](https://github.com/leanprover/lean4/pull/4453) 上游合入了 `ToExpr FilePath` 和 `compile_time_search_path%`。
* **模块系统**
  * [#4652](https://github.com/leanprover/lean4/pull/4652) 修复了 `finalizeImport` 中对 `const2ModIdx` 的处理：当声明被重新声明时，它会优先为该声明选择原始模块。
* **内核**
  * [#4637](https://github.com/leanprover/lean4/pull/4637) 添加了检查以防止大 `Nat` 指数运算被求值。精译器规约由 `exponentiation.threshold` 选项控制。
  * [#4683](https://github.com/leanprover/lean4/pull/4683) 更新了 `kernel/declaration.h` 中的注释，确保其反映当前 Lean 4 类型。
  * [#4796](https://github.com/leanprover/lean4/pull/4796) 通过使用带精确缓存的 `replace` 提升了性能。
  * [#4700](https://github.com/leanprover/lean4/pull/4700) 通过修复移动构造函数和移动赋值运算符的实现来提升性能。在某些工作负载中，表达式复制占总运行时间的 10%。见问题 [#4698](https://github.com/leanprover/lean4/issues/4698)。
  * [#4702](https://github.com/leanprover/lean4/pull/4702) 通过避免表达式复制改进了 `replace_rec_fn::apply` 的性能。在某些工作负载中，这些复制约占 `save_result` 时间的 13%。见同一问题。
* **其他修复或改进**
  * [#4590](https://github.com/leanprover/lean4/pull/4590) 修复了若干常量和 `trace.profiler.useHeartbeats` 中的拼写错误。
  * [#4617](https://github.com/leanprover/lean4/pull/4617) 为 `deprecated` attribute 添加了 since 日期。
  * [#4625](https://github.com/leanprover/lean4/pull/4625) 提升了“构造子作为变量”测试的稳健性。
  * [#4740](https://github.com/leanprover/lean4/pull/4740) 用 Zulip 上报的一个好例子扩展了测试。
  * [#4766](https://github.com/leanprover/lean4/pull/4766) 将 `Syntax.hasIdent` 提前，使其能更早使用，并理顺了依赖。
  * [#4881](https://github.com/leanprover/lean4/pull/4881) 拆分出了 `Lean.Language.Lean.Types`。
  * [#4893](https://github.com/leanprover/lean4/pull/4893) 为 `sharecommon` 函数添加了 `LEAN_EXPORT`。
  * 拼写修复：[#4635](https://github.com/leanprover/lean4/pull/4635)、[#4719](https://github.com/leanprover/lean4/pull/4719)、[af40e6](https://github.com/leanprover/lean4/commit/af40e618111581c82fc44de922368a02208b499f)
  * 文档：[#4748](https://github.com/leanprover/lean4/pull/4748)（`Command.Scope`）

````
# 编译器、运行时与 FFI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Compiler___-runtime___-and-FFI"
%%%

````markdown
* [#4661](https://github.com/leanprover/lean4/pull/4661) 将 `Std` 从 `libleanshared` 移到体积小得多的 `libInit_shared`。这修复了 Windows 构建。
* [#4668](https://github.com/leanprover/lean4/pull/4668) 修复了初始化，在 `lean_initialize` 中显式初始化 `Std`。
* [#4746](https://github.com/leanprover/lean4/pull/4746) 调整了 `shouldExport`，排除更多符号以低于 Windows 符号数限制。[#4884](https://github.com/leanprover/lean4/pull/4884) 和 [#4956](https://github.com/leanprover/lean4/pull/4956) 添加了一些例外以支持 Verso。
* [#4778](https://github.com/leanprover/lean4/pull/4778) 添加了 `lean_is_exclusive_obj`（`Lean.isExclusiveUnsafe`）和 `lean_set_external_data`。
* [#4515](https://github.com/leanprover/lean4/pull/4515) 修复了在 Windows 上调用带空格路径程序的问题。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Lake"
%%%

````markdown

* [#4735](https://github.com/leanprover/lean4/pull/4735) 改进了多项与 Git 检出、云端发布以及相关错误处理有关的内容。

  * 出错时，Lake 现在会打印所有顶层日志。顶层日志是 Lake 在作业监视器之外产生的日志（例如克隆依赖时）。
  * 当为某个依赖获取远端时，Lake 现在会强制抓取标签。这可防止因仓库重建已抓取标签而引发潜在错误。
  * Git 错误处理现在提供了更丰富的信息。
  * 内建包 facet `release`、`optRelease`、`extraDep` 现在会像其他 facet 一样显示标题。
  * `afterReleaseSync` 和 `afterReleaseAsync` 现在抓取的是 `optRelease` 而不是 `release`。
  * 新增对可选作业的支持，其失败不会导致整个构建失败。现在 `optRelease` 就是这样的作业。

* [#4608](https://github.com/leanprover/lean4/pull/4608) 在创建新项目时添加了草稿 CI 工作流。
* [#4847](https://github.com/leanprover/lean4/pull/4847) 添加了用于控制日志级别的 CLI 选项。`--log-level=<lv>` 控制 Lake 输出的最低日志级别。例如，`--log-level=error` 只会打印错误（不会打印警告或信息）。同时还添加了类似的 `--fail-level` 选项，用来控制会导致构建失败的最低日志级别。现有的 `--iofail` 和 `--wfail` 分别等价于 `--fail-level=info` 和 `--fail-level=warning`。

* 文档：[#4853](https://github.com/leanprover/lean4/pull/4853)


````
# DevOps/CI
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--DevOps___CI"
%%%

````markdown

* **工作流**
  * [#4531](https://github.com/leanprover/lean4/pull/4531) 让发布触发 `release.lean-lang.org` 的更新。
  * [#4598](https://github.com/leanprover/lean4/pull/4598) 将 `pr-release` 调整到新的 `lakefile.lean` 语法。
  * [#4632](https://github.com/leanprover/lean4/pull/4632) 让 `pr-release` 使用正确的标签名。
  * [#4638](https://github.com/leanprover/lean4/pull/4638) 添加了手动触发 nightly 发布的能力。
  * [#4640](https://github.com/leanprover/lean4/pull/4640) 为 `restart-on-label` CI 添加了更多调试输出。
  * [#4663](https://github.com/leanprover/lean4/pull/4663) 将 `restart-on-label` 的等待时间从 10 秒提高到 30 秒。
  * [#4664](https://github.com/leanprover/lean4/pull/4664) 升级了 `actions/checkout` 和 `actions/upload-artifacts` 的版本。
  * [582d6e](https://github.com/leanprover/lean4/commit/582d6e7f7168e0dc0819099edaace27d913b893e) 升级了 `actions/download-artifact` 的版本。
  * [6d9718](https://github.com/leanprover/lean4/commit/6d971827e253a4dc08cda3cf6524d7f37819eb47) 把被删掉的 `check-stage3` 加了回来。
  * [0768ad](https://github.com/leanprover/lean4/commit/0768ad4eb9020af0777587a25a692d181e857c14) 添加了 Jira 同步（供 FRO 使用）。
  * [#4830](https://github.com/leanprover/lean4/pull/4830) 添加了在 FRO Zulip 上报告 CI 错误的支持。
  * [#4838](https://github.com/leanprover/lean4/pull/4838) 在夜间发布时，为 mathlib4 添加了触发 `nightly_bump_toolchain` 的机制。
  * [abf420](https://github.com/leanprover/lean4/commit/abf4206e9c0fcadf17b6f7933434fd1580175015) 修复了 msys2。
  * [#4895](https://github.com/leanprover/lean4/pull/4895) 弃用了基于 Nix 的构建并移除了交互式组件。偏好 flake 构建的用户应在外部自行维护。
* [#4693](https://github.com/leanprover/lean4/pull/4693)、[#4458](https://github.com/leanprover/lean4/pull/4458) 和 [#4876](https://github.com/leanprover/lean4/pull/4876) 更新了**发布检查清单**。
* [#4669](https://github.com/leanprover/lean4/pull/4669) 修复了每个静态库的 “max dynamic symbols” 指标。
* [#4691](https://github.com/leanprover/lean4/pull/4691) 改进了 `tests/list_simp` 与 Mathlib 重新测试 simp 范式时的兼容性。
* [#4806](https://github.com/leanprover/lean4/pull/4806) 更新了快速入门指南。
* [c02aa9](https://github.com/leanprover/lean4/commit/c02aa98c6a08c3a9b05f68039c071085a4ef70d7) 在贡献指南中记录了**分诊团队**。


````
# 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___11___0-_LPAR_2024-09-02_RPAR_--Breaking-changes"
%%%

````markdown

* 对于由 `@[ext]` 生成的 `ext` 和 `ext_iff` 引理，`x` 和 `y` 这两个项参数现在变为隐式。此外，这两个引理现在受保护。([#4543](https://github.com/leanprover/lean4/pull/4543))

* `trace.profiler.useHearbeats` 现已改为 `trace.profiler.useHeartbeats`。([#4590](https://github.com/leanprover/lean4/pull/4590))

* 结构化递归代码中的一个 bug 修复在某些情况下可能会破坏现有代码：当递归参数类型中的某个参数被绑定在该类型索引之后时，就可能发生。通常可以通过重新排列函数参数来修复。([#4672](https://github.com/leanprover/lean4/pull/4672))

* `List.filterMapM` 现在按从左到右的顺序执行单子动作。([#4820](https://github.com/leanprover/lean4/pull/4820))

* `variable` 命令对 `theorem` 证明的影响已经改变。此类分节变量在证明中是否可访问，现在只取决于定理签名和其他顶层命令，而不再取决于证明本身。这一改变确保：
  * 定理的陈述独立于其证明。换言之，证明的变化不会改变定理陈述。
  * `induction` 之类的策略不会意外引入分节变量。
  * 在未来版本的 Lean 中，证明可以与后续声明并行精译。

  `variable` 对定理头部以及其他类型声明的影响保持不变。

  具体来说，分节变量会在以下情况下被引入：
  * 它们被定理头部直接引用；
  * 它们通过当前分节中的新 `include` 命令被引入，且之后没有在 `omit` 语句中提及；
  * 按照这些规则被引入的任意变量所直接引用的变量，或者
  * 仅引用这些规则所引入变量的实例隐式变量。

  为了迁移，新增了一个选项 `deprecated.oldSectionVars`，可在局部切回旧行为。

````
