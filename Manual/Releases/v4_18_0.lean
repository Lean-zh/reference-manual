/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: investigate why this is needed in the new compiler
set_option maxRecDepth 9900

#doc (Manual) "Lean 4.18.0 (2025-04-02)" =>
%%%
tag := "release-v4.18.0"
file := "v4.18.0"
%%%

````markdown
本次发布共合入 344 项变更。除下文列出的 166 项功能新增和 38 项修复外，还有 13 项重构、10 项文档改进、3 项性能改进、4 项测试套件改进以及 109 项其他变更。

## 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Highlights"
%%%

Lean v4.18 带来了多项令人振奋的新特性：

* 自动隐式参数的嵌入提示

  语言服务器现在会使用嵌入提示显示哪些变量是隐式引入作用域的，以及它们出现在哪里。将鼠标悬停在提示上会显示其类型，双击该提示则会把变量绑定显式插入代码中。

  截图请参见 [#6768](https://github.com/leanprover/lean4/pull/6768/files) 的说明。

  请注意，只有在 `set_option autoImplicit true` 时该特性才可见；这在普通 Lean 项目中是默认设置，但在 mathlib 中不是。

* [#6935](https://github.com/leanprover/lean4/pull/6935) 添加了策略 `expose_names`。它会创建一个新目标，其中的局部上下文被“展开”，从而让每个局部声明都拥有清晰、可访问的名称。如果没有任何局部声明需要重命名，则原目标会保持不变地返回。

  ```lean
  /--
  info: α : Sort u_1
  a b : α
  h_1 : a = b
  h_2 : True
  h_3 : True ∨ False
  h : b = a
  ⊢ b = a
  -/
  #guard_msgs (info) in
  example (a b : α) (h : a = b) (_ : True) (_ : True ∨ False) (h : b = a) : b = a := by
    expose_names
    trace_state
    rw [h]
  ```

  这个策略适合用于自动生成的策略建议，也有助于证明探索。尽管如此，最佳实践仍然是在变量进入作用域时（如 `intro`、`case` 等）就为其命名，而不要在完成、打磨后的证明中使用 `expose_names`。

* [#7069](https://github.com/leanprover/lean4/pull/7069) 添加了 `fun_induction` 和 `fun_cases` 策略，为使用函数归纳原则与函数分类原则提供了更便捷的方式。

  ```lean
  fun_induction foo  x y z
  ```

  会先精化 `foo x y z`，再查找 `foo.induct`，然后本质上执行

  ```lean
  induction z using foo.induct y
  ```

  并在此过程中自动判断哪些参数是普通参数、目标参数或被丢弃的参数。目前这只适用于非互递归函数。

  同样也有基于 `foo.fun_cases` 的 `fun_cases` 策略。

* [#6744](https://github.com/leanprover/lean4/pull/6744) 扩展了良基递归定义的预处理：当递归调用出现在 `List.map` 这类高阶函数的参数中时，它会自动把诸如 `h✝ : x ∈ xs` 这样的假设引入作用域。在很多情况下，这样就不再需要 `List.attach` 之类的函数。

  可以用 `set_option wf.preprocess false` 关闭该特性。

* [#6634](https://github.com/leanprover/lean4/pull/6634) 为 `variable` 命令添加了支持，可将已有变量的绑定器注解在严格隐式和实例隐式之间来回切换。

* [#7100](https://github.com/leanprover/lean4/pull/7100) 修改了 `structure` 语法，使父类型可以命名，例如
  ```lean
  structure S extends toParent : P
  ```
  **破坏性变更：** 语法还调整为结果类型出现在 `extends` 子句之前，例如 `structure S : Prop extends P`。这是为了避免解析歧义，同时这也是结果类型更自然的位置。该改动实现了 RFC [#7099](https://github.com/leanprover/lean4/issues/7099)。

* [#7103](https://github.com/leanprover/lean4/pull/7103) 让 `induction` 策略能够像 `cases` 一样，为泛化目标时使用的假设命名。例如，`induction h : xs.length` 会产生带有 `h : xs.length = 0` 和 `h : xs.length = n + 1` 假设的目标。对于多目标的归纳原则，目标处理也做了轻微调整：过去只要有任一目标不是自由变量，所有目标都会被泛化（从而让自由变量失去与其出现所在局部假设的联系）；现在只会泛化那些不是自由变量的目标。

* [#6869](https://github.com/leanprover/lean4/pull/6869) 添加了 `recommended_spelling` 命令，可用于记录某个记号的推荐拼写（例如在标识符中，`∧` 的推荐拼写是 `and`）。这些信息随后会附加到相应的文档字符串中，便于查阅。

* [#6893](https://github.com/leanprover/lean4/pull/6893) 为前端和服务器添加了插件支持。

* [#7061](https://github.com/leanprover/lean4/pull/7061) 为前提选择工具提供了基础 API，可由下游库实现。但它本身并不实现前提选择！

还有更多内容！请查看下方的 *语言* 一节。

值得一提的是，围绕以下主题已经开展了一系列工作（详见 *语言* 一节中对应的小节）：
- `try?` 策略已基于 `evalAndSuggest` 策略重新实现。`try?` 现在支持引用不可访问的局部名称，并且能给出更复杂的建议，包括使用 `exact?` 与 `fun_induction` 策略。新增了配置项 `-only`、`+missing`、`max:=<num>` 以及 `merge`。
- `bv_decide` 策略获得了多项更新：预处理新增功能，加入了对枚举归纳类型、`IntX` 和 `ISize` 的支持，并改进了 LRAT trimming 的性能。
- 线性整数算术表达式的规范化已经实现并接入 `simp +arith`。 [#7043](https://github.com/leanprover/lean4/pull/7043) 弃用了 `simp_arith`、`simp_arith!`、`simp_all_arith` 和 `simp_all_arith!`，改为推荐使用 `simp +arith`。

重要的库更新包括：

* [#6914](https://github.com/leanprover/lean4/pull/6914) 将有序映射数据结构 `DTreeMap`、`TreeMap`、`TreeSet` 及其 `.Raw` 变体引入标准库。随后的一系列 PR 又为这些数据结构上的操作补充了一批引理。

* [#7255](https://github.com/leanprover/lean4/pull/7255) 修复了 `Min (Option α)` 的定义。这是一次 **破坏性变更**。现在 `none` 被视为最小元素，因此对任意 `x : Option α` 都有 `min none x = min x none = none`。在 nightly-2025-02-27 之前，我们则有 `min none (some x) = min (some x) none = some x`。该 PR 还补充了 `Option` 上 `min`、`max`、`≤` 与 `<` 之间关系的基础引理。

`BitVec` 与定宽整数类型（`IntX`）的验证 API 有显著进展，同时也在持续推进 `List/Array/Vector` API 的对齐工作。关于 `Int.ediv/fdiv/tdiv` 的若干引理也得到了加强。

[#6950](https://github.com/leanprover/lean4/pull/6950) 为标准库新增了[风格指南](https://github.com/leanprover/lean4/blob/master/doc/std/style.md)和[命名约定](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md)。

_这份亮点摘要由 Violetta Sim 贡献。_

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language"
%%%

* [#6634](https://github.com/leanprover/lean4/pull/6634) 为 `variable` 命令添加了支持，可将已有变量的绑定器注解在严格隐式和实例隐式之间来回切换。

* [#6744](https://github.com/leanprover/lean4/pull/6744) 扩展了良基递归定义的预处理；详见上方亮点部分。

* [#6823](https://github.com/leanprover/lean4/pull/6823) 添加了树映射所需的一个内建策略和一个内建属性。该策略 `as_aux_lemma` 通常可用于把一段策略序列生成的证明项包装成单独的辅助引理，以保持证明项较小。在极少数情况下，如果该证明项会在外围项中出现多次，这会很有必要。新属性 `Std.Internal.tree_tac` 仅供内部使用，不应在 `Std` 之外使用。

* [#6853](https://github.com/leanprover/lean4/pull/6853) 为形如 `match _ : e with ...` 的 `match` 表达式添加了匿名等式证明支持。

* [#6869](https://github.com/leanprover/lean4/pull/6869) 添加了 `recommended_spelling` 命令；详见上方亮点部分。

* [#6891](https://github.com/leanprover/lean4/pull/6891) 修改了 `rewrite`/`rw`：如果精化后的引理存在任何即时精化错误（通过 synthetic sorry 的存在来检测），则中止重写。如果问题来自待解决的合成元变量（例如实例合成失败），则仍会继续重写。此改动的目的是避免在引理不存在等情况下出现晦涩的 “tactic 'rewrite' failed, equality or iff proof expected ?m.5” 错误。

* [#6893](https://github.com/leanprover/lean4/pull/6893) 为前端和服务器添加了插件支持。

* [#6935](https://github.com/leanprover/lean4/pull/6935) 添加了 `expose_names` 策略；详见上方亮点部分。

* [#6936](https://github.com/leanprover/lean4/pull/6936) 修复了 `#discr_tree_simp_key` 命令，因为它在 `lhs ≠ rhs` 中只显示 `lhs` 的键，但 `simp` 实际索引的是 `lhs = rhs`。

* [#6939](https://github.com/leanprover/lean4/pull/6939) 为 `inductive` 声明中构造子名称冲突以及 `mutual` 声明中名称冲突的情况添加了错误信息。

* [#6947](https://github.com/leanprover/lean4/pull/6947) 添加了 `binderNameHint` 小工具。它可以在 rewrite 和 simp 规则中尽可能保留用户给出的名称。

  表达式 `binderNameHint v binder e` 被定义为 `e`。

  如果它出现在某个方程右侧，而该方程又被 `rw` 或 `simp` 这类策略应用，并且 `v` 是局部变量、`binder` 是一个（经 beta 约简后）成为绑定器的表达式（即 `fun w => …` 或 `∀ w, …`），那么它会将 `v` 重命名为绑定器中使用的名字，并移除 `binderNameHint`。

  这个小工具的典型用法如下；它确保重写之后局部变量仍然叫 `name`，而不是 `x`：

  ```lean
  theorem all_eq_not_any_not (l : List α) (p : α → Bool) :
      l.all p = !l.any fun x => binderNameHint x p (!p x) := sorry

  example (names : List String) : names.all (fun name => "Waldo".isPrefixOf name) = true := by
    rw [all_eq_not_any_not]
    -- ⊢ (!names.any fun name => !"Waldo".isPrefixOf name) = true
  ```

  这个小工具在方程右侧受到 `simp`、`dsimp` 和 `rw` 支持，但不适用于假设，也不被其他策略支持。

* [#6951](https://github.com/leanprover/lean4/pull/6951) 为 simp 的 trace 消息添加了换行和缩进，使其更易阅读（至少我是这么觉得的）。

* [#6964](https://github.com/leanprover/lean4/pull/6964) 添加了便捷命令 `#info_trees in`，可打印后续命令生成的信息树。它对于调试或学习 `InfoTree` 很有帮助。

* [#7039](https://github.com/leanprover/lean4/pull/7039) 改进了良基定义的预处理，使 `wfParam` 能够穿过 let 表达式传播。

* [#7053](https://github.com/leanprover/lean4/pull/7053) 让 `simp` 在合同规则的假设中也遵循 `binderNameHint`。修复了 #7052。

* [#7055](https://github.com/leanprover/lean4/pull/7055) 改进了数组和向量字面量语法，允许末尾逗号，例如 `#[1, 2, 3,]`。

* [#7061](https://github.com/leanprover/lean4/pull/7061) 为前提选择工具提供了基础 API；详见上方亮点部分。

* [#7078](https://github.com/leanprover/lean4/pull/7078) 为 `Int` 和 `Nat` 的整除谓词实现了 simproc。

* [#7088](https://github.com/leanprover/lean4/pull/7088) 修复了带索引访问记法 `xs[i]` 的行为问题：当 `i` 合法性的证明是在统一过程中填入时，先前的行为不正确。

* [#7090](https://github.com/leanprover/lean4/pull/7090) 会从插件名中去掉 `lib` 前缀和 `_shared` 后缀。它还将大部分 dynlib 处理代码移到了 Lean 中，使这类预处理更加标准化。

* [#7100](https://github.com/leanprover/lean4/pull/7100) 修改了 `structure` 语法；详见上方亮点部分。

* [#7103](https://github.com/leanprover/lean4/pull/7103) 让 `induction` 策略能够为假设命名；详见上方亮点部分。

* [#7119](https://github.com/leanprover/lean4/pull/7119) 让 `trace.profiler` 输出中的检查器名称可以点击。

* [#7191](https://github.com/leanprover/lean4/pull/7191) 修复了无 widget 的多行消息中 “Try this” 建议的缩进，使其在 `#guard_msgs` 输出中显示正确。

* [#7192](https://github.com/leanprover/lean4/pull/7192) 防止 `exact?` 和 `apply?` 建议那些虽然对应正确证明、却无法精化的策略；同时也允许它们在需要时建议使用 `expose_names`。

* [#7200](https://github.com/leanprover/lean4/pull/7200) 允许 `DiscrTree.Key` 的调试形式自动换行。

* [#7213](https://github.com/leanprover/lean4/pull/7213) 在运行时初始化期间调用 `SetConsoleOutputCP(CP_UTF8)`，以便在 Windows 控制台中正确显示 Unicode。这同时影响 Lean 可执行文件本身以及用户可执行文件（包括 Lake）。

* [#7224](https://github.com/leanprover/lean4/pull/7224) 让 `induction … using` 和 `cases … using` 在提供的目标多于相应消去子所期望的数量时给出提示。

* [#7294](https://github.com/leanprover/lean4/pull/7294) 修复了 `Std.Internal.Rat.floor` 和 `Std.Internal.Rat.ceil` 中的错误。

### `try?` 策略更新
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--Updates-to-the-try___-Tactic"
%%%

* [#6961](https://github.com/leanprover/lean4/pull/6961) 添加了辅助策略 `evalAndSuggest`。它将用于重构 `try?`。

* [#6965](https://github.com/leanprover/lean4/pull/6965) 使用新的 `evalAndSuggest` 基础设施重新实现了 `try?` 策略。

* [#6967](https://github.com/leanprover/lean4/pull/6967) 确保 `try?` 能够给出需要引用不可访问局部名称的策略建议。
  示例：
    ```lean
    /--
    info: Try these:
    • · expose_names; induction as, bs_1 using app.induct <;> grind [= app]
    • · expose_names; induction as, bs_1 using app.induct <;> grind only [app]
    -/
    #guard_msgs (info) in
    example : app (app as bs) cs = app as (app bs cs) := by
      have bs := 20 -- shadows `bs` in the target
      try?
    ```

* [#6979](https://github.com/leanprover/lean4/pull/6979) 为 `try?` 增加了更复杂建议的支持。
  示例：
    ```lean
    example (as : List α) (a : α) : concat as a = as ++ [a] := by
      try?
    ```
    建议
    ```
    Try this: · induction as, a using concat.induct
      · rfl
      · simp_all
    ```

* [#6980](https://github.com/leanprover/lean4/pull/6980) 改进了 `try?` 的运行时校验与错误信息，同时简化了实现并移除了不必要的代码。

* [#6981](https://github.com/leanprover/lean4/pull/6981) 为 `try?` 添加了新的配置项。
  - `try? -only` 会省略 `simp only` 和 `grind only` 建议
  - `try? +missing` 会启用部分解，其中某些子目标以 `sorry` “解决”，需要用户手动完成证明
  - `try? (max:=<num>)` 设置生成建议的最大数量（默认值为 8）

* [#6991](https://github.com/leanprover/lean4/pull/6991) 改进了为 `<;>` 组合子生成建议的方式。

* [#6994](https://github.com/leanprover/lean4/pull/6994) 为 `try?` 策略添加了 `Try.Config.merge` 标志（默认值为 `true`）。当其为 `true` 时，`try?` 会将如下建议
  ```lean
  · induction xs, ys using bla.induct
      · grind only [List.length_reverse]
      · grind only [bla]
  ```
  压缩为：
  ```lean
  induction xs, ys using bla.induct <;> grind only [List.length_reverse, bla]
  ```

* [#6995](https://github.com/leanprover/lean4/pull/6995) 在 `try?` 策略中实现了对 `exact?` 的支持。

* [#7082](https://github.com/leanprover/lean4/pull/7082) 让 `try?` 使用 `fun_induction`，而不是 `induction … using foo.induct`。如果没有歧义，它会使用无参数简写 `fun_induction foo`。同时如果没有必要，也会避免先使用 `expose_names`，而是先直接尝试。

### 函数归纳策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--Functional-Induction-Tactic"
%%%

* [#7069](https://github.com/leanprover/lean4/pull/7069) 添加了 `fun_induction` 和 `fun_cases` 策略，它们让使用函数归纳原则和函数分类原则更加方便。

* [#7101](https://github.com/leanprover/lean4/pull/7101) 实现了 `fun_induction foo`，它类似于 `fun_induction foo x y z`，但会从目标中对 `foo` 的唯一合适调用自动选择要使用的参数。

* [#7127](https://github.com/leanprover/lean4/pull/7127) 跟进了 #7103 中 `induction` 泛化行为的变更，以保持 `fun_induction` 与之同步。同时也修复了一个 `Syntax` 索引差一错误。

### `bv_decide` 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--bv_decide-Tactic"
%%%

* [#6741](https://github.com/leanprover/lean4/pull/6741) 为 bv_decide 的预处理器实现了两条规则：将 `|||` 降低为 `&&&`，以便实现更多项共享并应用 `&&&` 相关规则；同时加入形如 `(a &&& b == -1#w) = (a == -1#w && b == -1#w)` 的重写，以保留在这种降级之前已经存在的重写行为。

* [#6924](https://github.com/leanprover/lean4/pull/6924) 将 Bitwuzla 的 EQUAL_ITE 规则加入 bv_decide 的预处理器。

* [#6926](https://github.com/leanprover/lean4/pull/6926) 将 Bitwuzla 的 BV_EQUAL_CONST_NOT 规则加入 bv_decide 的预处理器。

* [#6946](https://github.com/leanprover/lean4/pull/6946) 在 `bv_decide` 中实现了对枚举归纳类型的基础支持。现在它支持枚举归纳变量（以及其他未解释原子）与常量之间的相等性。

* [#7009](https://github.com/leanprover/lean4/pull/7009) 确保用户在尝试使用 `bv_decide` 时，会收到一条说明应导入哪个模块的错误信息。

* [#7019](https://github.com/leanprover/lean4/pull/7019) 正确展开了 bv_decide 中的 trace 节点名称，使其只需开启 `trace.Meta.Tactic.bv` 和 `trace.Meta.Tactic.sat` 即可见，而不再总是需要启用 profiler。

* [#7021](https://github.com/leanprover/lean4/pull/7021) 向 bv_decide 的预处理器中加入了关于 extractLsb 与 `&&&`、`^^^`、`~~~` 和 `bif` 相互作用的定理。

* [#7029](https://github.com/leanprover/lean4/pull/7029) 向 bv_decide 的预处理器中加入了 simproc，可将 2 的幂次乘法重写为常量位移。

* [#7033](https://github.com/leanprover/lean4/pull/7033) 改进了 bv_decide 对 UIntX 与枚举归纳类型反例的展示方式。

* [#7242](https://github.com/leanprover/lean4/pull/7242) 确保 bv_decide 在其结构体处理阶段可以处理应用于 `ite` 和 `cond` 的投影。

* [#7257](https://github.com/leanprover/lean4/pull/7257) 提升了 bv_decide 中 LRAT trimming 的性能。

* [#7269](https://github.com/leanprover/lean4/pull/7269) 在 `bv_decide` 中实现了对 `IntX` 和 `ISize` 的支持。

* [#7275](https://github.com/leanprover/lean4/pull/7275) 将 Bitwuzla 的所有 level 1 重写加入 bv_decide 的预处理器。

### 精化并行化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--Parallelizing-Elaboration"
%%%

* [#6770](https://github.com/leanprover/lean4/pull/6770) 让代码生成能够与后续精化并行进行。

* [#6988](https://github.com/leanprover/lean4/pull/6988) 确保中断内核不会在编辑器中留下错误且挥之不去的错误消息。

* [#7047](https://github.com/leanprover/lean4/pull/7047) 移除了已被增量精化取代的 `save` 和 `checkpoint` 策略。

* [#7076](https://github.com/leanprover/lean4/pull/7076) 引入了核心并行 API，以确保辅助声明可以惰性生成，同时不会重复工作，也不会在线程间产生冲突。

### `simp +arith` 中的线性整数规范化
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--Linear-Integer-Normalization-in-simp-___arith"
%%%

* [#7000](https://github.com/leanprover/lean4/pull/7000) 添加了用于证明线性整数规范化器正确性的辅助定理。

* [#7002](https://github.com/leanprover/lean4/pull/7002) 实现了线性整数算术表达式的规范化器。由于存在一些多余的 `[simp]` 属性，它尚未接入 `simp +arith`。

* [#7011](https://github.com/leanprover/lean4/pull/7011) 为整数加入了 `simp +arith`。它使用 `grind` 的新线性整数算术规范化器。我们仍需实现按系数最大公约数整除的支持；该 PR 还修复了规范化器中的若干错误。

* [#7015](https://github.com/leanprover/lean4/pull/7015) 确保 `simp +arith` 会规范化线性整数多项式中的系数。目前仍有一个待办项：收紧不等式的界。

* [#7030](https://github.com/leanprover/lean4/pull/7030) 完成了 `grind` 中线性整数不等式规范化器的实现。缺失的规范化步骤会将形如 `a_1*x_1 + ... + a_n*x_n + b <= 0` 的线性不等式替换为 `a_1/k * x_1 + ... + a_n/k * x_n + ceil(b/k) <= 0`，其中 `k = gcd(a_1, ..., a_n)`。`ceil(b/k)` 借助辅助函数 `cdiv b k` 实现。

* [#7040](https://github.com/leanprover/lean4/pull/7040) 确保在使用 `simp +arith` 时，诸如 `f (2*x + y)` 和 `f (y + x + x)` 这样的项具有相同的规范形。

* [#7043](https://github.com/leanprover/lean4/pull/7043) 弃用了 `simp_arith`、`simp_arith!`、`simp_all_arith` 和 `simp_all_arith!` 这些策略。用户只需使用 `+arith` 选项即可。

### `grind` 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--grind-Tactic"
%%%

`grind` 策略目前仍属实验性功能，仍在开发中。请避免在生产项目中使用它。

* [#6902](https://github.com/leanprover/lean4/pull/6902) 确保 `simp` 的诊断信息会包含在 `grind` 的诊断消息中。

* [#6937](https://github.com/leanprover/lean4/pull/6937) 通过清理局部声明名称，改进了 `grind` 的错误和 trace 消息。

* [#6940](https://github.com/leanprover/lean4/pull/6940) 改进了 `grind` 对 `p <-> q` 进行分类讨论的方式。

* [#7102](https://github.com/leanprover/lean4/pull/7102) 将 `grind` 调整为在 `reducible` 透明度设置下运行。我们不希望 `grind` 在定义相等性测试时展开任意项。该 PR 还修复了这一变化引入的若干问题。最常见的问题是证明中缺少 hint，尤其是在通过反射构造的证明中。此外，当使用 `set_option grind.debug true` 时，还引入了新的健全性检查。

* [#7231](https://github.com/leanprover/lean4/pull/7231) 为 `grind` 实现了构造不等证明的函数。

#### Cutsat 过程（线性整数算术问题求解器）
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Language--grind-Tactic--Cutsat-Procedure-_LPAR_Solver-for-Linear-Integer-Arithmetic-Problems_RPAR_"
%%%

* [#7077](https://github.com/leanprover/lean4/pull/7077) 证明了 cutsat 过程中用于论证 “Div-Solve” 规则正确性的辅助定理。

* [#7091](https://github.com/leanprover/lean4/pull/7091) 添加了用于规范化整除约束的辅助定理。它们将被用于在 `grind` 策略中实现 cutsat 过程。

* [#7092](https://github.com/leanprover/lean4/pull/7092) 在 `simp +arith` 中实现了整除约束规范化。

* [#7097](https://github.com/leanprover/lean4/pull/7097) 为 `grind` 中的 cutsat 过程实现了若干修改。
  - 线性多项式中，最大的变量现在位于开头。
  - 旧的 `LinearArith.Solver` 已被删除，规范化器迁移到了 `Simp`。
  - 创建了 cutsat 的首批文件，并加入了表示整除约束的基础设施。

* [#7122](https://github.com/leanprover/lean4/pull/7122) 为 `grind` 策略中的 cutsat 过程实现了整除约束求解器。

* [#7124](https://github.com/leanprover/lean4/pull/7124) 添加了辅助定理，用于证明 `grind` 策略中 cutsat 过程所用整除约束求解器的正确性。

* [#7138](https://github.com/leanprover/lean4/pull/7138) 在 `grind` 中为整除约束求解器实现了证明生成。

* [#7139](https://github.com/leanprover/lean4/pull/7139) 在 `grind` 中，对 cutsat 过程生成的证明使用 `let` 表达式来存储（共享的）上下文。

* [#7152](https://github.com/leanprover/lean4/pull/7152) 实现了在 cutsat 过程中支持整数不等式约束的基础设施。

* [#7155](https://github.com/leanprover/lean4/pull/7155) 为 cutsat 中的模型搜索过程实现了一些基础设施。

* [#7156](https://github.com/leanprover/lean4/pull/7156) 添加了一条辅助定理，将用于模型构造期间的整除约束冲突消解。

* [#7176](https://github.com/leanprover/lean4/pull/7176) 在 cutsat 过程中实现了整除约束的模型构造。

* [#7183](https://github.com/leanprover/lean4/pull/7183) 改进了 cutsat 的模型搜索过程。

* [#7186](https://github.com/leanprover/lean4/pull/7186) 简化了 cutsat 使用的证明和数据结构。

* [#7193](https://github.com/leanprover/lean4/pull/7193) 为在 cutsat 中添加等式支持加入了基础设施。

* [#7194](https://github.com/leanprover/lean4/pull/7194) 添加了在 cutsat 中求解等式所需的支撑定理。

* [#7202](https://github.com/leanprover/lean4/pull/7202) 添加了将与 cutsat 过程相关的项内化到 `grind` 核心模块中的支持。这是实现等式传播所必需的。

* [#7203](https://github.com/leanprover/lean4/pull/7203) 改进了 cutsat 中对等式的支持，同时简化了几个用于证明 cutsat 规则正确性的支撑定理。

* [#7217](https://github.com/leanprover/lean4/pull/7217) 改进了 cutsat 中对等式的支持。

* [#7220](https://github.com/leanprover/lean4/pull/7220) 实现了从 `grind` 核心到 cutsat 模块进行等式传播时缺失的情况。

* [#7234](https://github.com/leanprover/lean4/pull/7234) 实现了从 `grind` 核心模块到 cutsat 的不等式传播。

* [#7244](https://github.com/leanprover/lean4/pull/7244) 为 `grind` 中使用的 cutsat 过程加入了对不等式的支持。

* [#7248](https://github.com/leanprover/lean4/pull/7248) 在 cutsat 中实现了简单的等式传播 `p <= 0 -> -p <= 0 -> p = 0`。

* [#7252](https://github.com/leanprover/lean4/pull/7252) 利用不等式改进不等式约束，从而减少 cutsat 需要进行的分类讨论次数。

* [#7267](https://github.com/leanprover/lean4/pull/7267) 改进了 cutsat 的搜索过程。它增加了查找近似有理解的支持、检查不等式，并为所有缺失情况加入了占位实现。

* [#7278](https://github.com/leanprover/lean4/pull/7278) 为 `grind` 策略中的线性整数约束加入了反例生成功能。该功能是在 cutsat 过程中实现的。

* [#7279](https://github.com/leanprover/lean4/pull/7279) 为 cutsat 过程中使用的 **Cooper-Dvd-Left** 冲突消解规则添加了支撑定理。在模型构造期间，当尝试将模型扩展到变量 `x` 时，cutsat 可能发现一个涉及两个不等式（`x` 的下界与上界）以及一个整除约束的冲突：

  ```lean
  a * x + p ≤ 0
  b * x + q ≤ 0
  d ∣ c * x + s
  ```

* [#7284](https://github.com/leanprover/lean4/pull/7284) 为 cutsat 过程实现了非时间顺序回溯。该过程主要有两类分类讨论：不等式和 Cooper resolvent。这个 PR 聚焦于前者。

* [#7290](https://github.com/leanprover/lean4/pull/7290) 为 cutsat 过程中使用的 **Cooper-Left** 冲突消解规则添加了支撑定理。在模型构造期间，当尝试将模型扩展到变量 `x` 时，cutsat 可能发现一个涉及两个不等式（`x` 的下界与上界）的冲突。这是没有整除约束时 Cooper-Dvd-Left 的特例。

* [#7292](https://github.com/leanprover/lean4/pull/7292) 为 cutsat 过程中使用的 **Cooper-Dvd-Right** 冲突消解规则添加了支撑定理。在模型构造期间，当尝试将模型扩展到变量 `x` 时，cutsat 可能发现一个涉及两个不等式（`x` 的下界与上界）以及一个整除约束的冲突。

* [#7293](https://github.com/leanprover/lean4/pull/7293) 为 cutsat 过程中使用的 Cooper-Right 冲突消解规则添加了支撑定理。在模型构造期间，当尝试将模型扩展到变量 x 时，cutsat 可能发现一个涉及两个不等式（x 的下界与上界）的冲突。这是没有整除约束时 Cooper-Dvd-Right 的特例。


* [#7409](https://github.com/leanprover/lean4/pull/7409) 允许在良基定义的预处理中使用 `dsimp`。这修复了某些回归：当使用未命名条件的 `if-then-else` 时，如果终止性证明需要用到该条件，而相关子表达式只能通过 dsimp 而不能通过 simp 到达（例如位于依赖 let 中），先前会失败。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Library"
%%%

* [#5498](https://github.com/leanprover/lean4/pull/5498) 在有证明可用时，将 `BitVec.getElem` 设为 simp 规范形，并修改 `ext`，使其返回 `x[i]` 加上一个证明越界检查通过的假设。这让 `BitVec` 进一步与 Lean 标准数据类型的 API 约定保持一致。

* [#6326](https://github.com/leanprover/lean4/pull/6326) 添加了 `BitVec.(getMsbD, msb)_replicate, replicate_one` 定理，修正了 `BitVec.getLsbD_replicate` 中一个非终止 `simp`，并使用 `cases` 策略简化了 `BitVec.getElem_replicate` 的证明。

* [#6628](https://github.com/leanprover/lean4/pull/6628) 按照[这里](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2)的定义，为 `BitVec` 添加了用于检测溢出的 SMT-LIB 运算符 `BitVec.(uadd_overflow, sadd_overflow)`，并添加了证明这些定义与 `BitVec` 库函数（`uaddOverflow_eq`, `saddOverflow_eq`）等价的定理。用于这些证明的支撑定理包括 `BitVec.toNat_mod_cancel_of_lt, BitVec.toInt_lt, BitVec.le_toInt, Int.bmod_neg_iff`。该 PR 还包含了一组测试。

* [#6792](https://github.com/leanprover/lean4/pull/6792) 添加了定理 `BitVec.(getMsbD, msb)_(extractLsb', extractLsb), getMsbD_extractLsb'_eq_getLsbD`。

* [#6795](https://github.com/leanprover/lean4/pull/6795) 添加了定理 `BitVec.(getElem_umod_of_lt, getElem_umod, getLsbD_umod, getMsbD_umod)`。在定义这些定理时，我们依赖 `divRec`，并将 `d=0#w` 的情况排除出来单独处理，因为目前在 `divRec` 内没有针对此情形进行推理的基础设施。特别地，我们的实现遵循 mathlib 的标准： [除以 0 得到 0](https://github.com/leanprover/lean4/blob/c7c1e091c9f07ae6f8e8ff7246eb7650e2740dcb/src/Init/Data/BitVec/Basic.lean#L217)，而在 [SMTLIB 中则得到 `allOnes`](https://github.com/leanprover/lean4/blob/c7c1e091c9f07ae6f8e8ff7246eb7650e2740dcb/src/Init/Data/BitVec/Basic.lean#L237)。

* [#6830](https://github.com/leanprover/lean4/pull/6830) 改进了部分文件划分，并统一了 UV 模块中的错误消息。

* [#6850](https://github.com/leanprover/lean4/pull/6850) 为新的树映射添加了一些引理。这些引理描述 `empty`、`isEmpty`、`insert`、`contains` 之间的相互作用。关于 `contains` 与其他操作相互作用的更多引理将在后续 PR 中补充。

* [#6866](https://github.com/leanprover/lean4/pull/6866) 为 `PUnit` 和 `PEmpty` 补上了缺失的 `Hashable` 实例。

* [#6914](https://github.com/leanprover/lean4/pull/6914) 将有序映射数据结构 `DTreeMap`、`TreeMap`、`TreeSet` 及其 `.Raw` 变体引入标准库。树映射仍有一些哈希映射已有而它尚未具备的操作。目前这些操作还未完成验证，但相应引理会在后续 PR 中陆续补上。尽管树映射已经过优化，但更多微优化仍要等新的代码生成器准备好之后再继续。

* [#6922](https://github.com/leanprover/lean4/pull/6922) 为 `Array` 和 `Vector` 添加了 `LawfulBEq` 实例。

* [#6948](https://github.com/leanprover/lean4/pull/6948) 完成了 `List/Array/Vectors` 在 `insertIdx` 引理上的对齐工作。

* [#6954](https://github.com/leanprover/lean4/pull/6954) 验证了哈希映射和依赖哈希映射的 `toList` 函数。

* [#6958](https://github.com/leanprover/lean4/pull/6958) 通过考虑被丢弃的 promise 可能导致任务永远无法完成的问题，改进了 `Promise` API。

* [#6966](https://github.com/leanprover/lean4/pull/6966) 添加了一个仅供内部使用的严格检查器，用于检查 `List`/`Array`/`Vector` 变量名，并开始进行清理工作。

* [#6982](https://github.com/leanprover/lean4/pull/6982) 基于 @Rob23oa 在 https://github.com/leanprover-community/batteries/pull/1109, 中的工作，改进了关于单子以及 Array/Vector 上单子式操作的一些引理，并新增/泛化了若干额外引理。

* [#7013](https://github.com/leanprover/lean4/pull/7013) 改进了 List/Array/Vector/Option 的 simp 集，以提升汇合性，为 `simp_lc` 做准备。

* [#7017](https://github.com/leanprover/lean4/pull/7017) 将 simp 集 `boolToPropSimps` 重命名为 `bool_to_prop`，并将 `bv_toNat` 重命名为 `bitvec_to_nat`。之后还会继续加入更多类似命名的 simp 集。

* [#7034](https://github.com/leanprover/lean4/pull/7034) 为 `{List,Array}.{foldlM,foldrM,mapM,filterMapM,flatMapM}` 添加了 `wf_preprocess` 定理。

* [#7036](https://github.com/leanprover/lean4/pull/7036) 为树映射添加了一些已弃用的函数别名，以便从 `RBMap` 过渡到树映射更顺畅。

* [#7046](https://github.com/leanprover/lean4/pull/7046) 将 `UIntX.mk` 重命名为 `UIntX.ofBitVec`，并加入弃用项。

* [#7048](https://github.com/leanprover/lean4/pull/7048) 添加了函数 `IntX.ofBitVec`。

* [#7050](https://github.com/leanprover/lean4/pull/7050) 将函数 `UIntX.val` 重命名为 `UIntX.toFin`。

* [#7051](https://github.com/leanprover/lean4/pull/7051) 在树映射上实现了 `insertMany`、`ofList`、`ofArray`、`foldr` 和 `foldrM` 方法。

* [#7056](https://github.com/leanprover/lean4/pull/7056) 添加了 `UIntX.ofFin` 转换函数。

* [#7057](https://github.com/leanprover/lean4/pull/7057) 添加了函数 `UIntX.ofNatLT`。它原本计划作为 `UIntX.ofNatCore` 和 `UIntX.ofNat'` 的替代，但出于自举原因，我们需要先让该函数在 stage0 中存在，才能继续推进重命名和弃用，因此这个 PR 只是先添加了该函数。

* [#7059](https://github.com/leanprover/lean4/pull/7059) 不再优先使用 `List.get` / `List.get?` / `List.get!` 和 `Array.get!`，改为使用由 `GetElem` 统一介导的 getter。具体来说，它弃用了 `List.get?`、`List.get!` 和 `Array.get?`。同时还添加了 `Array.back`，它接收一个证明，与 `List.getLast` 对齐。

* [#7062](https://github.com/leanprover/lean4/pull/7062) 引入了 `UIntX.toIntX` 作为公开 API，用来获取与给定 `UIntX` 在二补码意义下等价的 `IntX`。

* [#7063](https://github.com/leanprover/lean4/pull/7063) 添加了 `ISize.toInt8`、`ISize.toInt16`、`Int8.toISize`、`Int16.toISize`。

* [#7064](https://github.com/leanprover/lean4/pull/7064) 将 `BitVec.ofNatLt` 重命名为 `BitVec.ofNatLT`，并为旧名称建立了弃用项。

* [#7066](https://github.com/leanprover/lean4/pull/7066) 将 `IntX.toNat` 重命名为 `IntX.toNatClampNeg`（以减少意外），并建立了弃用项。

* [#7068](https://github.com/leanprover/lean4/pull/7068) 跟进 #7057，为 `UIntX.ofNatLT` 添加了一个内建 dsimproc。事实证明，在 stage0 中我们需要它，才能真正推动将 `UIntX.ofNatCore` 弃用为 `UIntX.ofNatLT`。

* [#7070](https://github.com/leanprover/lean4/pull/7070) 在树映射上实现了 `min`、`max`、`minKey`、`maxKey`、`atIndex`、`getEntryLE`、`getKeyLE` 及相关方法。

* [#7071](https://github.com/leanprover/lean4/pull/7071) 以新名称 `UIntX.ofNatLT` 统一了现有函数 `UIntX.ofNatCore` 和 `UIntX.ofNat'`。

* [#7079](https://github.com/leanprover/lean4/pull/7079) 将 `Fin.toNat` 引入为 `Fin.val` 的别名。添加该函数是出于可发现性和一致性考虑。证明中的规范形仍然是 `Fin.val`，并有一个 `simp` 引理将 `Fin.toNat` 重写为 `Fin.val`。

* [#7080](https://github.com/leanprover/lean4/pull/7080) 添加了函数 `UIntX.ofNatTruncate`（`UInt32` 的版本此前已经存在）。

* [#7081](https://github.com/leanprover/lean4/pull/7081) 添加了函数 `IntX.ofIntLE`、`IntX.ofIntTruncate`，它们分别类似于无符号对应项 `UIntX.ofNatLT` 和 `UInt.ofNatTruncate`。

* [#7083](https://github.com/leanprover/lean4/pull/7083) 添加了基于值而非位字段的 `Float`/`Float32` 与 `IntX`/`UIntX` 之间的转换函数。

* [#7105](https://github.com/leanprover/lean4/pull/7105) 完成了 `Array/Vector.extract` 引理与 `List.take`、`List.drop` 引理的对齐。

* [#7106](https://github.com/leanprover/lean4/pull/7106) 完成了 `List/Array/Vector.finRange` 引理的对齐。

* [#7109](https://github.com/leanprover/lean4/pull/7109) 在树映射上实现了 `getThenInsertIfNew?` 和 `partition` 函数。

* [#7114](https://github.com/leanprover/lean4/pull/7114) 在树映射上实现了 `values` 和 `valuesArray` 方法。

* [#7116](https://github.com/leanprover/lean4/pull/7116) 在树映射上实现了 `getKey` 系列函数。同时还修正了树集合中 `entryAtIdx` 函数的命名，它本应叫做 `atIdx`。

* [#7118](https://github.com/leanprover/lean4/pull/7118) 在树映射上实现了 `modify` 和 `alter` 函数。

* [#7128](https://github.com/leanprover/lean4/pull/7128) 为 `IntX` 添加了 `Repr` 和 `Hashable` 实例。

* [#7131](https://github.com/leanprover/lean4/pull/7131) 添加了 `IntX.abs` 函数。它们由 `BitVec.abs` 指定，因此会将 `IntX.minValue` 映射到 `IntX.minValue`，与 Rust 的 `i8::abs` 类似。未来我们也可能提供返回 `UIntX` 和/或 `Nat` 的版本。

* [#7137](https://github.com/leanprover/lean4/pull/7137) 验证了哈希映射上的各种 fold 和 for 变体。

* [#7151](https://github.com/leanprover/lean4/pull/7151) 修复了 `IO.FS.createTempFile` 中的内存泄漏。

* [#7158](https://github.com/leanprover/lean4/pull/7158) 通过去掉一个不必要的假设，加强了 `Int.tdiv_eq_ediv`，为后续关于 `ediv`/`tdiv`/`fdiv` 引理的工作做准备。

* [#7161](https://github.com/leanprover/lean4/pull/7161) 补全了树映射中 `empty`、`isEmpty`、`contains`、`size`、`insert(IfNew)` 和 `erase` 这些函数之间相互作用的全部缺失引理。

* [#7162](https://github.com/leanprover/lean4/pull/7162) 将 `Int.DivModLemmas` 拆分为 `Bootstrap` 和 `Lemmas` 两个文件，从而可以在 `Lemmas` 中使用 `omega`。

* [#7163](https://github.com/leanprover/lean4/pull/7163) 提供了一个无条件定理，将 `Int.tdiv` 表示为 `Int.ediv`，而不仅限于非负参数情形。

* [#7165](https://github.com/leanprover/lean4/pull/7165) 提供了树映射中 `containsThenInsert(IfNew)` 与 `contains` 和 `insert(IfNew)` 相互作用的引理。

* [#7167](https://github.com/leanprover/lean4/pull/7167) 为树映射中 `get?` 与其他已有引理支持的操作之间的相互作用提供了引理。

* [#7174](https://github.com/leanprover/lean4/pull/7174) 添加了第一批关于有限类型之间迭代转换的引理，这些转换从某个 `UIntX` 类型的值开始。

* [#7199](https://github.com/leanprover/lean4/pull/7199) 为任意符号组合的参数添加了比较 `Int.ediv` 与 `tdiv`、`fdiv` 的定理。（此前我们只有它们相等情形的陈述。）

* [#7201](https://github.com/leanprover/lean4/pull/7201) 添加了 `Array/Vector.left/rightpad`。这些函数不会配套验证定理；simp 只会将它们展开为 `++` 操作。

* [#7205](https://github.com/leanprover/lean4/pull/7205) 完成了 `List.getLast`/`List.getLast!`/`List.getLast?` 引理与 Array 和 Vector 对应引理的对齐。

* [#7206](https://github.com/leanprover/lean4/pull/7206) 添加了定理 `BitVec.toFin_abs`，补全了 `BitVec.*_abs` 的 API。

* [#7207](https://github.com/leanprover/lean4/pull/7207) 提供了树映射函数 `get`、`get!` 和 `getD` 与其他已有引理支持的操作之间关系的引理。

* [#7208](https://github.com/leanprover/lean4/pull/7208) 对齐了 `List.dropLast` / `Array.pop` / `Vector.pop` 的引理。

* [#7210](https://github.com/leanprover/lean4/pull/7210) 补齐了剩余的有限类型迭代转换引理，这些转换从某个 `UIntX` 类型的值开始。

* [#7214](https://github.com/leanprover/lean4/pull/7214) 为 `PersistentHashSet` 类型添加了 `ForIn` 实例。

* [#7221](https://github.com/leanprover/lean4/pull/7221) 提供了树映射函数 `getKey?`、`getKey`、`getKey!`、`getKeyD` 以及 `insertIfNew` 与其他已有引理支持的函数之间相互作用的引理。

* [#7222](https://github.com/leanprover/lean4/pull/7222) 去掉了 `ReflCmp.compare_self` 的 `simp` 属性，因为它会匹配任意函数应用。作为替代，引入了新的 `simp` 引理 `ReflOrd.compare_self`，它只匹配 `compare` 的应用。

* [#7229](https://github.com/leanprover/lean4/pull/7229) 为树映射函数 `getThenInsertIfNew?` 提供了引理。

* [#7235](https://github.com/leanprover/lean4/pull/7235) 添加了 `Array.replace` 和 `Vector.replace`，证明了它们与 `List.replace` 的对应关系，并复现了基础 API。为此，它还补上了 `List.findX` API 中的一些空缺。

* [#7237](https://github.com/leanprover/lean4/pull/7237) 证明了原始树映射操作是良构的，并重构了树映射的文件结构，引入了新模块 `Std.{DTreeMap,TreeMap,TreeSet}.Raw`，并将 `AdditionalOperations` 拆分为封装类型和原始类型的独立文件。

* [#7245](https://github.com/leanprover/lean4/pull/7245) 为 `Std.Data.DHashMap.Internal.AssocList` 中的 `alter` 和 `modify` 函数补上了缺失的 `@[specialize]` 注解，这两个函数会被对应的哈希映射函数使用。

* [#7249](https://github.com/leanprover/lean4/pull/7249) 完成了 `List/Array/Vector.any/all` 相关定理的对齐。

* [#7255](https://github.com/leanprover/lean4/pull/7255) 修复了 `Min (Option α)` 的定义。这是一次破坏性变更。现在 `none` 被视为最小元素，因此对任意 `x : Option α` 都有 `min none x = min x none = none`。在 nightly-2025-02-27 之前，我们则有 `min none (some x) = min (some x) none = some x`。该 PR 还补充了 `Option` 上 `min`、`max`、`≤` 与 `<` 之间关系的基础引理。

* [#7259](https://github.com/leanprover/lean4/pull/7259) 包含了 `bv_decide` 和 `IntX` simproc 所需的 `IntX` 定理。

* [#7260](https://github.com/leanprover/lean4/pull/7260) 提供了树映射函数 `keys` 与 `toList` 及其和其他已有引理支持函数之间相互作用的引理。此外，它还修复了 `foldr` 中一个 bug（误调用 `foldlM` 而不是 `foldrM`）。

* [#7266](https://github.com/leanprover/lean4/pull/7266) 开始推进 `Int.ediv/fdiv/tdiv` 定理的对齐工作。

* [#7268](https://github.com/leanprover/lean4/pull/7268) 为有限有符号整数实现了 `Lean.ToExpr`。

* [#7271](https://github.com/leanprover/lean4/pull/7271) 调整了树映射 `foldr` 和 `foldrM` 所期望的 folding 函数参数顺序，使之与 `List` 的 API 一致。

* [#7273](https://github.com/leanprover/lean4/pull/7273) 修复了一条 `UIntX` 转换引理的陈述。

* [#7277](https://github.com/leanprover/lean4/pull/7277) 修复了 Float32.ofInt 中的一个 bug；此前它会返回 Float(64)。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Compiler"
%%%

* [#6928](https://github.com/leanprover/lean4/pull/6928) 在 LCNF elimDeadBranches 分析中，让 extern 声明求值为 ⊤，而不是 ⊥ 的默认值。

* [#6930](https://github.com/leanprover/lean4/pull/6930) 修改了特化后的 LCNF 声明的名称生成方式，不再去除宏作用域。这避免了在不同宏作用域中创建的特化之间发生名称冲突。由于常规的 `Name.append` 会检查宏作用域是否存在，因此这里需要使用 `appendCore`。

* [#6976](https://github.com/leanprover/lean4/pull/6976) 扩展了 `Task.map/bind` 等中 `sync` 标志的行为：即使必须先等待首个任务完成，也会以同步方式执行后续部分，从而大幅降低这类任务的开销。因此，该标志现在等价于 .NET 中的 `TaskContinuationOptions.ExecuteSynchronously`。

* [#7037](https://github.com/leanprover/lean4/pull/7037) 将 Lean 及 Lean 可执行文件在 x86-64 Linux 上所需的最低 glibc 版本放宽到 2.26。

* [#7041](https://github.com/leanprover/lean4/pull/7041) 将若干 LCNF 专用环境扩展的 `asyncMode` 从默认的 `.mainOnly` 改为 `.sync`，从而让它们即使在异步上下文中也能正常工作。

* [#7086](https://github.com/leanprover/lean4/pull/7086) 让新代码生成器中的 arity reduction 阶段在处理无已用参数声明时与旧版本保持一致。这很重要，因为否则我们可能创建一个不带参数的顶层声明，却包含不可达代码，而这些代码会在初始化期间被无条件求值。用新代码生成器构建的 Init.Core 在初始化时确实会出现这种情况。

## 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Pretty-Printing"
%%%

* [#7074](https://github.com/leanprover/lean4/pull/7074) 修改了签名美观打印器，为绑定器中的参数添加悬停信息。这让绑定器中的悬停体验与 pi 类型中的悬停保持一致。

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Documentation"
%%%

* [#6886](https://github.com/leanprover/lean4/pull/6886) 使用 #6869 中的 `recommended_spelling` 命令，为 Lean core 中定义的许多记号添加了推荐拼写。

* [#6950](https://github.com/leanprover/lean4/pull/6950) 为标准库添加了风格指南和命名约定。

* [#6962](https://github.com/leanprover/lean4/pull/6962) 改进了 `List.toArray` 的文档字符串。

* [#6998](https://github.com/leanprover/lean4/pull/6998) 修改了 `Prop` 的文档字符串，指出每个命题在命题相等意义下都等于 `True` 或 `False` 之一。这将帮助用户理解 `Prop` 与 `Bool` 的相似性。

* [#7026](https://github.com/leanprover/lean4/pull/7026) 澄清了 `do` 代码块的风格，并在命名约定中补充了关于 `ext` 和 `mono` 名称成分的信息，以及关于撇号名称和 simp 集命名的建议。

* [#7111](https://github.com/leanprover/lean4/pull/7111) 扩展了标准库风格指南，增加了关于 universe 变量、记号与 Unicode 用法，以及结构体定义的指导。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Server"
%%%

* [#6329](https://github.com/leanprover/lean4/pull/6329) 让语言服务器能够将多个互不相交的行区间显示为“正在处理”。即使在并行化尚未落地之前，我们也利用该特性在声明第一行显示诸如内核检查之类的后精化任务，以便将其与最后一步策略区分开来。

* [#6768](https://github.com/leanprover/lean4/pull/6768) 添加了对嵌入提示的初步支持，以及用于表示函数自动隐式参数的嵌入提示。悬停在自动隐式参数上会显示其类型，双击该自动隐式参数则会将其插入文本文件中。

  **破坏性变更：** 语义高亮请求处理器不再是纯请求处理器，而是有状态的。尤其是，这意味着使用 `chainLspRequestHandler` 扩展 Lean 语言服务器语义高亮的客户端，现在必须改用 `chainStatefulLspRequestHandler`。

* [#6887](https://github.com/leanprover/lean4/pull/6887) 修复了一个 bug：目标状态选择有时会在空白字符处选到不完整的增量快照，导致错误地返回 “no goals”。修复了 #6594；这个回归最早由 4.11.0 中的 #4727 引入。

* [#6959](https://github.com/leanprover/lean4/pull/6959) 对 #6768 中实现的自动隐式嵌入提示进行了一系列改进。
  具体包括：
  - 在 #6768 中，嵌入提示编辑延迟存在一个 bug，会在连续编辑中不断累积，因此有时会导致嵌入提示显示得慢很多。该 PR 实现了请求取消的基础设施，并为语义 token 和嵌入提示实现了请求取消，以解决这一问题。修复该编辑延迟 bug 之后，将编辑延迟从 2000ms 略微提高到 3000ms 也更合理了。
  - 在 #6768 中，我们对每一次嵌入提示请求都施加了编辑延迟，以减少嵌入提示闪烁。这也意味着编辑延迟会显著影响嵌入提示落后于文件进度条的程度。该 PR 调整了编辑延迟逻辑，使其只影响紧随相应 `didChange` 通知之后发送的请求。一旦编辑延迟耗尽，后续所有语义 token 请求都会无延迟响应，因此嵌入提示相对进度条的延迟只取决于我们发出刷新请求的频率以及 VS Code 响应这些请求所需的时间。
  - 对于嵌入提示，现在会在响应某个嵌入提示请求后 500ms 发出刷新请求，而不是 2000ms。这意味着经过编辑延迟后，嵌入提示相对于进度条的滞后通常只会在约 500ms 以内。对嵌入提示而言，这样做是合理的，因为它们的响应通常远小于例如语义 token 的响应。
  - 在 #6768 中，“Restart File” 不会触发刷新；现在会了。
  - VS Code 在应用嵌入提示时，不会立即从文档中移除旧的嵌入提示。在 #6768 中，这意味着旧提示在应用后还会停留片刻。为缓解这一问题，该 PR 调整了嵌入提示编辑延迟逻辑，以识别来自客户端的编辑是否属于应用嵌入提示的编辑，并将其后的嵌入提示请求的编辑延迟设为 0ms。这意味着嵌入提示现在会立即应用。
  - 在 #6768 中，悬停单字母自动隐式嵌入提示时体验有些别扭，因为 VS Code 在嵌入提示上使用的是普通光标图标，而不是细文本光标图标，因此很容易把光标放错位置。现在我们还会把自动隐式参数前面的分隔字符（` ` 或 `{`）也纳入悬停范围，使悬停操作顺畅得多。

* [#6978](https://github.com/leanprover/lean4/pull/6978) 修复了一个 bug：在未命名文件中，嵌入提示变更失效逻辑和嵌入提示编辑延迟逻辑都无法正常工作。感谢 @Julian 发现这个问题！


* [#7054](https://github.com/leanprover/lean4/pull/7054) 为以下高开销请求加入了语言服务器端的请求取消支持：代码操作、自动补全、文档符号、折叠区间和语义高亮。这意味着当客户端告知语言服务器某个请求已经过期（例如它属于文档的旧状态）时，语言服务器现在会提前取消该响应的计算，从而降低那些最终会被客户端丢弃的请求所带来的 CPU 负载。

* [#7087](https://github.com/leanprover/lean4/pull/7087) 确保语言服务器中的所有任务要么使用专用任务，要么复用线程池中的已有线程。这保证了精化任务不会阻止语言服务器任务被调度。随着并行化即将到来，精化更有可能挤占语言服务器的计算资源，因此这一点尤其重要；否则在核心数较少的机器上，语言服务器延迟可能显著增加。

* [#7112](https://github.com/leanprover/lean4/pull/7112) 添加了一个工具提示，用于说明自动隐式嵌入提示表示的含义，并为实例也加入了自动隐式嵌入提示。

* [#7134](https://github.com/leanprover/lean4/pull/7134) 通过将单次请求优化约 2 倍，并让 VS Code 等语言客户端可以复用先前补全请求的状态，显著提升了自动补全性能，从而大幅降低在标识符后继续输入更多字符时补全列表更新的延迟。

* [#7143](https://github.com/leanprover/lean4/pull/7143) 让服务器在所有情况下都不再向 info view 报告 trace 节点之间的换行，从而使 info view 能够把它们渲染在各自独立的行上，而不会出现多余的间距。

* [#7149](https://github.com/leanprover/lean4/pull/7149) 为嵌入提示请求加入了快速路径，使其能够复用之前请求中已计算好的嵌入提示，而不是重新计算。这一点很有必要，因为出于某种原因，VS Code 会在每次滚动一行时都发出一次嵌入提示请求，因此我们需要能够基于相同文档状态快速响应这些请求。否则，在较长文件中，每滚动一行都会触发一个可能需要几十毫秒才能响应的请求，给 CPU 带来不必要的压力。该 PR 还会根据请求的嵌入提示范围过滤结果集。

* [#7153](https://github.com/leanprover/lean4/pull/7153) 修改服务器，使其会对 Lake 配置文件（例如 `lakefile.lean`）运行 `lake setup-file`。

* [#7175](https://github.com/leanprover/lean4/pull/7175) 修复了一个 `Elab.async` 回归：精化任务会在文档编辑时被取消，即便其结果其实可以在文档新版本中复用，从而导致报告出不完整结果。

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Lake"
%%%

* [#6829](https://github.com/leanprover/lean4/pull/6829) 修改了 Lake 配置失败时的错误信息，以反映问题并不总是来自无效的 lakefile，也可能来自网络错误等其他问题。新的错误信息覆盖了所有这些可能性。

* [#6929](https://github.com/leanprover/lean4/pull/6929) 在 CMake 构建中，将上一阶段 Lake 的共享库作为插件传递给下一阶段 Lake。这使得 Lake 在构建时可以使用它自己的内建 elaborator / initializer。

* [#7001](https://github.com/leanprover/lean4/pull/7001) 为 Lake 添加了插件支持。预编译模块现在作为插件加载，而不再通过 `--load-dynlib`。

* [#7024](https://github.com/leanprover/lean4/pull/7024) 记录了如何在 `lake new|init` 中使用 Elan 的 `+` 选项。如果 `+` 选项意外泄露到了 Lake 中（例如用户在未通过 Elan 的情况下把该选项传给了 Lake 运行），它还会给出更有信息量的错误消息。

* [#7157](https://github.com/leanprover/lean4/pull/7157) 修改了 `lake setup-file`：对于导入 Lake（或其子模块）的文件，它现在会把 Lake 作为插件使用。因此，在编辑以 Lean 编写的 Lake 配置时，服务器现在会将 Lake 作为插件加载。这进一步使 Lake 能够使用内建语言扩展。

* [#7171](https://github.com/leanprover/lean4/pull/7171) 将 Lake DSL 改为使用内建 elaborator、macro 和 initializer。

* [#7182](https://github.com/leanprover/lean4/pull/7182) 让 `lake setup-file` 在 Lean 配置文件无效时也能成功。

* [#7209](https://github.com/leanprover/lean4/pull/7209) 修复了 Windows 新版 MSYS2 上损坏的 Lake 测试。从 MSYS2 0.0.20250221 起，`OSTYPE` 现在报告为 `cygwin` 而不是 `msys`，因此需要在若干 Lake 测试中对此进行处理。

* [#7211](https://github.com/leanprover/lean4/pull/7211) 修改了任务监视器，使其把 run job computation 本身作为一个独立任务执行。现在，即使所有未发现任务还未被枚举完，也会尽早报告进度。因此，在任务仍在计算期间，报告的总任务数现在可能继续增长（例如 `[X/Y[` 中的 `Y` 可能增大）。

* [#7233](https://github.com/leanprover/lean4/pull/7233) 在使用 `USE_LAKE` 通过 Lake 构建 Lake 时，会使用 Lake 插件。

* [#7291](https://github.com/leanprover/lean4/pull/7291) 修改了 Lake 任务监视器，使其显示最后一个（即最新的）正在运行/未完成任务，而不是第一个。这避免了监视器长时间聚焦在单个任务上（例如 “Running job computation”）。

* [#7399](https://github.com/leanprover/lean4/pull/7399) 将 Lake 中新的内建 initializer、elaborator 和 macro 回退为非内建实现。

* [#7608](https://github.com/leanprover/lean4/pull/7608) 移除了 Lake 构建和配置文件中对 Lake 插件的使用。

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___18___0-_LPAR_2025-04-02_RPAR_--Other"
%%%

* [#7129](https://github.com/leanprover/lean4/pull/7129) 在定义具有巨大 `Expr` 表示时，优化了未使用变量检查器的性能。

* [#7173](https://github.com/leanprover/lean4/pull/7173) 为每次 deriving handler 调用引入了一个 trace 节点，以服务于 `trace.profiler`。

* [#7184](https://github.com/leanprover/lean4/pull/7184) 为 macOS 添加了对 LEAN_BACKTRACE 的支持。此前这只在 glibc 下可用，但现在可以在所有类 Unix 系统上启用，因为例如 Musl 并不支持它。

* [#7190](https://github.com/leanprover/lean4/pull/7190) 让 stage2 的 Leanc 构建使用 stage2 oleans，而不是 stage1 oleans。此前之所以会发生错误，是因为 Leanc 自身的 OLEAN_OUT 位于构建根目录，而不是 `lib/lean` 子目录；当构建过程把这个 OLEAN_OUT 添加到 LEAN_PATH 时，该位置找不到任何 oleans，于是搜索退回到了 stage1 安装位置。

````
