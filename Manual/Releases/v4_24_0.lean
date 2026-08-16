/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.24.0 (2025-10-14)" =>
%%%
tag := "release-v4.24.0"
file := "v4.24.0"
%%%

````markdown
本次发布共合入 377 项变更。除下文列出的 105 项功能新增和 75 项修复外，还有 25 项重构、9 项文档改进、21 项性能改进、4 项测试套件改进，以及 138 项其他改动。

````
# 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights"
%%%

````markdown

Lean 4.24.0 继续改进模块系统和验证框架，增强了 `grind` 策略，并推进了标准库的发展。本次发布还引入了更高效的 `DecidableEq` 实例与 `noConfusion` 构造（[#10152](https://github.com/leanprover/lean4/pull/10152) 与 [#10300](https://github.com/leanprover/lean4/pull/10300)），从而优化编译。

作为我们持续改进性能的一个例子：

- [#10249](https://github.com/leanprover/lean4/pull/10249) 通过改进语言服务器的多处性能表现，将自动补全速度提升到了约 3.5 倍。

和往常一样，本次也包含大量错误修复和新特性，下面列出其中一部分：

````
## “try this” 建议显示在 “Messages” 下方
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--___Try-this___-suggestions-are-rendered-under-___Messages___"
%%%

````markdown

- [#9966](https://github.com/leanprover/lean4/pull/9966) 调整了 “try this” 小部件的呈现方式：它现在会作为 `Messages` 下方的一条小部件消息显示，而不是作为 `Suggestions` 区域下的独立小部件显示。这样做的主要好处是，这条消息不再会在 `Messages` 和 `Suggestions` 之间重复出现。

````
## `mvcgen` 中的 `invariants` 与 `with` 小节
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--invariants-and-with-sections-in-mvcgen"
%%%

````markdown

- [#9927](https://github.com/leanprover/lean4/pull/9927) 为 `mvcgen` 实现了受 `induction` 启发的扩展语法，允许可选的 `invariants` 和 `with` 小节。

下面的示例证明了 `nodup` 能正确检查列表中的重复元素。

  ```lean
  import Std.Tactic.Do
  import Std

  open Std Do

  def nodup (l : List Int) : Bool := Id.run do
    let mut seen : HashSet Int := ∅
    for x in l do
      if x ∈ seen then
        return false
      seen := seen.insert x
    return true

  theorem nodup_correct (h : nodup l = r) : r = true ↔ l.Nodup := by
    unfold nodup at h
    apply Id.of_wp_run_eq h; clear h
    mvcgen
    invariants
    · Invariant.withEarlyReturn
        (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
        (onContinue := fun xs seen =>
          ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
    with grind
  ```

````
## 库：二进有理数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Library___-Dyadic-rationals"
%%%

````markdown

- [#9993](https://github.com/leanprover/lean4/pull/9993) 定义了二进有理数，并证明它们构成一个可嵌入到有理数中的有序环。

````
## `grind` AC 求解器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Grind-AC-solver"
%%%

````markdown

`grind` 现在可以对结合、交换、幂等以及/或者幺元运算进行推理（[#10105](https://github.com/leanprover/lean4/pull/10105)、[#10146](https://github.com/leanprover/lean4/pull/10146) 等）：

```lean
example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) := by
  grind only

example {α} (as bs cs : List α) : as ++ (bs ++ cs) = ((as ++ []) ++ bs) ++ (cs ++ []) := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only
```

````
## 元编程说明
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Metaprogramming-notes"
%%%

````markdown

- [#10306](https://github.com/leanprover/lean4/pull/10306) 修复了 `rw` 策略中的几个错误。

元编程 API：若要精译重写定理并对表达式应用重写，请优先使用 `Lean.Elab.Tactic.elabRewrite`，而不是 `Lean.MVarId.rewrite`。

````
## 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Breaking-changes"
%%%

````markdown

- [#9749](https://github.com/leanprover/lean4/pull/9749) 将 Lake 代码库全面重构为使用新的模块系统。`Lake` 中的每个模块现在都是真正的 `module`。

  **破坏性变更：** 由于模块系统鼓励采用“默认 `private`”的设计，Lake API 已从先前“默认 `public`”的做法切换过来。因此，许多以前公开的定义现在都变成了私有。预计这些新变为私有的定义不会被用户大量使用，但仍可能遗漏重要用例。如果某个关键 API 现在无法访问、但看起来本应公开，鼓励用户在 GitHub 上提交 issue 反馈。

````
# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Language"
%%%

````markdown

* [#8891](https://github.com/leanprover/lean4/pull/8891) 改进把（自动冗余的）局部假设传给 `grind` 时产生的错误消息。

* [#9651](https://github.com/leanprover/lean4/pull/9651) 修改了通过 `partial_fixpoint` 定义的 `mutual` 块所生成的归纳引理与部分正确性引理。此外，还修改了通过 `mutual` 块为函数生成格论归纳原理的方式，使其与 `partial_fixpoint` 保持一致。

* [#9674](https://github.com/leanprover/lean4/pull/9674) 在精译定义体、定理体、`fun` 体和 `let` 函数体之前，会先清理 `optParam`/`autoParam` 等注解。声明头中的 `variable` 与绑定器都受支持。

* [#9918](https://github.com/leanprover/lean4/pull/9918) 防止 `rcases` 和 `obtain` 在拆解单构造器类型（如 `Exists`）时生成荒谬冗长的分支标签名。修复 #6550。

* [#9923](https://github.com/leanprover/lean4/pull/9923) 为一个会导致 doc-gen4 崩溃的反精译器添加了防护。这目前只是权宜之计，@sgraf812 休假回来后会进一步检查。

* [#9926](https://github.com/leanprover/lean4/pull/9926) 为 `Std.Tactic.Do.MGoalEntails` 反精译器添加检查，确保至少存在三个参数，从而防止潜在崩溃。

* [#9927](https://github.com/leanprover/lean4/pull/9927) 为 `mvcgen` 实现了扩展的、受 `induction` 启发的语法，允许可选的 `using invariants` 与 `with` 小节。

* [#9930](https://github.com/leanprover/lean4/pull/9930) 回退了 `grind cutsat` 将 `Nat.sub` 嵌入 `Int` 的方式。它修复了 David Renshaw 在 Zulip 上报告的一个回归。

* [#9938](https://github.com/leanprover/lean4/pull/9938)删除了重复的`mpure_intro` 策略定义。

* [#9939](https://github.com/leanprover/lean4/pull/9939) 将 `mvcgen using invariants | $n => $t` 展开为 `mvcgen; case inv<$n> => exact $t`，以避免在 #9581 的测试用例中可观察到的 MVar 实例化失误。

* [#9942](https://github.com/leanprover/lean4/pull/9942) 修改 `intro`，为每个假设创建局部化的策略信息，从而可以逐个变量地看出 `intro` 的工作方式。此外：
  - 该策略现在支持 `intro rfl`：它会像 `rintro rfl` 一样引入一个等式并立即代换（回顾一下，`rfl` 模式相当于执行 `intro h; subst h`）。如果 `eq_of_heq` 适用，`rintro` 现在也支持在 `rfl` 模式中处理 `HEq`。
  - 在 `intro (h : t)` 中，`t` 的精译会与同 `h` 的类型做统一交错进行，从而避免默认实例导致统一失败。
  - 会改变假设类型的策略（包括 `intro (h : t)`、`delta`、`dsimp`）现在会更新局部实例缓存。

* [#9945](https://github.com/leanprover/lean4/pull/9945) 优化 `grind cutsat` 生成的证明项。它会在构造最终证明时移除上下文对象中未使用的条目，从而显著减少结果项里的冗余内容。示例：
  ```lean
  /--
  trace: [grind.debug.proof] fun h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 =>
        let ctx := RArray.leaf (f 2);
        let p_1 := Poly.add 1 0 (Poly.num 0);
        let p_2 := Poly.add (-1) 0 (Poly.num 1);
        let p_3 := Poly.num 1;
        le_unsat ctx p_3 (eagerReduce (Eq.refl true)) (le_combine ctx p_2 p_1 p_3 (eagerReduce (Eq.refl true)) h_8 h_1)
  -/
  #guard_msgs in -- Context should contain only `f 2`
  open Lean Int Linear in
  set_option trace.grind.debug.proof true in
  example (f : Nat → Int) :
      f 1 <= 0 → f 2 <= 0 → f 3 <= 0 → f 4 <= 0 → f 5 <= 0 →
      f 6 <= 0 → f 7 <= 0 → f 8 <= 0 → -1 * f 2 + 1 <= 0 → False := by
    grind
  ```

* [#9946](https://github.com/leanprover/lean4/pull/9946) 优化 `grind ring` 生成的证明项。它与 #9945 类似，但面向 `grind` 中的 `ring` 模块；在生成最终证明时，会从上下文对象中移除未使用的条目，从而显著减少结果项里的冗余内容。示例：
  ```lean
  /--
  trace: [grind.debug.proof] fun h h_1 h_2 h_3 =>
        Classical.byContradiction fun h_4 =>
          let ctx := RArray.branch 1 (RArray.leaf x) (RArray.leaf x⁻¹);
          let e_1 := (Expr.var 0).mul (Expr.var 1);
          let e_2 := Expr.num 0;
          let e_3 := Expr.num 1;
          let e_4 := (Expr.var 0).pow 2;
          let m_1 := Mon.mult (Power.mk 1 1) Mon.unit;
          let m_2 := Mon.mult (Power.mk 0 1) Mon.unit;
          let p_1 := Poly.num (-1);
          let p_2 := Poly.add (-1) (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num 0);
          let p_3 := Poly.add 1 (Mon.mult (Power.mk 0 2) Mon.unit) (Poly.num 0);
          let p_4 := Poly.add 1 (Mon.mult (Power.mk 0 1) (Mon.mult (Power.mk 1 1) Mon.unit)) (Poly.num (-1));
          let p_5 := Poly.add 1 (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num 0);
          one_eq_zero_unsat ctx p_1 (eagerReduce (Eq.refl true))
            (Stepwise.simp ctx 1 p_4 (-1) m_1 p_5 p_1 (eagerReduce (Eq.refl true))
              (Stepwise.core ctx e_1 e_3 p_4 (eagerReduce (Eq.refl true)) (diseq0_to_eq x h_4))
              (Stepwise.mul ctx p_2 (-1) p_5 (eagerReduce (Eq.refl true))
                (Stepwise.superpose ctx 1 m_2 p_4 (-1) m_1 p_3 p_2 (eagerReduce (Eq.refl true))
                  (Stepwise.core ctx e_1 e_3 p_4 (eagerReduce (Eq.refl true)) (diseq0_to_eq x h_4))
                  (Stepwise.core ctx e_4 e_2 p_3 (eagerReduce (Eq.refl true)) h))))
  -/
  #guard_msgs in -- Context should contains only `x` and its inverse.
  set_option trace.grind.debug.proof true in
  set_option pp.structureInstances false in
  open Lean Grind CommRing in
  example [Field α] (x y z w : α) :
     x^2 = 0 → y^2 = 0 → z^3 = 0 → w^2 = 0 → x = 0 := by
    grind
  ```

* [#9947](https://github.com/leanprover/lean4/pull/9947) 优化 `grind linarith` 生成的证明项。它与 #9945 类似，但面向 `grind` 中的 `linarith` 模块；在生成最终证明时，会从上下文对象中移除未使用的条目，从而显著减少结果项里的冗余内容。

* [#9951](https://github.com/leanprover/lean4/pull/9951) 为所有归纳类型生成 `.ctorIdx` 函数，而不仅限于枚举类型。这可以作为其他构造（如 `BEq`、`noConfusion`）的基础，使它们即便面对大型归纳类型也能保持尺寸高效。

* [#9952](https://github.com/leanprover/lean4/pull/9952) 添加“非分支式分情况语句”：对每个归纳类型构造器 `T.con`，新增一个与 `T.casesOn` 类似的函数 `T.con.with`，但它只有一个分支（即 `con` 的分支），并额外带有假设 `t.toCtorIdx = 12`。

* [#9954](https://github.com/leanprover/lean4/pull/9954) 删除了选项 `grind +ringNull`。它为 `grind ring` 模块提供了另一种证明项构造方式，但效果不如默认模式，实际上已经成了死代码。该 PR 还利用 #9946 中加入的基础设施，优化了半环归一化证明项。**备注：** 在更新第 0 阶段之后，我们可以删除 `Init/Grind` 目录中的若干背景定理。

* [#9958](https://github.com/leanprover/lean4/pull/9958) 确保 `grind cutsat` 模块中的方程始终保持已解形式。也就是说，若用方程 `a*x + p = 0` 消去 `x`，则线性多项式 `p` 中不得再包含其他已消去的变量。在这个 PR 之前，这些方程保持的是三角形式。我们接下来会利用已解形式来线性化非线性项。

* [#9968](https://github.com/leanprover/lean4/pull/9968) 修改了实现非原子定义与 ```$cmd1 in $cmd2``` 语法的宏。这些宏涉及由 ```section``` 和 ```namespace``` 命令引入的隐式作用域。由于小节与命名空间本来就是用来界定局部属性的，把局部属性应用到上述上下文中出现的定义时，会产生不直观的行为；这正是下面这些示例失败的原因：
  ```lean4
  axiom A : Prop

* [#9974](https://github.com/leanprover/lean4/pull/9974) 为 `Lean.Parser.Command.visibility` 注册了解析器别名。这样一来，使用可见性修饰的简单命令宏就不必再导入 `Lean.Parser.Command`。

* [#9980](https://github.com/leanprover/lean4/pull/9980) 修复了 `grind cutsat` 所用动态变量重排函数中的一个错误。

* [#9989](https://github.com/leanprover/lean4/pull/9989) 将 `mvcgen` 的新扩展语法改为 `mvcgen invariants ... with ...`。

* [#9995](https://github.com/leanprover/lean4/pull/9995) 几乎完全重写了归纳谓词递归算法，尤其让 `IndPredBelow` 的行为更加一致。历史上，经由 `IndPredBelow` 生成 `brecOn` 一直很容易出错；现在这一问题应已修复，因为新算法非常直接，完全不依赖策略或元变量。此外，归纳谓词的新结构递归过程与常规结构递归共享了更多代码，因此现在也能像常规结构递归那样支持互递归和嵌套递归。例如，下面的代码现在可以工作：
  ```lean-4
  mutual

* [#9996](https://github.com/leanprover/lean4/pull/9996) 改进了 `grind cutsat` 对非线性单项式的支持。例如，给定单项式 `a * b`，如果 `cutsat` 发现 `a = 2`，它现在会传播出 `a * b = 2 * b`。回顾一下，`a * b` 这样的非线性单项式在 `cutsat` 中被当作变量，而 `cutsat` 是为线性整数算术设计的过程。

* [#10007](https://github.com/leanprover/lean4/pull/10007) 让 `#print` 在输出 `protected` 之前先输出 `private`，与语法保持一致。

* [#10008](https://github.com/leanprover/lean4/pull/10008) 修复了 `#eval` 的一个错误：点击求值后的表达式时，Infoview 可能显示错误。这是因为 `#eval` 在精化该表达式时没有保存所用的临时环境。

* [#10010](https://github.com/leanprover/lean4/pull/10010) 改进了 `grind cutsat` 对非线性 `/` 和 `%` 的支持。例如，给定 `a / b`，如果 `cutsat` 发现 `b = 2`，它现在会传播出 `a / b = b / 2`。这与 #9996 类似，不过针对的是 `/` 和 `%`。示例：

  ```lean
  example (a b c d : Nat)
      : b > 1 → d = 1 → b ≤ d + 1 → a % b = 1 → a = 2 * c → False := by
    grind
  ```

* [#10020](https://github.com/leanprover/lean4/pull/10020) 为 PR #10010 补上了一个遗漏的分支。

* [#10021](https://github.com/leanprover/lean4/pull/10021) 对 `grind` 标注分析脚本做了一些小改动，包括结果排序与错误处理；外部 UI 仍有待添加。

* [#10022](https://github.com/leanprover/lean4/pull/10022) 改进了 `grind cutsat` 在 `n` 不是数值字面量时对 `Fin n` 的支持。例如，下面的目标现在可以自动求解：

  ```lean
  example (p d : Nat) (n : Fin (p + 1))
      : 2 ≤ p → p ≤ d + 1 → d = 1 → n = 0 ∨ n = 1 ∨ n = 2 := by
    grind

* [#10034](https://github.com/leanprover/lean4/pull/10034) 修改了 “declaration uses 'sorry'” 错误，使其在消息中美观打印实际的 `sorry` 表达式。这样一来，`sorry` 就可以被悬停查看；如果它带有标签，你还可以“转到定义”来查看其来源。

* [#10038](https://github.com/leanprover/lean4/pull/10038) 确保 `grind` 错误消息在引用声明名时使用 `{.ofConstName declName}`。

* [#10060](https://github.com/leanprover/lean4/pull/10060) 让模块系统下“哪些派生实例拥有暴露定义”可以被更细粒度地控制：处理器不应暴露其实现，除非派生项本身或外围的 `section` 之一被标记为 `@[expose]`。内建处理器会在第 0 阶段更新后跟进调整。

* [#10069](https://github.com/leanprover/lean4/pull/10069) 为 `grind linarith` 添加了支持 `NatModule` 的辅助定理。

* [#10071](https://github.com/leanprover/lean4/pull/10071) 改进了 `grind cutsat` 对 `a^n` 的支持。例如，如果 `cutsat` 发现 `a` 和 `b` 都等于某个数值字面量，它现在会传播相应的等式。这与 #9996 类似，不过处理的是 `a^b`。示例：

  ```lean
  example (n : Nat) : n = 2 → 2 ^ (n+1) = 8 := by
    grind
  ```

* [#10085](https://github.com/leanprover/lean4/pull/10085) 为 `rawIdent` 解析器添加了解析器别名，使它可以用于 `Init` 中的 `syntax` 声明。

* [#10093](https://github.com/leanprover/lean4/pull/10093) 为 `grind` 中一个即将实现、支持结合与交换运算符的新求解器添加了背景定理。

* [#10095](https://github.com/leanprover/lean4/pull/10095) 修改 `grind` 的代数类型类，使其使用 `SMul x y` 取代 `HMul x y y`。

* [#10105](https://github.com/leanprover/lean4/pull/10105) 为 `grind` 增加了检测结合运算符的能力。新的 AC 模块还会检测该运算符是否满足交换性、幂等性，以及是否具有中性元；这些信息都会被缓存。

* [#10113](https://github.com/leanprover/lean4/pull/10113) 弃用 `.toCtorIdx`，改用命名更自然的 `.ctorIdx`（并同步更新标准库）。

* [#10120](https://github.com/leanprover/lean4/pull/10120) 修复了一个问题：使用广义字段记号（点记号）递归调用私有定义时，会报出 “invalid field” 错误。它还修复了另一处问题：`invalid field notation` 错误会把声明名带着 `_private` 前缀一起美观打印出来。

* [#10125](https://github.com/leanprover/lean4/pull/10125) 允许 `#guard_msgs` 通过配置选项 `(positions := true)` 报告已记录消息的相对位置。

* [#10129](https://github.com/leanprover/lean4/pull/10129) 将 `Grind` 使用的临时序类型类替换为 `Std` 中新公开的类型类。

* [#10134](https://github.com/leanprover/lean4/pull/10134) 让函数归纳原理的生成在用户使用 `let` 绑定某个随后会被 `match` 的变量时更稳健。修复 #10132。

* [#10135](https://github.com/leanprover/lean4/pull/10135) 让单构造器归纳类型的 `ctorIdx` 定义可以避开无意义的 `.casesOn`，并使用 `macro_inline` 以避免编译该函数并浪费符号。

* [#10141](https://github.com/leanprover/lean4/pull/10141) 回退了 #10135 中关于 `macro_inline` 的那部分改动。

* [#10144](https://github.com/leanprover/lean4/pull/10144) 修改了 `coinductive_fixpoint`/`inductive_fixpoint` 机制中对谓词（即映到 `Prop` 的函数）构造 `CompleteLattice` 实例的方式。

* [#10146](https://github.com/leanprover/lean4/pull/10146) 为 `grind` 中处理 AC 运算符的新过程实现了基础设施。它已经支持对不等性进行归一化；未来的 PR 将增加基于等式做化简以及计算临界对的支持。示例：
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
      : op a (op b c) = op (op a b) c := by
    grind only

* [#10151](https://github.com/leanprover/lean4/pull/10151) 确保在模块系统下，`where finally` 策略只要对应的占位都属于命题类型，即使这些占位位于公开作用域，也仍然可以访问私有数据。

* [#10152](https://github.com/leanprover/lean4/pull/10152) 为 `DecidableEq` 实例引入了另一种构造方式，从而避免默认构造的二次开销。

* [#10166](https://github.com/leanprover/lean4/pull/10166) 重新审视了 `grind` 当前预期失败的测试：把一些现在已经通过的测试移入主测试套件，更新了一些测试，并增加了若干关于指数归一化的测试。

* [#10177](https://github.com/leanprover/lean4/pull/10177) 修复了 #10160 暴露出来的 `grind` 预处理器错误。

* [#10179](https://github.com/leanprover/lean4/pull/10179) 修复了 `grind` 的实例归一化过程。`grind` 中有些模块直接使用核心中定义的内建实例（如 `cutsat`），而另一些模块则通过 `synthInstance` 合成实例（如 `ring`）。这种不一致会引入不匹配，并让同一项出现两种不同表示；该 PR 解决了这一问题。

* [#10183](https://github.com/leanprover/lean4/pull/10183) 让匹配方程在可能时直接用 `rfl` 证明，而不是先显式展开左侧；这可能生成更小的证明。

* [#10185](https://github.com/leanprover/lean4/pull/10185) 为 `grind` 的全部属性修饰符补充了文档（如 `=`、`usr`、`ext` 等）。

* [#10186](https://github.com/leanprover/lean4/pull/10186) 为 `grind ac` 模块添加了化简不等式的支持。

* [#10189](https://github.com/leanprover/lean4/pull/10189) 为新的 `grind ac` 模块实现了证明项。示例：
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
      : op a (op b b) = op c d → op c (op d c) = op (op a b) (op b c) := by
    grind only

* [#10205](https://github.com/leanprover/lean4/pull/10205) 为 `grind ac` 中的结合且交换运算符添加了超位推理支持。示例：

  ```lean
  example (a b c d e f g h : Nat) :
      max a b = max c d → max b e = max d f → max b g = max d h →
      max (max f d) (max c g) = max (max e (max d (max b (max c e)))) h := by
    grind -cutsat only

* [#10206](https://github.com/leanprover/lean4/pull/10206) 为 `grind ac` 中的结合但非交换运算符添加了超位推理支持。示例：
  ```lean
  example {α} (op : α → α → α) [Std.Associative op] (a b c d : α)
     : op a b = c →
       op b a = d →
       op (op c a) (op b c) = op (op a d) (op d b) := by
    grind

* [#10208](https://github.com/leanprover/lean4/pull/10208) 添加了额外的临界对，以确保当运算符同时满足结合性、交换性和幂等性时，`grind ac` 过程仍然完备。示例：
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op]
        (a b c d : α) : op a (op b b) = op d c → op (op b a) (op b c) = op c (op d c)  := by
    grind only
  ```

* [#10221](https://github.com/leanprover/lean4/pull/10221) 添加了额外的关键对，以确保当运算符具有结合性和幂等性但不具有交换性时，`grind ac` 过程仍然完备。示例：
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
      : op d (op x c) = op a b →
        op e (op f (op y w)) = op a (op b c) →
        op d (op x c) = op e (op f (op y w)) := by
    grind only

* [#10223](https://github.com/leanprover/lean4/pull/10223) 实现了把新 AC 模块中的等式传播到 `grind` 核心。示例：

  ```lean
  example {α β : Sort u} (f : α → β) (op : α → α → α) [Std.Associative op] [Std.Commutative op]
      (a b c d : α) : op a (op b b) = op d c → f (op (op b a) (op b c)) = f (op c (op d c)) := by
    grind only

* [#10230](https://github.com/leanprover/lean4/pull/10230) 为更多单子变换器添加了 `MonoBind`。这使 `partial_fixpoint` 可以用于基于 `Option` 和 `EIO` 的更复杂单子。示例：
  ```lean-4
  abbrev M := ReaderT String (StateT String.Pos Option)

* [#10237](https://github.com/leanprover/lean4/pull/10237) 修复了 `grind` 规范化器中的一个缺失分支。有些类型可能包含稍后才会被内部化到 `grind` 状态中的项或命题。

* [#10239](https://github.com/leanprover/lean4/pull/10239) 修复了针对含有未被常规参数引用的宇宙参数之定理的 E-匹配过程。这类定理在实践中不常见，但标准库中确实存在。示例：
  ```
  @[simp, grind =] theorem Std.Do.SPred.down_pure {φ : Prop} : (⌜φ⌝ : SPred []).down = φ := rfl
  ```

* [#10241](https://github.com/leanprover/lean4/pull/10241) 添加了一些 `grind` 配合 `Fin` 工作的测试用例。`tests/lean/grind/grind_fin.lean` 中仍有许多失败测试，我打算继续分拣和处理。

* [#10245](https://github.com/leanprover/lean4/pull/10245) 修改了（协）归纳谓词机制中使用的函数 `unfoldPredRel` 的实现，它会把谓词上的逐点序展开为量化与蕴含。此前的实现依赖 `withDeclsDND`，而它无法处理互相依赖的类型。这导致下面的示例失败：

  ```lean4
  inductive infSeq_functor1.{u} {α : Type u} (r : α → α → Prop) (call : {α : Type u} → (r : α → α → Prop) → α → Prop) : α → Prop where
    | step : r a b → infSeq_functor1 r call b → infSeq_functor1 r call a

* [#10265](https://github.com/leanprover/lean4/pull/10265) 修复了 #10242 暴露出来的 `grind ring` 崩溃。`grind ring` 不应假定所有归一化都已经完成，因为受类型约束所限，`simp` 无法改写某些子项。此外，`grind` 在少数地方会使用 `preprocessLight`，而它会跳过简化器/归一化器。

* [#10267](https://github.com/leanprover/lean4/pull/10267) 实现了在 `grind linarith` 中支持 `NatModule` 的基础设施，并用它处理不等性。后续 PR 还会增加对等式与不等式的支持。示例：
  ```lean
  open Lean Grind
  variable (M : Type) [NatModule M] [AddRightCancel M]

* [#10269](https://github.com/leanprover/lean4/pull/10269) 修改了字符串插值过程，使其省略冗余的空片段。例如，`s!"{1}{2}"` 过去会精译成 `toString "" ++ toString 1 ++ toString "" ++ toString 2 ++ toString ""`，现在则会精译成 `toString 1 ++ toString 2`。

* [#10271](https://github.com/leanprover/lean4/pull/10271) 修改了 `BEq` 这类派生实例内部函数的命名方式，使其使用可访问的名称。这样更便于对这些函数进行证明。例如，对类型 `T` 执行 `deriving BEq` 之后，`instBEqT` 的实现位于 `instBEqT.beq`。

* [#10273](https://github.com/leanprover/lean4/pull/10273) 尝试正确处理 `same-ctor-match` 结构的可见性。

* [#10274](https://github.com/leanprover/lean4/pull/10274) 修改了线性 `DecidableEq` 实现的写法：在比较构造器标签时改用 `match decEq`，而不是 `if h : `。否则，“智能展开”机制无法让 `rfl` 判定不同构造器彼此不同。

* [#10277](https://github.com/leanprover/lean4/pull/10277) 为 `OfNatModule.Q α` 补上了缺失的 `IsPartialOrder`、`IsLinearPreorder` 与 `IsLinearOrder` 实例。

* [#10278](https://github.com/leanprover/lean4/pull/10278) 在 `grind linarith` 中加入了对 `NatModule` 等式与不等式的支持。示例：
  ```lean
  open Lean Grind Std

* [#10280](https://github.com/leanprover/lean4/pull/10280) 添加了辅助定理 `Lean.Grind.Linarith.eq_normN`，用于在 `AddRightCancel` 实例不可用时归一化 `NatModule` 等式。

* [#10281](https://github.com/leanprover/lean4/pull/10281) 在 `AddRightCancel` 实例不可用时实现了 `NatModule` 的归一化。请注意，此时嵌入到 `IntModule` 并不是单射。因此，我们使用了一个自定义归一化器，类似于 `grind ring` 模块中 `CommSemiring` 所用的归一化器。示例：

  ```lean
  open Lean Grind
  example [NatModule α] (a b c : α)
      : 2•a + 2•(b + 2•c) + 3•a = 4•a + c + 2•b + 3•c + a := by
    grind
  ```

* [#10282](https://github.com/leanprover/lean4/pull/10282) 改进了 `grind linarith` 为 `NatModule` 生成的反例。`grind` 现在会隐藏辅助函数 `Grind.IntModule.OfNatModule.toQ` 的出现。

* [#10283](https://github.com/leanprover/lean4/pull/10283) 为 `grind ac` 模块实现了诊断信息。它现在会显示基、归一化后的不等性，以及为每个结合运算符检测到的附加性质。

* [#10290](https://github.com/leanprover/lean4/pull/10290) 为注册新的 `grind` 求解器增加了基础设施。`grind` 已经包含许多求解器，而这个 PR 是迈向模块化设计和支持用户自定义求解器的第一步。

* [#10294](https://github.com/leanprover/lean4/pull/10294) 完成了 `grind` 求解器扩展机制的设计，并将 `grind ac` 求解器迁移到新框架。未来的 PR 会为 API 补充文档，并迁移其余求解器。新设计的另一项好处是构建时间更快。

* [#10296](https://github.com/leanprover/lean4/pull/10296) 修复了 `grind cutsat` 中一个用于构造证明项的辅助函数错误。

* [#10300](https://github.com/leanprover/lean4/pull/10300) 为 `noConfusion` 的非对角用法（也就是不同构造器之间的情形）提供了另一种基于比较 `.ctorIdx` 的构造方式。这应当会带来更快的类型检查，因为内核只需约化 `.ctorIdx` 两次，而不必处理复杂的 `noConfusionType` 构造。

* [#10301](https://github.com/leanprover/lean4/pull/10301) 暴露了 `ctorIdx` 以及按构造器区分的消去器。修复 #10299。

* [#10306](https://github.com/leanprover/lean4/pull/10306) 修复了 `rw` 策略中的几个错误：它此前可能因为目标出现在重写类型里而“偷走”目标，也没有执行出现检查，且新生成的证明目标不会是合成不透明的。该 PR 还让 `rfl` 策略能够给合成不透明元变量赋值，从而与 `exact rfl` 等价。

* [#10307](https://github.com/leanprover/lean4/pull/10307) 将 Verso 解析器上游合入，并为在文档字符串中使用 Verso 添加了初步支持。这将允许编译器检查文档里的示例和交叉引用。

* [#10309](https://github.com/leanprover/lean4/pull/10309) 修改了 `simpa` 策略，使得在 `simpa ... using e` 中，范围 `simpa ... using` 上会附带策略信息，以显示化简后的目标。

* [#10313](https://github.com/leanprover/lean4/pull/10313) 为 `natCast` 和 `intCast` 添加了缺失的 `grind` 归一化规则。示例：
  ```
  open Lean.Grind
  variable (R : Type) (a b : R)

* [#10314](https://github.com/leanprover/lean4/pull/10314) 会在实例上跳过基于模型的理论组合。

* [#10315](https://github.com/leanprover/lean4/pull/10315) 添加了 `T.ctor.noConfusion` 声明，它们是 `T.noConfusion` 在 `T.ctor` 之间等式上的特化。目的是避免每次使用 `injection` 或类似策略时都去约化 `T.noConfusionType` 的构造。

* [#10316](https://github.com/leanprover/lean4/pull/10316) 共享了处理同一构造器之间等式以及判断这些等式类型是否正确的通用功能。具体而言，它也在 `CasesOnSameCtor` 以及 `BEq`、`DecidableEq`、`Ord` 的派生代码等位置使用 `mkInjectivityThm` 中更完整的逻辑，从而提升一致性并改进错误消息。

* [#10321](https://github.com/leanprover/lean4/pull/10321) 确保 `grind` 所用 E-匹配模块创建的辅助临时元变量 ID 不受调用 `grind` 之前已执行内容的影响，目的是提升 `grind` 的稳健性。

* [#10322](https://github.com/leanprover/lean4/pull/10322) 为 `grind` 引入功能受限的前端 `cutsat` 和 `grobner`。我们禁用了定理实例化（`grobner` 还禁用了分情况拆分），并关闭所有其他求解器。二者仍允许 `grind` 的配置项，因此例如可以用 `cutsat +ring`（或 `grobner +cutsat`）解决同时需要两者的问题。

* [#10323](https://github.com/leanprover/lean4/pull/10323) 修复了 `grind` 对 `OfNat.ofNat` 应用的规范化器。示例：
  ```lean
  example {C : Type} (h : Fin 2 → C) :
      -- `0` in the first `OfNat.ofNat` is not a raw literal
      h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by
    grind
  ```

* [#10324](https://github.com/leanprover/lean4/pull/10324) 禁用了一个会触发昂贵类型类搜索的未使用实例。

* [#10325](https://github.com/leanprover/lean4/pull/10325) 为实现 `ToInt` 接口的类型 `A` 实现了基于模型的理论组合。示例：
  ```lean
  example {C : Type} (h : Fin 4 → C) (x : Fin 4)
      : 3 ≤ x → x ≤ 3 → h x = h (-1) := by
    grind

* [#10326](https://github.com/leanprover/lean4/pull/10326) 修复了 `grind linarith` 中的一个性能问题。它此前会为无序的交换环构造多余的 `NatModule`/`IntModule` 结构；这类类型本应只交给 `grind ring` 处理。

* [#10331](https://github.com/leanprover/lean4/pull/10331) 用 Lean 而不是 C 实现了 `mkNoConfusionImp`。这减少了我们对 C 的依赖，并可能带来性能收益，因为它避免了在精译期间约化 `noConfusionType`（不过内核在类型检查时仍会约化它）。

* [#10332](https://github.com/leanprover/lean4/pull/10332) 确保信息树在 `classical` 策略之下会把 `Classical.propDecidable` 识别为实例。

* [#10335](https://github.com/leanprover/lean4/pull/10335) 修复了 `grind` 中的嵌套证明项检测；它必须检查工具项 `Grind.nestedProof` 是否被过度应用。

* [#10342](https://github.com/leanprover/lean4/pull/10342) 实现了新的 E-匹配模式推断过程，使其符合参考手册中关于“最小可索引子表达式”的记录行为。旧的推断过程没有落实这一条件。例如，手册中对 `[grind ->]` 的说明如下。

* [#10373](https://github.com/leanprover/lean4/pull/10373) 添加了 `pp.unicode` 选项，以及底层解析器 `unicodeSymbol "→" "->"` 的语法说明别名 `unicode("→", "->")`。这一语法也被加入到了 `notation` 命令中。当 `pp.unicode` 为真（默认值）时，美观打印会使用第一种形式；否则使用第二种 ASCII 形式。变体 `unicode("→", "->", preserveForPP)` 会让 `->` 形式成为首选；反精译器也可以直接在语法中插入 `→`，并按原样美观打印。这使得 `fun` 一类记号能够使用 `pp.unicode.fun` 之类的自定义选项，在美观打印时选择 Unicode 形式。

````
# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Library"
%%%

````markdown

* [#7858](https://github.com/leanprover/lean4/pull/7858) 实现了用于无符号乘法溢出检测的快速电路；Bitwuzla 采用了这一方案，提出它的论文如下： https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=987767

* [#9127](https://github.com/leanprover/lean4/pull/9127) 让 `saveModuleData` 在收到无法序列化的对象时抛出 `IO.Error`，而不是直接崩溃。这对保存模块本身影响不大，但在编写工具、通过 Batteries 的 `pickle` 往 olean 文件里保存辅助数据时很有用。

* [#9560](https://github.com/leanprover/lean4/pull/9560) 修复了 `forIn` 函数：此前如果其内部抛出异常，得到的 `Promise` 会被丢弃而没有值。它还修正了 `background` 函数的参数顺序。

* [#9599](https://github.com/leanprover/lean4/pull/9599) 添加了类型 `Std.Internal.Parsec.Error`，其中包含构造器 `.eof`（可用于判断解析是否因为输入不足而失败，从而在输入继续到来时重试，这对 HTTP 服务器很有用）与 `.other`（用于描述其他错误）。它还为许多函数补上了文档，并为 `ByteArray` Parsec 新增了一些函数，如 `peekWhen?`、`octDigit`、`takeWhile`、`takeUntil`、`skipWhile` 与 `skipUntil`。

* [#9632](https://github.com/leanprover/lean4/pull/9632) 为 `TreeMap` 的 `filter`、`map` 与 `filterMap` 操作添加了引理。这些引理原本已经存在于 `HashMap`，这里只是把对应内容移植过来。

* [#9685](https://github.com/leanprover/lean4/pull/9685) 验证了 `HashMap` 的 `toArray` 及其相关函数。

* [#9797](https://github.com/leanprover/lean4/pull/9797) 提供了一种快速批量给出高层序结构（预序、偏序、线性预序、线序）相关全部序实例的方法，可通过工厂函数 `PreorderPackage.ofLE`、`PartialOrderPackage.ofLE`、`LinearPreorderPackage.ofLE` 与 `LinearOrderPackage.ofLE` 实现。

* [#9908](https://github.com/leanprover/lean4/pull/9908) 让 `IsPreorder`、`IsPartialOrder`、`IsLinearPreorder` 与 `IsLinearOrder` 视需要扩展 `BEq` 和 `Ord`，新增把 `BEq`、`Ord` 同 `LE` 关联起来的类型类 `LawfulOrderBEq` 与 `LawfulOrderOrd`，并加入了大量引理与实例。

* [#9916](https://github.com/leanprover/lean4/pull/9916) 提供了可在给定 `Ord` 实例时批量派生序类型类的工厂。如果已有实例存在，则优先使用现有实例，而不是使用由 `Ord` 派生出的实例；如有需要，也可以手动指定任意实例。

* [#9924](https://github.com/leanprover/lean4/pull/9924) 修复了 `PostCond` 文档中的示例。

* [#9931](https://github.com/leanprover/lean4/pull/9931) 实现了 `Std.Do.Triple.mp`，使用户可以把同一程序的两个规格组合起来。

* [#9949](https://github.com/leanprover/lean4/pull/9949) 让大多数 `List.lookup` 引理在 `LawfulBEq α` 不可用时也能使用。

* [#9957](https://github.com/leanprover/lean4/pull/9957) 将来自 Batteries 的 `Rat` 定义上游合入，以供我们计划中的区间算术策略使用。

* [#9967](https://github.com/leanprover/lean4/pull/9967) 从 `SpecLemmas.lean` 中移除了本地 `Triple` 记号，以绕开一个会破坏第 2 阶段构建的错误。

* [#9979](https://github.com/leanprover/lean4/pull/9979) 用从 Batteries 上游合入的公共 `Rat` 替换 `Std.Internal.Rat`。

* [#9987](https://github.com/leanprover/lean4/pull/9987) 改进了证明基于 `Nat` 的 `PRange` 元素满足界限条件的策略，使其改为依赖 `omega` 策略。

* [#9993](https://github.com/leanprover/lean4/pull/9993) 定义了二进有理数，并证明它们构成一个可嵌入到有理数中的有序环。我们将把它用于未来的区间算术策略。

* [#9999](https://github.com/leanprover/lean4/pull/9999) 减少了我们为处理分配律而添加的 `Nat.Bitwise` `grind` 标注数量。新的较小标注集会鼓励 `grind` 重写到 DNF；旧行为只会让实例化很快达到上限。

* [#10000](https://github.com/leanprover/lean4/pull/10000) 删除了一条会在所有 `Option.map` 上触发的 `grind` 标注，它会造成雪崩式的实例化。

* [#10005](https://github.com/leanprover/lean4/pull/10005) 缩短了让某个类型兼容多态区间记号所需的工作量。以 `Nat` 为例，它将所需代码行数从 150 行减少到了 70 行。

* [#10015](https://github.com/leanprover/lean4/pull/10015) 暴露了 `Name.append`、`Name.appendCore` 与 `Name.hasMacroScopes` 的定义体。这使得在模块系统下可以通过反射证明名称字面量的拼接。

* [#10018](https://github.com/leanprover/lean4/pull/10018) 为 `Lean.Import` 派生了 `BEq` 与 `Hashable`。Lake 之前稍后才会这样做；现在在定义 `Import` 时就会完成。

* [#10019](https://github.com/leanprover/lean4/pull/10019) 为 `Lean.ParserState.setPos` 添加了 `@[expose]`。这使得对 `setPos` 产生的状态，为 `next'` 和 `get'` 之类函数证明有界性时，无需 `import all`。

* [#10024](https://github.com/leanprover/lean4/pull/10024) 为 `LawfulOrderMin/Max` 与 `LawfulOrderLeftLeaningMin/Max` API 添加了有用声明。尤其是，它为 `Min` 与 `Max` 引入了 `.leftLeaningOfLE` 工厂，还把 `LawfulOrderMin/Max.of_le` 重命名为 `.of_le_min_iff` 与 `.of_max_le_iff`，并新增了一个参数不同的第二变体。

* [#10045](https://github.com/leanprover/lean4/pull/10045) 实现了让区间记号适用于整数所需的类型类。例如，`((-2)...3).toList = [-2, -1, 0, 1, 2] : List Int`。

* [#10049](https://github.com/leanprover/lean4/pull/10049) 为在 #9993 中引入二进有理数补充了一些所需的背景材料。

* [#10050](https://github.com/leanprover/lean4/pull/10050) 修复了 `Data/Rat/Lemmas` 中的一些命名问题，并将消去器 `numDenCasesOn` 及其相关项上游合入。

* [#10059](https://github.com/leanprover/lean4/pull/10059) 改进了多态区间 API 中定义与引理的命名，并引入了推荐写法。例如，左闭右开的区间会参照 Mathlib 中的 `Ico` 记号，写作 `Rco`。

* [#10075](https://github.com/leanprover/lean4/pull/10075) 加入了一些关于 `Int` 的引理（以及对 `BitVec` 和 `Nat` 的少量修订），它们会用于为二进有理数做准备。这部分工作都来自 @Rob23oba；我把它从 #9993 中提前拆出来，以便让那个 PR 更易于处理。

* [#10077](https://github.com/leanprover/lean4/pull/10077) 将 `Mathlib.Data.Rat.Defs` 与 `Mathlib.Algebra.Order.Ring.Unbundled.Rat` 中关于 `Rat` 的引理上游合入，具体数量足以得到 `Lean.Grind.Field Rat` 和 `Lean.Grind.OrderedRing Rat`。除了这些引理外，还上游合入了 `Inv Rat`、`Pow Rat Nat` 与 `Pow Rat Int` 的实例。

* [#10107](https://github.com/leanprover/lean4/pull/10107) 为 `Rat` 添加了 `Lean.Grind.AddCommGroup` 实例。

* [#10138](https://github.com/leanprover/lean4/pull/10138) 添加了关于 `Dyadic.roundUp` 与 `Dyadic.roundDown` 运算的引理。

* [#10159](https://github.com/leanprover/lean4/pull/10159) 为所有 `Map` 变体添加了 `nodup_keys` 引理，作为现有 `distinct_keys` 的推论。

* [#10162](https://github.com/leanprover/lean4/pull/10162) 去掉了会过于频繁、且往往无益地触发的 `grind →` 标注。理想情况下，`grind` 只有在已经看见 `xs ++ ys` 与 `#[]` 处在同一个等价类中时，才应实例化这些引理，而不是一看到 `xs ++ ys` 就立即实例化。

* [#10163](https://github.com/leanprover/lean4/pull/10163) 删除了一些（希望确实是）不必要、但会导致实例化爆炸的 `grind` 标注。

* [#10173](https://github.com/leanprover/lean4/pull/10173) 从 `MonadAwait` 与 `MonadAsync` 中移除了 `extends Monad`，以避免实例欠定。

* [#10182](https://github.com/leanprover/lean4/pull/10182) 为 `Nat.fold` 与 `Nat.foldRev` 在求和上的行为添加了引理，以匹配现有关于 `dfold` 和 `dfoldRev` 的定理。

* [#10194](https://github.com/leanprover/lean4/pull/10194) 添加了给定精度下二进有理数的逆元及其刻画引理；它还清理了 `Int.DivMod` 与 `Rat` API 的若干部分，并证明了一些关于 `Rat.toDyadic` 的刻画引理。

* [#10216](https://github.com/leanprover/lean4/pull/10216) 修复了 #10193。

* [#10224](https://github.com/leanprover/lean4/pull/10224) 将 `HashMap`、`TreeMap` 与 `HashSet` 的单子化操作泛化为可适用于 `m : Type u → Type v`。

* [#10227](https://github.com/leanprover/lean4/pull/10227) 为 `ReaderT`、`StateT` 与 `ExceptT` 添加了 `@[grind]` 标注（几乎全部都是同现有 `@[simp]` 平行的 `@[grind =]` 标注）。

* [#10244](https://github.com/leanprover/lean4/pull/10244) 为区间和迭代器的 `toList` 与 `toArray` 函数添加了更多引理，同时将 `Array.mem_toArray` 重命名为 `List.mem_toArray`。

* [#10247](https://github.com/leanprover/lean4/pull/10247) 为所有容器类型补上了缺失的引理 `ofList_eq_insertMany_empty`、`get?_eq_some_iff`、`getElem?_eq_some_iff` 与 `getKey?_eq_some_iff`。

* [#10250](https://github.com/leanprover/lean4/pull/10250) 修复了 `LinearOrderPackage.ofOrd` 工厂中的一个错误。如果有 `LawfulEqOrd` 实例可用，它应自动使用它，而不是要求用户向工厂提供 `eq_of_compare` 参数。该 PR 还解决了一个与卫生相关的问题：当 `Std` 未打开时，这些工厂会失败。

* [#10303](https://github.com/leanprover/lean4/pull/10303) 为 `BitVec` 与 `UInt*` 类型加入了区间支持。这意味着现在可以写出例如 `for i in (1 : UInt8)...5 do` 这样的代码，以遍历类型为 `UInt8` 的值 1、2、3 和 4。

* [#10341](https://github.com/leanprover/lean4/pull/10341) 将 `Function.Injective` 与 `Function.Surjective` 的定义和基本事实从 Mathlib 上游合入。有了这些内容后，我们在 `grind` 中基于单射性进行推理时可以做得更好。

````
# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Compiler"
%%%

````markdown

* [#9631](https://github.com/leanprover/lean4/pull/9631) 让 `IO.RealWorld` 变为不透明。它还新增了一个仅供编译器使用的常量 `lcRealWorld`，用于在编译器内部表示该类型。默认情况下，不透明类型定义会被当作 `lcAny` 处理，而这里我们希望得到更高效的表示。目前差别还不大，但未来我们希望在运行时把 `IO.RealWorld` 完全抹除。

* [#9922](https://github.com/leanprover/lean4/pull/9922) 修改了 `internalizeCode`：它会把 `Expr` 中（这些位置全都是类型）所有带有非参数绑定自由变量的替换项都替换为 `lcAny`，从而保持“不存在此类依赖”的不变式。这个不变式在文件之间被破坏曾导致一个待合并 PR 中的测试失败，但很难为它写出直接测试。未来我们或许应当让 LCNF 检查器能够检测这一点。

* [#9972](https://github.com/leanprover/lean4/pull/9972) 修复了把 Mathlib 的 `FintypeCat` 当作代码运行时出现的一个问题：某个被擦除的类型构造器会被传给多态函数。此前我们把箭头类型下调为 `object`，这会与运行时把被擦除值表示为带标签标量的方式发生冲突。

* [#9977](https://github.com/leanprover/lean4/pull/9977) 增加了对子单例谓词之 `casesOn` 递归器的编译支持。

* [#10023](https://github.com/leanprover/lean4/pull/10023) 添加了支持，以正确处理支持大消去的归纳谓词在 `casesOn` 上的字段计算。对这类谓词，唯一允许的相关字段是同时也被用作索引的那些，此时我们可以找到给定的索引并改用那个项。

* [#10032](https://github.com/leanprover/lean4/pull/10032) 修改了在把 LCNF 下调到 IR 时对过度应用构造器的处理方式：从（稍显隐式的）断言失败改为生成 `unreachable`。对内联的不可达代码做变换时，可能会产生带额外参数的构造器应用。

* [#10040](https://github.com/leanprover/lean4/pull/10040) 修改了 `toMono` 阶段：它会用声明的 `_redArg` 等价物替换原声明，因此在进行 `noncomputable` 检查时，不再把被 `reduceArity` 阶段判定为无用的参数纳入考虑。

* [#10070](https://github.com/leanprover/lean4/pull/10070) 修复了 `noConfusion` 的编译问题，补上了从旧编译器移植这段代码时遗漏的一点：旧编译器只会针对所讨论归纳类型的每个非 `Prop` 输入字段反复展开主参数，这与 `noConfusion` 自身的构造相呼应；而新编译器此前错误地统计了所有字段。

* [#10133](https://github.com/leanprover/lean4/pull/10133) 修复了 Lean 生成的可执行文件在 Windows 上对 Unicode 文件系统路径的兼容性。

* [#10214](https://github.com/leanprover/lean4/pull/10214) 修复#10213。

* [#10256](https://github.com/leanprover/lean4/pull/10256) 修正了 `toIR` 中的一个错误：它可能会过度应用某个具有 IR 声明、但没有 mono 声明的函数。

* [#10355](https://github.com/leanprover/lean4/pull/10355) 修改了 `toLCNF`，使其把内建类型上的 `.proj` 转换为改用投影函数。

````
# 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Pretty-Printing"
%%%

````markdown

* [#10122](https://github.com/leanprover/lean4/pull/10122) 增加了使用广义字段记号（点记号）来美观打印公有类型上的私有定义之支持。它还修改了点记号的精译方式：在去掉私有前缀后再解析名称，从而允许对私有导入类型上的私有定义使用点记号。

* [#10373](https://github.com/leanprover/lean4/pull/10373) 添加了 `pp.unicode` 选项，以及底层解析器 `unicodeSymbol "→" "->"` 的语法说明别名 `unicode("→", "->")`。这一语法也被加入到了 `notation` 命令中。当 `pp.unicode` 为真（默认值）时，美观打印会使用第一种形式；否则使用第二种 ASCII 形式。变体 `unicode("→", "->", preserveForPP)` 会让 `->` 形式成为首选；反精译器也可以直接在语法中插入 `→`，并按原样美观打印。这使得 `fun` 一类记号能够使用 `pp.unicode.fun` 之类的自定义选项，在美观打印时选择 Unicode 形式。

* [#10374](https://github.com/leanprover/lean4/pull/10374) 添加了选项 `pp.piBinderNames` 与 `pp.piBinderNames.hygienic`。启用 `pp.piBinderNames` 后，非依赖的 Π 绑定器名称会被美观打印出来，而不再省略；当 `pp.piBinderNames.hygienic` 为假（默认值）时，只会美观打印其中非卫生的这类绑定器名称。若未显式设置，`pp.all` 会启用 `pp.piBinderNames`。

````
# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Documentation"
%%%

````markdown

* [#9956](https://github.com/leanprover/lean4/pull/9956) 为 `let` 与 `have` 策略的文档字符串补充了更多信息，包括不透明性、各自适用时机以及相关策略。

````
# 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Server"
%%%

````markdown

* [#9966](https://github.com/leanprover/lean4/pull/9966) 调整了 “try this” 小部件的呈现方式：它现在会作为 `Messages` 下方的一条小部件消息显示，而不是作为 `Suggestions` 区域下的独立小部件显示。这样做的主要好处是，这条消息不再会在 `Messages` 和 `Suggestions` 之间重复出现。

* [#10047](https://github.com/leanprover/lean4/pull/10047) 确保悬停在 `match` 上时会显示该 `match` 的类型。

* [#10052](https://github.com/leanprover/lean4/pull/10052) 修复了一个错误：它会导致 Lean 服务器的进程树在关闭 VS Code 后仍然存活。

* [#10249](https://github.com/leanprover/lean4/pull/10249) 通过语言服务器中的多项性能改进，把自动补全速度提升到了约 3.5 倍。在某台机器上，`import Mathlib` 后补全 `i` 过去需要 3200ms，现在则只需 920ms。

````
# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Lake"
%%%

````markdown

* [#9749](https://github.com/leanprover/lean4/pull/9749) 重构了 Lake 代码库，使其全面采用新的模块系统。`Lake` 中的每个模块现在都是真正的 `module`。

* [#10276](https://github.com/leanprover/lean4/pull/10276) 将 `verLit` 语法移入 `Lake.DSL` 命名空间，以与 `Lake.DSL` 中的其他代码保持一致。

````
# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Other"
%%%

````markdown

* [#10043](https://github.com/leanprover/lean4/pull/10043) 允许 Lean 的解析器在最终位置早于字符串末尾时运行，从而可以在输入的某个子区域上调用它。

* [#10217](https://github.com/leanprover/lean4/pull/10217) 确保 `@[init]` 声明（例如 `initialize` 生成的那些）在导入时会按声明顺序运行。

* [#10262](https://github.com/leanprover/lean4/pull/10262) 新增选项 `maxErrors`，用于限制单次 `lean` 运行时输出的错误条数，默认值为 100。达到上限后会中止处理，但这一限制只按单个命令层级进行统计。


````
