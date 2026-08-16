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
本次发布共合入 377 项改动。除下文列出的 105 项功能新增和 75 项修复外，还有 25 项重构、9 项文档改进、21 项性能改进、4 项测试套件改进，以及 138 项其他改动。

## 亮点
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights"
%%%

Lean 4.24.0 持续改进了模块系统和验证框架，增强了 `grind` 策略，并推进了标准库的发展。本次发布还引入了更高效的 `DecidableEq` 实例和 `noConfusion` 构造（[#10152](https://github.com/leanprover/lean4/pull/10152) 与 [#10300](https://github.com/leanprover/lean4/pull/10300)），从而优化编译。

作为我们持续改进性能的一个例子：

- [#10249](https://github.com/leanprover/lean4/pull/10249) 通过改进语言服务器的多处性能表现，将自动补全速度提升到了约 3.5 倍。

和往常一样，本次也包含大量错误修复和新特性，下面列出其中一部分：

### “try this” 建议显示在 “Messages” 下方
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--___Try-this___-suggestions-are-rendered-under-___Messages___"
%%%

- [#9966](https://github.com/leanprover/lean4/pull/9966) 调整了 “try this” 小部件的呈现方式：它现在显示为 `Messages` 下方的一条小部件消息，而不是 `Suggestions` 区域下单独的小部件。这样做的主要好处是，这条消息不会再在 `Messages` 和 `Suggestions` 之间重复显示。

### `mvcgen` 中的 `invariants` 与 `with` 小节
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--invariants-and-with-sections-in-mvcgen"
%%%

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

### 库：二进有理数
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Library___-Dyadic-rationals"
%%%

- [#9993](https://github.com/leanprover/lean4/pull/9993) 定义了二进有理数，并证明它们构成一个可嵌入到有理数中的有序环。

### `grind` AC 求解器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Grind-AC-solver"
%%%

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

### 元编程说明
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Metaprogramming-notes"
%%%

- [#10306](https://github.com/leanprover/lean4/pull/10306)在`rw` 战术中修补了几个错误。

代之以`Lean.MVarId.rewrite`取代`Lean.Elab.Tactic.elabRewrite`
用于拟订重写定理和对表达式进行重写。

### 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Highlights--Breaking-changes"
%%%

- [#9749](https://github.com/leanprover/lean4/pull/9749) 将 Lake 代码库全面重构为使用新的模块系统。`Lake` 中的每个模块现在都是真正的 `module`。

  **破坏性变更：** 由于模块系统鼓励采用“默认 `private`”的设计，Lake API 已经从先前“默认 `public`”的做法切换过来。因此，许多以前公开的定义现在都变成了私有。
预计用户不会大量使用,不过,重要的使用案例可能会错过。
如果关键 API 现在无法进入, 但似乎应该公开, 鼓励用户使用
将此作为GitHub的一个问题提出报告。

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Language"
%%%

* [#8891](https://github.com/leanprover/lean4/pull/8891) 改进通过时产生的错误信息(自动)
当地假设为`grind`。

* [#9651](https://github.com/leanprover/lean4/pull/9651) 修改了通过 `partial_fixpoint` 定义的 `mutual` 块所生成的归纳引理与部分正确性引理。此外，还修改了通过 `mutual` 块为函数生成格论归纳原理的方式，使其与 `partial_fixpoint` 保持一致。

* [#9674](https://github.com/leanprover/lean4/pull/9674)清除`optParam`/`autoParam`/etc。
拟订定义机构、理论机构、`fun` 机构和`let`
声明信头中的`variable`和粘合符均为
支持 。

* [#9918](https://github.com/leanprover/lean4/pull/9918) 防止`rcases` 和`obtain` 制造荒谬冗长的案件
将单个构建器类型( 如 `Exists` ) 分开时使用标记名称 。
修复#6550

* [#9923](https://github.com/leanprover/lean4/pull/9923) 为一个会导致 doc-gen4 崩溃的反精译器添加了防护。这目前只是权宜之计，@sgraf812 休假回来后会进一步检查。

* [#9926](https://github.com/leanprover/lean4/pull/9926) 为 `Std.Tactic.Do.MGoalEntails` 反精译器添加检查，确保至少存在三个参数，从而防止潜在崩溃。

* [#9927](https://github.com/leanprover/lean4/pull/9927) 为 `mvcgen` 实现了扩展的、受 `induction` 启发的语法，允许可选的 `using invariants` 与 `with` 小节。

* [#9930](https://github.com/leanprover/lean4/pull/9930) 回退了 `grind cutsat` 将 `Nat.sub` 嵌入 `Int` 的方式。它修复了 David Renshaw 在 Zulip 上报告的一个回归。

* [#9938](https://github.com/leanprover/lean4/pull/9938)删除了重复的`mpure_intro` 战术定义。

* [#9939](https://github.com/leanprover/lean4/pull/9939) 将 `mvcgen using invariants | $n => $t` 展开为 `mvcgen; case inv<$n> => exact $t`，以避免在 #9581 的测试用例中可观察到的 MVar 实例化失误。

* [#9942](https://github.com/leanprover/lean4/pull/9942) 修改`intro`,以创建适合每个
(`intro`)的假设,从而有可能了解`intro`如何工作
可变变量。此外:
  - 该策略支持`intro rfl`引入平等和
立即替换,如`rintro rfl`(回顾:`rfl`模式)
`rintro` 战术现在也可以了
如果`eq_of_heq`适用,则`rfl` 模式中的`HEq`支持。
  - `intro (h : t)`中`t`的`t`的拟订与[统一]
`h` 类型,防止默认情况引起
无法统一。
  - 改变假设类型的策略(包括`intro (h : t)`),
`delta`,`dsimp`)现在更新本地例缓存。

* [#9945](https://github.com/leanprover/lean4/pull/9945) 优化`grind cutsat` 产生的证明条件。
生成最终证明时上下文对象中未使用的条目,
按照由此得出的条件,大量减少垃圾数量。
示例:
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

* [#9946](https://github.com/leanprover/lean4/pull/9946) 优化`grind ring` 产生的证明条件。
类似#9945, 但对于 `grind` 中的环模 。
它在生成上下文对象时从上下文对象中删除未使用的条目
最终证明,显著减少垃圾数量,导致
术语. 示例:
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

* [#9947](https://github.com/leanprover/lean4/pull/9947) 优化`grind linarith` 产生的证明条件。
类似#9945, 但对于 `grind` 中的 `linarith` 模块而言。
它在生成上下文对象时从上下文对象中删除未使用的条目
最终证明,显著减少垃圾数量,导致
术语。

* [#9951](https://github.com/leanprover/lean4/pull/9951)产生`.ctorIdx`函数,用于所有感性类型,而不仅仅是
插图类型。 这可以作为其他建筑的构件
(`BEq`、`noConfusion`)即使对大型也具有大小效率的`BEq`、`noConfusion`
感应器

* [#9952](https://github.com/leanprover/lean4/pull/9952) 增加“非分处情况说明”:
`T.con`此`T.con` 添加一个相似的函数`T.con.with`
`T.casesOn`,但只有一个手臂(`con`的一臂)和一个额外的手臂
`t.toCtorIdx = 12` 假设。

* [#9954](https://github.com/leanprover/lean4/pull/9954) 删除备选案文`grind +ringNull`。
`grind ring` 模块的`grind ring` 校对值,但小于
比默认证明构建模式有效,并且有效
成为死代码。
并优化使用
在#9946中添加了基础设施。
** 备注:** 在更新第0阶段之后,我们可以删除若干背景。
`Init/Grind` 文件夹中的定理器。

* [#9958](https://github.com/leanprover/lean4/pull/9958)确保`grind cutsat`模块中的方程
以已解窗体保存的已解窗体。也就是说,给所用方程 `a*x + p = 0`
删除 `x`,线性多线性 `p` 不得包含其他
在本PRPR之前,方方程式维持在
三角形窗体。我们将使用解答窗体来线性化
非线性术语。

* [#9968](https://github.com/leanprover/lean4/pull/9968) 修改了实现非原子定义和 ```$cmd1 in $cmd2``` 语法的宏。这些宏涉及通过 ```section``` 和 ```namespace``` 命令引入的隐式作用域。由于 section 或 namespace 本来就是用来界定局部属性的，将局部属性应用到上述上下文中的定义时就会出现不直观的行为。这会导致下面的示例失败：
  ```lean4
  axiom A : Prop

* [#9974](https://github.com/leanprover/lean4/pull/9974) 登记`Lean.Parser.Command.visibility` 的解析别名。
这样可以避免以简单命令导入 `Lean.Parser.Command`
使用粘度的宏。

* [#9980](https://github.com/leanprover/lean4/pull/9980) 修正动态变量重新排序函数中使用的错误
`grind cutsat`。

* [#9989](https://github.com/leanprover/lean4/pull/9989) 将`mvcgen` 新的扩展语法修改为'mvcgen
变数.与.。

* [#9995](https://github.com/leanprover/lean4/pull/9995) 几乎完全重写了归纳谓词递归算法；尤其让 `IndPredBelow` 的行为更一致。历史上，通过 `IndPredBelow` 生成 `brecOn` 一直很容易出错——现在应该修好了，因为新算法非常直接，完全不依赖 tactic 或 metavariable。此外，新的归纳谓词结构递归过程与常规结构递归共享了更多代码，因此现在可以像常规结构递归一样进行互递归和嵌套递归。例如，下面的代码现在可以工作：
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

* [#10021](https://github.com/leanprover/lean4/pull/10021) 对 `grind` 标注分析脚本做了一些小改动，包括对结果排序和处理错误。仍需添加外部 UI。

* [#10022](https://github.com/leanprover/lean4/pull/10022) 改进了 `grind cutsat` 在 `n` 不是 numeral 时对 `Fin n` 的支持。例如，下面的目标现在可以自动求解：

  ```lean
  example (p d : Nat) (n : Fin (p + 1))
      : 2 ≤ p → p ≤ d + 1 → d = 1 → n = 0 ∨ n = 1 ∨ n = 2 := by
    grind

* [#10034](https://github.com/leanprover/lean4/pull/10034) 修改了 “declaration uses 'sorry'” 错误，使其在消息中美观打印实际的 `sorry` 表达式。这样一来，`sorry` 就可以被悬停查看；如果它带有标签，你还可以“转到定义”来查看其来源。

* [#10038](https://github.com/leanprover/lean4/pull/10038) 确保 `grind` 错误消息在引用声明名时使用 `{.ofConstName declName}`。

* [#10060](https://github.com/leanprover/lean4/pull/10060) 允许对由此产生的情况进行更多的精细控制
模块系统下有曝光定义:操作者不应
除非衍生项目或衍生项目
以 `@[expose]` 标记周围区域。
在更新第0阶段后更新。

* [#10069](https://github.com/leanprover/lean4/pull/10069) 在`grind linarith` 中添加辅助者定理以支持`NatModule`。

* [#10071](https://github.com/leanprover/lean4/pull/10071) 改进`grind cutsat`中`a^n`]对`a^n`[的支持。
`cutsat` 发现`a` 和`b`等于数字,现在
宣传平等。
与第9996号类似,但`a^b`。
示例:

  ```lean
  example (n : Nat) : n = 2 → 2 ^ (n+1) = 8 := by
    grind
  ```

* [#10085](https://github.com/leanprover/lean4/pull/10085)为`rawIdent`分析器添加一个解析别名,以便它能够
`Init` 中`syntax`项声明中使用的`Init`项声明中使用的[10]项声明。

* [#10093](https://github.com/leanprover/lean4/pull/10093)为在
`grind` 支持联合经营商和交流运营商。

* [#10095](https://github.com/leanprover/lean4/pull/10095)修改`grind`代数类型,以便使用`SMul x y`
取代`HMul x y y`。

* [#10105](https://github.com/leanprover/lean4/pull/10105)在`grind` 中增加支持侦查关联运营商。
新的空调模块还检测操作员是否具有通量,
以及该信息是否具有中性元素。
已缓存 。

* [#10113](https://github.com/leanprover/lean4/pull/10113) 将更自然命名的`.toCtorIdx`的`.ctorIdx`
(并更新标准库)。

* [#10120](https://github.com/leanprover/lean4/pull/10120) 确定私人定义反复援引的问题
使用通用字段符号( 点符号) 表示“ 无效 ”
字段“ 字段错误” 。它也会修正“ 无效字段标记” 的问题
错误会用 `_private` 来打印声明的名称
前缀 。

* [#10125](https://github.com/leanprover/lean4/pull/10125) 允许 `#guard_msgs` 通过配置选项 `(positions := true)` 报告已记录消息的相对位置。

* [#10129](https://github.com/leanprover/lean4/pull/10129) 将`Grind`所使用的临时命令类型类别改为`Grind`
`Std`中新的公开课程。

* [#10134](https://github.com/leanprover/lean4/pull/10134) 使职能上岗原则的产生更加
当用户 `let` - bind 键入一个变量时,该变量将被 `match` 插入。
修复了10132号

* [#10135](https://github.com/leanprover/lean4/pull/10135) 允许单建构体`ctorIdx` 定义
避免无谓的`.casesOn`,并使用`macro_inline`避免
编辑函数和浪费符号。

* [#10141](https://github.com/leanprover/lean4/pull/10141) 恢复第10135号`macro_inline`部分。

* [#10144](https://github.com/leanprover/lean4/pull/10144) 改变`CompleteLattice`实例的构建
内置的( 映射`Prop` )
`coinductive_fixpoint`/`inductive_fixpoint` 机制。

* [#10146](https://github.com/leanprover/lean4/pull/10146) 为 `grind` 中处理 AC 运算符的新过程实现了基础设施。它已经支持对不等式进行归一化；未来的 PR 将增加对使用等式做化简以及计算临界对的支持。示例：
等同, 计算关键对等。 例如 :
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
      : op a (op b c) = op (op a b) c := by
    grind only

* [#10151](https://github.com/leanprover/lean4/pull/10151) ensures `where finally` tactics can access private data under
  the module system even when the corresponding holes are in the public
  scope as long as all of them are of proposition types.

* [#10152](https://github.com/leanprover/lean4/pull/10152) introduces an alternative construction for `DecidableEq`
  instances that avoids the quadratic overhead of the default
  construction.

* [#10166](https://github.com/leanprover/lean4/pull/10166) reviews the expected-to-fail-right-now tests for `grind`, moving
  some (now passing) tests to the main test suite, updating some tests,
  and adding some tests about normalisation of exponents.

* [#10177](https://github.com/leanprover/lean4/pull/10177) fixes a bug in the `grind` preprocessor exposed by #10160.

* [#10179](https://github.com/leanprover/lean4/pull/10179) fixes `grind` instance normalization procedure.
  Some modules in grind use builtin instances defined directly in core
  (e.g., `cutsat`), while others synthesize them using `synthInstance`
  (e.g., `ring`). This inconsistency is problematic, as it may introduce
  mismatches and result in two different representations for the same
  term. fixes the issue.

* [#10183](https://github.com/leanprover/lean4/pull/10183) 让 match equation 在可能时直接用 `rfl` 证明，而不是先显式展开左侧。这可能带来更小的证明。

* [#10185](https://github.com/leanprover/lean4/pull/10185) documents all `grind` attribute modifiers (e.g., `=`, `usr`,
  `ext`, etc).

* [#10186](https://github.com/leanprover/lean4/pull/10186) 为 `grind ac` 模块添加了化简不等式的支持。

* [#10189](https://github.com/leanprover/lean4/pull/10189) 为新的 `grind ac` 模块实现了 proof term。示例：
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
      : op a (op b b) = op c d → op c (op d c) = op (op a b) (op b c) := by
    grind only

* [#10205](https://github.com/leanprover/lean4/pull/10205) 为 `grind ac` 中的结合且交换运算符添加了 superposition。示例：

  ```lean
  example (a b c d e f g h : Nat) :
      max a b = max c d → max b e = max d f → max b g = max d h →
      max (max f d) (max c g) = max (max e (max d (max b (max c e)))) h := by
    grind -cutsat only

* [#10206](https://github.com/leanprover/lean4/pull/10206) 为 `grind ac` 中的结合但非交换运算符添加了 superposition。示例：
  ```lean
  example {α} (op : α → α → α) [Std.Associative op] (a b c d : α)
     : op a b = c →
       op b a = d →
       op (op c a) (op b c) = op (op a d) (op d b) := by
    grind

* [#10208](https://github.com/leanprover/lean4/pull/10208) 增加额外关键对配以确保`grind ac`程序
当操作员为AC和无能时即为完整。例如:
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

* [#10230](https://github.com/leanprover/lean4/pull/10230) 为更多 monad transformer 添加了 `MonoBind`。这使得 `partial_fixpoint` 可用于基于 `Option` 和 `EIO` 的更复杂 monad。示例：
  ```lean-4
  abbrev M := ReaderT String (StateT String.Pos Option)

* [#10237](https://github.com/leanprover/lean4/pull/10237) 修复了 `grind` canonicalizer 中的一个缺失分支。有些类型可能包含稍后才会被 internalize 到 `grind` 状态中的项或命题。

* [#10239](https://github.com/leanprover/lean4/pull/10239) 修复了针对含有未被常规参数引用的 universe 参数的定理的 E-matching 过程。这类定理在实践中不常见，但标准库里确实有。示例：
  ```
  @[simp, grind =] theorem Std.Do.SPred.down_pure {φ : Prop} : (⌜φ⌝ : SPred []).down = φ := rfl
  ```

* [#10241](https://github.com/leanprover/lean4/pull/10241) 添加了一些 `grind` 配合 `Fin` 工作的测试用例。`tests/lean/grind/grind_fin.lean` 中仍有许多失败测试，我打算继续分拣和处理。

* [#10245](https://github.com/leanprover/lean4/pull/10245) 修改了（协）归纳谓词机制中使用的函数 `unfoldPredRel` 的实现，它会把谓词上的逐点序展开为量化与蕴含。此前的实现依赖 `withDeclsDND`，而它无法处理互相依赖的类型。这导致下面的示例失败：

  ```lean4
  inductive infSeq_functor1.{u} {α : Type u} (r : α → α → Prop) (call : {α : Type u} → (r : α → α → Prop) → α → Prop) : α → Prop where
    | step : r a b → infSeq_functor1 r call b → infSeq_functor1 r call a

* [#10265](https://github.com/leanprover/lean4/pull/10265)在#10242所暴露的`grind ring` 中修补恐慌。 `grind ring`
不应假定所有正常化都已经实施,因为
由于打字限制,`simp` 无法改写某些子术语。
此外,`grind`在少数地方使用`preprocessLight`,但跳过
简化/调整。

* [#10267](https://github.com/leanprover/lean4/pull/10267) 实施支持`NatModule`
`grind linarith`并用它处理不平等问题。
增加对平等和不平等的支持。例如:
  ```lean
  open Lean Grind
  variable (M : Type) [NatModule M] [AddRightCancel M]

* [#10269](https://github.com/leanprover/lean4/pull/10269) changes the string interpolation procedure to omit redundant
  empty parts. For example `s!"{1}{2}"` previously elaborated to `toString
  "" ++ toString 1 ++ toString "" ++ toString 2 ++ toString ""` and now
  elaborates to `toString 1 ++ toString 2`.

* [#10271](https://github.com/leanprover/lean4/pull/10271) changes the naming of the internal functions in deriving
  instances like BEq to use accessible names. This is necessary to
  reasonably easily prove things about these functions. For example after
  `deriving BEq` for a type `T`, the implementation of `instBEqT` is in
  `instBEqT.beq`.

* [#10273](https://github.com/leanprover/lean4/pull/10273) tries to do the right thing about the visibility of the
  same-ctor-match-construct.

* [#10274](https://github.com/leanprover/lean4/pull/10274) changes the implementation of the linear `DecidableEq`
  implementation to use `match decEq` rather than `if h : ` to compare the
  constructor tags. Otherwise, the “smart unfolding” machinery will not
  let `rfl` decide that different constructors are different.

* [#10277](https://github.com/leanprover/lean4/pull/10277) adds the missing instances `IsPartialOrder`, `IsLinearPreorder`
  and `IsLinearOrder` for `OfNatModule.Q α`.

* [#10278](https://github.com/leanprover/lean4/pull/10278) adds support for `NatModule` equalities and inequalities in
  `grind linarith`. Examples:
  ```lean
打开 Lean Grind Std

* [#10280](https://github.com/leanprover/lean4/pull/10280) 添加辅助定理`Lean.Grind.Linarith.eq_normN`
当情况`AddRightCancel`是
不详。

* [#10281](https://github.com/leanprover/lean4/pull/10281)在`AddRightCancel` 实现`NatModule` 正常化时`NatModule`
无法提供实例。 请注意, 在此情况下, 嵌入
`IntModule`不是注射。因此,我们使用海关正常化者,
类似 `CommSemiring` `grind ring` 中使用的`CommSemiring`归和器的`grind ring`
模块。示例:

  ```lean
  open Lean Grind
  example [NatModule α] (a b c : α)
      : 2•a + 2•(b + 2•c) + 3•a = 4•a + c + 2•b + 3•c + a := by
    grind
  ```

* [#10282](https://github.com/leanprover/lean4/pull/10282) 改进`grind linarith`为
`NatModule`s. `grind` 现在隐藏辅助功能的发生
`Grind.IntModule.OfNatModule.toQ`。

* [#10283](https://github.com/leanprover/lean4/pull/10283) 执行`grind ac` 模块的诊断信息。
现在显示基点、 正常化的不平等和附加的
每个关联操作员都检测到特性。

* [#10290](https://github.com/leanprover/lean4/pull/10290)为登记新的`grind`解决者增加基础设施。 `grind`
已经包括许多解答器, 而此 PR 是迈向
模块化设计和支持用户定义的解决方案。

* [#10294](https://github.com/leanprover/lean4/pull/10294) 完成了 `grind` solver extension 的设计，并将 `grind ac` solver 迁移到了新框架。未来的 PR 会为 API 撰写文档，并迁移剩余的 solver。新设计的另一项好处是构建时间更快。

* [#10296](https://github.com/leanprover/lean4/pull/10296)修正用于构建证明的辅助函数中的错误
`grind cutsat`。

* [#10300](https://github.com/leanprover/lean4/pull/10300) 提供了替代`noConfusion`
基于比较的对角外用途(即不同构造器的不同构造器)
`.ctorIdx`。这应导致更快的型号检查,如内核检查。
只须将`.ctorIdx` 减少两次,而不是使情况复杂化
`noConfusionType` 建筑。

* [#10301](https://github.com/leanprover/lean4/pull/10301) 暴露了COCIdx和每个构件除尘器。 固定# 10299 。

* [#10306](https://github.com/leanprover/lean4/pull/10306))在`rw`战术中修补了几个错误:它可以“偷窃”目标
因为它们出现在重写类型中,所以没有发生
检查,新的验证目标不会是合成的不透明。
让`rfl`策略指定合成的不透明可变可变变量,以便它
等于`exact rfl`。

* [#10307](https://github.com/leanprover/lean4/pull/10307) 将 Verso 解析器上游合入，并为 docstring 中使用 Verso 添加了初步支持。这将允许编译器检查文档中的示例和交叉引用。

* [#10309](https://github.com/leanprover/lean4/pull/10309)修改`simpa`战术,以便`simpa ... using e`
是显示简化范围的战术信息 `simpa ... using`
目标。

* [#10313](https://github.com/leanprover/lean4/pull/10313) 为`natCast`和`natCast`添加缺失的`grind`正常化规则
`intCast` 示例:
  ```
  open Lean.Grind
  variable (R : Type) (a b : R)

* [#10314](https://github.com/leanprover/lean4/pull/10314) 对实例跳过基于模型的理论组合。

* [#10315](https://github.com/leanprover/lean4/pull/10315) 添加了 `T.ctor.noConfusion` 声明，它们是 `T.noConfusion` 在 `T.ctor` 之间等式上的特化。目的是避免每次使用 `injection` 或类似策略时都去约化 `T.noConfusionType` 的构造。

* [#10316](https://github.com/leanprover/lean4/pull/10316) 共享了处理同一构造器之间等式以及判断这些等式类型是否正确的通用功能。具体而言，它也在 `CasesOnSameCtor` 以及 `BEq`、`DecidableEq`、`Ord` 的派生代码等位置使用 `mkInjectivityThm` 中更完整的逻辑，从而提升一致性并改进错误消息。

* [#10321](https://github.com/leanprover/lean4/pull/10321) 确保 `grind` 所用 E-matching 模块创建的辅助临时 metavariable ID 不受调用 `grind` 之前已执行内容的影响。目的是增强 `grind` 的稳健性。

* [#10322](https://github.com/leanprover/lean4/pull/10322) 为 `grind` 引入功能受限的前端 `cutsat` 和 `grobner`。我们禁用了定理实例化（`grobner` 还禁用了 case splitting），并关闭所有其他 solver。二者仍允许 `grind` 的配置项，因此例如可以用 `cutsat +ring`（或 `grobner +cutsat`）解决同时需要两者的问题。

* [#10323](https://github.com/leanprover/lean4/pull/10323) 修复了 `grind` 对 `OfNat.ofNat` 应用的 canonicalizer。示例：
  ```lean
  example {C : Type} (h : Fin 2 → C) :
      -- `0` in the first `OfNat.ofNat` is not a raw literal
      h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by
    grind
  ```

* [#10324](https://github.com/leanprover/lean4/pull/10324) 禁用了一个会导致昂贵 type class 搜索的未使用实例。

* [#10325](https://github.com/leanprover/lean4/pull/10325) 为实现 `ToInt` 接口的类型 `A` 实现了基于模型的理论组合。示例：
  ```lean
  example {C : Type} (h : Fin 4 → C) (x : Fin 4)
      : 3 ≤ x → x ≤ 3 → h x = h (-1) := by
    grind

* [#10326](https://github.com/leanprover/lean4/pull/10326)在`grind linarith`中确定绩效问题。
`NatModule` /`IntModule` 用于流通环结构的多余`NatModule`/`IntModule`
此类类型应由`grind ring`处理。
仅此而已。

* [#10331](https://github.com/leanprover/lean4/pull/10331) 执行`mkNoConfusionImp`在利安而不是在C`mkNoConfusionImp`。
减少对C的依赖,并可能因不依赖C而带来业绩效益
缩短`noConfusionType`在编程期间的`noConfusionType`
在进行类型检查时减去内核) 。

* [#10332](https://github.com/leanprover/lean4/pull/10332) 确保信息树承认`Classical.propDecidable`
例如,如果低于`classical`战术。

* [#10335](https://github.com/leanprover/lean4/pull/10335) 修正 [`grind` 中的嵌套验证词检测。 它必须检查 `grind`
该工具是否被过度使用。

* [#10342](https://github.com/leanprover/lean4/pull/10342) 实施一个新的电子比对模式推断程序,即:
证明手册中记录的行为
最小可索引化子表达式。旧的推断程序是
未执行此条件。 例如, 手动文件
`[grind ->]` 如下`[grind ->]`

* [#10373](https://github.com/leanprover/lean4/pull/10373) 添加`pp.unicode`选项和`unicode("→", "->")`语法
下层`unicodeSymbol "→" "->"`分析器的别名说明。
语法也添加到 `notation` 命令中。 当 `pp.unicode`
是真实的( 默认) , 然后在打印漂亮时使用第一个表单 。
另外,还使用了第二个ASCII格式。一个变体,“unicode (")",“unicode ("_")",
“ - > ” , 保留FORPP) ` causes the `- -  优先形式; 破坏者
可直接插入语法中的 `→` ,该语法将精美打印
as- is; 允许使用 `fun` 等自定义选项, 例如
`pp.unicode.fun` 选入英俊印刷时的 Unicode 格式。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Library"
%%%

* [#7858](https://github.com/leanprover/lean4/pull/7858) 执行未签名的溢漏探测快速电路
Bitwuzla使用的乘法建议如下:
https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=987767

* [#9127](https://github.com/leanprover/lean4/pull/9127) 使`saveModuleData` 抛出IO. Error 而不是惊慌,
如果给某些无法序列化的东西, 这其实并不重要
用于保存模块, 但是在写入工具以保存辅助工具时方便
通过电池`pickle`在单质文件中输入数据。

* [#9560](https://github.com/leanprover/lean4/pull/9560) 确定`forIn` 功能,该功能以前曾造成
承诺在提出例外时放弃,无价值
。它也纠正 `background` 的参数顺序。
函数。

* [#9599](https://github.com/leanprover/lean4/pull/9599)添加类型`Std.Internal.Parsec.Error`,其中
`.eof`(可用于检查由于未
有足够的输入, 然后在更多输入到达时重试
HTTP 服务器中有用)和`.other`,其中描述了其他错误。
它还为许多职能增加了文件,以及一些新的职能。
`ByteArray` 分析函数,例如`peekWhen?`、`octDigit`,
`takeWhile`、`takeUntil`、`skipWhile`和`skipUntil`。

* [#9632](https://github.com/leanprover/lean4/pull/9632)为`TreeMap` 作业`filter`、`map`和`map`加上`TreeMap`
`filterMap`.这些麻麻已经存在用于散列地图,只是
被从那里移到那里。

* [#9685](https://github.com/leanprover/lean4/pull/9685) 核实`toArray` 和与散列有关的功能。

* [#9797](https://github.com/leanprover/lean4/pull/9797) 提供迅速提供所有命令情况的手段
与某些高级订单结构(预订单,部分
可通过工厂进行。
`PreorderPackage.ofLE`、`PartialOrderPackage.ofLE`、
`LinearPreorderPackage.ofLE`和`LinearOrderPackage.ofLE`。

* [#9908](https://github.com/leanprover/lean4/pull/9908)作出`IsPreorder`、`IsPartialOrder`、`IsLinearPreorder`和
`IsLinearOrder` 延长`BEq`和`Ord`,酌情添加
`LawfulOrderBEq`和`LawfulOrderOrd`与`BEq`和`BEq`有关
`Ord`至`LE`,并增加许多脂质和实例。

* [#9916](https://github.com/leanprover/lean4/pull/9916) 提供工厂,根据
`Ord`实例。如果存在,则优先选择现有实例,而不是
可以从`Ord` 中得出`Ord`。可以具体说明任何实例。
如果需要, 手动手动 。

* [#9924](https://github.com/leanprover/lean4/pull/9924) 将`PostCond` 的示例固定在文件中。

* [#9931](https://github.com/leanprover/lean4/pull/9931) 执行`Std.Do.Triple.mp`,使用户能够组成两个`Std.Do.Triple.mp`
同一程序的具体规格。

* [#9949](https://github.com/leanprover/lean4/pull/9949)允许在下列条件下使用大部分`List.lookup` [ [ [ [ [ [ [ [ [ [ [ [ [允许使用大多数`List.lookup` Lemmmas
`LawfulBEq α` 不详。

* [#9957](https://github.com/leanprover/lean4/pull/9957) 将来自 Batteries 的 `Rat` 定义上游合入，以供我们计划中的区间算术策略使用。

* [#9967](https://github.com/leanprover/lean4/pull/9967) 从 SpecLemmas.lean 中删除本地 `Triple` 标记符号, 工作
围绕一个破坏舞台2结构的错误

* [#9979](https://github.com/leanprover/lean4/pull/9979) 用从 Batteries 上游合入的公共 `Rat` 替换 `Std.Internal.Rat`。

* [#9987](https://github.com/leanprover/lean4/pull/9987) 改进了证明以`Nat`为基础的`Nat`
`PRange` 依靠`omega` 战术进入入境。

* [#9993](https://github.com/leanprover/lean4/pull/9993) 定义了二进有理数，并证明它们构成一个可嵌入到有理数中的有序环。我们将把它用于未来的区间算术策略。

* [#9999](https://github.com/leanprover/lean4/pull/9999)减少`Nat.Bitwise`我们已备有的研磨说明的数量
新的小一套鼓励`grind`
旧行为导致饱和到
即时限制。

* [#10000](https://github.com/leanprover/lean4/pull/10000) 删去向所有`Option.map` 发射的`grind`注 ,
造成一场雪崩的即时反应

* [#10005](https://github.com/leanprover/lean4/pull/10005) 缩短了让某个类型兼容多态 range 记号所需的工作量。以 `Nat` 为例，它将所需代码行数从 150 行减少到了 70 行。

* [#10015](https://github.com/leanprover/lean4/pull/10015) 暴露`Name.append`、`Name.appendCore`和`Name.appendCore`
[`Name.hasMacroScopes` 。
使用模块系统时拼接名称字典 。

* [#10018](https://github.com/leanprover/lean4/pull/10018) `BEq`和`Hashable`的`Lean.Import`的`BEq`和`Hashable`。
嗣后,《古兰经》已订明,而《古兰经》已订明。

* [#10019](https://github.com/leanprover/lean4/pull/10019) 为 `Lean.ParserState.setPos` 添加了 `@[expose]`。这使得对 `setPos` 产生的状态，为 `next'` 和 `get'` 之类函数证明有界性时，无需 `import all`。

* [#10024](https://github.com/leanprover/lean4/pull/10024)在`LawfulOrderMin/Max`和`LawfulOrderMin/Max`中增加有用的声明
`LawfulOrderLeftLeaningMin/Max` API, 特别是它引入了`LawfulOrderLeftLeaningMin/Max` API。
`Min`和`Max`的`.leftLeaningOfLE`工厂。
`LawfulOrderMin/Max.of_le`至.of_le_min_iff` and `.of_max_le_iff`和
第二种变式采用不同的论据。

* [#10045](https://github.com/leanprover/lean4/pull/10045) 执行必要的类型类别类别,使范围标记
用于整数。 例如, `( 2)... 3] to list = [ 2, 1, 0, 1, 2]
: 清单

* [#10049](https://github.com/leanprover/lean4/pull/10049) 添加一些介绍短语所需的背景材料
理性在#9993。

* [#10050](https://github.com/leanprover/lean4/pull/10050) 修复了 `Data/Rat/Lemmas` 中的一些命名问题，并将消去器 `numDenCasesOn` 及其相关项上游合入。

* [#10059](https://github.com/leanprover/lean4/pull/10059) 改进多形态中定义和 Lemmas 的名称
API 区域 API。它也引入了推荐的拼法。例如,a
以 Mathlib 的类比拼写 `Rco`
`Ico` 间隔。

* [#10075](https://github.com/leanprover/lean4/pull/10075) 含有约`Int`(BTVec和BTVec的微小修正)
(Nat Nat) 用于编写词典。
@Rob23oba, 我提前从9993号取出来,
可操作。

* [#10077](https://github.com/leanprover/lean4/pull/10077) 将 `Mathlib.Data.Rat.Defs` 和 `Mathlib.Algebra.Order.Ring.Unbundled.Rat` 中关于 `Rat` 的引理上游合入，具体多到足以得到 `Lean.Grind.Field Rat` 和 `Lean.Grind.OrderedRing Rat`。除了引理外，还上游合入了 `Inv Rat`、`Pow Rat Nat` 和 `Pow Rat Int` 的实例。

* [#10107](https://github.com/leanprover/lean4/pull/10107) 添加`Lean.Grind.AddCommGroup`例`Rat`。

* [#10138](https://github.com/leanprover/lean4/pull/10138) 增加`Dyadic.roundUp` 和`Dyadic.roundDown`的`Dyadic.roundUp`
业务。

* [#10159](https://github.com/leanprover/lean4/pull/10159) 增加`nodup_keys` `nodup_keys` Lemmas,作为现有
`distinct_keys` 对所有`Map`变式。

* [#10162](https://github.com/leanprover/lean4/pull/10162) 去除了`grind →` 说明,该说明太频繁、无益地点火。
最好`grind`能即时处理这些色雷斯,但只有在以下情况下:
`xs ++ ys`和`#[]`在相同的等同类中已经见`xs ++ ys`和`#[]`,而不是
只要它看到`xs ++ ys`。

* [#10163](https://github.com/leanprover/lean4/pull/10163)删除一些(希望)不必要的说明`grind`
导致即时爆炸。

* [#10173](https://github.com/leanprover/lean4/pull/10173) 将`extends Monad`从`MonadAwait`和`MonadAsync`中删除`extends Monad`
避免未确定的情况。

* [#10182](https://github.com/leanprover/lean4/pull/10182) 为 `Nat.fold` 与 `Nat.foldRev` 在求和上的行为添加了引理，以匹配现有关于 `dfold` 和 `dfoldRev` 的定理。

* [#10194](https://github.com/leanprover/lean4/pull/10194) 添加了给定精度下二进有理数的逆元，以及相应的刻画引理。它还清理了 `Int.DivMod` 与 `Rat` API 的若干部分，并证明了一些关于 `Rat.toDyadic` 的刻画引理。
`Rat.toDyadic`。

* [#10216](https://github.com/leanprover/lean4/pull/10216) 修补#10193。

* [#10224](https://github.com/leanprover/lean4/pull/10224) 将`HashMap`、`TreeMap` 和`TreeMap`的`HashMap`、`TreeMap` 和[3]
`HashSet`为`m : Type u → Type v`工作。

* [#10227](https://github.com/leanprover/lean4/pull/10227) 增加`@[grind]` 说明(几乎全部`@[grind =]` 说明)
`ReaderT`、`StateT`、`ExceptT`。

* [#10244](https://github.com/leanprover/lean4/pull/10244)在`toList`和`toArray`的`toList`和`toArray`职能方面,增加了更多的`toList`和`toArray`
将 `Array.mem_toArray` 重新命名为
`List.mem_toArray`。

* [#10247](https://github.com/leanprover/lean4/pull/10247) 加上缺少的麻麻`ofList_eq_insertMany_empty` ,
`get?_eq_some_iff`、`getElem?_eq_some_iff`、`getElem?_eq_some_iff`和`getKey?_eq_some_iff`
所有类型的集装箱。

* [#10250](https://github.com/leanprover/lean4/pull/10250) 修复了 `LinearOrderPackage.ofOrd` 工厂中的一个错误。如果有 `LawfulEqOrd` 实例可用，它应自动使用它，而不是要求用户向工厂提供 `eq_of_compare` 参数。该 PR 还解决了一个与卫生相关的问题：当 `Std` 未打开时，这些工厂会失败。

* [#10303](https://github.com/leanprover/lean4/pull/10303) 增加`BitVec` 和`UInt*` 类型的范围支持。
例如,现在可以为一(1:UInt8.).5撰写。
`, in order to loop over the values 1, 2, 3 and 4 of type `8'。

* [#10341](https://github.com/leanprover/lean4/pull/10341) 将定义和基本事实移到 `Function.Injective`
从麦特立卜起行,我们可以做一个更好的工作。
在`grind` 中通过注射进行争论,如果有的话。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Compiler"
%%%

* [#9631](https://github.com/leanprover/lean4/pull/9631) 使 `IO.RealWorld` 透明。它还添加了一个新的编译器 - 仅
`lcRealWorld` 常数,用于在编译器中代表这类类型的编译器。
默认缺省,不透明类型定义被处理为 `lcAny` ,而我们
需要更有效率的代表权。目前,这不是什么大事。
但将来我们想彻底抹去
`IO.RealWorld` 运行时。

* [#9922](https://github.com/leanprover/lean4/pull/9922) 修改了 `internalizeCode`：它会把 `Expr` 中（这些位置全都是类型）所有带有非 param-bound fvar 的替换项都替换为 `lcAny`，从而保持“不存在此类依赖”的不变式。这个不变式在文件之间被破坏曾导致一个待合并 PR 中的测试失败，但很难为它写出直接测试。未来我们或许应当让 LCNF 检查器能够检测这一点。

* [#9972](https://github.com/leanprover/lean4/pull/9972))在将Mathlib的`FintypeCat`作为代码运行时修正一个问题,
将前一种被擦除的类型传递到多形态函数。我们曾经是
将箭头类型降为 `object`,与运行时间相冲突
表示被擦除值为标记的卡路里 。

* [#9977](https://github.com/leanprover/lean4/pull/9977)增加支持编译`casesOn` `casesOn`
Subsingleton 的前提 。

* [#10023](https://github.com/leanprover/lean4/pull/10023) 添加了支持，以正确处理支持大消去的归纳谓词在 `casesOn` 上的字段计算。对这类谓词，唯一允许的相关字段是同时也被用作索引的那些，此时我们可以找到给定的索引并改用那个项。

* [#10032](https://github.com/leanprover/lean4/pull/10032)在降低使用量时改变对过度使用的建筑建造商的处理
LCNF 改为IR,产生于未生产(默示的)断言未能生产
`unreachable`. 内线无法连接代码的转换可产生
附加参数的建筑师应用程序。

* [#10040](https://github.com/leanprover/lean4/pull/10040) 更改`toMono`通以 `_redArg` 取代`toMono`通
等等量,其后果是不考虑论点
为《公约》目的通过`reduceArity`号]
`noncomputable`检查。

* [#10070](https://github.com/leanprover/lean4/pull/10070)通过对监督工作进行补救,确定`noConfusion` 的编译
将此代码从旧的编译器中移植时生成的代码。 只有旧的编译器
反复为每个非`Prop` 输入字段扩展主数
审议中,反映`noConfusion` 本身的建造,
而新编译器错误地计算了所有字段。

* [#10133](https://github.com/leanprover/lean4/pull/10133) 修正精立生成的可执行文件与 Unicode 的兼容性
Windows 上的系统文件路径

* [#10214](https://github.com/leanprover/lean4/pull/10214) 修复#10213。

* [#10256](https://github.com/leanprover/lean4/pull/10256)纠正`toIR`中可能过分适用的错误`toIR`
函数,该函数具有IR 分解功能,但无单核分解功能。

* [#10355](https://github.com/leanprover/lean4/pull/10355)更改`toLCNF`,将内置型号的`.proj`转换为使用
代之以预测职能。

## 美观打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Pretty-Printing"
%%%

* [#10122](https://github.com/leanprover/lean4/pull/10122) 增加支持使用通用版面的漂亮印刷
关于公共类型私人定义的注释(点符号)
更改 dott 表达符号, 以在删除后解决名称
私有私人前缀, 用于对私人定义使用点符号
私人进口类型。

* [#10373](https://github.com/leanprover/lean4/pull/10373) 添加`pp.unicode`选项和`unicode("→", "->")`语法
下层`unicodeSymbol "→" "->"`分析器的别名说明。
语法也添加到 `notation` 命令中。 当 `pp.unicode`
是真实的( 默认) , 然后在打印漂亮时使用第一个表单 。
另外,还使用了第二个ASCII格式。一个变体,“unicode (")",“unicode ("_")",
“ - > ” , 保留FORPP) ` causes the `- -  优先形式; 破坏者
可直接插入语法中的 `→` ,该语法将精美打印
as- is; 允许使用 `fun` 等自定义选项, 例如
`pp.unicode.fun` 选入英俊印刷时的 Unicode 格式。

* [#10374](https://github.com/leanprover/lean4/pull/10374)增加备选案文`pp.piBinderNames`和
`pp.piBinderNames.hygienic`. 促成`pp.piBinderNames` 原因
非依赖的 pi 粘贴器名称要漂亮打印, 而不是
。当 `pp.piBinderNames.hygienic` 是假的(默认) 时,删除
只有非卫生的这种二进制名称印得漂亮。设置 `pp.all`
`pp.piBinderNames` ,如果未另作明确规定。

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Documentation"
%%%

* [#9956](https://github.com/leanprover/lean4/pull/9956)对`let`和`have`战术补充补充信息
有关不透明性、何时使用每个工具以及相关战术的口号。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Server"
%%%

* [#9966](https://github.com/leanprover/lean4/pull/9966) 调整“ 尝试此小部件” 小部件, 以作为小部件消息格式化
在“ Messages” 栏下, 而不是在“ 建议” 栏下的单独小部件 。
这样做的主要好处在于 小部件的信息不是
在“ Messages” 和“ 建议” 之间复制 。

* [#10047](https://github.com/leanprover/lean4/pull/10047) 确保在`match`上徘徊时显示该`match`
匹配。

* [#10052](https://github.com/leanprover/lean4/pull/10052) 修补导致利安服务器服务器处理树生存的错误
关闭《VS规则》。

* [#10249](https://github.com/leanprover/lean4/pull/10249)通过各种途径加速自动完成,以~3.5x乘数的速度加速到自动完成
语言服务器的性能改进。
`import Mathlib`,完成`i`,过去用3200米,现在改用
a = 920米。

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Lake"
%%%

* [#9749](https://github.com/leanprover/lean4/pull/9749) 重构Lake代码基使用新的模块系统
`Lake`中的每一单元现在都是`module`。

* [#10276](https://github.com/leanprover/lean4/pull/10276)将`verLit`语法移入 `Lake.DSL`命名空间
符合`Lake.DSL`中的其他代码。

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___24___0-_LPAR_2025-10-14_RPAR_--Other"
%%%

* [#10043](https://github.com/leanprover/lean4/pull/10043) 允许Lean的旁听员在
字符串结尾处, 可以在输入的分区中引用 。

* [#10217](https://github.com/leanprover/lean4/pull/10217)确保`@[init]`诸如`initialize` 的`@[init]` 声明等[]声明被运行
进口时申报的订单。

* [#10262](https://github.com/leanprover/lean4/pull/10262)增加一个新的选项`maxErrors`,限制误差次数
从单 `lean` 运行打印, 默认为 100 处理。
当限制达到时中止中止, 但此限制仅跟踪到
每人指挥级别。


````
