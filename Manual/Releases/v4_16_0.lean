/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.16.0 (2025-02-03)" =>
%%%
tag := "release-v4.16.0"
file := "v4.16.0"
%%%

````markdown
## 高亮
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights"
%%%

### 各不相同的 `sorry`
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights--Unique-sorrys"
%%%

[#5757](https://github.com/leanprover/lean4/pull/5757) 通过确保每个 `sorry` 在定义上都不等同于其他 `sorry`，让人为定义体中用 `sorry` 占位的定义构造“伪造”定理变得更困难。例如，下面的代码现在会失败：
```lean
example : (sorry : Nat) = sorry := rfl -- fails
```
不过，下面的例子仍然会成功，因为这里的 `sorry` 是同一个不确定的 `Nat`：
```lean
def f (n : Nat) : Nat := sorry
example : f 0 = f 1 := rfl -- succeeds
```
如果把参数放到冒号右侧，就可以写得更谨慎一些：
```lean
def f : (n : Nat) → Nat := sorry
example : f 0 = f 1 := rfl -- fails
```
现在，大多数合成 `sorry` 的来源（回顾一下：即由精化器产生的 `sorry`）都会是唯一的；唯一的例外是精化错误，因为让这类 `sorry` 也唯一化往往会造成令人困惑的连锁报错。不过，总体而言，这些 `sorry` 现在都会带标签。这样一来，在 Infoview 中对 `sorry` 使用“转到定义”就会跳到它的来源。选项 `set_option pp.sorrySource true` 会让漂亮打印器在 `sorry` 上显示源位置。

### 数字字面量中的分隔符
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights--Separators-in-numeric-literals"
%%%

[#6204](https://github.com/leanprover/lean4/pull/6204) 允许在数字字面量中使用 `_` 作为分隔符。例如 `1_000_000`、`0xff_ff` 或 `0b_10_11_01_00`。新的词法语法如下：
```text
numeral10 : [0-9]+ ("_"+ [0-9]+)*
numeral2  : "0" [bB] ("_"* [0-1]+)+
numeral8  : "0" [oO] ("_"* [0-7]+)+
numeral16 : "0" [xX] ("_"* hex_char+)+
float     : numeral10 "." numeral10? [eE[+-]numeral10]
```

### 其他新特性
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights--Additional-new-features"
%%%

* [#6300](https://github.com/leanprover/lean4/pull/6300) 新增 `debug.proofAsSorry` 选项。启用后，定理的证明会被忽略，并替换为 `sorry`。

* [#6362](https://github.com/leanprover/lean4/pull/6362) 为 `lean` CLI 新增 `--error=kind` 选项（简写为 `-Ekind`）。设置后，`kind` 类型的消息（例如 `linter.unusedVariables`）会被当作错误报告。这个设置在交互式上下文（如服务器）中不起作用。

* [#6366](https://github.com/leanprover/lean4/pull/6366) 新增对 `Float32` 的支持，并修复了运行时中的一个问题。

### 库更新
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights--Library-updates"
%%%

Lean 4 库进行了大量更新，改进了算术推理、增强了数据结构 API，并优化了库的组织方式。重点变化包括：更好地支持按位运算、移位与转换；扩充了 `Array`、`Vector` 和 `List` 的引理；并改进了顺序相关定义。一些模块为提高清晰度而重新组织，内部细化也进一步提升了一致性与正确性。

### 破坏性变更
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Highlights--Breaking-changes"
%%%

[#6330](https://github.com/leanprover/lean4/pull/6330) 从函数归纳原理中移除了不必要的参数。这是一项破坏性变更；受影响的代码通常只需少传几个参数即可完成调整。

_本高亮部分由 Violetta Sim 撰写。_

本次发布共合入 201 项变更。除下方列出的 74 项功能新增和 44 项修复外，另有 7 项重构、5 项文档改进和 62 项杂项工作。

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Language"
%%%

* [#3696](https://github.com/leanprover/lean4/pull/3696) 让所有消息构造器都能处理漂亮打印器错误。

* [#4460](https://github.com/leanprover/lean4/pull/4460) 为单个命令一次性运行全部 linter（合并执行），并将其放到与后续精化分离的线程中，这是精化器并行化迈出的第一步。

* [#5757](https://github.com/leanprover/lean4/pull/5757)，详见上文高亮部分。

* [#6123](https://github.com/leanprover/lean4/pull/6123) 确保在 `simp` 中规约项和检查定义相等性时，会使用 `Simp.Config` 里的配置。

* [#6204](https://github.com/leanprover/lean4/pull/6204)，详见上文高亮部分。

* [#6270](https://github.com/leanprover/lean4/pull/6270) 修复了一个问题：它可能导致 `injectivity` 策略在 reducible 模式下失败，从而使展开引理的生成失败（被 `unfold` 等策略使用）。具体来说，`Lean.Meta.isConstructorApp'?` 之前不知道 `n + 1` 等价于 `Nat.succ n`。

* [#6273](https://github.com/leanprover/lean4/pull/6273) 调整了 “foo has been deprecated: use betterFoo instead” 这类警告，使其中的 foo 和 betterFoo 都可以悬停查看。

* [#6278](https://github.com/leanprover/lean4/pull/6278) 允许向 `norm_cast` 传递 simp 配置选项。

* [#6286](https://github.com/leanprover/lean4/pull/6286) 确保 `bv_decide` 在其反射过程里尽可能使用定义相等性。此前它会构造显式的同余证明交给内核检查。这样一来，传给内核的证明项会更小，从而加快大型反射证明的检查速度。

* [#6288](https://github.com/leanprover/lean4/pull/6288) 在 `bv_decide` 的反射证明中使用 Lean.RArray，从而在变量很多的问题上提升速度。

* [#6295](https://github.com/leanprover/lean4/pull/6295) 为 `Init.Data.Fin.Basic` 中剩余的所有操作配置 simproc。

* [#6300](https://github.com/leanprover/lean4/pull/6300)，详见上文高亮部分。

* [#6330](https://github.com/leanprover/lean4/pull/6330)，详见上文高亮部分。

* [#6362](https://github.com/leanprover/lean4/pull/6362)，详见上文高亮部分。

* [#6366](https://github.com/leanprover/lean4/pull/6366)，详见上文高亮部分。

* [#6375](https://github.com/leanprover/lean4/pull/6375) 修复了化简器中的一个问题。此前它在消去未使用的 `let_fun` 表达式时，会产生带有悬空绑定变量的项。

* [#6378](https://github.com/leanprover/lean4/pull/6378) 为 `cases` 和 `induction` 应用于类型并非归纳类型的项时的报错添加了解释。对于 `Prop`，这些策略现在会建议使用 `by_cases` 策略。例如：
```
tactic 'cases' failed, major premise type is not an inductive type
  Prop
```

* [#6381](https://github.com/leanprover/lean4/pull/6381) 修复了 `withTrackingZetaDelta` 和 `withTrackingZetaDeltaSet` 中的一个问题。`MetaM` 缓存需要被重置。详见新增测试。

* [#6385](https://github.com/leanprover/lean4/pull/6385) 修复了 `simp_all?` 中的一个问题，该问题会导致某些局部声明遗漏在 `Try this:` 建议中。

* [#6386](https://github.com/leanprover/lean4/pull/6386) 确保当用户直接调用 `revertAll` 时，它会清除辅助声明。

* [#6387](https://github.com/leanprover/lean4/pull/6387) 修复了 `contradiction` 策略生成证明中的类型错误。

* [#6397](https://github.com/leanprover/lean4/pull/6397) 确保 `simp` 和 `dsimp` 不会展开用户本无意展开的定义。受此问题影响的示例见问题 #5755。

* [#6398](https://github.com/leanprover/lean4/pull/6398) 确保 `Meta.check` 会检查投影。

* [#6412](https://github.com/leanprover/lean4/pull/6412) 为化简器和 `grind` 策略使用的同余定理添加保留名。这样做是为了防止同一个同余定理被反复生成。

* [#6413](https://github.com/leanprover/lean4/pull/6413) 为仍在开发中的 `grind` 策略引入以下特性：
  - `Expr` 内化。
  - 同余定理缓存。
  - 添加新事实的过程。
  - 新的 tracing 选项。
  - 新的预处理步骤：折叠投影并消除悬空的 `Expr.mdata`。

* [#6414](https://github.com/leanprover/lean4/pull/6414) 修复了 `Lean.Meta.Closure` 中的一个问题。此前它会引入应用参数不足的延迟赋值元变量，使其永远无法被实例化。这个问题会影响 `match` 的精化，尤其是在期望类型中含有延迟处理的精化问题（例如策略块）时。

* [#6419](https://github.com/leanprover/lean4/pull/6419) 修复了仍在开发中的 `grind` 策略中的多个问题，并新增了打印 `grind` 内部状态的支持。

* [#6428](https://github.com/leanprover/lean4/pull/6428) 为 `grind` 策略新增一个预处理步骤：宇宙层级规范化。目标是避免在同余闭包模块中遗漏相等关系。

* [#6430](https://github.com/leanprover/lean4/pull/6430) 新增谓词 `Expr.fvarsSet a b`，当且仅当 `a` 的自由变量集合是 `b` 的自由变量集合的子集时，它返回 `true`。

* [#6433](https://github.com/leanprover/lean4/pull/6433) 为仍在开发中的 `grind` 策略新增自定义类型与实例规范化器。`grind` 使用同余闭包，但会忽略类型、类型构造器、实例和证明。由于证明无关性，证明会被忽略；类型、类型构造器和实例被视为辅助元素，不参与同余检测。相反，`grind` 只检查元素是否结构相等；在 `grind` 的上下文中，这等价于指针相等。新增测试展示了规范化器重要的例子。

* [#6435](https://github.com/leanprover/lean4/pull/6435) 为仍在开发中的 `grind` 策略实现了同余表，同时修复了若干问题，并新增一个预处理步骤。

* [#6437](https://github.com/leanprover/lean4/pull/6437) 为仍在开发中的 `grind` 策略新增检测 congruent 项的支持。它还引入了 `grind.debug` 选项；当该选项设为 `true` 时，每次合并等价类后都会检查大量不变量。这个选项仅用于调试。

* [#6438](https://github.com/leanprover/lean4/pull/6438) 确保 `norm_cast` 在存在 `no_index` 注解时不会失效。

* [#6441](https://github.com/leanprover/lean4/pull/6441) 为仍在开发中的 `grind` 策略新增基础的真值传播规则。

* [#6442](https://github.com/leanprover/lean4/pull/6442) 修复了 `grind` 中的 `checkParents` 健全性检查。

* [#6443](https://github.com/leanprover/lean4/pull/6443) 为仍在开发中的 `grind` 策略新增传播相等式真值的支持。

* [#6447](https://github.com/leanprover/lean4/pull/6447) 重构了 `grind`，并新增了使用 `GrindM` 单子调用化简器的支持。

* [#6448](https://github.com/leanprover/lean4/pull/6448) 声明了命令 `builtin_grind_propagator`，用于为 `grind` 注册方程传播器；同时也声明了配套的辅助属性。

* [#6449](https://github.com/leanprover/lean4/pull/6449) 完成了命令 `builtin_grind_propagator` 的实现。

* [#6452](https://github.com/leanprover/lean4/pull/6452) 为 `grind` 策略状态中属于同一等价类的任意两个表达式新增生成（小型）证明的支持。

* [#6453](https://github.com/leanprover/lean4/pull/6453) 改进了 `bv_decide` 在处理大字面量时的性能。

* [#6455](https://github.com/leanprover/lean4/pull/6455) 修复了仍在开发中的 `grind` 策略中相等性证明生成器的一个问题。

* [#6456](https://github.com/leanprover/lean4/pull/6456) 又修复了仍在开发中的 `grind` 策略中相等性证明生成器的一个问题。

* [#6457](https://github.com/leanprover/lean4/pull/6457) 为 `grind` 策略新增对已检测到的同余生成同余证明的支持。

* [#6458](https://github.com/leanprover/lean4/pull/6458) 为仍在开发中的 `grind` 策略新增紧凑同余证明支持。`mkCongrProof` 现在会检查该同余证明是否可以只用 `congr`、`congrFun` 和 `congrArg` 构造，从而避免生成更复杂的 `hcongr` 辅助定理。

* [#6459](https://github.com/leanprover/lean4/pull/6459) 新增仍在开发中的 `grind` 策略。目前它会生成一条警告消息，以明确说明该策略尚未可用于生产环境。

* [#6461](https://github.com/leanprover/lean4/pull/6461) 为仍在开发中的 `grind` 策略新增一条关于否定的传播规则。

* [#6463](https://github.com/leanprover/lean4/pull/6463) 为仍在开发中的 `grind` 策略新增构造子的支持。合并等价类时，`grind` 会检查构造子之间的相等式；如果构造子不同，就关闭目标；如果相同，则应用单射性。

* [#6464](https://github.com/leanprover/lean4/pull/6464) 为仍在开发中的 `grind` 策略完成了字面量值支持。现在只要 `grind` 合并了两个带有不同字面量值的等价类，就会关闭目标。

* [#6465](https://github.com/leanprover/lean4/pull/6465) 为仍在开发中的 `grind` 策略新增投影函数支持。

* [#6466](https://github.com/leanprover/lean4/pull/6466) 完成了仍在开发中的 `grind` 策略中 `addCongrTable` 的实现，同时新增测试说明额外检查为何必需，并更新了字段 `cgRoot`（同余根）。

* [#6468](https://github.com/leanprover/lean4/pull/6468) 修复了问题 #6467。

* [#6469](https://github.com/leanprover/lean4/pull/6469) 为在仍在开发中的 `grind` 策略中实现 E-匹配添加了支撑代码。

* [#6470](https://github.com/leanprover/lean4/pull/6470) 引入一条命令，用于指定 `grind` 策略在启发式实例化全局定理时使用的模式。请注意，这个 PR 只新增了解析器。

* [#6472](https://github.com/leanprover/lean4/pull/6472) 实现了命令 `grind_pattern`。这个新命令允许用户为定理关联模式。这些模式会用于基于 E-匹配的启发式实例化。未来还会加入 `@[grind_eq]`、`@[grind_fwd]` 与 `@[grind_bwd]` 属性，以自动为定理计算模式。

* [#6473](https://github.com/leanprover/lean4/pull/6473) 为 `ToExpr` 类新增派生处理器。它可以处理互递归和嵌套归纳类型，不过在这类情况下会退回为创建 `partial` 实例。这一实现是从 @kmill 编写的 Mathlib 派生处理器上游化而来，并修复了 autoimplicit 宇宙层级变量的处理问题。

* [#6474](https://github.com/leanprover/lean4/pull/6474) 为 `grind_pattern` 命令新增模式校验。新的 `checkCoverage` 函数也将用于实现 `@[grind_eq]`、`@[grind_fwd]` 和 `@[grind_bwd]` 属性。

* [#6475](https://github.com/leanprover/lean4/pull/6475) 为仍在开发中的 `grind` 策略新增激活相关定理的支持。若某个定理的模式中出现的符号也出现在 `grind` 目标中，则称这个定理与该 `grind` 目标相关。

* [#6478](https://github.com/leanprover/lean4/pull/6478) 在仍在开发中的 `grind` 策略中，激活 e匹配定理时会内化嵌套的 ground 模式。

* [#6481](https://github.com/leanprover/lean4/pull/6481) 为仍在开发中的 `grind` 策略实现了 E-匹配。我们仍需完成并内化新实例。

* [#6484](https://github.com/leanprover/lean4/pull/6484) 修复了若干差异未被展示出来的错误消息问题。

* [#6485](https://github.com/leanprover/lean4/pull/6485) 在仍在开发中的 `grind` 策略中实现了 `Grind.EMatch.instantiateTheorem`。

* [#6487](https://github.com/leanprover/lean4/pull/6487) 为 `structure` 父投影新增源位置信息，从而支持“转到定义”。关闭 #3063。

* [#6488](https://github.com/leanprover/lean4/pull/6488) 修复并重构了仍在开发中的 `grind` 策略的 E-匹配模块。

* [#6490](https://github.com/leanprover/lean4/pull/6490) 为 `grind` 策略新增基础配置选项。

* [#6492](https://github.com/leanprover/lean4/pull/6492) 修复了仍在开发中的 `grind` 策略中定理实例化过程的一个问题。

* [#6497](https://github.com/leanprover/lean4/pull/6497) 又修复了 `grind` 策略中一个定理实例化问题，并把需要处理的新实例移动到 `Goal`。

* [#6498](https://github.com/leanprover/lean4/pull/6498) 为 `grind` 策略新增传播依赖型全称量词项 `forall (h : p), q[h]` 的支持，其中 `p` 是一个命题。

* [#6499](https://github.com/leanprover/lean4/pull/6499) 修复了 `grind` 的证明规范化器。

* [#6500](https://github.com/leanprover/lean4/pull/6500) 修复了 `grind` 中 `markNestedProofs` 的一个问题。详见新增测试。

* [#6502](https://github.com/leanprover/lean4/pull/6502) 修复了 `grind` 策略使用的证明组装过程中的一个问题。

* [#6503](https://github.com/leanprover/lean4/pull/6503) 为仍在开发中的 `grind` 策略新增了一个简单策略：持续内化由 E-匹配发现的新定理实例。

* [#6506](https://github.com/leanprover/lean4/pull/6506) 新增 `monotonicity` 策略，供 `partial_fixpoint` 特性内部使用。

* [#6508](https://github.com/leanprover/lean4/pull/6508) 修复了 `grind` 策略健全性检查器中的一个问题。新增测试给出了它此前 panic 的一个例子。

* [#6509](https://github.com/leanprover/lean4/pull/6509) 修复了 `grind` 策略中使用的同余闭包数据结构的一个问题。新增测试包含一个此前会触发 panic 的例子。类似的 panic 也曾出现在测试 `grind_nested_proofs.lean` 中。

* [#6510](https://github.com/leanprover/lean4/pull/6510) 为 `grind` 中的相等关系新增一条自定义同余规则。该规则考虑到 `Eq` 是对称关系。未来还会加入对任意对称关系的支持。当前这条规则对 `grind` 有效传播不等式非常重要。

* [#6512](https://github.com/leanprover/lean4/pull/6512) 为 `grind` 策略引入用户自定义回退代码支持。回退代码可用于检查失败的 `grind` 子目标状态，或调用用户自定义自动化。用户现在可以写 `grind on_failure <code>`，其中 `<code>` 应具有类型 `GoalM Unit`。示例见该 PR 修改过的测试。

* [#6513](https://github.com/leanprover/lean4/pull/6513) 为 `grind` 策略新增对（依赖型）if-then-else 项（即 `ite` 与 `dite` 应用）的支持。

* [#6514](https://github.com/leanprover/lean4/pull/6514) 通过避免创建不必要的元变量，增强了 `grind` 中断言新事实的过程。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Library"
%%%

* [#6182](https://github.com/leanprover/lean4/pull/6182) 新增 `BitVec.[toInt|toFin]_concat`，并将若干定理移到 concat 章节，因为 `toInt_concat` 的证明需要 `BitVec.msb_concat`。

* [#6188](https://github.com/leanprover/lean4/pull/6188) 补全了 UInt 类型按位运算（`and`、`or`、`xor`、`shiftLeft`、`shiftRight`）的 `toNat` 定理，并新增了 `toBitVec` 定理。同时将 `and_toNat` 重命名为 `toNat_and`，以符合当前命名约定。

* [#6238](https://github.com/leanprover/lean4/pull/6238) 新增定理，用其二补码整数解释来刻画位向量无符号右移后的值。若无符号右移至少一位，则位向量的值不超过 `2^(w-1)`，并使其作为 `Int` 与 `Nat` 的解释一致。当 `n = 0` 时，右移后的值就等于该整数解释。

* [#6244](https://github.com/leanprover/lean4/pull/6244) 修改 `HashMap.toList` 的实现，使其顺序与 `HashMap.toArray` 一致。

* [#6272](https://github.com/leanprover/lean4/pull/6272) 引入 `Array` 排列的基础理论，并证明 `Array.swap_perm`。

* [#6282](https://github.com/leanprover/lean4/pull/6282) 将 `IO.Channel` 与 `IO.Mutex` 从 `Init` 移到 `Std.Sync`，并将它们重命名为 `Std.Channel` 与 `Std.Mutex`。

* [#6294](https://github.com/leanprover/lean4/pull/6294) 将 `List.length_flatMap`、`countP_flatMap` 和 `count_flatMap` 从 Mathlib 上游化。此前因为尚未上游化 `List.sum`，这些定理无法表达。

* [#6315](https://github.com/leanprover/lean4/pull/6315) 为 `Fin.cast` 与 `BitVec.cast` 添加 `protected`，以避免与 `_root_.cast` 混淆。无论如何，这些函数大多都应通过 dot-记法使用。

* [#6316](https://github.com/leanprover/lean4/pull/6316) 新增引理，将针对 `Option` 的 `for` 循环简化为 `Option.pelim`，从而与将 `List` 上的 `for` 循环简化为 `List.fold` 的引理保持一致。

* [#6317](https://github.com/leanprover/lean4/pull/6317) 补全了 BitVec.ofBool 的基础 API。

* [#6318](https://github.com/leanprover/lean4/pull/6318) 通过为 `Array.find?` 提供独立于 `Array.findM?` 的实现，推广了它的宇宙层级。

* [#6324](https://github.com/leanprover/lean4/pull/6324) 为基础 `Vector` 操作新增 `GetElem` 引理。

* [#6333](https://github.com/leanprover/lean4/pull/6333) 将 panic 函数泛化到 `Sort u` 类型，而非 `Type u`。这能更好支持宇宙多态类型，并避免令人困惑的错误。

* [#6334](https://github.com/leanprover/lean4/pull/6334) 为 `>>>` 在按位运算上的分配新增 `Nat` 定理，与 `BitVec` 上的对应定理保持一致。

* [#6338](https://github.com/leanprover/lean4/pull/6338) 新增 `BitVec.[toFin|getMsbD]_setWidth`、`[getMsb|msb]_signExtend` 以及 `ofInt_toInt`。

* [#6341](https://github.com/leanprover/lean4/pull/6341) 泛化 `DecidableRel`，使其支持异构关系。

* [#6353](https://github.com/leanprover/lean4/pull/6353) 为 `Array.any/all` 复现了 `List.any/all` 周边的 API。

* [#6364](https://github.com/leanprover/lean4/pull/6364) 采纳 Batteries 环境 linter 给出的修复建议，尤其是 `simpNF` 与 `unusedHavesSuffices`。

* [#6365](https://github.com/leanprover/lean4/pull/6365) 扩展了 `Array.set` 和 `Array.setIfInBounds` 的引理，以对齐现有的 `List.set` 引理。

* [#6367](https://github.com/leanprover/lean4/pull/6367) 让 `Vector` 关于成员关系与索引的引理与 `List` 和 `Array` 保持一致。

* [#6369](https://github.com/leanprover/lean4/pull/6369) 新增关于 `Vector.set`、`anyM`、`any`、`allM` 与 `all` 的引理。

* [#6376](https://github.com/leanprover/lean4/pull/6376) 为 `Vector` 上的 `==` 新增定理，对齐 `List` 与 `Array` 上已有的对应内容。

* [#6379](https://github.com/leanprover/lean4/pull/6379) 用从 Mathlib 上游化的 `List.Lex` 替换了归纳谓词 `List.lt`。（此前 `Lex.lt` 是用 `<` 定义的；现在则被泛化为接受任意关系。）这会细微改变 `List α` 上的顺序概念。

  `List.lt` 是较弱的关系：特别地，如果 `l₁ < l₂`，那么按照 `List.lt`，即便 `a` 与 `b` 只是不可比较（既非 `a < b`，也非 `b < a`），也可能有 `a :: l₁ < b :: l₂`；而按照 `List.Lex`，这就要求 `a = b`。

  当 `<` 是全序时，即 `¬ · < ·` 具有反对称性时，这两种关系是一致的。

  Mathlib 早已覆盖了 `List α` 的顺序实例，因此已经在使用 Mathlib 的用户应当不会注意到这项变化。

  我们同时新增了布尔值版本的 `List.lex` 函数，它以 `BEq` 类型类和任意 `lt` 函数为参数。这样就能通过弱于严格相等的 `==` 函数，支持此前 `List.lt` 所提供的灵活性。

* [#6390](https://github.com/leanprover/lean4/pull/6390) 重新定义 `Range.forIn'` 与 `Range.forM`，为后续编写相关引理做准备。

* [#6391](https://github.com/leanprover/lean4/pull/6391) 要求 `Std.Range` 中的步长必须为正，以避免语义不明确的行为。

* [#6396](https://github.com/leanprover/lean4/pull/6396) 新增引理，将基于 `Std.Range` 的 `for` 循环规约为基于 `List.range'` 的 `for` 循环。

* [#6399](https://github.com/leanprover/lean4/pull/6399) 为 `Array` 与 `Vector` 新增关于字典序的基础引理，与 `List` 对齐。

* [#6423](https://github.com/leanprover/lean4/pull/6423) 为 `List`/`Array`/`Vector` 补上缺失的字典序引理。

* [#6477](https://github.com/leanprover/lean4/pull/6477) 增加支撑 `partial_fixpoint` 特性所需的 domain theory。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Compiler"
%%%

* [#6311](https://github.com/leanprover/lean4/pull/6311) 为新代码生成器新增 `HEq` 支持。

* [#6348](https://github.com/leanprover/lean4/pull/6348) 为 Lean 运行时新增 `Float32` 支持。

* [#6350](https://github.com/leanprover/lean4/pull/6350) 为 `Float32` 支持补齐缺失特性并修复问题。

* [#6383](https://github.com/leanprover/lean4/pull/6383) 确保新的代码生成器会为未标记为 `@[extern]` 的 `opaque` 定义生成代码。备注：这是旧代码生成器的行为。

* [#6405](https://github.com/leanprover/lean4/pull/6405) 为新代码生成器新增擦除 `Decidable.decide` 的支持。同时新增 `Probe.runOnDeclsNamed` 函数，有助于为编译器内部编写有针对性的单文件测试。

* [#6415](https://github.com/leanprover/lean4/pull/6415) 修复了 `sharecommon` 模块中的一个问题。此前它会对已经由 `sharecommon` 处理过的对象返回错误结果。触发该问题的例子见新增测试。

* [#6429](https://github.com/leanprover/lean4/pull/6429) 为 extern LCNF 声明新增支持，这是与现有代码生成器保持一致所必需的。

* [#6535](https://github.com/leanprover/lean4/pull/6535) 避免了 Windows 上的链接器警告。

* [#6547](https://github.com/leanprover/lean4/pull/6547) 应可防止 Lake 意外拾取机器上安装的其他链接器。

* [#6574](https://github.com/leanprover/lean4/pull/6574) 真实地阻止了 Lake 意外拾取机器上安装的其他工具链。

## 漂亮打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Pretty-Printing"
%%%

* [#5689](https://github.com/leanprover/lean4/pull/5689) 调整了漂亮打印器反解析名称的方式。以前漂亮打印时会使用所有 `export`；现在只使用那些把名称导入父命名空间的 `export`（启发式地说，这些是库作者有意提供的“API 导出”），而不再使用把名称导入无关命名空间的“横向导出”；#6189 中的 dot 记法特性现在会鼓励后者。

* [#5757](https://github.com/leanprover/lean4/pull/5757) 除了引入带标签的 `sorry` 外，还修复了一个问题：带借用注解参数（例如 `String.append` 的第二个参数）漂亮打印后附带的元数据，与普通参数附带的元数据不一致。

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Documentation"
%%%

* [#6450](https://github.com/leanprover/lean4/pull/6450) 为 `@[app_delab]` 属性添加文档字符串。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Server"
%%%

* [#6279](https://github.com/leanprover/lean4/pull/6279) 修复了结构实例字段补全中的一个问题。此前它在使用 Mathlib 风格方括号结构实例时无法正常工作。

* [#6408](https://github.com/leanprover/lean4/pull/6408) 修复了一次回归：此前不存在的目标也会被显示出来。这个回归由 #5835 触发，最初源于 #4926。

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Lake"
%%%

* [#6176](https://github.com/leanprover/lean4/pull/6176) 修改了 Lake 的构建流程，不再使用 `leanc` 编译 C 文件或链接共享库与可执行文件。取而代之的是，它直接以所需参数调用随包附带的编译器（若无则调用本地编译器）。

* [#6289](https://github.com/leanprover/lean4/pull/6289) 调整 Lake 模块以使用 `prelude`，并将其纳入 `check-prelude` CI。

* [#6291](https://github.com/leanprover/lean4/pull/6291) 确保在把零散日志条目追加到作业日志前部时，日志错误位置能被正确保留。同时还为 `Log.Pos` 增加了比较支持。

* [#6388](https://github.com/leanprover/lean4/pull/6388) 合并了 `BuildJob` 与 `Job`，并弃用了前者。`Job` 现在会把跟踪作为其状态的一部分，并可通过单子方式进行交互；同时也简化了 `OpaqueJob` 的实现。

* [#6411](https://github.com/leanprover/lean4/pull/6411) 新增能力：可通过独立的 JSON 文件覆写 Lake 清单中的包条目。这个文件可以通过命令行 `--packages` 指定，也可以持久放置在 `.lake/package-overrides.json`。

* [#6422](https://github.com/leanprover/lean4/pull/6422) 修复了 #6388 中的一个问题：此前 `Package.afterBuildCahe*` 函数会因缓存是否被抓取而生成不同的跟踪。

* [#6627](https://github.com/leanprover/lean4/pull/6627) 旨在修复 Mathlib 报告的跟踪问题，这些问题会导致下游项目中的 `lake exe cache` 失效。

* [#6631](https://github.com/leanprover/lean4/pull/6631) 为共享库设置 `MACOSX_DEPLOYMENT_TARGET`（此前只对可执行文件设置）。

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___16___0-_LPAR_2025-02-03_RPAR_--Other"
%%%

* [#6285](https://github.com/leanprover/lean4/pull/6285) 将 `ToLevel` 类型类从 mathlib 上游化，并用它修复现有 `ToExpr` 实例，使其真正具备宇宙多态性（此前当宇宙层级非零时会生成格式错误的表达式）。我们还在 mathlib 的 `ToLevel` 定义基础上做了改进，确保该类无论宇宙参数如何都始终位于 `Type` 中。

* [#6363](https://github.com/leanprover/lean4/pull/6363) 修复了 Firefox 性能分析器比较模式在加载时的错误。

````
