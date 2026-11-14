/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.36.0-rc2 (2026-10-27)" =>
%%%
tag := "release-v4.36.0"
file := "v4.36.0"
%%%

:::warn
这些发布说明描述的是_候选版本_，而非最终版本。
内容可能不完整，并且可能变化。
:::

此版本合入了 219 项更改。
除下面列出的 65 项新增功能
和 83 项修复外，
还有 11 项重构，
1 项文档改进，
30 项性能改进，
3 项测试套件改进，
以及 26 项其他更改。

# 语言
%%%
file := "Language"
tag := "Manual-Releases-v4_36_0-Language"
%%%

```markdown

- [#15839](https://github.com/leanprover/lean4/pull/15839)
  修复一处竞争条件：原实现本应在模块文档字符串之间持久保存作用域扩展状态，但未正确实现。修复方式是移除此错误功能，未来 PR 可能以正确版本替代。

- [#15572](https://github.com/leanprover/lean4/pull/15572)
  为“`[deprecated]` 属性应指定开始弃用的日期或库版本”警告添加提示与代码操作。

- [#15499](https://github.com/leanprover/lean4/pull/15499)
  使生成的方程引理（`f.eq_1`、`f.eq_2` 等）的陈述不依赖首次请求方程时的选项。此前首个使用方程的证明中的局部 `set_option` 可能改变陈述；由于证明并行精译，同一文件不同构建的陈述可能不同，导致某些线程数下编译成功、另一些下失败。

- [#15485](https://github.com/leanprover/lean4/pull/15485)
  命令存在语法错误且禁用 `showPartialSyntaxErrors` 时，跳过无状态检查器。

- [#14316](https://github.com/leanprover/lean4/pull/14316)
  使类型类解析缓存在命令间持久保存：若查询不含元变量、局部实例或自由变量，且结果本身封闭，就供后续命令复用，相同查询不再重新搜索。仅在记录的依赖未变化时使用条目，因此新实例、合一提示和可约性变化会精确使受影响条目失效。标准库构建中类型类解析时间减少约 14%，总指令数减少 1.2%；Mathlib 总体改善 0.2%，因为多数查询含尚未持久缓存的局部实例。

- [#15399](https://github.com/leanprover/lean4/pull/15399)
  修复类型类解析缓存在可能观察到的声明改变后仍返回旧结果的问题，尤其是后续 `attribute [reducible]`，或作用域、局部可约性属性生效和失效时。目前缓存局限于单个命令，故较少显现，但这是跨命令共享缓存所需的前提，因为此类变化在命令间很常见。

- [#15319](https://github.com/leanprover/lean4/pull/15319)
  新增 `Expr.hasAnyMVar`、`Expr.containsMVar`，对应已有的 `Expr.hasAnyFVar`、`Expr.containsFVar`。

- [#15355](https://github.com/leanprover/lean4/pull/15355)
  使 `SavedState.restore` 丢弃被回滚的已跟踪环境变化之后记录的类型类解析缓存条目。验证条目的代次随环境回滚，但 `Meta.Cache` 保留，后续不同变化可能恢复记录的代次并误用旧条目；例如失败尝试中添加后回滚的实例，可能在添加另一实例后仍被返回。除修复边界情况外，这也是跨命令缓存的前提：条目需经受回溯而不对已回滚状态重新验证。

- [#15354](https://github.com/leanprover/lean4/pull/15354)
  使类型类解析缓存条目记录搜索所查询的实例与合一提示状态，变化后即停止使用条目，即使环境变化不会清空缓存。例如，通过 `liftCommandElabM` 运行命令添加的实例现在能被同一计算的后续查询找到，在 `CoreM` 层激活的作用域实例和合一提示也同样如此。除修复边界情况外，这也是跨命令缓存的前提。

- [#15325](https://github.com/leanprover/lean4/pull/15325)
  使类型类解析缓存结果依赖搜索读取的选项。此前命令内缓存复用忽略选项，因此项级 `set_option`（如 `synthInstance.maxSize`）下的结果可能在选项值不同的地方使用。搜索从未读取的选项仍不会划分缓存。除修复命令内边界情况外，这也是跨命令缓存的前提。

- [#15313](https://github.com/leanprover/lean4/pull/15313)
  不再为每个函数重新推导并检查整个相互定义块的不动点方程，大幅加速大型相互 `partial_fixpoint` 块方程引理的实现化；200 个函数的块约快 13 倍。

- [#11386](https://github.com/leanprover/lean4/pull/11386)
  添加标注 `wf_preprocess` 的定理，使用户可像使用 `List.map` 等常用列表函数一样，方便地使用 `List.any` 编写树等嵌套归纳类型上的函数。

- [#15286](https://github.com/leanprover/lean4/pull/15286)
  使 `deprecated_syntax` 标注的策略每次调用至多警告一次，展开中使用的策略不再重复警告。例如弃用 `mintro` 后，`mintro a b c` 展开为 `mintro a; mintro b c`，原先打印五条警告，现在只有一条。

- [#15216](https://github.com/leanprover/lean4/pull/15216)
  使 `inferInstanceAs` 复用非公开定义的现有实例。通过在私有作用域检查实例可复用性实现，因为此时新生成及已有实例中的辅助定义都不公开。

- [#15204](https://github.com/leanprover/lean4/pull/15204)
  当 simp 实参是 simproc 或 simp 扩展时，拒绝 `←` 修饰符，不再静默忽略。

- [#15237](https://github.com/leanprover/lean4/pull/15237)
  添加 `Environment.realizationEnvContains forConst c`，报告 `realizeConst forConst` 回调能否访问 `c`。当实现化依赖多个常量时，据此选择 `forConst`：目标的实现化环境必须包含其余全部常量。

- [#14537](https://github.com/leanprover/lean4/pull/14537)
  改进 `rfl` 等因定义相等性检查失败而失败的策略的错误消息。此前已能分析需显式显示项的哪些部分才能揭示不匹配，但有时采用错误配置；现修复这些问题。

- [#15242](https://github.com/leanprover/lean4/pull/15242)
  去除构造 `brecOn` 应用中不影响结果的工作，加速结构递归定义的精译。

- [#15240](https://github.com/leanprover/lean4/pull/15240)
  使 `Meta.isProofQuick` 对类型为 `motive` 变量应用于实参的 `match` 辅助函数、`casesOn`、`brecOn` 和递归器等应用给出确定答案。此前会进入 `isProof` 的慢路径，推断类型并归约到 sort。

- [#15239](https://github.com/leanprover/lean4/pull/15239)
  精译结构递归定义时移除冗余的 `abstractNestedProofs` 处理，减少含大量此类定义的文件的精译时间。

- [#15238](https://github.com/leanprover/lean4/pull/15238)
  移除 #15232 在 LCNF 声明扩展引入的逐声明开销；它在编译大量声明的模块时耗费约 1% 指令，同时保留已实现化常量的线性时间重放。

- [#15232](https://github.com/leanprover/lean4/pull/15232)
  使常量实现化的代价（例如 `simp only [f]` 所需方程引理）不再依赖当前文件大小。此前包含大量实现化的文件会出现二次减速；4000 对定义/定理的文件精译从 99 秒降至 32 秒，每对耗时现在恒定。

- [#15230](https://github.com/leanprover/lean4/pull/15230)
  加速含 `match` 的定义及使用 `mkAuxDefinition`、`mkAuxTheorem` 且 `zetaDelta := false` 创建的辅助定义的精译。在含 12800 个小模式匹配定义的文件中，累积精译时间从约 19 秒降至约 17 秒。

- [#15228](https://github.com/leanprover/lean4/pull/15228)
  修复前端逐命令开销随命令在文件中位置线性增长，导致多命令文件二次增长的问题。

- [#15223](https://github.com/leanprover/lean4/pull/15223)
  修复大量递归定义文件精译的二次减速：定义精译中的 `share common exprs` 每次递归调用都对完整输入文件哈希，数千个结构递归或良基递归定义的文件可能将大部分时间耗在此处。

- [#15091](https://github.com/leanprover/lean4/pull/15091)
  为 `def` 契约添加位于 `ensures` 后的 `throws e => R` 子句，陈述生成规约定理的异常后置条件。它绑定抛出的异常，若为状态单子还绑定抛出时状态。`throws (e : ε) s => R` 的类型标注选择 `ε` 类型异常层；无标注则选择最外层。未提及异常层保持后置条件 `⊥`，因此仍排除其异常；省略 `ensures` 则保持后置条件 `⊤`。

- [#15064](https://github.com/leanprover/lean4/pull/15064)
  替换 Verso 文档字符串解析器，正确跟踪底层具体语法的全部细节；同时改进文档字符串扩展 API，并使解析错误更便于采取行动。这为自动格式化 Verso 文档语法扫清障碍。

- [#15199](https://github.com/leanprover/lean4/pull/15199)
  移除为自举引入的 `Lean.Elab.BuiltinDo.Let`、`Lean.Elab.Do.InferControlInfo` 中的 `internal.parseQuotWithCurrentStage` 选项，消除 #15090 引入的构建指令数回退。

```

# 库
%%%
file := "Library"
tag := "Manual-Releases-v4_36_0-Library"
%%%

```markdown

- [#15654](https://github.com/leanprover/lean4/pull/15654)
  修复 `String.toByteArray`、`String.toUTF8` 中长期存在、由近期新增测试发现的内存泄漏。

- [#15581](https://github.com/leanprover/lean4/pull/15581)
  将 `String` 的序重新定义为 UTF-8 编码的字典序，而非字符列表的字典序。

- [#15659](https://github.com/leanprover/lean4/pull/15659)
  导出 `Init.Data.Int.DivMod.Pow` 中声明的引理。

- [#15651](https://github.com/leanprover/lean4/pull/15651)
  新增 `String.fromUTF8Lossy`，尝试将 `ByteArray` 解析为 `String`，并按明确规定的方式用 Unicode 替代字符替换无效 UTF-8。

- [#15647](https://github.com/leanprover/lean4/pull/15647)
  为 `UIntX`/`IntX` 位运算补齐 simproc。

- [#15628](https://github.com/leanprover/lean4/pull/15628)
  使 `Lean.Json.parse` 拒绝重复键（转义解码后比较）的 JSON 对象，而非静默保留最后一个值。

- [#15594](https://github.com/leanprover/lean4/pull/15594)
  重命名错误函数及其他辅助函数。

- [#15547](https://github.com/leanprover/lean4/pull/15547)
  添加基于 RAII 的作用域锁守卫。

- [#15545](https://github.com/leanprover/lean4/pull/15545)
  移除 uv 套接字、定时器和信号对象中 libuv 句柄的独立分配。

- [#15571](https://github.com/leanprover/lean4/pull/15571)
  修复 `LT JsonNumber` 实例处理 `0` 的方式；此前 `(0 : JsonNumber) < 5e-2` 求值为 `false`。

- [#15523](https://github.com/leanprover/lean4/pull/15523)
  修复 libuv 定时器与信号的崩溃：

  * 单次定时器和信号回调在释放事件循环对句柄的引用前兑现承诺（sync := true），导致崩溃。
  * libuv 将重复周期 0 视为单次定时器，因此周期 0 毫秒的重复 `Timer` 只触发一次，后续承诺一直等待。现在每毫秒触发一次。
  * `Signal.cancel` 只丢弃待兑现承诺，保留处理器监听；无承诺等待时到达的信号会兑现下次 `next` 的承诺。
  * 各平台上的信号等待器都用 `Signal.toInt32` 的数值兑现，而非操作系统的信号编号。

- [#15469](https://github.com/leanprover/lean4/pull/15469)
  使 `Std.Http` 服务器按 RFC 9110 §5.6.7 的 HTTP-date 格式生成 `Date` 头，如 `Sun, 06 Nov 1994 08:49:37 GMT`，而非数字时区偏移（`+0000`）。Apache HttpClient 缓存、Go 的 `http.ParseTime`、Rust 的 `httpdate` 等严格解析 HTTP 日期的客户端不接受旧格式。

- [#15533](https://github.com/leanprover/lean4/pull/15533)
  在 Lean 中重新实现 `String.toList`，同时移除所有曾有
  `String.data` 的痕迹，后者弃用至今已近一年。

- [#15443](https://github.com/leanprover/lean4/pull/15443)
  使 `Std.Http` 服务器在无时区数据库的系统（如不带 `tzdata` 的 `ubuntu:24.04` Docker 镜像）上也能发送响应。此前生成 `Date` 头时需在 zoneinfo 文件中查找 `UTC`，导致每次连接均不返回响应就关闭。

- [#15517](https://github.com/leanprover/lean4/pull/15517)
  将 `Lean.Order.iSup`、`Lean.Order.iInf` 的索引改为 `{ι : Sort v}`，使对命题 `P` 的 `⨆ h : P, f h` 可精译。`le_iSup`、`iSup_le`、`iInf_le`、`le_iInf`、`iSup_apply`、`iInf_apply` 使用相同的 `Sort` 索引。

- [#15175](https://github.com/leanprover/lean4/pull/15175)
  修复 `Loop.configure` 泄漏，并在分配巨大数组前拒绝超过 2^31-1 的 `System.random` 值。

- [#15329](https://github.com/leanprover/lean4/pull/15329)
  为 `ByteArray` 添加高效 `LE` 与 `Ord` 实例，并由此推导全部其他序实例。

- [#15316](https://github.com/leanprover/lean4/pull/15316)
  移除 `Init.Data.Option.Basic` 中重复派生的 `BEq (Option a)` 实例，改为公开 `Init.Core` 中派生的实例。

- [#15315](https://github.com/leanprover/lean4/pull/15315)
  调整 `Array.compareLex` 和 `Vector.compareLex` 的属性，确保真正进行特化；此前比较函数仅通过闭包传递。

- [#15304](https://github.com/leanprover/lean4/pull/15304)
  补齐 `List`、`Array`、`Vector` 的序实例。

- [#15299](https://github.com/leanprover/lean4/pull/15299)
  使 `grind` 及 `vcgen … with finish` 更可靠地证明使用格运算的断言目标。例如 `vcgen` 教程的 `nodup` 证明现在可用 `vcgen … with finish` 关闭，像过去使用 `mvgen` 时一样。

- [#15414](https://github.com/leanprover/lean4/pull/15414)
  降低某些过于积极、会过早触发跨理论推理的 grind E-匹配标注的激进程度。

- [#15387](https://github.com/leanprover/lean4/pull/15387)
  为 `Std.Internal.Order` 的格理论添加引理及谓词变换器的计算规则。

- [#15192](https://github.com/leanprover/lean4/pull/15192)
  修复 `ContextAsync.race`、`ContextAsync.raceAll`、`ContextAsync.run`、`ContextAsync.background` 的取消行为；`Notify.notifyOne` 不再将唤醒机会浪费在选择结果已决定的等待器上。

- [#15274](https://github.com/leanprover/lean4/pull/15274)
  补齐 `BitVec` 的序实例。

- [#15174](https://github.com/leanprover/lean4/pull/15174)
  解决 TCP、UDP 模块中的多个问题。

- [#15266](https://github.com/leanprover/lean4/pull/15266)
  为 #15257 添加的 `Float.minimum`、`Float.minimumNumber` 操作提供逻辑模型。

- [#15257](https://github.com/leanprover/lean4/pull/15257)
  定义对应 IEEE-754-2019 同名操作的 `Float.minimum`、`Float.minimumNumber`，并将 `Min Float` 重新定义为 `Float.minimum`。

- [#15115](https://github.com/leanprover/lean4/pull/15115)
  公开 `Char.ordinal`、`Char.ofOrdinal`、`Char.succ?`、`Char.succMany?`，使其跨模块边界归约。`Char` 上的范围通过 `UpwardEnumerable Char` 实例由后两者构造，因此此前在使用模块系统的文件中，`cbv`、内核归约会卡在这些应用处。

- [#15247](https://github.com/leanprover/lean4/pull/15247)
  添加基础的 CaDiCaL FFI 模块，以及与 `Std.Sat` API 交互的小型包装。

- [#15252](https://github.com/leanprover/lean4/pull/15252)
  移除 `withPtrEq` 函数。

- [#15217](https://github.com/leanprover/lean4/pull/15217)
  将类型变量 `EPred` 更名为 `EPosts`、值变量 `epost` 更名为 `eposts`，因为它们表示异常后置条件的集合而非单个谓词；提供 deprecated_arg 别名，使按名称传递 `EPred` 的代码仍能编译。

- [#15171](https://github.com/leanprover/lean4/pull/15171)
  为一致性重命名多个 `Std.WP` 名称，并弃用旧名：`WP.wpTrans` 投影改为 `WP.trans`，单调性字段 `WP.wp_trans_monotone` 改为 `WP.trans_monotone`，引理 `wpTrans_apply_eq` 改为 `trans_apply_eq`。最弱前置条件单调性引理 `WP.wp_consequence`/`wp_econs` 改为统一的 `wp_monotone` 系列：双通道使用 `wp_monotone`，单通道使用 `wp_monotone_post`、`wp_monotone_epost`，空异常后置条件使用 `wp_monotone_bot`，并提供 `_le` 传递性变体。

- [#15201](https://github.com/leanprover/lean4/pull/15201)
  重构 AIG 到 CNF 转换，从仅操作 `AIG Nat` 推广到泛型 `AIG`，有两项优势：
  1. 无需执行 `relabelNat`，CNF 表示也略高效：不再用 AIG 原子的 `Nat` 标识，而直接用 AIG 索引，避免为每个 AIG 原子额外生成一个 Tseitin 原子。
  2. 未来可跨多次运行增量使用 AIG 到 CNF API；为此已引入 `State.cast`，以跨运行复用缓存状态。

- [#15067](https://github.com/leanprover/lean4/pull/15067)
  将框架机制扩展到 `Std.WP` 的异常通道。例如，异常退出携带状态的程序逻辑现在支持 `⦃P⦄ x ⦃Q; E⦄ → ⦃F ⋆ P⦄ x ⦃F ⋆ Q; F ⋆ E⦄` 这样的框架规则。框架闭包、框架条件及框架规则增加异常后置条件的配套操作 `opE : R → EPred → EPred`，默认忽略框架。

- [#14793](https://github.com/leanprover/lean4/pull/14793)
  修复 #14776。

- [#14795](https://github.com/leanprover/lean4/pull/14795)
  修复 UDP 和 TCP 模块接收函数的两个问题。

```

# 策略
%%%
file := "Tactics"
tag := "Manual-Releases-v4_36_0-Tactics"
%%%

```markdown

- [#15750](https://github.com/leanprover/lean4/pull/15750)
  修复 #15420 引入并由 leanprover/cslib#1141 报告的两处 `grind` 回归：关于 λ-项上归纳谓词的证明在 v4.35.0 成功，却在 v4.36.0-rc1 失败。规范化器现在对所有 `α` 将 `∀ _ : α, True` 重写为 `True`，不再仅限命题；`grind` 对新假设执行的立即 `cases` 也像其他情形拆分一样重置 E-匹配轮数。

- [#15678](https://github.com/leanprover/lean4/pull/15678)
  修复启用 `Sym.simp` 规范化器（`set_option backward.grind.normalizer false`）时，`grind` 无法证明有序环中 `c = b → a ≤ b + c + d → a ≤ b + b + d` 等目标的问题。规范化将 `b + b + d` 改为 `2 * b + d`，使两不等式在 `c = b` 后不再同余，而原先没有模块关联两个和。

- [#15675](https://github.com/leanprover/lean4/pull/15675)
  修复 `linarith` 在无 `LawfulOrderLT` 实例的类型上推理 `<` 时，`grind` 报内部错误“structure does not have a lawful LT instance”或“structure does not support LT”的问题。例如 `[IntModule α] [LE α] [LT α] [IsLinearOrder α] [OrderedAdd α] (a b c : α) : a < b → b < c → a < c` 现在以普通 `grind failed` 消息失败。

- [#15672](https://github.com/leanprover/lean4/pull/15672)
  修复启用 `Sym.simp` 规范化器（`set_option backward.grind.normalizer false`）时，`grind` 无法使用域中数值 `k` 的 `k⁻¹` 的问题。例如此前无法证明 `[Field R] [IsCharP R 0] (h : f (a * 2⁻¹) = 1) (h2 : a = 2 * b) : f b = 1`。

- [#15642](https://github.com/leanprover/lean4/pull/15642)
  为基于 `Sym.simp` 的 `grind` 规范化器添加默认 `false` 的 `Grind.Config.distrib`。默认像旧规范化器一样，将 `x * (y + 1)` 等非常量多项式之积、和的幂、积的逆保留为因子已规范化的原子；`grind +distrib` 则展开为多项式范式。线性算术把非线性项视为原子，保持未展开可在导出 `y + 1 = z` 后保留 `x * (y + 1) = x * z` 等事实。

- [#15624](https://github.com/leanprover/lean4/pull/15624)
  使 `grind` 将符号位宽 `w` 的 `k#w` 字面量转为所用的 `BitVec` 字面量 `OfNat.ofNat` 形式，使 `Sym.simp` 规范化器下 `BitVec.sdiv_zero` 等定理能像旧规范化器一样应用于 `x.sdiv 0`。

- [#15623](https://github.com/leanprover/lean4/pull/15623)
  使基于 `Sym.simp` 的 `grind` 规范化器重写依赖命题绑定的定义域，例如将 `∀ h : i < a.size, q h` 变为 `∀ h : i + 1 ≤ a.size, ...`，与旧规范化器一致。

- [#15619](https://github.com/leanprover/lean4/pull/15619)
  修复基于 `Sym.simp` 的 `grind` 规范化器处理模式含算术的 `match` 方程时的 panic，例如对匹配 `Vec α (n + 1 + 1)` 的函数使用 `grind [h.eq_def]`。

- [#15618](https://github.com/leanprover/lean4/pull/15618)
  修复 `grind` 在抽象环上类型转换中误报 `ring term with unexpected instance` 的问题，例如 `[CommRing R]` 下的 `(m + n) • a = m • a + n • a`，以及基于 `Sym.simp` 的规范化器的相应失败。

- [#15616](https://github.com/leanprover/lean4/pull/15616)
  将 `BitVec.zero`、`BitVec.ofNat _ (Bool.toNat _)` 和 `BitVec.carry` 加入 `bv_decide` 支持的项。

- [#15612](https://github.com/leanprover/lean4/pull/15612)
  修复由 `intros` 引入或作为参数事实断言的假设，其类型标注 `[grind cases eager]` 时被 `grind` 丢失的问题。原先各分支只保留构造器字段，因此对无字段构造器的谓词 `P`，`example : P → ¬P → False := by grind` 及目标 `P` 上的 `grind [(mkP)]` 会失败。

- [#15611](https://github.com/leanprover/lean4/pull/15611)
  修复参数事实类型标注 `[grind cases eager]` 时，`grind?` 报“proof contains unresolved internal metavariable”。这种事实在初始化时拆分目标，而原先只为第一个目标生成脚本；现在处理每个目标，并在建议脚本中为每个目标提供一个 `·` 块。

- [#15609](https://github.com/leanprover/lean4/pull/15609)
  使 `grind [mkP]` 接受陈述不是 `∀` 且不可索引的定理，如零元归纳谓词 `P` 的 `theorem mkP : P`。参数被作为事实断言，不再需要 `grind [(mkP)]` 变通写法；`grind?` 与 `finish?` 的建议也保留这些标识符。

- [#15606](https://github.com/leanprover/lean4/pull/15606)
  修复 `finish?` 仅凭参数就关闭目标时误报“generated tactic cannot close the goal”的警告，例如 `grind => finish? [inj f_inj]`。

- [#15602](https://github.com/leanprover/lean4/pull/15602)
  修复 `grind?`、`finish?` 在建议中丢失 `inj f_inj`、`funCC q` 等参数，导致粘贴后失败的问题。

- [#15600](https://github.com/leanprover/lean4/pull/15600)
  修复 `grind` 在由 `@[implicit_reducible]` 定义包装的实例上失败的问题。

- [#15599](https://github.com/leanprover/lean4/pull/15599)
  修复 `grind` 内部错误 `ring term has not been internalized`：环求解器发现 `a ≠ b` 等不等式时，含 `a - b` 的项仍在内部化；Rabinowitsch 步骤随即构造并内部化 `(a - b) * (a - b)⁻¹`，但 `(a - b)⁻¹` 尚无 `ENode`。关闭 #15590。

- [#15589](https://github.com/leanprover/lean4/pull/15589)
  修复 `grind ring` 在 `BitVec n` 等无 `NoNatZeroDivisors` 的环中传播蕴含等式时的 panic。

- [#15588](https://github.com/leanprover/lean4/pull/15588)
  修复作用域内存在高优先级自定义 `Pow Int Nat` 实例时 `grind` 的内部错误 `ring term has not been internalized`；#15506 后，Mathlib 的 `Int` 上 `Monoid.npow` 实例会触发此情况。

- [#15555](https://github.com/leanprover/lean4/pull/15555)
  使 `vcgen` 应用规约时从目标的 `wp` 应用获取程序类型和 `WP` 实例，因此即使程序类型与实例程序类型不同也可工作，例如 `def Tagged (n : Nat) (α : Type) := α` 下，目标 `wp (Prog := Tagged n Exp) e Q E` 中的程序 `e : Exp`。

- [#15582](https://github.com/leanprover/lean4/pull/15582)
  使 `cbv` 像处理 `ite`、`dite` 一样惰性求值 `cond`（`bif c then a else b`）。此前即使条件为字面量 `true`，也求值两个分支；未选中的昂贵或不终止分支会浪费时间或耗尽 `cbv.maxSteps`。修复使 `cond` simproc 模式包含全部四个实参。

- [#15497](https://github.com/leanprover/lean4/pull/15497)
  为 `WP.Frames` 添加守卫，使 `vcgen` 能为占用范围依赖状态的程序保留跨调用的资源框架。

- [#15526](https://github.com/leanprover/lean4/pull/15526)
  修复使用 `module` 的文件中，`sym => simp` 在非依赖箭头（如 `x + 0 = y → p`）内重写时的内核错误。

- [#15515](https://github.com/leanprover/lean4/pull/15515)
  使 `vcgen` 将规约前置条件 `fun _ => ∃ h : i < xs.size, Q () xs[i]` 拆为验证条件 `i < xs.size` 及假设 `h` 下关于 `Q () xs[i]` 的蕴涵，使主体中程序尾部的 `wp` 得以推进。`fun _ => ⨆ h : i < xs.size, Q () xs[i]` 同样拆分。

- [#15524](https://github.com/leanprover/lean4/pull/15524)
  修复 `grind [h _ _ pf]` 等唯一孔是证明的提示导致 `unknown free variable` 内部错误；#15506 后它破坏了 Mathlib 的 `List.pairwise_iff_forall_infix`。

- [#15506](https://github.com/leanprover/lean4/pull/15506)
  修复幂传播重建仍在内部化实参的项时，`grind` 报 `semiring term has not been internalized` 的内部错误（#15479）。

- [#15503](https://github.com/leanprover/lean4/pull/15503)
  修复 `sym` 配合 `arith`、以及 `grind` 配合 `Sym.simp` 规范化器在 `{α : Sort u} (a b : α)` 等 `Sort u` 类型等式目标上的失败。环分类器使用 `getDecLevel` 计算载体宇宙层级，会报“invalid universe level, u is not greater than 0”；现在用 `getDecLevel?` 并报告类型无环结构，与序分类器一致。

- [#15491](https://github.com/leanprover/lean4/pull/15491)
  使 `vcgen` 识别更多 `@[spec]` 前置条件对模式后置条件 `Q`/`E` 保持合取的情况；对此类规约直接应用，不运行框架推断。

- [#15487](https://github.com/leanprover/lean4/pull/15487)
  使 `vcgen` 像格的交 `⊓` 一样拆分规约前置条件中的逐点 `∧`。

- [#15483](https://github.com/leanprover/lean4/pull/15483)
  使 `Sym.simp` 像 `Meta.simp` 一样，将不处于数值实参位置的原始 `Nat` 字面量重写为 `OfNat.ofNat`。模式变量绑定原始数值字面量的规则，如 `[grind hom]` 规则 `(OfNat.ofNat a : Fin n).val = a % n`，会生成 `nat_lit 0 % (p + 1)` 等后续步骤不再识别为数值的项，导致采用 `Sym.simp` 规范化器的 `grind` 在 `Fin (p + 1)`、`BitVec n` 目标上失败。

- [#15482](https://github.com/leanprover/lean4/pull/15482)
  使 `grind` 能证明 `UIntN`、`BitVec` 上乘以接近模数的数值的目标，例如 `UInt32` 上 `-1 * a`、`4294967295 * a`；此前会耗尽 `lia` 步数。`[grind hom]` 注入 `Nat` 时将 `(c * a).toNat` 变为 `c * a.toNat % 2^w`，`cutsat` 精确消去 `a.toNat` 时会按系数 `c` 拆分；而 `(-a).toNat` 为 `(2^w - a.toNat) % 2^w`，系数仅为 `1`。

- [#15478](https://github.com/leanprover/lean4/pull/15478)
  修复 `grind` 环模块生成被内核拒绝的证明。对数值 `a` 的逆 `a⁻¹`，`processInv` 使用数值为 `denoteInt k`（即 `OfNat` 数值或其相反数）的定理断言 `a * a⁻¹ = 1` 或 `a⁻¹ = 0`；但识别器也接受仅与它命题相等的 `↑(0 : Nat)`、`↑(3 : Int)`、`-0`、`- -3`，从而把 `Field.inv_zero : 0⁻¹ = 0` 当作 `(↑0)⁻¹ = ↑0` 的证明推入。

- [#15476](https://github.com/leanprover/lean4/pull/15476)
  使 `Sym` 算术规范化器像旧 `grind` 一样，将任意位置的数值类型转换（如 `↑(0 : Nat)`、`↑(-2 : Int)`）重写为载体中的数值。此前仅在 `+`、`*` 等内部解释转换，单独、作为函数实参或位于 `⁻¹` 下的转换会保留，使 `(↑0)⁻¹` 进入环求解器，错误应用 `Field.inv_zero` 并产生内核拒绝的证明（`backward.grind.normalizer := false` 下的 `grind_9321`）。

- [#15475](https://github.com/leanprover/lean4/pull/15475)
  使基于 `Sym.simp` 的 `grind` 规范化器将每个 `Fin` 字面量重写为规范形式。此前 `@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat` 等值为嵌套数值、类型索引为闭项的字面量保持原样，被视为与 `(0 : Fin 2)` 不同的字面量，产生被内核拒绝的证明（`grind_canon_ofnat`）。

- [#15473](https://github.com/leanprover/lean4/pull/15473)
  在基于 `Sym.simp` 的 `grind` 规范化器中，`Sym.simp` 后增加 `Sym.dsimp`，归约应用固定实参中的 β-红式和结构体实例投影，与旧规范化器的 `Simp.Config.dsimp` 一致。`Sym.simp` 不访问这些实参，态射复合隐式对象中残留的红式使 `grind_cat.lean` 中 `Functor.flip` 的目标无法匹配 `NatTrans.naturality`。

- [#15467](https://github.com/leanprover/lean4/pull/15467)
  使 `Sym` 的投影归约（`Sym.simp`、`Sym.dsimp`、规范化器使用的 `Sym.reduceProjApp?`）像 `simp` 一样，以 `.reducible` 而非环境透明度暴露结构体实参。基于 `Sym.simp` 的 `grind` 在设置属性时以 `.default` 透明度规范化 E-匹配模式，曾将 `(asIso f).hom` 展开并折叠为变量，导致以 `invalid pattern` 拒绝定理。

- [#15466](https://github.com/leanprover/lean4/pull/15466)
  修复 `grind` 同余表条目失效的两条路径，它们曾使 `grind.debug` 在含 `match` 条件的目标上不确定地失败；同时为该表添加确定性不变量检查。

- [#15465](https://github.com/leanprover/lean4/pull/15465)
  使基于 `Sym.simp` 的 `grind` 规范化器遵守 `match` 方程标注：`Grind.simpMatchDiscrsOnly` 只简化判别式，`Grind.PreMatchCond` 保持条件原样。`f.eq_def` 等匹配方程的 E-匹配实例现在能在 `backward.grind.normalizer := false` 下工作，此前会失败或生成内核拒绝的证明。

- [#15464](https://github.com/leanprover/lean4/pull/15464)
  添加默认 `true` 的 `backward.grind.normalizer` 选项，选择旧的基于 `simp` 的规范化器；设为 `false` 时，`grind` 使用由 `grind_norm` 开发的 `Sym.simp` 规范化器，处理假设、目标、E-匹配实例、广义模式及设置属性时的 E-匹配模式。默认行为不变。

- [#15463](https://github.com/leanprover/lean4/pull/15463)
  扩展 `Sym.Simp.evalGround`，求值 `Int.toNat`、`Int.natAbs` 及 `UInt8`、`UInt16`、`UInt32`、`UInt64` 字面量的 `toNat`，如 `(-7 : Int).natAbs` 变为 `7`。由于 `[grind hom]` 重写器使用 `evalGround`，`grind` 也受益。

- [#15461](https://github.com/leanprover/lean4/pull/15461)
  将 `bv_decide` 所需的实现化常量设为私有，避免导入多个
  实现化了这些常量的模块时名称冲突。

- [#15460](https://github.com/leanprover/lean4/pull/15460)
  扩展 `Sym.Simp.evalGround`，求值字面量上的 `String.push` 和 `String.singleton`，如 `"abc".push 'd'` 变为 `"abcd"`。`[grind hom]` 重写器使用此函数，因此 `grind` 也受益。

- [#15458](https://github.com/leanprover/lean4/pull/15458)
  使基于 `Sym.simp` 的 `grind` 规范化器产生 `grind` 所保留的 `OfNat.ofNat` 形式位向量字面量，而非 `BitVec.ofNat`。`3#8 + 5#8`、`3 &&& 5`、`(3#8).zeroExtend 16`、`300#8` 等闭项现在求值为与旧规范化器相同的字面量。

- [#15448](https://github.com/leanprover/lean4/pull/15448)
  修复 `grind` 在同时提及 `Char.ofNat 97` 和 `'a'` 的目标上的内核错误，并在实参等于字面量时求值 `Char.toNat`、`Char.val`、`Char.ofNat`，例如 `y = 'a' → y.toNat = 97` 和 `n = 97 → Char.ofNat n = 'a'`。

- [#15445](https://github.com/leanprover/lean4/pull/15445)
  使 `grind` 可通过 `val` 解释证明 `Fin.log2` 及作用域内 `Nat`、`Int` 到 `Fin n` 转换的目标，例如 `(x.log2).val = Nat.log2 x.val`、`((i : Int) : Fin n).val = (i % n).toNat`、`((k : Nat) : Fin n).val = k % n`。

- [#15434](https://github.com/leanprover/lean4/pull/15434)
  使 `Sym.Arith` 规范化器在 `grind` 使用的模式中，求解 `Fin n`、`UInt8`、`BitVec w` 等非零特征交换环的方程。若系数 `k` 模特征可逆，`k * m + k' = 0` 或 `k * m₁ = k * m₂` 会对单项式求解：`Fin 5` 中 `4 * x + 2 = 0` 变为 `x = 2`，正如 `Int` 中 `2 * x = 6` 已可变为 `x = 3`。

- [#15433](https://github.com/leanprover/lean4/pull/15433)
  扩展 `Sym.Simp.evalGround` 求值字面量上的 `Fin` 函数：`succ`、`castSucc`、`rev`、`last`、`val`、`pred`、`castAdd`、`addNat`、`natAdd`、`castLT`、`castLE`、`subNat`、`mk`、`ofNat`。同时规范化 `Fin` 字面量：`(7 : Fin 5)` 变为 `2`，并求值 `(4 : Fin (5 + 1))` 中非数值形式的类型索引。`Fin` 算术和比较此前已支持。

- [#15398](https://github.com/leanprover/lean4/pull/15398)
  为 bv_decide 引入 CEGAR/按需引理过程，即使不与 `grind` 模式交互也能支持未解释函数。为此将求解流程重构为完全增量式，并使用增量 SAT 求解。通过 `bv_decide +uf` 启用同余功能，目前仅限：
  1. 返回 Bool/BitVec 的函数；
  2. 仅对非依赖 Bool/BitVec 实参进行同余推理，详见 bv_uf 测试示例。

- [#15420](https://github.com/leanprover/lean4/pull/15420)
  修复 #15378 引入的 `grind` 回归：`Imp a b` 通过 `[grind norm]` 规则展开为 `a → b` 时，`Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4)` 不再可证，但显式 `→` 形式仍可证。现在先规范化目标再取反，且规范化器不再将 `(∀ x, p x) → q` 重写为 `(∃ x, ¬p x) ∨ q`。

- [#15419](https://github.com/leanprover/lean4/pull/15419)
  扩展 `Sym.Simp.evalGround` 求值字符字面量的 `Char.val`，如 `'a'.val` 变为 `97`，补充 #15411 添加的其他 `Char` 操作。

- [#15417](https://github.com/leanprover/lean4/pull/15417)
  修复同态重写器转换假设提及 `let` 绑定字面量的等式时，`grind` 报 `Application type mismatch` 的问题，例如 `let m : BitVec 2 := 1#2` 下的 `b = m.cpop`。关闭 #15388。

- [#15411](https://github.com/leanprover/lean4/pull/15411)
  扩展 `Sym.Simp.evalGround` 求值字符字面量上的 `Char` 操作：`toNat`、`toLower`、`toUpper`、`toString`、`isWhitespace`、`isUpper`、`isLower`、`isAlpha`、`isDigit`、`isAlphanum`、`==`、`!=`。当 `n` 为数值时也将 `Char.ofNat n` 转为字符字面量，使字符只有一种表示。

- [#15409](https://github.com/leanprover/lean4/pull/15409)
  添加不会阻塞简化器的 `simpControl` 变体 `Sym.Simp.reduceControl`：简化 `ite`/`dite`/`cond` 条件和 `match` 判别式，确定后归约该项，否则允许简化器访问分支。基于 `Sym.simp` 的 `grind` 规范化器用它代替 `reduceMatcher`。

- [#15405](https://github.com/leanprover/lean4/pull/15405)
  修复 `Sym.simp` 的 `arith` simproc 在 `a + f (b + 0)` 等项上的共享违规；启用 `sym.debug` 时会在 `assertShared` 中 panic。

- [#15322](https://github.com/leanprover/lean4/pull/15322)
  使 `Sym.intros` 像精译器一样，将名称以 `__` 开头的绑定作为实现细节局部变量引入。`vcgen` 通过 `Sym.intros` 引入 `do` 块的汇合点 `__do_jp`，因此验证条件局部上下文中不再显示汇合点及其主体。

- [#15389](https://github.com/leanprover/lean4/pull/15389)
  修复 `Sym.dsimp` 深入 `fun`、`∀`、`let` 绑定且绑定变量出现在主体或后续绑定类型时的共享违规；启用 `sym.debug` 时原先在 `assertShared` 中 panic。

- [#15383](https://github.com/leanprover/lean4/pull/15383)
  为 `[grind hom]` 添加 `fallback` 修饰符，仅在无其他同态规则匹配时应用回退规则，使用 `Sym.simp` 已有的 `eq_def` 展开第二层机制。

- [#15378](https://github.com/leanprover/lean4/pull/15378)
  修复 `grind` 规范化器的 `pushNot` simproc，将 `¬(p → q)` 变为 `p ∧ ¬q`，将 `¬∀ x, p x` 变为 `∃ x, ¬p x`。自 #9271 起，这些重写一直是死代码：simproc 将 `forallE` 分支与整个 `¬p` 而非 `p` 匹配，并用对命题变量返回 false 的语法检查 `Expr.isProp` 检查定义域。基于 `Sym.simp` 的规范化器中的相同 `isProp` 检查也已修复。

- [#15377](https://github.com/leanprover/lean4/pull/15377)
  从已是 `[grind hom]` 规则的引理上移除 `grind =` 属性，使 `grind` 仅通过同态重写器推导一次项的 `toNat`、`toInt`、`val` 像，而非两次。

- [#15370](https://github.com/leanprover/lean4/pull/15370)
  使 `grind` 能证明涉及返回 `Bool` 的有符号比较 `BitVec.slt`、`BitVec.sle` 的目标，如 `Int64` 的 `(x < y) ↔ (x.toBitVec.slt y.toBitVec = true)`，以及 `x.slt y = true ↔ x.toInt < y.toInt`、`x.slt y → y.sle z → x.slt z`、`x.slt y = !(y.sle x)`。

- [#15369](https://github.com/leanprover/lean4/pull/15369)
  使 `grind` 能证明按位取反的有符号值性质，如 `BitVec 16` 的 `(~~~x).toInt = (~~~x.toInt).bmod (2 ^ 16)`、固定位宽有符号整数的对应目标，以及 `~~~a = -a - 1` 等普通 `Int` 事实。

- [#15367](https://github.com/leanprover/lean4/pull/15367)
  使 `grind` 能证明位向量按变量位数左移后的有符号值性质，如 `(x <<< n).toInt = (x.toInt <<< n).bmod (2 ^ 16)`；也允许组合嵌套有符号结果，如 `((x <<< m) <<< n).toInt = (x.toInt * 2 ^ m * 2 ^ n).bmod (2 ^ 16)`、`((x + y) <<< n).toInt = ((x.toInt + y.toInt) * 2 ^ n).bmod (2 ^ 16)`、`((x * y) * z).toInt = (x.toInt * y.toInt * z.toInt).bmod (2 ^ 16)`。

- [#15366](https://github.com/leanprover/lean4/pull/15366)
  当 `f` 是定义或条件定理时，使 `sym =>` 中的 `simp [f]`、`dsimp [f]` 表现得像默认简化器。条件定理（如模式重叠定义的方程定理）的旁条件现在用 `grind` 解决；无适用方程定理时展开非递归定义。`dsimp` 接受定义和 `rfl` 定理；可约定义被忽略并警告，而非失败。

- [#15363](https://github.com/leanprover/lean4/pull/15363)
  修复 `grind` 在包含 `-0 : Int` 的目标（如 `f (-((0 : Nat) : Int)) = f 0`）上生成内核拒绝证明的问题；现在将 `-0` 规范化为 `0`。

- [#15365](https://github.com/leanprover/lean4/pull/15365)
  使 `grind` 关联算术移位的无符号值与操作数的有符号值，现能证明 `BitVec 16` 上 `((x.sshiftRight n).toNat : Int) = (x.toInt / 2 ^ n) % 2 ^ 16` 等目标。

- [#15364](https://github.com/leanprover/lean4/pull/15364)
  使 `grind` 通过 `[grind hom]` 到 `Nat` 的注入推理位向量旋转，现能证明 `BitVec 16` 上 `(x.rotateLeft n).toNat = (x.toNat * 2 ^ (n % 16) + x.toNat / 2 ^ (16 - n % 16)) % 2 ^ 16` 及对应 `rotateRight` 目标。

- [#15362](https://github.com/leanprover/lean4/pull/15362)
  修复 `Sym.DSimp.zetaDelta`、`Sym.DSimp.zetaDeltaAll`，使其展开出现在应用头部的 let 绑定变量。此前当 `foo := fun x y => x + y` 为局部定义时，`grind`/`sym` 的 `dsimp [foo]`、`dsimp [*]` 及 `bv_decide` 规范化都不处理 `foo a b`，而 `Meta.DSimp` 会归约为 `a + b`。

- [#15350](https://github.com/leanprover/lean4/pull/15350)
  使 `grind` 通过 `[grind hom]` 注入推理位向量幂，现能证明 `BitVec 16` 上 `(x.pow z).toNat = x.toNat ^ z % 2 ^ 16`、`(x.pow z).toInt = (x.toInt ^ z).bmod (2 ^ 16)` 等目标。

- [#15348](https://github.com/leanprover/lean4/pull/15348)
  使 `grind` 通过 `[grind hom]` 到 `Nat` 的注入推理位向量拼接，如证明 `BitVec 8` 上 `(x ++ y).toNat = x.toNat * 2 ^ 8 + y.toNat`。同时修复左侧类型索引含 `Nat` 算术的 `Sym.simp` 规则，例如 `(x ++ y).toNat` 位宽 `m + n`，此前无法在位宽已规范化为数值时触发。

- [#15347](https://github.com/leanprover/lean4/pull/15347)
  允许 `grind` 的 `cutsat` 求解器在一次证明搜索中多次重排变量。首次模型搜索后由后续 E-匹配等创建的变量原先追加在末尾；若其界约束系数很大，Cooper 消元的情形拆分会枚举该系数并耗尽 `liaSteps`。例如 `BitVec 16` 的 `(x <<< 1).toInt = (x.toInt <<< 1).bmod (2 ^ 16)` 曾失败，因为 `BitVec.toInt_eq_toNat_bmod` 实例引入的商 `x.toNat / 2 ^ 16` 位于顺序末尾、系数为 `2 ^ 16`。现在可证明这些目标。

- [#15345](https://github.com/leanprover/lean4/pull/15345)
  为 `grind` 添加常量掩码 `&&&` 支持，掩码形如 `1…10…0`（一串 1 后接一串 0），适用于 `Nat`，并通过 `[grind hom]` 适用于 `BitVec` 及固定位宽整数。掩码重写为 `cutsat` 支持的字面量 `%`、`/`、`*`：`x &&& (2^n - 1)` 为 `x % 2^n`，`x &&& ((2^n - 1) * 2^k)` 为 `x / 2^k % 2^n * 2^k`。现可证明 `BitVec 8` 的 `(x &&& 0xe0).toNat = x.toNat / 32 % 8 * 32` 及 `UInt8` 的 `x &&& 0xC0 = 0 → x &&& 0x40 = 0`。尚不处理有空洞的掩码（如 `0b101`）或 `Int`。

- [#15344](https://github.com/leanprover/lean4/pull/15344)
  使 `Sym.Arith.normalize?`（从而 `Sym.simp` 的 `arith` simproc）在任意域上，当旁条件证明器证明 `x ≠ 0` 时消去原子 `x` 的 `x * x⁻¹`。`a * b / a` 变为 `b`，`a ^ 3 / a` 变为 `a ^ 2`，`a / (2 * a)` 变为 `2⁻¹`。simproc DSL 接受 `arith with d`，因此 `arith with grind` 使用目标假设；请求过旁条件的结果依赖上下文。

- [#15343](https://github.com/leanprover/lean4/pull/15343)
  在特征零的域中，使 `Sym.Arith.normalize?`（及 `Sym.simp` 的 `arith`）将数值的逆作为有理系数。`a / 2 + a / 2` 规范化为 `a`，`a / 2 + b / 3` 为 `(3 * a + 2 * b) * 6⁻¹`；关系消去分母，如 `a / 2 + b / 3 = 1` 变为 `3 * a + 2 * b = 6`。没有 `IsCharP _ 0` 实例时，数值的逆仍为原子。

- [#15259](https://github.com/leanprover/lean4/pull/15259)
  将 `BitVec.toNat_ofInt` 注册为 `[grind hom]` 规则，使 `grind` 能推理 `BitVec.ofInt` 的无符号值，尤其使 `cutsat` 可跟踪经 `BitVec.ofInt` 计算的进位。

- [#15262](https://github.com/leanprover/lean4/pull/15262)
  将 `BitVec.toInt_signExtend` 注册为 `[grind hom]` 规则，使 `grind` 能推理 `BitVec.signExtend` 的有符号值：缩窄时将 `toInt` 模 `2 ^ v`，扩宽时保持不变。

- [#15311](https://github.com/leanprover/lean4/pull/15311)
  修复 `grind` 从不激活闭模式含 lambda、依赖 `∀` 或 `Char`、负 `Int` 等非参数字面量的 E-匹配定理。例如即使目标含 `myPred mySet` 与 `mySet = fun _ => True`，也不用 `@[grind .] theorem myPred_of_true : myPred (fun _ => True)`；`@[grind =] theorem fc_a : fc 'a' = 1` 也无法证明 `fc 'a' = 1`。显式 `grind [myPred_of_true]` 原本可行，因为参数会绕过符号索引。

- [#15310](https://github.com/leanprover/lean4/pull/15310)
  修复绑定类型依赖先前绑定时（如 `∀ k : Nat, k < 32 → ...`），`Sym.dsimp` 产生悬空自由变量，导致 `bv_decide` 报 `unknown free variable`。关闭 #15195。

- [#15046](https://github.com/leanprover/lean4/pull/15046)
  修复 `Lean.Meta.Sym.Simp.toHave` 将 `have` 的依赖按正序传给要求逆序的 `Expr.betaRev` 的问题。若 `have` 的值依赖同一参数列中至少两个先前 `have`，重建时会交换依赖，生成类型不正确的证明项，被内核以应用类型不匹配拒绝。

- [#14827](https://github.com/leanprover/lean4/pull/14827)
  使 `vcgen` 对更多异常后置条件类型逐点陈述验证条件，并使 `throws` 子句适用于自定义类型。对 `Except ε`，异常后置条件 `fun e => e = "x"` 现在产生 `∀ e, e = "x" → …`，而非函数间蕴涵。`structure Thrown where onThrow : String → Prop` 等自定义类型通过将其转换为异常后置条件栈的 `ToEStack` 实例，也能获得相同逐点条件；加上 `EPostSlot` 实例后还支持 `def` 契约的 `throws` 子句。

- [#15290](https://github.com/leanprover/lean4/pull/15290)
  将 `vcgen` 语法移到新模块 `Std.WP.Tactic`，并弃用 `Std.Do` 证明模式策略。`import Std.WP` 现在提供 `vcgen`；`mintro`、`mspec` 等证明模式策略每次调用报告一条指向 `vcgen` 的弃用警告。无实际效果的选项 `mvcgen.warning` 也弃用。

- [#15298](https://github.com/leanprover/lean4/pull/15298)
  为 `Sym.Arith.normalize?`（及 `Sym.simp` 的 `arith`）添加不需要旁条件的域重写。在 `Field` 中，`a / b` 变为 `a * b⁻¹`，先规范化逆号下的项，再将逆推到原子：`(a * b)⁻¹ ↦ a⁻¹ * b⁻¹`、`(-a)⁻¹ ↦ -a⁻¹`、`a⁻¹⁻¹ ↦ a`、`0⁻¹ ↦ 0`、`1⁻¹ ↦ 1`。原子或数值 `x` 的 `x⁻¹` 随后成为多项式原子，因此 `a / b + a / b` 变为 `2 * (a * b⁻¹)`。

- [#15297](https://github.com/leanprover/lean4/pull/15297)
  将 `Sym.Arith.normalize?`（及 `Sym.simp` 的 `arith`）扩展到非交换 `Ring`、`Semiring`。单项式保留因子顺序，因此 `a * b` 与 `b * a` 不同，`(a + b)^2` 规范化为 `a^2 + a*b + b*a + b^2`。项、关系及特征的支持与交换情形相同。

- [#15296](https://github.com/leanprover/lean4/pull/15296)
  修复 `Sym.simp` 的 `arith` simproc，使原子间自反关系得以关闭：`x ≤ x`、`x = x` 现在规范化为 `0 ≤ 0`、`0 = 0` 并由 `post` 关闭，与此前 `x + 0 ≤ x` 一致。

- [#15295](https://github.com/leanprover/lean4/pull/15295)
  使 `Sym.Arith` 关系规范化器（及 `Sym.simp` 的 `arith`）使用环特征，因此 `UInt8` 上 `256 * u + v = v` 规范化为 `0 = 0`，`u + 2 = v` 被识别为已规范。此前仅对项按特征取模。

- [#15293](https://github.com/leanprover/lean4/pull/15293)
  将 `Sym.Arith.normalize?`（及 `Sym.simp` 的 `arith`）扩展到 `CommRing`、`CommSemiring` 上的 `lhs = rhs`、`lhs ≤ rhs`、`lhs < rhs`。先全部移到一侧再按符号拆分，使 `x + y = z + 2 * x` 变为 `y = x + z`，`a ≤ b + a` 变为 `0 ≤ b`；两侧归为同一多项式时关闭目标。

- [#15292](https://github.com/leanprover/lean4/pull/15292)
  为 `Sym.simp` 添加 `arith` simproc，使用 `Sym.Arith.normalize?` 将环、半环项规范化为多项式范式。通过 `register_sym_simp` 选择启用，适合作为 `pre` simproc：先看到最大算术子树，用完整简化器简化其原子，再反射为语法一次。范式标为最终结果（`done := true`）并缓存。

- [#15280](https://github.com/leanprover/lean4/pull/15280)
  使 `Expr.toPolyS`、`Expr.toPolyS_nc` 像 `Expr.toPoly` 一样处理零指数，半环中 `x ^ 0` 规范化为 `1` 而非指数为 0 的单项式。`Sym.Arith` 现在将 `x ^ 0 : Nat` 重写为 `1`。

- [#15279](https://github.com/leanprover/lean4/pull/15279)
  新增 `Sym.Arith.normalize?`，通过反射式证明将 `CommRing`、`CommSemiring` 的项重写为多项式范式。它将供 `Sym.simp` 算术使用；本 PR 提供 `SymM` 层 API 与测试，尚未集成简化器。

- [#15267](https://github.com/leanprover/lean4/pull/15267)
  修复 bv_decide 在投影与匹配归约方面的回归。

- [#15263](https://github.com/leanprover/lean4/pull/15263)
  将序结构分类（`LE`、`IsPreorder`、`LT`、`LawfulOrderLT`、`IsPartialOrder`、`IsLinearPreorder`、`OrderedRing`）从 `grind` 序模块移到 `Sym.Arith`，供其他 `Sym` 组件复用。没有用户可见变化。

- [#15190](https://github.com/leanprover/lean4/pull/15190)
  使 `grind` 环求解器使用 `Sym.Arith` 的环分类、运算缓存、反射和解释，删除 `Grind/Arith/CommRing` 下的重复实现。现在每次 `SymM` 运行只分类一次类型，而非每个目标一次，因此同次 `grind` 的各目标及 `sym` 块的各策略共享结果。通过程序驱动 `grind` 的代码会看到新布局：逐目标环状态仅保存求解数据，`Result` 携带 `Sym.Arith` 环记录，`goalToMessageData`、`evalCheck` 接收这些记录。

```

# 编译器
%%%
file := "Compiler"
tag := "Manual-Releases-v4_36_0-Compiler"
%%%

```markdown

- [#15516](https://github.com/leanprover/lean4/pull/15516)
  移除每个构造器（因此也包括每个结构体）最多 255 个对象字段的限制。

- [#15539](https://github.com/leanprover/lean4/pull/15539)
  将一些全局对象标为持久，修复仅发生在 IR
  解释器调试代码中的引用计数竞争；同时为加固，将另一个目前未多线程使用、
  但未来可能这样使用的全局对象
  也标为持久。

- [#15520](https://github.com/leanprover/lean4/pull/15520)
  使符号缓存返回引用，而不复制缓存内容；同时不在可能递归调用解释器后使用这些引用。当前基于桶的 `std::unordered_map` 虽无需如此，但未来 `flat_map` 可能因重哈希使引用失效，故提前避免。

- [#15131](https://github.com/leanprover/lean4/pull/15131)
  为高元数闭包应用添加快速路径。此前向底层函数指针传参时总保留实参所有权，导致非线性。现在像低元数闭包一样，若闭包被线性传递，则使用线性传参快速路径。此外，闭包现在*可能*进行尾调用；具体行为仍依赖平台和编译器，不应依赖。

- [#15493](https://github.com/leanprover/lean4/pull/15493)
  使 IR 解释器在函数入口正确调整栈帧，而非变量访问时动态调整，确保变量访问无分支。

- [#15486](https://github.com/leanprover/lean4/pull/15486)
  预先计算 IR 声明的部分信息，供未来工作使用。

- [#15407](https://github.com/leanprover/lean4/pull/15407)
  使 `ctorIdx` 在几乎所有情况下仅读取构造器标签，显著例外包括：
  - 只有一个构造器的类型若为平凡类型，可能被展开为其他类型，因此静态返回 `1`；
  - `Nat`、`Int` 等内置类型。

- [#15277](https://github.com/leanprover/lean4/pull/15277)
  放宽同一运算 `UInt32` 与 `UInt64` 结果必须相等的约束，使 `USize` 常量折叠更智能。此前要求两个输出完全相同；但为使 `USize` 字面量在两种平台位宽上含义一致，只需 `UInt64` 输出截为 `UInt32` 后与 `UInt32` 输出相同。

- [#15276](https://github.com/leanprover/lean4/pull/15276)
  修改 LCNF simp 中“等价情形”折叠器的启发式。此前对 `cases` 每对分支
  都做 α-等价比较，导致每个 cases
  有 O(n^2) 次查询。新方法受 GHC 启发，改为选择
  以下之一：
  - 默认分支；
  - 首个全部参数都未使用的分支。

- [#15275](https://github.com/leanprover/lean4/pull/15275)
  更系统地引入常量折叠器，尝试覆盖 `Nat`、`UInt` 及其他类型少量特例中所有有意义的简单关系。

- [#15256](https://github.com/leanprover/lean4/pull/15256)
  扩展派生值分析，允许编译器将任意形式的可能相关分配用作派生值的父项。

- [#15251](https://github.com/leanprover/lean4/pull/15251)
  修改 ExplicitRC 确定派生借用的方式。此前立即为整个程序计算完整派生值树，使单个变量 `s` 总以所有控制流分支中所有可能派生值为子项；每次使用都会遍历这些子项，造成大量额外工作。新过程仅在树中保留当前程序作用域中的派生值。

```

# 服务器
%%%
file := "Server"
tag := "Manual-Releases-v4_36_0-Server"
%%%

```markdown

- [#15331](https://github.com/leanprover/lean4/pull/15331)
  修复空 `grind =>`、`sym =>` 或 `impossible by` 块之后，例如关键字后或准备输入下一策略的下一缩进行，目标视图显示“no goals”而非目标状态的问题。

```

# Lake

```markdown

- [#15630](https://github.com/leanprover/lean4/pull/15630)
  为 `lake shake` 添加 `--add-downstream <MODULE>`、`--add-public-downstream <MODULE>`，确保每个不会造成导入环的被检查模块，都直接或传递导入指定模块。这为项目检查并强制某个提供检查器或代码操作的模块（如项目 `Init`）处处生效提供内置方式。

- [#15474](https://github.com/leanprover/lean4/pull/15474)
  使 Lake 以解析后的键获取由部分目标键命名的分面，让省略包名、显式包名及模块请求，与直接目标请求共享构建存储条目。

- [#15231](https://github.com/leanprover/lean4/pull/15231)
  修复模块内容尚未缓存和/或包与平台无关时，Lake 为 `-o` 无法复用缓存 `.ltar` 的问题。

- [#14906](https://github.com/leanprover/lean4/pull/14906)
  将 `leanir` 代码生成分离为独立 Lake 作业和目标。模块与库的 `leanArts` 分面弃用，分为 `elabArts` 和 `irArts`；为兼容，`leanArts` 委托到 `irArts`。

- [#12545](https://github.com/leanprover/lean4/pull/12545)
  添加 `lake samply` 命令，使用 [samply](https://github.com/mstange/samply)
  记录 Lean 可执行文件的 CPU 性能剖析，解析地址、
  还原 Lean 编译器符号名，并将结果提供给
  [Firefox Profiler](https://profiler.firefox.com) 查看。

```

# 其他
%%%
file := "Other"
tag := "Manual-Releases-v4_36_0-Other"
%%%

```markdown

- [#15665](https://github.com/leanprover/lean4/pull/15665)
  将 Lean Beam 的 CLI、MCP 服务器、守护进程及 LSP 插件加入 Linux、macOS 发行工具链。

- [#15559](https://github.com/leanprover/lean4/pull/15559)
  不再从 `module` 导出仅在证明内部实现化的 `foo.eq_1` 等常量，使这些证明不再触发下游重建；导入模块会按需再次实现化这些常量。

- [#15558](https://github.com/leanprover/lean4/pull/15558)
  不再从 `module` 导出声明键控环境扩展中属于私有声明的条目，例如投影函数信息，使其变化不再触发下游重建。

- [#15565](https://github.com/leanprover/lean4/pull/15565)
  修复启用核心的 `compiler.postponeCompile` 时发现的 `leanir` panic 及另外三个较小问题。

- [#15512](https://github.com/leanprover/lean4/pull/15512)
  不再为导入环境扩展条目创建冗余副本，加快语言服务器之外的模块系统导入并减少内存使用；Mathlib 导入时间减少约 6%。

- [#15150](https://github.com/leanprover/lean4/pull/15150)
  确保发行版本的 `Lean.toolchain` 含 `v`，如 `"leanprover/lean4:v4.34.0-rc2"`，以符合 `lean-toolchain` 文件标准格式，也使 `ToolchainVer.ofString` 可成功解析 `Lean.toolchain`。

```

# 未分类
%%%
file := "Uncategorised"
tag := "Lean-__________________--____________--Lean-4___36___0-rc2-_LPAR_2026-10-27_RPAR_--Uncategorised"
%%%

```markdown

- [#15002](https://github.com/leanprover/lean4/pull/15002)
  为 `Lean.Data.Html.Syntax` 添加类似 HTML 的语法及将其精译到 `Lean.Data.Html` 的精译器。

- [#14935](https://github.com/leanprover/lean4/pull/14935)
  新增表示 HTML 森林的 `Lean.Data.Html` 类型，主要面向 HTML 编写（而非网络服务器内部表示等），并提供产生 `String` 的渲染器。

```
