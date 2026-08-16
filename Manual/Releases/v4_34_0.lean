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

#doc (Manual) "Lean4.34.0-rc1 (2026-08-10)" =>
%%%
tag := "release-v4.34.0"
file := "v4.34.0"
%%%

:::warn
这些发行说明描述的是_候选版本_，而不是最终版本。
它们可能不完整并且可能会发生变化。
:::

此版本有 144 项更改。
除了新增的 52 项功能之外
以及下面列出的 53 个修复，
有 5 处重构更改，
5 项文档改进，
6 项性能改进，
1 对测试套件的改进，
以及其他 22 项变更。

# 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Language"
%%%

````markdown

- [#14701](https://github.com/leanprover/lean4/pull/14701)
  让 `def` 契约的 `ensures` 子句可以像 `fun` 一样分情况书写，从而按结果的形状陈述后置条件：`ensures | none => False | some v => 2 * v ≤ n`。契约子句现在也会像源码中那样，在格式化输出时另起一行。

- [#14686](https://github.com/leanprover/lean4/pull/14686)
  使 `requires`、`ensures` 和 `invariant` 子句像 `fun` 一样接受绑定器上的类型标注：`requires s : Nat => s = 0` 现在会按绑定器形式精译，而不再被视为普通项。如果一个类型标注覆盖了 `invariant` 子句的全部绑定器，则会报错，因为前两个绑定器分别表示循环已经处理的前缀和尚未处理的后缀。

- [#14682](https://github.com/leanprover/lean4/pull/14682)
  允许解构绑定器的 `for` 循环携带 `invariant` 子句，因此遍历映射时可以绑定 `(k, v)` 并同时声明不变量。如果某种容器无法用该子句验证，错误会直接在子句出现的位置报告，并指出缺少哪个 `PureForIn` 实例，而不会稍后才表现为缺少适用规范的 `vcgen` 辅助机制。

- [#14596](https://github.com/leanprover/lean4/pull/14596)
  使 `vcgen` 的循环不变量可用于其迭代产生其元素而不产生任何影响的每个容器。哈希映射、树映射、它们的集合、多态范围、切片和迭代器现在支持 `for … invariant`，包括元素类型为全域多态的容器，以前根本没有循环规范。通过声明其循环无效果来支持新容器，而不是为其添加循环规范。

- [#14604](https://github.com/leanprover/lean4/pull/14604)
  添加 `cbv at` 功能以在局部假设上运行 `cbv` ，但现在对于 `SymM` 不变量来说是安全的，即每个 `cbv` 调用（对局部假设）包含在单个 `SymM` 上下文中，该上下文仍然是增量的

- [#14602](https://github.com/leanprover/lean4/pull/14602)
  将 `assert` 元素添加到 `do` 符号中以进行内在验证。 `assert P` 表明 `P` 在程序中的该点成立； `assert s => P s` 使用 `fun` 接受的相同绑定器来绑定断言本身的参数，例如状态单子的状态。 `vcgen` 从程序中读取断言并证明它作为验证条件；在运行时该元素不执行任何操作。

- [#14603](https://github.com/leanprover/lean4/pull/14603)
  让 `requires` 和 `invariant` 子句绑定断言本身的参数，因此断言是函数的单子不再需要显式 `fun`。对于状态单子，状态可以直接命名：

  ```lean
  def sumIntoState (xs : List Nat) : StateM Nat Unit
      requires s => s = 0
      ensures _ s => s = xs.sum
    := do
    for x in xs invariant pref _ s => s = pref.sum do
      modify (· + x)
  ```

- [#14601](https://github.com/leanprover/lean4/pull/14601)
  使 `Std.Internal.Do` 的循环不变式成为迄今为止消耗的元素和剩余元素的普通函数，而不是由正在迭代的列表索引的游标。 `for … invariant` 子句绑定两个列表 `invariant pref suff => …`，验证条件直接提及它们而不是 `{ prefix := …, suffix := …, property := ⋯ }.prefix`。

- [#14589](https://github.com/leanprover/lean4/pull/14589)
  拼写 `def` 合约 `requires` 的先决条件条款，与 `ensures` 配对。

- [#14586](https://github.com/leanprover/lean4/pull/14586)
  警告未命名的 `initialize` 块上的 `public/private` 可见性修饰符 - 它们不会做任何可能令人困惑的事情。

- [#14581](https://github.com/leanprover/lean4/pull/14581)
  将 `withSetOptionIn` 概括为包装函数的结果类型。之前的签名只接受 `CommandElab`，它返回 `Unit`。有状态检查器 (#14357) 的阶段返回值，因此它们无法使用帮助器（例如，请参阅leanprover-community/mathlib4#42186）。所有现有的调用站点都使用 `Unit` 实例化结果类型，并且不会更改。

- [#14579](https://github.com/leanprover/lean4/pull/14579)
  让 `def` 合约在 `where … finally` 的 `spec` 部分解除 `vcgen` 无法自行证明的验证条件。该部分是一个普通的策略块，在 `vcgen` 保持打开的任何内容上运行，因此条件通过它们的案例名称来寻址，并且它们的绑定器命名条件所涉及的变量：

  ```lean
  def sumEvens (xs : List Nat) : Id Nat
      ensures r => ∃ k, r = 2 * k
    := do
    let mut acc := 0
    for x in xs invariant _cur => acc % 2 = 0 do
      acc := acc + 2 * x
    return acc
  where finally
    | spec =>
      case vc1 acc h => exact ⟨acc / 2, by omega⟩
  ```

- [#14567](https://github.com/leanprover/lean4/pull/14567)
  允许 `cbv` 处理依赖投影的堆栈，其组合是非依赖的。

- [#14533](https://github.com/leanprover/lean4/pull/14533)
更改不推荐使用语法警告的显示方式。在本身已弃用的定义内部，已弃用的语法警告将被静音。

- [#14564](https://github.com/leanprover/lean4/pull/14564)
  更改了对已弃用模块警告的处理。以前，弃用警告显示在与文件的第一个命令相对应的语法引用处。现在，标头被重新解析并用于提取正确的位置以显示弃用警告。

- [#14389](https://github.com/leanprover/lean4/pull/14389)
  为 `Std.Internal.Do` do-notation 添加内在验证语法：`vcgen` 自动释放的循环不变量和函数契约。

- [#14402](https://github.com/leanprover/lean4/pull/14402)
  向检查器添加对代码操作的支持。  当启用 `Elab.async` 时，在调度检查器任务之前，我们为信息树节点创建一个 Promise。然后，我们通过检查器执行累积新添加的信息树，并解析检查器任务内部的 Promise。最后，在主要任务中，我们修改信息树（包装在命令上下文中）并添加一个带有 mvar id 的新叶子，最终将填充一个承诺值。

- [#14520](https://github.com/leanprover/lean4/pull/14520)
  修复了 `instantiateMVars` 中的指数爆炸（时间和内存，通常表现为内存不足故障），其证明条款重复引用通过 `MVarId.assert`/`intro` 引入的假设 - 正如 `MVarId.note`、`replaceLocalDecl`、`simp at h` 以及每一步 LNSym 的 `sym_n` 策略所做的那样。修复#14329。

- [#14478](https://github.com/leanprover/lean4/pull/14478)
  改变了我们弃用用户注册选项的方式（通过 `register_option` 添加）。为了确保我们在使用 `set_option` 与选项交互时以及在元代码中收到警告，我们要求通过 `@[deprecated]` 属性进行弃用，并使用该属性中的信息填充内部 `deprecation?` 字段。

- [#7577](https://github.com/leanprover/lean4/pull/7577)
  概括 `conv` 和 `simp` 策略以应用 `pi_congr` 而不是 `forall_congr`。 #7507 的测试用例有现在可以工作的示例，但之前只在宇宙 `v=0` 上工作。

- [#14391](https://github.com/leanprover/lean4/pull/14391)
  将 `Lean.Environment.replay` 重构为 `Lean.Kernel.Environment.replay`，以便环境在 `Kernel.Environment` 而不是 `Environment` 上重放工作，避免使用不稳定的 `Environment.ofKernelEnv`。有关更多背景信息，请参阅#13783。

- [#14357](https://github.com/leanprover/lean4/pull/14357)
  引入了有状态的检查器，它允许检查器在命令精译中持久保存并共享状态。

- [#14418](https://github.com/leanprover/lean4/pull/14418)
  更改 `checkUnivs` 检查器的行为，以在计算不单独出现的宇宙时采用所有声明和构造函数（如果处理归纳类型）。

- [#14437](https://github.com/leanprover/lean4/pull/14437)
  修复了 `inferInstanceAs` 标记其包装辅助定义 `@[expose]`，即使它们的主体仅在私有范围内类型良好，这使得通过 `inferInstanceAs` 为没有公开主体的类型定义的实例为公共错误类型。

- [#14386](https://github.com/leanprover/lean4/pull/14386)
  是 #14352 的后续内容（引入 `postprocess_traces`）。它提供了一个新命令 `store_traces_as myTraces in cmd`，该命令运行命令 `cmd` 并将其跟踪信息以名称 `name` 存储在内存中。可以使用 `#postprocess_traces tracePostprocessor myTraces` 转换和查看存储的轨迹。

- [#14397](https://github.com/leanprover/lean4/pull/14397)
  使 `set_option ... in` 策略支持增量细化，因此其策略块内的编辑会重用未更改的主导策略的结果，而不是重新运行整个块。

- [#14387](https://github.com/leanprover/lean4/pull/14387)
将 `logLintExt` 数据保留的级别更改为 `server`。以前，它全部保留在 `public` 级别，从而导致性能下降。

````

# 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Library"
%%%

````markdown

- [#14728](https://github.com/leanprover/lean4/pull/14728)
  使 `Expr.getUsedConstants` 收集 `Expr.proj` 的 `typeName` 字段，以便我们获得直接使用的常量的完整列表。

- [#14699](https://github.com/leanprover/lean4/pull/14699)
  更改了定理 `Nat.div_lt_div_right` 的陈述，其结论是 `b / a < c / a ↔ b < c`，不需要 `a ∣ b` 作为假设。

- [#14726](https://github.com/leanprover/lean4/pull/14726)
  将 `List.dropLast_take` 的假设从 `i < l.length` 削弱到 `i ≤ l.length`。

- [#14507](https://github.com/leanprover/lean4/pull/14507)
  概括了 `vcgen` 的 `while` 循环规范的终止措施。度量可以映射到具有 `WellFoundedRelation` 实例的任何类型，并且可以读取单子状态：

  ```lean
  case inv2 => exact .ofMeasure fun i => i            -- Nat measure
  case inv2 => exact .ofMeasure fun (i, j) => (i, j)  -- lexicographic
  case inv2 => exact .ofMeasure fun _ s => n - s      -- reads the monadic state
  ```

- [#14707](https://github.com/leanprover/lean4/pull/14707)
  将缺少的 `cbv_eval` 注释添加到 `HashMap`/`HashSet` 上的 `ofList`/`ofArray`、`get!`、`getD`、`insert` 操作中。

- [#14687](https://github.com/leanprover/lean4/pull/14687)
  修复了以巨大切片边界调用 `String.Pos.Raw.extract` 时发生的释放后使用问题。

- [#14623](https://github.com/leanprover/lean4/pull/14623)
  概括 `MonadTail (StateT σ m)` 实例无需 `Nonempty σ` 即可工作。这意味着即使状态类型没有 `Nonempty` 实例，现在也可以使用 `StateT` 单子证明有关 `while` 的规范。

- [#14268](https://github.com/leanprover/lean4/pull/14268)
  添加 HTTP 服务器基准测试

- [#14541](https://github.com/leanprover/lean4/pull/14541)
  修复了 `Builder.stream` 函数可能对已知大小进行时间敏感的覆盖。

- [#14571](https://github.com/leanprover/lean4/pull/14571)
  消除 HTTP 未知大小的流测试的碎片。在某些特定场景中，它可能会失败，因为 `tryRecv?` 在发送响应头和发送 `"aaa"` 之间的时间间隔内运行。

- [#14588](https://github.com/leanprover/lean4/pull/14588)
  将 `cond_eq_ite` 转换为 `simp` 引理。

- [#14538](https://github.com/leanprover/lean4/pull/14538)
  将 `eq_false_of_ne_true` 移动到 `Bool` 命名空间，以便与所有其他 `Bool` 函数保持一致，并将 `Bool.and'` （一个 `grind` 辅助函数）移动到 `Internal.Bool.and'`。

- [#14501](https://github.com/leanprover/lean4/pull/14501)
  将 `dite` 和 `ite` 建立为 `dif` 和 `if` 语法的推荐拼写。

- [#14168](https://github.com/leanprover/lean4/pull/14168)
  让 Hoare `Triple` 在与程序的值类型无关的宇宙中使用断言类型 `Pred` ，因此规范可以对像 `σ → Prop` 这样的断言进行量化，而值保留在 `Type 0` ，而 `vcgen` 直接对此类规范进行推理。

- [#14523](https://github.com/leanprover/lean4/pull/14523)
  弃用 `letFun` 函数，该函数在一年前的 #9086 中已不再使用。

- [#14062](https://github.com/leanprover/lean4/pull/14062)
使 HTTP/1.1 客户端正确完成读取不携带正文的响应（头响应）

- [#14059](https://github.com/leanprover/lean4/pull/14059)
  添加 `closeWithError` 使正文流失败。

- [#13901](https://github.com/leanprover/lean4/pull/13901)
  添加了 `RedirectPlan` 类型，该类型使用 RFC9110 逻辑来验证重定向响应并自动重定向。

- [#14253](https://github.com/leanprover/lean4/pull/14253)
  使 `Selectable.one` 和其他相关函数处理错误并通过在 `one` 和 `combine` 上使用 `Selector` 来简化错误。

- [#14502](https://github.com/leanprover/lean4/pull/14502)
  将 `Lean.Order.instCCPO_std` 范围限定为 `Std.Internal.Do` ，因此霍尔三重表示法（将异常后置条件默认为 `⊥` ）在 `open Std.Internal.Do` 之后进行精译，而无需 `open Lean.Order` 。

- [#12166](https://github.com/leanprover/lean4/pull/12166)
  删除 `pairwise_iff_getElem` 对 `Init.Data.List.Nat.TakeDrop` 的依赖并实现 `nodup_iff_getElem_inj`。

- [#14495](https://github.com/leanprover/lean4/pull/14495)
  根据 `Float.Model` 和 `Float32.Model` 重新定义 `IntN.toFloat` 和 `Float.ofIntN` （以及相应的 `Float32` 和 `ISize` 函数）。该模型已经存在，但由于疏忽而未被使用。

- [#13900](https://github.com/leanprover/lean4/pull/13900)
  添加了 `Replayable` 类型类，可用于检查某些 `Body` 是否可以在重定向请求中重播。

- [#14481](https://github.com/leanprover/lean4/pull/14481)
  通过以下方式改进了 `Float` / `Float.Model` / `Float32` / `Float32.Model` / `UnpackedFloat` 周围的接口：
  - 添加声明 `Float.nan` / `Float.inf` / `Float32.nan` / `Float32.inf` 及其相应的模型 `Float.Model.nan` / `Float.Model.inf` / `Float32.Model.nan` / `Float32.Model.inf`（从 Batteries 上游合入）。
  - 添加了缩写`Int.toFloat`和`Int.toFloat32`，类似于现有的`Nat.toFloat`和`Nat.toFloat32`。
  - `Float.Model.Format` 现在需要 `2 ≤ exponentBits` 而不仅仅是 `0 < exponentBits`；这是 `pack` 和 `unpack` 正确运行的必要条件
  - 定义 `Float.ofNat` / `Float.ofInt` / `Float32.ofNat` / `Float32.ofInt` 现已公开。
  -  类型 `Float.Model.UnpackedFloat.Sign` 现在具有 `deriving DecidableEq` 而不仅仅是 `deriving BEq`。
  - `unpackMantissa` / `unpackExponent` / `unpackSign` 的定义现在使用 `BitVec.extractLsb'` 而不是 `BitVec.extractLsb`

- [#14462](https://github.com/leanprover/lean4/pull/14462)
  将 `Nat.div_eq` 重命名为 `Nat.div_eq_ite`，将 `Nat.mod_eq` 重命名为 `Nat.mod_eq_ite`。

- [#14458](https://github.com/leanprover/lean4/pull/14458)
  添加一些关于 `Nat.nextPowerOfTwo` 的引理。

- [#14412](https://github.com/leanprover/lean4/pull/14412)
  弃用并从 `ExceptCpsT.runK` 中删除未使用的参数 `s : ε`。

- [#14294](https://github.com/leanprover/lean4/pull/14294)
  将 `String.toList` 设为半可约，因为展开它会让定义相等性检查器深入其内部实现细节。

````

# 策略
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Tactics"
%%%

```markdown

- [#14713](https://github.com/leanprover/lean4/pull/14713)
添加了对 `bv_decide` 的支持，以便在 `sym`/`grind` 交互模式下使用时使用 `grind` 状态。 `bv_decide` 现在选取（相关）等价类，将它们编码到 SAT 问题中，然后像平常一样处理问题。

- [#14709](https://github.com/leanprover/lean4/pull/14709)
确保在规范化 `grind` 中的类型时应用 β 缩减。

- [#14694](https://github.com/leanprover/lean4/pull/14694)
确保分配的元变量在`SymM`判别树模块中得到正确处理。

- [#14691](https://github.com/leanprover/lean4/pull/14691)
确保`SymM`匹配器/统一器不会被`Expr.mdata`混淆。

- [#14683](https://github.com/leanprover/lean4/pull/14683)
使得`bv_decide`的嵌入约束能够正确理解`a = true`和`(!a) = true`。这使我们能够在预处理中解决更多的问题。

- [#14681](https://github.com/leanprover/lean4/pull/14681)
添加了对限制 `bv_decide` 将作为用户分析的复杂类型集的支持。默认情况下，`bv_decide`猜测其上下文中的枚举和结构可能是相关的，并尝试将它们合并到求解过程中。现在用户可以通过`bv_decide types [MyEnum, MyStruct]`提供一组受限的类型。 `bv_decide` 仅适用于这些类型，并在通过此选项后禁用自动发现。

- [#14672](https://github.com/leanprover/lean4/pull/14672)
使 `bv_decide` 在 `sym =>` 模式下可用。

- [#14669](https://github.com/leanprover/lean4/pull/14669)
使 `vcgen` 尝试按优先顺序匹配程序的 `@[spec]` 定理，并应用符合目标的第一个定理，因此调用站点无法合成其实例参数的规范不再隐藏更具体的定理。

- [#14215](https://github.com/leanprover/lean4/pull/14215)
将`bv_decide`的预处理器移植到`SymM`。对于大型、重写繁重的问题，我们观察到性能提升高达 6 倍。此外，它将嵌入约束替换的渐近性固定为与所有假设的大小呈线性关系。还有一些重大变化包括：
- `bv_normalize`的证明力略有改变（正面和负面）
- `@[bv_normalize]` 现在是`Sym.simp` 集合，它在模式匹配能力和所需定理形状方面存在一些差异。

- [#14664](https://github.com/leanprover/lean4/pull/14664)
修复了`SymM`中`mkTheoremFromDecl`的错误。它没有正确处理需要适配器的多态定理。

- [#14529](https://github.com/leanprover/lean4/pull/14529)
重新设计`@[frameproc]`过程如何释放其分割验证条件，以便框架推理扩展到其内置晶格分割的残差无法分解的运算符。分离合取`∗`的过程，用于留下任何分割规则都无法释放的`∗`，从而停止`vcgen`；一个过程现在可以根据需要释放其分离的 VC，因此分离逻辑框架以`vcgen … with finish` 结束。

- [#14535](https://github.com/leanprover/lean4/pull/14535)
  修复了 `vcgen [f, h, …]` 在自递归函数 `f` 的同级调用处报告 `No spec found` 的问题。当参数列表既指定展开 `f`，又为 `f` 提供规范 `h` 时，无论 `h` 是显式命名还是由 `*` 引入，都可能出现该问题。现在，方括号中定义的展开规则优先级低于同一程序的命名规范和 `*` 假设，因此遇到递归调用时，`vcgen` 会应用该规范并停止，而不会再次展开 `f`，进入同级调用没有匹配规范的分支。该回归来自 #14528；它曾将这些展开规则提升到命名规范的优先级。

- [#14530](https://github.com/leanprover/lean4/pull/14530)
  修复了将 `vcgen [someDef]` 提供的方程或展开规范用于深度嵌入程序时 `vcgen` 的崩溃；这里的深度嵌入程序是指程序类型只有裸 `Std.Internal.Do.WP` 实例、而没有单子实例。

- [#14528](https://github.com/leanprover/lean4/pull/14528)
使每个 `vcgen [f]` 参数在调用站点优先级带上进入规范数据库，因此要展开的定义或作为术语提供的规范在同一程序上优先于环境 `@[spec]`。

- [#14524](https://github.com/leanprover/lean4/pull/14524)
修复了可证明无法访问的 `match` 分支上的 `vcgen … with finish`：它不再报告成功，同时留下内核拒绝的未分配元变量 (`declaration has metavariables`)，也不再在证明需要解除前提条件的验证条件上失败并显示 `finish failed`。

- [#14492](https://github.com/leanprover/lean4/pull/14492)
使得 `vcgen` 更喜欢在 `vcgen [...]` 参数中命名的规范，而不是从环境局部假设中收集的规范，并且更喜欢 `foo` 而不是由 `vcgen [foo, *]` 中的 `*` 引入的假设，因此，当多个匹配时，您在调用站点提供的规范获胜。

- [#14497](https://github.com/leanprover/lean4/pull/14497)
教`vcgen`分解`Prop`蕴涵的右侧上的原始`∀`/`→`以及任何`Pi`断言格上的`iInf`。

- [#14490](https://github.com/leanprover/lean4/pull/14490)
当它为程序选择的规范结果与它不统一时，使 `vcgen` 报告一个干净的缺失规范错误，而不是转储内部向后规则及其类型。

- [#14487](https://github.com/leanprover/lean4/pull/14487)
让`vcgen [...]`接受任意术语参数，而不仅仅是裸标识符，镜像`simp [...]`。证明 Hoare-triple 或 `⊑ wp` 规范的术语被注册为规范，任何其他术语证明都被视为简单引理，因此像 `vcgen [show l = r from h]`、`vcgen [foo x]` 和 `vcgen [@foo]` 这样的形式现在可以使用。

- [#14429](https://github.com/leanprover/lean4/pull/14429)
使`vcgen [f]`处理定义`f`，其主体是其参数上的`match`，就像`simp [f]`一样。具有不透明判别式的调用现在通过展开定理 `f.eq_def` 进行重写，并拆分公开的 `match`，而不是报告丢失的规范。

- [#14475](https://github.com/leanprover/lean4/pull/14475)
修复了当替代方案具有 `let` 绑定字段时，来自 `fun_induction`（和 `induction`/`cases`）的虚假“提供了太多变量名称”错误，以便现在可以命名此类替代方案的所有假设。

- [#14469](https://github.com/leanprover/lean4/pull/14469)
使`vcgen`在前面的策略`have`、`let`或`suffices`之后起作用，这些策略之前因“vcgen：无法确定目标的程序类型”而失败。

- [#14468](https://github.com/leanprover/lean4/pull/14468)
将标准库迁移到 `[grind hom]` 和 `[grind hom_pred]` 属性修饰符，并删除已弃用的 `[grind homo]` 和 `[grind homo_pred]` 拼写。

- [#14460](https://github.com/leanprover/lean4/pull/14460)
将额外的 `BitVec` 操作添加到 `Simp.Simp.evalGround` 和 `Sym.DSimp.evalGround` 支持的操作集中。

- [#14459](https://github.com/leanprover/lean4/pull/14459)
添加`Sym.dsimp`在实例中重写的选项。这通常是不可取的，因为它可能导致非标准实例。然而，例如，我们可能想要重写实例中的基本术语，以使更多术语在语法上相等。

- [#14464](https://github.com/leanprover/lean4/pull/14464)
将 `[grind homo]` 和 `[grind homo_pred]` 属性修饰符重命名为 `[grind hom]` 和 `[grind hom_pred]`。以前的拼写仍然是具有相同行为的已弃用别名，一旦标准库在后续 PR 中迁移到新拼写，就会将其删除。

- [#14457](https://github.com/leanprover/lean4/pull/14457)
记录`[grind homo]`定理集的同态源类型：当注册`=`注入规则（翻译`Eq τ`的规则）时，`τ`的头常量被添加到新的环境扩展中，源类型不以常量为头的规则将被拒绝。源类型标识 `grind` 同态引擎必须在 E 图中跟踪的术语。 `reset_grind_attrs%` 命令清除新扩展名。

- [#14454](https://github.com/leanprover/lean4/pull/14454)
使用新的 `[grind homo]` 和 `[grind homo_pred]` 属性注释 `BitVec`、`Fin` 和固定（有符号和无符号）整数的定理。此 PR 基于 Andres Erbsen 在 https://github.com/AeneasVerif/kraken/pull/122 实现的原型

- [#14452](https://github.com/leanprover/lean4/pull/14452)
拒绝作为条件重写规则的`[grind homo]`定理。条件定理被拒绝，并出现指向 E 匹配属性的错误。 `reset_grind_attrs%` 命令现在还清除 `[grind homo]` 和 `[grind homo_pred]` 扩展。

- [#14451](https://github.com/leanprover/lean4/pull/14451)
  添加属性 `[grind homo_pred]`。该属性提供一套独立机制来补充 `[grind homo]`：它不是重写集，而是按头符号索引的急切事实注入器。`[grind homo]`` rules translate terms, `[grind homo_pred]` 定理会在项进入 E 图时立即生成关于它的新事实。

- [#14446](https://github.com/leanprover/lean4/pull/14446)
添加属性`[grind homo]`。这只是第一步。我们将使用它来实现描述的方法
  https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#14444](https://github.com/leanprover/lean4/pull/14444)
确保在尝试传播 `match` 表达式条件时，`grind` 不会超时检查定义相等性。

- [#14439](https://github.com/leanprover/lean4/pull/14439)
修复了一个 `grind` 错误，其中规范化器可以重新合成发生在通过预处理跳过的绑定器主体中的命题实例（例如 `Nonempty α`），从而生成缺少 `Grind.nestedProof` 包装器的封闭嵌套证明。然后，同余闭包将该术语视为与同一应用程序的正确包装出现的术语不同，并且 `grind` 错过了有效的矛盾。关闭#13655。

- [#14431](https://github.com/leanprover/lean4/pull/14431)
修复了当相同的相等规范在一次运行中匹配两个不同的程序时，例如，`vcgen`因`Failed to apply rule`而失败。通过`vcgen [f]`注册的递归函数方程：缓存的后向规则专门用于第一个匹配的程序，不能应用于下一个匹配的程序。

- [#14428](https://github.com/leanprover/lean4/pull/14428)
修复了 `grind` 过滤器语法。它阻止了 `grind =>` 嵌套在 `match` 表达式中使用。

- [#14426](https://github.com/leanprover/lean4/pull/14426)
修复了在同一符号下重新插入部分激活的定理时，`grind`从自定义`grind`属性中删除电子匹配定理的问题。

- [#14425](https://github.com/leanprover/lean4/pull/14425)
实现对使用 `grind` 提出条件 `Sym.simp` 定理中的假设的支持。

- [#14424](https://github.com/leanprover/lean4/pull/14424)
  修复了 `Sym.simp` 中违反最大共享的问题：当条件重写消解了一个出现在定理右侧的假设时，消解器提供的证明会直接拼接到结果项中，而没有恢复最大共享，从而破坏 `SymM` 的共享不变量（可由 `sym.debug` 检测）。消解器本身不必返回满足最大共享的证明。此问题由 @hargoniX 报告。

- [#14416](https://github.com/leanprover/lean4/pull/14416)
修复了 `vcgen` 和 `mvcgen` 无法拆分 `match h : e with ...` 表达式，其替代方案绑定了等式 `h : e = pattern`。修复#12275。

- [#14405](https://github.com/leanprover/lean4/pull/14405)
改进了对 `SymM` 匹配器/统一器中偏移的支持。例如，请参阅无法处理的新测试。

- [#13587](https://github.com/leanprover/lean4/pull/13587)
修复了内部化整数表达式时 `lia`/`grind` 引发的内核类型不匹配；这类表达式的语法结构与其多项式表示不同。`eq_def` 证明项原先通过普通的 `Eq.refl e`，把 `x.denote ctx = e.denote ctx` 桥接到 `Poly.denote' ctx p = 0`，但 `Poly.denote'` 会折叠尾随 `+ 0` 等子结构（删除 `(.num 0)` 单项式），而 `e` 会保留它。于是 `x.denote` 与 `Poly.denote' p` 之间的等式并非定义相等，内核会拒绝该应用。

- [#14404](https://github.com/leanprover/lean4/pull/14404)
修复了`Sym.simp`无法重写包含未分配元变量的术语，并防止匹配器在匹配非线性模式时不合理地统一此类元变量。

- [#14401](https://github.com/leanprover/lean4/pull/14401)
修复了`SymM`中的`preprocessType`。默认情况下它不能执行`zetaDelta`。

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Compiler"
%%%

```markdown

- [#14717](https://github.com/leanprover/lean4/pull/14717)
  修复 `String.Pos.Raw.extract` 的模型与运行时不一致问题，并为 `String.extract` 添加更快的变体 `lean_string_utf8_extract_fast`；该变体假定传入的位置有效。

- [#14505](https://github.com/leanprover/lean4/pull/14505)
通过确保在必要时在每个模块的初始化程序中发生对 `lean_initialize` 的必要调用，修复了编译器问题，即 `Lean` 库的私有导入可能会导致段错误。作为后续清理，对 `lean_initialize_runtime_module` 的调用也被隐式调用，这意味着 Lean 作为 FFI 库的用户不再需要自己调用这些函数。

- [#14332](https://github.com/leanprover/lean4/pull/14332)
将 `DT_SONAME` 条目添加到 Linux 上的共享库 `libInit_shared, libleanshared*, libLake_shared` 中。这类似于 Mac 上的 `LC_ID_DYLIB`，我们已经通过 `-install_name` 设置了。修复#9420。

- [#14479](https://github.com/leanprover/lean4/pull/14479)
如果两个线程同时调用`lean_decode_io_error`，则可以防止可能的损坏。它还更改了`IO.Error`中`osCode`的语义，以便它模拟posix`errno`，而不是转发转换为无符号整数的uv错误代码。

- [#14471](https://github.com/leanprover/lean4/pull/14471)
修复了一个清理程序警告，其中 `initialize` 函数因未能调用 `io_mk_world` 而被传递未初始化的内存作为其 `world` 参数。

- [#14463](https://github.com/leanprover/lean4/pull/14463)
恢复#14423，直到我们弄清楚 Windows 上的情况。

- [#14423](https://github.com/leanprover/lean4/pull/14423)
如果两个线程同时调用`lean_decode_io_error`，则可以防止可能的损坏。它还更改了`IO.Error`中`osCode`的语义，以便它模拟posix`errno`，而不是转发转换为无符号整数的uv错误代码。

- [#14204](https://github.com/leanprover/lean4/pull/14204)
防止磁盘空间耗尽时静默的 olean 截断。

```

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Pretty-Printing"
%%%

```markdown

- [#14512](https://github.com/leanprover/lean4/pull/14512)
  让 `for` do 元素在美化打印时于 `do` 前添加空格。此前 do 元素的 `for` 解析器输出没有前导空格的 `"do "`，因此重新格式化 `for … do` 块时会把范围与关键字粘在一起（`for x in xs do` 被打印成 `for x in xsdo`）。其他同类 do 关键字（`while`、`unless` 以及项级 `for`）都已输出 ` do `；此更改使 `for` 与它们一致。

- [#14367](https://github.com/leanprover/lean4/pull/14367)
修复了 `@[simp ←]` 属性将漂亮地打印为 `@[simp← ]` 的问题，以及 `@[grind norm ←]`、`@[wf_preprocess ←]`、`@[bv_normalize ←]` 等的类似问题。另请参阅 [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Whitespace.20linter.20interaction.20with.20reverse.20simp.20attributes/near/590971428) 的讨论。

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Documentation"
%%%

```markdown

- [#14436](https://github.com/leanprover/lean4/pull/14436)
从 `repeatM` 文档字符串中删除对展开引理的引用，并将该引理移至 `repeatM.Internal` 命名空间中。

```

# Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Lake"
%%%

```markdown

- [#14723](https://github.com/leanprover/lean4/pull/14723)
使 `MACOSX_DEPLOYMENT_TARGET` 可通过 Lake 接口进行配置——既可以跨构建，也可以用于共享库或可执行文件的自定义构建。  它还将目标包含在跟踪中，确保在值发生变化时进行重建（例如，如果设置了环境变量`MACOSX_DEPLOYMENT_TARGET`）。

- [#14724](https://github.com/leanprover/lean4/pull/14724)
为 `lake cache get` 添加 `--package` 选项，该选项获取工作区中特定包（而不仅仅是根）的输出。这对于从自定义服务下载依赖项输出特别有用。此外，未记录的 `--rev` 支持已从 `put` 中删除，并为 `put-staged` 记录。

- [#14720](https://github.com/leanprover/lean4/pull/14720)
将构建期间所有与缓存相关的故障降级为`trace`级别消息。这确保使用 `--wfail` 或 `--iofail` 运行的构建不会仅仅由于缓存而失败。

- [#14622](https://github.com/leanprover/lean4/pull/14622)
向 `lake lint` 添加了 `--code-quality` 选项，该选项将内置检查器结果作为机器可读的 JSON 条目而不是人类可读的诊断发出。每个模块和检查器的文本检查器警告都会聚合到一个保存警告计数的条目中，并且每个标记的声明都会报告环境检查器结果；两者都由检查器的选项名称作为键控。该选项意味着 `--builtin-lint` 和 `--builtin-only`。

- [#14617](https://github.com/leanprover/lean4/pull/14617)
重构`lake lint --builtin-lint`内部结构，使其具有`Mode`标志（报告与记录异常），以应对即将运行的代码质量检查的第三种模式。

- [#14629](https://github.com/leanprover/lean4/pull/14629)
当 `lean` 已经发出错误级别诊断并以代码 1 退出时，会抑制 Lake 的包装器行 `error: Lean exited with code 1`，这是常见的类型错误路径，并且是真实错误旁边的纯粹噪声。

- [#14625](https://github.com/leanprover/lean4/pull/14625)
使 Lake 在 `lean_lib` 根模块没有源文件时报告底层文件错误，而不是仅报告某些模块导入错误。

- [#14651](https://github.com/leanprover/lean4/pull/14651)
修复了 `lake cache get` / `lake cache put` 中失败的工件传输可能无法记录或导致整个传输批次提前中止的多种方式。有时，这会在本地 Lake 缓存中留下损坏的工件，这可能会破坏下游构建。

- [#14630](https://github.com/leanprover/lean4/pull/14630)
当当前依赖项清单未知指定的包名称时，使 `lake update <pkg>...` 失败并出现明显错误。以前，未知或拼写错误的名称（包括大小写不匹配）会被默默忽略，这令人困惑。

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Other"
%%%

```markdown

- [#14161](https://github.com/leanprover/lean4/pull/14161)
添加了对使用线程清理程序进行编译的支持。这既增加了内存消耗，又大大减慢了Lean的速度，因此我们只运行一小部分测试来保持合理的时间。开发人员需要自己向集合中添加额外的测试。

```
