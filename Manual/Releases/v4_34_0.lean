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

#doc (Manual) "精益4.34.0-rc1 (2026-08-10)" =>
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
  让 `def` 合约的 `ensures` 子句像 `fun` 一样编写，因此可以根据结果的形状来声明后置条件：`ensures __FIX000__ none => False __FIX001__ some v => 2 * v ≤ n`。现在，合同条款在打印精美时也以自己的行开始，就像在源代码中编写的那样。

- [#14686](https://github.com/leanprover/lean4/pull/14686)
  使 `requires`、`ensures` 和 `invariant` 子句接受其绑定器上的类型归属，就像 `fun` 所做的那样： `requires s : Nat => s = 0` 现在详细说明为绑定器形式，而不是被视为术语。覆盖 `invariant` 子句的所有绑定程序的归属将被报告为错误，因为它的前两个绑定程序是循环使用的前缀和剩余后缀。

- [#14682](https://github.com/leanprover/lean4/pull/14682)
让解构其绑定器的 `for` 循环携带 `invariant` 子句，因此映射上的循环可以绑定 `(k, v)` 并仍然声明其不变量。该子句无法验证的容器会在该子句出现的位置报告，并命名它缺少的 `PureForIn` 实例，而不是稍后作为没有适用规范的 `vcgen` 小工具显示。

- [#14596](https://github.com/leanprover/lean4/pull/14596)
  使 `vcgen` 的循环不变量可用于其迭代产生其元素而不产生任何影响的每个容器。哈希映射、树映射、它们的集合、多态范围、切片和迭代器现在支持 `for … invariant`，包括元素类型为全域多态的容器，以前根本没有循环规范。通过声明其循环无效果来支持新容器，而不是为其添加循环规范。

- [#14604](https://github.com/leanprover/lean4/pull/14604)
  添加 `cbv at` 功能以在局部假设上运行 `cbv` ，但现在对于 `SymM` 不变量来说是安全的，即每个 `cbv` 调用（对局部假设）包含在单个 `SymM` 上下文中，该上下文仍然是增量的

- [#14602](https://github.com/leanprover/lean4/pull/14602)
  将 `assert` 元素添加到 `do` 符号中以进行内在验证。 `assert P` 表明 `P` 在程序中的该点成立； `assert s => P s` 使用 `fun` 接受的相同绑定器来绑定断言本身的参数，例如状态单子的状态。 `vcgen` 从程序中读取断言并证明它作为验证条件；在运行时该元素不执行任何操作。

- [#14603](https://github.com/leanprover/lean4/pull/14603)
  让 `requires` 和 `invariant` 子句绑定断言本身的参数，因此断言是函数的 monad 不再需要显式 `fun`。对于状态 monad，状态可以直接命名：

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
  将 `withSetOptionIn` 概括为包装函数的结果类型。之前的签名只接受 `CommandElab`，它返回 `Unit`。有状态 linter (#14357) 的阶段返回值，因此它们无法使用帮助器（例如，请参阅leanprover-community/mathlib4#42186）。所有现有的调用站点都使用 `Unit` 实例化结果类型，并且不会更改。

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
  向 linter 添加对代码操作的支持。  当启用 `Elab.async` 时，在调度 linter 任务之前，我们为信息树节点创建一个 Promise。然后，我们通过 linter 执行累积新添加的信息树，并解析 linter 任务内部的 Promise。最后，在主要任务中，我们修改信息树（包装在命令上下文中）并添加一个带有 mvar id 的新叶子，最终将填充一个承诺值。

- [#14520](https://github.com/leanprover/lean4/pull/14520)
  修复了 `instantiateMVars` 中的指数爆炸（时间和内存，通常表现为内存不足故障），其证明条款重复引用通过 `MVarId.assert`/`intro` 引入的假设 - 正如 `MVarId.note`、`replaceLocalDecl`、`simp at h` 以及每一步 LNSym 的 `sym_n` 策略所做的那样。修复#14329。

- [#14478](https://github.com/leanprover/lean4/pull/14478)
  改变了我们弃用用户注册选项的方式（通过 `register_option` 添加）。为了确保我们在使用 `set_option` 与选项交互时以及在元代码中收到警告，我们要求通过 `@[deprecated]` 属性进行弃用，并使用该属性中的信息填充内部 `deprecation?` 字段。

- [#7577](https://github.com/leanprover/lean4/pull/7577)
  概括 `conv` 和 `simp` 策略以应用 `pi_congr` 而不是 `forall_congr`。 #7507 的测试用例有现在可以工作的示例，但之前只在 Universe `v=0` 上工作。

- [#14391](https://github.com/leanprover/lean4/pull/14391)
  将 `Lean.Environment.replay` 重构为 `Lean.Kernel.Environment.replay`，以便环境在 `Kernel.Environment` 而不是 `Environment` 上重放工作，避免使用不稳定的 `Environment.ofKernelEnv`。有关更多背景信息，请参阅#13783。

- [#14357](https://github.com/leanprover/lean4/pull/14357)
  引入了有状态的 linter，它允许 linter 在命令阐述中持久保存并共享状态。

- [#14418](https://github.com/leanprover/lean4/pull/14418)
  更改 `checkUnivs` linter 的行为，以在计算不单独出现的 Universe 时采用所有声明和构造函数（如果处理归纳类型）。

- [#14437](https://github.com/leanprover/lean4/pull/14437)
  修复了 `inferInstanceAs` 标记其包装辅助定义 `@[expose]`，即使它们的主体仅在私有范围内类型良好，这使得通过 `inferInstanceAs` 为没有公开主体的类型定义的实例为公共错误类型。

- [#14386](https://github.com/leanprover/lean4/pull/14386)
  是 #14352 的后续内容（引入 `postprocess_traces`）。它提供了一个新命令 `store_traces_as myTraces in cmd`，该命令运行命令 `cmd` 并将其跟踪信息以名称 `name` 存储在内存中。可以使用 `#postprocess_traces tracePostprocessor myTraces` 转换和查看存储的轨迹。

- [#14397](https://github.com/leanprover/lean4/pull/14397)
  使 `set_option ... in` 策略支持增量细化，因此其策略块内的编辑会重用未更改的主导策略的结果，而不是重新运行整个块。

- [#14387](https://github.com/leanprover/lean4/pull/14387)
将 `logLintExt` 数据保留的级别更改为 `server`。以前，它全部保留在 `public` 级别，从而导致性能下降。

````

# 图书馆
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
  修复了使用巨大切片调用它时 `String.Pos.Raw.extract` 中释放后的使用
  限制。

- [#14623](https://github.com/leanprover/lean4/pull/14623)
  概括 `MonadTail (StateT σ m)` 实例无需 `Nonempty σ` 即可工作。这意味着即使状态类型没有 `Nonempty` 实例，现在也可以使用 `StateT` monad 证明有关 `while` 的规范。

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
  将 `Lean.Order.instCCPO_std` 范围限定为 `Std.Internal.Do` ，因此霍尔三重表示法（将异常后置条件默认为 `⊥` ）在 `open Std.Internal.Do` 之后进行详细说明，而无需 `open Lean.Order` 。

- [#12166](https://github.com/leanprover/lean4/pull/12166)
  删除 `pairwise_iff_getElem` 对 `Init.Data.List.Nat.TakeDrop` 的依赖并实现 `nodup_iff_getElem_inj`。

- [#14495](https://github.com/leanprover/lean4/pull/14495)
  根据 `Float.Model` 和 `Float32.Model` 重新定义 `IntN.toFloat` 和 `Float.ofIntN` （以及相应的 `Float32` 和 `ISize` 函数）。该模型已经存在，但由于疏忽而未被使用。

- [#13900](https://github.com/leanprover/lean4/pull/13900)
  添加了 `Replayable` 类型类，可用于检查某些 `Body` 是否可以在重定向请求中重播。

- [#14481](https://github.com/leanprover/lean4/pull/14481)
  通过以下方式改进了 `Float` / `Float.Model` / `Float32` / `Float32.Model` / `UnpackedFloat` 周围的 API：
  - 添加了声明 `Float.nan` / `Float.inf` / `Float32.nan` / `Float32.inf` 及其相应的型号 `Float.Model.nan` / `Float.Model.inf` / `Float32.Model.nan` / `Float32.Model.inf` （如果愿意的话，从电池上游）。
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
使 `String.toList` 可半简化，因为展开它会将定义相等检查器深入到其内部实现的杂草中。

````

# 战术
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Tactics"
%%%

```markdown

- [#14713](https://github.com/leanprover/lean4/pull/14713)
  adds support for `bv_decide` to make use of the `grind` state when used in `sym`/`grind` interactive mode. `bv_decide` now picks up on the (relevant) equivalence classes, encodes them into the SAT problem and then handles the problem as normally.

- [#14709](https://github.com/leanprover/lean4/pull/14709)
  ensures beta-reduction is applied when canonicalizing types in `grind`.

- [#14694](https://github.com/leanprover/lean4/pull/14694)
  ensures assigned metavariables are properly handled in the `SymM` discrimination tree module.

- [#14691](https://github.com/leanprover/lean4/pull/14691)
  ensures that the `SymM` matcher/unifier does not get confused by `Expr.mdata`.

- [#14683](https://github.com/leanprover/lean4/pull/14683)
  makes `bv_decide`'s embedded constraints pass understand both `a = true` and `(!a) = true` correctly. This allows us to solve slightly more problems in pre-processing.

- [#14681](https://github.com/leanprover/lean4/pull/14681)
  adds support for restricting the set of complex types that `bv_decide` is going to analyze as a user. By default `bv_decide` guesses that enums and structures in its context might be relevant and tries to incorporate them into the solving process. Now users can supply a restricted set of types via `bv_decide types [MyEnum, MyStruct]`. `bv_decide` is only going to work these types and disable automated discovery once this option is passed.

- [#14672](https://github.com/leanprover/lean4/pull/14672)
  makes `bv_decide` available from within `sym =>` mode.

- [#14669](https://github.com/leanprover/lean4/pull/14669)
  makes `vcgen` try the `@[spec]` theorems matching a program in priority order and apply the first one that fits the goal, so a spec whose instance argument the call site cannot synthesize no longer shadows a more specific one.

- [#14215](https://github.com/leanprover/lean4/pull/14215)
  ports `bv_decide`'s pre-processor to `SymM`. For large, rewriting heavy problems we observe a performance win of up to 6x. Furthermore, it fixes the asymptotics of embedded constraint substitution to be linear in the size of all hypotheses. There are also some breaking changes included:
  - `bv_normalize`'s proving power got slightly changed (both positively and negatively)
  - `@[bv_normalize]` is now a `Sym.simp` set which comes with some differences in terms of pattern matching power and required shape of the theorem.

- [#14664](https://github.com/leanprover/lean4/pull/14664)
  fixes a bug in `mkTheoremFromDecl` in `SymM`. It did not correctly handled polymorphic theorems that require adapters.

- [#14529](https://github.com/leanprover/lean4/pull/14529)
  reworks how a `@[frameproc]` procedure discharges its split verification condition so that frame inference scales to operators whose residual the built-in lattice split cannot decompose. A procedure for separating conjunction `∗` used to leave behind a `∗` that no split rule could discharge, halting `vcgen`; a procedure may now discharge its split VC however it wants, so separation-logic framing closes with `vcgen … with finish`.

- [#14535](https://github.com/leanprover/lean4/pull/14535)
  fixes `vcgen [f, h, …]` reporting `No spec found` for a sibling call inside a self-recursive `f` when the list both brackets `f` to unfold and supplies a spec `h` for `f`, whether `h` is named or pulled by `*`. A bracketed definition's unfoldings now rank below both a named spec and a `*` hypothesis for the same program, so at a recursive call `vcgen` applies that spec and stops rather than unfolding `f` again into a branch whose sibling call has no matching spec. The regression came from #14528, which had raised these unfoldings to the named-spec priority.

- [#14530](https://github.com/leanprover/lean4/pull/14530)
  fixes a panic in `vcgen` when an equation or unfold spec supplied via `vcgen [someDef]` is used for a program in a deep embedding, i.e. a program type with a bare `Std.Internal.Do.WP` instance rather than a monadic one.

- [#14528](https://github.com/leanprover/lean4/pull/14528)
  makes every `vcgen [f]` argument enter the spec database at the call-site priority band, so a definition to unfold or a spec supplied as a term outranks an ambient `@[spec]` on the same program.

- [#14524](https://github.com/leanprover/lean4/pull/14524)
  fixes `vcgen … with finish` on a provably unreachable `match` branch: it no longer reports success while leaving an unassigned metavariable that the kernel rejects (`declaration has metavariables`), nor fails with `finish failed` on a verification condition whose proof needs a lifted precondition.

- [#14492](https://github.com/leanprover/lean4/pull/14492)
  makes `vcgen` prefer a spec named in a `vcgen [...]` argument over one collected from an ambient local hypothesis, and prefer `foo` over a hypothesis pulled in by `*` in `vcgen [foo, *]`, so the spec you supply at a call site wins when several match.

- [#14497](https://github.com/leanprover/lean4/pull/14497)
  teaches `vcgen` to decompose a raw `∀`/`→` on the RHS of a `Prop` entailment and an `iInf` on any `Pi` assertion lattice.

- [#14490](https://github.com/leanprover/lean4/pull/14490)
  makes `vcgen` report a clean missing-spec error when the spec it selects for a program turns out not to unify with it, instead of dumping the internal backward rule and its type.

- [#14487](https://github.com/leanprover/lean4/pull/14487)
  lets `vcgen [...]` accept arbitrary term arguments, not just bare identifiers, mirroring `simp [...]`. A term that proves a Hoare-triple or `⊑ wp` specification is registered as a spec, and any other term proof is handled as a simp lemma, so forms like `vcgen [show l = r from h]`, `vcgen [foo x]`, and `vcgen [@foo]` now work.

- [#14429](https://github.com/leanprover/lean4/pull/14429)
  makes `vcgen [f]` handle a definition `f` whose body is a `match` on its arguments like `simp [f]` does. A call with an opaque discriminant now rewrites through the unfold theorem `f.eq_def` and splits the exposed `match`, instead of reporting a missing spec.

- [#14475](https://github.com/leanprover/lean4/pull/14475)
  fixes a spurious "Too many variable names provided" error from `fun_induction` (and `induction`/`cases`) when an alternative had a `let`-bound field, so that all hypotheses of such an alternative can now be named.

- [#14469](https://github.com/leanprover/lean4/pull/14469)
  makes `vcgen` work after a preceding tactic `have`, `let`, or `suffices`, which previously failed with "vcgen: could not determine the program type of the goal".

- [#14468](https://github.com/leanprover/lean4/pull/14468)
  migrates the standard library to the `[grind hom]` and `[grind hom_pred]` attribute modifiers and removes the deprecated `[grind homo]` and `[grind homo_pred]` spellings.

- [#14460](https://github.com/leanprover/lean4/pull/14460)
  adds additional `BitVec` operations to the set of operations supported by `Simp.Simp.evalGround` and `Sym.DSimp.evalGround`.

- [#14459](https://github.com/leanprover/lean4/pull/14459)
  adds an option for `Sym.dsimp` to rewrite in instances. This is usually not desirable as it can lead to non-standard instances. However, we might for example want to rewrite ground terms in instances to make more terms syntactically equal.

- [#14464](https://github.com/leanprover/lean4/pull/14464)
  renames the `[grind homo]` and `[grind homo_pred]` attribute modifiers to `[grind hom]` and `[grind hom_pred]`. The previous spellings remain as deprecated aliases with identical behavior, and will be removed once the standard library migrates to the new spellings in a follow-up PR.

- [#14457](https://github.com/leanprover/lean4/pull/14457)
  records the homomorphism source types of a `[grind homo]` theorem set: when an `=`-injection rule (a rule translating `Eq τ`) is registered, the head constant of `τ` is added to a new environment extension, and rules whose source type is not headed by a constant are rejected. The source types identify the terms the `grind` homomorphism engine must track in the E-graph. The `reset_grind_attrs%` command clears the new extension.

- [#14454](https://github.com/leanprover/lean4/pull/14454)
  annotates theorems for `BitVec`, `Fin`, and fixed (signed and unsigned) integers using then new  `[grind homo]` and `[grind homo_pred]` attributes. This PR is based on the prototype implemented by Andres Erbsen at https://github.com/AeneasVerif/kraken/pull/122

- [#14452](https://github.com/leanprover/lean4/pull/14452)
  rejects `[grind homo]` theorems that are conditional rewriting rules. Conditional theorems are rejected with an error pointing to the E-matching attributes. The `reset_grind_attrs%` command now also clears the `[grind homo]` and `[grind homo_pred]` extensions.

- [#14451](https://github.com/leanprover/lean4/pull/14451)
  adds the attribute `[grind homo_pred]`. This attribute is used for a separate mechanism which complements `[grind homo]`. It is not a rewrite set but an eager fact injector keyed by head symbol. Where `[grind homo]`` rules translate terms, `[grind homo_pred]` theorems generate new facts about terms the moment they enter the E-graph.

- [#14446](https://github.com/leanprover/lean4/pull/14446)
  adds the attribute `[grind homo]`. This is just the first step. We are going to use it to implement the approach described at
  https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#14444](https://github.com/leanprover/lean4/pull/14444)
  ensures `grind` doesn't timeout checking for definitionally equality while trying to propagate `match`-expressions conditions.

- [#14439](https://github.com/leanprover/lean4/pull/14439)
  fixes a `grind` bug where the canonicalizer could resynthesize a propositional instance (e.g. `Nonempty α`) occurring in a binder body skipped by preprocessing, producing a closed nested proof lacking the `Grind.nestedProof` wrapper. Congruence closure then treated the term as distinct from correctly wrapped occurrences of the same application, and `grind` missed valid contradictions. Closes #13655.

- [#14431](https://github.com/leanprover/lean4/pull/14431)
  fixes `vcgen` failing with `Failed to apply rule` when the same equality spec matches two different programs within one run, e.g. the equations of a recursive function registered via `vcgen [f]`: the cached backward rule was specialized to the first matched program and could not be applied to the next one.

- [#14428](https://github.com/leanprover/lean4/pull/14428)
  fixes the `grind` filter syntax. It prevented `grind =>` from being used nested in `match` expressions.

- [#14426](https://github.com/leanprover/lean4/pull/14426)
  fixes `grind` dropping E-matching theorems from custom `grind` attributes when a partially activated theorem was reinserted under the same symbol.

- [#14425](https://github.com/leanprover/lean4/pull/14425)
  implements support for using `grind` to discharge hypotheses in conditional `Sym.simp` theorems.

- [#14424](https://github.com/leanprover/lean4/pull/14424)
  fixes a maximal-sharing violation in `Sym.simp`: when a conditional rewrite discharged a hypothesis that occurs in the theorem's right-hand side., the discharger-provided proof was spliced into the resulting term without restoring maximal sharing, violating the `SymM` sharing invariant (detected by `sym.debug`). Dischargers are not required to return maximally shared proofs. This issue was reported by @hargoniX

- [#14416](https://github.com/leanprover/lean4/pull/14416)
  fixes `vcgen` and `mvcgen` failing to split `match h : e with ...` expressions, whose alternatives bind an equality `h : e = pattern`. Fixes #12275.

- [#14405](https://github.com/leanprover/lean4/pull/14405)
  improves the support for offsets in `SymM` matcher/unifier. See new test for example that could not be handled.

- [#13587](https://github.com/leanprover/lean4/pull/13587)
  fixes a kernel type mismatch raised by `lia`/`grind` when internalizing an integer expression whose syntactic structure differs from the structure of its polynomial representation. The mismatch occurred because the `eq_def` proof term bridged `x.denote ctx = e.denote ctx` to `Poly.denote' ctx p = 0` via a plain `Eq.refl e`, but `Poly.denote'` collapses sub-structure such as a trailing `+ 0` (the `(.num 0)` monomial is dropped) while `e` keeps it. The kernel then rejected the application because the equality between `x.denote` and `Poly.denote' p` did not hold definitionally.

- [#14404](https://github.com/leanprover/lean4/pull/14404)
  fixes `Sym.simp` failing to rewrite terms containing unassigned metavariables, and prevents the matcher from unsoundly unifying such metavariables when matching nonlinear patterns.

- [#14401](https://github.com/leanprover/lean4/pull/14401)
  fixes `preprocessType` in `SymM`. It must not perform `zetaDelta` by default.

```

# 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Compiler"
%%%

```markdown

- [#14717](https://github.com/leanprover/lean4/pull/14717)
  the model/runtime mismatch in `String.Pos.Raw.extract` and adds a faster variant (`lean_string_utf8_extract_fast`) for `String.extract` that assumes that the positions are valid positions.

- [#14505](https://github.com/leanprover/lean4/pull/14505)
  fixes a compiler issue where private imports of the `Lean` library could lead to segfaults by ensuring the necessary call to `lean_initialize` happens in each module's initializer when necessary. As a follow-up clean up, the call to `lean_initialize_runtime_module` is made implicit as well, meaning users of Lean as an FFI library do not need to call these functions themselves anymore.

- [#14332](https://github.com/leanprover/lean4/pull/14332)
  adds `DT_SONAME` entries to the shared libraries `libInit_shared, libleanshared*, libLake_shared` on Linux. This is analogous to `LC_ID_DYLIB` on Mac which we already set via `-install_name`. Fixes #9420.

- [#14479](https://github.com/leanprover/lean4/pull/14479)
  prevents possible corruption if two threads simultaneously call `lean_decode_io_error`. It also changes the semantics of `osCode` in `IO.Error`, such that it emulates posix `errno` rather than forwarding uv error codes cast to unsigned integers.

- [#14471](https://github.com/leanprover/lean4/pull/14471)
  fixes a sanitizer warning where `initialize` functions were passed uninitialized memory as their `world` argument, by failing to call `io_mk_world`.

- [#14463](https://github.com/leanprover/lean4/pull/14463)
  reverts #14423 until we can get the situation on Windows figured out.

- [#14423](https://github.com/leanprover/lean4/pull/14423)
  prevents possible corruption if two threads simultaneously call `lean_decode_io_error`. It also changes the semantics of `osCode` in `IO.Error`, such that it emulates posix `errno` rather than forwarding uv error codes cast to unsigned integers.

- [#14204](https://github.com/leanprover/lean4/pull/14204)
  prevents silent olean truncation when disk space is exhausted.

```

# 漂亮的打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Pretty-Printing"
%%%

```markdown

- [#14512](https://github.com/leanprover/lean4/pull/14512)
  makes a `for` do-element pretty-print with a space before `do`. The do-element `for` parser emitted `"do "` with no leading space, so reformatting a `for … do` block glued the range to the keyword (`for x in xs do` printed as `for x in xsdo`). Every sibling do-keyword (`while`, `unless`, term-level `for`) already emits ` do `; this aligns `for`.

- [#14367](https://github.com/leanprover/lean4/pull/14367)
  fixes an issue where the `@[simp ←]` attribute would pretty-print as `@[simp← ]`, along with analogous issues with `@[grind norm ←]`, `@[wf_preprocess ←]`, `@[bv_normalize ←]`, etc. See also discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Whitespace.20linter.20interaction.20with.20reverse.20simp.20attributes/near/590971428).

```

# 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Documentation"
%%%

```markdown

- [#14436](https://github.com/leanprover/lean4/pull/14436)
  removes references to the unfolding lemma from the `repeatM` docstrings and moves that lemma into the `repeatM.Internal` namespace.

```

# 湖
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Lake"
%%%

```markdown

- [#14723](https://github.com/leanprover/lean4/pull/14723)
  makes the `MACOSX_DEPLOYMENT_TARGET` configurable via the Lake API -- both across a build and for custom builds of shared libraries or executables.  It also includes the target in traces, ensuring a rebuilding if the value changes (e.g., if the environment variable `MACOSX_DEPLOYMENT_TARGET` is set).

- [#14724](https://github.com/leanprover/lean4/pull/14724)
  adds the `--package` option for `lake cache get`, which fetches outputs for a specific package in the workspace (not just the root). This is particularly useful for downloading dependency outputs from a custom service. In addition, the undocumented `--rev` support has been removed from `put` and documented for `put-staged`.

- [#14720](https://github.com/leanprover/lean4/pull/14720)
  demotes all cache-related failures during a build to `trace`-level messages. This ensures that builds run with `--wfail` or `--iofail` do not fail solely due to the cache.

- [#14622](https://github.com/leanprover/lean4/pull/14622)
  adds a `--code-quality` option to `lake lint` that emits builtin linter results as machine-readable JSON entries instead of human-readable diagnostics. Text-linter warnings are aggregated per module and linter into one entry holding the warning count, and environment-linter findings are reported per flagged declaration; both are keyed by the linter's option name. The option implies `--builtin-lint` and `--builtin-only`.

- [#14617](https://github.com/leanprover/lean4/pull/14617)
  refactors `lake lint --builtin-lint` internals so that it has a `Mode` flag (reporting vs recording exceptions) in the anticipation of the third mode of running upcoming code quality checks.

- [#14629](https://github.com/leanprover/lean4/pull/14629)
  suppresses Lake's wrapper line `error: Lean exited with code 1` when `lean` has already emitted error-level diagnostics and exited with code 1, which is the usual type-error path and was pure noise next to the real errors.

- [#14625](https://github.com/leanprover/lean4/pull/14625)
  makes Lake report the underlying file error when a `lean_lib` root module has no source file, instead of only reporting that some modules have bad imports.

- [#14651](https://github.com/leanprover/lean4/pull/14651)
  fixes a number of ways a failed artifact transfer in `lake cache get` / `lake cache put` could fail to be recorded or could lead to an early abort of the entire transfer batch. Sometimes this would leave a corrupted artifact in the local Lake cache, which could break downstream builds.

- [#14630](https://github.com/leanprover/lean4/pull/14630)
  makes `lake update <pkg>...` fail with a clear error when a specified package name is not known to the current dependency manifest. Previously, unknown or misspelled names (including case mismatches) were silently ignored, which was confusing.

```

# 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___34___0-rc1-_LPAR_2026-08-10_RPAR_--Other"
%%%

```markdown

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  adds support for compiling with thread sanitizer. This both increases memory consumption and slows lean down massively so we only run a very small subset of tests to remain in a reasonable time. Developers need to add additional tests to the set themselves.

```
