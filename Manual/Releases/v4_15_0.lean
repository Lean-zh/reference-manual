/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.15.0 (2025-01-04)" =>
%%%
tag := "release-v4.15.0"
file := "v4.15.0"
%%%

````markdown

## 语言
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Language"
%%%

- [#4595](https://github.com/leanprover/lean4/pull/4595) 实现了 `Simp.Config.implicitDefEqsProofs`。当其为 `true`（默认即为 `true`）时，`simp` **不会** 为与 `rfl` 定理关联的重写规则构造证明项。用户通过给定理加上 `@[simp]` 属性来提供重写规则。如果定理的证明只是 `rfl`（自反性），并且 `implicitDefEqProofs := true`，那么 `simp` **不会** 构造一个应用该注解定理的证明项。

- [#5429](https://github.com/leanprover/lean4/pull/5429) 避免负向环境查找。

- [#5501](https://github.com/leanprover/lean4/pull/5501) 确保 `instantiateMVarsProfiling` 会添加一个跟踪节点。

- [#5856](https://github.com/leanprover/lean4/pull/5856) 为互递归 def 精化器新增一项特性：当类是 `Prop` 时，`instance` 命令会生成定理而不是定义。

- [#5907](https://github.com/leanprover/lean4/pull/5907) 去掉 `simpa?` 的 “try this” 建议中的 trailing 设置。

- [#5920](https://github.com/leanprover/lean4/pull/5920) 修改了哪些投影会成为实例的规则。此前，所有父级以及所有以子对象字段表示的间接祖先，其投影都会成为实例；现在只有直接父级的投影会成为实例。

- [#5934](https://github.com/leanprover/lean4/pull/5934) 让 `all_goals` 在失败时会 admit 目标。

- [#5942](https://github.com/leanprover/lean4/pull/5942) 在 `bv_decide` 中引入合成原子记号。

- [#5945](https://github.com/leanprover/lean4/pull/5945) 新增定义 `Message.kind`，用于返回消息的顶层标签。它会以新字段 `kind` 序列化到 `SerialMessaege` 中，以便外部消费者（例如 Lake）可以通过 `lean --json` 识别消息类型。

- [#5968](https://github.com/leanprover/lean4/pull/5968) 修复了 `arg` conv 策略在报错时错误报告参数个数的问题。

- [#5979](https://github.com/leanprover/lean4/pull/5979) 在 `bv_decide` 中加入 `BitVec.twoPow`。

- [#5991](https://github.com/leanprover/lean4/pull/5991) 简化了 `omega` 的实现。

- [#5992](https://github.com/leanprover/lean4/pull/5992) 修复 `bv_decide` normalizer 的样式问题。

- [#5999](https://github.com/leanprover/lean4/pull/5999) 为 `decide`/`decide!`/`native_decide` 新增配置选项，并将这些策略重构为同一后端的前端。新增 `+revert` 选项，可清理局部上下文并回退目标所依赖的所有局部变量，以及间接的命题性假设。它还让 `native_decide` 在失败时于精化阶段报错，同时不牺牲性能（判定过程仍只执行一次）。现在 `native_decide` 还支持宇宙多态。

- [#6010](https://github.com/leanprover/lean4/pull/6010) 将 `bv_decide` 的配置方式从大量 `set_option` 改为类似 `simp` 或 `omega` 的 elaborated 配置。值得注意的例外是 `sat.solver`，它仍然是 `set_option`，以便用户能为整个项目或文件全局配置自定义 SAT 求解器。此外，还通过新配置引入了为 simp 预处理设置 `maxSteps` 的能力。

- [#6012](https://github.com/leanprover/lean4/pull/6012) 改进了对新语法词元的校验。此前校验代码存在不一致：有些原子记号只有在带有前导空格作为漂亮打印器提示时才会被接受。另外，带内部空白的原子记号现在不再允许。

- [#6016](https://github.com/leanprover/lean4/pull/6016) 移除了 `decide!` 策略，改用 `decide +kernel`（破坏性变更）。

- [#6019](https://github.com/leanprover/lean4/pull/6019) 从 `MkBinding.mkBinding` 中移除了 `@[specilize]`，因为这个函数无法被特化（它的参数里没有函数）。结果是，本可特化的函数 `Nat.foldRevM.loop` 也不再被特化，从而导致生成的代码性能更差。

- [#6022](https://github.com/leanprover/lean4/pull/6022) 让 `change` 策略和 conv 策略使用相同的精化策略。它对目标和局部假设都一致生效。现在 `change` 可以为元变量赋值，例如：
```lean
example (x y z : Nat) : x + y = z := by
  change ?a = _
  let w := ?a
  -- now `w : Nat := x + y`
```

- [#6024](https://github.com/leanprover/lean4/pull/6024) 修复了单子提升强制转换精化器的一个问题：此前即使表达式不是单子，它也会做部分统一。这个行为可能被利用来传播有助于精化推进的信息；例如，下面第一个 `change` 之所以能工作，就是因为单子提升强制转换精化器会把 `@Eq _ _` 与 `@Eq (Nat × Nat) p` 统一起来：
```lean
example (p : Nat × Nat) : p = p := by
  change _ = ⟨_, _⟩ -- used to work (yielding `p = (p.fst, p.snd)`), now it doesn't
  change ⟨_, _⟩ = _ -- never worked
```
因此，这是一项破坏性变更；你可能需要调整表达式，显式写出额外的隐式参数。

- [#6029](https://github.com/leanprover/lean4/pull/6029) 为 `bv_normalize`（由 `bv_decide` 使用）新增一条规范化规则：在适当条件下把 `x / 2^k` 转换为 `x >>> k`。这使我们能够把用于 bitblasting 的昂贵除法电路化简为成本低得多的移位电路。具体来说，它允许进行如下规范化：

- [#6030](https://github.com/leanprover/lean4/pull/6030) 修复了 #5020 之后的 `simp only [· ∈ ·]`。

- [#6035](https://github.com/leanprover/lean4/pull/6035) 将来自 Bitwuzla 的 and-flattening 预处理过程引入 `bv_decide`。它会把形如 `(a && b) = true` 的假设拆成 `a = true` 和 `b = true`，并可与现有的嵌入式约束替换过程形成协同作用。

- [#6037](https://github.com/leanprover/lean4/pull/6037) 修复了 `bv_decide` 的嵌入式约束替换在局部上下文中存在重复定理时，无法在边界场景下生成正确反例的问题。

- [#6045](https://github.com/leanprover/lean4/pull/6045) 为部分函数添加 `LEAN_ALWAYS_INLINE`。

- [#6048](https://github.com/leanprover/lean4/pull/6048) 修复了 `simp?` 给出的建议输出缩进不合法的问题。

- [#6051](https://github.com/leanprover/lean4/pull/6051) 将 `Meta.Context.config` 标记为私有。

- [#6053](https://github.com/leanprover/lean4/pull/6053) 修复了 `whnf` 和 `isDefEq` 的缓存基础设施，确保缓存会考虑所有相关配置标志。同时也清理了 `WHNF.lean` 模块，并改进了 `whnf` 的配置。

- [#6061](https://github.com/leanprover/lean4/pull/6061) 新增一个 `simp_arith` 基准测试。

- [#6062](https://github.com/leanprover/lean4/pull/6062) 优化 `Nat.Linear.Expr.toPoly`。

- [#6064](https://github.com/leanprover/lean4/pull/6064) 优化 `Nat.Linear.Poly.norm`。

- [#6068](https://github.com/leanprover/lean4/pull/6068) 在需要处理许多变量时，改进了 `simp_arith` 的渐进性能。

- [#6077](https://github.com/leanprover/lean4/pull/6077) 为 `bv_decide` 的配置结构新增选项，使所有非强制性的预处理过程都可以被关闭。

- [#6082](https://github.com/leanprover/lean4/pull/6082) 改变了规范化器处理 `forall` 和 `lambda` 的方式，用临时 fvar 替换 bvar。它修复了 @hrmacbeth 在 [zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Quantifiers.20in.20CanonM/near/482483448) 上报告的一个问题。

- [#6093](https://github.com/leanprover/lean4/pull/6093) 在 ArgsPacker 中使用 `mkFreshUserName`。

- [#6096](https://github.com/leanprover/lean4/pull/6096) 改进了结构体上的 `#print` 命令，使其显示全部字段，以及这些字段继承自哪些父级，同时隐藏哪些父级以子对象表示等内部细节。如果有需要，这些信息仍保留在构造子中。私有常量的漂亮打印器也得到改进；它现在会像处理其他名称一样处理来自当前模块的私有名称，而来自其他模块的私有名称会被做卫生化处理。

- [#6098](https://github.com/leanprover/lean4/pull/6098) 修改 `Lean.MVarId.replaceTargetDefEq` 和 `Lean.MVarId.replaceLocalDeclDefEq`，在判断表达式是否改变时使用 `Expr.equal` 而不是 `Expr.eqv`。这样做的理由是绑定器名称和绑定器 info 对用户可见，并且会影响精化。

- [#6105](https://github.com/leanprover/lean4/pull/6105) 修复了由元变量上下文中的循环赋值导致的栈溢出。该循环是由结构体实例精化器无意引入的。

- [#6108](https://github.com/leanprover/lean4/pull/6108) 在 `apply?` 结果中关闭 `pp.mvars`。

- [#6109](https://github.com/leanprover/lean4/pull/6109) 修复了 `injection` 策略中的一个问题。该策略可能会执行多个子策略；如果其中任何一个失败，我们就必须回溯部分赋值。这个问题曾在问题 #6066 中导致报错：“`mvarId` is already assigned”。该问题仍未完全解决，因为其中示例里的匹配表达式方程生成器仍然会失败。

- [#6112](https://github.com/leanprover/lean4/pull/6112) 对 `@[deprecated]` 属性提出了更严格的要求：要么提供替换标识符，如 `@[deprecated bar]`，要么提供建议文本，如 `@[deprecated "Past its use by date"]`，并且还要求有 `since := "..."` 字段。

- [#6114](https://github.com/leanprover/lean4/pull/6114) 放宽了原子记号规则，允许 `''` 作为原子记号的前缀；在 #6012 之后，原先只对单独的 `''` 做了例外处理。该 PR 还添加了一些用于原子记号校验的单元测试。

- [#6116](https://github.com/leanprover/lean4/pull/6116) 修复了一个问题：当递归参数的索引在函数参数中出现的顺序与其类型定义中的顺序不一致时，结构递归无法正常工作。

- [#6125](https://github.com/leanprover/lean4/pull/6125) 为 `mutual` 代码块中的 `structure` 提供支持，使通过 `inductive` 和 `structure` 定义的归纳类型可以互递归。其限制为：（1）`extends` 子句中的父级必须在 `mutual` 块之前定义；（2）不允许互递归的类（这也是 `class inductive` 共有的限制）。此外，它还改进了归纳类型和结构体的宇宙层级推断。破坏性变更：结构体父级现在会在该结构体已进入作用域时精化（修复方式：使用限定名或重命名结构体以避免遮蔽），并且结构体父级不再在启用 autoimplicits 的情况下精化。

- [#6128](https://github.com/leanprover/lean4/pull/6128) 做了与 #6104 相同的修复，但不会破坏 `Plausible` 中的测试/文件。做法是：不为 `elimMVar` 创建出的元变量类型生成未使用的 let 绑定器。（这对查看元变量类型的用户也有好处，例如在错误消息中。）

- [#6129](https://github.com/leanprover/lean4/pull/6129) 修复了 `zetaDelta := false` 时 `isDefEq` 中的一个问题。可参见新增测试中的一个小例子。

- [#6131](https://github.com/leanprover/lean4/pull/6131) 修复了定义相等性测试（`isDefEq`）中的一个问题。对形如 `c.{u} =?= c.{v}` 的统一约束，它此前不会尝试展开 `c`。这个问题不影响内核。

- [#6141](https://github.com/leanprover/lean4/pull/6141) 在 snapshot 类型中利用递归结构。

- [#6145](https://github.com/leanprover/lean4/pull/6145) 修复了 `revert` 策略，使其把新的目标创建为 `syntheticOpaque` 元变量，而不是 `natural` 元变量。

- [#6146](https://github.com/leanprover/lean4/pull/6146) 修复了生成匹配表达式拆分器定理时出现的一个非终止问题。这个问题出现在拆分器定理的证明自动化反复对同一个局部声明应用 `injection` 时；由于前向依赖，该声明无法被移除。可参见问题 #6065 中的复现示例。

- [#6165](https://github.com/leanprover/lean4/pull/6165) 修改结构体实例记法与 `where` 记法，使它们对字段使用同一套记法。结构体实例记法现在允许绑定器、类型标注和方程，而 `where` 记法允许完整的结构体 lval。下面是结构体实例记法的一个例子：
```lean
structure PosFun where
  f : Nat → Nat
  pos : ∀ n, 0 < f n
```

- [#6168](https://github.com/leanprover/lean4/pull/6168) 扩展了 rewrite 策略中 “动机 is not 类型 correct” 的报错信息，解释其含义；同时还会漂亮打印出类型不正确的动机，并报告相应的类型错误。

- [#6170](https://github.com/leanprover/lean4/pull/6170) 新增核心元编程函数，用于在精化中 fork 出后台任务，并使其结果对报告系统和语言服务器可见。

- [#6175](https://github.com/leanprover/lean4/pull/6175) 修复了 `structure`/`class` 命令中的一个问题：如果某些父级不是以子对象表示，但却使用了其他父级作为实例，那么会触发内核错误。关闭 #2611。

- [#6180](https://github.com/leanprover/lean4/pull/6180) 修复了生成匹配表达式方程定理时出现的一个非终止问题。这个问题出现在方程定理的证明自动化反复对同一个局部声明应用 `injection(` 时；由于前向依赖，该声明无法被移除。可参见问题 #6067 中的复现示例。

- [#6189](https://github.com/leanprover/lean4/pull/6189) 改变了广义字段记法（“dot 记法”）解析函数的方式。新规则是：若 `x : S`，则 `x.f` 会相对于根命名空间解析名称 `S.f`（因此现在会受 `export` 和 `open` 的影响）。破坏性变更：别名的解析方式现在不同了。此前若 `x : S`，并且 `S.f` 是 `S'.f` 的别名，那么 `x.f` 会使用 `S'.f` 并查找类型为 `S'` 的参数。现在它会查找类型为 `S` 的参数，这通常更有用。依赖旧行为的代码应考虑把 `S` 或 `S'` 定义为对方，因为 dot 记法在解析过程中可以展开定义。

- [#6206](https://github.com/leanprover/lean4/pull/6206) 通过添加从 `List.Nat` 到 `Lean.Meta.Occurrences` 的强制转换，使得可以写 `rw (occs := [1,2]) ...`，而不必写 `rw (occs := .pos [1,2]) ...`。

- [#6220](https://github.com/leanprover/lean4/pull/6220) 为 `simp` 正式加入对 `let_fun` 的支持。

- [#6236](https://github.com/leanprover/lean4/pull/6236) 修复了这样一个问题：编辑包含嵌套文档字符串的命令时，整个命令无法被重新解析。

## 库
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Library"
%%%

- [#4904](https://github.com/leanprover/lean4/pull/4904) 为 Lean 4 Std 引入日期与时间功能。

- [#5616](https://github.com/leanprover/lean4/pull/5616) 是对 https://github.com/leanprover/lean4/pull/5609 的后续补充，添加了在分母为零时刻画 `smtUDiv` 和 `smtSDiv` 行为的引理。

- [#5866](https://github.com/leanprover/lean4/pull/5866) 验证了 `Std.HashMap` 上的 `keys` 函数。

- [#5885](https://github.com/leanprover/lean4/pull/5885) 添加 Int16/Int32/Int64。

- [#5926](https://github.com/leanprover/lean4/pull/5926) 添加 `Option.or_some'`。

- [#5927](https://github.com/leanprover/lean4/pull/5927) 添加 `List.pmap_eq_self`。

- [#5937](https://github.com/leanprover/lean4/pull/5937) 将关于 Fin.foldX 的引理上游化。

- [#5938](https://github.com/leanprover/lean4/pull/5938) 将 `List.ofFn` 上游化，并将其与 `Array.ofFn` 关联起来。

- [#5941](https://github.com/leanprover/lean4/pull/5941) 加入 `List.mapFinIdx` 及其引理，并与 `Array` 版本关联起来。

- [#5949](https://github.com/leanprover/lean4/pull/5949) 合并 `decide_True` 与 `decide_true_eq_true`。

- [#5950](https://github.com/leanprover/lean4/pull/5950) 将 `Array.takeWhile` 与 `List.takeWhile` 关联起来。

- [#5951](https://github.com/leanprover/lean4/pull/5951) 移除 `BitVec.ofFin_sub` 与 `sub_ofFin` 上的 `@[simp]`。

- [#5952](https://github.com/leanprover/lean4/pull/5952) 将 `Array.eraseIdx` 与 `List.eraseIdx` 关联起来。

- [#5961](https://github.com/leanprover/lean4/pull/5961) 定义 ISize 及其基础操作。

- [#5969](https://github.com/leanprover/lean4/pull/5969) 将 `List.insertIdx` 从 Batteries 上游化、将相关引理从 Mathlib 上游化，并修订这些引理。

- [#5970](https://github.com/leanprover/lean4/pull/5970) 弃用 `Array.split`，改用等价的 `Array.partition`。

- [#5971](https://github.com/leanprover/lean4/pull/5971) 将 `Array.isPrefixOf` 与 `List.isPrefixOf` 关联起来。

- [#5972](https://github.com/leanprover/lean4/pull/5972) 将 `Array.zipWith`/`zip`/`unzip` 与 `List` 版本关联起来。

- [#5974](https://github.com/leanprover/lean4/pull/5974) 再添加一个 `List.find?_eq_some` 引理。

- [#5981](https://github.com/leanprover/lean4/pull/5981) 将默认的 SizeOf 实例命名为 `instSizeOfDefault`。

- [#5982](https://github.com/leanprover/lean4/pull/5982) 添加关于 `List.ofFn` 的一些小引理。

- [#5984](https://github.com/leanprover/lean4/pull/5984) 为 `List` 添加引理，描述 {`foldl`, `foldr`, `foldlM`, `foldlrM`} 与 {`filter`, `filterMap`} 之间的相互作用。

- [#5985](https://github.com/leanprover/lean4/pull/5985) 将 `Array` 上的 `findSomeM?`、`findM?`、`findSome?` 和 `find?` 与 `List` 上的对应操作关联起来，并为 `Array` 的 `findSomeRevM?`、`findRevM?`、`findSomeRev?`、`findRev?` 提供 simp 引理（用 `reverse` 和常规正向查找操作来表述）。

- [#5987](https://github.com/leanprover/lean4/pull/5987) 在 `bv_decide` 中加入 `BitVec.getMsbD`。

- [#5988](https://github.com/leanprover/lean4/pull/5988) 修改 `Array.set` 的签名，使其接受 `Nat` 和一个由策略提供的边界证明，而不是 `Fin`。

- [#5995](https://github.com/leanprover/lean4/pull/5995) 在 `bv_decide` 中加入 `BitVec.sshiftRight'`。

- [#6007](https://github.com/leanprover/lean4/pull/6007) 修复 `List.modifyTailIdx` 的命名。

- [#6008](https://github.com/leanprover/lean4/pull/6008) 为单子 transformer 的 ext 引理补上缺失的 `@[ext]` 属性。

- [#6023](https://github.com/leanprover/lean4/pull/6023) 添加 `List.forIn_eq_foldlM` 的多个变体。

- [#6025](https://github.com/leanprover/lean4/pull/6025) 弃用重复的 `Fin.size_pos`。

- [#6032](https://github.com/leanprover/lean4/pull/6032) 修改 `Array.get` 的签名，使其接受 `Nat` 与一个证明，而不是 `Fin`，以与其余（规划中的）Array API 保持一致。请注意，由于引导构建问题，我们无法把 `get_elem_tactic` 作为该证明的 autoparameter 提供。鉴于用户大多会使用 `GetElem` 提供的 `xs[i]` 记法，这应该不是问题。

- [#6041](https://github.com/leanprover/lean4/pull/6041) 调整了高阶 `Array` 函数的参数顺序，优先把 `Array` 放在最后（除了带默认值的位置参数）。这与 `List` API 更一致，也更灵活，因为 dot 记法允许两种不同的部分应用形式。

- [#6049](https://github.com/leanprover/lean4/pull/6049) 新增一个用于访问当前线程 ID 的原语。

- [#6052](https://github.com/leanprover/lean4/pull/6052) 新增 `Array.pmap`，以及一个基于零拷贝 `Array.attachWith` 的 `@[csimp]` 引理。

- [#6055](https://github.com/leanprover/lean4/pull/6055) 延续 `List` 上已有的引理，为 `Array` 上的 `for` 循环添加引理。

- [#6056](https://github.com/leanprover/lean4/pull/6056) 将一些 `NameMap` 函数上游化。

- [#6060](https://github.com/leanprover/lean4/pull/6060) 实现了从 `Bool` 到所有 `UIntX` 与 `IntX` 类型的转换函数。

- [#6070](https://github.com/leanprover/lean4/pull/6070) 添加 Lean.RArray 数据结构。

- [#6074](https://github.com/leanprover/lean4/pull/6074) 允许在 `Squash` 中使用 `Sort u`。

- [#6094](https://github.com/leanprover/lean4/pull/6094) 添加浮点数与 `UInt64` 之间的原始位转换。所有受支持平台上的 Float 与 UInt 共享相同字节序，且 IEEE 754 标准确切规定了浮点数的位布局。注意，`Float.toBits` 与 `Float.toUInt64` 不同：后者试图保留数值而不是位模式。

- [#6095](https://github.com/leanprover/lean4/pull/6095) 泛化 `List.get_mem`。

- [#6097](https://github.com/leanprover/lean4/pull/6097) 调整命名约定并规范化 `NaN`。

- [#6102](https://github.com/leanprover/lean4/pull/6102) 将 `IO.rand` 和 `IO.setRandSeed` 移到 `BaseIO` 单子中。

- [#6106](https://github.com/leanprover/lean4/pull/6106) 修复左右单射性引理的命名。

- [#6111](https://github.com/leanprover/lean4/pull/6111) 补齐了 `Array.findSome?` 和 `Array.find?` 的 API，并迁移了对应 `List` 语句中的证明。

- [#6120](https://github.com/leanprover/lean4/pull/6120) 添加定理 `BitVec.(getMsbD, msb)_(rotateLeft, rotateRight)`。

- [#6126](https://github.com/leanprover/lean4/pull/6126) 添加引理，用于提取通过 `sub`/`neg`/`sshiftRight'`/`abs` 得到的 `BitVec` 的指定比特位。

- [#6130](https://github.com/leanprover/lean4/pull/6130) 添加 `Lean.loadPlugin`，向 Lean 代码暴露与 `lean` 可执行文件 `--plugin` 选项类似的功能。

- [#6132](https://github.com/leanprover/lean4/pull/6132) 将 `List.attach`/`attachWith`/`pmap` 的验证 API 复制到 `Array`。

- [#6133](https://github.com/leanprover/lean4/pull/6133) 用 `Array.eraseIdx` 和 `Array.insertIdx` 替换 `Array.feraseIdx` 与 `Array.insertAt`；两者都接受一个 `Nat` 参数和一个由策略提供的越界证明。我们还提供了 `eraseIdxIfInBounds` 和 `insertIdxIfInBounds`，当索引越界时它们是 no-op。另有返回 `Fin` 值版本的 `Array.findIdx?`。这些改动共同以较为易用的方式提升了编译器/精化器中多处数组索引的安全性。

- [#6136](https://github.com/leanprover/lean4/pull/6136) 修复了 `(default : Float)` 的运行时求值。

- [#6139](https://github.com/leanprover/lean4/pull/6139) 修改了函数 `Nat.fold`、`Nat.foldRev`、`Nat.any`、`Nat.all` 的签名，使函数能够接收上界。这让我们得以在许多地方把运行时数组越界检查变成编译时检查。

- [#6148](https://github.com/leanprover/lean4/pull/6148) 添加了一个用于创建临时目录的原语，对应于现有创建临时文件的功能。

- [#6149](https://github.com/leanprover/lean4/pull/6149) 通过补上 `getMsbD` 的实现，完善了 `ofNatLt`、`allOnes` 和 `not` 的逐元素访问器。

- [#6151](https://github.com/leanprover/lean4/pull/6151) 补全了 `BitVec` 按位运算的 `toInt` 接口。

- [#6154](https://github.com/leanprover/lean4/pull/6154) 实现 `BitVec.toInt_abs`。

- [#6155](https://github.com/leanprover/lean4/pull/6155) 为 `BitVec.signExtend` 添加 `toNat` 定理。

- [#6157](https://github.com/leanprover/lean4/pull/6157) 为 `BitVec.signExtend` 添加 `toInt` 定理。

- [#6160](https://github.com/leanprover/lean4/pull/6160) 添加定理 `mod_eq_sub`，把定理 `sub_mul_eq_mod_of_lt_of_le` 取消私有，并在 `rotate*` 章节中调整其位置，以便在其他证明中使用。

- [#6184](https://github.com/leanprover/lean4/pull/6184) 在能够把运行时边界检查转为编译时边界检查的场景下，优先使用 `Array.findFinIdx?` 而不是 `Array.findIdx?`。

- [#6188](https://github.com/leanprover/lean4/pull/6188) 补全了 UInt 类型按位运算（`and`、`or`、`xor`、`shiftLeft`、`shiftRight`）的 `toNat` 定理，并新增了 `toBitVec` 定理。同时将 `and_toNat` 重命名为 `toNat_and`，以符合当前命名约定。

- [#6190](https://github.com/leanprover/lean4/pull/6190) 添加内建 simproc `USize.reduceToNat`，用于规约作用在小于 `UInt32.size`（即 `4294967296`）字面量上的 `USize.toNat`。

- [#6191](https://github.com/leanprover/lean4/pull/6191) 添加 `Array.zipWithAll`，以及将其与 `List.zipWithAll` 关联的基础引理。

- [#6192](https://github.com/leanprover/lean4/pull/6192) 为那些最初没有获得弃用属性的 `Lean.HashMap` 函数补上弃用声明。

- [#6193](https://github.com/leanprover/lean4/pull/6193) 完成 `Init.Data.Array.BinSearch` 中的 TODO，移除 `partial` 关键字，并把运行时边界检查改为编译时边界检查。

- [#6194](https://github.com/leanprover/lean4/pull/6194) 修改 `Array.swap` 的签名，使其接受 `Nat` 参数，并通过策略提供边界检查。同时将 `Array.swap!` 重命名为 `Array.swapIfInBounds`。

- [#6195](https://github.com/leanprover/lean4/pull/6195) 将 `Array.setD` 重命名为 `Array.setIfInBounds`。

- [#6197](https://github.com/leanprover/lean4/pull/6197) 将 `Vector` 的定义及其基础函数从 Batteries 上游化。

- [#6200](https://github.com/leanprover/lean4/pull/6200) 将 `Nat.lt_pow_self` 和 `Nat.lt_two_pow` 从 Mathlib 上游化，并用它们证明 simp 定理 `Nat.mod_two_pow`。

- [#6202](https://github.com/leanprover/lean4/pull/6202) 将 `USize.toUInt64` 改为普通的非 opaque 定义。

- [#6203](https://github.com/leanprover/lean4/pull/6203) 添加定理 `le_usize_size` 和 `usize_size_le`，让证明有关 `USize.size` 的不等式更容易。

- [#6205](https://github.com/leanprover/lean4/pull/6205) 将一些 UInt 定理从 Batteries 上游化，并补充更多与 `toNat` 相关的定理。同时还添加了缺失的 `UInt8` 和 `UInt16` 与 `USize` 之间的双向转换，使 UInt 类型的接口保持一致。

- [#6207](https://github.com/leanprover/lean4/pull/6207) 确保 `Fin.foldl` 和 `Fin.foldr` 是 semireducible。没有这一点，定义相等式 `example (f : Fin 3 → ℕ) : List.ofFn f = [f 0, f 1, f 2] := rfl` 会失败。

- [#6208](https://github.com/leanprover/lean4/pull/6208) 修复 `Vector.indexOf?`。

- [#6217](https://github.com/leanprover/lean4/pull/6217) 为 `List` 的 `==` 操作添加 `simp` 引理。

- [#6221](https://github.com/leanprover/lean4/pull/6221) 修复了以下问题：
  - 在其他 Linux 发行版中，默认的 `tzdata` 目录可能与此前定义的不同；现在当目录缺失时会启用回退行为来保证正确性。
  - 去除本地时间标识符中不必要的字符。

- [#6222](https://github.com/leanprover/lean4/pull/6222) 修改 `HashSet.insertMany` 和 `HashSet.Raw.insertMany` 的定义，使它们等价于反复调用 `HashSet.insert`/`HashSet.Raw.insert`。同时也澄清了所有 `insert` 与 `insertMany` 函数的文档字符串。

- [#6230](https://github.com/leanprover/lean4/pull/6230) 将一些关于 `List.foldX` 的引理复制到 `Array`。

- [#6233](https://github.com/leanprover/lean4/pull/6233) 将关于 `Vector` 的引理从 Batteries 上游化。

- [#6234](https://github.com/leanprover/lean4/pull/6234) 将 `List.finRange` 的定义及其基础引理从 Batteries 上游化。

- [#6235](https://github.com/leanprover/lean4/pull/6235) 将 `Nat.fold`/`foldRev`/`any`/`all` 这些操作与 `List.finRange` 上对应的 `List` 操作关联起来。

- [#6241](https://github.com/leanprover/lean4/pull/6241) 重构 `Array.qsort`，移除运行时数组边界检查，并避免使用 `partial`。我们使用 `Vector` API 以及 auto_params，从而无需手写任何证明。新代码的基准表现与旧代码无可区分。

- [#6242](https://github.com/leanprover/lean4/pull/6242) 弃用 `Fin.ofNat`，改用 `Fin.ofNat'`（它接受一个 `[NeZero]` 实例，而不是返回 `Fin (n+1)` 的元素）。

- [#6247](https://github.com/leanprover/lean4/pull/6247) 添加定理 `numBits_pos`、`le_numBits`、`numBits_le`，让证明有关 `System.Platform.numBits` 的不等式更容易。

## 编译器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Compiler"
%%%

- [#5840](https://github.com/leanprover/lean4/pull/5840) 修改 `lean_sharecommon_{eq,hash}`，使其只考虑对象的有效字节，而不考虑任何未指定/未初始化的空余容量中的字节。

- [#6087](https://github.com/leanprover/lean4/pull/6087) 修复了旧代码生成器中 `Nat.ble` 和 `Nat.blt` 函数的常量折叠问题，该问题会导致错误编译。

- [#6143](https://github.com/leanprover/lean4/pull/6143) 使 Lean 在 sanitizer 环境下表现得更合理，参见 https://github.com/google/sanitizers/issues/1688。就我所知，https://github.com/google/sanitizers/wiki/AddressSanitizerUseAfterReturn#algorithm 会用堆分配替换局部变量，因此获取局部变量地址不再适合作为单调的栈使用量度量方式。

- [#6209](https://github.com/leanprover/lean4/pull/6209) 记录了 `Runtime.markPersistent` 在哪些条件下是不安全的，并据此调整了精化器。

- [#6257](https://github.com/leanprover/lean4/pull/6257) 加固 `markPersistent` 的使用。

## 漂亮打印
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Pretty-Printing"
%%%

- [#2934](https://github.com/leanprover/lean4/pull/2934) 新增选项 `pp.parens`（默认值：false），它会让漂亮打印器积极插入括号，这在教学和理解表达式结构时都很有用。例如，它会把 `p → q → r` 漂亮打印为 `p → (q → r)`。

- [#6014](https://github.com/leanprover/lean4/pull/6014) 阻止把 `Nat.succ ?_` 漂亮打印成 `?_.succ`，这会让 `apply?` 更易用。

- [#6085](https://github.com/leanprover/lean4/pull/6085) 改进了带 `CoeFnType.coeFun` 标记的强制转换的项 info（例如 Mathlib 中的 `DFunLike.coe`），使得对函数名执行“转到定义”能够生效。悬停在这类被强制转换的函数上时，现在会显示被强制转换的对象，而不是强制转换表达式本身；若悬停在函数应用中的空白处，仍可看到强制转换表达式。

- [#6096](https://github.com/leanprover/lean4/pull/6096) 改进了结构体上的 `#print` 命令，使其显示全部字段，以及这些字段继承自哪些父级，同时隐藏哪些父级以子对象表示等内部细节。如果有需要，这些信息仍保留在构造子中。私有常量的漂亮打印器也得到改进；它现在会像处理其他名称一样处理来自当前模块的私有名称，而来自其他模块的私有名称会被做卫生化处理。

- [#6119](https://github.com/leanprover/lean4/pull/6119) 新增 delab 选项 `pp.coercions.types`；启用后，会以显式类型标注显示所有强制转换。

- [#6161](https://github.com/leanprover/lean4/pull/6161) 确保在漂亮打印时，会在 `+opt` 和 `-opt` 配置选项前打印空白，从而改进 `simp?` 等策略的使用体验。

- [#6181](https://github.com/leanprover/lean4/pull/6181) 修复了一个问题：签名漂亮打印器先前会忽略 `pp.raw` 的当前设置。这修复了 `#check ident` 不遵循 `pp.raw` 的问题。关闭 #6090。

- [#6213](https://github.com/leanprover/lean4/pull/6213) 使 “synthesized 类型类实例 is not definitionally equal” 这类错误能显示出具体差异。

## 文档
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Documentation"
%%%

- [#6009](https://github.com/leanprover/lean4/pull/6009) 修复了 prec 的文档字符串中的一个拼写错误，并让文字表述更精确一点。

- [#6040](https://github.com/leanprover/lean4/pull/6040) 在文档字符串中把 join → flatten。

- [#6110](https://github.com/leanprover/lean4/pull/6110) 在补充文档的同时，对 `Lean.Elab.StructInst` 模块做了一些轻量重构。

- [#6144](https://github.com/leanprover/lean4/pull/6144) 将 3 个 doc-string 改为模块文档，因为它们看起来本来就是为此准备的！

- [#6150](https://github.com/leanprover/lean4/pull/6150) 细化内核代码注释。

- [#6158](https://github.com/leanprover/lean4/pull/6158) 调整 Data.Sum 中的文件引用。

- [#6239](https://github.com/leanprover/lean4/pull/6239) 解释了 `Expr.abstract` 引入 de Bruijn 索引的顺序。

## 服务器
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Server"
%%%

- [#5835](https://github.com/leanprover/lean4/pull/5835) 为结构体实例记法的字段添加自动补全。具体来说，现在在结构体实例记法的空白处用 `Ctrl+Space` 查询补全时，会出现完整字段列表。对自定义语法，也可以通过把字段列表解析器包在 `structInstFields` 解析器中来启用空白处结构补全。

- [#5837](https://github.com/leanprover/lean4/pull/5837) 修复了一个老的自动补全问题：当 `x.` 无法被精化为 dot 补全时，它此前会给出毫无意义的补全项。

- [#5996](https://github.com/leanprover/lean4/pull/5996) 避免补全过程中出现最大 heartbeat 错误。

- [#6031](https://github.com/leanprover/lean4/pull/6031) 修复了一次回归：此前转到定义与文档高亮在策略块上行为异常。

- [#6246](https://github.com/leanprover/lean4/pull/6246) 修复了一个性能问题：此前 Lean 语言服务器每次保存文件时都会遍历整个项目文件树，阻塞所有其他请求与通知的处理，并在保存后显著增加整体语言服务器延迟。

## Lake
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Lake"
%%%

- [#5684](https://github.com/leanprover/lean4/pull/5684) 在 `lake update` 时更新工具链。

- [#6026](https://github.com/leanprover/lean4/pull/6026) 为 `lake new` 模板生成的每个 Lean 文件在末尾添加换行符。

- [#6218](https://github.com/leanprover/lean4/pull/6218) 如果包的构建目录已经存在，Lake 将不再自动抓取 GitHub 云端发布产物（与 Reservoir 缓存的行为保持一致）。这样可防止缓存覆盖现有的预构建产物。用户仍可通过运行 `lake build <pkg>:release` 手动抓取缓存并覆盖构建目录。

- [#6225](https://github.com/leanprover/lean4/pull/6225) 让 `lake build` 也会积极打印包 materialization 的日志行。此前，只有 `lake update` 会进行主动日志输出。

- [#6231](https://github.com/leanprover/lean4/pull/6231) 改进了 Lake 从 Reservoir 获取依赖失败时产生的错误信息。如果该包未被索引，它会给出如何从 GitHub 引入该包的建议。

## 其他
%%%
tag := "The-Lean-Language-Reference--Release-Notes--Lean-4___15___0-_LPAR_2025-01-04_RPAR_--Other"
%%%

- [#6137](https://github.com/leanprover/lean4/pull/6137) 添加对在跟踪性能分析器输出中显示多个线程的支持。

- [#6138](https://github.com/leanprover/lean4/pull/6138) 修复了 `trace.profiler.pp` 未使用项漂亮打印器的问题。

- [#6259](https://github.com/leanprover/lean4/pull/6259) 确保嵌套跟踪节点仅在 `trace.profiler` 处于激活状态时才带有计时信息。
````
