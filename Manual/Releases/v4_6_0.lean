/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.6.0 (2024-02-29)" =>
%%%
tag := "release-v4.6.0"
file := "v4.6.0"
%%%

````markdown
* 为 `simp` 添加自定义化简过程（即 `simproc`）。Simproc 可以由化简器在指定的项模式上触发。下面是一个小例子：
  ```lean
  import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

  def foo (x : Nat) : Nat :=
    x + 10

  /--
  The `simproc` `reduceFoo` is invoked on terms that match the pattern `foo _`.
  -/
  simproc reduceFoo (foo _) :=
    /- A term of type `Expr → SimpM Step -/
    fun e => do
      /-
      The `Step` type has three constructors: `.done`, `.visit`, `.continue`.
      * The constructor `.done` instructs `simp` that the result does
        not need to be simplified further.
      * The constructor `.visit` instructs `simp` to visit the resulting expression.
      * The constructor `.continue` instructs `simp` to try other simplification procedures.

      All three constructors take a `Result`. The `.continue` constructor may also take `none`.
      `Result` has two fields `expr` (the new expression), and `proof?` (an optional proof).
       If the new expression is definitionally equal to the input one, then `proof?` can be omitted or set to `none`.
      -/
      /- `simp` uses matching modulo reducibility. So, we ensure the term is a `foo`-application. -/
      unless e.isAppOfArity ``foo 1 do
        return .continue
      /- `Nat.fromExpr?` tries to convert an expression into a `Nat` value -/
      let some n ← Nat.fromExpr? e.appArg!
        | return .continue
      return .done { expr := Lean.mkNatLit (n+10) }
  ```
  我们可以用命令 `set_option simprocs false` 禁用 simproc 支持。这个命令在将文件移植到 v4.6.0 时尤其有用。
  Simproc 可以受作用域约束、手动加入 `simp` 命令，也可以用 `-` 屏蔽。`simp?` 同样支持它们。`simp only` 不会执行任何 `simproc`。下面是针对上述 `simproc` 的一些示例。
  ```lean
  example : x + foo 2 = 12 + x := by
    set_option simprocs false in
      /- This `simp` command does not make progress since `simproc`s are disabled. -/
      fail_if_success simp
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- `simp only` must not use the default simproc set. -/
    fail_if_success simp only
    simp_arith

  example : x + foo 2 = 12 + x := by
    /-
    `simp only` does not use the default simproc set,
    but we can provide simprocs as arguments. -/
    simp only [reduceFoo]
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- We can use `-` to disable `simproc`s. -/
    fail_if_success simp [-reduceFoo]
    simp_arith
  ```
  命令 `register_simp_attr <id>` 现在会创建一个名为 `<id>` 的 `simp` **以及** `simproc` 集。下面这条命令告诉 Lean 将 `reduceFoo` 化简过程放入 `my_simp` 集；若未指定集合，则 Lean 使用默认的 `simp` 集。
  ```lean
  simproc [my_simp] reduceFoo (foo _) := ...
  ```

* `termination_by` 与 `decreasing_by` 终止性提示的语法已全面调整：

  * 它们现在直接放在所作用的函数之后，而不再放在整个 `mutual` 块之后。
  * 因此，提示中不再需要写出函数名。
  * 如果函数带有 `where` 子句，则该函数的 `termination_by` 与
    `decreasing_by` 放在 `where` 之前。`where` 子句中的函数也可以有各自的终止性提示，
    并且各自紧跟在对应定义之后。
  * `termination_by` 子句现在只能绑定“额外参数”，即那些并未在函数头中绑定，
    而是在 lambda 表达式（`:= fun x y z =>`）或模式（`| x, n + 1 => …`）中绑定的参数。
    这些额外参数过去被理解为函数参数的后缀；现在则被理解为前缀。

  迁移指南：在简单情况下，只需去掉函数名，以及任何已经在函数头绑定的变量。
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by foo a b => a - b
  +termination_by a b => a - b
  ```
  或者
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by _ a b => a - b
  +termination_by a b => a - b
  ```

  如果参数已经在函数头（即 `:` 之前）绑定，也要将它们去掉：
  ```diff
   def foo (a b : Nat) : Nat := …
  -termination_by foo a b => a - b
  +termination_by a - b
  ```

  否则，如果有多个额外参数，请确保引用的是正确那些参数；绑定变量现在按从左到右解释，不再是从右到左：
  ```diff
   def foo : Nat → Nat → Nat → Nat
     | a, b, c => …
  -termination_by foo b c => b
  +termination_by a b => b
  ```

  对于 `mutual` 块，请将终止性参数（不带函数名）放到对应函数定义旁边：
  ```diff
  -mutual
  -def foo : Nat → Nat → Nat := …
  -def bar : Nat → Nat := …
  -end
  -termination_by
  -  foo a b => a - b
  -  bar a => a
  +mutual
  +def foo : Nat → Nat → Nat := …
  +termination_by a b => a - b
  +def bar : Nat → Nat := …
  +termination_by a => a
  +end
  ```

  同样地，如果通过 `where` 或 `let rec` 进行（互）递归，终止性提示现在也直接放在它所作用的函数之后：
  ```diff
  -def foo (a b : Nat) : Nat := …
  -  where bar (x : Nat) : Nat := …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat := …
  +termination_by a - b
  +  where
  +    bar (x : Nat) : Nat := …
  +    termination_by x

  -def foo (a b : Nat) : Nat :=
  -  let rec bar (x : Nat) :  Nat := …
  -  …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat :=
  +  let rec bar (x : Nat) : Nat := …
  +    termination_by x
  +  …
  +termination_by a - b
  ```

  过去若一个 `decreasing_by` 子句会作用于多个互递归函数，现在必须将该策略分别重复写出。

* `decreasing_by` 的语义已更改；现在策略会一次性应用于所有终止性证明目标，而不是逐个应用。

  这使得交互式编写终止性证明更方便，因为现在可以分别聚焦每个子目标，例如使用 `·`。此前，给出的策略脚本必须对 _所有_ 目标都有效，因此常常需要借助 `first` 之类的策略组合子：

  ```diff
   def foo (n : Nat) := … foo e1 … foo e2 …
  -decreasing_by
  -simp_wf
  -first | apply something_about_e1; …
  -      | apply something_about_e2; …
  +decreasing_by
  +all_goals simp_wf
  +· apply something_about_e1; …
  +· apply something_about_e2; …
  ```

  如果要恢复旧行为、将某个策略分别应用到每个目标，请使用 `all_goals`：
  ```diff
   def foo (n : Nat) := …
  -decreasing_by some_tactic
  +decreasing_by all_goals some_tactic
  ```

  对于互递归，现在每个 `decreasing_by` 只作用于它所属的函数。如果递归组中的某些函数没有自己的 `decreasing_by`，则会使用默认的 `decreasing_tactic`。如果多个函数需要应用同一个策略，就必须在这些函数处分别重复书写 `decreasing_by` 子句。

* 调整 `InfoTree.context`，以便在精译命令时更方便地为其补充局部上下文。这会破坏与下游项目的向后兼容性：凡是手动遍历 `InfoTree` 而不是通过 `InfoUtils.lean` 中函数访问的项目，以及手动创建并保存 `InfoTree` 的项目，都会受影响。如何迁移代码，请参见 [PR #3159](https://github.com/leanprover/lean4/pull/3159)。

* 为语言服务器添加对[调用层级请求](https://www.youtube.com/watch?v=r5LA7ivUb2c)的支持（[PR #3082](https://github.com/leanprover/lean4/pull/3082)）。该 PR 对 .ilean 格式的修改意味着，项目必须完整重建一次，以生成新格式的 .ilean 文件，之后“查找引用”等功能才能再次正常工作。

* 含有多个来源的结构体实例（例如 `{a, b, c with x := 0}`）现在会严格按从左到右的顺序，从这些来源中填充字段。此外，结构体实例精译器现在会更积极地利用来源来填充子对象字段，从而避免不必要的来源 eta 展开，因此大幅降低了对高成本结构体 eta 归约的依赖。这对 mathlib 影响很大，使总 CPU 指令数降低了 3%，并支持了像 leanprover-community/mathlib4#8386 这样的重要重构，而后者将构建时间缩短了近 20%。参见 [PR #2478](https://github.com/leanprover/lean4/pull/2478) 和 [RFC #2451](https://github.com/leanprover/lean4/issues/2451)。

* 添加美观打印器设置，以省略深度嵌套的项（`pp.deepTerms false` 和 `pp.deepTerms.threshold`）（[PR #3201](https://github.com/leanprover/lean4/pull/3201)）

* 添加美观打印器选项 `pp.numeralTypes` 与 `pp.natLit`。
  当 `pp.numeralTypes` 为 true 时，自然数、整数和有理数字面量会以带类型标注的形式进行美观打印，例如 `(2 : Rat)`、`(-2 : Rat)` 和 `(-2 / 3 : Rat)`。
  当 `pp.natLit` 为 true 时，原始自然数字面量会被美观打印为 `nat_lit 2`。
  参见 [PR #2933](https://github.com/leanprover/lean4/pull/2933) 和 [RFC #3021](https://github.com/leanprover/lean4/issues/3021)。

Lake 更新：
* 改进平台信息与控制 [#3226](https://github.com/leanprover/lean4/pull/3226)
* 支持从不受支持的清单版本执行 `lake update` [#3149](https://github.com/leanprover/lean4/pull/3149)

其他改进：
* 让 `intro` 识别 `let_fun` [#3115](https://github.com/leanprover/lean4/pull/3115)
* 在 `rw` 中生成更简洁的证明项 [#3121](https://github.com/leanprover/lean4/pull/3121)
* 在 `simp` 生成的证明中融合嵌套的 `mkCongrArg` 调用 [#3203](https://github.com/leanprover/lean4/pull/3203)
* 支持 `induction using` 后接一般项 [#3188](https://github.com/leanprover/lean4/pull/3188)
* 允许在 `let` 中做泛化 [#3060](https://github.com/leanprover/lean4/pull/3060)，修复 [#3065](https://github.com/leanprover/lean4/issues/3065)
* 对越界的 `swap!` 进行归约时应返回 `a`，而不是 `default`` [#3197](https://github.com/leanprover/lean4/pull/3197)，修复 [#3196](https://github.com/leanprover/lean4/issues/3196)
* 为含 `Prop` 字段的结构体派生 `BEq` [#3191](https://github.com/leanprover/lean4/pull/3191)，修复 [#3140](https://github.com/leanprover/lean4/issues/3140)
* 在更多 `casesOnApp`/`matcherApp` 情况下改进 refine [#3176](https://github.com/leanprover/lean4/pull/3176)，修复 [#3175](https://github.com/leanprover/lean4/pull/3175)
* 不再从 Lean 模块名中剥离带点的组成部分 [#2994](https://github.com/leanprover/lean4/pull/2994)，修复 [#2999](https://github.com/leanprover/lean4/issues/2999)
* 修复某些处理器下 `deriving` 只派生第一条声明的问题 [#3058](https://github.com/leanprover/lean4/pull/3058)，修复 [#3057](https://github.com/leanprover/lean4/issues/3057)
* 在 kabstract/rw 中，对于不允许的出现位置不再实例化元变量 [#2539](https://github.com/leanprover/lean4/pull/2539)，修复 [#2538](https://github.com/leanprover/lean4/issues/2538)
* 为 `cases h : ...` 提供悬停信息 [#3084](https://github.com/leanprover/lean4/pull/3084)
````
