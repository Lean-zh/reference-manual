/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0-m5 (2022-08-22)" =>
%%%
tag := "release-v4.0.0-m5"
file := "v4.0.0-m5"
%%%

````markdown
这是 Lean 4 的第五个里程碑版本。它包含许多改进和许多新特性。
自上一个里程碑以来，我们已有 1495 次提交。

贡献者：
```
   885  Leonardo de Moura
   310  Sebastian Ullrich
    69  E.W.Ayers
    66  Wojciech Nawrocki
    49  Gabriel Ebner
    38  Mario Carneiro
    22  larsk21
    10  tydeu
     6  Ed Ayers
     6  Mariana Alanis
     4  Chris Lovett
     3  Jannis Limperg
     2  François G. Dorais
     2  Henrik Böving
     2  Jakob von Raumer
     2  Scott Morrison
     2  Siddharth
     1  Andrés Goens
     1  Arthur Paulino
     1  Connor Baker
     1  Joscha
     1  KaseQuark
     1  Lars
     1  Mac
     1  Marcus Rossel
     1  Patrick Massot
     1  Siddharth Bhat
     1  Timo
     1  Vincent de Haan
     1  William Blake
     1  Yuri de Wit
     1  ammkrn
     1  asdasd1dsadsa
     1  kzvi
```



* 将 Lake 更新到 v4.0.0。详细变更请参见 [v4.0.0 发布说明](https://github.com/leanprover/lake/releases/tag/v4.0.0)。

* 现在支持位于不同命名空间中的互递归声明。例如：
  ```lean
  mutual
    def Foo.boo (x : Nat) :=
      match x with
      | 0 => 1
      | x + 1 => 2*Boo.bla x

    def Boo.bla (x : Nat) :=
      match x with
      | 0 => 2
      | x+1 => 3*Foo.boo x
  end
  ```
  系统会为公共前缀自动创建一个 `namespace`。例如：
  ```lean
  mutual
    def Tst.Foo.boo (x : Nat) := ...
    def Tst.Boo.bla (x : Nat) := ...
  end
  ```
  会展开为
  ```lean
  namespace Tst
  mutual
    def Foo.boo (x : Nat) := ...
    def Boo.bla (x : Nat) := ...
  end
  end Tst
  ```

* 允许用户为现有类型类安装自己的 `deriving` 处理器。
  示例见 [Simple.lean](https://github.com/leanprover/lean4/blob/master/tests/pkg/deriving/UserDeriving/Simple.lean)。

* 添加 tactic `congr (num)?`。更多细节见文档字符串。

* [缺失文档检查器](https://github.com/leanprover/lean4/pull/1390)

* `match` 语法记法现在会检查未使用的分支。参见 issue [#1371](https://github.com/leanprover/lean4/issues/1371)。

* 为结构体实例字段提供自动补全。例如：
  ```lean
  example : Nat × Nat := {
    f -- HERE
  }
  ```
  `fst` 现在会出现在自动补全建议列表中。

* 为点式标识符记法提供自动补全。例如：
  ```lean
  example : Nat :=
    .su -- HERE
  ```
  `succ` 现在会出现在自动补全建议列表中。

* 声明 `OfNat` 实例时不再需要 `nat_lit`。参见 issues [#1389](https://github.com/leanprover/lean4/issues/1389) 和 [#875](https://github.com/leanprover/lean4/issues/875)。例如：
  ```lean
  inductive Bit where
    | zero
    | one

  instance inst0 : OfNat Bit 0 where
    ofNat := Bit.zero

  instance : OfNat Bit 1 where
    ofNat := Bit.one

  example : Bit := 0
  example : Bit := 1
  ```

* 添加 `[elabAsElim]` 属性（在 Lean 3 中名为 `elab_as_eliminator`）。动机：简化 Mathlib 向 Lean 4 的移植。

* `Trans` 类型类现在接受位于 `Type u` 中的关系。参见这条 [Zulip 讨论](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Calc.20mode/near/291214574)。

* 接受未经转义的关键字作为归纳类型构造子名称。在使用处通常可以通过点记法避免转义。
  ```lean
  inductive MyExpr
    | let : ...

  def f : MyExpr → MyExpr
    | .let ... => .let ...
  ```

* 对形如 `[Nat -> Decidable p]` 的参数化局部实例报错。类型类解析过程
  无法使用这类局部实例，因为该参数不具有前向依赖。
  可使用 `set_option checkBinderAnnotations false` 关闭此检查。

* 添加选项 `pp.showLetValues`。当其设为 `false` 时，信息视图会隐藏目标中 `let` 变量的值。
  默认情况下，在显示 tactic 目标时它为 `true`，否则为 `false`。
  更多细节见 [问题 #1345](https://github.com/leanprover/lean4/issues/1345)。

* 添加选项 `warningAsError`。设为 true 时，警告消息会被当作错误处理。

* 在模式中支持点记法与具名参数。例如：
  ```lean
  def getForallBinderType (e : Expr) : Expr :=
    match e with
    | .forallE (binderType := type) .. => type
    | _ => panic! "forall expected"
  ```

* “跳转到定义”现在可用于以下属性中嵌入的函数名：
  `@[implementedBy funName]`、`@[tactic parserName]`、`@[termElab parserName]`、`@[commandElab parserName]`、
  `@[builtinTactic parserName]`、`@[builtinTermElab parserName]` 和 `@[builtinCommandElab parserName]`。
   参见 [问题 #1350](https://github.com/leanprover/lean4/issues/1350)。

* 提升 `MVarId` 方法的可发现性。参见 [问题 #1346](https://github.com/leanprover/lean4/issues/1346)。
  我们仍需为 `FVarId`、`LVarId`、`Expr` 以及其他对象添加类似的方法。
  许多现有方法已被标记为弃用。

* 添加属性 `[deprecated]`，用于标记已弃用的声明。例如：
  ```lean
  def g (x : Nat) := x + 1

  -- Whenever `f` is used, a warning message is generated suggesting to use `g` instead.
  @[deprecated g]
  def f (x : Nat) := x + 1

  #check f 0 -- warning: `f` has been deprecated, use `g` instead

  -- Whenever `h` is used, a warning message is generated.
  @[deprecated]
  def h (x : Nat) := x + 1

  #check h 0 -- warning: `h` has been deprecated
  ```

* 为 universe level 元变量 id 添加类型 `LevelMVarId`（及缩写 `LMVarId`）。
  动机：防止元编程者混淆 universe 元变量 id 与表达式元变量 id。

* 改进 `calc` 项与 tactic。参见 [问题 #1342](https://github.com/leanprover/lean4/issues/1342)。

* [放宽 antiquotation 解析](https://github.com/leanprover/lean4/pull/1272)，进一步减少了显式 `$x:p` antiquotation 种类注解的需求。

* 为归纳类型中的计算字段添加支持。例如：
  ```lean
  inductive Exp
    | var (i : Nat)
    | app (a b : Exp)
  with
    @[computedField] hash : Exp → Nat
      | .var i => i
      | .app a b => a.hash * b.hash + 1
  ```
  随后，`Exp.hash` 函数的结果会作为额外的“计算”字段存储在 `.var` 和 `.app` 构造子中；
  `Exp.hash` 直接访问该字段，因此可在常数时间内运行（即使面对 DAG 风格的值也是如此）。

* 更新 `a[i]` 记法。它现在基于如下类型类
  ```lean
  class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
    getElem (xs : cont) (i : idx) (h : dom xs i) : Elem
  ```
  记法 `a[i]` 现在定义如下
  ```lean
  macro:max x:term noWs "[" i:term "]" : term => `(getElem $x $i (by get_elem_tactic))
  ```
  `i` 是合法索引的证明由 tactic `get_elem_tactic` 自动合成。
  例如，类型 `Array α` 具有如下实例
  ```lean
  instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where ...
  instance : GetElem (Array α) USize α fun xs i => LT.lt i.toNat xs.size where ...
  ```
  你可以使用记法 `a[i]'h` 手动给出该证明。
  此外还引入了另外两种记法：`a[i]!` 与 `a[i]?`。对于 `a[i]!`，若 `i` 不是合法索引，则会在
  运行时产生 panic 报错消息。`a[i]?` 的类型是 `Option α`，如果索引 `i` 非法，
  `a[i]?` 会求值为 `none`。
  这三种新记法定义如下：
  ```lean
  @[inline] def getElem' [GetElem cont idx elem dom] (xs : cont) (i : idx) (h : dom xs i) : elem :=
  getElem xs i h

  @[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
    if h : _ then getElem xs i h else panic! "index out of bounds"

  @[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
  macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)
  macro x:term noWs "[" i:term "]'" h:term:max : term => `(getElem' $x $i $h)
  ```
  参见 [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/String.2EgetOp/near/287855425) 上的讨论。
  示例：
  ```lean
  example (a : Array Int) (i : Nat) : Int :=
    a[i] -- Error: failed to prove index is valid ...

  example (a : Array Int) (i : Nat) (h : i < a.size) : Int :=
    a[i] -- Ok

  example (a : Array Int) (i : Nat) : Int :=
    a[i]! -- Ok

  example (a : Array Int) (i : Nat) : Option Int :=
    a[i]? -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    a[0]'(by rw [h]; decide) -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    have : 0 < a.size := by rw [h]; decide
    have : 1 < a.size := by rw [h]; decide
    a[0] + a[1] -- Ok

  example (a : Array Int) (i : USize) (h : i.toNat < a.size) : Int :=
    a[i] -- Ok
  ```
  `get_elem_tactic` 定义如下
  ```lean
  macro "get_elem_tactic" : tactic =>
    `(first
      | get_elem_tactic_trivial
      | fail "failed to prove index is valid, ..."
     )
  ```
  辅助 tactic `get_elem_tactic_trivial` 可以通过 `macro_rules` 扩展。默认情况下，它会尝试 `trivial`、`simp_arith`，以及针对 `Fin` 的特殊情形。未来它还会尝试 `linarith`。
  你可以像下面这样用 `my_tactic` 扩展 `get_elem_tactic_trivial`
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| my_tactic)
  ```
  请注意，`GetElem` 中 `Idx` 的类型并不依赖于 `Cont`。因此，你不能写出这样的实例 `instance : GetElem (Array α) (Fin ??) α fun xs i => ...`，不过 Lean 库提供了如下辅助实例：
  ```lean
  instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
    getElem xs i h := getElem xs i.1 h
  ```
  以及辅助 tactic
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)
  ```
  例如：
  ```lean
  example (a : Array Nat) (i : Fin a.size) :=
    a[i] -- Ok

  example (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
    a[i] -- Ok
  ```

* 更好地支持递归声明中的限定名。现在支持如下写法：
  ```lean
  namespace Nat
    def fact : Nat → Nat
    | 0 => 1
    | n+1 => (n+1) * Nat.fact n
  end Nat
  ```

* 在 `#eval` 中添加对 `CommandElabM` monad 的支持。例如：
  ```lean
  import Lean

  open Lean Elab Command

  #eval do
    let id := mkIdent `foo
    elabCommand (← `(def $id := 10))

  #eval foo -- 10
  ```

* 即使期望类型不可用，也会尝试精化 `do` 记法。当期望类型不可用时，我们仍然会延后精化。
  这一变更在编写如下示例时尤其有用
  ```lean
  #eval do
    IO.println "hello"
    IO.println "world"
  ```
  也就是说，我们不再需要使用 `#eval show IO _ from do ...` 这种写法。
  需要注意的是，当期望类型不可用时，自动单子提升的效果会变差。
  单子多态函数（例如 `ST.Ref.get`）同样需要期望类型。

* 在 Linux 上，panic 现在默认会打印回溯；可通过将环境变量 `LEAN_BACKTRACE` 设为 `0` 来禁用。
  其他平台尚待确定。

* 现在会在需要时自动引入 `group(·)` `syntax` 组合子，例如在 `(...)+` 中使用多个解析器时。

* 添加[“类型化宏”](https://github.com/leanprover/lean4/pull/1251)：syntax antiquotation 产生和接受的语法树现在会记住其语法种类，从而避免意外生成格式错误的语法树，并减少对显式 `:kind` antiquotation 注解的需求。详情见该 PR。

* 受保护定义的别名现在也同样受保护。例如：
  ```lean
  protected def Nat.double (x : Nat) := 2*x

  namespace Ex
  export Nat (double) -- Add alias Ex.double for Nat.double
  end Ex

  open Ex
  #check Ex.double -- Ok
  #check double -- Error, `Ex.double` is alias for `Nat.double` which is protected
  ```

* 使用 `IO.getRandomBytes` 为 `IO.rand` 初始化随机种子。参见[该 PR](https://github.com/leanprover/lean4-samples/pull/2)中的讨论。

* 改进点记法与别名之间的交互。更多细节参见 [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Namespace-based.20overloading.20does.20not.20find.20exports/near/282946185) 上的讨论。
  例如：
  ```lean
  def Set (α : Type) := α → Prop
  def Set.union (s₁ s₂ : Set α) : Set α := fun a => s₁ a ∨ s₂ a
  def FinSet (n : Nat) := Fin n → Prop

  namespace FinSet
    export Set (union) -- FinSet.union is now an alias for `Set.union`
  end FinSet

  example (x y : FinSet 10) : FinSet 10 :=
    x.union y -- Works
  ```

* `ext` 与 `enter` 这两个 conv tactic 现在可以进入 let 声明内部。例如：
  ```lean
  example (g : Nat → Nat) (y : Nat) (h : let x := y + 1; g (0+x) = x) : g (y + 1) = y + 1 := by
    conv at h => enter [x, 1, 1]; rw [Nat.zero_add]
    /-
      g : Nat → Nat
      y : Nat
      h : let x := y + 1;
          g x = x
      ⊢ g (y + 1) = y + 1
    -/
    exact h
  ```

* 添加 `zeta` conv tactic，用于展开 let 声明。例如：
  ```lean
  example (h : let x := y + 1; 0 + x = y) : False := by
    conv at h => zeta; rw [Nat.zero_add]
    /-
      y : Nat
      h : y + 1 = y
      ⊢ False
    -/
    simp_arith at h
  ```

* 改进命名空间解析。参见问题 [#1224](https://github.com/leanprover/lean4/issues/1224)。例如：
  ```lean
  import Lean
  open Lean Parser Elab
  open Tactic -- now opens both `Lean.Parser.Tactic` and `Lean.Elab.Tactic`
  ```

* 将 `constant` 命令重命名为 `opaque`。参见 [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/What.20is.20.60opaque.60.3F/near/284926171) 上的讨论。

* 扩展 `induction` 与 `cases` 语法：单个分支中可包含多个左侧模式。这一扩展与 `match` 表达式上的实现非常相似。例如：
  ```lean
  inductive Foo where
    | mk1 (x : Nat) | mk2 (x : Nat) | mk3

  def f (v : Foo) :=
    match v with
    | .mk1 x => x + 1
    | .mk2 x => 2*x + 1
    | .mk3   => 1

  theorem f_gt_zero : f v > 0 := by
    cases v with
    | mk1 x | mk2 x => simp_arith!  -- New feature used here!
    | mk3 => decide
  ```

* [现在支持 `do` 块中的 `let/if` 缩进。](https://github.com/leanprover/lean4/issues/1120)

* 添加无名 antiquotation `$_`，用于语法 quotation 模式。

* [添加未使用变量检查器](https://github.com/leanprover/lean4/pull/1159)。欢迎反馈！

* 如果声明体中包含一个既未出现在声明类型中、也不是显式参数的 universe 参数，Lean 现在会报错。
  例如：
  ```lean
  /-
  The following declaration now produces an error because `PUnit` is universe polymorphic,
  but the universe parameter does not occur in the function type `Nat → Nat`
  -/
  def f (n : Nat) : Nat :=
    let aux (_ : PUnit) : Nat := n + 1
    aux ⟨⟩

  /-
  The following declaration is accepted because the universe parameter was explicitly provided in the
  function signature.
  -/
  def g.{u} (n : Nat) : Nat :=
    let aux (_ : PUnit.{u}) : Nat := n + 1
    aux ⟨⟩
  ```

* 添加 `subst_vars` tactic。

* [修复多重继承中结构体字段里的 `autoParam` 丢失问题。](https://github.com/leanprover/lean4/issues/1158)。

* 添加 `[eliminator]` 属性。它允许用户为 `induction` 与 `cases` tactics 指定默认的递归子/消去子。
  这是 `using` 记法的另一种替代方式。例如：
  ```lean
  @[eliminator] protected def recDiag {motive : Nat → Nat → Sort u}
      (zero_zero : motive 0 0)
      (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
      (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
      (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1))
      (x y : Nat) :  motive x y :=
    let rec go : (x y : Nat) → motive x y
      | 0,     0 => zero_zero
      | x+1, 0   => succ_zero x (go x 0)
      | 0,   y+1 => zero_succ y (go 0 y)
      | x+1, y+1 => succ_succ x y (go x y)
    go x y
  termination_by go x y => (x, y)

  def f (x y : Nat) :=
    match x, y with
    | 0,   0   => 1
    | x+1, 0   => f x 0
    | 0,   y+1 => f 0 y
    | x+1, y+1 => f x y
  termination_by f x y => (x, y)

  example (x y : Nat) : f x y > 0 := by
    induction x, y <;> simp [f, *]
  ```

* 为结构递归与良基递归模块添加对 `casesOn` 应用的支持。
  这一特性在使用 tactic 编写定义时非常有用。例如：
  ```lean
  inductive Foo where
    | a | b | c
    | pair: Foo × Foo → Foo

  def Foo.deq (a b : Foo) : Decidable (a = b) := by
    cases a <;> cases b
    any_goals apply isFalse Foo.noConfusion
    any_goals apply isTrue rfl
    case pair a b =>
      let (a₁, a₂) := a
      let (b₁, b₂) := b
      exact match deq a₁ b₁, deq a₂ b₂ with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁,h₂])
      | isFalse h₁, _ => isFalse (fun h => by cases h; cases (h₁ rfl))
      | _, isFalse h₂ => isFalse (fun h => by cases h; cases (h₂ rfl))
  ```

* `Option` 再次成为 monad。辅助类型 `OptionM` 已被移除。参见 [Zulip 讨论串](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Do.20we.20still.20need.20OptionM.3F/near/279761084)。

* 改进 `split` tactic。它过去会在形如 `match h : e with ...` 且 `e` 不是自由变量的 `match` 表达式上失败。
  这种失败过去发生在泛化阶段。


* 为在判别式中使用 `h :` 记法的 `match` 表达式引入新的编码。相关信息在反精化过程中不会丢失，
  这也为更好的 `split` tactic 奠定了基础。例如：
  ```lean
  #print Nat.decEq
  /-
  protected def Nat.decEq : (n m : Nat) → Decidable (n = m) :=
  fun n m =>
    match h : Nat.beq n m with
    | true => isTrue (_ : n = m)
    | false => isFalse (_ : ¬n = m)
  -/
  ```

* `exists` tactic 现在接受以逗号分隔的项列表。

* 添加 `dsimp` 与 `dsimp!` tactics。它们保证结果项在定义上相等，并且只应用
  `rfl` 定理。

* 修复在 `match` 模式中使用带 `[matchPattern]` 标记的定义（例如 `Nat.add`）时的绑定器信息。
  现在，下面示例中的变量 `y` 会具有正确的绑定器信息。
  ```lean
  def f (x : Nat) : Nat :=
    match x with
    | 0 => 1
    | y + 1 => y
  ```

* （修复）结构体字段的默认值现在可以依赖结构体参数。例如：
  ```lean
  structure Something (i: Nat) where
  n1: Nat := 1
  n2: Nat := 1 + i

  def s : Something 10 := {}
  example : s.n2 = 11 := rfl
  ```

* 在 `simp` 所使用的 `dsimp` 辅助方法中应用 `rfl` 定理。`dsimp` 可以在表达式中的任意位置使用，
  因为它保持定义相等。

* 细化 auto bound implicit 特性。它不再把与当前正在定义的声明同名的未绑定变量纳入考虑。例如：
  ```lean
  def f : f → Bool := -- Error at second `f`
    fun _ => true

  inductive Foo : List Foo → Type -- Error at second `Foo`
    | x : Foo []
  ```
  在这一细化之前，上述声明会被接受，而第二个 `f` 与 `Foo` 会被视作 auto implicit 变量。也就是说，
  `f : {f : Sort u} → f → Bool`，以及
  `Foo : {Foo : Type u} → List Foo → Type`。


* 修复递归声明的语法高亮。例如
  ```lean
  inductive List (α : Type u) where
    | nil : List α  -- `List` is not highlighted as a variable anymore
    | cons (head : α) (tail : List α) : List α

  def List.map (f : α → β) : List α → List β
    | []    => []
    | a::as => f a :: map f as -- `map` is not highlighted as a variable anymore
  ```
* 为 `Lean.Meta.Simp.Config` 添加 `autoUnfold` 选项，以及以下宏
  - `simp!` for `simp (config := { autoUnfold := true })`
  - `simp_arith!` for `simp (config := { autoUnfold := true, arith := true })`
  - `simp_all!` for `simp_all (config := { autoUnfold := true })`
  - `simp_all_arith!` for `simp_all (config := { autoUnfold := true, arith := true })`

  当 `autoUnfold` 设为 true 时，`simp` 会尝试展开以下几类定义
  - 由结构递归定义的递归定义。
  - 函数体为 `match` 表达式的非递归定义。此类定义
    仅在 `match` 可归约时才会被展开。
  例如：
  ```lean
  def append (as bs : List α) : List α :=
    match as with
    | [] => bs
    | a :: as => a :: append as bs

  theorem append_nil (as : List α) : append as [] = as := by
    induction as <;> simp_all!

  theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
    induction as <;> simp_all!
  ```

* 添加 `save` tactic，以更方便地创建 checkpoint。例如：
  ```lean
  example : <some-proposition> := by
    tac_1
    tac_2
    save
    tac_3
    ...
  ```
  等价于
  ```lean
  example : <some-proposition> := by
    checkpoint
      tac_1
      tac_2
    tac_3
    ...
  ```

* 移除对归纳数据类型构造子中 `{}` 注解的支持。这一注解几乎无人使用，而参数绑定的绑定器信息现在可通过新的“归纳族索引提升为参数”机制来控制。例如，下面这个使用 `{}` 的声明
  ```lean
  inductive LE' (n : Nat) : Nat → Prop where
    | refl {} : LE' n n -- Want `n` to be explicit
    | succ  : LE' n m → LE' n (m+1)
  ```
  现在可以写成
  ```lean
  inductive LE' : Nat → Nat → Prop where
    | refl (n : Nat) : LE' n n
    | succ : LE' n m → LE' n (m+1)
  ```
  在这两种写法中，该归纳族都有一个参数和一个索引。
  请记住，实际参数个数可通过命令 `#print` 查看。

* 移除 `structure` 命令中对 `{}` 注解的支持。

* 对 LSP 服务器做了多项改进。例如：在互递归片段中支持“跳转到定义”、修复 match 表达式模式中的错误悬停信息、支持模式变量的“跳转到定义”、修复函数头中的自动补全，等等。

* 在 `macro ... xs:p* ...` 及类似的组合子宏绑定中，`xs` 现在具有正确的类型 `Array Syntax`

* 语法模式中的标识符在匹配时现在会忽略宏作用域。

* 改进构造子 auto implicit 参数的绑定器名称。例如，给定归纳数据类型
  ```lean
  inductive Member : α → List α → Type u
    | head : Member a (a::as)
    | tail : Member a bs → Member a (b::bs)
  ```
  之前：
  ```lean
  #check @Member.head
  -- @Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)
  ```
  现在：
  ```lean
  #check @Member.head
  -- @Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)
  ```

* 改进当构造子参数 universe level 过大时的错误消息。

* 添加对 `for h : i in [start:stop] do .. ` 的支持，其中 `h : i ∈ [start:stop]`。这一特性有助于证明如下函数的终止性：
  ```lean
  inductive Expr where
    | app (f : String) (args : Array Expr)

  def Expr.size (e : Expr) : Nat := Id.run do
    match e with
    | app f args =>
      let mut sz := 1
      for h : i in [: args.size] do
        -- h.upper : i < args.size
        sz := sz + size (args.get ⟨i, h.upper⟩)
      return sz
  ```

* 添加 tactic `case'`。它与 `case` 类似，但在失败时不会自动承认目标。
  例如，当我们在 `first | ... | ...` 中需要使用 `case'`，并希望在 `case'` 失败时尝试下一个分支时，这个新 tactic 就很有用。

* 添加 tactic 宏
  ```lean
  macro "stop" s:tacticSeq : tactic => `(repeat sorry)
  ```
  参见 [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Partial.20evaluation.20of.20a.20file) 上的讨论。

* 显示目标时，如果不可访问的命题名没有前向依赖，我们就不再显示它们的名称，
但仍会显示它们的类型。
例如，目标
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
  h✝ : k < key
  a✝³ : BST left
  a✝² : ForallTree (fun k v => k < key) left
  a✝¹ : BST right
  a✝ : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```
  现在会显示为
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
   : k < key
   : BST left
   : ForallTree (fun k v => k < key) left
   : BST right
   : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```

* `by_cases` tactic 中的假设名现在是可选的。

* [修复 `syntax` 与 kind 名称之间的不一致](https://github.com/leanprover/lean4/issues/1090)。
  节点种类 `numLit`、`charLit`、`nameLit`、`strLit` 和 `scientificLit` 现在分别改名为
  `num`、`char`、`name`、`str` 与 `scientific`。例如，我们现在写作
  ```lean
  macro_rules | `($n:num) => `("hello")
  ```
  而不是
  ```lean
  macro_rules | `($n:numLit) => `("hello")
  ```

* （实验性）为大型交互式证明添加新的 `checkpoint <tactic-seq>` tactic。

* 将 tactic `nativeDecide` 重命名为 `native_decide`。

* 现在任何语法中都接受 antiquotation。因此，`incQuotDepth` `syntax` 解析器已经过时并被移除。

* 已将 tactic `nativeDecide` 重命名为 `native_decide`。

* 在精化 `match` 分支右侧之前，先“清理”局部上下文。例如：
  ```lean
  example (x : Nat) : Nat :=
    match g x with
    | (a, b) => _ -- Local context does not contain the auxiliary `_discr := g x` anymore

  example (x : Nat × Nat) (h : x.1 > 0) : f x > 0 := by
    match x with
    | (a, b) => _ -- Local context does not contain the `h✝ : x.fst > 0` anymore
  ```

* 改进 `let` 模式（以及 `have` 模式）的宏展开。在下面的例子中，
  ```lean
  example (x : Nat × Nat) : f x > 0 := by
    let (a, b) := x
    done
  ```
  生成的目标现在是 `... |- f (a, b) > 0`，而不是 `... |- f x > 0`。

* 添加交叉编译的 [aarch64 Linux](https://github.com/leanprover/lean4/pull/1066) 与 [aarch64 macOS](https://github.com/leanprover/lean4/pull/1076) 发布版本。

* [在文档中加入教程风格的示例](https://github.com/leanprover/lean4/tree/master/doc/examples)，使用 LeanInk+Alectryon 渲染。

````
