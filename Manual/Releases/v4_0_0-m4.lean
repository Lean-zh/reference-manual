/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0-m4 (2022-03-27)" =>
%%%
tag := "release-v4.0.0-m4"
file := "v4.0.0-m4"
%%%

````markdown
这是 Lean 4 的第四个里程碑版本。它包含许多改进和许多新特性。
自上一个里程碑以来，我们已有 600 多次提交。

贡献者：

```
$ git shortlog -s -n v4.0.0-m3..v4.0.0-m4
   501  Leonardo de Moura
    65  Sebastian Ullrich
    11  Daniel Fabian
    10  larsk21
     5  Gabriel Ebner
     2  E.W.Ayers
     2  Jonathan Coates
     2  Joscha
     2  Mario Carneiro
     2  ammkrn
     1  Chris Lovett
     1  François G. Dorais
     1  Jakob von Raumer
     1  Lars
     1  Patrick Stevens
     1  Wojciech Nawrocki
     1  Xubai Wang
     1  casavaca
     1  zygi
```

* `simp` 现在接受用户自定义的 simp 属性。你可以创建一个文件（例如 `MySimp.lean`），其中包含如下内容，以定义新的 `simp` 属性
  ```lean
  import Lean
  open Lean.Meta

  initialize my_ext : SimpExtension ← registerSimpAttr `my_simp "my own simp attribute"
  ```
  如果你不需要访问 `my_ext`，也可以使用如下宏
  ```lean
  import Lean

  register_simp_attr my_simp "my own simp attribute"
  ```
  请注意，新的 `simp` 属性在定义它的那个 Lean 文件中并不会启用。
  下面是一个使用这一新特性的小例子。
  ```lean
  import MySimp

  def f (x : Nat) := x + 2
  def g (x : Nat) := x + 1

  @[my_simp] theorem f_eq : f x = x + 2 := rfl
  @[my_simp] theorem g_eq : g x = x + 1 := rfl

  example : f x + g x = 2*x + 3 := by
    simp_arith [my_simp]
  ```

* 扩展 `match` 语法：单个分支中可以有多个左侧模式。例如：
  ```lean
  def fib : Nat → Nat
  | 0 | 1 => 1
  | n+2 => fib n + fib (n+1)
  ```
  这一特性曾在 [issue 371](https://github.com/leanprover/lean4/issues/371) 中讨论。它通过宏展开实现，因此下面这样的写法现在会被接受。
  ```lean
  inductive StrOrNum where
    | S (s : String)
    | I (i : Int)

  def StrOrNum.asString (x : StrOrNum) :=
    match x with
    | I a | S a => toString a
  ```


* 改进 `#eval` 命令。现在，当它无法为结果类型合成 `Lean.MetaEval` 实例时，会先对类型做归约再重试。下面的例子现在无需额外注解即可工作
  ```lean
  def Foo := List Nat

  def test (x : Nat) : Foo :=
    [x, x+1, x+2]

  #eval test 4
  ```

* `rw` tactic 现在可以对给定定义应用自动生成的等式定理。例如：
  ```lean
  example (a : Nat) (h : n = 1) : [a].length = n := by
    rw [List.length]
    trace_state -- .. |- [].length + 1 = n
    rw [List.length]
    trace_state -- .. |- 0 + 1 = n
    rw [h]
  ```

* [自动补全的模糊匹配](https://github.com/leanprover/lean4/pull/1023)

* 将点记法 `x.field` 扩展到箭头类型。如果 `x` 的类型是箭头类型，我们会查找 `Function.field`。
例如，给定 `f : Nat → Nat` 和 `g : Nat → Nat`，`f.comp g` 现在表示 `Function.comp f g`。

* 新的 `.<identifier>` 记法现在也可用于期望函数类型的位置。
  ```lean
  example (xs : List Nat) : List Nat := .map .succ xs
  example (xs : List α) : Std.RBTree α ord := xs.foldl .insert ∅
  ```

* [为语言服务器添加代码折叠支持](https://github.com/leanprover/lean4/pull/1014)。

* 在 `do` 块中支持记法 `let <pattern> := <expr> | <else-case>`。

* 移除对“自动” `pure` 的支持。在这条 [Zulip 讨论串](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/for.2C.20unexpected.20need.20for.20type.20ascription/near/269083574)中，大家的共识似乎是“自动” `pure` 带来的困惑大于价值。

* 移除 `congr` 定理中“左侧所有函数参数都必须是自由变量”的限制。例如，下面的定理现在是合法的 `congr` 定理。
  ```lean
  @[congr]
  theorem dep_congr [DecidableEq ι] {p : ι → Set α} [∀ i, Inhabited (p i)] :
                    ∀ {i j} (h : i = j) (x : p i) (y : α) (hx : x = y), Pi.single (f := (p ·)) i x = Pi.single (f := (p ·)) j ⟨y, hx ▸ h ▸ x.2⟩ :=
  ```

* [部分应用的 congruence 定理。](https://github.com/leanprover/lean4/issues/988)

* 在期望类型是元变量时，改进精化延后启发式。Lean 现在会先归约期望类型，再执行测试。

* [移除已弃用的 leanpkg](https://github.com/leanprover/lean4/pull/985)，改用现已随 Lean 一起提供的 [Lake](https://github.com/leanprover/lake)。

* 对“跳转到定义”和“查找所有引用”的准确性做了多项改进。

* 自动生成的 congruence lemma 现已支持对证明和 `Decidable` 实例进行 cast（见 [wishlist](https://github.com/leanprover/lean4/issues/988)）。

* 将选项 `autoBoundImplicitLocal` 重命名为 `autoImplicit`。

* [放宽 auto-implicit 限制](https://github.com/leanprover/lean4/pull/1011)。命令 `set_option relaxedAutoImplicit false` 可关闭这些放宽规则。

* 如果目标中存在 `False.elim` 应用，`contradiction` tactic 现在会直接关闭该目标。

* 将 tactic `byCases` 重命名为 `by_cases`（动机：统一命名约定）。

* 模式中出现的局部实例现在会被类型类解析过程纳入考虑。例如：
  ```lean
  def concat : List ((α : Type) × ToString α × α) → String
    | [] => ""
    | ⟨_, _, a⟩ :: as => toString a ++ concat as
  ```

* 为 `match` 表达式提供 motive 的记法已更改。
  之前：
  ```lean
  match x, rfl : (y : Nat) → x = y → Nat with
  | 0,   h => ...
  | x+1, h => ...
  ```
  现在：
  ```lean
  match (motive := (y : Nat) → x = y → Nat) x, rfl with
  | 0,   h => ...
  | x+1, h => ...
  ```
  有了这一变化，在 `match` 表达式中为等式证明命名的记法不再对空白敏感。也就是说，
  现在可以写成
  ```lean
  match h : sort.swap a b with
  | (r₁, r₂) => ... -- `h : sort.swap a b = (r₁, r₂)`
  ```

* 即使期望类型不是命题，`match` 表达式的默认行为现在也是 `(generalizing := true)`。在下面的例子中，过去我们必须手动写出 `(generalizing := true)`。
  ```lean
  inductive Fam : Type → Type 1 where
    | any : Fam α
    | nat : Nat → Fam Nat

  example (a : α) (x : Fam α) : α :=
    match x with
    | Fam.any   => a
    | Fam.nat n => n
  ```

* 现在，在使用良基递归编译互递归定义时，我们使用 `PSum`（而不是 `Sum`）。

* 更好地支持参数化的良基关系。参见 [issue #1017](https://github.com/leanprover/lean4/issues/1017)。这一变化会影响底层 `termination_by'` 提示，因为在构造良基关系类型时，函数参数的固定前缀不再被“打包”。例如，在下面的定义中，`as` 是固定前缀的一部分，因此不会再被打包。此前版本中，`termination_by'` 项会写作 `measure fun ⟨as, i, _⟩ => as.size - i`
  ```lean
  def sum (as : Array Nat) (i : Nat) (s : Nat) : Nat :=
    if h : i < as.size then
      sum as (i+1) (s + as.get ⟨i, h⟩)
    else
      s
  termination_by' measure fun ⟨i, _⟩ => as.size - i
  ```

* 为 `do` 块添加 `while <cond> do <do-block>`、`repeat <do-block>` 和 `repeat <do-block> until <cond>` 宏。这些宏基于 `partial` 定义，因此只适合用于编写那些我们并不打算证明其性质的程序。

* 为 `Simp.Config` 添加 `arith` 选项，宏 `simp_arith` 会展开为 `simp (config := { arith := true })`。目前仅支持 `Nat` 和线性算术。例如：
  ```lean
  example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
    simp_arith
  ```

* 添加 `fail <string>?` tactic，它总是失败。

* 在依赖消去中添加对无环性的支持。参见 [issue #1022](https://github.com/leanprover/lean4/issues/1022)。

* 添加 `trace <string>` tactic，用于调试。

* 为 `Unit → α` 类型添加非平凡的 `SizeOf` 实例，并让用户自定义归纳类型自动生成的 `SizeOf` 实例也支持它们。例如，给定归纳数据类型
  ```lean
  inductive LazyList (α : Type u) where
    | nil                               : LazyList α
    | cons (hd : α) (tl : LazyList α)   : LazyList α
    | delayed (t : Thunk (LazyList α))  : LazyList α
  ```
  我们现在得到的是 `sizeOf (LazyList.delayed t) = 1 + sizeOf t`，而不再是 `sizeOf (LazyList.delayed t) = 2`。

* 在证明终止性时，添加对猜测（非常）简单良基关系的支持。例如，下面的函数不再需要 `termination_by` 注解。
  ```lean
  def Array.insertAtAux (i : Nat) (as : Array α) (j : Nat) : Array α :=
    if h : i < j then
      let as := as.swap! (j-1) j;
      insertAtAux i as (j-1)
    else
      as
  ```

* 添加对 `for h : x in xs do ...` 记法的支持，其中 `h : x ∈ xs`。这主要对证明终止性有用。

* 归纳族的 auto implicit 行为已更改。出现在归纳族索引中的 auto implicit 参数，如非固定（见下一条），也会被视为索引。例如
  ```lean
  inductive HasType : Index n → Vector Ty n → Ty → Type where
  ```
  现在会被解释为
  ```lean
  inductive HasType : {n : Nat} → Index n → Vector Ty n → Ty → Type where
  ```

* 为了让前一条特性更便于使用，我们会将归纳族索引中的固定前缀提升为参数。例如，Lean 现在接受下面的声明
  ```lean
  inductive Lst : Type u → Type u
    | nil  : Lst α
    | cons : α → Lst α → Lst α
  ```
  其中 `Lst α` 里的 `α` 是参数。实际参数个数可用命令 `#print Lst` 查看。该特性也确保我们仍然接受如下声明
  ```lean
  inductive Sublist : List α → List α → Prop
    | slnil : Sublist [] []
    | cons l₁ l₂ a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
    | cons2 l₁ l₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)
  ```

* 添加 auto implicit 的“链式传播”。出现在 auto implicit 类型中的未赋值元变量现在会变成新的 auto implicit 局部变量。考虑下面的例子：
  ```lean
  inductive HasType : Fin n → Vector Ty n → Ty → Type where
    | stop : HasType 0 (ty :: ctx) ty
    | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```
  `ctx` 在这两个构造子中都是 auto implicit 局部变量，其类型为 `ctx : Vector Ty ?m`。若没有 auto implicit 的“链式传播”，元变量 `?m` 会保持未赋值。新特性会再创建一个隐式局部变量 `n : Nat`，并将 `n` 赋给 `?m`。因此，上面的声明实际上是下面这一写法的简写
  ```lean
  inductive HasType : {n : Nat} → Fin n → Vector Ty n → Ty → Type where
    | stop : {ty : Ty} → {n : Nat} → {ctx : Vector Ty n} → HasType 0 (ty :: ctx) ty
    | pop  : {n : Nat} → {k : Fin n} → {ctx : Vector Ty n} → {ty : Ty} → HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```

* 从 recursor 的次要前提与投影声明中移除辅助类型注解（例如 `autoParam` 与 `optParam`）。考虑下面的例子
  ```lean
  structure A :=
    x : Nat
    h : x = 1 := by trivial

  example (a : A) : a.x = 1 := by
    have aux := a.h
    -- `aux` has now type `a.x = 1` instead of `autoParam (a.x = 1) auto✝`
    exact aux

  example (a : A) : a.x = 1 := by
    cases a with
    | mk x h =>
      -- `h` has now type `x = 1` instead of `autoParam (x = 1) auto✝`
      assumption
  ```

* 我们现在接受模式中的重载记法，但要求每个分支中的模式变量集合相同。例如：
  ```lean
  inductive Vector (α : Type u) : Nat → Type u
    | nil : Vector α 0
    | cons : α → Vector α n → Vector α (n+1)

  infix:67 " :: " => Vector.cons -- Overloading the `::` notation

  def head1 (x : List α) (h : x ≠ []) : α :=
    match x with
    | a :: as => a -- `::` is `List.cons` here

  def head2 (x : Vector α (n+1)) : α :=
    match x with
    | a :: as => a -- `::` is `Vector.cons` here
  ```

* 新增借鉴自 Swift 的 `.<identifier>` 记法。命名空间会从期望类型中推断。参见 [issue #944](https://github.com/leanprover/lean4/issues/944)。例如：
  ```lean
  def f (x : Nat) : Except String Nat :=
    if x > 0 then
      .ok x
    else
      .error "x is zero"

  namespace Lean.Elab
  open Lsp

  def identOf : Info → Option (RefIdent × Bool)
    | .ofTermInfo ti => match ti.expr with
      | .const n .. => some (.const n, ti.isBinder)
      | .fvar id .. => some (.fvar id, ti.isBinder)
      | _ => none
    | .ofFieldInfo fi => some (.const fi.projName, false)
    | _ => none

  def isImplicit (bi : BinderInfo) : Bool :=
    bi matches .implicit

  end Lean.Elab
  ```
````
