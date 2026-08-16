/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "元组" =>
%%%
tag := "tuples"
%%%



:::paragraph
Lean 标准库包含多种类似元组的类型。
在实践中，它们有四个方面的差异：
 * 第一投影是类型还是命题
 * 第二投影是类型还是命题
 * 第二投影的类型是否依赖于第一投影的值
 * 整个类型本身是命题还是类型
:::

:::table +header
* + 类型
  + 第一投影
  + 第二投影
  + 依值？
  + 宇宙
* + {name}`Prod`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Type v`
  + ❌️
  + {lean (universes := "u v")}`Type (max u v)`
* + {name}`And`
  + {lean (universes := "u v")}`Prop`
  + {lean (universes := "u v")}`Prop`
  + ❌️
  + {lean (universes := "u v")}`Prop`
* + {name}`Sigma`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Type v`
  + ✔
  + {lean (universes := "u v")}`Type (max u v)`
* + {name}`Subtype`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Prop`
  + ✔
  + {lean (universes := "u v")}`Type u`
* + {name}`Exists`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Prop`
  + ✔
  + {lean (universes := "u v")}`Prop`
:::

:::paragraph
该表中的某些潜在行在库里并不存在：

 * 不存在“第一投影是命题”的依值有序对，因为 {tech (key := "proof irrelevance")}[证明无关性] 会让它失去意义。

 * 不存在把类型与命题组合起来的非依值有序对，因为这种情况在实践中很少见：把数据与_无关的_证明放在一起并不常见。
:::

这些差异会带来非常不同的使用场景。
{name}`Prod` 及其变体 {name}`PProd` 与 {name}`MProd` 只是把数据放在一起——它们是积。
由于第二投影依值，{name}`Sigma` 具有和的特征：对于第一投影类型中的每个元素，第二投影都可能对应不同的类型。
{name}`Subtype` 选出某个类型中满足给定谓词的值。
尽管它在语法上像一个有序对，但在实践中它被当作真正的子集。
{name}`And` 是逻辑联结词，而 {name}`Exists` 是量词。
本章记录的是这些类似元组的有序对，也就是 {name}`Prod` 与 {name}`Sigma`。

# 有序对
%%%
tag := "pairs"
%%%

```lean -show
section
variable {α : Type u} {β : Type v} {γ : Type w} {x : α} {y : β} {z : γ}
```

类型 {lean}`α × β` 是 {lean}`Prod α β` 的一种 {tech (key := "notation")}[记法]，它包含有序对：第一个元素属于 {lean}`α`，第二个元素属于 {lean}`β`。
这些有序对写在圆括号中，并以逗号分隔。
更大的元组表示为嵌套元组，因此 {lean}`α × β × γ` 等价于 {lean}`α × (β × γ)`，而 {lean}`(x, y, z)` 等价于 {lean}`(x, (y, z))`。

:::syntax term (title := "积类型")
```grammar
$_ × $_
```
积 {lean}`Prod α β` 写作 {lean}`α × β`。
:::

:::syntax term (title := "有序对")
```grammar
($_, $_)
```
:::

{docstring Prod}

```lean -show
section
variable {α : Sort u} {β : Sort v} {γ : Type w}
```

还存在变体 {lean}`α ×' β`（它是 {lean}`PProd α β` 的记法）以及 {lean}`MProd`，它们在 {tech (key := "universe")}[宇宙] 层级方面有所不同：与 {name}`PSum` 类似，{name}`PProd` 允许 {lean}`α` 或 {lean}`β` 之一是命题，而 {lean}`MProd` 要求二者都是位于_同一_宇宙层级的类型。
一般来说，{name}`PProd` 主要用于证明自动化和精译器的实现，因为它往往会引发无法解决的宇宙层级合一问题。
另一方面，{lean}`MProd` 在某些高级用例中可以简化宇宙层级问题。

```lean -show
end
```

:::syntax term (title := "任意 Sort 的积")
```grammar
$_ ×' $_
```
积 {lean}`PProd α β`（其中两个参数都可以是命题）写作 {lean}`α × β`。
:::


{docstring PProd}

{docstring MProd}

## 接口参考
%%%
tag := "prod-api"
%%%

作为单纯的有序对，{lean}`Prod` 的主要 API 由模式匹配以及第一、第二投影 {name}`Prod.fst` 和 {name}`Prod.snd` 提供。

### 变换

%%%
tag := "Lean-__________________--Basic-Types--Tuples--Ordered-Pairs--API-Reference--Transformation"
%%%
{docstring Prod.map}

{docstring Prod.swap}

### 自然数范围

%%%
tag := "Lean-__________________--Basic-Types--Tuples--Ordered-Pairs--API-Reference--Natural-Number-Ranges"
%%%
{docstring Prod.allI}

{docstring Prod.anyI}

{docstring Prod.foldI}

### 排序

%%%
tag := "Lean-__________________--Basic-Types--Tuples--Ordered-Pairs--API-Reference--Ordering"
%%%
{docstring Prod.lexLt}


# 依值有序对
%%%
tag := "sigma-types"
%%%


{deftech (key := "Dependent pairs")}_依值有序对_ 也称为 {deftech (key := "dependent sums")}_依值和_ 或 {deftech (key := "Σ-types")}_Σ-类型_，{see "Σ-types"}[Sigma 类型]{index}[Σ-types] 是这样一种有序对：第二个项的类型可以依赖于第一个项的_值_。
它与存在量词{TODO}[xref]以及 {name}`Subtype` 关系密切。
不同于存在量化语句，依值有序对位于 {lean}`Type` 宇宙中，是与计算相关的数据。
不同于子类型，这里的第二个项也同样是与计算相关的数据。
与普通有序对一样，依值有序对也可以嵌套；这种嵌套是右结合的。

:::syntax term (title := "依值有序对类型")

```grammar
($x:ident : $t) × $t
```

```grammar
Σ $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
Σ ($x:ident $[$x:ident]* : $t), $_
```

依值有序对类型会绑定一个或多个变量，最终项中可以使用这些变量。
若只绑定一个变量，则它的类型就是有序对第一个元素的类型，而最终项则是第二个元素的类型。
若绑定多个变量，则类型会按右结合方式嵌套。
标识符也可以写成 `_`。
带括号的写法允许多个被绑定变量具有不同类型，而不带括号的写法要求它们都具有相同类型。
:::

::::example "嵌套的依值有序对类型"

:::paragraph
类型
```leanTerm
Σ n k : Nat, Fin (n * k)
```
等价于
```leanTerm
Σ n : Nat, Σ k : Nat, Fin (n * k)
```
以及
```leanTerm
(n : Nat) × (k : Nat) × Fin (n * k)
```
:::

:::paragraph
类型
```leanTerm
Σ (n k : Nat) (i : Fin (n * k)) , Fin i.val
```
等价于
```leanTerm
Σ (n : Nat), Σ (k : Nat), Σ (i : Fin (n * k)) , Fin i.val
```
以及
```leanTerm
(n : Nat) × (k : Nat) × (i : Fin (n * k)) × Fin i.val
```
:::

这两种标注风格不能在同一个 {keywordOf «termΣ_,_»}`Σ` 类型中混用：
```syntaxError mixedNesting (category := term)
Σ n k (i : Fin (n * k)) , Fin i.val
```
```leanOutput mixedNesting
<example>:1:5-1:7: unexpected token '('; expected ','
```
::::

```lean -show
section
variable {α : Type} (x : α)
```
::::paragraph
依值有序对通常有两种用法：

 1. 它们可用于把某个具体的类型索引与该索引族中的值“打包”在一起，适用于事先不知道索引值的情况。
    类型 {lean}`Σ n, Fin n` 就是一对值：一个自然数，以及另一个严格小于它的数。
    这是依值有序对最常见的用法。

 2. :::paragraph
    第一个元素可以看作一个“标签”，用于在不同类型之间选择第二个项的类型。
    这类似于和类型中选择某个构造子时，会同时决定该构造子参数的类型。
    例如，类型

    ```leanTerm
    Σ (b : Bool), if b then Unit else α
    ```

    等价于 {lean}`Option α`；其中 {lean  (type := "Option α")}`none` 对应 {lean  (type := "Σ (b : Bool), if b then Unit else α")}`⟨true, ()⟩`，而 {lean  (type := "Option α")}`some x` 对应 {lean  (type := "Σ (b : Bool), if b then Unit else α")}`⟨false, x⟩`。
    这种用法并不常见，因为通常直接定义一个专用的 {tech (key := "inductive type")}[归纳类型] 会更容易。
    :::
::::

```lean -show
end
```

{docstring Sigma}

:::::example "带数据的依值有序对"

::::ioExample
类型 {name}`Vector` 会把一个已知长度与数组关联起来，它可以与该长度本身一起放入依值有序对中。
尽管从逻辑上说，这与直接使用 {name}`Array` 等价，但为了弥补 API 之间的衔接空缺，这种构造有时是必要的。

```ioLean
def getNLinesRev : (n : Nat) → IO (Vector String n)
  | 0 => pure #v[]
  | n + 1 => do
    let xs ← getNLinesRev n
    return xs.push (← (← IO.getStdin).getLine)

def getNLines (n : Nat) : IO (Vector String n) := do
  return (← getNLinesRev n).reverse

partial def getValues : IO (Σ n, Vector String n) := do
  let stdin ← IO.getStdin

  IO.println "How many lines to read?"
  let howMany ← stdin.getLine

  if let some howMany := howMany.trimAscii.copy.toNat? then
    return ⟨howMany, (← getNLines howMany)⟩
  else
    IO.eprintln "Please enter a number."
    getValues

def main : IO Unit := do
  let values ← getValues
  IO.println s!"Got {values.fst} values. They are:"
  for x in values.snd do
    IO.println x.trimAscii
```
:::paragraph
向该程序提供如下标准输入时：
```stdin
4
Apples
Quince
Plums
Raspberries
```
输出为：
```stdout
How many lines to read?
Got 4 values. They are:
Raspberries
Plums
Quince
Apples
```
:::
::::

:::::

:::example "把依值有序对当作和类型"
{name}`Sigma` 可用于实现和类型。
第一投影中的 {name}`Bool` 指示 {name}`Sum'` 的第二投影值来自哪个类型。
```lean
def Sum' (α : Type) (β : Type) : Type :=
  Σ (b : Bool),
    match b with
    | true => α
    | false => β
```

两个注入构造子都会把一个标签（即 {name}`Bool`）与指定类型的值配对。
为它们加上 {attr}`match_pattern` 标注后，它们既可用于普通项，也可用于模式。
```lean
variable {α β : Type}

@[match_pattern]
def Sum'.inl (x : α) : Sum' α β := ⟨true, x⟩

@[match_pattern]
def Sum'.inr (x : β) : Sum' α β := ⟨false, x⟩

def Sum'.swap : Sum' α β → Sum' β α
  | .inl x => .inr x
  | .inr y => .inl y
```
:::


正如 {name}`Prod` 有允许命题与类型一并出现的变体 {name}`PProd` 一样，{name}`PSigma` 也允许其投影是命题。
它与 {name}`PProd` 有相同的缺点：更容易导致宇宙层级合一失败。
不过，在实现自定义证明自动化，或某些罕见的高级用例中，{name}`PSigma` 可能是必要的。

:::syntax term (title := "全多态依值有序对类型")

```grammar
Σ' $x:ident $[$_:ident]* $[: $t]? , $_
```

```grammar
Σ' ($x:ident $[$x:ident]* : $t), $_
```

{keyword}`Σ'` 的嵌套规则以及其绑定结构规则，都与 {keywordOf «termΣ_,_»}`Σ` 相同。
:::

{docstring PSigma}
