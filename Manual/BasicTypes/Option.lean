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

#doc (Manual) "可选值" =>
%%%
tag := "option"
%%%

:::::leanSection

```lean -show
variable {α : Type u} (v : α) {β : Type v}
```

{lean}`Option α` 是一种值的类型，它可以是某个 {lean}`some v`，其中 {lean}`v`﻿` : `﻿{lean}`α`；也可以是 {lean  (type := "Option α")}`none`。
在函数式编程中，此类型的使用方式类似于可空类型：{lean  (type := "Option α")}`none` 表示不存在值。
此外，从 {lean}`α` 到 {lean}`β` 的偏函数可以由类型 {lean}`α → Option β` 来表示，当该函数对某些输入未定义时，结果即为 {lean  (type := "Option β")}`none`。
在计算上，这些偏函数表示失败或错误的可能性，并且它们对应于可以提前终止但不抛出包含信息之异常的程序。

{lean}`Option` 也可以被认为类似于最多包含一个元素的列表。
从这个角度来看，遍历 {lean}`Option` 包括仅在存在值时才执行操作。
{lean}`Option` API 经常使用这种视角。

::::leanSection

:::example "作为可空性的 Option"

```imports -show
import Std
```

```lean -show
open Std (HashMap)
variable {Coll} [BEq α] [Hashable α] (a : α) (b : β) {xs : Coll} [GetElem Coll α β fun _ _ => True] {i : α} {m : HashMap α β}
```

函数 {name}`Std.HashMap.get?` 在指定的键 `a : α` 所属的 {lean}`HashMap α β` 中进行查找：

```signature
Std.HashMap.get?.{u, v} {α : Type u} {β : Type v}
  [BEq α] [Hashable α]
  (m : HashMap α β) (a : α) :
  Option β
```
因为无法事先知道该键是否确实在映射中，所以返回类型为 {lean}`Option β`，其中 {lean  (type := "Option β")}`none` 表示该键不在映射中，而 {lean}`some b` 表示找到了该键，并且 `b` 是检索到的值。

{lean}`xs[i]` 语法用于在有可用证明证明 {lean}`i` 是 {lean}`xs` 的有效索引时索引到集合中，它有一个变体 {lean}`xs[i]?`，该变体会根据给定索引是否有效来返回一个可选值。
如果 {lean}`m`﻿` : `﻿{lean}`HashMap α β` 并且 {lean}`a`﻿` : `﻿{lean}`α`，那么 {lean}`m[a]?` 等价于 {lean}`HashMap.get? m a`。

:::
::::

:::example "作为安全可空性的 Option"
在许多编程语言中，记住检查空值非常重要。
当使用 {name}`Option` 时，类型系统会在正确的地方要求进行这些检查：{lean}`Option α` 和 {lean}`α` 不是同一种类型，并且在它们之间进行转换需要处理 {lean  (type := "Option α")}`none` 的情况。
这可以通过诸如 {name}`Option.getD` 之类的辅助工具或使用模式匹配来完成。

```imports -show
import Std
```

```lean
def postalCodes : Std.HashMap Nat String :=
  Std.HashMap.emptyWithCapacity 1 |>.insert 12345 "Schenectady"
```

```lean (name := getD)
#eval postalCodes[12346]?.getD "not found"
```
```leanOutput getD
"not found"
```

```lean (name := m)
#eval
  match postalCodes[12346]? with
  | none => "not found"
  | some city => city
```
```leanOutput m
"not found"
```

```lean (name := iflet)
#eval
  if let some city := postalCodes[12345]? then
    city
  else
    "not found"
```
```leanOutput iflet
"Schenectady"
```

:::

:::::

{docstring Option}


# 强制转换

```lean -show
section
variable {α : Type u} (line : String)
```

从 {lean}`α` 到 {lean}`Option α` 存在一个{tech (key := "coercion")}[强制转换]，它会将值包装在 {lean}`some` 中。
这使得可以以类似于其他语言中可空类型的风格来使用 {name}`Option`，在这些语言中，缺失的值由 {name}`none` 指示，而存在的值没有特殊标记。

:::example "强制转换和 {name}`Option`"
在 {lean}`getAlpha` 中，读取了一行输入。
如果该行（在去掉开头和结尾的空格后）只由字母组成，则将其返回；否则，函数返回 {name}`none`。

```lean
def getAlpha : IO (Option String) := do
  let line := (← (← IO.getStdin).getLine).trim
  if line.length > 0 && line.all Char.isAlpha then
    return line
  else
    return none
```

在成功的情况下，没有显式地将 {name}`some` 包装在 {lean}`line` 周围。
{name}`some` 是由强制转换自动插入的。

:::

```lean -show
end
```


# API 参考

## 提取值

{docstring Option.get}

{docstring Option.get!}

{docstring Option.getD}

{docstring Option.getDM}

{docstring Option.getM}

{docstring Option.elim}

{docstring Option.elimM}

{docstring Option.merge}


## 属性和比较

{docstring Option.isNone}

{docstring Option.isSome}

{docstring Option.isEqSome}

:::leanSection
```lean -show
variable {α} [DecidableEq α] [LT α] [Min α] [Max α]
```
可选值的排序通常使用 {inst}`DecidableEq (Option α)`、{inst}`LT (Option α)`、{inst}`Min (Option α)` 和 {inst}`Max (Option α)` 实例。
:::

{docstring Option.min}

{docstring Option.max}

{docstring Option.lt}

{docstring Option.decidableEqNone}

## 转换

{docstring Option.toArray}

{docstring Option.toList}

{docstring Option.repr}

{docstring Option.format}

## 控制

{name}`Option` 可以被认为是描述一个可能无法返回值的计算。
{inst}`Monad Option` 实例以及 {inst}`Alternative Option` 正是基于这种理解。
返回 {name}`none` 也可以被认为是抛出了一个不包含任何有用信息的异常，这被体现在 {inst}`MonadExcept Unit Option` 实例中。

{docstring Option.guard}

{docstring Option.bind}

{docstring Option.bindM}

{docstring Option.join}

{docstring Option.sequence}

{docstring Option.tryCatch}

{docstring Option.or}

{docstring Option.orElse}


## 迭代

{name}`Option` 可以被认为是一个最多包含一个值的集合。
从这个角度来看，迭代运算符可以理解为对包含的值（如果存在）执行某些操作，如果不存在则什么也不做。

{docstring Option.all}

{docstring Option.any}

{docstring Option.filter}

{docstring Option.filterM}

{docstring Option.forM}

{docstring Option.map}

{docstring Option.mapA}

{docstring Option.mapM}

## 递归辅助

{docstring Option.attach}

{docstring Option.attachWith}

{docstring Option.unattach}

## 推理

{docstring Option.choice}

{docstring Option.pbind}

{docstring Option.pelim}

{docstring Option.pmap}
