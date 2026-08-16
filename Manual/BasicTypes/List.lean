/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.List.Predicates
import Manual.BasicTypes.List.Comparisons
import Manual.BasicTypes.List.Partitioning
import Manual.BasicTypes.List.Modification
import Manual.BasicTypes.List.Transformation

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "链表" =>
%%%
tag := "List"
%%%

链表由 {tech (key := "inductive type")}[归纳类型] {name}`List` 实现，包含一个有序的元素序列。
不同于 {ref "Array"}[数组]，Lean 会按照归纳类型的通常规则来编译列表；不过，借助 {attr}`csimp` 机制，某些列表操作在编译后的代码中会被替换为尾递归的等价实现。{TODO}[从此处继续撰写并添加交叉引用]
Lean 同时为列表字面量和构造子 {name}`List.cons` 提供了语法。

{docstring List}

# 语法
%%%
tag := "list-syntax"
%%%

列表字面量写在方括号中，列表元素以逗号分隔。
把元素添加到列表头部的构造子 {name}`List.cons` 用中缀运算符 {keywordOf «term_::_»}`::` 表示。
列表语法既可用于普通项，也可用于模式。

:::syntax term (title := "列表字面量")
```grammar
[$_,*]
```

{includeDocstring «term[_]»}

:::

:::syntax term (title := "列表构造")
```grammar
$_ :: $_
```

{includeDocstring «term_::_»}

:::

:::example "构造列表"
这些例子都彼此等价：
```lean
example : List Nat := [1, 2, 3]
example : List Nat := 1 :: [2, 3]
example : List Nat := 1 :: 2 :: [3]
example : List Nat := 1 :: 2 :: 3 :: []
example : List Nat := 1 :: 2 :: 3 :: .nil
example : List Nat := 1 :: 2 :: .cons 3 .nil
example : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
```
:::

:::example "模式匹配与列表"
这些函数都彼此等价：
```lean
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split' : List α → List α × List α
  | .nil => (.nil, .nil)
  | x :: [] => (.singleton x, .nil)
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split'' : List α → List α × List α
  | .nil => (.nil, .nil)
  | .cons x .nil => (.singleton x, .nil)
  | .cons x (.cons x' xs) =>
    let (ys, zs) := split xs
    (.cons x ys, .cons x' zs)
```
```lean -show
-- 验证上述说法
example : @split = @split' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split', List.singleton]

example : @split = @split'' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split'', List.singleton]
```
:::


# 性能说明
%%%
tag := "list-performance"
%%%

编译器不会覆盖或修改列表的表示：它们就是链表，每个元素都要经过一次指针间接访问。
计算列表长度需要完整遍历一次列表，而修改列表中的某个元素则需要遍历并重新分配该元素之前的前缀部分。
由于 Lean 使用基于引用计数的内存管理，像 {name}`List.map` 这样遍历列表、并为原列表中的每个元素分配一个新的 {name}`List.cons` 构造子的操作，在没有其他引用指向原列表时，可以复用原列表的内存。

由于列表在规约与说明中扮演着重要角色，大多数列表函数都尽可能直接地用结构递归编写。
这使得按归纳法编写证明更容易，但也意味着这些操作会消耗与列表长度成比例的栈空间。
许多列表函数都存在与其非尾递归版本等价的尾递归版本，但在推理时更难使用。
在编译后的代码中，尾递归版本会自动替代非尾递归版本。

# 接口参考
%%%
tag := "list-api-reference"
%%%

{include 2 Manual.BasicTypes.List.Predicates}

## 构造列表

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Constructing-Lists"
%%%
{docstring List.singleton}

{docstring List.concat}

{docstring List.replicate}

{docstring List.replicateTR}

{docstring List.ofFn}

{docstring List.append}

{docstring List.appendTR}

{docstring List.range}

{docstring List.range'}

{docstring List.range'TR}

{docstring List.finRange}

## 长度

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Length"
%%%
{docstring List.length}

{docstring List.lengthTR}

{docstring List.isEmpty}

## 头与尾

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Head-and-Tail"
%%%
{docstring List.head}

{docstring List.head?}

{docstring List.headD}

{docstring List.head!}

{docstring List.tail}

{docstring List.tail!}

{docstring List.tail?}

{docstring List.tailD}


## 查找

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Lookups"
%%%
{docstring List.get}

{docstring List.getD}

{docstring List.getLast}

{docstring List.getLast?}

{docstring List.getLastD}

{docstring List.getLast!}

{docstring List.lookup}

{docstring List.max?}

{docstring List.min?}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Queries"
%%%
{docstring List.count}

{docstring List.countP}

{docstring List.idxOf}

{docstring List.idxOf?}

{docstring List.finIdxOf?}

{docstring List.find?}

{docstring List.findFinIdx?}

{docstring List.findIdx}

{docstring List.findIdx?}

{docstring List.findM?}

{docstring List.findSome?}

{docstring List.findSomeM?}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Conversions"
%%%
{docstring List.toArray}

{docstring List.toArrayImpl}

{docstring List.toByteArray}

{docstring List.toFloatArray}

{docstring List.toString}


{include 2 Manual.BasicTypes.List.Modification}

## 排序

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Sorting"
%%%
{docstring List.mergeSort}

{docstring List.merge}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Iteration"
%%%
{docstring List.iter}

{docstring List.iterM}

{docstring List.forA}

{docstring List.forM}

{docstring List.firstM}

{docstring List.sum}

### 折叠

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Iteration--Folds"
%%%
:::paragraph
折叠是使用某个函数将列表元素组合起来的运算。
根据函数调用的嵌套方式，它们分为两类：

: {deftech (key := "Left folds")}[左折叠]

  左折叠从列表头开始向末尾依次组合元素。
  列表头会先与初始值组合，该结果再与下一个值组合，依此类推。

: {deftech (key := "Right folds")}[右折叠]

  右折叠从列表尾开始向开头组合元素，就像把每个 {name List.cons}`cons` 构造子替换成一次对组合函数的调用，并把 {name List.nil}`nil` 替换成初始值一样。

带 `-M` 后缀的单子折叠允许组合函数使用某个 {tech (key := "monad")}[单子] 中的效应，这也可能包括提前终止折叠。
:::

{docstring List.foldl}

{docstring List.foldlM}

{docstring List.foldlRecOn}

{docstring List.foldr}

{docstring List.foldrM}

{docstring List.foldrRecOn}

{docstring List.foldrTR}

{include 2 Manual.BasicTypes.List.Transformation}

## 过滤

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Filtering"
%%%
{docstring List.filter}

{docstring List.filterTR}

{docstring List.filterM}

{docstring List.filterRevM}

{docstring List.filterMap}

{docstring List.filterMapTR}

{docstring List.filterMapM}

{include Manual.BasicTypes.List.Partitioning}

## 元素判定

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Element-Predicates"
%%%
{docstring List.contains}

{docstring List.elem}

{docstring List.all}

{docstring List.allM}

{docstring List.any}

{docstring List.anyM}

{docstring List.and}

{docstring List.or}

{include 2 Manual.BasicTypes.List.Comparisons}

## 终止辅助

%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Termination-Helpers"
%%%
{docstring List.attach}

{docstring List.attachWith}

{docstring List.unattach}

{docstring List.pmap}
