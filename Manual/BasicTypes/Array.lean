/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 500000

example := Char

#doc (Manual) "数组" =>
%%%
tag := "Array"
%%%

{lean}`Array` 类型表示元素序列，可以通过其在序列中的位置进行访问。
Lean 对数组提供了专门支持：
 * 它有一个_逻辑模型_，用元素列表来规定其行为，从而给出各个数组操作的含义。
 * 它在编译后的代码中有一种经过优化的运行时表示，即 {tech (key := "dynamic arrays")}[动态数组]，Lean 运行时还会专门优化数组操作。
 * 可以使用 {ref "array-syntax"}[数组字面量语法] 来书写数组。

在编译后的代码中，数组可以比列表或其他序列高效得多。
这部分是因为它具有良好的局部性：序列中的所有元素都在内存中彼此相邻，因此处理器缓存可以被高效利用。
更重要的是，如果一个数组只有唯一引用，那么原本需要复制或分配数据结构的操作就可以通过原地修改来实现。
当 Lean 代码以始终只有唯一引用的方式使用数组时（也就是 {deftech (key := "linearly")}_线性地_ 使用它），便能避免持久化数据结构的性能开销，同时依旧像普通纯函数式程序一样易于编写、阅读与证明性质。

# 逻辑模型

{docstring Array}

数组的逻辑模型是一个只有单个字段的结构体，该字段是元素列表。
这使得在较低层次上规定和证明数组处理函数的性质时更加方便。

# 运行时表示
%%%
tag := "array-runtime"
%%%

Lean 的数组是 {deftech (key := "dynamic arrays")}_动态数组_：它们是一段具有既定容量的连续内存块，通常其中不会全部被占用。
只要数组中的元素个数小于容量，就可以在末尾追加新元素，而无需重新分配或移动数据。
向没有剩余空间的数组中添加元素时，会触发一次将容量翻倍的重新分配。
其摊还开销与数组大小呈线性关系。
数组中的值按 {ref "inductive-types-ffi"}[外部函数接口一节]所述的方式表示。

:::figure "数组的内存布局" (tag := "arrayffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean 对象头"),
  ("m_size", .size_t, twoLine "字节数" "size_t"),
  ("m_capacity", .size_t, twoLine "已分配空间" "size_t"),
  ("m_data", .data none, some <| .styledText (base := fieldLabelStyle) <|
    "数组数据" ++ "\n" ++ family "monospace" "lean_object *" ++ " 数组")
]
```
:::

在对象头之后，数组包含：

: 大小

  当前存储在数组中的对象个数

: 容量

  为数组分配的内存中可容纳的对象个数

: 数据

  数组中的值

Lean 运行时中的许多数组函数都会通过查看对象头中的引用计数，来检查自己是否独占其参数。
如果是，并且数组容量足够，那么就可以直接修改现有数组，而无需分配新的内存。
否则，就必须分配一个新数组。

## 性能说明
%%%
tag := "array-performance"
%%%


尽管 {name}`Array.mk` 和 {name}`Array.toList` 看起来只是普通的构造子与投影，但在编译后的代码中，它们都需要 *与数组大小成线性关系的时间*。
这是因为在链表与紧凑数组之间转换时，必然需要访问每一个元素。

可变数组可用于编写非常高效的代码。
不过，它们并不是好的持久化数据结构。
更新共享数组时无法使用原地修改，并且需要耗费与数组大小成线性关系的时间。
在性能关键的代码中使用数组时，务必确保它们是 {tech (key := "linearly")}[线性地] 使用的。

# 语法
%%%
tag := "array-syntax"
%%%

数组字面量允许直接在代码中书写数组。
它们既可用于表达式上下文，也可用于模式上下文。

:::syntax term (title := "数组字面量")
数组字面量以 `#[` 开始，包含一串以逗号分隔的项，并以 `]` 结束。

```grammar
#[$t,*]
```
:::

::::keepEnv
:::example "数组字面量"
数组字面量既可以用作表达式，也可以用作模式。

```lean
def oneTwoThree : Array Nat := #[1, 2, 3]

#eval
  match oneTwoThree with
  | #[x, y, z] => some ((x + z) / y)
  | _ => none
```
:::
::::

此外，还可以用下列语法提取 {ref "subarray"}[子数组]：
:::syntax term (title := "子数组")
起始下标后跟一个冒号，会构造出一个子数组，包含从起始下标开始（含该位置）直到末尾的值：
```grammar
$t[$t:term :]
```

同时提供起始与结束下标时，会构造出一个子数组，包含从起始下标（含）到结束下标（不含）的值：
```grammar
$t[$t:term : $_:term]
```
:::

::::keepEnv
:::example "子数组语法"

数组 {lean}`ten` 包含前十个自然数。
```lean
def ten : Array Nat :=
  .range 10
```

可以使用子数组语法构造一个表示 {lean}`ten` 后半部分的子数组：
```lean (name := subarr1)
#eval ten[5:]
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```

类似地，通过给出结束位置，可以构造出包含 2 到 5 的子数组：
```lean (name := subarr2)
#eval ten[2:6]
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```

由于子数组仅存储其在底层数组中所关注的起止下标，因此可以恢复出该数组本身：
```lean (name := subarr3)
#eval ten[2:6].array == ten
```
```leanOutput subarr3
true
```
:::
::::

# 接口参考
%%%
tag := "array-api"
%%%

## 构造数组

{docstring Array.empty}

{docstring Array.emptyWithCapacity}

{docstring Array.singleton}

{docstring Array.range}

{docstring Array.range'}

{docstring Array.finRange}

{docstring Array.ofFn}

{docstring Array.replicate}

{docstring Array.append}

{docstring Array.appendList}

{docstring Array.leftpad}

{docstring Array.rightpad}

## 大小

{docstring Array.size}

{docstring Array.usize}

{docstring Array.isEmpty}

## 查找

{docstring Array.extract}

{docstring Array.getD}

{docstring Array.uget}

{docstring Array.back}

{docstring Array.back?}

{docstring Array.back!}

{docstring Array.getMax?}

## 查询

{docstring Array.count}

{docstring Array.countP}

{docstring Array.idxOf}

{docstring Array.idxOf?}

{docstring Array.finIdxOf?}

## 转换

{docstring Array.toList}

{docstring Array.toListRev}

{docstring Array.toListAppend}

{docstring Array.toVector}

{docstring Array.toSubarray}

{docstring Array.ofSubarray}


## 修改

{docstring Array.push}

{docstring Array.pop}

{docstring Array.popWhile}

{docstring Array.erase}

{docstring Array.eraseP}

{docstring Array.eraseIdx}

{docstring Array.eraseIdx!}

{docstring Array.eraseIdxIfInBounds}

{docstring Array.eraseReps}

{docstring Array.swap}

{docstring Array.swapIfInBounds}

{docstring Array.swapAt}

{docstring Array.swapAt!}

{docstring Array.replace}

{docstring Array.set}

{docstring Array.set!}

{docstring Array.setIfInBounds}

{docstring Array.uset}

{docstring Array.modify}

{docstring Array.modifyM}

{docstring Array.modifyOp}

{docstring Array.insertIdx}

{docstring Array.insertIdx!}

{docstring Array.insertIdxIfInBounds}

{docstring Array.reverse}

{docstring Array.take}

{docstring Array.takeWhile}

{docstring Array.drop}

{docstring Array.shrink}

{docstring Array.flatten}

{docstring Array.getEvenElems}

## 有序数组

{docstring Array.qsort}

{docstring Array.qsortOrd}

{docstring Array.insertionSort}

{docstring Array.binInsert}

{docstring Array.binInsertM}

{docstring Array.binSearch}

{docstring Array.binSearchContains}



## 迭代

{docstring Array.iter}

{docstring Array.iterFromIdx}

{docstring Array.iterM}

{docstring Array.iterFromIdxM}

{docstring Array.foldr}

{docstring Array.foldrM}

{docstring Array.foldl}

{docstring Array.foldlM}

{docstring Array.forM}

{docstring Array.forRevM}

{docstring Array.firstM}

{docstring Array.sum}

## 变换

{docstring Array.map}

{docstring Array.mapMono}

{docstring Array.mapM}

{docstring Array.mapM'}

{docstring Array.mapMonoM}

{docstring Array.mapIdx}

{docstring Array.mapIdxM}

{docstring Array.mapFinIdx}

{docstring Array.mapFinIdxM}

{docstring Array.flatMap}

{docstring Array.flatMapM}

{docstring Array.zip}

{docstring Array.zipWith}

{docstring Array.zipWithAll}

{docstring Array.zipIdx}

{docstring Array.unzip}


## 过滤

{docstring Array.filter}

{docstring Array.filterM}

{docstring Array.filterRevM}

{docstring Array.filterMap}

{docstring Array.filterMapM}

{docstring Array.filterSepElems}

{docstring Array.filterSepElemsM}

## 分割

{docstring Array.partition}

{docstring Array.groupByKey}


## 元素判定

{docstring Array.contains}

{docstring Array.elem}

{docstring Array.find?}

{docstring Array.findRev?}

{docstring Array.findIdx}

{docstring Array.findIdx?}

{docstring Array.findIdxM?}

{docstring Array.findFinIdx?}

{docstring Array.findM?}

{docstring Array.findRevM?}

{docstring Array.findSome?}

{docstring Array.findSome!}

{docstring Array.findSomeM?}

{docstring Array.findSomeRev?}

{docstring Array.findSomeRevM?}

{docstring Array.all}

{docstring Array.allM}

{docstring Array.any}

{docstring Array.anyM}

{docstring Array.allDiff}

{docstring Array.isEqv}

## 比较

{docstring Array.isPrefixOf}

{docstring Array.lex}

## 终止辅助

{docstring Array.attach}

{docstring Array.attachWith}

{docstring Array.unattach}

{docstring Array.pmap}

{include 1 Manual.BasicTypes.Array.Subarray}

{include 0 Manual.BasicTypes.Array.FFI}
