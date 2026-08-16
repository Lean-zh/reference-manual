/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G3

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
file := "Arrays"
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

%%%
tag := "Lean-__________________--Basic-Types--Arrays--Logical-Model"
%%%
{zhdocstring Array Manual.ZhDocString.Ch19Ch20.G3.c001}

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

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Constructing-Arrays"
%%%
{zhdocstring Array.empty Manual.ZhDocString.Ch19Ch20.G3.c002}

{zhdocstring Array.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G3.c003}

{zhdocstring Array.singleton Manual.ZhDocString.Ch19Ch20.G3.c004}

{zhdocstring Array.range Manual.ZhDocString.Ch19Ch20.G3.c005}

{zhdocstring Array.range' Manual.ZhDocString.Ch19Ch20.G3.c006}

{zhdocstring Array.finRange Manual.ZhDocString.Ch19Ch20.G3.c007}

{zhdocstring Array.ofFn Manual.ZhDocString.Ch19Ch20.G3.c008}

{zhdocstring Array.replicate Manual.ZhDocString.Ch19Ch20.G3.c009}

{zhdocstring Array.append Manual.ZhDocString.Ch19Ch20.G3.c010}

{zhdocstring Array.appendList Manual.ZhDocString.Ch19Ch20.G3.c011}

{zhdocstring Array.leftpad Manual.ZhDocString.Ch19Ch20.G3.c012}

{zhdocstring Array.rightpad Manual.ZhDocString.Ch19Ch20.G3.c013}

## 大小

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Size"
%%%
{zhdocstring Array.size Manual.ZhDocString.Ch19Ch20.G3.c014}

{zhdocstring Array.usize Manual.ZhDocString.Ch19Ch20.G3.c015}

{zhdocstring Array.isEmpty Manual.ZhDocString.Ch19Ch20.G3.c016}

## 查找

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Lookups"
%%%
{zhdocstring Array.extract Manual.ZhDocString.Ch19Ch20.G3.c017}

{zhdocstring Array.getD Manual.ZhDocString.Ch19Ch20.G3.c018}

{zhdocstring Array.uget Manual.ZhDocString.Ch19Ch20.G3.c019}

{zhdocstring Array.back Manual.ZhDocString.Ch19Ch20.G3.c020}

{zhdocstring Array.back? Manual.ZhDocString.Ch19Ch20.G3.c021}

{zhdocstring Array.back! Manual.ZhDocString.Ch19Ch20.G3.c022}

{zhdocstring Array.getMax? Manual.ZhDocString.Ch19Ch20.G3.c023}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Queries"
%%%
{zhdocstring Array.count Manual.ZhDocString.Ch19Ch20.G3.c024}

{zhdocstring Array.countP Manual.ZhDocString.Ch19Ch20.G3.c025}

{zhdocstring Array.idxOf Manual.ZhDocString.Ch19Ch20.G3.c026}

{zhdocstring Array.idxOf? Manual.ZhDocString.Ch19Ch20.G3.c027}

{zhdocstring Array.finIdxOf? Manual.ZhDocString.Ch19Ch20.G3.c028}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Conversions"
%%%
{zhdocstring Array.toList Manual.ZhDocString.Ch19Ch20.G3.c029}

{zhdocstring Array.toListRev Manual.ZhDocString.Ch19Ch20.G3.c030}

{zhdocstring Array.toListAppend Manual.ZhDocString.Ch19Ch20.G3.c031}

{zhdocstring Array.toVector Manual.ZhDocString.Ch19Ch20.G3.c032}

{zhdocstring Array.toSubarray Manual.ZhDocString.Ch19Ch20.G3.c033}

{zhdocstring Array.ofSubarray Manual.ZhDocString.Ch19Ch20.G3.c034}


## 修改

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Modification"
%%%
{zhdocstring Array.push Manual.ZhDocString.Ch19Ch20.G3.c035}

{zhdocstring Array.pop Manual.ZhDocString.Ch19Ch20.G3.c036}

{zhdocstring Array.popWhile Manual.ZhDocString.Ch19Ch20.G3.c037}

{zhdocstring Array.erase Manual.ZhDocString.Ch19Ch20.G3.c038}

{zhdocstring Array.eraseP Manual.ZhDocString.Ch19Ch20.G3.c039}

{zhdocstring Array.eraseIdx Manual.ZhDocString.Ch19Ch20.G3.c040}

{zhdocstring Array.eraseIdx! Manual.ZhDocString.Ch19Ch20.G3.c041}

{zhdocstring Array.eraseIdxIfInBounds Manual.ZhDocString.Ch19Ch20.G3.c042}

{zhdocstring Array.eraseReps Manual.ZhDocString.Ch19Ch20.G3.c043}

{zhdocstring Array.swap Manual.ZhDocString.Ch19Ch20.G3.c044}

{zhdocstring Array.swapIfInBounds Manual.ZhDocString.Ch19Ch20.G3.c045}

{zhdocstring Array.swapAt Manual.ZhDocString.Ch19Ch20.G3.c046}

{zhdocstring Array.swapAt! Manual.ZhDocString.Ch19Ch20.G3.c047}

{zhdocstring Array.replace Manual.ZhDocString.Ch19Ch20.G3.c048}

{zhdocstring Array.set Manual.ZhDocString.Ch19Ch20.G3.c049}

{zhdocstring Array.set! Manual.ZhDocString.Ch19Ch20.G3.c050}

{zhdocstring Array.setIfInBounds Manual.ZhDocString.Ch19Ch20.G3.c051}

{zhdocstring Array.uset Manual.ZhDocString.Ch19Ch20.G3.c052}

{zhdocstring Array.modify Manual.ZhDocString.Ch19Ch20.G3.c053}

{zhdocstring Array.modifyM Manual.ZhDocString.Ch19Ch20.G3.c054}

{zhdocstring Array.modifyOp Manual.ZhDocString.Ch19Ch20.G3.c055}

{zhdocstring Array.insertIdx Manual.ZhDocString.Ch19Ch20.G3.c056}

{zhdocstring Array.insertIdx! Manual.ZhDocString.Ch19Ch20.G3.c057}

{zhdocstring Array.insertIdxIfInBounds Manual.ZhDocString.Ch19Ch20.G3.c058}

{zhdocstring Array.reverse Manual.ZhDocString.Ch19Ch20.G3.c059}

{zhdocstring Array.take Manual.ZhDocString.Ch19Ch20.G3.c060}

{zhdocstring Array.takeWhile Manual.ZhDocString.Ch19Ch20.G3.c061}

{zhdocstring Array.drop Manual.ZhDocString.Ch19Ch20.G3.c062}

{zhdocstring Array.shrink Manual.ZhDocString.Ch19Ch20.G3.c063}

{zhdocstring Array.flatten Manual.ZhDocString.Ch19Ch20.G3.c064}

{zhdocstring Array.getEvenElems Manual.ZhDocString.Ch19Ch20.G3.c065}

## 有序数组

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Sorted-Arrays"
%%%
{zhdocstring Array.qsort Manual.ZhDocString.Ch19Ch20.G3.c066}

{zhdocstring Array.qsortOrd Manual.ZhDocString.Ch19Ch20.G3.c067}

{zhdocstring Array.insertionSort Manual.ZhDocString.Ch19Ch20.G3.c068}

{zhdocstring Array.binInsert Manual.ZhDocString.Ch19Ch20.G3.c069}

{zhdocstring Array.binInsertM Manual.ZhDocString.Ch19Ch20.G3.c070}

{zhdocstring Array.binSearch Manual.ZhDocString.Ch19Ch20.G3.c071}

{zhdocstring Array.binSearchContains Manual.ZhDocString.Ch19Ch20.G3.c072}



## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Iteration"
%%%
{zhdocstring Array.iter Manual.ZhDocString.Ch19Ch20.G3.c073}

{zhdocstring Array.iterFromIdx Manual.ZhDocString.Ch19Ch20.G3.c074}

{zhdocstring Array.iterM Manual.ZhDocString.Ch19Ch20.G3.c075}

{zhdocstring Array.iterFromIdxM Manual.ZhDocString.Ch19Ch20.G3.c076}

{zhdocstring Array.foldr Manual.ZhDocString.Ch19Ch20.G3.c077}

{zhdocstring Array.foldrM Manual.ZhDocString.Ch19Ch20.G3.c078}

{zhdocstring Array.foldl Manual.ZhDocString.Ch19Ch20.G3.c079}

{zhdocstring Array.foldlM Manual.ZhDocString.Ch19Ch20.G3.c080}

{zhdocstring Array.forM Manual.ZhDocString.Ch19Ch20.G3.c081}

{zhdocstring Array.forRevM Manual.ZhDocString.Ch19Ch20.G3.c082}

{zhdocstring Array.firstM Manual.ZhDocString.Ch19Ch20.G3.c083}

{zhdocstring Array.sum Manual.ZhDocString.Ch19Ch20.G3.c084}

## 变换

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Transformation"
%%%
{zhdocstring Array.map Manual.ZhDocString.Ch19Ch20.G3.c085}

{zhdocstring Array.mapMono Manual.ZhDocString.Ch19Ch20.G3.c086}

{zhdocstring Array.mapM Manual.ZhDocString.Ch19Ch20.G3.c087}

{zhdocstring Array.mapM' Manual.ZhDocString.Ch19Ch20.G3.c088}

{zhdocstring Array.mapMonoM Manual.ZhDocString.Ch19Ch20.G3.c089}

{zhdocstring Array.mapIdx Manual.ZhDocString.Ch19Ch20.G3.c090}

{zhdocstring Array.mapIdxM Manual.ZhDocString.Ch19Ch20.G3.c091}

{zhdocstring Array.mapFinIdx Manual.ZhDocString.Ch19Ch20.G3.c092}

{zhdocstring Array.mapFinIdxM Manual.ZhDocString.Ch19Ch20.G3.c093}

{zhdocstring Array.flatMap Manual.ZhDocString.Ch19Ch20.G3.c094}

{zhdocstring Array.flatMapM Manual.ZhDocString.Ch19Ch20.G3.c095}

{zhdocstring Array.zip Manual.ZhDocString.Ch19Ch20.G3.c096}

{zhdocstring Array.zipWith Manual.ZhDocString.Ch19Ch20.G3.c097}

{zhdocstring Array.zipWithAll Manual.ZhDocString.Ch19Ch20.G3.c098}

{zhdocstring Array.zipIdx Manual.ZhDocString.Ch19Ch20.G3.c099}

{zhdocstring Array.unzip Manual.ZhDocString.Ch19Ch20.G3.c100}


## 过滤

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Filtering"
%%%
{zhdocstring Array.filter Manual.ZhDocString.Ch19Ch20.G3.c101}

{zhdocstring Array.filterM Manual.ZhDocString.Ch19Ch20.G3.c102}

{zhdocstring Array.filterRevM Manual.ZhDocString.Ch19Ch20.G3.c103}

{zhdocstring Array.filterMap Manual.ZhDocString.Ch19Ch20.G3.c104}

{zhdocstring Array.filterMapM Manual.ZhDocString.Ch19Ch20.G3.c105}

{zhdocstring Array.filterSepElems Manual.ZhDocString.Ch19Ch20.G3.c106}

{zhdocstring Array.filterSepElemsM Manual.ZhDocString.Ch19Ch20.G3.c107}

## 分割

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Partitioning"
%%%
{zhdocstring Array.partition Manual.ZhDocString.Ch19Ch20.G3.c108}

{zhdocstring Array.groupByKey Manual.ZhDocString.Ch19Ch20.G3.c109}


## 元素判定

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Element-Predicates"
%%%
{zhdocstring Array.contains Manual.ZhDocString.Ch19Ch20.G3.c110}

{zhdocstring Array.elem Manual.ZhDocString.Ch19Ch20.G3.c111}

{zhdocstring Array.find? Manual.ZhDocString.Ch19Ch20.G3.c112}

{zhdocstring Array.findRev? Manual.ZhDocString.Ch19Ch20.G3.c113}

{zhdocstring Array.findIdx Manual.ZhDocString.Ch19Ch20.G3.c114}

{zhdocstring Array.findIdx? Manual.ZhDocString.Ch19Ch20.G3.c115}

{zhdocstring Array.findIdxM? Manual.ZhDocString.Ch19Ch20.G3.c116}

{zhdocstring Array.findFinIdx? Manual.ZhDocString.Ch19Ch20.G3.c117}

{zhdocstring Array.findM? Manual.ZhDocString.Ch19Ch20.G3.c118}

{zhdocstring Array.findRevM? Manual.ZhDocString.Ch19Ch20.G3.c119}

{zhdocstring Array.findSome? Manual.ZhDocString.Ch19Ch20.G3.c120}

{zhdocstring Array.findSome! Manual.ZhDocString.Ch19Ch20.G3.c121}

{zhdocstring Array.findSomeM? Manual.ZhDocString.Ch19Ch20.G3.c122}

{zhdocstring Array.findSomeRev? Manual.ZhDocString.Ch19Ch20.G3.c123}

{zhdocstring Array.findSomeRevM? Manual.ZhDocString.Ch19Ch20.G3.c124}

{zhdocstring Array.all Manual.ZhDocString.Ch19Ch20.G3.c125}

{zhdocstring Array.allM Manual.ZhDocString.Ch19Ch20.G3.c126}

{zhdocstring Array.any Manual.ZhDocString.Ch19Ch20.G3.c127}

{zhdocstring Array.anyM Manual.ZhDocString.Ch19Ch20.G3.c128}

{zhdocstring Array.allDiff Manual.ZhDocString.Ch19Ch20.G3.c129}

{zhdocstring Array.isEqv Manual.ZhDocString.Ch19Ch20.G3.c130}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Comparisons"
%%%
{zhdocstring Array.isPrefixOf Manual.ZhDocString.Ch19Ch20.G3.c131}

{zhdocstring Array.lex Manual.ZhDocString.Ch19Ch20.G3.c132}

## 终止辅助

%%%
tag := "Lean-__________________--Basic-Types--Arrays--API-Reference--Termination-Helpers"
%%%
{zhdocstring Array.attach Manual.ZhDocString.Ch19Ch20.G3.c133}

{zhdocstring Array.attachWith Manual.ZhDocString.Ch19Ch20.G3.c134}

{zhdocstring Array.unattach Manual.ZhDocString.Ch19Ch20.G3.c135}

{zhdocstring Array.pmap Manual.ZhDocString.Ch19Ch20.G3.c136}

{include 1 Manual.BasicTypes.Array.Subarray}

{include 0 Manual.BasicTypes.Array.FFI}
