/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G1

import Manual.BasicTypes.Maps.TreeSet
import Manual.BasicTypes.Maps.TreeMap

import Std.Data.HashMap
import Std.Data.HashMap.Raw
import Std.Data.HashMap.RawLemmas
import Std.Data.DHashMap
import Std.Data.DHashMap.Raw
import Std.Data.DHashMap.RawLemmas
import Std.Data.ExtHashMap
import Std.Data.TreeMap
import Std.Data.DTreeMap
import Std.Data.DTreeMap.Raw
import Std.Data.ExtHashSet
import Std.Data.TreeSet
import Std.Data.HashSet
import Std.Data.HashSet.Raw
import Std.Data.HashSet.RawLemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option maxHeartbeats 1000000

#doc (Manual) "映射与集合" =>
%%%
tag := "maps"
file := "Maps-and-Sets"
%%%

{deftech (key := "map")}_映射_是一种将键关联到值的数据结构。
它们也常被称为 {deftech (key := "dictionaries")}_字典_、{deftech (key := "associative arrays")}_关联数组_，或直接称为哈希表。


::::paragraph
在 Lean 中，映射可能具有下列性质：

: 表示

  映射在内存中的表示可以是树，也可以是哈希表。
  当数据结构的 {ref "reference-counting"}[引用] 被共享时，基于树的表示更合适，因为哈希表建立在 {ref "Array"}[数组] 之上。
  当引用不是唯一时，修改数组需要整体复制；而修改树时，只需复制从树根到被修改节点的路径。
  相比之下，当引用不共享时，哈希表可能更高效，因为未共享的数组可以在常数时间内原地修改。
  此外，基于树的映射会按顺序存储数据，因此支持按序遍历。

: 外延性

  映射可以看作从键到值的偏函数。
  {deftech (key := "Extensional maps")}_外延映射_{index (subterm := "extensional")}[map] 指的是命题相等恰好符合这一解释的映射。
  这会让推理更加方便，但也会排除一些原本能够区分它们的有用操作。
  一般来说，只有在验证需要时才应使用外延映射。

: 是否依值

  {deftech (key := "dependent map")}_依值映射_{index (subterm := "dependent")}[map] 指的是其中每个值的类型由其对应的键决定，而不是保持常量的映射。
  依值映射具有更强的表达能力，但也更难使用。
  它们会对使用者提出更多要求。
  例如，{name Std.DHashMap}`DHashMap` 上的许多操作需要 {name}`LawfulBEq` 实例，而不是仅仅需要 {name}`BEq`。

::::

::::: leanSection

```lean -show
open Std
```


:::table +header
*
  - 映射
  - 表示
  - 外延？
  - 依值？

*
  - {name}`TreeMap`
  - 树
  - 否
  - 否

*
  - {name}`DTreeMap`
  - 树
  - 否
  - 是

*
  - {name}`HashMap`
  - 哈希表
  - 否
  - 否

*
  - {name}`DHashMap`
  - 哈希表
  - 否
  - 是

*
  - {name}`ExtHashMap`
  - 哈希表
  - 是
  - 否

*
  - {name}`ExtDHashMap`
  - 哈希表
  - 是
  - 是

:::

:::::

只要把值类型设为 {name}`Unit`，映射就总能被当作集合使用。
提供了下列集合类型：
 * {name}`Std.HashSet` 是基于哈希表的集合。它的性能特征与 {name}`Std.HashMap` 类似：底层基于数组，因此在不共享时可以高效更新。
 * {name}`Std.TreeSet` 是基于平衡树的集合。它的性能特征与 {name}`Std.TreeMap` 类似。
 * {name}`Std.ExtHashSet` 是一种外延哈希集合类型，符合数学上有限集合的概念：若两个集合包含相同元素，则它们相等。


# 库设计

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Library-Design"
%%%
映射与集合上的所有基本操作都经过了完整验证。
相对于使用列表实现的更简单模型，它们都已被证明是正确的。
与此同时，映射与集合也具有可预测的性能。

某些类型还包含了一些尚未完全验证的附加操作。
这些操作依然很有用，而且并非所有程序都需要完全验证。
例如 {name Std.HashMap.partition}`HashMap.partition` 与 {name Std.TreeMap.filterMap}`TreeMap.filterMap`。

## 融合操作

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Library-Design--Fused-Operations"
%%%
根据表中原有内容来修改表是很常见的。
为了避免对同一数据结构遍历两次，许多“查询/修改”操作对都提供了“融合”变体，可以在修改映射或集合的同时完成查询。
在某些情况下，查询结果还会影响修改行为。

例如，{name}`Std.HashMap` 提供 {name Std.HashMap.containsThenInsert}`containsThenInsert`：它在向映射插入键值对的同时，告知该键此前是否已存在；还提供 {name Std.HashMap.containsThenInsertIfNew}`containsThenInsertIfNew`：只有在该映射此前不存在该键时，才插入新的映射关系。
函数 {name Std.HashMap.alter}`alter` 可以在不重复搜索同一个键的情况下修改该键对应的值；修改方式由一个函数给出，其中缺失值用 {name}`none` 表示。

## 原始数据与不变量
%%%
tag := "raw-data"
%%%

基于哈希的映射与基于树的映射都依赖某些内部良构性不变量，例如树必须保持平衡且有序。
在 Lean 标准库中，这些数据结构表示为“底层数据”与“其良构性证明”的一对值。
这一点大多只是内部实现细节；不过，在一种情况下它与用户相关：这种表示方式会阻止它们被用在 {tech (key := "nested inductive types")}[嵌套归纳类型] 中。

为了让它们能够用于嵌套归纳类型，标准库为每个容器都提供了“{deftech (key := "raw")}[原始]”变体，以及将其不变量分离出来的“分离式”版本。
它们遵循如下命名约定：
 * `T.Raw` 是类型 `T` 去掉不变量后的版本。例如，{name}`Std.HashMap.Raw` 就是不带内嵌证明的 {name}`Std.HashMap` 版本。
 * `T.Raw.WF` 是对应的良构性谓词。例如，{name}`Std.HashMap.Raw.WF` 断言某个 {name}`Std.HashMap.Raw` 是良构的。
 * `T` 上的每个操作 `T.f`，在 `T.Raw` 上都有对应操作 `T.Raw.f`。例如，{name}`Std.HashMap.Raw.insert` 是配合原始哈希映射使用的 {name}`Std.HashMap.insert` 版本。
 * 每个操作 `T.Raw.f` 都有相应的良构性引理 `T.Raw.WF.f`。例如，{name}`Std.HashMap.Raw.WF.insert` 断言：向一个良构的原始哈希映射插入新的键值对后，结果仍然是良构的原始哈希映射。

由于绝大多数用例并不需要这些引理，与原始类型有关的引理并不会默认随数据结构一起全部导入。
通常需要额外导入 `Std.Data.T.RawLemmas`（其中 `T` 是相应的数据结构）。

当映射或集合内部出现嵌套归纳类型时，应分三个阶段来定义：

 1. 先定义该嵌套归纳类型的原始版本，使其使用映射或集合类型的原始版本，并定义所有必要操作。
 2. 接着定义一个归纳谓词，断言原始嵌套类型中的所有映射或集合都是良构的，并证明原始类型上的操作保持良构性。
 3. 最后为该嵌套归纳类型构造合适的接口：定义一个 API，在需要时证明良构性性质，并把这些证明细节对用户隐藏起来。

:::example "使用 `Std.HashMap` 的嵌套归纳类型"

```imports -show
import Std
```

此示例要求导入 `Std.Data.HashMap.RawLemmas`。
为了让代码更短，这里打开 `Std` 命名空间：
```lean
open Std
```

一个冒险游戏的地图可以由一系列通过通道连接起来的房间组成。
每个房间都有描述，每条通道也都朝向某个特定方向。
这可以表示为一个递归结构。

```lean +error (name:=badNesting) -keep
structure Maze where
  description : String
  passages : HashMap String Maze
```

这个定义会被拒绝：

```leanOutput badNesting
(kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
```

要让它工作，必须把良构性谓词从结构本身中分离出来。
第一步是重新定义该类型，使其不再内嵌哈希映射的不变量：

```lean
structure RawMaze where
  description : String
  passages : Std.HashMap.Raw String RawMaze
```

最基本的原始迷宫没有任何通道：
```lean
def RawMaze.base (description : String) : RawMaze where
  description := description
  passages := ∅
```

可以用 {name}`RawMaze.insert` 向原始迷宫中加入一条通往下一个迷宫的通道：
```lean
def RawMaze.insert (maze : RawMaze)
    (direction : String) (next : RawMaze) : RawMaze :=
  { maze with
    passages := maze.passages.insert direction next
  }
```

第二步是为 {name}`RawMaze` 定义一个良构性谓词，确保其中包含的每个哈希映射都是良构的。
如果 {name RawMaze.passages}`passages` 字段本身是良构的，并且其中包含的所有原始迷宫也都是良构的，那么这个原始迷宫就是良构的。

```lean
inductive RawMaze.WF : RawMaze → Prop
  | mk {description passages} :
    (∀ (dir : String) v, passages[dir]? = some v → WF v) →
    passages.WF →
    WF { description, passages := passages }
```

基础迷宫是良构的；而向某个其他良构迷宫中插入一条通往良构迷宫的通道，得到的仍是良构迷宫：
```lean
theorem RawMaze.base_wf (description : String) :
    RawMaze.WF (.base description) := by
  constructor
  . intro v h h'
    simp [Std.HashMap.Raw.getElem?_empty] at *
  . exact HashMap.Raw.WF.empty

def RawMaze.insert_wf (maze : RawMaze) :
    WF maze → WF next → WF (maze.insert dir next) := by
  let ⟨desc, passages⟩ := maze
  intro ⟨wfMore, wfPassages⟩ wfNext
  constructor
  . intro dir' v
    rw [HashMap.Raw.getElem?_insert wfPassages]
    split <;> intros <;> simp_all [wfMore dir']
  . simp_all [HashMap.Raw.WF.insert]
```

最后，可以定义一个更友好的接口，使用户不必关心良构性问题。
{name}`Maze` 会把一个 {name}`RawMaze` 与其良构性证明打包在一起：
```lean
structure Maze where
  raw : RawMaze
  wf : raw.WF
```

运算 {name Maze.base}`base` 和 {name Maze.insert}`insert` 会自动处理良构性的证明义务：
```lean
def Maze.base (description : String) : Maze where
  raw := .base description
  wf := by apply RawMaze.base_wf

def Maze.insert (maze : Maze)
    (dir : String) (next : Maze) : Maze where
  raw := maze.raw.insert dir next.raw
  wf := RawMaze.insert_wf maze.raw maze.wf next.wf
```

{name}`Maze` API 的使用者既可以查看当前迷宫的描述，也可以尝试沿某个方向走向新的迷宫：
```lean
def Maze.description (maze : Maze) : String :=
  maze.raw.description

def Maze.go? (maze : Maze) (dir : String) : Option Maze :=
  match h : maze.raw.passages[dir]? with
  | none => none
  | some m' =>
    Maze.mk m' <| by
      let ⟨r, wf⟩ := maze
      let ⟨wfAll, _⟩ := wf
      apply wfAll dir
      apply h
```
:::

## 保持唯一引用的合适运算

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Library-Design--Suitable-Operators-for-Uniqueness"
%%%
在使用数据结构时，应尽量确保尽可能多的引用保持唯一；这能让 Lean 在维持纯函数接口的同时，在幕后使用破坏性更新。
映射与集合库提供了一些可用于保持引用唯一性的运算。
特别是，在可能的情况下，应优先使用 {name Std.HashMap.alter}`alter` 或 {name Std.HashMap.modify}`modify` 之类的操作，而不是显式取出某个值、修改它、再将其重新插入。
这些操作可以避免在修改过程中产生该值的第二个引用。

:::example "修改映射中的值"

```imports -show
import Std
```

```lean
open Std
```

函数 {name}`addAlias` 用于在某个数据集中跟踪一个字符串的别名。
添加别名的一种方式是先查找已有别名（默认为空数组），再插入新别名，最后把得到的数组保存回映射中：

```lean
def addAlias (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  aliases.insert key (prior.push value)
```

这种实现的性能特征较差。
由于映射保留了对旧值的引用，因此数组必须被复制，而不能原地修改。
更好的实现是在修改之前显式地把旧值从映射中删除：

```lean
def addAlias' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  let aliases := aliases.erase key
  aliases.insert key (prior.push value)
```

使用 {name}`HashMap.alter` 会更好。
它免去了显式删除并重新插入该值的需要：

```lean
def addAlias'' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  aliases.alter key fun prior? =>
    some ((prior?.getD #[]).push value)
```

:::



# 哈希映射
%%%
tag := "HashMap"
%%%

本节中的声明应通过 `import Std.HashMap` 导入。

{zhdocstring Std.HashMap Manual.ZhDocString.Ch19Ch20.G1.c001 +hideFields +hideStructureConstructor}


## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Creation"
%%%
{zhdocstring Std.HashMap.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c002}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Properties"
%%%
{zhdocstring Std.HashMap.size Manual.ZhDocString.Ch19Ch20.G1.c003}

{zhdocstring Std.HashMap.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c004}

{zhdocstring Std.HashMap.Equiv Manual.ZhDocString.Ch19Ch20.G1.c005}

:::syntax term (title := "等价") (namespace := Std.HashMap)

关系 {name Std.HashMap.Equiv}`HashMap.Equiv` 也可以写成一个中缀运算符，该运算符的作用域限定在其命名空间内：

```grammar
$_ ~m $_
```

:::

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Queries"
%%%
{zhdocstring Std.HashMap.contains Manual.ZhDocString.Ch19Ch20.G1.c006}

{zhdocstring Std.HashMap.get Manual.ZhDocString.Ch19Ch20.G1.c007}

{zhdocstring Std.HashMap.get! Manual.ZhDocString.Ch19Ch20.G1.c008}

{zhdocstring Std.HashMap.get? Manual.ZhDocString.Ch19Ch20.G1.c009}

{zhdocstring Std.HashMap.getD Manual.ZhDocString.Ch19Ch20.G1.c010}

{zhdocstring Std.HashMap.getKey Manual.ZhDocString.Ch19Ch20.G1.c011}

{zhdocstring Std.HashMap.getKey! Manual.ZhDocString.Ch19Ch20.G1.c012}

{zhdocstring Std.HashMap.getKey? Manual.ZhDocString.Ch19Ch20.G1.c013}

{zhdocstring Std.HashMap.getKeyD Manual.ZhDocString.Ch19Ch20.G1.c014}

{zhdocstring Std.HashMap.keys Manual.ZhDocString.Ch19Ch20.G1.c015}

{zhdocstring Std.HashMap.keysArray Manual.ZhDocString.Ch19Ch20.G1.c016}

{zhdocstring Std.HashMap.values Manual.ZhDocString.Ch19Ch20.G1.c017}

{zhdocstring Std.HashMap.valuesArray Manual.ZhDocString.Ch19Ch20.G1.c018}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Modification"
%%%
{zhdocstring Std.HashMap.alter Manual.ZhDocString.Ch19Ch20.G1.c019}

{zhdocstring Std.HashMap.modify Manual.ZhDocString.Ch19Ch20.G1.c020}

{zhdocstring Std.HashMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c021}

{zhdocstring Std.HashMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G1.c022}

{zhdocstring Std.HashMap.erase Manual.ZhDocString.Ch19Ch20.G1.c023}

{zhdocstring Std.HashMap.filter Manual.ZhDocString.Ch19Ch20.G1.c024}

{zhdocstring Std.HashMap.filterMap Manual.ZhDocString.Ch19Ch20.G1.c025}

{zhdocstring Std.HashMap.insert Manual.ZhDocString.Ch19Ch20.G1.c026}

{zhdocstring Std.HashMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G1.c027}

{zhdocstring Std.HashMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G1.c028}

{zhdocstring Std.HashMap.insertMany Manual.ZhDocString.Ch19Ch20.G1.c029}

{zhdocstring Std.HashMap.insertManyIfNewUnit Manual.ZhDocString.Ch19Ch20.G1.c030}

{zhdocstring Std.HashMap.partition Manual.ZhDocString.Ch19Ch20.G1.c031}

{zhdocstring Std.HashMap.union Manual.ZhDocString.Ch19Ch20.G1.c032}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Iteration"
%%%
{zhdocstring Std.HashMap.iter Manual.ZhDocString.Ch19Ch20.G1.c033}

{zhdocstring Std.HashMap.keysIter Manual.ZhDocString.Ch19Ch20.G1.c034}

{zhdocstring Std.HashMap.valuesIter Manual.ZhDocString.Ch19Ch20.G1.c035}

{zhdocstring Std.HashMap.map Manual.ZhDocString.Ch19Ch20.G1.c036}

{zhdocstring Std.HashMap.fold Manual.ZhDocString.Ch19Ch20.G1.c037}

{zhdocstring Std.HashMap.foldM Manual.ZhDocString.Ch19Ch20.G1.c038}

{zhdocstring Std.HashMap.forIn Manual.ZhDocString.Ch19Ch20.G1.c039}

{zhdocstring Std.HashMap.forM Manual.ZhDocString.Ch19Ch20.G1.c040}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Conversion"
%%%
{zhdocstring Std.HashMap.ofList Manual.ZhDocString.Ch19Ch20.G1.c041}

{zhdocstring Std.HashMap.toArray Manual.ZhDocString.Ch19Ch20.G1.c042}

{zhdocstring Std.HashMap.toList Manual.ZhDocString.Ch19Ch20.G1.c043}

{zhdocstring Std.HashMap.unitOfArray Manual.ZhDocString.Ch19Ch20.G1.c044}

{zhdocstring Std.HashMap.unitOfList Manual.ZhDocString.Ch19Ch20.G1.c045}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.HashMap.Raw` 与 `Std.HashMap.RawLemmas`。

{zhdocstring Std.HashMap.Raw Manual.ZhDocString.Ch19Ch20.G1.c046}

{zhdocstring Std.HashMap.Raw.WF Manual.ZhDocString.Ch19Ch20.G1.c047}

# 依值哈希映射
%%%
tag := "DHashMap"
%%%

本节中的声明应通过 `import Std.DHashMap` 导入。

{zhdocstring Std.DHashMap Manual.ZhDocString.Ch19Ch20.G1.c048 +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Creation"
%%%
{zhdocstring Std.DHashMap.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c049}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Properties"
%%%
{zhdocstring Std.DHashMap.size Manual.ZhDocString.Ch19Ch20.G1.c050}

{zhdocstring Std.DHashMap.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c051}

{zhdocstring Std.DHashMap.Equiv Manual.ZhDocString.Ch19Ch20.G1.c052}

:::syntax term (title := "等价") (namespace := Std.DHashMap)

关系 {name Std.DHashMap.Equiv}`DHashMap.Equiv` 也可以写成一个中缀运算符，该运算符的作用域限定在其命名空间内：

```grammar
$_ ~m $_
```

:::

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Queries"
%%%
{zhdocstring Std.DHashMap.contains Manual.ZhDocString.Ch19Ch20.G1.c053}

{zhdocstring Std.DHashMap.get Manual.ZhDocString.Ch19Ch20.G1.c054}

{zhdocstring Std.DHashMap.get! Manual.ZhDocString.Ch19Ch20.G1.c055}

{zhdocstring Std.DHashMap.get? Manual.ZhDocString.Ch19Ch20.G1.c056}

{zhdocstring Std.DHashMap.getD Manual.ZhDocString.Ch19Ch20.G1.c057}

{zhdocstring Std.DHashMap.getKey Manual.ZhDocString.Ch19Ch20.G1.c058}

{zhdocstring Std.DHashMap.getKey! Manual.ZhDocString.Ch19Ch20.G1.c059}

{zhdocstring Std.DHashMap.getKey? Manual.ZhDocString.Ch19Ch20.G1.c060}

{zhdocstring Std.DHashMap.getKeyD Manual.ZhDocString.Ch19Ch20.G1.c061}

{zhdocstring Std.DHashMap.keys Manual.ZhDocString.Ch19Ch20.G1.c062}

{zhdocstring Std.DHashMap.keysArray Manual.ZhDocString.Ch19Ch20.G1.c063}

{zhdocstring Std.DHashMap.values Manual.ZhDocString.Ch19Ch20.G1.c064}


{zhdocstring Std.DHashMap.valuesArray Manual.ZhDocString.Ch19Ch20.G1.c065}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Modification"
%%%
{zhdocstring Std.DHashMap.alter Manual.ZhDocString.Ch19Ch20.G1.c066}

{zhdocstring Std.DHashMap.modify Manual.ZhDocString.Ch19Ch20.G1.c067}

{zhdocstring Std.DHashMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c068}

{zhdocstring Std.DHashMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G1.c069}

{zhdocstring Std.DHashMap.erase Manual.ZhDocString.Ch19Ch20.G1.c070}

{zhdocstring Std.DHashMap.filter Manual.ZhDocString.Ch19Ch20.G1.c071}

{zhdocstring Std.DHashMap.filterMap Manual.ZhDocString.Ch19Ch20.G1.c072}

{zhdocstring Std.DHashMap.insert Manual.ZhDocString.Ch19Ch20.G1.c073}

{zhdocstring Std.DHashMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G1.c074}

{zhdocstring Std.DHashMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G1.c075}

{zhdocstring Std.DHashMap.insertMany Manual.ZhDocString.Ch19Ch20.G1.c076}

{zhdocstring Std.DHashMap.partition Manual.ZhDocString.Ch19Ch20.G1.c077}

{zhdocstring Std.DHashMap.union Manual.ZhDocString.Ch19Ch20.G1.c078}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Iteration"
%%%
{zhdocstring Std.DHashMap.iter Manual.ZhDocString.Ch19Ch20.G1.c079}

{zhdocstring Std.DHashMap.keysIter Manual.ZhDocString.Ch19Ch20.G1.c080}

{zhdocstring Std.DHashMap.valuesIter Manual.ZhDocString.Ch19Ch20.G1.c081}

{zhdocstring Std.DHashMap.map Manual.ZhDocString.Ch19Ch20.G1.c082}

{zhdocstring Std.DHashMap.fold Manual.ZhDocString.Ch19Ch20.G1.c083}

{zhdocstring Std.DHashMap.foldM Manual.ZhDocString.Ch19Ch20.G1.c084}

{zhdocstring Std.DHashMap.forIn Manual.ZhDocString.Ch19Ch20.G1.c085}

{zhdocstring Std.DHashMap.forM Manual.ZhDocString.Ch19Ch20.G1.c086}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Conversion"
%%%
{zhdocstring Std.DHashMap.ofList Manual.ZhDocString.Ch19Ch20.G1.c087}

{zhdocstring Std.DHashMap.toArray Manual.ZhDocString.Ch19Ch20.G1.c088}

{zhdocstring Std.DHashMap.toList Manual.ZhDocString.Ch19Ch20.G1.c089}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.DHashMap.Raw` 与 `Std.DHashMap.RawLemmas`。

{zhdocstring Std.DHashMap.Raw Manual.ZhDocString.Ch19Ch20.G1.c090}

{zhdocstring Std.DHashMap.Raw.WF Manual.ZhDocString.Ch19Ch20.G1.c091}

# 外延哈希映射
%%%
tag := "ExtHashMap"
%%%

本节中的声明应通过 `import Std.ExtHashMap` 导入。

{zhdocstring Std.ExtHashMap Manual.ZhDocString.Ch19Ch20.G1.c092 +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Creation"
%%%
{zhdocstring Std.ExtHashMap.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c093}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Properties"
%%%
{zhdocstring Std.ExtHashMap.size Manual.ZhDocString.Ch19Ch20.G1.c094}

{zhdocstring Std.ExtHashMap.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c095}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Queries"
%%%
{zhdocstring Std.ExtHashMap.contains Manual.ZhDocString.Ch19Ch20.G1.c096}

{zhdocstring Std.ExtHashMap.get Manual.ZhDocString.Ch19Ch20.G1.c097}

{zhdocstring Std.ExtHashMap.get! Manual.ZhDocString.Ch19Ch20.G1.c098}

{zhdocstring Std.ExtHashMap.get? Manual.ZhDocString.Ch19Ch20.G1.c099}

{zhdocstring Std.ExtHashMap.getD Manual.ZhDocString.Ch19Ch20.G1.c100}

{zhdocstring Std.ExtHashMap.getKey Manual.ZhDocString.Ch19Ch20.G1.c101}

{zhdocstring Std.ExtHashMap.getKey! Manual.ZhDocString.Ch19Ch20.G1.c102}

{zhdocstring Std.ExtHashMap.getKey? Manual.ZhDocString.Ch19Ch20.G1.c103}

{zhdocstring Std.ExtHashMap.getKeyD Manual.ZhDocString.Ch19Ch20.G1.c104}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Modification"
%%%
{zhdocstring Std.ExtHashMap.alter Manual.ZhDocString.Ch19Ch20.G1.c105}

{zhdocstring Std.ExtHashMap.modify Manual.ZhDocString.Ch19Ch20.G1.c106}

{zhdocstring Std.ExtHashMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c107}

{zhdocstring Std.ExtHashMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G1.c108}

{zhdocstring Std.ExtHashMap.erase Manual.ZhDocString.Ch19Ch20.G1.c109}

{zhdocstring Std.ExtHashMap.filter Manual.ZhDocString.Ch19Ch20.G1.c110}

{zhdocstring Std.ExtHashMap.filterMap Manual.ZhDocString.Ch19Ch20.G1.c111}

{zhdocstring Std.ExtHashMap.insert Manual.ZhDocString.Ch19Ch20.G1.c112}

{zhdocstring Std.ExtHashMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G1.c113}

{zhdocstring Std.ExtHashMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G1.c114}

{zhdocstring Std.ExtHashMap.insertMany Manual.ZhDocString.Ch19Ch20.G1.c115}

{zhdocstring Std.ExtHashMap.insertManyIfNewUnit Manual.ZhDocString.Ch19Ch20.G1.c116}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Iteration"
%%%
{zhdocstring Std.ExtHashMap.map Manual.ZhDocString.Ch19Ch20.G1.c117}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Conversion"
%%%
{zhdocstring Std.ExtHashMap.ofList Manual.ZhDocString.Ch19Ch20.G1.c118}

{zhdocstring Std.ExtHashMap.unitOfArray Manual.ZhDocString.Ch19Ch20.G1.c119}

{zhdocstring Std.ExtHashMap.unitOfList Manual.ZhDocString.Ch19Ch20.G1.c120}

# 外延依值哈希映射
%%%
tag := "ExtDHashMap"
%%%

本节中的声明应通过 `import Std.ExtDHashMap` 导入。

{zhdocstring Std.ExtDHashMap Manual.ZhDocString.Ch19Ch20.G1.c121 +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Creation"
%%%
{zhdocstring Std.ExtDHashMap.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c122}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Properties"
%%%
{zhdocstring Std.ExtDHashMap.size Manual.ZhDocString.Ch19Ch20.G1.c123}

{zhdocstring Std.ExtDHashMap.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c124}


## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Queries"
%%%
{zhdocstring Std.ExtDHashMap.contains Manual.ZhDocString.Ch19Ch20.G1.c125}

{zhdocstring Std.ExtDHashMap.get Manual.ZhDocString.Ch19Ch20.G1.c126}

{zhdocstring Std.ExtDHashMap.get! Manual.ZhDocString.Ch19Ch20.G1.c127}

{zhdocstring Std.ExtDHashMap.get? Manual.ZhDocString.Ch19Ch20.G1.c128}

{zhdocstring Std.ExtDHashMap.getD Manual.ZhDocString.Ch19Ch20.G1.c129}

{zhdocstring Std.ExtDHashMap.getKey Manual.ZhDocString.Ch19Ch20.G1.c130}

{zhdocstring Std.ExtDHashMap.getKey! Manual.ZhDocString.Ch19Ch20.G1.c131}

{zhdocstring Std.ExtDHashMap.getKey? Manual.ZhDocString.Ch19Ch20.G1.c132}

{zhdocstring Std.ExtDHashMap.getKeyD Manual.ZhDocString.Ch19Ch20.G1.c133}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Modification"
%%%
{zhdocstring Std.ExtDHashMap.alter Manual.ZhDocString.Ch19Ch20.G1.c134}

{zhdocstring Std.ExtDHashMap.modify Manual.ZhDocString.Ch19Ch20.G1.c135}

{zhdocstring Std.ExtDHashMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c136}

{zhdocstring Std.ExtDHashMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G1.c137}

{zhdocstring Std.ExtDHashMap.erase Manual.ZhDocString.Ch19Ch20.G1.c138}

{zhdocstring Std.ExtDHashMap.filter Manual.ZhDocString.Ch19Ch20.G1.c139}

{zhdocstring Std.ExtDHashMap.filterMap Manual.ZhDocString.Ch19Ch20.G1.c140}

{zhdocstring Std.ExtDHashMap.insert Manual.ZhDocString.Ch19Ch20.G1.c141}

{zhdocstring Std.ExtDHashMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G1.c142}

{zhdocstring Std.ExtDHashMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G1.c143}

{zhdocstring Std.ExtDHashMap.insertMany Manual.ZhDocString.Ch19Ch20.G1.c144}


## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Iteration"
%%%
{zhdocstring Std.ExtDHashMap.map Manual.ZhDocString.Ch19Ch20.G1.c145}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Conversion"
%%%
{zhdocstring Std.ExtDHashMap.ofList Manual.ZhDocString.Ch19Ch20.G1.c146}


# 哈希集合
%%%
tag := "HashSet"
%%%

{zhdocstring Std.HashSet Manual.ZhDocString.Ch19Ch20.G1.c147}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Creation"
%%%
{zhdocstring Std.HashSet.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c148}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Properties"
%%%
{zhdocstring Std.HashSet.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c149}

{zhdocstring Std.HashSet.size Manual.ZhDocString.Ch19Ch20.G1.c150}

{zhdocstring Std.HashSet.Equiv Manual.ZhDocString.Ch19Ch20.G1.c151}

:::syntax term (title := "等价") (namespace := Std.HashMap)

关系 {name Std.HashSet.Equiv}`HashSet.Equiv` 也可以写成一个中缀运算符，该运算符的作用域限定在其命名空间内：

```grammar
$_ ~m $_
```

:::


## 查询


%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Queries"
%%%
{zhdocstring Std.HashSet.contains Manual.ZhDocString.Ch19Ch20.G1.c152}

{zhdocstring Std.HashSet.get Manual.ZhDocString.Ch19Ch20.G1.c153}

{zhdocstring Std.HashSet.get! Manual.ZhDocString.Ch19Ch20.G1.c154}

{zhdocstring Std.HashSet.get? Manual.ZhDocString.Ch19Ch20.G1.c155}

{zhdocstring Std.HashSet.getD Manual.ZhDocString.Ch19Ch20.G1.c156}


## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Modification"
%%%
{zhdocstring Std.HashSet.insert Manual.ZhDocString.Ch19Ch20.G1.c157}

{zhdocstring Std.HashSet.insertMany Manual.ZhDocString.Ch19Ch20.G1.c158}

{zhdocstring Std.HashSet.erase Manual.ZhDocString.Ch19Ch20.G1.c159}

{zhdocstring Std.HashSet.filter Manual.ZhDocString.Ch19Ch20.G1.c160}

{zhdocstring Std.HashSet.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c161}

{zhdocstring Std.HashSet.partition Manual.ZhDocString.Ch19Ch20.G1.c162}

{zhdocstring Std.HashSet.union Manual.ZhDocString.Ch19Ch20.G1.c163}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Iteration"
%%%
{zhdocstring Std.HashSet.iter Manual.ZhDocString.Ch19Ch20.G1.c164}

{zhdocstring Std.HashSet.all Manual.ZhDocString.Ch19Ch20.G1.c165}

{zhdocstring Std.HashSet.any Manual.ZhDocString.Ch19Ch20.G1.c166}

{zhdocstring Std.HashSet.fold Manual.ZhDocString.Ch19Ch20.G1.c167}

{zhdocstring Std.HashSet.foldM Manual.ZhDocString.Ch19Ch20.G1.c168}

{zhdocstring Std.HashSet.forIn Manual.ZhDocString.Ch19Ch20.G1.c169}

{zhdocstring Std.HashSet.forM Manual.ZhDocString.Ch19Ch20.G1.c170}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Conversion"
%%%
{zhdocstring Std.HashSet.ofList Manual.ZhDocString.Ch19Ch20.G1.c171}

{zhdocstring Std.HashSet.toList Manual.ZhDocString.Ch19Ch20.G1.c172}

{zhdocstring Std.HashSet.ofArray Manual.ZhDocString.Ch19Ch20.G1.c173}

{zhdocstring Std.HashSet.toArray Manual.ZhDocString.Ch19Ch20.G1.c174}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Unbundled-Variants"
%%%
分离式集合会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.HashSet.Raw` 与 `Std.HashSet.RawLemmas`。

{zhdocstring Std.HashSet.Raw Manual.ZhDocString.Ch19Ch20.G1.c175}

{zhdocstring Std.HashSet.Raw.WF Manual.ZhDocString.Ch19Ch20.G1.c176}


# 外延哈希集合
%%%
tag := "ExtHashSet"
%%%

{zhdocstring Std.ExtHashSet Manual.ZhDocString.Ch19Ch20.G1.c177}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Creation"
%%%
{zhdocstring Std.ExtHashSet.emptyWithCapacity Manual.ZhDocString.Ch19Ch20.G1.c178}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Properties"
%%%
{zhdocstring Std.ExtHashSet.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c179}

{zhdocstring Std.ExtHashSet.size Manual.ZhDocString.Ch19Ch20.G1.c180}


## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Queries"
%%%
{zhdocstring Std.ExtHashSet.contains Manual.ZhDocString.Ch19Ch20.G1.c181}

{zhdocstring Std.ExtHashSet.get Manual.ZhDocString.Ch19Ch20.G1.c182}

{zhdocstring Std.ExtHashSet.get! Manual.ZhDocString.Ch19Ch20.G1.c183}

{zhdocstring Std.ExtHashSet.get? Manual.ZhDocString.Ch19Ch20.G1.c184}

{zhdocstring Std.ExtHashSet.getD Manual.ZhDocString.Ch19Ch20.G1.c185}


## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Modification"
%%%
{zhdocstring Std.ExtHashSet.insert Manual.ZhDocString.Ch19Ch20.G1.c186}

{zhdocstring Std.ExtHashSet.insertMany Manual.ZhDocString.Ch19Ch20.G1.c187}

{zhdocstring Std.ExtHashSet.erase Manual.ZhDocString.Ch19Ch20.G1.c188}

{zhdocstring Std.ExtHashSet.filter Manual.ZhDocString.Ch19Ch20.G1.c189}

{zhdocstring Std.ExtHashSet.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c190}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Conversion"
%%%
{zhdocstring Std.ExtHashSet.ofList Manual.ZhDocString.Ch19Ch20.G1.c191}

{zhdocstring Std.ExtHashSet.ofArray Manual.ZhDocString.Ch19Ch20.G1.c192}

{include 1 Manual.BasicTypes.Maps.TreeMap}


# 依值树映射
%%%
tag := "DTreeMap"
%%%

本节中的声明应通过 `import Std.DTreeMap` 导入。

{zhdocstring Std.DTreeMap Manual.ZhDocString.Ch19Ch20.G1.c193 +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Creation"
%%%
{zhdocstring Std.DTreeMap.empty Manual.ZhDocString.Ch19Ch20.G1.c194}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Properties"
%%%
{zhdocstring Std.DTreeMap.size Manual.ZhDocString.Ch19Ch20.G1.c195}

{zhdocstring Std.DTreeMap.isEmpty Manual.ZhDocString.Ch19Ch20.G1.c196}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Queries"
%%%
{zhdocstring Std.DTreeMap.contains Manual.ZhDocString.Ch19Ch20.G1.c197}

{zhdocstring Std.DTreeMap.get Manual.ZhDocString.Ch19Ch20.G1.c198}

{zhdocstring Std.DTreeMap.get! Manual.ZhDocString.Ch19Ch20.G1.c199}

{zhdocstring Std.DTreeMap.get? Manual.ZhDocString.Ch19Ch20.G1.c200}

{zhdocstring Std.DTreeMap.getD Manual.ZhDocString.Ch19Ch20.G1.c201}

{zhdocstring Std.DTreeMap.getKey Manual.ZhDocString.Ch19Ch20.G1.c202}

{zhdocstring Std.DTreeMap.getKey! Manual.ZhDocString.Ch19Ch20.G1.c203}

{zhdocstring Std.DTreeMap.getKey? Manual.ZhDocString.Ch19Ch20.G1.c204}

{zhdocstring Std.DTreeMap.getKeyD Manual.ZhDocString.Ch19Ch20.G1.c205}

{zhdocstring Std.DTreeMap.keys Manual.ZhDocString.Ch19Ch20.G1.c206}

{zhdocstring Std.DTreeMap.keysArray Manual.ZhDocString.Ch19Ch20.G1.c207}

{zhdocstring Std.DTreeMap.values Manual.ZhDocString.Ch19Ch20.G1.c208}

{zhdocstring Std.DTreeMap.valuesArray Manual.ZhDocString.Ch19Ch20.G1.c209}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Modification"
%%%
{zhdocstring Std.DTreeMap.alter Manual.ZhDocString.Ch19Ch20.G1.c210}

{zhdocstring Std.DTreeMap.modify Manual.ZhDocString.Ch19Ch20.G1.c211}

{zhdocstring Std.DTreeMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G1.c212}

{zhdocstring Std.DTreeMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G1.c213}

{zhdocstring Std.DTreeMap.erase Manual.ZhDocString.Ch19Ch20.G1.c214}

{zhdocstring Std.DTreeMap.filter Manual.ZhDocString.Ch19Ch20.G1.c215}

{zhdocstring Std.DTreeMap.filterMap Manual.ZhDocString.Ch19Ch20.G1.c216}

{zhdocstring Std.DTreeMap.insert Manual.ZhDocString.Ch19Ch20.G1.c217}

{zhdocstring Std.DTreeMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G1.c218}

{zhdocstring Std.DTreeMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G1.c219}

{zhdocstring Std.DTreeMap.insertMany Manual.ZhDocString.Ch19Ch20.G1.c220}

{zhdocstring Std.DTreeMap.partition Manual.ZhDocString.Ch19Ch20.G1.c221}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Iteration"
%%%
{zhdocstring Std.DTreeMap.iter Manual.ZhDocString.Ch19Ch20.G1.c222}

{zhdocstring Std.DTreeMap.keysIter Manual.ZhDocString.Ch19Ch20.G1.c223}

{zhdocstring Std.DTreeMap.valuesIter Manual.ZhDocString.Ch19Ch20.G1.c224}

{zhdocstring Std.DTreeMap.map Manual.ZhDocString.Ch19Ch20.G1.c225}

{zhdocstring Std.DTreeMap.foldl Manual.ZhDocString.Ch19Ch20.G1.c226}

{zhdocstring Std.DTreeMap.foldlM Manual.ZhDocString.Ch19Ch20.G1.c227}

{zhdocstring Std.DTreeMap.forIn Manual.ZhDocString.Ch19Ch20.G1.c228}

{zhdocstring Std.DTreeMap.forM Manual.ZhDocString.Ch19Ch20.G1.c229}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Conversion"
%%%
{zhdocstring Std.DTreeMap.ofList Manual.ZhDocString.Ch19Ch20.G1.c230}

{zhdocstring Std.DTreeMap.toArray Manual.ZhDocString.Ch19Ch20.G1.c231}

{zhdocstring Std.DTreeMap.toList Manual.ZhDocString.Ch19Ch20.G1.c232}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.DTreeMap.Raw`。

{zhdocstring Std.DTreeMap.Raw Manual.ZhDocString.Ch19Ch20.G1.c233}

{zhdocstring Std.DTreeMap.Raw.WF Manual.ZhDocString.Ch19Ch20.G1.c234}

{include 1 Manual.BasicTypes.Maps.TreeSet}
