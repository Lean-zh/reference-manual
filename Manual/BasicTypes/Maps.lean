/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

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

{docstring Std.HashMap +hideFields +hideStructureConstructor}


## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Creation"
%%%
{docstring Std.HashMap.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Properties"
%%%
{docstring Std.HashMap.size}

{docstring Std.HashMap.isEmpty}

{docstring Std.HashMap.Equiv}

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
{docstring Std.HashMap.contains}

{docstring Std.HashMap.get}

{docstring Std.HashMap.get!}

{docstring Std.HashMap.get?}

{docstring Std.HashMap.getD}

{docstring Std.HashMap.getKey}

{docstring Std.HashMap.getKey!}

{docstring Std.HashMap.getKey?}

{docstring Std.HashMap.getKeyD}

{docstring Std.HashMap.keys}

{docstring Std.HashMap.keysArray}

{docstring Std.HashMap.values}

{docstring Std.HashMap.valuesArray}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Modification"
%%%
{docstring Std.HashMap.alter}

{docstring Std.HashMap.modify}

{docstring Std.HashMap.containsThenInsert}

{docstring Std.HashMap.containsThenInsertIfNew}

{docstring Std.HashMap.erase}

{docstring Std.HashMap.filter}

{docstring Std.HashMap.filterMap}

{docstring Std.HashMap.insert}

{docstring Std.HashMap.insertIfNew}

{docstring Std.HashMap.getThenInsertIfNew?}

{docstring Std.HashMap.insertMany}

{docstring Std.HashMap.insertManyIfNewUnit}

{docstring Std.HashMap.partition}

{docstring Std.HashMap.union}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Iteration"
%%%
{docstring Std.HashMap.iter}

{docstring Std.HashMap.keysIter}

{docstring Std.HashMap.valuesIter}

{docstring Std.HashMap.map}

{docstring Std.HashMap.fold}

{docstring Std.HashMap.foldM}

{docstring Std.HashMap.forIn}

{docstring Std.HashMap.forM}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Conversion"
%%%
{docstring Std.HashMap.ofList}

{docstring Std.HashMap.toArray}

{docstring Std.HashMap.toList}

{docstring Std.HashMap.unitOfArray}

{docstring Std.HashMap.unitOfList}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.HashMap.Raw` 与 `Std.HashMap.RawLemmas`。

{docstring Std.HashMap.Raw}

{docstring Std.HashMap.Raw.WF}

# 依值哈希映射
%%%
tag := "DHashMap"
%%%

本节中的声明应通过 `import Std.DHashMap` 导入。

{docstring Std.DHashMap +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Creation"
%%%
{docstring Std.DHashMap.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Properties"
%%%
{docstring Std.DHashMap.size}

{docstring Std.DHashMap.isEmpty}

{docstring Std.DHashMap.Equiv}

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
{docstring Std.DHashMap.contains}

{docstring Std.DHashMap.get}

{docstring Std.DHashMap.get!}

{docstring Std.DHashMap.get?}

{docstring Std.DHashMap.getD}

{docstring Std.DHashMap.getKey}

{docstring Std.DHashMap.getKey!}

{docstring Std.DHashMap.getKey?}

{docstring Std.DHashMap.getKeyD}

{docstring Std.DHashMap.keys}

{docstring Std.DHashMap.keysArray}

{docstring Std.DHashMap.values}


{docstring Std.DHashMap.valuesArray}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Modification"
%%%
{docstring Std.DHashMap.alter}

{docstring Std.DHashMap.modify}

{docstring Std.DHashMap.containsThenInsert}

{docstring Std.DHashMap.containsThenInsertIfNew}

{docstring Std.DHashMap.erase}

{docstring Std.DHashMap.filter}

{docstring Std.DHashMap.filterMap}

{docstring Std.DHashMap.insert}

{docstring Std.DHashMap.insertIfNew}

{docstring Std.DHashMap.getThenInsertIfNew?}

{docstring Std.DHashMap.insertMany}

{docstring Std.DHashMap.partition}

{docstring Std.DHashMap.union}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Iteration"
%%%
{docstring Std.DHashMap.iter}

{docstring Std.DHashMap.keysIter}

{docstring Std.DHashMap.valuesIter}

{docstring Std.DHashMap.map}

{docstring Std.DHashMap.fold}

{docstring Std.DHashMap.foldM}

{docstring Std.DHashMap.forIn}

{docstring Std.DHashMap.forM}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Conversion"
%%%
{docstring Std.DHashMap.ofList}

{docstring Std.DHashMap.toArray}

{docstring Std.DHashMap.toList}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Hash-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.DHashMap.Raw` 与 `Std.DHashMap.RawLemmas`。

{docstring Std.DHashMap.Raw}

{docstring Std.DHashMap.Raw.WF}

# 外延哈希映射
%%%
tag := "ExtHashMap"
%%%

本节中的声明应通过 `import Std.ExtHashMap` 导入。

{docstring Std.ExtHashMap +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Creation"
%%%
{docstring Std.ExtHashMap.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Properties"
%%%
{docstring Std.ExtHashMap.size}

{docstring Std.ExtHashMap.isEmpty}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Queries"
%%%
{docstring Std.ExtHashMap.contains}

{docstring Std.ExtHashMap.get}

{docstring Std.ExtHashMap.get!}

{docstring Std.ExtHashMap.get?}

{docstring Std.ExtHashMap.getD}

{docstring Std.ExtHashMap.getKey}

{docstring Std.ExtHashMap.getKey!}

{docstring Std.ExtHashMap.getKey?}

{docstring Std.ExtHashMap.getKeyD}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Modification"
%%%
{docstring Std.ExtHashMap.alter}

{docstring Std.ExtHashMap.modify}

{docstring Std.ExtHashMap.containsThenInsert}

{docstring Std.ExtHashMap.containsThenInsertIfNew}

{docstring Std.ExtHashMap.erase}

{docstring Std.ExtHashMap.filter}

{docstring Std.ExtHashMap.filterMap}

{docstring Std.ExtHashMap.insert}

{docstring Std.ExtHashMap.insertIfNew}

{docstring Std.ExtHashMap.getThenInsertIfNew?}

{docstring Std.ExtHashMap.insertMany}

{docstring Std.ExtHashMap.insertManyIfNewUnit}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Iteration"
%%%
{docstring Std.ExtHashMap.map}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Maps--Conversion"
%%%
{docstring Std.ExtHashMap.ofList}

{docstring Std.ExtHashMap.unitOfArray}

{docstring Std.ExtHashMap.unitOfList}

# 外延依值哈希映射
%%%
tag := "ExtDHashMap"
%%%

本节中的声明应通过 `import Std.ExtDHashMap` 导入。

{docstring Std.ExtDHashMap +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Creation"
%%%
{docstring Std.ExtDHashMap.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Properties"
%%%
{docstring Std.ExtDHashMap.size}

{docstring Std.ExtDHashMap.isEmpty}


## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Queries"
%%%
{docstring Std.ExtDHashMap.contains}

{docstring Std.ExtDHashMap.get}

{docstring Std.ExtDHashMap.get!}

{docstring Std.ExtDHashMap.get?}

{docstring Std.ExtDHashMap.getD}

{docstring Std.ExtDHashMap.getKey}

{docstring Std.ExtDHashMap.getKey!}

{docstring Std.ExtDHashMap.getKey?}

{docstring Std.ExtDHashMap.getKeyD}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Modification"
%%%
{docstring Std.ExtDHashMap.alter}

{docstring Std.ExtDHashMap.modify}

{docstring Std.ExtDHashMap.containsThenInsert}

{docstring Std.ExtDHashMap.containsThenInsertIfNew}

{docstring Std.ExtDHashMap.erase}

{docstring Std.ExtDHashMap.filter}

{docstring Std.ExtDHashMap.filterMap}

{docstring Std.ExtDHashMap.insert}

{docstring Std.ExtDHashMap.insertIfNew}

{docstring Std.ExtDHashMap.getThenInsertIfNew?}

{docstring Std.ExtDHashMap.insertMany}


## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Iteration"
%%%
{docstring Std.ExtDHashMap.map}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Dependent-Hash-Maps--Conversion"
%%%
{docstring Std.ExtDHashMap.ofList}


# 哈希集合
%%%
tag := "HashSet"
%%%

{docstring Std.HashSet}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Creation"
%%%
{docstring Std.HashSet.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Properties"
%%%
{docstring Std.HashSet.isEmpty}

{docstring Std.HashSet.size}

{docstring Std.HashSet.Equiv}

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
{docstring Std.HashSet.contains}

{docstring Std.HashSet.get}

{docstring Std.HashSet.get!}

{docstring Std.HashSet.get?}

{docstring Std.HashSet.getD}


## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Modification"
%%%
{docstring Std.HashSet.insert}

{docstring Std.HashSet.insertMany}

{docstring Std.HashSet.erase}

{docstring Std.HashSet.filter}

{docstring Std.HashSet.containsThenInsert}

{docstring Std.HashSet.partition}

{docstring Std.HashSet.union}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Iteration"
%%%
{docstring Std.HashSet.iter}

{docstring Std.HashSet.all}

{docstring Std.HashSet.any}

{docstring Std.HashSet.fold}

{docstring Std.HashSet.foldM}

{docstring Std.HashSet.forIn}

{docstring Std.HashSet.forM}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Conversion"
%%%
{docstring Std.HashSet.ofList}

{docstring Std.HashSet.toList}

{docstring Std.HashSet.ofArray}

{docstring Std.HashSet.toArray}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Hash-Sets--Unbundled-Variants"
%%%
分离式集合会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.HashSet.Raw` 与 `Std.HashSet.RawLemmas`。

{docstring Std.HashSet.Raw}

{docstring Std.HashSet.Raw.WF}


# 外延哈希集合
%%%
tag := "ExtHashSet"
%%%

{docstring Std.ExtHashSet}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Creation"
%%%
{docstring Std.ExtHashSet.emptyWithCapacity}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Properties"
%%%
{docstring Std.ExtHashSet.isEmpty}

{docstring Std.ExtHashSet.size}


## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Queries"
%%%
{docstring Std.ExtHashSet.contains}

{docstring Std.ExtHashSet.get}

{docstring Std.ExtHashSet.get!}

{docstring Std.ExtHashSet.get?}

{docstring Std.ExtHashSet.getD}


## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Modification"
%%%
{docstring Std.ExtHashSet.insert}

{docstring Std.ExtHashSet.insertMany}

{docstring Std.ExtHashSet.erase}

{docstring Std.ExtHashSet.filter}

{docstring Std.ExtHashSet.containsThenInsert}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Extensional-Hash-Sets--Conversion"
%%%
{docstring Std.ExtHashSet.ofList}

{docstring Std.ExtHashSet.ofArray}

{include 1 Manual.BasicTypes.Maps.TreeMap}


# 依值树映射
%%%
tag := "DTreeMap"
%%%

本节中的声明应通过 `import Std.DTreeMap` 导入。

{docstring Std.DTreeMap +hideFields +hideStructureConstructor}

## 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Creation"
%%%
{docstring Std.DTreeMap.empty}

## 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Properties"
%%%
{docstring Std.DTreeMap.size}

{docstring Std.DTreeMap.isEmpty}

## 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Queries"
%%%
{docstring Std.DTreeMap.contains}

{docstring Std.DTreeMap.get}

{docstring Std.DTreeMap.get!}

{docstring Std.DTreeMap.get?}

{docstring Std.DTreeMap.getD}

{docstring Std.DTreeMap.getKey}

{docstring Std.DTreeMap.getKey!}

{docstring Std.DTreeMap.getKey?}

{docstring Std.DTreeMap.getKeyD}

{docstring Std.DTreeMap.keys}

{docstring Std.DTreeMap.keysArray}

{docstring Std.DTreeMap.values}

{docstring Std.DTreeMap.valuesArray}

## 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Modification"
%%%
{docstring Std.DTreeMap.alter}

{docstring Std.DTreeMap.modify}

{docstring Std.DTreeMap.containsThenInsert}

{docstring Std.DTreeMap.containsThenInsertIfNew}

{docstring Std.DTreeMap.erase}

{docstring Std.DTreeMap.filter}

{docstring Std.DTreeMap.filterMap}

{docstring Std.DTreeMap.insert}

{docstring Std.DTreeMap.insertIfNew}

{docstring Std.DTreeMap.getThenInsertIfNew?}

{docstring Std.DTreeMap.insertMany}

{docstring Std.DTreeMap.partition}

## 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Iteration"
%%%
{docstring Std.DTreeMap.iter}

{docstring Std.DTreeMap.keysIter}

{docstring Std.DTreeMap.valuesIter}

{docstring Std.DTreeMap.map}

{docstring Std.DTreeMap.foldl}

{docstring Std.DTreeMap.foldlM}

{docstring Std.DTreeMap.forIn}

{docstring Std.DTreeMap.forM}

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Conversion"
%%%
{docstring Std.DTreeMap.ofList}

{docstring Std.DTreeMap.toArray}

{docstring Std.DTreeMap.toList}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Dependent-Tree-Based-Maps--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.DTreeMap.Raw`。

{docstring Std.DTreeMap.Raw}

{docstring Std.DTreeMap.Raw.WF}

{include 1 Manual.BasicTypes.Maps.TreeSet}
