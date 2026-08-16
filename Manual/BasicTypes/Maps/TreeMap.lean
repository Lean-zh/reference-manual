/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


import Std.Data.TreeMap
import Std.Data.TreeMap.Raw


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "基于树的映射" =>
%%%
tag := "TreeMap"
%%%


本节中的声明应通过 `import Std.TreeMap` 导入。

{docstring Std.TreeMap +hideFields +hideStructureConstructor}

# 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Creation"
%%%
{docstring Std.TreeMap.empty}

# 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Properties"
%%%
{docstring Std.TreeMap.size}

{docstring Std.TreeMap.isEmpty}


# 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Queries"
%%%
{docstring Std.TreeMap.contains}

{docstring Std.TreeMap.get}

{docstring Std.TreeMap.get!}

{docstring Std.TreeMap.get?}

{docstring Std.TreeMap.getD}

{docstring Std.TreeMap.getKey}

{docstring Std.TreeMap.getKey!}

{docstring Std.TreeMap.getKey?}

{docstring Std.TreeMap.getKeyD}

{docstring Std.TreeMap.keys}

{docstring Std.TreeMap.keysArray}

{docstring Std.TreeMap.values}

{docstring Std.TreeMap.valuesArray}

## 基于顺序的查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Queries--Ordering-Based-Queries"
%%%
{docstring Std.TreeMap.entryAtIdx}

{docstring Std.TreeMap.entryAtIdx!}

{docstring Std.TreeMap.entryAtIdx?}

{docstring Std.TreeMap.entryAtIdxD}

{docstring Std.TreeMap.getEntryGE}

{docstring Std.TreeMap.getEntryGE!}

{docstring Std.TreeMap.getEntryGE?}

{docstring Std.TreeMap.getEntryGED}

{docstring Std.TreeMap.getEntryGT}

{docstring Std.TreeMap.getEntryGT!}

{docstring Std.TreeMap.getEntryGT?}

{docstring Std.TreeMap.getEntryGTD}

{docstring Std.TreeMap.getEntryLE}

{docstring Std.TreeMap.getEntryLE!}

{docstring Std.TreeMap.getEntryLE?}

{docstring Std.TreeMap.getEntryLED}

{docstring Std.TreeMap.getEntryLT}

{docstring Std.TreeMap.getEntryLT!}

{docstring Std.TreeMap.getEntryLT?}

{docstring Std.TreeMap.getEntryLTD}

{docstring Std.TreeMap.getKeyGE}

{docstring Std.TreeMap.getKeyGE!}

{docstring Std.TreeMap.getKeyGE?}

{docstring Std.TreeMap.getKeyGED}

{docstring Std.TreeMap.getKeyGT}

{docstring Std.TreeMap.getKeyGT!}

{docstring Std.TreeMap.getKeyGT?}

{docstring Std.TreeMap.getKeyGTD}

{docstring Std.TreeMap.getKeyLE}

{docstring Std.TreeMap.getKeyLE!}

{docstring Std.TreeMap.getKeyLE?}

{docstring Std.TreeMap.getKeyLED}

{docstring Std.TreeMap.getKeyLT}

{docstring Std.TreeMap.getKeyLT!}

{docstring Std.TreeMap.getKeyLT?}

{docstring Std.TreeMap.getKeyLTD}

{docstring Std.TreeMap.keyAtIdx}

{docstring Std.TreeMap.keyAtIdx!}

{docstring Std.TreeMap.keyAtIdx?}

{docstring Std.TreeMap.keyAtIdxD}

{docstring Std.TreeMap.minEntry}

{docstring Std.TreeMap.minEntry!}

{docstring Std.TreeMap.minEntry?}

{docstring Std.TreeMap.minEntryD}

{docstring Std.TreeMap.minKey}

{docstring Std.TreeMap.minKey!}

{docstring Std.TreeMap.minKey?}

{docstring Std.TreeMap.minKeyD}

{docstring Std.TreeMap.maxEntry}

{docstring Std.TreeMap.maxEntry!}

{docstring Std.TreeMap.maxEntry?}

{docstring Std.TreeMap.maxEntryD}

{docstring Std.TreeMap.maxKey}

{docstring Std.TreeMap.maxKey!}

{docstring Std.TreeMap.maxKey?}

{docstring Std.TreeMap.maxKeyD}


# 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Modification"
%%%
{docstring Std.TreeMap.alter}

{docstring Std.TreeMap.modify}

{docstring Std.TreeMap.containsThenInsert}

{docstring Std.TreeMap.containsThenInsertIfNew}

{docstring Std.TreeMap.erase}

{docstring Std.TreeMap.eraseMany}

{docstring Std.TreeMap.filter}

{docstring Std.TreeMap.filterMap}

{docstring Std.TreeMap.insert}

{docstring Std.TreeMap.insertIfNew}

{docstring Std.TreeMap.getThenInsertIfNew?}

{docstring Std.TreeMap.insertMany}

{docstring Std.TreeMap.insertManyIfNewUnit}

{docstring Std.TreeMap.mergeWith}

{docstring Std.TreeMap.partition}


# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Iteration"
%%%
{docstring Std.TreeMap.iter}

{docstring Std.TreeMap.keysIter}

{docstring Std.TreeMap.valuesIter}

{docstring Std.TreeMap.map}

{docstring Std.TreeMap.all}

{docstring Std.TreeMap.any}

{docstring Std.TreeMap.foldl}

{docstring Std.TreeMap.foldlM}

{docstring Std.TreeMap.foldr}

{docstring Std.TreeMap.foldrM}

{docstring Std.TreeMap.forIn}

{docstring Std.TreeMap.forM}

# 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Conversion"
%%%
{docstring Std.TreeMap.ofList}

{docstring Std.TreeMap.toList}

{docstring Std.TreeMap.ofArray}

{docstring Std.TreeMap.toArray}

{docstring Std.TreeMap.unitOfArray}

{docstring Std.TreeMap.unitOfList}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Conversion--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.TreeMap.Raw`。

{docstring Std.TreeMap.Raw}

{docstring Std.TreeMap.Raw.WF}
