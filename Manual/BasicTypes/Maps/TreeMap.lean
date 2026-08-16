/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G6


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

{zhdocstring Std.TreeMap Manual.ZhDocString.Ch19Ch20.G6.c001 +hideFields +hideStructureConstructor}

# 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Creation"
%%%
{zhdocstring Std.TreeMap.empty Manual.ZhDocString.Ch19Ch20.G6.c002}

# 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Properties"
%%%
{zhdocstring Std.TreeMap.size Manual.ZhDocString.Ch19Ch20.G6.c003}

{zhdocstring Std.TreeMap.isEmpty Manual.ZhDocString.Ch19Ch20.G6.c004}


# 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Queries"
%%%
{zhdocstring Std.TreeMap.contains Manual.ZhDocString.Ch19Ch20.G6.c005}

{zhdocstring Std.TreeMap.get Manual.ZhDocString.Ch19Ch20.G6.c006}

{zhdocstring Std.TreeMap.get! Manual.ZhDocString.Ch19Ch20.G6.c007}

{zhdocstring Std.TreeMap.get? Manual.ZhDocString.Ch19Ch20.G6.c008}

{zhdocstring Std.TreeMap.getD Manual.ZhDocString.Ch19Ch20.G6.c009}

{zhdocstring Std.TreeMap.getKey Manual.ZhDocString.Ch19Ch20.G6.c010}

{zhdocstring Std.TreeMap.getKey! Manual.ZhDocString.Ch19Ch20.G6.c011}

{zhdocstring Std.TreeMap.getKey? Manual.ZhDocString.Ch19Ch20.G6.c012}

{zhdocstring Std.TreeMap.getKeyD Manual.ZhDocString.Ch19Ch20.G6.c013}

{zhdocstring Std.TreeMap.keys Manual.ZhDocString.Ch19Ch20.G6.c014}

{zhdocstring Std.TreeMap.keysArray Manual.ZhDocString.Ch19Ch20.G6.c015}

{zhdocstring Std.TreeMap.values Manual.ZhDocString.Ch19Ch20.G6.c016}

{zhdocstring Std.TreeMap.valuesArray Manual.ZhDocString.Ch19Ch20.G6.c017}

## 基于顺序的查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Queries--Ordering-Based-Queries"
%%%
{zhdocstring Std.TreeMap.entryAtIdx Manual.ZhDocString.Ch19Ch20.G6.c018}

{zhdocstring Std.TreeMap.entryAtIdx! Manual.ZhDocString.Ch19Ch20.G6.c019}

{zhdocstring Std.TreeMap.entryAtIdx? Manual.ZhDocString.Ch19Ch20.G6.c020}

{zhdocstring Std.TreeMap.entryAtIdxD Manual.ZhDocString.Ch19Ch20.G6.c021}

{zhdocstring Std.TreeMap.getEntryGE Manual.ZhDocString.Ch19Ch20.G6.c022}

{zhdocstring Std.TreeMap.getEntryGE! Manual.ZhDocString.Ch19Ch20.G6.c023}

{zhdocstring Std.TreeMap.getEntryGE? Manual.ZhDocString.Ch19Ch20.G6.c024}

{zhdocstring Std.TreeMap.getEntryGED Manual.ZhDocString.Ch19Ch20.G6.c025}

{zhdocstring Std.TreeMap.getEntryGT Manual.ZhDocString.Ch19Ch20.G6.c026}

{zhdocstring Std.TreeMap.getEntryGT! Manual.ZhDocString.Ch19Ch20.G6.c027}

{zhdocstring Std.TreeMap.getEntryGT? Manual.ZhDocString.Ch19Ch20.G6.c028}

{zhdocstring Std.TreeMap.getEntryGTD Manual.ZhDocString.Ch19Ch20.G6.c029}

{zhdocstring Std.TreeMap.getEntryLE Manual.ZhDocString.Ch19Ch20.G6.c030}

{zhdocstring Std.TreeMap.getEntryLE! Manual.ZhDocString.Ch19Ch20.G6.c031}

{zhdocstring Std.TreeMap.getEntryLE? Manual.ZhDocString.Ch19Ch20.G6.c032}

{zhdocstring Std.TreeMap.getEntryLED Manual.ZhDocString.Ch19Ch20.G6.c033}

{zhdocstring Std.TreeMap.getEntryLT Manual.ZhDocString.Ch19Ch20.G6.c034}

{zhdocstring Std.TreeMap.getEntryLT! Manual.ZhDocString.Ch19Ch20.G6.c035}

{zhdocstring Std.TreeMap.getEntryLT? Manual.ZhDocString.Ch19Ch20.G6.c036}

{zhdocstring Std.TreeMap.getEntryLTD Manual.ZhDocString.Ch19Ch20.G6.c037}

{zhdocstring Std.TreeMap.getKeyGE Manual.ZhDocString.Ch19Ch20.G6.c038}

{zhdocstring Std.TreeMap.getKeyGE! Manual.ZhDocString.Ch19Ch20.G6.c039}

{zhdocstring Std.TreeMap.getKeyGE? Manual.ZhDocString.Ch19Ch20.G6.c040}

{zhdocstring Std.TreeMap.getKeyGED Manual.ZhDocString.Ch19Ch20.G6.c041}

{zhdocstring Std.TreeMap.getKeyGT Manual.ZhDocString.Ch19Ch20.G6.c042}

{zhdocstring Std.TreeMap.getKeyGT! Manual.ZhDocString.Ch19Ch20.G6.c043}

{zhdocstring Std.TreeMap.getKeyGT? Manual.ZhDocString.Ch19Ch20.G6.c044}

{zhdocstring Std.TreeMap.getKeyGTD Manual.ZhDocString.Ch19Ch20.G6.c045}

{zhdocstring Std.TreeMap.getKeyLE Manual.ZhDocString.Ch19Ch20.G6.c046}

{zhdocstring Std.TreeMap.getKeyLE! Manual.ZhDocString.Ch19Ch20.G6.c047}

{zhdocstring Std.TreeMap.getKeyLE? Manual.ZhDocString.Ch19Ch20.G6.c048}

{zhdocstring Std.TreeMap.getKeyLED Manual.ZhDocString.Ch19Ch20.G6.c049}

{zhdocstring Std.TreeMap.getKeyLT Manual.ZhDocString.Ch19Ch20.G6.c050}

{zhdocstring Std.TreeMap.getKeyLT! Manual.ZhDocString.Ch19Ch20.G6.c051}

{zhdocstring Std.TreeMap.getKeyLT? Manual.ZhDocString.Ch19Ch20.G6.c052}

{zhdocstring Std.TreeMap.getKeyLTD Manual.ZhDocString.Ch19Ch20.G6.c053}

{zhdocstring Std.TreeMap.keyAtIdx Manual.ZhDocString.Ch19Ch20.G6.c054}

{zhdocstring Std.TreeMap.keyAtIdx! Manual.ZhDocString.Ch19Ch20.G6.c055}

{zhdocstring Std.TreeMap.keyAtIdx? Manual.ZhDocString.Ch19Ch20.G6.c056}

{zhdocstring Std.TreeMap.keyAtIdxD Manual.ZhDocString.Ch19Ch20.G6.c057}

{zhdocstring Std.TreeMap.minEntry Manual.ZhDocString.Ch19Ch20.G6.c058}

{zhdocstring Std.TreeMap.minEntry! Manual.ZhDocString.Ch19Ch20.G6.c059}

{zhdocstring Std.TreeMap.minEntry? Manual.ZhDocString.Ch19Ch20.G6.c060}

{zhdocstring Std.TreeMap.minEntryD Manual.ZhDocString.Ch19Ch20.G6.c061}

{zhdocstring Std.TreeMap.minKey Manual.ZhDocString.Ch19Ch20.G6.c062}

{zhdocstring Std.TreeMap.minKey! Manual.ZhDocString.Ch19Ch20.G6.c063}

{zhdocstring Std.TreeMap.minKey? Manual.ZhDocString.Ch19Ch20.G6.c064}

{zhdocstring Std.TreeMap.minKeyD Manual.ZhDocString.Ch19Ch20.G6.c065}

{zhdocstring Std.TreeMap.maxEntry Manual.ZhDocString.Ch19Ch20.G6.c066}

{zhdocstring Std.TreeMap.maxEntry! Manual.ZhDocString.Ch19Ch20.G6.c067}

{zhdocstring Std.TreeMap.maxEntry? Manual.ZhDocString.Ch19Ch20.G6.c068}

{zhdocstring Std.TreeMap.maxEntryD Manual.ZhDocString.Ch19Ch20.G6.c069}

{zhdocstring Std.TreeMap.maxKey Manual.ZhDocString.Ch19Ch20.G6.c070}

{zhdocstring Std.TreeMap.maxKey! Manual.ZhDocString.Ch19Ch20.G6.c071}

{zhdocstring Std.TreeMap.maxKey? Manual.ZhDocString.Ch19Ch20.G6.c072}

{zhdocstring Std.TreeMap.maxKeyD Manual.ZhDocString.Ch19Ch20.G6.c073}


# 修改

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Modification"
%%%
{zhdocstring Std.TreeMap.alter Manual.ZhDocString.Ch19Ch20.G6.c074}

{zhdocstring Std.TreeMap.modify Manual.ZhDocString.Ch19Ch20.G6.c075}

{zhdocstring Std.TreeMap.containsThenInsert Manual.ZhDocString.Ch19Ch20.G6.c076}

{zhdocstring Std.TreeMap.containsThenInsertIfNew Manual.ZhDocString.Ch19Ch20.G6.c077}

{zhdocstring Std.TreeMap.erase Manual.ZhDocString.Ch19Ch20.G6.c078}

{zhdocstring Std.TreeMap.eraseMany Manual.ZhDocString.Ch19Ch20.G6.c079}

{zhdocstring Std.TreeMap.filter Manual.ZhDocString.Ch19Ch20.G6.c080}

{zhdocstring Std.TreeMap.filterMap Manual.ZhDocString.Ch19Ch20.G6.c081}

{zhdocstring Std.TreeMap.insert Manual.ZhDocString.Ch19Ch20.G6.c082}

{zhdocstring Std.TreeMap.insertIfNew Manual.ZhDocString.Ch19Ch20.G6.c083}

{zhdocstring Std.TreeMap.getThenInsertIfNew? Manual.ZhDocString.Ch19Ch20.G6.c084}

{zhdocstring Std.TreeMap.insertMany Manual.ZhDocString.Ch19Ch20.G6.c085}

{zhdocstring Std.TreeMap.insertManyIfNewUnit Manual.ZhDocString.Ch19Ch20.G6.c086}

{zhdocstring Std.TreeMap.mergeWith Manual.ZhDocString.Ch19Ch20.G6.c087}

{zhdocstring Std.TreeMap.partition Manual.ZhDocString.Ch19Ch20.G6.c088}


# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Iteration"
%%%
{zhdocstring Std.TreeMap.iter Manual.ZhDocString.Ch19Ch20.G6.c089}

{zhdocstring Std.TreeMap.keysIter Manual.ZhDocString.Ch19Ch20.G6.c090}

{zhdocstring Std.TreeMap.valuesIter Manual.ZhDocString.Ch19Ch20.G6.c091}

{zhdocstring Std.TreeMap.map Manual.ZhDocString.Ch19Ch20.G6.c092}

{zhdocstring Std.TreeMap.all Manual.ZhDocString.Ch19Ch20.G6.c093}

{zhdocstring Std.TreeMap.any Manual.ZhDocString.Ch19Ch20.G6.c094}

{zhdocstring Std.TreeMap.foldl Manual.ZhDocString.Ch19Ch20.G6.c095}

{zhdocstring Std.TreeMap.foldlM Manual.ZhDocString.Ch19Ch20.G6.c096}

{zhdocstring Std.TreeMap.foldr Manual.ZhDocString.Ch19Ch20.G6.c097}

{zhdocstring Std.TreeMap.foldrM Manual.ZhDocString.Ch19Ch20.G6.c098}

{zhdocstring Std.TreeMap.forIn Manual.ZhDocString.Ch19Ch20.G6.c099}

{zhdocstring Std.TreeMap.forM Manual.ZhDocString.Ch19Ch20.G6.c100}

# 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Conversion"
%%%
{zhdocstring Std.TreeMap.ofList Manual.ZhDocString.Ch19Ch20.G6.c101}

{zhdocstring Std.TreeMap.toList Manual.ZhDocString.Ch19Ch20.G6.c102}

{zhdocstring Std.TreeMap.ofArray Manual.ZhDocString.Ch19Ch20.G6.c103}

{zhdocstring Std.TreeMap.toArray Manual.ZhDocString.Ch19Ch20.G6.c104}

{zhdocstring Std.TreeMap.unitOfArray Manual.ZhDocString.Ch19Ch20.G6.c105}

{zhdocstring Std.TreeMap.unitOfList Manual.ZhDocString.Ch19Ch20.G6.c106}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Maps--Conversion--Unbundled-Variants"
%%%
分离式映射会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.TreeMap.Raw`。

{zhdocstring Std.TreeMap.Raw Manual.ZhDocString.Ch19Ch20.G6.c107}

{zhdocstring Std.TreeMap.Raw.WF Manual.ZhDocString.Ch19Ch20.G6.c108}
