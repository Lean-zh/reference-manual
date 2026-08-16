/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


import Std.Data.TreeSet
import Std.Data.TreeSet.Raw

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "基于树的集合" =>
%%%
tag := "TreeSet"
%%%

{docstring Std.TreeSet +hideStructureConstructor +hideFields}

# 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Creation"
%%%
{docstring Std.TreeSet.empty}

# 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Properties"
%%%
{docstring Std.TreeSet.isEmpty}

{docstring Std.TreeSet.size}

# 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Queries"
%%%
{docstring Std.TreeSet.contains}

{docstring Std.TreeSet.get}

{docstring Std.TreeSet.get!}

{docstring Std.TreeSet.get?}

{docstring Std.TreeSet.getD}

## 基于顺序的查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Queries--Ordering-Based-Queries"
%%%
{docstring Std.TreeSet.atIdx}

{docstring Std.TreeSet.atIdx!}

{docstring Std.TreeSet.atIdx?}

{docstring Std.TreeSet.atIdxD}

{docstring Std.TreeSet.getGE}

{docstring Std.TreeSet.getGE!}

{docstring Std.TreeSet.getGE?}

{docstring Std.TreeSet.getGED}

{docstring Std.TreeSet.getGT}

{docstring Std.TreeSet.getGT!}

{docstring Std.TreeSet.getGT?}

{docstring Std.TreeSet.getGTD}

{docstring Std.TreeSet.getLE}

{docstring Std.TreeSet.getLE!}

{docstring Std.TreeSet.getLE?}

{docstring Std.TreeSet.getLED}

{docstring Std.TreeSet.getLT}

{docstring Std.TreeSet.getLT!}

{docstring Std.TreeSet.getLT?}

{docstring Std.TreeSet.getLTD}


{docstring Std.TreeSet.min}

{docstring Std.TreeSet.min!}

{docstring Std.TreeSet.min?}

{docstring Std.TreeSet.minD}

{docstring Std.TreeSet.max}

{docstring Std.TreeSet.max!}

{docstring Std.TreeSet.max?}

{docstring Std.TreeSet.maxD}

# 修改


%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Modification"
%%%
{docstring Std.TreeSet.insert}

{docstring Std.TreeSet.insertMany}

{docstring Std.TreeSet.containsThenInsert}

{docstring Std.TreeSet.erase}

{docstring Std.TreeSet.eraseMany}

{docstring Std.TreeSet.filter}

{docstring Std.TreeSet.merge}

{docstring Std.TreeSet.partition}


# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Iteration"
%%%
{docstring Std.TreeSet.iter}

{docstring Std.TreeSet.all}

{docstring Std.TreeSet.any}

{docstring Std.TreeSet.foldl}

{docstring Std.TreeSet.foldlM}

{docstring Std.TreeSet.foldr}

{docstring Std.TreeSet.foldrM}

{docstring Std.TreeSet.forIn}

{docstring Std.TreeSet.forM}


# 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Conversion"
%%%
{docstring Std.TreeSet.toList}

{docstring Std.TreeSet.ofList}

{docstring Std.TreeSet.toArray}

{docstring Std.TreeSet.ofArray}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Conversion--Unbundled-Variants"
%%%
分离式集合会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.TreeSet.Raw`。

{docstring Std.TreeSet.Raw}

{docstring Std.TreeSet.Raw.WF}
