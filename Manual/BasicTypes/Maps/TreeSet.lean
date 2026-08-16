/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G3


import Std.Data.TreeSet
import Std.Data.TreeSet.Raw

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "基于树的集合" =>
%%%
tag := "TreeSet"
%%%

{zhdocstring Std.TreeSet Manual.ZhDocString.Ch19Ch20.G3.c137 +hideStructureConstructor +hideFields}

# 创建

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Creation"
%%%
{zhdocstring Std.TreeSet.empty Manual.ZhDocString.Ch19Ch20.G3.c138}

# 性质

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Properties"
%%%
{zhdocstring Std.TreeSet.isEmpty Manual.ZhDocString.Ch19Ch20.G3.c139}

{zhdocstring Std.TreeSet.size Manual.ZhDocString.Ch19Ch20.G3.c140}

# 查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Queries"
%%%
{zhdocstring Std.TreeSet.contains Manual.ZhDocString.Ch19Ch20.G3.c141}

{zhdocstring Std.TreeSet.get Manual.ZhDocString.Ch19Ch20.G3.c142}

{zhdocstring Std.TreeSet.get! Manual.ZhDocString.Ch19Ch20.G3.c143}

{zhdocstring Std.TreeSet.get? Manual.ZhDocString.Ch19Ch20.G3.c144}

{zhdocstring Std.TreeSet.getD Manual.ZhDocString.Ch19Ch20.G3.c145}

## 基于顺序的查询

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Queries--Ordering-Based-Queries"
%%%
{zhdocstring Std.TreeSet.atIdx Manual.ZhDocString.Ch19Ch20.G3.c146}

{zhdocstring Std.TreeSet.atIdx! Manual.ZhDocString.Ch19Ch20.G3.c147}

{zhdocstring Std.TreeSet.atIdx? Manual.ZhDocString.Ch19Ch20.G3.c148}

{zhdocstring Std.TreeSet.atIdxD Manual.ZhDocString.Ch19Ch20.G3.c149}

{zhdocstring Std.TreeSet.getGE Manual.ZhDocString.Ch19Ch20.G3.c150}

{zhdocstring Std.TreeSet.getGE! Manual.ZhDocString.Ch19Ch20.G3.c151}

{zhdocstring Std.TreeSet.getGE? Manual.ZhDocString.Ch19Ch20.G3.c152}

{zhdocstring Std.TreeSet.getGED Manual.ZhDocString.Ch19Ch20.G3.c153}

{zhdocstring Std.TreeSet.getGT Manual.ZhDocString.Ch19Ch20.G3.c154}

{zhdocstring Std.TreeSet.getGT! Manual.ZhDocString.Ch19Ch20.G3.c155}

{zhdocstring Std.TreeSet.getGT? Manual.ZhDocString.Ch19Ch20.G3.c156}

{zhdocstring Std.TreeSet.getGTD Manual.ZhDocString.Ch19Ch20.G3.c157}

{zhdocstring Std.TreeSet.getLE Manual.ZhDocString.Ch19Ch20.G3.c158}

{zhdocstring Std.TreeSet.getLE! Manual.ZhDocString.Ch19Ch20.G3.c159}

{zhdocstring Std.TreeSet.getLE? Manual.ZhDocString.Ch19Ch20.G3.c160}

{zhdocstring Std.TreeSet.getLED Manual.ZhDocString.Ch19Ch20.G3.c161}

{zhdocstring Std.TreeSet.getLT Manual.ZhDocString.Ch19Ch20.G3.c162}

{zhdocstring Std.TreeSet.getLT! Manual.ZhDocString.Ch19Ch20.G3.c163}

{zhdocstring Std.TreeSet.getLT? Manual.ZhDocString.Ch19Ch20.G3.c164}

{zhdocstring Std.TreeSet.getLTD Manual.ZhDocString.Ch19Ch20.G3.c165}


{zhdocstring Std.TreeSet.min Manual.ZhDocString.Ch19Ch20.G3.c166}

{zhdocstring Std.TreeSet.min! Manual.ZhDocString.Ch19Ch20.G3.c167}

{zhdocstring Std.TreeSet.min? Manual.ZhDocString.Ch19Ch20.G3.c168}

{zhdocstring Std.TreeSet.minD Manual.ZhDocString.Ch19Ch20.G3.c169}

{zhdocstring Std.TreeSet.max Manual.ZhDocString.Ch19Ch20.G3.c170}

{zhdocstring Std.TreeSet.max! Manual.ZhDocString.Ch19Ch20.G3.c171}

{zhdocstring Std.TreeSet.max? Manual.ZhDocString.Ch19Ch20.G3.c172}

{zhdocstring Std.TreeSet.maxD Manual.ZhDocString.Ch19Ch20.G3.c173}

# 修改


%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Modification"
%%%
{zhdocstring Std.TreeSet.insert Manual.ZhDocString.Ch19Ch20.G3.c174}

{zhdocstring Std.TreeSet.insertMany Manual.ZhDocString.Ch19Ch20.G3.c175}

{zhdocstring Std.TreeSet.containsThenInsert Manual.ZhDocString.Ch19Ch20.G3.c176}

{zhdocstring Std.TreeSet.erase Manual.ZhDocString.Ch19Ch20.G3.c177}

{zhdocstring Std.TreeSet.eraseMany Manual.ZhDocString.Ch19Ch20.G3.c178}

{zhdocstring Std.TreeSet.filter Manual.ZhDocString.Ch19Ch20.G3.c179}

{zhdocstring Std.TreeSet.merge Manual.ZhDocString.Ch19Ch20.G3.c180}

{zhdocstring Std.TreeSet.partition Manual.ZhDocString.Ch19Ch20.G3.c181}


# 迭代

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Iteration"
%%%
{zhdocstring Std.TreeSet.iter Manual.ZhDocString.Ch19Ch20.G3.c182}

{zhdocstring Std.TreeSet.all Manual.ZhDocString.Ch19Ch20.G3.c183}

{zhdocstring Std.TreeSet.any Manual.ZhDocString.Ch19Ch20.G3.c184}

{zhdocstring Std.TreeSet.foldl Manual.ZhDocString.Ch19Ch20.G3.c185}

{zhdocstring Std.TreeSet.foldlM Manual.ZhDocString.Ch19Ch20.G3.c186}

{zhdocstring Std.TreeSet.foldr Manual.ZhDocString.Ch19Ch20.G3.c187}

{zhdocstring Std.TreeSet.foldrM Manual.ZhDocString.Ch19Ch20.G3.c188}

{zhdocstring Std.TreeSet.forIn Manual.ZhDocString.Ch19Ch20.G3.c189}

{zhdocstring Std.TreeSet.forM Manual.ZhDocString.Ch19Ch20.G3.c190}


# 转换

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Conversion"
%%%
{zhdocstring Std.TreeSet.toList Manual.ZhDocString.Ch19Ch20.G3.c191}

{zhdocstring Std.TreeSet.ofList Manual.ZhDocString.Ch19Ch20.G3.c192}

{zhdocstring Std.TreeSet.toArray Manual.ZhDocString.Ch19Ch20.G3.c193}

{zhdocstring Std.TreeSet.ofArray Manual.ZhDocString.Ch19Ch20.G3.c194}

## 分离式变体

%%%
tag := "Lean-__________________--Basic-Types--Maps-and-Sets--Tree-Based-Sets--Conversion--Unbundled-Variants"
%%%
分离式集合会将良构性证明与数据本身分开。
这主要在定义 {ref "raw-data"}[嵌套归纳类型] 时有用。
要使用这些变体，请导入模块 `Std.TreeSet.Raw`。

{zhdocstring Std.TreeSet.Raw Manual.ZhDocString.Ch19Ch20.G3.c195}

{zhdocstring Std.TreeSet.Raw.WF Manual.ZhDocString.Ch19Ch20.G3.c196}
