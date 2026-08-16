/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "原始子字符串" =>
%%%
tag := "string-api-substring"
%%%

原生子字符串是一种底层类型，它将字符串与其内部限定某个区域的字节位置组合在一起。
大多数代码应该改用{ref "string-api-slice"}[切片]，因为它们更安全也更方便。

{zhdocstring String.toRawSubstring Manual.ZhDocString.Ch19Ch20.G9.c051}

{zhdocstring String.toRawSubstring' Manual.ZhDocString.Ch19Ch20.G9.c052}

{zhdocstring Substring.Raw Manual.ZhDocString.Ch19Ch20.G9.c053}

# 属性

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Properties"
%%%
{zhdocstring Substring.Raw.isEmpty Manual.ZhDocString.Ch19Ch20.G9.c054}

{zhdocstring Substring.Raw.bsize Manual.ZhDocString.Ch19Ch20.G9.c055}

# 位置

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Positions"
%%%
{zhdocstring Substring.Raw.atEnd Manual.ZhDocString.Ch19Ch20.G9.c056}

{zhdocstring Substring.Raw.posOf Manual.ZhDocString.Ch19Ch20.G9.c057}

{zhdocstring Substring.Raw.next Manual.ZhDocString.Ch19Ch20.G9.c058}

{zhdocstring Substring.Raw.nextn Manual.ZhDocString.Ch19Ch20.G9.c059}

{zhdocstring Substring.Raw.prev Manual.ZhDocString.Ch19Ch20.G9.c060}

{zhdocstring Substring.Raw.prevn Manual.ZhDocString.Ch19Ch20.G9.c061}


# 归折与聚合

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Folds-and-Aggregation"
%%%
{zhdocstring Substring.Raw.foldl Manual.ZhDocString.Ch19Ch20.G9.c062}

{zhdocstring Substring.Raw.foldr Manual.ZhDocString.Ch19Ch20.G9.c063}

{zhdocstring Substring.Raw.all Manual.ZhDocString.Ch19Ch20.G9.c064}

{zhdocstring Substring.Raw.any Manual.ZhDocString.Ch19Ch20.G9.c065}

# 比较

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Comparisons"
%%%
{zhdocstring Substring.Raw.beq Manual.ZhDocString.Ch19Ch20.G9.c066}

{zhdocstring Substring.Raw.sameAs Manual.ZhDocString.Ch19Ch20.G9.c067}

# 前缀与后缀

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Prefix-and-Suffix"
%%%
{zhdocstring Substring.Raw.commonPrefix Manual.ZhDocString.Ch19Ch20.G9.c068}

{zhdocstring Substring.Raw.commonSuffix Manual.ZhDocString.Ch19Ch20.G9.c069}

{zhdocstring Substring.Raw.dropPrefix? Manual.ZhDocString.Ch19Ch20.G9.c070}

{zhdocstring Substring.Raw.dropSuffix? Manual.ZhDocString.Ch19Ch20.G9.c071}

# 查找

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Lookups"
%%%
{zhdocstring Substring.Raw.get Manual.ZhDocString.Ch19Ch20.G9.c072}

{zhdocstring Substring.Raw.contains Manual.ZhDocString.Ch19Ch20.G9.c073}

{zhdocstring Substring.Raw.front Manual.ZhDocString.Ch19Ch20.G9.c074}


# 修改

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Modifications"
%%%
{zhdocstring Substring.Raw.drop Manual.ZhDocString.Ch19Ch20.G9.c075}

{zhdocstring Substring.Raw.dropWhile Manual.ZhDocString.Ch19Ch20.G9.c076}

{zhdocstring Substring.Raw.dropRight Manual.ZhDocString.Ch19Ch20.G9.c077}

{zhdocstring Substring.Raw.dropRightWhile Manual.ZhDocString.Ch19Ch20.G9.c078}


{zhdocstring Substring.Raw.take Manual.ZhDocString.Ch19Ch20.G9.c079}

{zhdocstring Substring.Raw.takeWhile Manual.ZhDocString.Ch19Ch20.G9.c080}

{zhdocstring Substring.Raw.takeRight Manual.ZhDocString.Ch19Ch20.G9.c081}

{zhdocstring Substring.Raw.takeRightWhile Manual.ZhDocString.Ch19Ch20.G9.c082}

{zhdocstring Substring.Raw.extract Manual.ZhDocString.Ch19Ch20.G9.c083}

{zhdocstring Substring.Raw.trim Manual.ZhDocString.Ch19Ch20.G9.c084}

{zhdocstring Substring.Raw.trimLeft Manual.ZhDocString.Ch19Ch20.G9.c085}

{zhdocstring Substring.Raw.trimRight Manual.ZhDocString.Ch19Ch20.G9.c086}

{zhdocstring Substring.Raw.splitOn Manual.ZhDocString.Ch19Ch20.G9.c087}

{zhdocstring Substring.Raw.repair Manual.ZhDocString.Ch19Ch20.G9.c088}

# 转换

%%%
tag := "Lean-__________________--Basic-Types--Strings--API-Reference--Raw-Substrings--Conversions"
%%%
{zhdocstring Substring.Raw.toString Manual.ZhDocString.Ch19Ch20.G9.c089}

{zhdocstring Substring.Raw.isNat Manual.ZhDocString.Ch19Ch20.G9.c090}

{zhdocstring Substring.Raw.toNat? Manual.ZhDocString.Ch19Ch20.G9.c091 +allowMissing}

{zhdocstring Substring.Raw.toLegacyIterator Manual.ZhDocString.Ch19Ch20.G9.c092}

{zhdocstring Substring.Raw.toName Manual.ZhDocString.Ch19Ch20.G9.c093}
