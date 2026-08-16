/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "原生子字符串" =>
%%%
tag := "string-api-substring"
%%%

原生子字符串是一种底层类型，它将字符串与其内部限定某个区域的字节位置组合在一起。
大多数代码应该改用{ref "string-api-slice"}[切片]，因为它们更安全也更方便。

{docstring String.toRawSubstring}

{docstring String.toRawSubstring'}

{docstring Substring.Raw}

# 属性

{docstring Substring.Raw.isEmpty}

{docstring Substring.Raw.bsize}

# 位置

{docstring Substring.Raw.atEnd}

{docstring Substring.Raw.posOf}

{docstring Substring.Raw.next}

{docstring Substring.Raw.nextn}

{docstring Substring.Raw.prev}

{docstring Substring.Raw.prevn}


# 归折与聚合

{docstring Substring.Raw.foldl}

{docstring Substring.Raw.foldr}

{docstring Substring.Raw.all}

{docstring Substring.Raw.any}

# 比较

{docstring Substring.Raw.beq}

{docstring Substring.Raw.sameAs}

# 前缀与后缀

{docstring Substring.Raw.commonPrefix}

{docstring Substring.Raw.commonSuffix}

{docstring Substring.Raw.dropPrefix?}

{docstring Substring.Raw.dropSuffix?}

# 查找

{docstring Substring.Raw.get}

{docstring Substring.Raw.contains}

{docstring Substring.Raw.front}


# 修改

{docstring Substring.Raw.drop}

{docstring Substring.Raw.dropWhile}

{docstring Substring.Raw.dropRight}

{docstring Substring.Raw.dropRightWhile}


{docstring Substring.Raw.take}

{docstring Substring.Raw.takeWhile}

{docstring Substring.Raw.takeRight}

{docstring Substring.Raw.takeRightWhile}

{docstring Substring.Raw.extract}

{docstring Substring.Raw.trim}

{docstring Substring.Raw.trimLeft}

{docstring Substring.Raw.trimRight}

{docstring Substring.Raw.splitOn}

{docstring Substring.Raw.repair}

# 转换

{docstring Substring.Raw.toString}

{docstring Substring.Raw.isNat}

{docstring Substring.Raw.toNat? +allowMissing}

{docstring Substring.Raw.toLegacyIterator}

{docstring Substring.Raw.toName}
