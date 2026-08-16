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

#doc (Manual) "位置" =>
%%%
tag := "string-api-valid-pos"
%%%


{docstring String.ValidPos}

# 字符串内

{docstring String.startValidPos}

{docstring String.endValidPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

# 查找

{docstring String.ValidPos.get}

{docstring String.ValidPos.get!}

{docstring String.ValidPos.get?}

{docstring String.ValidPos.set}

{docstring String.ValidPos.extract +allowMissing}

# 修改

{docstring String.ValidPos.modify}

{docstring String.ValidPos.byte}

# 调整

{docstring String.ValidPos.prev}

{docstring String.ValidPos.prev!}

{docstring String.ValidPos.prev?}

{docstring String.ValidPos.next}

{docstring String.ValidPos.next!}

{docstring String.ValidPos.next?}

# 其他字符串

{docstring String.ValidPos.cast}

{docstring String.ValidPos.ofCopy}

{docstring String.ValidPos.setOfLE}

{docstring String.ValidPos.modifyOfLE}

{docstring String.ValidPos.toSlice}
