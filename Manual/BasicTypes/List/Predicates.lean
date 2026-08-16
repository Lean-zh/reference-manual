/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
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

#doc (Manual) "谓词与关系" =>
%%%
tag := "Lean-__________________--Basic-Types--Linked-Lists--API-Reference--Predicates-and-Relations"
%%%

{zhdocstring List.IsPrefix Manual.ZhDocString.Ch19Ch20.G9.c191}

:::syntax term (title := "列表前缀")
```grammar
$_ <+: $_
```

{includeDocstring List.«term_<+:_»}

:::

{zhdocstring List.IsSuffix Manual.ZhDocString.Ch19Ch20.G9.c192}

:::syntax term (title := "列表后缀")
```grammar
$_ <:+ $_
```

{includeDocstring List.«term_<:+_»}

:::

{zhdocstring List.IsInfix Manual.ZhDocString.Ch19Ch20.G9.c193}

:::syntax term (title := "列表中缀")
```grammar
$_ <:+: $_
```

{includeDocstring List.«term_<:+:_»}

:::

{zhdocstring List.Sublist Manual.ZhDocString.Ch19Ch20.G9.c194}

::: syntax term (title := "子列表") (namespace := List)
```grammar
$_ <+ $_
```

{includeDocstring List.«term_<+_»}

只有在打开 `List` 命名空间时，此语法才可用。
:::

{zhdocstring List.Perm Manual.ZhDocString.Ch19Ch20.G9.c195}

:::syntax term (title := "列表置换") (namespace := List)
```grammar
$_ ~ $_
```

{includeDocstring List.«term_~_»}

只有在打开 `List` 命名空间时，此语法才可用。
:::

{zhdocstring List.Pairwise Manual.ZhDocString.Ch19Ch20.G9.c196}

{zhdocstring List.Nodup Manual.ZhDocString.Ch19Ch20.G9.c197}

{zhdocstring List.Lex Manual.ZhDocString.Ch19Ch20.G9.c198}

{zhdocstring List.Mem Manual.ZhDocString.Ch19Ch20.G9.c199}
