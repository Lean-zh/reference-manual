/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "谓词与关系" =>

{docstring List.IsPrefix}

:::syntax term (title := "列表前缀")
```grammar
$_ <+: $_
```

{includeDocstring List.«term_<+:_»}

:::

{docstring List.IsSuffix}

:::syntax term (title := "列表后缀")
```grammar
$_ <:+ $_
```

{includeDocstring List.«term_<:+_»}

:::

{docstring List.IsInfix}

:::syntax term (title := "列表中缀")
```grammar
$_ <:+: $_
```

{includeDocstring List.«term_<:+:_»}

:::

{docstring List.Sublist}

::: syntax term (title := "子列表") (namespace := List)
```grammar
$_ <+ $_
```

{includeDocstring List.«term_<+_»}

只有在打开 `List` 命名空间时，此语法才可用。
:::

{docstring List.Perm}

:::syntax term (title := "列表置换") (namespace := List)
```grammar
$_ ~ $_
```

{includeDocstring List.«term_~_»}

只有在打开 `List` 命名空间时，此语法才可用。
:::

{docstring List.Pairwise}

{docstring List.Nodup}

{docstring List.Lex}

{docstring List.Mem}
