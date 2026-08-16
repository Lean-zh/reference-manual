/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G9

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "字符" =>
%%%
tag := "Char"
%%%

字符由 {name}`Char` 类型表示，它可以是任何 Unicode [标量值](http://www.unicode.org/glossary/#unicode_scalar_value)。
{ref "String"}[字符串]是 UTF-8 编码的字节数组，而字符则由完整的 32 位值表示。
Lean 为字符字面量提供了特殊的{ref "char-syntax"}[语法]。

# 逻辑模型
%%%
tag := "char-model"
%%%

从 Lean 的逻辑角度来看，字符由一个 32 位无符号整数和一个证明它是有效 Unicode 标量值的证明组成。

{zhdocstring Char Manual.ZhDocString.Ch19Ch20.G9.c142}

# 运行时表示
%%%
tag := "char-runtime"
%%%

作为一个{ref "inductive-types-trivial-wrappers"}[平凡包装器]，字符的表示方式与 {lean}`UInt32` 完全相同。
特别地，在单态语境中，字符被表示为 32 位立即数。
换句话说，类型为 {lean}`Char` 的构造子或结构体的字段不需要间接引用即可访问。
在多态语境中，字符是{tech (key := "boxed")}[装箱]的。


# 语法
%%%
tag := "char-syntax"
%%%

字符字面量由包含在单引号（`'`，Unicode `'APOSTROPHE' (U+0027)`）内的单个字符或转义序列组成。
在这些单引号之间，字符字面量可以包含除 `'` 之外的字符，包括换行符，这些字符将被字面量地包含进来（无论文件编码和平台如何，Lean 源文件中的所有换行符都会被解释为 `'\n'`）。
特殊字符可以使用反斜杠进行转义，因此 `'\''` 是一个包含单引号的字符字面量。
接受以下形式的转义序列：

: `\r`, `\n`, `\t`, `\\`, `\"`, `\'`

  这些转义序列具有通常的含义，分别映射到 `CR`、`LF`、制表符、反斜杠、双引号和单引号。

: `\xNN`

  当 `NN` 是两个十六进制数字的序列时，此转义序列表示其 Unicode 代码点由该两位十六进制代码指定的字符。

: `\uNNNN`

  当 `NN` 是四个十六进制数字的序列时，此转义序列表示其 Unicode 代码点由该四位十六进制代码指定的字符。


# API 参考
%%%
tag := "char-api"
%%%

## 转换

%%%
tag := "Lean-__________________--Basic-Types--Characters--API-Reference--Conversions"
%%%
{zhdocstring Char.ofNat Manual.ZhDocString.Ch19Ch20.G9.c143}

{zhdocstring Char.toNat Manual.ZhDocString.Ch19Ch20.G9.c144}

{zhdocstring Char.isValidCharNat Manual.ZhDocString.Ch19Ch20.G9.c145}

{zhdocstring Char.ofUInt8 Manual.ZhDocString.Ch19Ch20.G9.c146}

{zhdocstring Char.toUInt8 Manual.ZhDocString.Ch19Ch20.G9.c147}


有两种方法可以将字符转换为字符串。
{name}`Char.toString` 将字符转换为仅包含该字符的单字符字符串，而 {name}`Char.quote` 将字符转换为相应字符字面量的字符串表示。

{zhdocstring Char.toString Manual.ZhDocString.Ch19Ch20.G9.c148}

{zhdocstring Char.quote Manual.ZhDocString.Ch19Ch20.G9.c149}

:::example "从字符到字符串"

{name}`Char.toString` 生成一个仅包含该字符的字符串：

```lean (name := e)
#eval 'e'.toString
```
```leanOutput e
"e"
```

```lean (name := e')
#eval '\x65'.toString
```
```leanOutput e'
"e"
```

```lean (name := n')
#eval '"'.toString
```
```leanOutput n'
"\""
```

{name}`Char.quote` 生成一个包含经过适当转义的字符字面量的字符串：
```lean (name := eq)
#eval 'e'.quote
```
```leanOutput eq
"'e'"
```

```lean (name := eq')
#eval '\x65'.quote
```
```leanOutput eq'
"'e'"
```

```lean (name := nq')
#eval '"'.quote
```
```leanOutput nq'
"'\\\"'"
```


:::




## 字符类
%%%
tag := "char-api-classes"
%%%

{zhdocstring Char.isAlpha Manual.ZhDocString.Ch19Ch20.G9.c150}

{zhdocstring Char.isAlphanum Manual.ZhDocString.Ch19Ch20.G9.c151}

{zhdocstring Char.isDigit Manual.ZhDocString.Ch19Ch20.G9.c152}

{zhdocstring Char.isLower Manual.ZhDocString.Ch19Ch20.G9.c153}

{zhdocstring Char.isUpper Manual.ZhDocString.Ch19Ch20.G9.c154}

{zhdocstring Char.isWhitespace Manual.ZhDocString.Ch19Ch20.G9.c155}

## 大小写转换

%%%
tag := "Lean-__________________--Basic-Types--Characters--API-Reference--Case-Conversion"
%%%
{zhdocstring Char.toUpper Manual.ZhDocString.Ch19Ch20.G9.c156}

{zhdocstring Char.toLower Manual.ZhDocString.Ch19Ch20.G9.c157}

## 比较

%%%
tag := "Lean-__________________--Basic-Types--Characters--API-Reference--Comparisons"
%%%
{zhdocstring Char.le Manual.ZhDocString.Ch19Ch20.G9.c158}

{zhdocstring Char.lt Manual.ZhDocString.Ch19Ch20.G9.c159}

## Unicode

%%%
tag := "Lean-__________________--Basic-Types--Characters--API-Reference--Unicode"
%%%
{zhdocstring Char.utf8Size Manual.ZhDocString.Ch19Ch20.G9.c160}
