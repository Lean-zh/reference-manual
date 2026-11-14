/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

-- Needed for the if-then-else normalization example.
import Std.Data.TreeMap
import Std.Data.HashMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External


set_option pp.rawOnError true

set_option linter.typography.quotes true
set_option linter.typography.dashes true


open Manual (comment)

#doc (Manual) "外部内核" =>
%%%
file := "External-Kernels"
tag := "external-kernels"
htmlSplit := .never
%%%

Lean 既是具有强大自动化能力的证明助手，也是一门可扩展、功能完备的编程语言。
然而，所有能在 Lean 中证明的定理都会由{tech (key := "elaborator")}[精译器]转换到一个小得多的{ref "type-system"}[核心类型论]中。
Lean {tech (key := "kernel")}[内核]是用于检查该核心理论的小型、健壮的检查器。

如{ref "validating-proofs"}[验证 Lean 证明一章]所述，Lean 的设计允许独立实现的内核检查其核心理论。
这提供了额外一层保障。

:::paragraph
Lean 发行版包含以下独立实现的内核：

: Nanoda ({executable +def}`nanoda_bin`)

  Chris Bailey 使用 Rust 实现的 Lean 内核（[源码](https://github.com/ammkrn/nanoda_lib)）。

: {executable +def}`lean4lean`

  Mario Carneiro 将官方内核移植到 Lean 的实现（[源码](https://github.com/digama0/lean4lean)）。
  其中的重要部分已相对于 Lean 类型论的规约进行形式化验证。

: {executable +def}`con-leche`

  Lean FRO 使用 Lean 实现的 Lean 内核（[源码](https://github.com/leanprover/con-leche)）。
  它包含一个经机器检查的证明：它接受的每个环境都具有集合论模型，因此它绝不会接受 {name}`False` 的证明。

: {executable +def}`con-ron`

  Lean FRO 将 {executable}`con-leche` 移植到 Rust 的实现（[源码](https://github.com/leanprover/con-ron)）。

:::

内核不需要能够调用任何特定的外部 API，也不需要使用任何特定的数据结构。
它们接收一个以换行符分隔的 JSON 文件，其中包含所有待检查的项和定义。

# Lean 导出格式
%%%
file := "Lean-Export-Format"
tag := "export-format"
%%%

本节描述导出格式的 3.1.0 版本。
导出文件采用[以换行符分隔的 JSON](https://github.com/ndjson/ndjson-spec)：每行包含一个对象，对象本身不含换行符。
导出的 `.ndjson` 文件以{exportType "Initial metadata object"}[初始元数据对象]开头，其中包含导出器、Lean 和导出格式的版本信息：

```exportFormat "Initial metadata object"
{
  "meta": {
    "exporter": {
      "name": string,
      "version": string
    },
    "lean": {
      "githash": string,
      "version": string
    },
    "format": {
      "version": string
    }
  }
}
```

元数据对象之后是一系列带整数标号的基本对象（{name Lean.Name}`Name`、{name Lean.Level}`Level` 或 {name Lean.Expr}`Expr`）和声明（{exportType "Axiom"}[公理]、{exportType "Definition"}[定义]、{exportType "Theorem"}[定理]、{exportType "Opaque"}[不透明声明]、{exportType "Quotient"}[商类型声明]、{exportType "Inductive Declaration"}[归纳声明]，后者包含{exportType "ConstructorVal"}[构造器]和{exportType "RecursorVal"}[递归器]）；同一个归纳声明或相互归纳声明的相关元素（归纳规约、构造器和递归器）会被编组在一起。

导出格式包含一些冗余信息；完整的外部检查器可能会忽略这些信息，或仅验证它们（例如递归器的类型）。
包含这些信息是为了方便需要获取全部常量及其类型的其他工具（例如依赖分析工具）。

这些元素的构造方式如下所述。
为便于阅读，示例中加入了换行；请注意，NDJSON 格式要求这些 JSON 对象在实际输出时不包含任何换行。

## 索引
%%%
file := "Indices"
tag := "Lean-__________________--____________--Lean-____________--______"
%%%

:::paragraph
导出格式使用显式索引来引用名称、层级和表达式。
每种对象各自占用一张表，不同表可以复用相同的索引值。
同一张表内的每个索引都是唯一的。
本规约使用以下类型描述引用表项的自然数：

: {exportType +def}`NameIdx`

  名称表中的索引，由 {exportField}`in` 绑定。
  索引 0 指向匿名名称，并且是预定义的。

: {exportType +def}`LevelIdx`

  {tech (key := "universe level")}[层级]表中的索引，由 {exportField}`il` 绑定。
  索引 0 指向层级 0，并且是预定义的。

: {exportType +def}`ExprIdx`

  表达式表中的索引，由 {exportField}`ie` 绑定。
  没有预定义的值。

: {exportType +def}`NameIdxDef`

  本行定义的 {exportType}`NameIdx`。

: {exportType +def}`LevelIdxDef`

  本行定义的 {exportType}`LevelIdx`。

: {exportType +def}`ExprIdxDef`

  本行定义的 {exportType}`ExprIdx`。

如果一个索引被重复定义，内核应拒绝该代码。
每个索引的定义都必须位于其所有使用之前；遇到未定义的索引时，内核应拒绝该代码。
:::

其他整数字段表示整数值。
它们可以是 de Bruijn 索引（{exportField}`bvar`）、数值名称分量（{exportField}`i`）、字段索引（{exportField}`idx`）、定义高度（{exportField}`regular`）、构造器位置（{exportField}`cidx`）或计数（{exportField}`numParams`、{exportField}`numIndices`、{exportField}`numNested`、{exportField}`numFields`、{exportField}`numMotives`、{exportField}`numMinors`、{exportField}`nfields`）。
自然数字面量被编码为 JSON 字符串字面量而非 JSON 数字，以降低解析器在 $`2^{53}` 等限制处截断数值的风险。


## 名称
%%%
file := "Names"
tag := "Lean-__________________--____________--Lean-____________--______-0"
%%%

名称有两种格式，分别对应 {name}`Lean.Name` 的构造器。
索引 0 预定义为指向 {name}`Lean.Name.anonymous`。

```exportFormat "Name.str"
{
  "str": {
    "pre": NameIdx,
    "str": string
  },
  "in": NameIdxDef
}
```

```exportFormat "Name.num"
{
  "num": {
    "pre": NameIdx,
    "i": integer
  },
  "in": NameIdxDef
}
```

## 层级
%%%
file := "Levels"
tag := "Lean-__________________--____________--Lean-____________--______-1"
%%%

{tech (key := "Universe levels")}[宇宙层级]有四种格式，分别对应 {name}`Lean.Level` 的构造器。
索引 0 预定义为指向 {name}`Lean.Level.zero`，不会另行表示。

```exportFormat "Level.succ"
{
  "succ": LevelIdx,
  "il": LevelIdxDef
}
```

```exportFormat "Level.max"
{
  "max": [LevelIdx, LevelIdx],
  "il": LevelIdxDef
}
```

```exportFormat "Level.imax"
{
  "imax": [LevelIdx, LevelIdx],
  "il": LevelIdxDef
}
```

```exportFormat "Level.param"
{
  "param": NameIdx,
  "il": LevelIdxDef
}
```

## 表达式
%%%
file := "Expressions"
tag := "Lean-__________________--____________--Lean-____________--_________"
%%%

精译后代码中可能出现的每个 {name}`Lean.Expr` 构造器都有对应的 JSON 表示。
自由变量和元变量不会出现在导出文件中。
没有预定义的表达式。

```exportFormat "Expr.bvar"
{
  "bvar": integer,
  "ie": ExprIdxDef
}
```


```exportFormat "Expr.sort"
{
  "sort": LevelIdx,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.const"
{
  "const": {
    "name": NameIdx,
    "us": Array<LevelIdx>
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.app"
{
  "app": {
    "fn": ExprIdx,
    "arg": ExprIdx
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lam"
{
  "lam": {
    "name": NameIdx,
    "type": ExprIdx,
    "body": ExprIdx,
    "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.forallE"
{
  "forallE": {
    "name": NameIdx,
    "type": ExprIdx,
    "body": ExprIdx,
    "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.letE"
{
  "letE": {
    "name": NameIdx,
    "type": ExprIdx,
    "value": ExprIdx,
    "body": ExprIdx,
    "nondep": boolean
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.proj"
{
  "proj": {
    "typeName": NameIdx,
    "idx": integer,
    "struct": ExprIdx
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lit (Literal.natVal)"
{
  "natVal": string,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lit (Literal.strVal)"
{
  "strVal": string,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.mdata"
{
  "mdata": {
    "expr": ExprIdx,
    "data": object
  },
  "ie": ExprIdxDef
}
```

默认情况下，导出前会去除元数据。
`--export-mdata` 标志使导出文件包含元数据；存在元数据时，{exportField}`data` 是一个对象，其值是由 {name}`repr` 格式化的字符串。

## 声明
%%%
file := "Declarations"
tag := "Lean-__________________--____________--Lean-____________--______-2"
%%%

核心类型论中的每种声明都有对应的 JSON 表示。
有时，多种 Lean 声明会精译为同一种底层表示；{ref "structures"}[结构体]和{ref "inductive-types"}[归纳类型]就是一个例子。
这种情况下只使用一种表示。

### 公理
%%%
file := "Axioms"
tag := "Lean-__________________--____________--Lean-____________--______--______"
%%%

```exportFormat "Axiom"
{
  "axiom": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "isUnsafe": boolean
  }
}
```

### 定义
%%%
file := "Definitions"
tag := "Lean-__________________--____________--Lean-____________--______--______-0"
%%%

```exportFormat "Definition"
{
  "def": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "hints": "opaque" | "abbrev" | {"regular": integer},
    "safety": "unsafe" | "safe" | "partial",
    "all": Array<NameIdx>
  }
}
```

### 不透明声明
%%%
file := "Opaques"
tag := "Lean-__________________--____________--Lean-____________--______--_______________"
%%%

```exportFormat "Opaque"
{
  "opaque": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "isUnsafe": boolean,
    "all": Array<NameIdx>
  }
}
```

### 定理
%%%
file := "Theorems"
tag := "Lean-__________________--____________--Lean-____________--______--______-1"
%%%

```exportFormat "Theorem"
{
  "thm": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "all": Array<NameIdx>
  }
}
```

### 商类型
%%%
file := "Quotients"
tag := "Lean-__________________--____________--Lean-____________--______--_________"
%%%

官方 Lean 内核使用无字段的构造器 {name}`Lean.Declaration.quotDecl` 作为输入来声明商类型相关声明。
随后，它会将组成商类型包的四个声明加入环境。
为方便使用，导出格式包含这些生成声明的数据。

```exportFormat "Quotient"
{
  "quot": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "kind": "type" | "ctor" | "lift" | "ind"
  }
}
```

### 归纳声明
%%%
file := "Inductive-Declaration___"
tag := "Lean-__________________--____________--Lean-____________--______--____________"
%%%

官方 Lean 内核接收一个 {name}`Lean.Declaration.inductDecl`，其中包含一组（相互）归纳声明及其构造器。
内核据此推导{tech (key := "recursors")}[递归器]及信息字段，例如 {name Lean.InductiveVal.isRec}`isRec`、{name Lean.InductiveVal.isReflexive}`isReflexive` 或 {name Lean.ConstructorVal.cidx}`cidx`。
为方便使用，导出格式包含这些生成声明的数据。
{tech (key := "ι-reductions")}[ι-归约]由 {exportType}`RecursorRule` 条目指定。
独立内核可以信任文件中包含的派生递归器信息，也可以重新生成并检查它们，以获得额外保障。

```exportFormat "Inductive Declaration"
{
  "inductive": {
    "types": Array<InductiveVal>,
    "ctors": Array<ConstructorVal>,
    "recs": Array<RecursorVal>
  }
}
```

```exportFormat "InductiveVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "numParams": integer,
  "numIndices": integer,
  "all": Array<NameIdx>,
  "ctors": Array<NameIdx>,
  "numNested": integer,
  "isRec": boolean,
  "isUnsafe": boolean,
  "isReflexive": boolean
}
```

```exportFormat "ConstructorVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "induct": NameIdx,
  "cidx": integer,
  "numParams": integer,
  "numFields": integer,
  "isUnsafe": boolean
}
```

```exportFormat "RecursorVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "all": Array<NameIdx>,
  "numParams": integer,
  "numIndices": integer,
  "numMotives": integer,
  "numMinors": integer,
  "rules": Array<RecursorRule>,
  "k": boolean,
  "isUnsafe": boolean
}
```

```exportFormat "RecursorRule"
{
  "ctor": NameIdx,
  "nfields": integer,
  "rhs": ExprIdx
}
```
