/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.ZhDocString.Interaction

import Std.Data.HashSet

import Manual.Meta
import Manual.Papers

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.code.warnLineLength 72
set_option verso.docstring.allowMissing true

#doc (Manual) "格式化输出" =>
%%%
tag := "format-repr"
%%%

{name}`Repr` 类型类用于为数据提供一种标准表示；该表示可以被解析和求值，从而得到一个等价的值。
这并不是严格的正确性准则：对于某些类型，尤其是嵌入了命题的类型，这一点无法做到。
不过，{name}`Repr` 实例产生的输出应尽可能接近可被解析和求值的内容。

:::paragraph
除了可供机器读取之外，这种表示还应便于人类理解——特别是，行不应过长，嵌套值应缩进。
这是通过两步过程实现的：

 1. {name}`Repr` 实例生成一个类型为 {name}`Std.Format` 的中间文档，它紧凑地表示一_组_字符串，这些字符串的区别在于换行和缩进的位置。
 2. 渲染过程根据期望的最大行长等准则，从该集合中选择“最佳”代表。

尤其是，{name}`Std.Format` 可以组合式地构建，因此 {name}`Repr` 实例无需考虑周围的缩进上下文。
:::


# 格式
%%%
tag := "Format"
%%%


::::leanSection
```lean -show
open Std (Format)
open Std.Format
variable {str : String} {indent : String} {n : Nat}
```
:::paragraph
{name}`Format`{margin}[这里介绍的 API 改编自 Wadler 的工作（{citehere wadler2003}[]）。它经过修改，以便在严格求值语言中高效运行，并支持元数据标签等额外功能。]是字符串集合的一种紧凑表示。
最重要的 {name Std.Format}`Format` 操作如下：

: 字符串

  使用 {name}`text` 构造器可以将 {name}`String` 转换为 {name}`Format`。
  此构造器已注册为从 {name}`String` 到 {name}`Format` 的{ref "coercions"}[强制转换]，因此通常无需显式调用。
  {lean}`text str` 表示仅包含 {lean}`str` 的单元素集合。
  如果字符串包含换行字符（{lean}`'\n'`），无论分组如何，它们都会无条件地作为换行插入最终输出。
  不过，它们会按照当前缩进级别进行缩进。

: 追加

  可以使用 {inst}`Append Format` 实例提供的 `++` 运算符追加两个 {name}`Format`。

: 分组与换行

  构造器 {name}`line` 表示同时包含 {lean}`"\n" ++ indent` 和 {lean}`" "` 的集合，其中 {lean}`indent` 是一个包含足够空格、可使该行正确缩进的字符串。
  从命令式角度看，可以把它视为一个换行：如果当前行有足够空间，它就会被“展平”为空格。
  换行出现在_分组_中：最近一层包围它的 {name}`group` 运算符应用决定该换行属于哪个分组。
  默认情况下，一个分组内的所有 {name}`line` 要么都表示 {lean}`"\n"`，要么都表示 {lean}`" "`；也可以将分组配置为填充行，此时分组中数量最少的一部分 {name}`line` 表示 {lean}`"\n"`。
  不属于任何分组的 {name}`line` 始终表示 {lean}`"\n"`。

: 缩进

  插入换行时，输出也会缩进。
  {lean}`nest n` 将文档的缩进增加 {lean}`n` 个空格。
  这不足以表示所有 Lean 语法，因为有时要求各列精确对齐。
  {lean}`align` 是一种确保输出字符串位于当前缩进级别的文档：如果可能就只插入空格，否则插入一个换行，后接若干空格。

: 标记

  Lean 的交互功能需要能够把输出与其所表示的底层值关联起来。
  例如，这使 Lean 开发环境能够在悬停于项、证明状态或错误消息上时呈现精译后的项。
  可以使用 {lean}`tag n` 以 {name}`Nat` 值 {lean}`n` 给文档加_标签_；这些 {name}`Nat` 应在一张旁表中映射到底层值。
:::
::::

:::example "宽度与换行"
```imports -show
import Std
```
```lean
open Std Format
```

辅助函数 {name}`parenSeq` 创建一个带圆括号的序列，并通过分组和缩进使其适应不同的输出宽度。
```lean
def parenSeq (xs : List Format) : Format :=
  group <|
    nest 2 (text "(" ++ line ++ joinSep xs line) ++
    line ++
    ")"
```

此文档表示一个带圆括号的数字序列：
```lean
def lst : Format := parenSeq nums
where nums := [1, 2, 3, 4, 5].map (text s!"{·}")
```

```lean -show -keep
-- 检查下一段中的陈述
/-- info: 120 -/
#check_msgs in
#eval defWidth
```

以默认的 120 字符行宽渲染它时，整个序列会位于一行：
```lean (name := lstp)
#eval IO.println lst.pretty
```
```leanOutput lstp
( 1 2 3 4 5 )
```

因为所有 {name}`line` 都属于同一个 {name}`group`，它们要么全部渲染为空格，要么全部渲染为换行。
如果只有 9 个字符的可用宽度，{name}`lst` 中的所有 {name}`line` 都会变成换行：
```lean (name := lstp9)
#eval IO.println (lst.pretty (width := 9))
```
```leanOutput lstp9
(
  1
  2
  3
  4
  5
)
```


此文档在另一个带圆括号的序列中包含三份 {name}`lst`：
```lean
def lsts := parenSeq [lst, lst, lst]
```

在默认宽度下，它仍位于一行：
```lean (name := lstsp)
#eval IO.println lsts.pretty
```
```leanOutput lstsp
( ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) )
```

如果只有 20 个字符的可用宽度，每次出现的 {name}`lst` 都会单独占一行。
这是因为，将外层 {name}`group` 转换为换行已经足以使字符串保持在 20 列以内：
```lean (name := lstsp20)
#eval IO.println (lsts.pretty (width := 20))
```
```leanOutput lstsp20
(
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
)
```

如果只有 10 个字符的可用宽度，每个数字都必须单独占一行：
```lean (name := lstsp10)
#eval IO.println (lsts.pretty (width := 10))
```
```leanOutput lstsp10
(
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
)
```
:::


:::example "分组与填充"
```lean
open Std Format
```

辅助函数 {name}`parenSeq` 创建一个带圆括号的序列，其中每个元素都另起一行并缩进：
```lean
def parenSeq (xs : List Format) : Format :=
  nest 2 (text "(" ++ line ++ joinSep xs line) ++
  line ++
  ")"
```

{name}`nums` 包含从一到二十的数字，是一个格式列表：
```lean
def nums : List Format :=
  Nat.fold 20 (init := []) fun i _ ys =>
    text s!"{20 - i}" :: ys
```

```lean (name := nums)
#eval nums
```

由于 {name}`parenSeq` 没有引入任何分组，所得文档不会被渲染为一行：
```lean
#eval IO.println (pretty (parenSeq nums))
```

可以通过对它们进行分组来修复此问题。
{name}`grouped` 使用 {name}`group` 进行分组，而 {name}`filled` 使用 {name}`fill`。
```lean
def grouped := group (parenSeq nums)
def filled := fill (parenSeq nums)
```

两个分组运算符都会使 {name}`line` 被渲染为空格。
如果空间充足，两者都会渲染为一行：
```lean (name := groupedp)
#eval IO.println (pretty grouped)
```
```leanOutput groupedp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

```lean (name := filledp)
#eval IO.println (pretty filled)
```
```leanOutput filledp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

然而，当一行空间不足时，两者的差异便会显现。
除非 {name}`group` 中的_所有_换行都能变为空格，否则没有任何一个能变为空格：
```lean (name := groupedp30)
#eval IO.println (pretty (width := 30) grouped)
```
```leanOutput groupedp30
(
  1
  2
  3
  4
  5
  6
  7
  8
  9
  10
  11
  12
  13
  14
  15
  16
  17
  18
  19
  20
)
```

另一方面，使用 {name}`fill` 时，只会按避免宽度过宽所需插入换行：
```lean (name := filledp30)
#eval IO.println (pretty (width := 30) filled)
```
```leanOutput filledp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 )
```

在更长的序列中可以清楚看到 {name}`fill` 的行为：
```lean (name := filledbigp30)
#eval IO.println <|
  pretty (width := 30) (fill (parenSeq (nums ++ nums ++ nums ++ nums)))
```
```leanOutput filledbigp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 1 2
  3 4 5 6 7 8 9 10 11 12 13 14
  15 16 17 18 19 20 1 2 3 4 5
  6 7 8 9 10 11 12 13 14 15 16
  17 18 19 20 1 2 3 4 5 6 7 8
  9 10 11 12 13 14 15 16 17 18
  19 20 )
```
:::

::::example "字符串中的换行字符"
字符串中包含换行字符时，渲染过程会无条件地插入换行。
不过，这些换行仍会遵循当前缩进级别。

文档 {name}`str` 由一个内嵌了两个换行的字符串组成：
```lean
open Std Format

def str : Format := text "abc\nxyz\n123"
```

:::paragraph
无论是否分组，打印字符串时都会使用这些换行：
```lean (name := str1)
#eval IO.println str.pretty
```
```leanOutput str1
abc
xyz
123
```
```lean (name := str2)
#eval IO.println (group str).pretty
```
```leanOutput str2
abc
xyz
123
```
:::

:::paragraph
由于该字符串并不以换行结尾，第一个字符串的最后一行会与第二个字符串的第一行位于同一行：
```lean (name := str3)
#eval IO.println (str ++ str).pretty
```
```leanOutput str3
abc
xyz
123abc
xyz
123
```
:::

:::paragraph
不过，提高缩进级别会使字符串的三行都从同一列开始：
```lean (name := str4)
#eval IO.println (text "It is:" ++ indentD str).pretty
```
```leanOutput str4
It is:
  abc
  xyz
  123
```

```lean (name := str5)
#eval IO.println (nest 8 <| text "It is:" ++ align true ++ str).pretty
```
```leanOutput str5
It is:  abc
        xyz
        123
```
:::

::::

## 文档
%%%
tag := "format-api"
%%%

{zhdocstring Std.Format ZhDoc.Std.Format}

{zhdocstring Std.Format.FlattenBehavior ZhDoc.Std.Format.FlattenBehavior}

{zhdocstring Std.Format.fill ZhDoc.Std.Format.fill}

## 空文档
%%%
tag := "format-empty"
%%%


:::paragraph
空字符串在 {name}`Std.Format` 中没有唯一的单一表示。
以下各项都表示空字符串：

* {lean  (type := "Std.Format")}`.nil`
* {lean  (type := "Std.Format")}`.text ""`
* {lean  (type := "Std.Format")}`.text "" ++ .nil`
* {lean  (type := "Std.Format")}`.nil ++ .text ""`

使用 {name}`Std.Format.isEmpty` 检查文档是否包含零个字符；若要专门检查它是否为构造器 {lean}`Std.Format.nil`，则使用 {name}`Std.Format.isNil`。
:::

{zhdocstring Std.Format.isEmpty ZhDoc.Std.Format.isEmpty}

{zhdocstring Std.Format.isNil ZhDoc.Std.Format.isNil}



## 序列
%%%
tag := "format-join"
%%%

当存在某种重复内容（例如列表元素）时，本节中的运算符很有用。
通常的做法是在分隔符参数中包含 {name Std.Format.line}`line`，并使用{ref "format-brackets"}[括起运算符]。

{zhdocstring Std.Format.join ZhDoc.Std.Format.join}

{zhdocstring Std.Format.joinSep ZhDoc.Std.Format.joinSep}

{zhdocstring Std.Format.prefixJoin ZhDoc.Std.Format.prefixJoin}

{zhdocstring Std.Format.joinSuffix ZhDoc.Std.Format.joinSuffix}

## 缩进
%%%
tag := "format-indent"
%%%

这些运算符使得在 {name}`Std.Format.nest` 之上实现一致的缩进风格更加容易。

{zhdocstring Std.Format.nestD ZhDoc.Std.Format.nestD}

{zhdocstring Std.Format.defIndent ZhDoc.Std.Format.defIndent}

{zhdocstring Std.Format.indentD ZhDoc.Std.Format.indentD}

## 方括号与圆括号
%%%
tag := "format-brackets"
%%%

这些运算符使实现一致的括号风格更加容易。

{zhdocstring Std.Format.bracket ZhDoc.Std.Format.bracket}

{zhdocstring Std.Format.sbracket ZhDoc.Std.Format.sbracket}

{zhdocstring Std.Format.paren ZhDoc.Std.Format.paren}

{zhdocstring Std.Format.bracketFill ZhDoc.Std.Format.bracketFill}

## 渲染
%%%
tag := "format-render"
%%%

{inst}`ToString Std.Format` 实例使用默认参数调用 {name}`Std.Format.pretty`。

渲染文档有两种方式：
* 使用 {name Std.Format.pretty}`pretty` 构造 {name}`String`。
  必须先完整构造整个字符串，之后才能将其中任何内容发送给用户。
* 使用 {name Std.Format.prettyM}`prettyM`，利用某个 {name}`Monad` 中的效果，增量地发出 {name}`String`。
  每一行一经渲染就会被发出。
  这适用于流式输出。

{zhdocstring Std.Format.pretty ZhDoc.Std.Format.pretty}

{zhdocstring Std.Format.defWidth ZhDoc.Std.Format.defWidth}

{zhdocstring Std.Format.prettyM ZhDoc.Std.Format.prettyM}

{zhdocstring Std.Format.MonadPrettyFormat ZhDoc.Std.Format.MonadPrettyFormat}

## `ToFormat` 类
%%%
tag := "The-Lean-Language-Reference--Interacting-with-Lean--Formatted-Output--Format--The--ToFormat--Class"
%%%

{name}`Std.ToFormat` 类用于提供一种格式化值的标准方式，并不要求这种格式是有效的 Lean 语法。
错误消息和某些{ref "format-join"}[序列连接运算符]会使用这些实例。

{zhdocstring Std.ToFormat ZhDoc.Std.ToFormat}

# `Repr`
%%%
tag := "repr"
%%%

{name}`Repr` 实例描述如何将值表示为 {name}`Std.Format`。
因为它们应当发出有效的 Lean 语法，所以这些实例需要考虑{tech (key := "precedence")}[优先级]。
插入最大数量的圆括号确实可行，但会使人类更难阅读所得输出。

{zhdocstring Repr ZhDoc.Repr}

{zhdocstring repr ZhDoc.repr}

{zhdocstring reprStr ZhDoc.reprStr}

:::example "最多的圆括号"
类型 {name}`NatOrInt` 可以包含一个 {name}`Nat` 或一个 {name}`Int`：
```lean
inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt
```
这个 {inst}`Repr NatOrInt` 实例通过插入许多圆括号来确保输出是有效的 Lean 语法：
```lean
instance : Repr NatOrInt where
  reprPrec x _ :=
    .nestD <| .group <|
      match x with
      | .nat n =>
          .text "(" ++ "NatOrInt.nat" ++ .line ++ "(" ++ repr n ++ "))"
      | .int i =>
          .text "(" ++ "NatOrInt.int" ++ .line ++ "(" ++ repr i ++ "))"
```
无论它包含 {name}`Nat`、非负的 {name}`Int`，还是负的 {name}`Int`，结果都可以被解析：
```lean (name := parens)
open NatOrInt in
#eval do
  IO.println <| repr <| nat 3
  IO.println <| repr <| int 5
  IO.println <| repr <| int (-5)
```
```leanOutput parens
(NatOrInt.nat (3))
(NatOrInt.int (5))
(NatOrInt.int (-5))
```
不过，{lean}`(NatOrInt.nat (3))` 并不是特别惯用的 Lean 写法，而且冗余的圆括号会使大型表达式难以阅读。
:::


方法 {name}`Repr.reprPrec` 具有如下签名：
```signature
Repr.reprPrec.{u} {α : Type u} [Repr α] : α → Nat → Std.Format
```
第一个显式参数是要表示的值，第二个则是该值所在上下文的{tech (key := "precedence")}[优先级]。
可以利用此优先级决定是否插入圆括号：如果实例所生成语法的优先级不高于其上下文的优先级，就需要圆括号。

## 如何编写 `Repr` 实例
%%%
tag := "repr-instance-howto"
%%%

Lean 可以使用{ref "deriving-instances"}[实例派生]为大多数类型自动生成合适的 {name}`Repr` 实例。
不过，在某些情况下需要手动编写实例：

* 有些库以函数而非构造器作为类型的主要接口；在这种情况下，{name}`Repr` 实例应表示对这些函数的调用。
  例如，{inst}`Repr (HashSet α)` 实例使用 {name}`Std.HashSet.ofList`。

* 有些归纳类型包含良构性证明。
  因为程序无法检查证明，所以不能直接渲染它们。
  这是类型采用构造器以外接口的常见原因。

* 具有特殊语法的类型（例如 {name}`List`）应在其 {name}`Repr` 实例中使用这种语法。

* 为结构派生的 {name}`Repr` 实例使用{tech (key := "structure instance")}[结构实例]记法。
  手写实例可以显式使用构造器名称，也可以使用{tech (key := "anonymous constructor syntax")}[匿名构造器语法]。

```lean -show -keep
/-- info: Std.HashSet.ofList [0, 3, 5] -/
#check_msgs in
#eval IO.println <| repr (({} : Std.HashSet Nat).insert 3 |>.insert 5 |>.insert 0)
```
```lean -show -keep
structure S where
  x : Nat
  y : Nat
deriving Repr
/-- info: { x := 2, y := 3 } -/
#check_msgs in
#eval IO.println <| repr <| S.mk 2 3
```

编写自定义 {name}`Repr` 实例时，请遵循以下约定：

: 优先级

  检查优先级，按需添加圆括号，并将正确的优先级传给内嵌数据的 {name}`reprPrec` 实例。
  每个实例都负责在需要时为自身加上圆括号；实例通常不应为对 {name}`reprPrec` 的递归调用加圆括号。

  函数应用具有最高优先级 {lean}`max_prec`。
  辅助函数 {name}`Repr.addAppParen` 和 {name}`reprArg` 分别在需要时为应用加上圆括号，以及把适当的优先级传给函数参数。

: 完全限定名称

  {name}`Repr` 实例无法访问给定位置处已打开的命名空间集合。
  环境中所有常量的名称都应完全限定，以消除歧义。

: 默认嵌套

  嵌套数据应使用 {name Std.Format.nestD}`nestD` 缩进，以确保各实例之间的缩进一致。

: 分组与换行

  每个包含换行的 {name}`Repr` 实例，其输出都应包围在 {name Std.Format.group}`group` 中。
  此外，如果所得代码包含概念上相互嵌套的表达式，则应在每个嵌套层级外围插入一个 {name Std.Format.group}`group`。
  通常应在以下位置插入换行：
    * 构造器与它的每个参数之间
    * `:=` 之后
    * `,` 之后
    * {tech (key := "structure instance")}[结构实例]记法的左右花括号与其内容之间
    * 中缀运算符之后，而不是之前

: 圆括号与方括号

  应使用 {name}`Std.Format.bracket` 或其特化形式插入圆括号和方括号：圆括号使用 {name}`Std.Format.paren`，方括号使用 {name}`Std.Format.sbracket`。
  这些运算符对带圆括号或方括号表达式的内容进行对齐，其方式与 Lean 相同。
  结尾的圆括号和方括号不应单独占一行，而应与其内容保持在一起。

{zhdocstring Repr.addAppParen ZhDoc.Repr.addAppParen}

{zhdocstring reprArg ZhDoc.reprArg}


:::example "带构造器的归纳类型"
归纳类型 {name}`N.NatOrInt` 可以包含一个 {name}`Nat` 或一个 {name}`Int`：
```lean
namespace N

inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt

```
{inst}`Repr NatOrInt` 实例遵循上述约定：
 * 右侧是一个函数应用，因此它使用 {name}`Repr.addAppParen` 在必要时添加圆括号。
 * 圆括号包围整个主体，且不额外加入 {name Std.Format.line}`line`。
 * 整个函数应用被分组，并按默认量嵌套。
 * 函数与其参数之间用一个 {name Std.Format.line}`line` 分隔；这个换行通常会成为空格，因为 {inst}`Repr Nat` 和 {inst}`Repr Int` 实例不太可能产生很长的输出。
 * 对 {name}`reprPrec` 的递归调用传入 {lean}`max_prec`，因为它们位于函数参数位置，而函数应用具有最高优先级。

```lean
instance : Repr NatOrInt where
  reprPrec
    | .nat n =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.nat" ++ .line ++ reprPrec n max_prec
    | .int i =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.int" ++ .line ++ reprPrec i max_prec
```
```lean (name := nat5)
#eval IO.println (repr (NatOrInt.nat 5))
```
```leanOutput nat5
N.NatOrInt.nat 5
```
```lean (name := int5)
#eval IO.println (repr (NatOrInt.int 5))
```
```leanOutput int5
N.NatOrInt.int 5
```
```lean (name := intm5)
#eval IO.println (repr (NatOrInt.int (-5)))
```
```leanOutput intm5
N.NatOrInt.int (-5)
```
```lean (name := someintm5)
#eval IO.println (repr (some (NatOrInt.int (-5))))
```
```leanOutput someintm5
some (N.NatOrInt.int (-5))
```


```lean (name := lstnat)
#eval IO.println (repr <| (List.range 10).map (NatOrInt.nat))
```
```leanOutput lstnat
[N.NatOrInt.nat 0,
 N.NatOrInt.nat 1,
 N.NatOrInt.nat 2,
 N.NatOrInt.nat 3,
 N.NatOrInt.nat 4,
 N.NatOrInt.nat 5,
 N.NatOrInt.nat 6,
 N.NatOrInt.nat 7,
 N.NatOrInt.nat 8,
 N.NatOrInt.nat 9]
```

```lean (name := lstnat3)
#eval IO.println <|
  Std.Format.pretty (width := 3) <|
    repr <| (List.range 10).map NatOrInt.nat
```
```leanOutput lstnat3
[N.NatOrInt.nat
   0,
 N.NatOrInt.nat
   1,
 N.NatOrInt.nat
   2,
 N.NatOrInt.nat
   3,
 N.NatOrInt.nat
   4,
 N.NatOrInt.nat
   5,
 N.NatOrInt.nat
   6,
 N.NatOrInt.nat
   7,
 N.NatOrInt.nat
   8,
 N.NatOrInt.nat
   9]
```

:::

:::example "中缀语法"
此示例演示如何使用优先级编码左结合的美化打印器。
类型 {lean}`AddExpr` 表示包含常量和加法的表达式：
```lean
inductive AddExpr where
  | nat : Nat → AddExpr
  | add : AddExpr → AddExpr → AddExpr
```

{name}`OfNat` 和 {name}`Add` 实例为 {name}`AddExpr` 提供了更方便的语法：
```lean
instance : OfNat AddExpr n where
  ofNat := .nat n

instance : Add AddExpr where
  add := .add
```

{inst}`Repr AddExpr` 实例应只插入必要的圆括号。
Lean 的加法运算符是左结合的，优先级为 65，因此左侧的递归调用使用优先级 64；如果当前上下文的优先级大于或等于 65，则为运算符自身加圆括号：
```lean
protected def AddExpr.reprPrec : AddExpr → Nat → Std.Format
  | .nat n, p  =>
    Repr.reprPrec n p
  | .add e1 e2, p =>
    let out : Std.Format :=
      .nestD <| .group <|
        AddExpr.reprPrec e1 64 ++ " " ++ "+" ++ .line ++
        AddExpr.reprPrec e2 65
    if p ≥ 65 then out.paren else out

instance : Repr AddExpr := ⟨AddExpr.reprPrec⟩
```

```lean -show -keep
-- 测试为中缀运算符给出的准则是否与 Lean 自身的美化打印器一致
/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11 : Nat
-/
#check_msgs in
#check 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11
-/
#check_msgs in
#eval (1 : AddExpr) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

```

无论输入如何加括号，此实例都只插入必要的圆括号：
```lean (name := prec1)
#eval IO.println (repr (((2 + 3) + 4) : AddExpr))
```
```leanOutput prec1
2 + 3 + 4
```
```lean (name:=prec2)
#eval IO.println (repr ((2 + 3 + 4) : AddExpr))
```
```leanOutput prec2
2 + 3 + 4
```
```lean (name:=prec3)
#eval IO.println (repr ((2 + (3 + 4)) : AddExpr))
```
```leanOutput prec3
2 + (3 + 4)
```
```lean (name:=prec4)
#eval IO.println (repr ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr))
```
```leanOutput prec4
[2 + (3 + 4), 2 + 3 + 4]
```
实现中使用的 {name Std.Format.group}`group`、{name Std.Format.nestD}`nestD` 和 {name Std.Format.line}`line` 会在狭窄上下文中产生预期的换行与缩进：
```lean (name:=prec5)
#eval ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr)
  |> repr
  |>.pretty (width := 0)
  |> IO.println
```
```leanOutput prec5
[2 +
   (3 +
      4),
 2 +
     3 +
   4]
```
:::

## 原子类型
%%%
tag := "ReprAtom"
%%%

当列表元素足够小时，每个元素单独占一行既难以阅读又浪费空间。
为提高可读性，{name}`List` 有两个 {name}`Repr` 实例：一个对其内容使用 {name}`Std.Format.bracket`，另一个使用 {name}`Std.Format.bracketFill`。
后者定义在前者之后，因此会在可能时被选中；不过，它要求有空类型类 {name}`ReprAtom` 的实例。

如果某类型的 {name}`Repr` 实例从不生成空格或换行，那么该类型应有一个 {name}`ReprAtom` 实例。
Lean 为 {name}`String`、{name}`UInt8`、{name}`Nat`、{name}`Char` 和 {name}`Bool` 等类型提供了 {name}`ReprAtom` 实例。

```lean -show
open Lean Elab Command in
#eval show CommandElabM Unit from
  for x in [``String, ``UInt8, ``Nat, ``Char, ``Bool] do
    runTermElabM fun _ => do
      discard <| Meta.synthInstance (.app (.const ``ReprAtom [0]) (.const x []))
      Term.synthesizeSyntheticMVarsNoPostponing
```

{zhdocstring ReprAtom ZhDoc.ReprAtom}

::::example "原子类型与 `Repr`"

归纳类型 {name}`ABC` 的所有构造器都没有参数：

```lean
inductive ABC where
  | a
  | b
  | c
deriving Repr
```

派生的 {inst}`Repr ABC` 实例用于显示列表：
```lean (name := abc1)
def abc : List ABC := [.a, .b, .c]

def abcs : List ABC := abc ++ abc ++ abc

#eval IO.println ((repr abcs).pretty (width := 14))
```

由于宽度很窄，因此会插入换行：
```leanOutput abc1
[ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c]
```

:::paragraph
不过，将列表转换为 {lean}`List Nat` 会得到格式不同的结果。
```lean (name := abc2)
def ABC.toNat : ABC → Nat
  | .a => 0
  | .b => 1
  | .c => 2

#eval IO.print ((repr (abcs.map ABC.toNat)).pretty (width := 14))
```
此时换行少得多：
```leanOutput abc2
[0, 1, 2, 0,
 1, 2, 0, 1,
 2]
```
:::

这是因为存在 {inst}`ReprAtom Nat` 实例。
为 {name}`ABC` 添加一个这样的实例会产生类似的行为：
```lean (name := abc3)
instance : ReprAtom ABC := ⟨⟩

#eval IO.println ((repr abcs).pretty (width := 14))
```
```leanOutput abc3
[ABC.a, ABC.b,
 ABC.c, ABC.a,
 ABC.b, ABC.c,
 ABC.a, ABC.b,
 ABC.c]
```
::::
