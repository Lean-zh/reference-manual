/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`unknownIdentifier`" =>
%%%
shortTitle := "unknownIdentifier"
tag := "Lean-__________________--Error-Explanations--About___--unknownIdentifier"
%%%

{errorExplanationHeader lean.unknownIdentifier}

此错误表示 Lean 无法找到与给定名称匹配的变量或常量。更确切地说，这意味着该名称无法被
*解析*，如手册的 {ref "identifiers-and-resolution"}[标识符]章节所述：无法将输入解释为局部变量
或节变量（如果适用）、之前声明的全局常量，或前述任一项的投影。（“如果适用”是指在某些情况下——
例如 {keywordOf Lean.Parser.Command.print}`#print` 命令的参数——名称只解析为全局常量。）

请注意，此错误消息只会显示该标识符的一种可能解析，但出现此错误表示它可能指代的*所有*名称都解析失败。
例如，如果输入标识符 `x` 时命名空间 `A` 和 `B` 已打开，错误消息“未知标识符 \`x\`”表示找不到
`x`、`A.x` 或 `B.x` 中的任何一个（或者如果 `A.x` 或 `B.x` 存在，其中之一是受保护声明）。

此错误的常见原因包括忘记导入定义常量的模块、命名空间未打开时省略常量的命名空间，或尝试引用
不在作用域内的局部变量。

为帮助解决其中一些常见问题，此错误消息附带一个代码操作，用于建议与所提供名称相似的常量名称。
这些名称包括环境中的常量，以及可以从其他模块导入的常量。请注意，这些建议只能通过受支持代码
编辑器的内置代码操作机制获得，不会作为错误消息本身中的提示出现。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--unknownIdentifier--Examples"
%%%
:::errorExample "变量不在作用域内"
```broken
example (s : IO.FS.Stream) := do
  IO.withStdout s do
    let text := "Hello"
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
```output
Unknown identifier `text`
```
```fixed
example (s : IO.FS.Stream) := do
  let text := "Hello"
  IO.withStdout s do
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
此示例最后一行会产生未知标识符错误，因为变量 `text` 不在作用域内。第三行的
{keywordOf Lean.Parser.Term.let}`let` 绑定的作用域是内部 {keywordOf Lean.Parser.Term.do}`do` 块，
无法在外部 {keywordOf Lean.Parser.Term.do}`do` 块中访问。将此绑定移到外部
{keywordOf Lean.Parser.Term.do}`do` 块后，它在内部块中也仍处于作用域内，从而解决此问题。
:::

:::errorExample "缺少命名空间"
```broken
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  rgb 255 0 0
```
```output
Unknown identifier `rgb`
```
```fixed "限定名称"
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  Color.rgb 255 0 0
```
```fixed "打开命名空间"
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

open Color in
def red : Color :=
  rgb 255 0 0
```

在此示例中，最后一行的标识符 `rgb` 无法解析为同名的 `Color` 构造器。这是因为构造器的名称实际
上是 `Color.rgb`：归纳类型的所有构造器都在该类型的命名空间中命名。由于 `Color` 命名空间未打开，
标识符 `rgb` 不能不带命名空间前缀使用。

解决此错误的一种方法是提供完整限定的构造器名称 `Color.rgb`；也可以使用点标识符记法 `.rgb`，
因为 `.rgb 255 0 0` 的预期类型是 `Color`。或者，可以打开 `Color` 命名空间，继续省略标识符
中的 `Color` 前缀。
:::

:::errorExample "受保护常量名称缺少命名空间前缀"

```broken
protected def A.x := ()

open A

example := x
```
```output
Unknown identifier `x`
```
```fixed "限定名称"
protected def A.x := ()

open A

example := A.x
```
```fixed "受限打开"
protected def A.x := ()

open A (x)

example := x
```

在此示例中，由于常量 `A.x` 是 {keyword}`protected`，即使打开了 `A` 命名空间，也不能通过后缀
`x` 引用它。因此，标识符 `x` 解析失败。相反，要引用 {keyword}`protected` 常量，必须至少包含
其最内层命名空间——在本例中是 `A`。或者，第二个修正示例所展示的*受限打开*语法允许通过未限定
名称引用 {keyword}`protected` 常量，而无需打开它所在命名空间的其余部分（详情请参阅手册中的
{ref "namespaces-sections"}[命名空间和节]章节）。
:::

:::errorExample "点标识符记法推断出不可解析名称"

```broken
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  .toNat (b₁ || b₂)
```
```output
Unknown constant `Nat.toNat`

Note: Inferred this name from the expected resulting type of `.toNat`:
  Nat
```
```fixed "广义字段记法"
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  (b₁ || b₂).toNat
```
```fixed "限定名称"
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  Bool.toNat (b₁ || b₂)
```

在此示例中，点标识符记法 `.toNat` 使 Lean 推断出无法解析的名称（`Nat.toNat`）。点标识符记法
所使用的命名空间总是根据其所在表达式的预期类型推断；由于 `disjoinToNat` 上的类型注解，在本例中
该类型是 `Nat`。若要使用参数类型的命名空间——这似乎是代码作者的意图——请使用第一个修正示例
所示的*广义字段记法*。或者，也可以通过书写完整限定的函数名称来显式指定正确的命名空间。
:::

:::errorExample "自动绑定变量"

```broken
set_option relaxedAutoImplicit false in
def thisBreaks (x : α₁) (y : size₁) := ()

set_option autoImplicit false in
def thisAlsoBreaks (x : α₂) (y : size₂) := ()
```
```output
Unknown identifier `size₁`

Note: It is not possible to treat `size₁` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.
```
```fixed "修改选项"
set_option relaxedAutoImplicit true in
def thisWorks (x : α₁) (y : size₁) := ()

set_option autoImplicit true in
def thisAlsoWorks (x : α₂) (y : size₂) := ()
```
```fixed "为未知标识符添加隐式绑定"
set_option relaxedAutoImplicit false in
def thisWorks {size₁} (x : α₁) (y : size₁) := ()

set_option autoImplicit false in
def thisAlsoWorks {α₂ size₂} (x : α₂) (y : size₂) := ()
```

Lean 遇到定义类型中无法识别的标识符时，默认会为这些未知标识符添加
{ref "automatic-implicit-parameters"}[自动隐式参数]。然而，许多文件或项目会将
{option}`autoImplicit` 或 {option}`relaxedAutoImplicit` 选项设为 {name}`false`，从而禁用此功能。

如果不重新启用 {option}`autoImplicit` 或 {option}`relaxedAutoImplicit` 选项，修复此错误最简单的
方法就是像上面的示例一样，将未知标识符添加为
{ref "implicit-functions"}[普通隐式参数]。
:::
