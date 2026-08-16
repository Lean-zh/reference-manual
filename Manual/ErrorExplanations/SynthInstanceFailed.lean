/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`synthInstanceFailed`" =>
%%%
shortTitle := "synthInstanceFailed"
tag := "Lean-__________________--Error-Explanations--About___--synthInstanceFailed"
%%%

{errorExplanationHeader lean.synthInstanceFailed}

```lean -show
variable {t : Type} (x y : Int)
```

{ref "type-classes"}[类型类] 是 Lean 及许多其他编程语言用来处理重载操作的机制。处理特定
重载操作的代码是类型类的一个 {tech}_实例_；决定给定重载操作应使用哪个实例称为_精译_实例。

例如，当 Lean 遇到表达式 {lean}`x + y`，且 {lean}`x` 和 {lean}`y` 都具有
{name}`Int` 类型时，需要查找如何将两个整数相加，并查找结果类型。这被描述为精译类型类
对于某种类型 `t` 的 {lean}`HAdd Int Int t`。
{lean}`HAdd Int Int t` 的实例，其中 `t` 是某种类型。

许多类型类实例精译失败是由于使用了错误的二元运算。成功和失败并不总是显而易见，因为有些实例
是根据其他实例定义的，Lean 必须递归搜索才能找到合适的实例。可以
{ref "instance-search"}[检查 Lean 的实例精译]，这有助于诊断棘手的类型类实例精译失败。

# 示例

%%%
tag := "Lean-__________________--Error-Explanations--About___--synthInstanceFailed--Examples"
%%%
:::errorExample "使用错误的二元运算"

```broken
#eval "A" + "3"
```
```output
failed to synthesize instance of type class
  HAdd String String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
#eval "A" ++ "3"
```

二元运算 `+` 与 {name}`HAdd` 类型类相关联，而字符串无法进行相加。二元运算 `++` 与
{name}`HAppend` 类型类相关联，是拼接字符串的正确方式。
:::

:::errorExample "参数类型错误"

```broken
def x : Int := 3
#eval x ++ "meters"
```
```output
failed to synthesize instance of type class
  HAppend Int String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
def x : Int := 3
#eval ToString.toString x ++ "meters"
```

Lean 不允许直接将整数和字符串相加。函数 {name}`ToString.toString` 使用类型类重载将值转换为
字符串；通过成功搜索 {lean}`ToString Int` 的实例，第二个示例即可成功。
:::

:::errorExample "缺少类型类实例"

```broken
inductive MyColor where
  | chartreuse | sienna | thistle

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```output
failed to synthesize instance of type class
  Inhabited MyColor

Hint: Adding the command `deriving instance Inhabited for MyColor` may allow Lean to derive the missing instance.
```
```fixed "定义类型时派生实例"
inductive MyColor where
  | chartreuse | sienna | thistle
deriving Inhabited

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "单独派生实例"
inductive MyColor where
  | chartreuse | sienna | thistle

deriving instance Inhabited for MyColor

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "定义实例"
inductive MyColor where
  | chartreuse | sienna | thistle

instance : Inhabited MyColor where
  default := .sienna

def forceColor (oc : Option MyColor) :=
  oc.get!
```

类型类合成可能失败，因为只需提供该类型类的一个实例。这通常发生在 {name}`Repr`、{name}`BEq`、
{name}`ToJson` 和 {name}`Inhabited` 等类型类上。Lean 通常可以在定义类型时，或使用独立的
{keywordOf Lean.Parser.Command.deriving}`deriving` 命令，通过 `deriving` 关键字
{ref "deriving-instances"}[自动生成类型类的实例]。
:::
