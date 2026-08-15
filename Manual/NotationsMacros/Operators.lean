/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "自定义运算符" =>
%%%
tag := "operators"
file := "Custom-Operators"
%%%

Lean 支持自定义中缀、前缀和后缀运算符。
任何 Lean 库都可以添加新运算符，而这些新运算符与语言内置运算符具有同等地位。
每个新运算符都会被赋予一个作为函数的解释，随后对该运算符的使用会被翻译为对该函数的使用。
运算符到函数调用的这种翻译被称为它的 {deftech (key := "expansion")}_展开_。
如果这个函数是某个 {tech (key := "type class")}[类型类] {tech (key := "method")}[方法]，那么就可以通过定义该类的实例来重载生成的运算符。

所有运算符都有一个 {deftech (key := "precedence")}_优先级_。
运算符优先级决定了无括号表达式中的运算顺序：由于乘法的优先级高于加法，{lean}`2 + 3 * 4` 等价于 {lean}`2 + (3 * 4)`，而 {lean}`2 * 3 + 4` 等价于 {lean}`(2 * 3) + 4`。
中缀运算符还具有一个 {deftech (key := "associativity")}_结合性_，它决定了同一优先级的一串运算符应如何理解：

: {deftech (key := "Left-associative")}[左结合]

  这类运算符向左嵌套。
  加法是左结合的，因此 {lean}`2 + 3 + 4 + 5` 等价于 {lean}`((2 + 3) + 4) + 5`。

: {deftech (key := "Right-associative")}[右结合]

  这类运算符向右嵌套。
  积类型是右结合的，因此 {lean}`Nat × String × Unit × Option Int` 等价于 {lean}`Nat × (String × (Unit × Option Int))`。

: {deftech (key := "Non-associative")}[非结合]

  将这类运算符串接起来会导致语法错误。
  必须显式加括号。
  等号是非结合的，因此下面的写法是错误的：

  ```syntaxError eqs (category := term)
  1 + 2 = 3 = 2 + 1
  ```
  解析器错误为：
  ```leanOutput eqs
  <example>:1:10-1:11: expected end of input
  ```
::::keepEnv
:::example "前缀与中缀运算符的优先级" (file := "Precedence for Prefix and Infix Operators")
```lean -show
axiom A : Prop
axiom B : Prop
example : (¬A ∧ B = (¬A) ∧ B) = (¬A ∧ ((B = ¬A) ∧ B)) := rfl
example : (¬A ∧ B) = ((¬A) ∧ B) := rfl
```

命题 {lean}`¬A ∧ B` 等价于 {lean}`(¬A) ∧ B`，因为 `¬` 的优先级高于 `∧`。
由于 `∧` 的优先级高于 `=`，并且它是右结合的，所以 {lean}`¬A ∧ B = (¬A) ∧ B` 等价于 {lean}`¬A ∧ ((B = ¬A) ∧ B)`。
:::
::::

Lean 提供了用于定义新运算符的命令：
:::syntax command (title := "运算符声明")
非结合中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

左结合中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infixl` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixl:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

右结合中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infixr` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixr:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

前缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`prefix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind prefix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

后缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`postfix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind postfix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```
:::

这些命令前面都可以带有 {tech (key := "documentation comments")}[文档注释] 和 {tech (key := "attributes")}[属性]。
当用户将鼠标悬停在运算符上时，会显示该文档注释；而属性则和其他任何声明一样，可以调用任意元程序。
{attr}`inherit_doc` 属性会让实现该运算符的函数的文档被复用于运算符本身。

运算符与 {tech (key := "section scopes")}[节作用域] 的交互方式和属性相同。
默认情况下，运算符在任何传递导入了其定义所在模块的模块中都可用；但也可以将其声明为 `scoped` 或 `local`，分别把可用范围限制为当前命名空间已被打开的上下文，或者当前的 {tech (key := "section scope")}[节作用域]。

自定义运算符需要在冒号后提供一个 {ref "precedence"}[优先级] 说明。
自定义运算符没有可回退使用的默认优先级。

运算符也可以显式命名。
这个名字表示对 Lean 语法的扩展，主要用于元编程。
如果没有显式提供名字，Lean 会根据运算符自动生成一个。
不应依赖这个名字的具体分配方式，因为内部命名算法可能改变，而且上游依赖中引入相似运算符也可能造成冲突；在这种情况下，Lean 会修改所分配的名字，直到它唯一为止。

::::keepEnv
:::example "自动分配的运算符名称" (file := "Assigned Operator Names")
给定这个中缀运算符：
```lean
infix:90 " ⤴ " => Option.getD
```
生成的解析器扩展会被赋予内部名称 {name}`«term_⤴_»`。
:::
::::

::::keepEnv
:::example "显式提供的运算符名称" (file := "Provided Operator Names")
给定这个中缀运算符：
```lean
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
生成的解析器扩展会命名为 {name}`getDOp`。
:::
::::

::::keepEnv
:::example "继承文档" (file := "Inheriting Documentation")
给定这个中缀运算符：
```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
生成的解析器扩展具有与 {name}`Option.getD` 相同的文档。
:::
::::



当定义了多个共享同一语法的运算符时，Lean 的解析器会尝试它们全部。
如果有多个成功，就会选择消耗输入最多的那个——这被称为 {deftech (key := "local longest-match rule")}_局部最长匹配规则_。
在某些情况下，多个运算符的解析都可能成功，并且它们覆盖的是输入中的同一范围。
这时会使用运算符的 {tech (key := "priority")}[优先级] 来选择合适的结果。
最后，如果多个同优先级运算符在最长匹配上并列，解析器就会保留所有结果，并由精译器逐个尝试；如果不能恰好有一个成功精译，则整体失败。

:::::keepEnv

::::example "歧义运算符与优先级" (file := "Ambiguous Operators and Priorities")

:::keepEnv
将 `+` 的另一种实现定义为 {lean}`Or` 只需要一条中缀运算符声明。
```lean
infix:65  " + " => Or
```

有了这个声明，Lean 在精译加法时会同时尝试使用 {name}`HAdd.hAdd` 的内置语法和 {lean}`Or` 的新语法：
```lean (name := trueOrFalse1)
#check True + False
```
```leanOutput trueOrFalse1
True + False : Prop
```
```lean (name := twoPlusTwo1)
#check 2 + 2
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```

不过，由于这个新运算符不是结合的，{tech (key := "local longest-match rule")}[局部最长匹配规则] 意味着只有 {name}`HAdd.hAdd` 能应用于不加括号的三参数写法：
```lean +error (name := trueOrFalseOrTrue1)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize instance of type class
  HAdd Prop Prop ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::keepEnv
如果把这个中缀运算符声明为高优先级，那么在有歧义的情况下 Lean 就不会尝试内置的 {name}`HAdd.hAdd` 运算符：
```lean
infix:65 (priority := high)  " + " => Or
```

```lean (name := trueOrFalse2)
#check True + False
```
```leanOutput trueOrFalse2
True + False : Prop
```
```lean (name := twoPlusTwo2) +error
#check 2 + 2
```
```leanOutput twoPlusTwo2
failed to synthesize instance of type class
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

这个新运算符不是结合的，因此 {tech (key := "local longest-match rule")}[局部最长匹配规则] 意味着只有 {name}`HAdd.hAdd` 能应用于三参数写法：
```lean +error (name := trueOrFalseOrTrue2)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize instance of type class
  HAdd Prop Prop ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

::::
:::::


实际的运算符以字符串字面量给出。
新运算符必须满足下列要求：
 * 它至少必须包含一个字符。
 * 第一个字符不能是单引号或双引号（`'` 或 `"`），除非运算符本身是 `''`。
 * 它不能以反引号（`` ` ``）开头，后面也不能紧跟一个可作为引用名称合法前缀的字符。
 * 它不能以数字开头。
 * 它不能包含内部空白。

运算符字符串字面量可以以空格开头或结尾。
这些空格不属于运算符语法的一部分，它们的存在也不会要求在使用运算符时必须在两侧留空格。
不过，空格的存在会使 Lean 在向用户显示运算符时插入空格。
省略这些空格会让运算符参数在显示时紧贴运算符本身。


:::keepEnv
```lean -show
-- 验证前一段关于内部空白的说法
/-- error: invalid atom -/
#check_msgs in
infix:99 " <<<< >>>> " => Nat.add


--- 进一步验证关于合法原子的说法
/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "" => Nat.mul


/-- error: invalid atom -/
#check_msgs in
infix:9 (name := alsobogus) " ` " => Nat.mul

-- 这个可以
#check_msgs in
infix:9 (name := nonbogus) " `` " => Nat.mul

/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "`a" => Nat.mul

```
:::

最后，运算符的含义通过 {keywordOf Lean.Parser.Command.mixfix}`=>` 给出，并与运算符本身分隔开。
这里可以是任意 Lean 项。
对运算符的使用会被解糖为函数应用，并把给定项放在函数位置。
前缀和后缀运算符会把该项应用到自己的单个显式参数上。
中缀运算符则会按顺序把该项应用到左参数和右参数上。
除了要能在每个使用点接收参数之外，对这个项没有其他特殊要求。
运算符可以构造函数，因此这个项可以期待比运算符更多的参数。
隐式参数和 {tech (key := "instance-implicit")}[实例隐式] 参数会在每个应用点被解析，这使得运算符可以由某个 {tech (key := "type class")}[类型类] {tech (key := "method")}[方法] 来定义。

```lean -show -keep
-- 再次核对上面对运算符的说法
prefix:max "blah" => Nat.add
#check (blah 5)
```

如果这个项要么是全局环境中的一个名称，要么是这样一个名称对一个或多个参数的应用，那么 Lean 会自动为该运算符生成一个 {tech (key := "unexpander")}[逆展开器]。
这意味着，凡是原本会显示相应函数项的地方，运算符都会显示在 Lean 的 {tech (key := "proof states")}[证明状态]、错误消息和其他输出中。
Lean 不会跟踪原始项里是否真的使用了该运算符；只要有机会，它就会把它插入进去。

:::::keepEnv
::::example "Lean 输出中的自定义运算符" (file := "Custom Operators in Lean's Output")
函数 {lean}`perhapsFactorial` 会在数字不太大时计算它的阶乘。
```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none
```

可以用后缀惊叹问号运算符来表示它。
```lean
postfix:90 "‽" => perhapsFactorial
```

在尝试证明 {lean}`∀ n, n ≥ 8 → (perhapsFactorial n).isNone` 时，初始证明状态会使用这个新运算符，尽管定理原文并没有这样写：
```proofState
∀ n, n ≥ 8 → (perhapsFactorial n).isNone := by skip
/--
⊢ ∀ (n : Nat), n ≥ 8 → n‽.isNone = true
-/

```
::::
:::::

:::example "中缀运算符、已定义函数与逆展开器" (file := "Infix Operators, Defined Functions, and Unexpanders")
当运算符不会展开成对某个已定义函数的应用时，就不会生成逆展开器。
这里，后缀惊叹问号会展开成一个匿名函数：当参数不太大时，它会取其阶乘。

```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

set_option quotPrecheck false in
postfix:90 "‽" => fun (n : Nat) => if n < 8 then some (fact n) else none
```

由于展开式中没有具名函数，因此无法生成逆展开器：
```lean (name := noUnexp)
#check 7‽
```
```leanOutput noUnexp
(fun n => if n < 8 then some (fact n) else none) 7 : Option Nat
```

使用具名函数则会产生一个逆展开器，它会用于那些由 {name}`perhapsFactorial` 的应用构成的项：
```lean
def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none

postfix:90 "‽'" => perhapsFactorial

```
```lean (name := withUnexp)
#check 7‽'
```
```leanOutput withUnexp
7‽' : Option Nat
```
:::
