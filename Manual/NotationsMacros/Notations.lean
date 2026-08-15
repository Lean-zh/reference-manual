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

#doc (Manual) "记法" =>
%%%
tag := "notations"
file := "Notations"
%%%

术语 {deftech (key := "notation")}_记法_ 在 Lean 中有两种用法：它既可以指代用简洁方式写下想法这一一般概念，也可以指代一种语言特性，这种特性使得只需很少代码就能方便地实现记法。
与自定义运算符一样，Lean 记法允许用新形式扩展项的语法。
不过，记法更为一般：新语法可以自由地将必需的关键字或运算符与子项交错组合，并且它们对优先级层级提供了更精细的控制。
记法还可以在生成的子项中重新排列其参数，而中缀运算符则总是按固定顺序将参数提供给函数项。
由于记法可以定义混合使用前缀、中缀和后缀成分的运算符，它们也可以被称为 {deftech (key := "mixfix")}_混合定界_ 运算符。

:::syntax command (title := "记法声明")
记法使用 {keywordOf Lean.Parser.Command.notation}`notation` 命令来定义。

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind notation$[:$_:prec]? $[(name := $_:ident)]? $[(priority := $_:prio)]? $[$_:notationItem]* => $_:term
```
:::

:::syntax Lean.Parser.Command.notationItem -open (title := "记法项")
记法定义的主体由一串 {deftech (key := "notation items")}_记法项_ 组成，它们既可以是字符串字面量，也可以是带可选优先级的标识符。
```grammar
$s:str
```
```grammar
$x:ident$[:$_:prec]?
```
:::

与运算符声明一样，文档注释的内容会在用户与新语法交互时显示给他们。
添加 {attr}`inherit_doc` 属性会将记法展开后所得项首部函数的文档注释复制到新语法上。
还可以添加其他属性，以便在生成的定义上调用其他编译期元程序。

记法与 {tech (key := "section scopes")}[节作用域] 的交互方式和属性、运算符相同。
默认情况下，记法在任何传递导入了其定义所在模块的模块中都可用；但也可以将其声明为 `scoped` 或 `local`，分别把可用范围限制为当前命名空间已被打开的上下文，或者当前的 {tech (key := "section scope")}[节作用域]。

和运算符一样，解析记法时会使用 {tech (key := "local longest-match rule")}[局部最长匹配规则]。
如果有多个记法在最长匹配上并列，就使用声明的优先权来决定采用哪个解析结果。
如果这样仍无法消除歧义，那么所有结果都会被保留下来，并由精译器依次尝试；当且仅当恰好有一个能够成功精译时，整体才算成功。

与只包含单个运算符及其结合方式和记号不同，记法声明的主体由一串 {deftech (key := "notation items")}_记法项_ 组成，它们既可以是新的 {tech (key := "atoms")}[原子]（既包括 `if`、`#eval`、`where` 等关键字，也包括 `=>`、`+`、`↗`、`⟦`、`⋉` 等符号），也可以是项所占据的位置。
与运算符中的用法相同，字符串字面量用来指明原子的放置位置。
字符串中的前导和尾随空格不会影响解析，但在 Lean 的 {tech (key := "proof states")}[证明状态] 和错误消息中显示该语法时，它们会使 Lean 在相应位置插入空格。
标识符表明在何处期望出现项，并为相应的项命名，以便将其插入记法的展开中。

虽然自定义运算符只涉及一种优先级概念，但记法中会牵涉多个优先级。
记法自身有一个优先级，其中每个要解析的项也各自有优先级。
记法的优先级决定了它可以在哪些上下文中被解析：解析器只会尝试解析那些优先级至少与当前上下文一样高的产生式。
例如，因为乘法的优先级高于加法，解析器在解析加法的参数时会尝试解析中缀乘法项，反之则不会。
每个待解析项的优先级决定了其中还可以出现哪些其他产生式。

如果没有为记法自身提供优先级，则默认值取决于记法的形式。
如果记法既以原子开始又以原子结束（由字符串字面量表示），那么默认优先级就是 `max`。{TODO}[keywordOf]
这既适用于只由单个原子构成的记法，也适用于含有多个项、且首尾两项都是原子的记法。
否则，整个记法的默认优先级是 `lead`。
如果作为项的记法项没有提供优先级，那么它们默认使用优先级 `min`。

```lean -keep -show

-- 测试记法的默认优先级

/-- 解析器 max -/
notation "takesMax " e:max => e
/-- 解析器 lead -/
notation "takesLead " e:lead => e
/-- 解析器 min -/
notation "takesMin " e:min => e

/-- 取第一个 -/
notation e1 " <# " e2 => e1

/-- 在括号里也取第一个！ -/
notation "<<<<<" e1 " <<# " e2 ">>>>>" => e1

elab "#parse_test " "[" e:term "]"  : command => do
  Lean.logInfoAt e (toString e)
  pure ()

-- 这里，takesMax 与 takesLead 区分了这些记法

/-- info: («term_<#_» (termTakesMax_ "takesMax" (num "1")) "<#" (num "2")) -/
#check_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#check_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- 这里，takesMax 与 takesLead 无法区分这些记法，因为两者的优先级都是 `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesLead <<<<< 1 <<# 2 >>>>> ]
```

在必需的双箭头 ({keywordOf Lean.Parser.Command.notation}`=>`) 之后，需要为记法提供一个展开式。
运算符总是按顺序把其实参应用到对应函数上，而记法则可以把其项放在展开式中的任意位置。
这些项通过名字来引用。
项在展开式中可以出现任意多次。
由于记法展开是发生在精译或代码生成之前的纯语法过程，在展开式中复制项可能导致求值结果项时重复计算，甚至在单子中工作时造成副作用被重复执行。

::::keepEnv
:::example "记法展开中被忽略的项" (file := "Ignored Terms in Notation Expansion")
这个记法会忽略它的第一个参数：
```lean
notation (name := ignore) "ignore " _ign:arg e:arg => e
```

被忽略位置上的项会被丢弃，而 Lean 从不会尝试精译它，因此这里可以使用原本会导致错误的项：
```lean (name := ignore)
#eval ignore (2 + "whatever") 5
```
```leanOutput ignore
5
```

不过，被忽略的项在语法上仍然必须合法：
```syntaxError ignore' (category := command)
#eval ignore (2 +) 5
```
```leanOutput ignore'
<example>:1:17-1:18: unexpected token ')'; expected term
```
:::
::::

::::keepEnv
:::example "记法展开中重复的项" (file := "Duplicated Terms in Notation Expansion")

{keywordOf dup}`dup!` 记法会复制它的子项。

```lean
notation (name := dup) "dup!" t:arg => (t, t)
```

由于该项被复制，它可以分别以不同类型进行精译：
```lean
def e : Nat × Int := dup! (2 + 2)
```

打印生成的定义可以看出，加法的计算会执行两次：
```lean (name := dup)
#print e
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
```
:::
::::


当展开式由对全局环境中已定义函数的应用构成，且记法中的每个项都恰好出现一次时，就会生成一个 {tech (key := "unexpander")}[逆展开器]。
当原本会显示匹配的函数应用项时，新记法会显示在 Lean 的 {tech (key := "proof states")}[证明状态]、错误消息及其他输出中。
和自定义运算符一样，Lean 不会跟踪原始项是否使用了该记法；在 Lean 的输出中，只要有机会它就会使用它。

:::example "记法、已定义函数与逆展开器" (file := "Notations, Defined Functions, and Unexpanders")
当记法不会展开成对某个已定义函数的应用时，就不会生成逆展开器。
这里，该记法会展开为一个匿名函数：
```lean
notation "[" start " ⇒ " stop "]" => fun x => x > start && x < stop
```

由于展开式中没有具名函数，因此无法生成逆展开器：
```lean (name := noUnexp)
#check [5 ⇒ 8]
```
```leanOutput noUnexp
fun x => decide (x > 5) && decide (x < 8) : Nat → Bool
```

使用具名函数则会产生一个逆展开器，它会用于那些由 {name}`between` 的应用构成的项：
```lean
def between (start stop : Nat) : Nat → Prop :=
  fun x => x > start && x < stop

notation "[" start " ⇒' " stop "]" => between start stop
```
```lean (name := withUnexp)
#check [5 ⇒' 8]
```
```leanOutput withUnexp
[5 ⇒' 8] : Nat → Prop
```
:::

# 运算符与记法
%%%
tag := "operators-and-notations"
%%%

在内部，运算符声明会被翻译为记法声明。
项形式的记法项会插入到运算符期望参数的位置，并出现在展开式中的对应位置。
对于前缀和后缀运算符，记法自身的优先级以及其项的优先级都等于运算符声明的优先级。
对于非结合的中缀运算符，记法的优先级是声明的优先级，但两个参数都在更高一级的优先级上解析，这会阻止不加括号的连续使用。
结合性的中缀运算符对记法自身以及其中一个参数使用运算符的优先级，而对另一个参数使用高一级的优先级；这只会阻止某一个方向上的连续应用。
左结合运算符对右参数使用更高的优先级，而右结合运算符对左参数使用更高的优先级。
