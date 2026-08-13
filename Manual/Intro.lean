/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
/-
#doc (Manual) "Introduction" =>
-/


#doc (Manual) "简介" =>
%%%
file := "Introduction"
htmlSplit := .never
tag := "introduction"
%%%

这是Lean语言参考手册。
它旨在对Lean进行全面而精确的描述，是Lean用户查找详细信息的参考资料，而不是给新用户的入门教程。
如需其他文档，请参阅[Lean文档总览(英文)](https://lean-lang.org/documentation/) 或 [lean中文文档](https://www.leanprover.cn/)。
本手册涵盖Lean {versionString}[]版本。


# 历史
%%%
tag := "history-of-lean"
%%%

Leonardo de Moura于2013年在微软研究院发起了Lean项目，Lean 0.1于2014年6月16日正式发布。
Lean项目的目标是结合由小型、可独立实现的逻辑内核所提供的高度信任度与类似SMT求解器等工具的便利性和自动化能力，同时能够扩展到大型问题。
这一愿景仍然引领着Lean的发展，我们不断致力于改进自动化、提升性能和增强用户友好性；受信任的核心证明检查器依然极为精简，并且存在独立实现。


Lean的初始版本主要是以C++库的形式配置，客户端代码能够在其中执行可被独立检查的可靠证明。
在早期，这些Lean版本的设计迅速向传统的交互式证明器演进，最初使用Lua编写策略，后来又引入了专用前端语法。
2017年1月20日，Lean 3.0系列首次发布。Lean 3被数学家广泛采纳，并首创自我可扩展性：策略、符号和顶层命令都可以用Lean本身来定义。
数学界创建了Mathlib，在Lean 3末期，Mathlib已拥有超过一百万行形式化数学，所有证明均由计算机机械化验证。
然而，该系统本身依然由C++实现，这对Lean的灵活性构成了限制，由于开发需要具备多种技能，导致了开发变得困难。


Lean 4的开发始于2018年，并于2023年9月8日发布了4.0版本。
Lean 4代表着一个重要的里程碑：自4.0版本起，Lean实现了自托管(self-hosted)——大约90%的Lean实现代码本身就以Lean编写。
Lean 4丰富的扩展API使用户能够根据自己的需求对其进行适配，而不必依赖核心开发团队来添加所需功能。
此外，自托管大大加快了开发进程，因此功能与性能都能更快地交付
Lean 4比Lean 3速度更快，并且能够处理更大规模的问题。
在Lean开发者的支持下，社区于2023年成功将Mathlib迁移到Lean 4，目前其规模已超过150万行。
即便Mathlib增长了50%，Lean 4对它的检查速度比Lean 3对较小库的检查还要快。
Lean 4的开发周期几乎与所有先前版本加总的开发周期持平，如今我们对其设计非常满意——不再计划进行重写。


Leonardo de Moura及其联合创始人Sebastian Ullrich于2023年7月在Convergent Research旗下发起了Lean Focused Research Organization (FRO)非盈利机构，得到了Simons Foundation International、Alfred P. Sloan基金会和Richard Merkin的慈善支持。
该FRO目前拥有十余名员工，致力于支持Lean及更广泛Lean社区的发展与可扩展性。


# 排版方式
%%%
tag := "typographical-conventions"
%%%

本文档采用了多种排版和布局方式，来表示不同方面的信息。


## Lean代码
%%%
tag := "code-samples"
%%%


本文档包含许多Lean代码示例。其格式如下：

```lean
def hello : IO Unit := IO.println "Hello, world!"
```

编译器输出（可能是错误、警告，或仅是信息）既在代码中显示，也会单独列出：

```lean (name := output) +error
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
```


信息性输出，例如{keywordOf Lean.Parser.Command.eval}`#eval`的结果，呈现如下：
```leanOutput output (severity := information)
"The answer is 4"
```

警告如下显示：
```leanOutput output (severity := warning)
declaration uses `sorry`
```


错误消息如下显示：
```leanOutput output (severity := error)
Application type mismatch: The argument
  "two"
has type
  String
but is expected to have type
  Nat
in the application
  Nat.succ "two"
```


策略证明的状态通常通过可点击的小按钮指示，例如在{tactic}`rfl`之后:

(译者注: 注意by和rfl之后有一个很小的长条状按钮，或者当鼠标移动到by或rfl上时会弹出一个气泡框显式当前的证明状态)
```lean
example : 2 + 2 = 4 := by rfl
```

:::tacticExample
证明状态有时会单独展示。
在尝试证明{goal}`2 + 2 = 4`时，初始证明状态为：
```pre
⊢ 2 + 2 = 4
```
使用{tacticStep}`rfl`后，得到的状态是：
```post

```

```setup
skip
```
:::

代码示例中的标识符会链接到其文档页面。

带有语法错误的代码示例会在出错位置给出指示，并附带错误信息：
```syntaxError intro
def f : Option Nat → Type
  | some 0 => Unit
  | => Option (f t)
  | none => Empty
```
```leanOutput intro
<example>:3:3-3:6: unexpected token '=>'; expected term
```


## 示例
%%%
tag := "example-boxes"
%%%


说明性示例会折叠在如下所示的提示框中：


::::keepEnv
:::example "偶数"
这是一个示例的样例

一种定义偶数的方法是使用归纳谓词：
```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)
```
:::
::::


## 技术术语
%%%
tag := "technical-terms"
%%%


{deftech (key := "Technical terminology")}_技术术语_是指在撰写技术资料时以非常特定的含义使用的术语，例如本参考资料中的术语。
{tech (key := "Technical terminology")}[技术术语]通常会通过类似这样的链接超链接到其定义页面。

(译者注: 由于翻译进度的原因, 部分技术术语会以 中文(英文) 或 英文(中文) 的方式展示, 括号内的部分是超链接)


## 常量、语法和策略参考
%%%
tag := "reference-boxes"
%%%


定义、归纳类型、语法生成器和战术有特定的描述。这些描述标记如下：


::::keepEnv
```lean
/--
偶数：如果一个数字能被二整除，则该数字是偶数。
-/
inductive Even : Nat → Prop where
  | /-- 0是偶数 -/
    zero : Even 0
  | /-- 如果 n 是偶数，那么 n + 2 也是偶数。 -/
    plusTwo : Even n → Even (n + 2)
```

{docstring Even}

::::


# How to Cite This Work

In formal citations, please cite this work as _The Lean Language Reference_ by The Lean Developers.
Additionally, please include the corresponding version of Lean in the citation, which is {versionString}[].

# Open-Source Licenses
%%%
tag := "dependency-licenses"
number := false
%%%

{licenseInfo}
