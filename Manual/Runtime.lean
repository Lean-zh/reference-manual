/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.LexedText
import Manual.Papers
import Manual.ZhDocString.Runtime
import Std.Async.Process

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "运行时代码" =>
%%%
tag := "runtime"
file := some "Run-Time-Code"
%%%

编译后的 Lean 代码会使用 Lean 运行时提供的服务。
运行时包含高效的底层原语，用于衔接 Lean 语言与其支持的平台。
这些服务包括：

 : 内存管理

    Lean 不要求程序员手动管理内存。
    系统会在需要存储值时分配空间，并释放那些已无法访问（因而也不再有用）的值。
    具体来说，Lean 使用{tech (key := "reference count")}[引用计数]，每个已分配对象都会维护指向它的引用数量。
    编译器会生成对内存管理例程的调用，用以分配内存和修改引用计数；这些例程由运行时提供，编译后代码中用于表示 Lean 值的数据结构也是如此。

 : 多线程

    {name}`Task` API 可用于编写并行及并发代码。
    运行时负责在操作系统线程间调度 Lean 任务。

 : 原语运算符

    出于效率考虑，许多内置类型都有特殊的表示方式，包括 {lean}`Nat`、{lean}`Array`、{lean}`String` 和定宽整数。
    运行时为这些类型实现原语运算符，以利用这些优化过的表示方式。


原语运算符有很多。
各运算符的说明见{ref "basic-types"}[基本类型]下相应的小节。

# 装箱
%%%
tag := "boxing"
file := some "Boxing"
%%%

:::paragraph
Lean 值在运行时可以用两种方式表示：
* {deftech (key := "Boxed")}_装箱_值可能是指向堆中值的指针，也可能需要通过移位和掩码才能取得。
* {deftech (key := "Unboxed")}_非装箱_值可以直接取得。
:::

装箱值要么是指向对象的指针，此时最低位为 0；要么是立即值，此时最低位为 1，将其表示右移一位即可得到该值。

采用非装箱表示的类型（例如 {name}`UInt8` 和{tech (key := "enum inductive")}[枚举归纳]类型），在编译器能够确定值具有相应类型的上下文中，会表示为对应的 C 类型。
在某些上下文中（例如 {name}`Array` 这样的泛型容器类型），原本采用非装箱表示的值必须先装箱才能存储。
换言之，由于{tech (key := "enum inductive")}[枚举归纳]类型 {name}`Bool` 采用非装箱表示，调用 {name}`Bool.not` 时传入和返回的都是非装箱的 `uint8_t` 值；但 {lean}`Array Bool` 中的各个 {name}`Bool` 值则是装箱的。
归纳类型构造器中类型为 {lean}`Bool` 的字段采用非装箱表示，而多态字段实例化为 {lean}`Bool` 后，其中存储的 {lean}`Bool` 则采用装箱表示。


# 引用计数
%%%
tag := "reference-counting"
file := some "Reference-Counting"
%%%

Lean 使用{deftech (key := "reference count")}_引用计数_来管理内存。
每个已分配对象都会维护一个计数，记录有多少其他对象引用它。
新增引用时计数递增，丢弃引用时计数递减。
当引用计数降为零时，该对象便不再可达，也不可能再参与程序后续的执行。
系统会释放该对象并丢弃它对其他对象的全部引用，这可能进一步触发其他对象的释放。

:::paragraph
引用计数有许多优点：

 : 复用内存

    如果某个对象的引用计数恰在需要分配另一个同样大小的对象时降为零，就可以安全地将原对象的内存复用于新对象。
    因此，当待遍历的数据结构恰好只有一个引用时，许多常见的数据结构遍历（例如 {name}`List.map`）都不必分配内存。

 : 条件允许时原地更新

    字符串和数组等原语类型（参见{ref "String"}[字符串]和{ref "Array"}[数组]）可以在数据共享时执行复制，而在数据未共享时原地修改。
    只要待修改值只有这一个引用，这些原语类型上的许多操作就会直接修改值，而不是复制值。
    这可以显著提升性能。
    精心编写的 {lean}`Array` 代码既能避免不可变数据结构的性能开销，又能保留纯函数便于推理的特性。

 : 可预测性

    引用计数会在可预测的时刻递减。
    因此，可以用引用计数对象管理文件句柄等其他资源。
    在 Lean 中，{name IO.FS.Handle}`Handle` 无需显式关闭，因为它一旦不再可访问就会立即关闭。

 : 更简单的 FFI

    回收未使用的内存时，不需要移动由引用计数管理的对象。
    这大幅简化了与 C 等其他语言所编写代码的交互。

:::

引用计数的传统缺点包括更新引用计数带来的性能开销，以及无法识别和释放循环数据。
前一个缺点通过基于_借用_的分析得到缓解；这种分析可以省去许多引用计数更新。
不过，多线程代码要求线程之间同步引用计数更新，这也会带来显著的开销。
为降低这种开销，Lean 将值划分为可从多个线程访问的值和不可从多个线程访问的值。
单线程引用计数的更新速度可以远高于多线程引用计数，而且许多值只会在单个线程上访问。
这些技术相结合，大幅降低了引用计数的性能开销。
由于 Lean 的可验证片段无法创建循环数据，Lean 运行时没有检测循环数据的机制。
关于 Lean 中引用计数的实现，{citet countingBeans}[]提供了更多细节。

## 观察唯一性

要在 Lean 中编写高效代码，确保数组和字符串只有一个引用至关重要。
原语 {name}`dbgTraceIfShared` 可用于检查数据结构是否存在别名。
调用它时，它会原样返回参数；如果参数的引用计数大于一，则打印所提供的跟踪消息。

{zhdocstring dbgTraceIfShared ZhDoc.Runtime.dbgTraceIfShared}

受 {keywordOf Lean.Parser.Command.eval}`#eval` 具体实现方式的影响，将 {name}`dbgTraceIfShared` 与 {keywordOf Lean.Parser.Command.eval}`#eval` 一同使用可能产生误导。
应当改在明确经过编译并运行的代码中使用它。

::::example "观察唯一性"
:::ioExample
该程序从用户处读取一行输入，将第一个字符替换为空格后打印出来。
如果字符串未被共享，且新旧字符都属于 Unicode 的 7 位 ASCII 子集，替换字符串中的字符时就会执行原地更新。
{name}`dbgTraceIfShared` 调用没有任何输出，这表明字符串确实会原地更新，而不是先被复制。

```ioLean
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println (String.Pos.set (dbgTraceIfShared "String update" str).startPos ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
```

使用以下输入运行时：
```stdin
Here is input.
```

程序输出：
```stdout
 ere is input.
```
标准错误输出为空：
```stderr
```
:::

:::ioExample
这个版本的程序保留了对原字符串的引用，因此调用 {name}`String.set` 时必须复制字符串。
这一点可以从它的标准错误输出中看出。

```ioLean
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println (String.Pos.set (dbgTraceIfShared "String update" str).startPos ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
  IO.println "Original input:"
  IO.println line
```

使用以下输入运行时：
```stdin
Here is input.
```

程序输出：
```stdout
 ere is input.
Original input:
Here is input.
```

在标准错误中可以看到传给 {name}`dbgTraceIfShared` 的消息。
```stderr
shared RC String update
```
:::
::::

## 编译器中间表示（IR）

编译器选项 {option}`trace.compiler.ir.result` 可用于查看函数的编译器中间表示（IR）。
在这种中间表示中，引用计数、内存分配和复用都是显式的：
 * `isShared` 运算符检查引用计数是否为 `1`。
 * `ctor_`$`n` 分配某个类型的第 $`n` 个构造器。
 * `proj_`$`n` 从构造器值中取出第 $`n` 个字段。
 * `set `$`x`﻿`[`$`n`﻿`]` 修改 $`x` 中构造器的第 $`n` 个字段。
 * `ret `$`x` 返回 $`x` 中的值。

引用计数操作的具体方式可能取决于内联等优化阶段的结果。
绝大多数 Lean 代码无须关注这些细节就能获得良好性能，但在编写性能关键型代码时，掌握如何诊断唯一引用相关的问题可能非常重要。

{zhOptionDocs trace.compiler.ir.result ZhDoc.Runtime.Option.trace.compiler.ir.result}

:::example "IR 中的引用计数"
通过编译器中间表示（IR）可以观察引用计数何时递增，这有助于诊断以下情形：本以为某个值只有一个传入引用，但它实际上却被共享。
这里，{lean}`process` 和 {lean}`process'` 都接受一个字符串参数，使用 {name}`String.set` 修改它，并返回一对字符串。
{lean}`process` 将常量字符串作为二元组的第二个元素返回，而 {lean}`process'` 则返回原字符串。

```lean
set_option trace.compiler.ir.result true
```
```lean (name := p1)
def process (str : String) : String × String :=
  (str.set 0 ' ', "")
```
```lean (name := p2)
def process' (str : String) : String × String:=
  (str.set 0 ' ', str)
```

{lean}`process` 的 IR 中不包含 `inc` 或 `dec` 指令。
如果传入的字符串 `x_1` 是唯一引用，那么将它传给 {name}`String.set` 时，它仍然是唯一引用，因此可以就地修改：
```leanOutput p1 (allowDiff := 5)
[Compiler.IR] [result]
    def process._closed_0 : obj :=
      let x_1 : obj := "";
      ret x_1
    def process (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := process._closed_0;
      let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
      ret x_6
```

另一方面，{lean}`process'` 的 IR 会在调用 {name}`String.set` 之前递增该字符串的引用计数。
因此，无论 `x_1` 的原始引用是否唯一，修改后的字符串 `x_4` 都是一个副本：
```leanOutput p2
[Compiler.IR] [result]
    def process' (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      inc x_1;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := ctor_0[Prod.mk] x_4 x_1;
      ret x_5
```
:::

:::example "IR 中的内存复用"
函数 {lean}`discardElems` 是 {name}`List.map` 的简化版本，它将列表中的每个元素替换为 {lean}`()`。
查看其中间表示可以看出，当列表的引用唯一时，它会复用列表的内存。

```lean (name := discardElems)
set_option trace.compiler.ir.result true

def discardElems : List α → List Unit
  | [] => []
  | _ :: xs => () :: discardElems xs
```

这会生成如下 IR：

```leanOutput discardElems
[Compiler.IR] [result]
    def discardElems._redArg (x_1 : tobj) : tobj :=
      case x_1 : tobj of
      List.nil →
        let x_2 : tagged := ctor_0[List.nil];
        ret x_2
      List.cons →
        let x_3 : tobj := proj[1] x_1;
        block_4 (x_5 : tobj) (x_6 : u8) :=
          let x_7 : tagged := ctor_0[PUnit.unit];
          let x_8 : tobj := discardElems._redArg x_3;
          block_9 (x_10 : obj) :=
            ret x_10;
          case x_6 : u8 of
          Bool.false →
            set x_5[1] := x_8;
            set x_5[0] := x_7;
            jmp block_9 x_5
          Bool.true →
            let x_11 : obj := ctor_1[List.cons] x_7 x_8;
            jmp block_9 x_11;
        let x_12 : u8 := isShared x_1;
        case x_12 : u8 of
        Bool.false →
          let x_13 : tobj := proj[0] x_1;
          dec x_13;
          jmp block_4 x_1 x_12
        Bool.true →
          inc x_3;
          dec x_1;
          jmp block_4 ◾ x_12
[Compiler.IR] [result]
    def discardElems (x_1 : ◾) (x_2 : tobj) : tobj :=
      let x_3 : tobj := discardElems._redArg x_2;
      ret x_3
```

在 IR 中，{name}`List.cons` 分支会显式检查参数值是否被共享（即其引用计数是否大于一）。
如果引用唯一，则会递减被丢弃的列表元素 `x_5` 的引用计数，并复用构造器值。
如果引用被共享，则会在 `x_11` 中为结果分配一个新的 {name}`List.cons`。
:::


### 更多主题
%%%
draft := true
%%%

:::planned 208

 * 紧凑区域

 * C 代码应在何时递增或递减引用计数？

 * 借用标注（`@&`）有什么含义？

:::

# 多线程执行
%%%
file := some "Multi-Threaded-Execution"
%%%

Lean 提供了用于并行和并发程序的原语，并使用{tech (key := "tasks")}[任务]来描述它们。
Lean 运行时系统包含一个任务管理器，负责为任务分配硬件资源。
关于它以及用于定义任务的 API，可参阅{ref "concurrency"}[多线程程序一节]中的详细说明。

# 外部函数接口
%%%
tag := "ffi"
file := some "Foreign-Function-Interface"
%%%


*当前接口是为 Lean 内部使用而设计的，应视为不稳定接口*。
未来将对其加以改进和扩展。

Lean 能与任何支持 C ABI 的语言高效互操作。
不过，目前这种支持仅限于传递 Lean 数据类型；尤其是，尚无法在 Lean 与 C 之间按值传入或返回 C {C}`struct` 等复合数据结构。

与其他语言互操作主要使用两个属性：
  {TODO}[它也可以与 `def` 一起使用以提供内部定义，但用户需自行确保两个定义一致。]
* `@[export sym] def leanSym : ...`

:::syntax attr (title := "外部符号")
```grammar
extern $s:str
```

将 Lean 声明绑定到指定的外部符号。
:::

:::syntax attr (title := "导出的符号")
```grammar
export $x:ident
```
以未经名称修饰的符号名 `sym` 导出 Lean 常量。
:::


有关如何从 Lean 调用外部代码以及反向调用的简单示例，请参阅 Lean 源码仓库中的 [FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/ffi) 和[反向 FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/reverse-ffi) 示例。

## Lean ABI

:::leanSection
```lean -show
variable {α₁ αₙ β αᵢ}
private axiom «α₂→…→αₙ₋₁».{u} : Type u
local macro "..." : term => ``(«α₂→…→αₙ₋₁»)
```

Lean 的{deftech (key := "Application Binary Interface")}_应用二进制接口_（ABI）描述了如何按照平台原生调用约定对 Lean 声明的签名进行编码。
它以目标平台的标准 C ABI 和调用约定为基础。
可以用属性 {attr}`extern "sym"` 或 {attr}`export sym` 标记 Lean 声明，使其与外部函数交互：前者令编译后的代码使用 C 声明 {C}`sym` 作为实现，后者则使该声明以 {C}`sym` 的名称供 C 使用。

在这两种情况下，C 声明的类型都从带该属性之声明的 Lean 类型推导而来。
设 {lean}`α₁ → ... → αₙ → β` 是该声明经过{tech (key := "normal form")}[规范化]的类型。
若 `n` 为 0，则相应的 C 声明为
```C
extern s sym;
```
其中，{C}`s` 是按照{ref "ffi-types"}[下一节]所述规则将 {lean}`β` 转换成的 C 类型。
对于标有 {attr}`extern` 的定义，只有在调用该 Lean 模块或某个导入它的模块的初始化器之后，才能保证符号的值已经初始化。
有关{ref "ffi-initialization"}[初始化]的一节将更详细地介绍初始化器。

若 `n` 大于 0，则相应的 C 声明为
```C
s sym(t₁, ..., tₙ);
```
其中，形参类型 `tᵢ` 是类型 {lean}`αᵢ` 转换成的 C 类型。
对于 {attr}`extern`，会先移除所有{tech (key := "irrelevant")}[不相关]类型。
:::

### 将 Lean 类型转换为 C 类型
%%%
tag := "ffi-types"
%%%

:::leanSection
```lean -show
universe u
variable (_p : Prop)
local notation "p" => _p
private axiom «...» : Sort u
local macro "..." : term => ``(«...»)
```

在{tech (key := "application binary interface")}[ABI] 中，Lean 类型按以下方式转换为 C 类型：

* 整数类型 {lean}`UInt8`、……、{lean}`UInt64`、{lean}`USize` 分别由 C 类型 {C}`uint8_t`、……、{C}`uint64_t`、{C}`size_t` 表示。
  若其{ref "fixed-int-runtime"}[运行时表示]需要{tech (key := "boxed")}[装箱]，则会在 FFI 边界处将其拆箱。
* {lean}`Char` 由 {C}`uint32_t` 表示。
* {lean}`Float` 由 {C}`double` 表示。
* {name}`Nat` 和 {name}`Int` 由 {C}`lean_object *` 表示。
  它们的运行时值要么是指向不透明大整数对象的指针；要么在“指针”的最低位为 1（{C}`lean_is_scalar`）时，是经过编码的自然数或整数（{C}`lean_box`/{C}`lean_unbox`）。
* 宇宙 {lean}`Sort u`、类型构造器 {lean}`... → Sort u` 或命题 {lean}`p`​` :`{lean}` Prop` 都是{tech (key := "irrelevant")}[不相关]的，它们要么被静态擦除（见上文），要么由运行时值为 {C}`lean_box(0)` 的 {C}`lean_object *` 表示。
* 其他没有编译器特殊支持的归纳类型采用何种 ABI，取决于该类型的具体情况。
  其 ABI 与这些类型的{ref "run-time-inductives"}[运行时表示]相同。
  其运行时值要么是指向 {C}`lean_object` 某个子类型对象的指针（见下文“归纳类型”一节）；要么，当归纳类型的第 {C}`cidx` 个构造器没有任何相关参数时，是值 {C}`lean_box(cidx)`。

:::

```lean -show
variable (u : Unit)
```

:::example "ABI 中的 `Unit`"
{lean}`u`​` : `{lean}`Unit` 的运行时值始终为 `lean_box(0)`。
:::

### 借用
%%%
tag := "ffi-borrowing"
%%%

默认情况下，{attr}`extern` 函数的所有 {C}`lean_object *` 形参都被视为{deftech (key := "owned")}_拥有_。
外部代码会收到一个“虚拟引用计数令牌”，并负责将该令牌传递给另一个消耗型函数（恰好一次），或通过 {C}`lean_dec` 释放它。
为减少引用计数开销，可以在形参类型前加上 {keywordOf Lean.Parser.Term.borrowed}`@&`，将其标记为{deftech (key := "borrowed")}_借用_。
借用对象只能传给其他非消耗型函数（次数不限），或使用 {C}`lean_inc` 将其转换为拥有值。
在 `lean.h` 中，{C}`lean_object *` 的别名 {C}`lean_obj_arg` 和 {C}`b_lean_obj_arg` 用于在 C 端标示这种区别。
目前，返回值和 `@[export]` 形参始终是拥有的。

:::syntax term (title := "借用形参")
```grammar
@& $_
```
在形参类型前加上 {keyword}`@&`，即可将其标记为{tech (key := "borrowed")}[借用]。
:::

## 初始化
%%%
tag := "ffi-initialization"
%%%

将 Lean 代码纳入更大的程序时，必须先对模块进行{deftech (key := "initialize")}_初始化_，然后才能访问其中的任何声明。
模块初始化包括：
* 初始化所有“常量定义”（零元函数），其中包括从其他函数中提升出来的闭项；
* 执行所有标有 {attr}`init` 属性的代码；以及
* 如果设置了模块初始化器的 `builtin` 形参，则执行所有标有 {attr}`builtin_init` 属性的代码。

对于从 Lean 代码编译出的可执行文件，以及通过 `lean --plugin` 加载的“插件”，模块初始化器会自动带 `builtin` 标志运行。
对于 `lean` 导入的所有其他模块，初始化器运行时不带 `builtin`。
换言之，无论模块是否有可用的原生代码，当且仅当模块被导入时，才会运行其 {attr}`init` 函数；而无论模块是否被导入，{attr}`builtin_init` 函数都只会为原生可执行文件或插件运行。
Lean 编译器使用内置初始化器来完成诸如注册基础解析器之类的工作；即使不导入这些解析器所属的模块，它们也应当可用，这是自举所必需的。

包 `foo` 中模块 `A.B` 的初始化器名为 {C}`initialize_foo_A_B`。
对于 Lean 核心中的模块（例如 {module}`Init.Prelude`），其初始化器名为 {C}`initialize_Init_Prelude`。
模块初始化器会自动初始化所有已导入的模块。
使用相同的 `builtin` 标志运行时，它们还具有幂等性，但并非线程安全。

*关于进程相关功能的重要事项*：使用 `libuv` 中进程相关函数（例如 {name}`Std.IO.Process.getProcessTitle` 和 {name}`Std.IO.Process.setProcessTitle`）的应用程序，必须在调用任何模块初始化器*之前*调用 `lean_setup_args(argc, argv)`（它会返回一个可能经过修改的 `argv`，必须用其替代原始的 `argv`）。
这样可以正确设置进程处理能力，而 Lean 运行时所依赖的某些系统级操作离不开这些能力。

综上所述，在访问任何 Lean 声明之前，应当恰好运行一次如下代码：
```C
char ** lean_setup_args(int argc, char ** argv);

lean_object * initialize_A_B(uint8_t builtin);
lean_object * initialize_C(uint8_t builtin);
...

argv = lean_setup_args(argc, argv); // 使用进程相关功能时

lean_object * res;
// 使用与 Lean 可执行文件相同的默认值
uint8_t builtin = 1;
res = initialize_foo_A_B(builtin);
if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
} else {
    lean_io_result_show_error(res);
    lean_dec(res);
    return ...;  // 初始化失败时，不得访问 Lean 声明
}
res = initialize_bar_C(builtin);
if (lean_io_result_is_ok(res)) {
...

//lean_init_task_manager();  // （间接）使用 `Task` 的代码需要调用此函数
lean_io_mark_end_initialization();
```

此外，凡不是由 Lean 运行时自身生成的线程，都必须调用以下函数进行初始化，才能供 Lean 使用：
```C
void lean_initialize_thread();
```
并且应当调用以下函数终结线程，以释放所有线程局部资源：
```C
void lean_finalize_thread();
```

## 解释器中的 `@[extern]`

Lean 解释器可以运行符号存在于已加载共享库中的 Lean 声明，其中包括标有 {attr}`extern` 的声明。
要运行此类代码（例如使用 {keywordOf Lean.Parser.Command.eval}`#eval`），必须完成以下步骤：
  1. 将包含该声明的模块及其依赖项编译为共享库
  1. 通过 `lean --load-dynlib=` 提供该共享库，以运行导入此模块的代码。

仅加载包含外部符号的外部库并不足够，因为解释器还依赖于为每个 {attr}`extern` 声明生成的代码。
因此，无法在同一文件中解释 {attr}`extern` 声明。
Lean 源码仓库的 [`tests/compiler/foreign`](https://github.com/leanprover/lean4/tree/master/tests/compiler/foreign/) 中包含这种用法的示例。
