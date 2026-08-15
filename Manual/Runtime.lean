/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.LexedText
import Manual.Papers
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

{docstring dbgTraceIfShared}

受 {keywordOf Lean.Parser.Command.eval}`#eval` 具体实现方式的影响，将 {name}`dbgTraceIfShared` 与 {keywordOf Lean.Parser.Command.eval}`#eval` 一同使用可能产生误导。
应当改在明确经过编译并运行的代码中使用它。

::::example "观察唯一性"
:::ioExample
该程序从用户处读取一行输入，将第一个字符替换为空格后打印出来。
如果字符串未被共享，且新旧字符都属于 Unicode 的 7 位 ASCII 子集，替换字符串中的字符时就会执行原地更新。
{name}`dbgTraceIfShared` 调用没有任何输出，这表明字符串确实会原地更新，而不是先被复制。

```ioLean
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

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
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

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

{optionDocs trace.compiler.ir.result}

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
  | x :: xs => () :: discardElems xs
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

# Foreign Function Interface
%%%
tag := "ffi"
%%%


*The current interface was designed for internal use in Lean and should be considered unstable*.
It will be refined and extended in the future.

Lean offers efficient interoperability with any language that supports the C ABI.
This support is, however, currently limited to transferring Lean data types; in particular, it is not yet possible to pass or return compound data structures such as C {C}`struct`s by value from or to Lean.

There are two primary attributes for interoperating with other languages:
  {TODO}[It can also be used with `def` to provide an internal definition, but ensuring consistency of both definitions is up to the user.]
* `@[export sym] def leanSym : ...`

:::syntax attr (title := "External Symbols")
```grammar
extern $s:str
```

Binds a Lean declaration to the specified external symbol.
:::

:::syntax attr (title := "Exported Symbols")
```grammar
export $x:ident
```
Exports a Lean constant with the unmangled symbol name `sym`.
:::


For simple examples of how to call foreign code from Lean and vice versa, see [the FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/ffi) and [reverse FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/reverse-ffi) examples in the Lean source repository.

## The Lean ABI

:::leanSection
```lean -show
variable {α₁ αₙ β αᵢ}
private axiom «α₂→…→αₙ₋₁».{u} : Type u
local macro "..." : term => ``(«α₂→…→αₙ₋₁»)
```

The Lean {deftech}_Application Binary Interface_ (ABI) describes how the signature of a Lean declaration is encoded in the platform-native calling convention.
It is based on the standard C ABI and calling convention of the target platform.
Lean declarations can be marked for interaction with foreign functions using either the attribute {attr}`extern "sym"`, which causes compiled code to use the C declaration {C}`sym` as the implementation, or the attribute {attr}`export sym`, which makes the declaration available as {C}`sym` to C.

In both cases, the C declaration's type is derived from the Lean type of the declaration with the attribute.
Let {lean}`α₁ → ... → αₙ → β` be the declaration's {tech (key := "normal form")}[normalized] type.
If `n` is 0, the corresponding C declaration is
```C
extern s sym;
```
where {C}`s` is the C translation of {lean}`β` as specified in {ref "ffi-types"}[the next section].
In the case of a definition marked {attr}`extern`, the symbol's value is only guaranteed to be initialized after calling the Lean module's initializer or that of an importing module.
The section on {ref "ffi-initialization"}[initialization] describes initializers in greater detail.

If `n` is greater than 0, the corresponding C declaration is
```C
s sym(t₁, ..., tₙ);
```
where the parameter types `tᵢ` are the C translations of the types {lean}`αᵢ`.
In the case of {attr}`extern`, all {tech}[irrelevant] types are removed first.
:::

### Translating Types from Lean to C
%%%
tag := "ffi-types"
%%%

:::leanSection
```lean -show
universe u
variable (p : Prop)
private axiom «...» : Sort u
local macro "..." : term => ``(«...»)
```

In the {tech (key := "application binary interface")}[ABI], Lean types are translated to C types as follows:

* The integer types {lean}`UInt8`, …, {lean}`UInt64`, {lean}`USize` are represented by the C types {C}`uint8_t`, ..., {C}`uint64_t`, {C}`size_t`, respectively.
  If their {ref "fixed-int-runtime"}[run-time representation] requires {tech (key := "boxed")}[boxing], then they are unboxed at the FFI boundary.
* {lean}`Char` is represented by {C}`uint32_t`.
* {lean}`Float` is represented by {C}`double`.
* {name}`Nat` and {name}`Int` are represented by {C}`lean_object *`.
  Their runtime values is either a pointer to an opaque bignum object or, if the lowest bit of the “pointer” is 1 ({C}`lean_is_scalar`), an encoded natural number or integer ({C}`lean_box`/{C}`lean_unbox`).
* A universe {lean}`Sort u`, type constructor {lean}`... → Sort u`, or proposition {lean}`p`​` :`{lean}` Prop` is {tech}[irrelevant] and is either statically erased (see above) or represented as a {C}`lean_object *` with the runtime value {C}`lean_box(0)`
* The ABI for other inductive types that don't have special compiler support depends on the specifics of the type.
  It is the same as the {ref "run-time-inductives"}[run-time representation] of these types.
  Its runtime value is either a pointer to an object of a subtype of {C}`lean_object` (see the “Inductive types” section below) or it is the value {C}`lean_box(cidx)` for the {C}`cidx`th constructor of an inductive type if this constructor does not have any relevant parameters.

:::

```lean -show
variable (u : Unit)
```

:::example "`Unit` in the ABI"
The runtime value of {lean}`u`​` : `{lean}`Unit` is always `lean_box(0)`.
:::

### Borrowing
%%%
tag := "ffi-borrowing"
%%%

By default, all {C}`lean_object *` parameters of an {attr}`extern` function are considered {deftech}_owned_.
The external code is passed a “virtual RC token” and is responsible for passing this token along to another consuming function (exactly once) or freeing it via {C}`lean_dec`.
To reduce reference counting overhead, parameters can be marked as {deftech}_borrowed_ by prefixing their type with {keywordOf Lean.Parser.Term.borrowed}`@&`.
Borrowed objects must only be passed to other non-consuming functions (arbitrarily often) or converted to owned values using {C}`lean_inc`.
In `lean.h`, the {C}`lean_object *` aliases {C}`lean_obj_arg` and {C}`b_lean_obj_arg` are used to mark this difference on the C side.
Return values and `@[export]` parameters are always owned at the moment.

:::syntax term (title := "Borrowed Parameters")
```grammar
@& $_
```
Parameters may be marked as {tech}[borrowed] by prefixing their types with {keyword}`@&`.
:::

## Initialization
%%%
tag := "ffi-initialization"
%%%

When including Lean code in a larger program, modules must be {deftech (key := "initialize")}_initialized_ before accessing any of their declarations.
Module initialization entails:
* initialization of all “constant definitions” (nullary functions), including closed terms lifted out of other functions,
* execution of all code marked with the {attr}`init` attribute, and
* execution of all code marked with the {attr}`builtin_init` attribute, if the `builtin` parameter of the module initializer has been set.

The module initializer is automatically run with the `builtin` flag for executables compiled from Lean code and for “plugins” loaded with `lean --plugin`.
For all other modules imported by `lean`, the initializer is run without `builtin`.
In other words, {attr}`init` functions are run if and only if their module is imported, regardless of whether they have native code available, while {attr}`builtin_init` functions are only run for native executable or plugins, regardless of whether their module is imported.
The Lean compiler uses built-in initializers for purposes such as registering basic parsers that should be available even without importing their module, which is necessary for bootstrapping.

The initializer for module `A.B` in a package `foo` is called {C}`initialize_foo_A_B`.
For modules in the Lean core (e.g., {module}`Init.Prelude`), the initializer is called {C}`initialize_Init_Prelude`.
Module initializers will automatically initialize any imported modules.
They are also idempotent (when run with the same `builtin` flag), but not thread-safe.

*Important for process-related functionality*: applications that use process-related functions from `libuv`, such as {name}`Std.IO.Process.getProcessTitle` and {name}`Std.IO.Process.setProcessTitle`, must call `lean_setup_args(argc, argv)` (which returns a potentially modified `argv` that must be used in place of the original) *before* calling any module initializer.
This sets up process handling capabilities correctly, which is essential for certain system-level operations that Lean's runtime may depend on.

Putting everything together, code like the following should be run exactly once before accessing any Lean declarations:
```C
char ** lean_setup_args(int argc, char ** argv);

lean_object * initialize_A_B(uint8_t builtin);
lean_object * initialize_C(uint8_t builtin);
...

argv = lean_setup_args(argc, argv); // if using process-related functionality

lean_object * res;
// use same default as for Lean executables
uint8_t builtin = 1;
res = initialize_foo_A_B(builtin);
if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
} else {
    lean_io_result_show_error(res);
    lean_dec(res);
    return ...;  // do not access Lean declarations if initialization failed
}
res = initialize_bar_C(builtin);
if (lean_io_result_is_ok(res)) {
...

//lean_init_task_manager();  // necessary for code that (indirectly) uses `Task`
lean_io_mark_end_initialization();
```

In addition, any other thread not spawned by the Lean runtime itself must be initialized for Lean use by calling
```C
void lean_initialize_thread();
```
and should be finalized in order to free all thread-local resources by calling
```C
void lean_finalize_thread();
```

## `@[extern]` in the Interpreter

The Lean interpreter can run Lean declarations for which symbols are available in loaded shared libraries, which includes declarations that are marked {attr}`extern`.
To run this code (e.g. with {keywordOf Lean.Parser.Command.eval}`#eval`), the following steps are necessary:
  1. The module containing the declaration and its dependencies must be compiled into a shared library
  1. This shared library should be provided to `lean --load-dynlib=` to run code that imports the module.

It is not sufficient to load the foreign library containing the external symbol because the interpreter depends on code that is emitted for each {attr}`extern` declaration.
Thus it is not possible to interpret an {attr}`extern` declaration in the same file.
The Lean source repository contains an example of this usage in [`tests/compiler/foreign`](https://github.com/leanprover/lean4/tree/master/tests/compiler/foreign/).
