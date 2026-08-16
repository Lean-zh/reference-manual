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

#doc (Manual) "任务与线程" =>
%%%
tag := "concurrency"
file := "Tasks and Threads"
%%%

:::leanSection
```lean -show
variable {α : Type u}
```

{deftech (key := "Tasks")}_任务_是编写多线程代码的基本原语。
{lean}`Task α` 表示一个会在某一时刻{tech (key := "resolve promise")}_兑现_为 `α` 类型值的计算；该计算可以在另一个线程上执行。
任务兑现后即可读取其值；若在兑现前尝试取得其值，当前线程会阻塞，直至任务兑现。
任务类似于 JavaScript 中的承诺、Rust 中的 `JoinHandle` 以及 Scala 中的 `Future`。

任务既可以执行纯计算，也可以执行 {name}`IO` 动作。
纯任务的 API 类似于{tech (key := "thunks")}[悬式]的 API：{name}`Task.spawn` 从 {lean}`Unit → α` 函数创建 {lean}`Task α`，而 {name}`Task.get` 等待函数值计算完毕后将其返回。
该值会被缓存，后续请求无须重新计算。
关键区别在于计算发生的时机：悬式的值只有在被强制求值时才计算，而任务会伺机在另一线程中执行。

{name}`IO` 中的任务使用 {name}`IO.asTask` 创建。
类似地，{name}`BaseIO.asTask` 与 {name}`EIO.asTask` 用于在其他 {name}`IO` 单子中创建任务。
这些任务可能产生副作用，也可以与其他任务通信。
:::

当任务的最后一个引用被丢弃时，该任务会被{deftech (key := "cancel")}_取消_。
使用 {name}`Task.spawn` 创建的纯任务会在取消时终止。
使用 {name}`IO.asTask`、{name}`EIO.asTask` 或 {name}`BaseIO.asTask` 生成的任务会继续执行，必须使用 {name}`IO.checkCanceled` 显式检查是否已取消。
可以使用 {name}`IO.cancel` 显式取消任务。

Lean 运行时维护一个用于运行任务的线程池。
若设置了环境变量 {envVar +def}`LEAN_NUM_THREADS`，线程池大小由它决定；否则由当前机器的逻辑处理器数量决定。
线程池大小并非硬性上限；在某些情况下，为避免死锁可以超出该大小。
默认情况下，这些线程用于运行任务；每个任务都有一个{deftech (key := "task priority")}_优先级_（{name}`Task.Priority`），高优先级任务先于低优先级任务执行。
也可以用足够高的优先级生成任务，从而为其分配专用线程。

{docstring Task (label := "type") +hideStructureConstructor +hideFields}

# 创建任务
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Creating-Tasks"
%%%

纯任务通常应使用 {name}`Task.spawn` 创建；{name}`Task.pure` 则表示一个已经兑现为所给值的任务。
非纯任务由某个 {name BaseIO.asTask}`asTask` 动作创建。

## 纯任务
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Creating-Tasks--Pure-Tasks"
%%%

纯任务可以在 {name}`IO` 单子族之外创建。
当其最后一个引用被丢弃时，它们会终止。

{docstring Task.spawn}

{docstring Task.pure}

## 非纯任务
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Creating-Tasks--Impure-Tasks"
%%%

使用某个 {name IO.asTask}`asTask` 函数生成带副作用的任务时，务必要真正执行所得的 {name}`IO` 动作。
每次执行所得动作时都会生成一个任务；调用 {name IO.asTask}`asTask` 时并不会生成任务。
即使不再有任何引用，非纯任务仍会继续运行，不过此时会发出取消请求。
也可以使用 {name}`IO.cancel` 显式请求取消。
非纯任务必须使用 {name}`IO.checkCanceled` 检查取消请求。

{docstring BaseIO.asTask}

{docstring EIO.asTask}

{docstring IO.asTask}

## 优先级
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Creating-Tasks--Priorities"
%%%

线程调度器使用任务优先级把任务分配给线程。
在 {name Task.Priority.default}`default` 到 {name Task.Priority.max}`max` 的优先级范围内，高优先级任务总是先于低优先级任务执行。
以 {name Task.Priority.dedicated}`dedicated` 优先级生成的任务会被分配各自的专用线程，不会与其他任务争用线程池中的线程。

{docstring Task.Priority}

{docstring Task.Priority.default}

{docstring Task.Priority.max}

{docstring Task.Priority.dedicated}

# 任务结果
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Task-Results"
%%%

{docstring Task.get}

{docstring IO.wait}

{docstring IO.waitAny}

# 任务定序
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Sequencing-Tasks"
%%%

这些运算符从已有任务创建新任务。
只要可能，最好使用 {name}`Task.map` 或 {name}`Task.bind`，而不要在新任务中手动调用 {name}`Task.get`，因为前两者不会暂时增大线程池。

{docstring Task.map}

{docstring Task.bind}

{docstring Task.mapList}

{docstring BaseIO.mapTask}

{docstring EIO.mapTask}

{docstring IO.mapTask}

{docstring BaseIO.mapTasks}

{docstring EIO.mapTasks}

{docstring IO.mapTasks}

{docstring BaseIO.bindTask}

{docstring EIO.bindTask}

{docstring IO.bindTask}

{docstring BaseIO.chainTask}

{docstring EIO.chainTask}

{docstring IO.chainTask}

# 取消与状态
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Cancellation-and-Status"
%%%

非纯任务应使用 `IO.checkCanceled` 响应取消；取消可能由 `IO.cancel` 引发，也可能在任务的最后一个引用被丢弃时发生。
纯任务会在取消时自动终止。

{docstring IO.cancel}

{docstring IO.checkCanceled}

{docstring IO.hasFinished}

{docstring IO.getTaskState}

{docstring IO.TaskState}

{docstring IO.getTID}

# 承诺
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Promises"
%%%

承诺表示一个将在未来提供的值。
提供该值称为{deftech (key := "resolve promise")}_兑现_承诺。
承诺创建后，可以像其他值一样存入数据结构或四处传递；尝试读取它时会阻塞，直至它兑现。


{docstring IO.Promise}

{docstring IO.Promise.new}

{docstring IO.Promise.isResolved}

{docstring IO.Promise.result?}

{docstring IO.Promise.result!}

{docstring IO.Promise.resultD}

{docstring IO.Promise.resolve}

# 任务间通信
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Communication-Between-Tasks"
%%%

除本节介绍的类型与操作外，{name}`IO.Ref` 也可用作锁。
取走引用（使用 {name ST.Ref.take}`take`）会使其他线程在读取时阻塞，直到再次用 {name ST.Ref.set}`set` 设置该引用。
这种模式在{ref "ref-locks"}[引用单元一节]中介绍。

## 通道
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Communication-Between-Tasks--Channels"
%%%

导入 {module}`Std.Sync.Channel` 后即可使用本节中的类型与函数。

{docstring Std.Channel}

{docstring Std.Channel.new}

{docstring Std.Channel.send}

{docstring Std.Channel.recv}


{docstring Std.Channel.forAsync}


{docstring Std.Channel.sync}

{docstring Std.Channel.Sync}


{docstring Std.CloseableChannel}

{docstring Std.CloseableChannel.new}





:::leanSection
```lean -show
variable {m : Type → Type v} {α : Type} [MonadLiftT BaseIO m] [Inhabited α] [Monad m]
```
同步通道也可使用 {keywordOf Lean.Parser.Term.doFor}`for` 循环读取。
具体而言，对于每个具有 {inst}`MonadLiftT BaseIO m` 实例的单子 {lean}`m`，以及每个具有 {inst}`Inhabited α` 实例的 {lean}`α`，都存在类型为 {inst}`ForIn m (Std.Channel.Sync α) α` 的实例。
:::
## 互斥锁
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Communication-Between-Tasks--Mutexes"
%%%

导入 {module}`Std.Sync.Mutex` 后即可使用本节中的类型与函数。

{docstring Std.Mutex (label := "type") +hideStructureConstructor +hideFields}

{docstring Std.Mutex.new}

{docstring Std.Mutex.atomically}

{docstring Std.Mutex.atomicallyOnce}

{docstring Std.AtomicT}


## 条件变量
%%%
tag := "Lean-__________________--IO--Tasks-and-Threads--Communication-Between-Tasks--Condition-Variables"
%%%

导入 {module}`Std.Sync.Mutex` 后即可使用本节中的类型与函数。

{docstring Std.Condvar}

{docstring Std.Condvar.new}

{docstring Std.Condvar.wait}

{docstring Std.Condvar.notifyOne}

{docstring Std.Condvar.notifyAll}

{docstring Std.Condvar.waitUntil}
