/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Std.Async
import Std.Sync.Channel

import Manual.Meta
import Manual.ZhDocString.Upstream

import Lean.Parser.Command

open Std.Async
open Std (CloseableChannel)

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "异步编程" =>
%%%
file := some "Async"
tag := "Lean-__________________--IO--Asynchronous-Programming"
%%%

{name}`Async` 单子提供构建异步程序的工具与抽象，使程序能够安全地复用不同的数据源。
典型用途包括网络服务器及其他执行 IO 的交互式应用：它们必须响应传入数据、超时、连接断开等多种事件。
一般来说，与操作系统交互的顺序程序只需使用 {name}`IO`。
并行程序应使用 {name}`Task`。
当程序可能花费大量时间等待外部事件或 I/O 时，{name}`Async` 最为合适。

{name}`Async` 最重要的功能是{deftech (key := "event selection")}_事件选择_。
给定一组潜在输入以及对各个输入作出响应的计算，事件选择会确保事件发生时触发相应计算。
每个计算都在关联事件发生时恰好触发一次，并且数据绝不会丢失。
若无适当的库支持，这些性质很难保证。

在底层，异步任务使用任务和承诺来表示。
异步计算先在当前线程上运行，直到必须等待尚不可用的结果，例如定时器或传入的网络数据。
尚不可用的数据由 {name IO.Promise}`Promise` 表示。
此时，异步计算会挂起。
它不会阻塞线程，而是让出控制权，并安排在等待的承诺兑现后恢复执行。
因此，一个线程能够同时推进许多处于等待中的计算。
标准库使用 `libuv` 事件循环作为 I/O 后端，响应定时器、套接字、信号和名称解析等操作系统事件，兑现这些承诺。
不过，异步模型本身仅依赖任务和承诺：任何能兑现承诺的数据源（例如通道）都同样能使异步计算恢复执行。

# 异步计算
%%%
file := "Asynchronous-Computations"
tag := "Lean-__________________--IO--Asynchronous-Programming--Asynchronous-Computations"
%%%

:::paragraph
编写异步程序有三个单子，分别对应 {name}`IO` 的一种变体：

* {name}`Async` 描述可能抛出 {name}`IO.Error` 的异步计算，对应 {name}`IO`。
* {name}`EAsync` 描述可能抛出指定类型错误的异步计算，对应 {name}`EIO`。
* {name}`BaseAsync` 描述不会抛出错误的异步计算，对应 {name}`BaseIO`。

:::

{zhdocstringFrom Async}

{zhdocstringFrom EAsync}

{zhdocstringFrom BaseAsync}

{name}`EAsync` 和 {name}`Async` 中的无限循环使用特殊的 {name}`ForIn` 实例，确保在 {keywordOf Lean.Parser.Term.doRepeat}`repeat` 和 {keywordOf Lean.Parser.Term.doWhile}`while` 循环中不消耗栈帧。
因此，可以在服务器等长期运行的异步应用中使用它们，而不会造成栈溢出。

每个单子都有一种对应的异步任务类型，可由该单子协调。
这些任务可以看作正在执行的计算的句柄。
对单子动作调用 {name}`async` 会创建一个在线程池线程上运行的任务；对任务调用 {name}`await` 会得到一个等待该任务完成的单子动作。
将 {name}`Task.Priority.dedicated` 作为 `prio` 参数传给 {name}`async`，则会改为使用专用线程运行任务。

{zhdocstringFrom ETask}

{zhdocstringFrom AsyncTask}

{zhdocstringFrom MaybeTask +allowMissing}

关键在于，对任务调用 {name}`await` 绝不会阻塞操作系统线程。
只有在 {name}`IO` 与 {name}`Async` 单子之间的{ref "async-run"}[边界]上，线程才会阻塞。
异步任务通过 {name}`await` 等待值时，用于处理该值的代码会附加到任务上。
任务完成时，这段代码会像其他任务一样被调度到线程池中执行。

异步任务与{ref "concurrency"}[其他 Lean 任务]使用相同的{tech (key := "task priority")}[优先级]系统，并由同一个调度器运行。

## 运行异步计算
%%%
file := "Running-Asynchronous-Computations"
tag := "async-run"
%%%

可以从 {name}`IO` 中以等待或阻塞两种方式运行异步计算。
线程等待异步计算时，该计算会先在等待它的线程上执行，直到首次挂起。
挂起后，计算可以被调度到线程池中的任意线程；等待线程则阻塞，直到结果可用。
线程阻塞于异步计算时，该计算作为指定优先级的普通{tech (key := "task")}[任务]在工作线程上运行，调用线程调用 {name}`Task.get` 阻塞等待结果。
由于 {name}`Async` 是 {name}`EAsync` 的定义别名，可以使用{tech (key := "generalized field notation")}[广义字段记法]在 {name}`Async` 类型的项上调用 {name}`EAsync.wait`。

{zhdocstringFrom EAsync.wait}

{zhdocstringFrom BaseAsync.wait}

{zhdocstringFrom Async.block}

{zhdocstringFrom EAsync.block}

{zhdocstringFrom ETask.block}

{zhdocstringFrom AsyncTask.block}

异步计算还可以在 {name}`IO` 中作为普通的 {name}`Task` 运行。

{zhdocstringFrom Async.toIO}

{zhdocstringFrom EAsync.toEIO}

{zhdocstringFrom BaseAsync.toBaseIO}

{zhdocstringFrom EAsync.asTask}

{zhdocstringFrom BaseAsync.asTask}

与 {name}`IO.asTask` 相比，{name}`EAsync.asTask` 调度的是_异步任务_。
{name}`IO.asTask` 创建的任务是同步的，会一直占用工作线程直到完成；{name}`EAsync.asTask` 创建的任务则会在挂起点释放工作线程，并在等待的值可用时恢复为任务。

::::example "运行异步计算"
{name}`Async.block` 运行异步计算，并在 {name}`IO` 中返回其结果。
以下程序打印一条消息，等待十毫秒，然后再打印一条消息：
:::ioExample
```ioLean
module
import Std.Async
open Std.Async

def greet : Async Unit := do
  IO.println "before sleeping"
  sleep 10
  IO.println "after sleeping"

public def main : IO Unit := greet.block
```
它会打印两条消息，中间有短暂的停顿：
```stdout
before sleeping
after sleeping
```
:::
::::

## 管理任务
%%%
file := "Managing-Tasks"
tag := "Lean-__________________--IO--Asynchronous-Programming--Asynchronous-Computations--Managing-Tasks"
%%%

通常通过单子的 {name}`MonadAsync` 和 {name}`MonadAwait` 实例操作异步任务。
各自的方法 {name}`MonadAsync.async` 和 {name}`MonadAwait.await` 从 {namespace}`Std.Async` 中{ref "exporting-names"}[导出]。
主执行线程通常会创建若干异步任务，并在需要它们的结果以继续执行时等待这些结果。
{name}`async` 和 {name}`await` 不是 Lean 编译器的内置函数，也不会触发全程序变换。
它们只是按照框架要求的方式创建或消费与底层承诺关联的任务。

{zhdocstringFrom MonadAwait}

{zhdocstringFrom MonadAsync}

若要启动一个永远不需要其返回值的异步任务，请使用 {name}`background`。

{zhdocstringFrom background}

除 {name}`Async` 单子及任务的实例外，库还提供了允许读取器和状态单子变换器使用 {name}`async` 与 {name}`await` 的实例，以及允许异常单子变换器使用 {name}`await` 的实例。

```lean -show
-- The transformer instances for `await` and `async`.
example : MonadAwait AsyncTask (StateT Nat Async) := inferInstance
example : MonadAwait AsyncTask (ReaderT Nat Async) := inferInstance
example : MonadAwait AsyncTask (ExceptT String Async) := inferInstance
example : MonadAsync AsyncTask (StateT Nat Async) := inferInstance
example : MonadAsync AsyncTask (ReaderT Nat Async) := inferInstance
```

:::example "创建并等待任务"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
{name}`async` 将计算作为并发任务启动，{name}`await` 则等待任务的结果。
这里并发获取一种颜色和一种口味，再将两个结果合成一个有序对：
```lean (name := bothOut)
def fetchColor : Async String := do
  sleep 20
  return "green"

def fetchFlavor : Async String := do
  sleep 20
  return "sweet"

def fetchBoth : Async (String × String) := do
  let color ← async fetchColor
  let flavor ← async fetchFlavor
  return (← await color, ← await flavor)

#eval fetchBoth.block
```
```leanOutput bothOut
("green", "sweet")
```
:::

::::example "后台任务"
{name}`background` 启动一个结果永远不会被等待的计算。
这里有一个在后台运行的日志记录器，打印发送到通道的每条消息：
:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (Channel)

def logger (ch : Channel String) : Async Unit := do
  while true do
    IO.println (← await (← ch.recv))

public def main : IO Unit := do
  let ch ← Channel.new (α := String)
  Async.block do
    background (logger ch)
    discard <| ch.send "hello from the background"
    sleep 20
```
后台日志记录器会在程序退出前打印其收到的消息：
```stdout
hello from the background
```
:::
::::

## 变换和检查任务
%%%
file := "Transforming-and-Inspecting-Tasks"
tag := "Lean-__________________--IO--Asynchronous-Programming--Asynchronous-Computations--Transforming-and-Inspecting-Tasks"
%%%

无需先等待任务完成，就可以变换异步任务最终产生的结果。
{name}`AsyncTask.map` 将函数应用于任务结果，而 {name}`AsyncTask.bindIO` 和 {name}`AsyncTask.mapTaskIO` 将后续 {name}`IO` 工作接到该任务之后。
无论哪种方式，原始任务中的错误都会传播到变换后的任务。

{zhdocstringFrom AsyncTask.map}

{zhdocstringFrom AsyncTask.bindIO}

{zhdocstringFrom AsyncTask.mapTaskIO}

通过获取任务的 {name}`IO.TaskState`，可以在不阻塞的情况下检查其进度。

{zhdocstringFrom ETask.getState}

{zhdocstringFrom AsyncTask.getState}

{name}`MaybeTask` 要么是一个立即可用的值，要么是一个将产生该值的任务。
它可以转换为普通 {name}`Task`，可以阻塞读取其值，也可以映射其值；还可以将包含 {name}`MaybeTask` 的 {name}`Task` 展平为单个 {name}`Task`。

{zhdocstringFrom MaybeTask.toTask}

{zhdocstringFrom MaybeTask.get}

{zhdocstringFrom MaybeTask.map}

{zhdocstringFrom MaybeTask.joinTask}

## 转换
%%%
file := "Conversions"
tag := "Manual-IO-Async-Conversions"
%%%

现有的 {name}`Task`、{name}`IO.Promise` 或 {name}`Except` 值都可以转换为 {name}`Async` 计算。
这些转换使 {name}`Async` 程序能直接调用产生 {name}`Task` 或 {name}`IO.Promise` 的代码，例如基于回调的 API 的包装或手写的异步原语。
{name}`EAsync` 和 {name}`BaseAsync` 也有从 {name}`Task` 与 {name}`Except` 转换的对应操作；从 {name}`IO.Promise` 转换的操作仅用于 {name}`Async`，因为丢弃的承诺会被报告为 {name}`IO.Error`。

{name}`IO.Promise` 可能在兑现前就被丢弃，例如预期负责兑现它的代码被取消或放弃，且该承诺的最后一个引用消失时。
此后，该承诺就再也无法兑现。
由于{tech (key := "reference counts")}[引用计数]是确定性的，运行时会在事情发生的当下检测到它，而非在某个不可预测的后续时刻。
{name}`Async.ofPromise` 和 {name}`Async.ofPurePromise` 会检测被丢弃的承诺，并产生 {name}`Async` 错误而非触发 panic；错误消息可通过 `error` 参数提供，默认为 `the promise linked to the Async was dropped`。

```lean -show
-- A promise that is dropped without ever being resolved surfaces as an `Async`
-- error rather than panicking, because these conversions use `IO.Promise.result?`.
-- Reference counts are deterministic, so the drop happens as soon as the only
-- reference to the promise goes away.
#eval show IO Unit from do
  let msg ← (do
    try
      let _ ← (Async.ofPromise (α := Nat) IO.Promise.new).block
      pure "no error"
    catch e => pure (toString e))
  unless msg == "the promise linked to the Async was dropped" do
    throw (IO.userError "ofPromise: a dropped promise should produce an error")

#eval show IO Unit from do
  let msg ← (do
    try
      let _ ← (Async.ofPurePromise (α := Nat) IO.Promise.new).block
      pure "no error"
    catch e => pure (toString e))
  unless msg == "the promise linked to the Async was dropped" do
    throw (IO.userError "ofPurePromise: a dropped promise should produce an error")
```

{zhdocstringFrom Async.ofTask}

{zhdocstringFrom EAsync.ofTask}

{zhdocstringFrom EAsync.ofETask}

{zhdocstringFrom BaseAsync.ofTask}

{zhdocstringFrom Async.ofIOTask}

{zhdocstringFrom Async.ofAsyncTask}

{zhdocstringFrom Async.ofPromise}

{zhdocstringFrom Async.ofPurePromise}

{name}`ETask.ofPromise!` 直接将承诺转换为任务；若承诺被丢弃，它会触发 panic 而不是产生错误。

{zhdocstringFrom ETask.ofPromise!}

{zhdocstringFrom Async.ofExcept}

{zhdocstringFrom EAsync.ofExcept}

{zhdocstringFrom BaseAsync.ofExcept}

# 并发组合
%%%
file := "Concurrent-Composition"
tag := "Lean-__________________--IO--Asynchronous-Programming--Concurrent-Composition"
%%%

并发组合同时运行多个异步计算，并合并它们的结果。
这些运算以 {name}`async` 和 {name}`await` 定义，但为并发异步编程提供了更高层、更有结构的方式。
每种运算都会以可选参数 `prio` 给出的{tech (key := "task priority")}[优先级]在共享调度器上启动{tech (key := "tasks")}[任务]，然后等待它们。
并发运算分为两类：一类等待每个子计算并返回全部结果，另一类返回首个完成的子计算的结果。

{name}`Async.concurrently` 运行两个计算并将结果作为有序对返回；{name}`Async.concurrentlyAll` 运行计算数组并按相同顺序返回结果。
二者都会等待所有子计算完成，且按位置而非时间顺序等待，因此异常按失败子计算的位置报告，而不是按失败发生的先后报告（见{ref "errors-and-concurrency"}[错误与并发]）。

{name}`Async.race` 运行两个计算并返回先完成者的结果；{name}`Async.raceAll` 对计算数组执行相同操作。
{name}`Async.race` 或 {name}`Async.raceAll` 的结果，是时间上首个完成的子计算的结果，无论它是抛出的异常还是返回的值。
快速失败的计算优先于缓慢成功的计算。

这些运算都不会取消结果未被使用的计算。
在 {name}`Async.race` 和 {name}`Async.raceAll` 中，未最先完成的计算仍会运行至完成，随后丢弃它们的结果。
在 {name}`Async.concurrently` 和 {name}`Async.concurrentlyAll` 中，一个子计算失败并不会停止其他子计算。
{name}`ContextAsync` 上的对应运算（例如 {name}`ContextAsync.race`）则会取消不再需要的计算。

若要并发启动计算且不等待其结果，请使用 {name}`background`。

```lean -show
-- `race` returns the first computation to finish.
#eval do
  let r ← (Async.race (do sleep 80; return 1) (do sleep 10; return 2)).block
  unless r == 2 do throw (IO.userError "race: first to finish")

-- No cancellation: the loser keeps running to completion after the race returns.
#eval show IO Unit from do
  let ranToEnd ← IO.mkRef false
  let r ← (Async.race
    (do sleep 10; return "fast")
    (do sleep 40; ranToEnd.set true; return "slow")).block
  unless r == "fast" do throw (IO.userError "race: winner")
  IO.sleep 80
  unless (← ranToEnd.get) do throw (IO.userError "race: loser was canceled")

-- `ContextAsync.race` cancels the loser.
def ctxRaceCancelsLoser : Async Bool := ContextAsync.run do
  let cancelledP ← IO.Promise.new (α := Bool)
  let loser : ContextAsync Nat := do
    let c ← Selector.cancelled
    discard <| Selectable.one #[.case c (fun _ => pure ())]
    cancelledP.resolve true
    return 2
  let r ← ContextAsync.race (do sleep 5; return 1) loser
  unless r == 1 do throw (IO.userError "ctxRace: winner")
  Async.race (await cancelledP) (do sleep 500; return false)
#eval do
  unless (← ctxRaceCancelsLoser.block) do throw (IO.userError "ctxRace: loser was not cancelled")

-- `concurrentlyAll` returns results in array order, not completion order.
#eval do
  let r ← (Async.concurrentlyAll #[
    (do sleep 50; return 1),
    (do sleep 10; return 2),
    (do sleep 30; return 3)]).block
  unless r == #[1, 2, 3] do throw (IO.userError "concurrentlyAll: order")
```

每种运算都适用于 {name}`BaseAsync`、{name}`EAsync` 和 {name}`Async`。

{zhdocstringFrom Async.concurrently}

{zhdocstringFrom EAsync.concurrently}

{zhdocstringFrom BaseAsync.concurrently}

{zhdocstringFrom Async.concurrentlyAll}

{zhdocstringFrom EAsync.concurrentlyAll}

{zhdocstringFrom BaseAsync.concurrentlyAll}

{zhdocstringFrom Async.race}

{zhdocstringFrom EAsync.race}

{zhdocstringFrom BaseAsync.race}

{zhdocstringFrom Async.raceAll}

{zhdocstringFrom EAsync.raceAll}

{zhdocstringFrom BaseAsync.raceAll}

# 事件选择
%%%
file := "Event-Selection"
tag := "async-select"
%%%

:::leanSection
```lean -show
variable (α : Type)
```
{tech (key := "Event selection")}[事件选择]同时涉及作为事件来源的{deftech (key := "selectors")}_选择器_，以及将选择器与其事件发生时执行的代码配对的{deftech (key := "selectables")}[可选项]。
选择器的事件发生时，该选择器就已{deftech (key := "resolved")}_就绪_。
选择器就绪后，可选项的代码不会立即执行，而是由事件选择调用时才运行。
选择器已就绪的可选项被选中执行时，称其已被{deftech (key := "selected")}_选中_。

{lean}`Selector α` 在事件发生时提供 {lean}`α` 类型的值；{lean}`Selectable α` 则包含一个在选择器就绪后运行的 {name}`Async` 动作。
{name}`Selectable` 中选择器的类型是_构造器_ {name}`Selectable.case` 的字段，而非该类型的{tech (key := "parameter")}[参数]；因此等待不同类型事件数据的可选项可以一起使用。
:::

{zhdocstringFrom Selector}

{zhdocstringFrom Selectable +allowMissing}

事件选择通过以下三个运算调用：
 * {name}`Selectable.one` 阻塞直到一个可选项的事件发生，并返回结果值；
 * {name}`Selectable.tryOne` 检查是否有可选项已就绪，并返回关联值，但不会阻塞；
 * {name}`Selectable.combine` 创建新的 {name}`Selector`：当底层任意 {name}`Selectable` 的选择器事件发生时，新选择器的事件也会发生，并产生该 {name}`Selectable` 的数据。

{zhdocstringFrom Selectable.one}

{zhdocstringFrom Selectable.tryOne}

{zhdocstringFrom Selectable.combine}

:::example "无阻塞轮询"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
{name}`Selectable.tryOne` 检查是否有选择器已经就绪，立即返回对应的值；若都未就绪，则返回 {name}`none`，而不阻塞。
用 `:=` 而非 `←` 定义选择，使 `pick` 表示 {name}`Async` 计算本身而非结果，因此可以重复运行同一次轮询。
```lean (name := tryOneOut)
#eval show IO (Option String × Option String × Option String) from do
  let colors ← Channel.new (α := String)
  let flavors ← Channel.new (α := String)
  let pick := Selectable.tryOne #[
    .case colors.recvSelector fun color => return color,
    .case flavors.recvSelector fun flavor => return flavor
  ]
  let whenEmpty ← pick.block
  discard <| colors.send "gray"
  let afterColor ← pick.block
  discard <| flavors.send "salty"
  let afterFlavor ← pick.block
  return (whenEmpty, afterColor, afterFlavor)
```
```leanOutput tryOneOut
(none, some "gray", some "salty")
```
:::

:::example "选择与超时"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
{name}`CloseableChannel` 通过 {name}`CloseableChannel.recvSelector` 提供选择器，在通道收到值时就绪。
{name}`Selector.sleep` 是经过指定毫秒数后就绪的选择器。
函数 {name}`recv` 组合二者，最多等待 100 毫秒接收值；超时后不返回值并终止：
```lean
def recv (ch : CloseableChannel Nat) : Async (Option Nat) := do
  Selectable.one #[
    .case ch.recvSelector fun n? => return n?,
    .case (← Selector.sleep 100) fun () => return none
  ]
```

若通道包含一个值，则 {name CloseableChannel.recvSelector}`recvSelector` 获胜：
```lean (name := recvWin)
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| ch.send 42
  (recv ch).block
```
```leanOutput recvWin
some 42
```
否则定时器获胜：
```lean (name := timerWin)
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  -- nothing sent: the timeout wins
  (recv ch).block
```
```leanOutput timerWin
none
```
:::

:::example "选择"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
{name}`CloseableChannel` 通过 {name}`CloseableChannel.recvSelector` 提供选择器，在通道收到值时就绪。
函数 {name}`recv2` 选择两个通道中最先返回的值：
```lean
def recv2 (ch1 ch2 : CloseableChannel Nat) : Async (Option Nat) := do
  Selectable.one #[
    .case ch1.recvSelector fun n? => return n?,
    .case ch2.recvSelector fun n? => return n?
  ]
```

若只有一个通道包含值，则返回该值：
```lean (name := chan1)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch1.send 1
  (recv2 ch1 ch2).block
```
```leanOutput chan1
some 1
```

```lean (name := chan2)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch2.send 2
  (recv2 ch1 ch2).block
```
```leanOutput chan2
some 2
```

若两个通道都没有值，{name}`recv2` 会阻塞，直到其中一个通道具有值；先有值者获胜：
```lean (name := recv2race)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 100
    ch1.send 1
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 50
    ch2.send 2
  (recv2 ch1 ch2).block
```
```leanOutput recv2race
some 2
```
:::


{name}`Selectable.one` 和 {name}`Selectable.tryOne` 在收到空可选项数组时都会抛出异常，因为不可能从空无中获取值。

事件选择是{deftech (key := "fair")}_公平的_。
这意味着，在选择器当前已就绪的所有可选项中，每个可选项获胜并调用关联代码的概率相等。
这很重要，因为有偏的事件选择可能使某个可选项_永远_不被调用，从而导致它本应处理的数据源无限积累数据。
在底层，每次都会随机排列可选项的顺序，以保证公平性。

```lean -show
-- Both selection operators reject an empty array.
#eval do
  let e ← try discard <| (Selectable.one (α := Nat) #[]).block; pure "" catch e => pure (toString e)
  unless e == "Selectable.one requires at least one Selectable" do throw (IO.userError s!"one: {e}")
  let e ← try discard <| (Selectable.tryOne (α := Nat) #[]).block; pure "" catch e => pure (toString e)
  unless e == "Selectable.tryOne requires at least one Selectable" do throw (IO.userError s!"tryOne: {e}")

-- Fairness: over many selections between two ready channels, each wins at least once.
def fairness : Async Unit := do
  let a ← CloseableChannel.new (α := Nat)
  let b ← CloseableChannel.new (α := Nat)
  let mut aWins := 0
  let mut bWins := 0
  for _ in [0:200] do
    discard <| a.send 0
    discard <| b.send 0
    let w ← Selectable.one #[.case a.recvSelector (fun _ => return 0), .case b.recvSelector (fun _ => return 1)]
    if w == 0 then aWins := aWins + 1 else bWins := bWins + 1
    -- drain the loser so both channels start each round with exactly one value
    discard <| (if w == 0 then b else a).recv
  unless aWins > 0 && bWins > 0 do throw (IO.userError s!"fairness: {aWins} vs {bWins}")
#eval fairness.block
```

此外，事件选择绝不会导致落败可选项的数据丢失。
实现确保从选择器取出的数据必定传给可选项的代码，并确保选择器就绪后至多调用一次关联可选项的代码。
防止数据丢失和重复投递的协议，将检查选择器是否就绪与实际消费其数据分开，并以原子方式从已就绪选择器中选择一个。

```lean -show
-- Hidden regression test for the no-data-loss claim above. Both channels are
-- empty when selection begins, so the waiting path is taken; only A is delivered
-- during selection, and B's value (sent afterward) must still be received intact.
def noDataLoss : Async (String × String) := do
  let chA ← CloseableChannel.new (α := String)
  let chB ← CloseableChannel.new (α := String)
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 20; discard <| chA.send "from A"
  let winner ← Selectable.one #[
    .case chA.recvSelector fun s? => return ("A:" ++ s?.getD "?"),
    .case chB.recvSelector fun s? => return ("B:" ++ s?.getD "?")
  ]
  discard <| chB.send "from B"
  let next ← Selectable.one #[
    .case chB.recvSelector fun s? => return ("B:" ++ s?.getD "?")
  ]
  return (winner, next)
#eval do
  let (winner, next) ← noDataLoss.block
  unless winner == "A:from A" do throw (IO.userError "noDataLoss winner")
  unless next == "B:from B" do throw (IO.userError "noDataLoss next")
```

## 选择协议
%%%
file := "Selection-Protocol"
tag := "selector-protocol"
%%%

:::sectionNote
本节主要面向新选择器的作者。
:::

事件选择首先随机排列可选项的顺序。
依次调用各个选择器的非阻塞轮询函数 {name}`Selector.tryFn`，直到有一个返回 {name}`some`。
该可选项即为获胜者；随后调用其代码，无需继续其他工作。
在这条快速路径上，只有一个选择器的数据被消费，因此不会发生数据丢失或重复投递。
无需清理，因为返回 {name}`none` 的 {name Selector.tryFn}`tryFn` 必须保持其数据源不变。

若首轮中没有选择器就绪（即每个 {name Selector.tryFn}`tryFn` 都返回 {name}`none`），则必须等待某个选择器就绪。
等待过程分为三个阶段：{ref "selector-protocol-registration"}[注册]、{ref "selector-protocol-race"}[竞争]与{ref "selector-protocol-cleanup"}[清理]。
竞争与注册并发进行：在全部选择器注册完毕前，竞争就已开始，甚至可能已经结束。

获胜可选项的数据会传给其 {name}`Selectable.cont` 续延。
该续延以异步方式计算 {name}`Selectable.one` 返回的结果。

### 注册
%%%
file := "Registration"
tag := "selector-protocol-registration"
%%%

注册前会再次随机排列可选项的顺序。
注册过程中，通过 {name}`Selector.registerFn` 依次向各个选择器注册一个{tech (key := "waiter")}[等待器]。
选择器必须将注册仅视为对其数据感兴趣的表示，因此 {name Selector.registerFn}`registerFn` 本身不应消费数据。

首次调用 {name Selector.registerFn}`registerFn` 后，竞争便开始。
最先有数据的选择器通过等待器赢得竞争。
选择器可以在调用自身的 {name Selector.registerFn}`registerFn` 期间获胜。
如果数据在最初的 {name Selector.tryFn}`tryFn` 循环与注册阶段之间变得可用，就没有理由延后到其他时候才获胜。

一次选择涉及的所有等待器共享一个原子标志，表示是否已选出获胜者；每个等待器又各有一个承诺，供选择器获胜时投递数据。
若该标志已经设置，注册过程就会提前停止，因为这说明某个选择器已经获胜，继续注册没有意义。
同样，若 {name Selector.registerFn}`registerFn` 抛出异常，该过程也会停止。
若已有选择器获胜，则返回其结果并丢弃异常；否则，异常成为此次选择的结果。

### 竞争
%%%
file := "Racing"
tag := "selector-protocol-race"
%%%

首个可选项一旦注册，竞争便开始，直到一个可选项获胜或注册因异常而失败。
可选项的事件就绪时，会在自己的等待器上调用 {name}`Waiter.race`；等待器判断它是否获胜。

{deftech (key := "waiter")}_等待器_是一种以原子方式从提供的值中选出一个值的机制。
其内部包含一个原子标志，用于表示已经选出了获胜者。
客户端有值时，会带着两个回调调用 {name}`Waiter.race`：一个用于所提供的值未被接受（竞争落败）的情况，另一个用于值被接受的情况。
竞争获胜时调用的回调应兑现等待器的承诺，该承诺会作为参数提供给获胜回调。
竞争落败时调用的回调必须保持所有数据原样不动。
这一两阶段协议保证不会丢失数据，因为选择器只有在已经获胜后才消费事件。

{zhdocstringFrom Waiter +allowMissing}

{zhdocstringFrom Waiter.race}

{zhdocstringFrom Waiter.withPromise}

{zhdocstringFrom Waiter.checkFinished}

### 清理
%%%
file := "Cleanup"
tag := "selector-protocol-cleanup"
%%%

{ref "selector-protocol-race"}[竞争]结束后，选择器有机会进行清理。
无论是有选择器获胜，还是 {name}`Selector.registerFn` 抛出异常，都会进行清理；但最初的 {name Selector.tryFn}`tryFn` 循环直接返回值时不会清理。
此阶段会对数组中的每个选择器调用 {name}`Selector.unregisterFn`，不论它是否在{ref "selector-protocol-registration"}[注册阶段]注册过，也不论它是否在注册期间抛出异常。

清理总会发生，不受注册、竞争或此前选择器的 {name Selector.unregisterFn}`unregisterFn` 实现中发生的错误影响。
因此，必须保证即使选择器的 {name Selector.registerFn}`registerFn` 落败、从未被调用或抛出了异常，调用其 {name Selector.unregisterFn}`unregisterFn` 仍然安全。


:::example "自然数节拍器"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```

{name}`natTicker` 是每隔 100 毫秒提供一个 {name}`Nat` 的选择器，其值逐次递增。
其状态由两个值决定：
1. 一个计数器，即保存下一个待发出 {name}`Nat` 的 {name}`IO.Ref`；
2. 该过程的启动时间。

{name}`Selector.tryFn` 检查是否已为每个发出的 `Nat` 经过至少 100 毫秒。
若是，则递增该值并立即返回：
```lean
def tickerTryFn (counter : IO.Ref Nat) (startMs : Nat) := do
  let nowMs ← IO.monoMsNow
  let n ← counter.get
  if nowMs ≥ startMs + n * 100 then
    counter.set (n + 1)
    return (some n)
  else
    return none
```

若竞争未立即进行，则注册一个等待器。
随后启动后台任务，休眠直到下一个 {name}`Nat` 就绪，并调用等待器的 {name Waiter.race}`race`；若竞争获胜，就递增计数器：
```lean
def tickerRegisterFn (counter : IO.Ref Nat) (startMs : Nat)
    (waiter : Waiter Nat) : Async Unit := do
  let n ← counter.get
  let delay := startMs + n * 100 - (← IO.monoMsNow)
  let sleep ← Sleep.mk <| .ofNat delay
  discard <| background do
    sleep.wait
    waiter.race (pure ()) fun promise => do
      counter.set (n + 1)
      promise.resolve (.ok n)
```
这些组件可以组合成一个选择器：
```lean
def natTicker : IO (Selector Nat) := do
  let current ← IO.mkRef 0
  let startMs ← IO.monoMsNow
  return {
    tryFn := tickerTryFn current startMs
    registerFn := tickerRegisterFn current startMs
    unregisterFn := pure ()
  }
```

该选择器不是线程安全的。
在同一次 {name}`Selectable.one` 中多次使用它是安全的，因为不会丢失数据（仅在明确获胜后才调用 {name ST.Ref.set}`set`）。
然而，在同一个 {name}`natTicker` 上并发调用 {name}`Selectable.one` 可能造成数据竞争。
修正此问题需要谨慎地加锁。

```lean -show
-- Backs the "multiple uses in a single `Selectable.one`" safety claim above:
-- using the same ticker in two branches of one selection emits each value once.
#eval do
  let t ← natTicker
  let a ← (Selectable.one #[.case t (fun n => return n)]).block
  let b ← (Selectable.one #[
    .case t (fun n => return n),
    .case t (fun n => return n)
  ]).block
  unless a == 0 do throw (IO.userError "natTicker: first tick")
  unless b == 1 do throw (IO.userError "natTicker: shared use in one selection")
```
:::

# 标准选择器
%%%
file := "Standard-Selectors"
tag := "Lean-__________________--IO--Asynchronous-Programming--Standard-Selectors"
%%%

标准库为定时器、通过通道接收值，以及{ref "async-network"}[网络套接字]等事件提供了多种{tech (key := "selectors")}[选择器]。
这些选择器让 {name}`Async` 程序能够可靠地处理来自多种数据源的输入。

选择器建立在某个数据源之上时，必须避免再直接使用同一数据源，这一点非常重要。
例如，不应在同一通道上同时使用 {name Std.CloseableChannel.recvSelector}`recvSelector` 和 {name Std.CloseableChannel.recv}`recv`。
若选择器依赖对数据源实际状态的独占控制，这种混用可能违反{ref "selector-protocol"}[选择器协议]。

{zhdocstringFrom Sleep.selector}

{zhdocstringFrom Std.Channel.recvSelector}

{zhdocstringFrom Std.CloseableChannel.recvSelector}

{zhdocstringFrom Std.Broadcast.Receiver.recvSelector}

{zhdocstringFrom Std.Notify.selector}

{zhdocstringFrom Std.CancellationToken.selector}

{zhdocstringFrom Std.CancellationContext.doneSelector}

{zhdocstringFrom Selector.cancelled}

{zhdocstringFrom TCP.Socket.Server.acceptSelector}

{zhdocstringFrom TCP.Socket.Client.recvSelector}

{zhdocstringFrom UDP.Socket.recvSelector}

{zhdocstringFrom Signal.Waiter.selector}

{zhdocstringFrom Std.StreamMap.selector}

# 错误
%%%
file := "Errors"
tag := "Lean-__________________--IO--Asynchronous-Programming--Errors"
%%%

:::leanSection
```lean -show
variable (α : Type) (ε : Type)
```
{name}`Async` 中的错误处理与 {name}`IO` 中的错误处理对应：
 * 与 {name}`BaseIO` 一样，{name}`BaseAsync` 不能抛出错误。
 * 与 {name}`EIO` 一样，{name}`EAsync` 以错误类型为参数。在底层，{lean}`EAsync ε α` 就是 {lean}`BaseAsync (Except ε α)`，其 {name}`Monad` 实例类似于 {name}`ExceptT` 的实例。
 * {lean}`Async α` 就是 {lean}`EAsync IO.Error α`，正如 {lean}`IO α` 就是 {lean}`EIO IO.Error α`。
:::

{name}`Async` 错误处理的细节由这种组织方式决定。
通过 {name}`async` 创建的异步任务抛出异常时，父任务不会观察到它。
只有通过 {name}`await` 请求任务结果时，错误才会显现。
如果从未对任务调用 {name}`await`，*错误便会消失*。
换言之，通过 {name}`background` 或 {name}`ContextAsync.disown` 创建的任务中的错误完全不会传播。

```lean -show
-- Hidden regression tests for the error-handling claims above.

-- A spawned task's error surfaces at `await`, not at `async`:
def caughtAtAwait : Async Nat := do
  let t ← async (m := Async) do
    throw (IO.userError "boom")
  try await t catch _ => return 0
#eval do
  let r ← caughtAtAwait.block
  unless r == 0 do throw (IO.userError "caughtAtAwait")

-- An error in a `background` task is silently swallowed:
def swallowedError : Async String := do
  background (t := AsyncTask) (show Async Unit from throw (IO.userError "lost"))
  sleep 30
  return "no error observed"
#eval do
  let r ← swallowedError.block
  unless r == "no error observed" do throw (IO.userError "swallowedError")

-- An error in a `ContextAsync.disown` task is silently swallowed:
def disownSwallows : Async String := ContextAsync.run do
  ContextAsync.disown (throw (IO.userError "lost") : ContextAsync Unit)
  sleep 30
  return "no error observed"
#eval do
  let r ← disownSwallows.block
  unless r == "no error observed" do throw (IO.userError "disownSwallows")

-- `bind` short-circuits: statements after a throw don't run (like `ExceptT`):
def bindShortCircuits : Async (List Nat) := do
  let log ← IO.mkRef ([] : List Nat)
  try
    log.modify (· ++ [1])
    throw (IO.userError "stop")
    log.modify (· ++ [2])
  catch _ => pure ()
  log.get
#eval do
  let r ← bindShortCircuits.block
  unless r == [1] do throw (IO.userError "bindShortCircuits")

-- A throwing finalizer masks the original error:
def finalizerMasks : Async String := do
  try
    try
      throw (IO.userError "original")
    finally
      (throw (IO.userError "from finalizer") : Async Unit)
  catch e => return (toString e)
#eval do
  let r ← finalizerMasks.block
  unless r == "from finalizer" do throw (IO.userError "finalizerMasks")
```

## 错误与并发
%%%
file := "Errors-and-Concurrency"
tag := "errors-and-concurrency"
%%%

并发运算 {name}`Async.concurrently` 和 {name}`Async.concurrentlyAll` 按位置而非时间顺序等待子任务的结果。
这意味着任务产生的错误按源代码顺序报告，而不是按错误发生的时间顺序报告。

:::example "并发与错误传播"
```imports -show
import Std.Async
```
```lean -show
open Std Async
```
{name}`failFast` 等待 5 毫秒后抛出异常，{name}`failSlow` 则等待 250 毫秒：
```lean
def failFast : Async Nat := do
  sleep 5
  throw <| .userError "Fast failure"

def failSlow : Async Nat := do
  sleep 250
  throw <| .userError "Slow failure"
```
通过 {name}`Async.concurrently` 运行时，程序会以 {name}`failSlow` 的错误失败。虽然它比 {name}`failFast` 的错误更晚发生，但程序先等待的是 {name}`failSlow` 的结果。
```lean +error (name := failed)
#eval Async.block do
  let val ← Async.concurrently (prio := .dedicated) failSlow failFast
  pure ()
```
```leanOutput failed
Slow failure
```
:::

{name}`Async.race` 和 {name}`Async.raceAll` 返回_首个_完成任务的结果，无论成功还是失败。
这意味着迅速产生的错误优先于缓慢产生的成功结果。

```lean -show
-- `race` resolves with the first to *finish*: a fast error beats a slow success.
def raceFailFast : Async Nat := do sleep 10; throw (IO.userError "fast failure")
def raceSlowOk : Async Nat := do sleep 100; return 42
#eval do
  let r ← (show IO String from do
    try
      discard <| (Async.race raceFailFast raceSlowOk).block
      return "no error"
    catch e => return (toString e))
  unless r == "fast failure" do throw (IO.userError "raceFailFast")
```

## 事件选择中的错误
%%%
file := "Errors-in-Event-Selection"
tag := "Lean-__________________--IO--Asynchronous-Programming--Errors--Errors-in-Event-Selection"
%%%

选择期间，{ref "async-select"}[协议]的任何阶段都可能发生错误。
选择器在最初的 {name Selector.tryFn}`tryFn` 循环中抛出错误时，选择立即终止。
{name Selector.registerFn}`registerFn` 抛出的错误会成为选择结果，除非已有竞争获胜者；后一种情况下优先采用获胜者的结果。
{name Selector.unregisterFn}`unregisterFn` 抛出的错误会被抑制并丢弃。
竞争获胜的选择器可用 {name}`Except.ok` 或 {name}`Except.error` 兑现承诺；后一种情况下，{name}`Selectable.one` 调用本身的结果也是错误。

```lean -show
-- A tryFn error terminates the selection, even when a sibling is ready.
def tryFnThrower : Selector Nat := {
  tryFn := throw (IO.userError "poll failed")
  registerFn := fun _ => pure ()
  unregisterFn := pure ()
}
def tryFnErrorTerminates : Async Unit := do
  let mut sawError := 0
  for _ in [0:20] do
    let ch ← CloseableChannel.new (α := Nat)
    discard <| ch.send 1
    let r ← try discard <| Selectable.one #[.case ch.recvSelector (fun _ => return 0), .case tryFnThrower (fun _ => return 1)]; pure "" catch e => pure (toString e)
    if r == "poll failed" then sawError := sawError + 1
    else if r != "" then throw (IO.userError s!"tryFnErrorTerminates: {r}")
  -- with random order, the throwing selector is sometimes polled first
  unless sawError > 0 do throw (IO.userError "tryFnErrorTerminates: error never surfaced")
#eval tryFnErrorTerminates.block

-- A registerFn error is discarded when a winner already exists.
def registerErrorAfterWin : Async Unit := do
  let mut valueWon := 0
  for _ in [0:20] do
    let ch ← CloseableChannel.new (α := Nat)
    -- Makes the channel ready, then fails. If the channel was registered first, it wins and the
    -- error is discarded; otherwise registration stops and the error is the result.
    let sendThenThrow : Selector Nat := {
      tryFn := return none
      registerFn := fun _ => do discard <| ch.send 5; throw (IO.userError "ignored")
      unregisterFn := pure ()
    }
    let r ← try Selectable.one #[.case ch.recvSelector (fun n? => return n?.getD 0), .case sendThenThrow (fun n => return n)]
      catch e => if toString e == "ignored" then pure 0 else throw e
    if r == 5 then valueWon := valueWon + 1
    else if r != 0 then throw (IO.userError s!"registerErrorAfterWin: {r}")
  unless valueWon > 0 do throw (IO.userError "registerErrorAfterWin: value never won")
#eval registerErrorAfterWin.block
```

```lean -show
-- An error thrown by the winning continuation propagates out of `Selectable.one`.
def selErrorPropagates : Async String := do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| ch.send 1
  try
    Selectable.one #[.case ch.recvSelector fun _ =>
      throw (IO.userError "cont failed")]
  catch e => return (toString e)
#eval do
  let r ← selErrorPropagates.block
  unless r == "cont failed" do throw (IO.userError "selErrorPropagates")
```

```lean -show
-- When a sibling's registerFn throws, the selection fails with that error, the other
-- selectors are unregistered, and a later send is received rather than consumed by a stale waiter.
def registerErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => throw (IO.userError "boom")
  unregisterFn := pure ()
}
def registerErrorCleansUp : Async Unit := do
  let ch ← CloseableChannel.new (α := Nat)
  let unregistered ← IO.mkRef false
  let victim : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => pure ()
    unregisterFn := unregistered.set true
  }
  let err ← try
      discard <| Selectable.one #[
        .case ch.recvSelector (fun _ => return 0),
        .case victim (fun _ => return 1),
        .case registerErrorThrower (fun _ => return 2)]
      pure ""
    catch e => pure (toString e)
  unless err == "boom" do throw (IO.userError s!"registerErrorCleansUp: got '{err}'")
  unless (← unregistered.get) do throw (IO.userError "registerErrorCleansUp: victim was not unregistered")
  discard <| ch.send 7
  unless (← ch.tryRecv) == some 7 do throw (IO.userError "registerErrorCleansUp: value was consumed by a stale waiter")
#eval registerErrorCleansUp.block
```

```lean -show
-- When a sibling's unregisterFn throws, every other selector is still unregistered and the
-- winning selectable's value is returned.
def unregisterErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => pure ()
  unregisterFn := throw (IO.userError "boom")
}
def unregisterErrorCleansUp : Async Unit := do
  let cleaned ← IO.mkRef false
  let ch ← CloseableChannel.new (α := Nat)
  let victim : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => pure ()
    unregisterFn := cleaned.set true
  }
  -- Sends on the channel during registration, so the channel wins the race rather than the initial poll.
  let sender : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => discard <| ch.send 0
    unregisterFn := pure ()
  }
  let r ← Selectable.one #[
    .case victim (fun _ => return 0),
    .case ch.recvSelector (fun _ => return 1),
    .case unregisterErrorThrower (fun _ => return 2),
    .case sender (fun _ => return 3)]
  unless r == 1 do throw (IO.userError s!"unregisterErrorCleansUp: winner was {r}")
  unless (← cleaned.get) do throw (IO.userError "unregisterErrorCleansUp: victim was not unregistered")
#eval unregisterErrorCleansUp.block
```

# 定时器
%%%
file := "Timers"
tag := "Lean-__________________--IO--Asynchronous-Programming--Timers"
%%%

定时器分为两类：_休眠定时器_允许计算等待给定时长一次；_间隔定时器_则以该时长为间隔重复提供事件。
创建定时器不会开始倒计时。
首次调用 {name}`Sleep.wait`、调用 {name}`Interval.tick`，或定时器首次参与选择时，才会开始运行。
休眠定时器在{ref "selector-protocol-race"}[竞争]中落败后，会在下一次选择时重新开始。
使用 {name}`Sleep.stop` 或 {name}`Interval.stop` 停止定时器，会使等待该定时器的所有任务永远挂起。

```lean -show
def timeIt (act : Async α) : Async Nat := do
  let t0 ← IO.monoMsNow
  discard act
  return (← IO.monoMsNow) - t0

-- The countdown of a `Selector.sleep` begins at its first selection, not at creation.
def sleepSelectorStartsLazily : Async Unit := do
  let s ← Selector.sleep 100
  sleep 150
  let ch ← CloseableChannel.new (α := Nat)
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms ≥ 80 do throw (IO.userError s!"Selector.sleep started before its first selection ({ms} ms)")
#eval sleepSelectorStartsLazily.block

-- A `Selector.sleep` that has fired resolves immediately in later selections.
def sleepSelectorIsSingleShot : Async Unit := do
  let s ← Selector.sleep 100
  let ch ← CloseableChannel.new (α := Nat)
  discard <| Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())]
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms < 50 do throw (IO.userError s!"Selector.sleep fired again after {ms} ms")
#eval sleepSelectorIsSingleShot.block

-- A `Selector.sleep` that loses a selection restarts its countdown at the next selection.
def sleepSelectorRestartsAfterLoss : Async Unit := do
  let s ← Selector.sleep 100
  let ch ← CloseableChannel.new (α := Nat)
  discard <| background (do sleep 30; discard <| ch.send 1)
  discard <| Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())]
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms ≥ 80 do throw (IO.userError s!"Selector.sleep kept its countdown after losing ({ms} ms)")
#eval sleepSelectorRestartsAfterLoss.block
```

{zhdocstringFrom sleep}

{zhdocstringFrom Sleep +allowMissing}

{zhdocstringFrom Sleep.mk}

{zhdocstringFrom Sleep.wait}

{zhdocstringFrom Sleep.reset}

{zhdocstringFrom Sleep.stop}

{zhdocstringFrom Interval +allowMissing}

{zhdocstringFrom Interval.mk}

{zhdocstringFrom Interval.tick}

{zhdocstringFrom Interval.reset}

{zhdocstringFrom Interval.stop}

{zhdocstringFrom Selector.sleep}



::::example "选择器与定时器"
此程序运行一个循环。
每轮迭代最多等待两秒钟以获取一行输入。
若收到输入，就回显该行并继续循环。
若本轮超时，则程序退出。
通过 {name}`Selectable.one` 让定时器与传递输入行的通道竞争，以检查是否超时。
该通道可以参与选择，并由一个读取 `stdin` 的专用线程向其提供数据。

:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (CloseableChannel)

-- Blocking reader on a dedicated thread: forward each line, close on EOF.
partial def reader (stdin : IO.FS.Stream) (ch : CloseableChannel String) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    discard <| (ch.close).toBaseIO
  else
    discard <| ch.send line
    reader stdin ch

-- Echo each line; stop on EOF (channel closed) or 2s of silence.
partial def echo (ch : CloseableChannel String) : Async Unit := do
  let more ← Selectable.one #[
    .case ch.recvSelector fun
      | some line => do IO.print (s!"got: {line}"); return true
      | none => do IO.println "done"; return false,
    .case (← Selector.sleep 2000) fun _ => do
      IO.println "done"
      return false
  ]
  if more then echo ch

public def main : IO Unit := do
  let ch ← CloseableChannel.new (α := String)
  discard <| IO.asTask (prio := .dedicated) (reader (← IO.getStdin) ch)
  (echo ch).block
```
使用以下输入运行时：
```stdin
One line
Another
```
它产生以下输出：
```stdout
got: One line
got: Another
done
```
:::

::::

# 异步 I/O
%%%
file := "Asynchronous-I___O"
tag := "Lean-__________________--IO--Asynchronous-Programming--Asynchronous-I___O"
%%%
:::leanSection
```lean -show
open Std.Async.IO
open Std (Channel Broadcast)
variable {α : Type} [Inhabited α]
```
类型类 {name}`AsyncRead`、{name}`AsyncWrite` 和 {name}`AsyncStream` 提供带缓冲的异步 I/O。
主要的 {name}`AsyncRead` 实例包括 {inst}`AsyncRead (Channel α) α`、{inst}`AsyncRead (CloseableChannel α) (Option α)` 和 {inst}`AsyncRead (Broadcast.Receiver α) (Option α)`。
类似地，主要的 {name}`AsyncWrite` 实例包括 {inst}`AsyncWrite (Channel α) α`、{inst}`AsyncWrite (CloseableChannel α) α` 和 {inst}`AsyncWrite (Broadcast α) α`。
{name}`AsyncStream` 在与 {name}`AsyncRead` 相同的类型上具有实例，但提供基于{tech (key := "selector")}[选择器]的元素迭代，因此可以与其他数据源组合。
:::

{zhdocstringFrom Std.Async.IO.AsyncRead +allowMissing}

{zhdocstringFrom Std.Async.IO.AsyncWrite +allowMissing}

{zhdocstringFrom Std.Async.IO.AsyncStream +allowMissing}

## 网络
%%%
file := "Network"
tag := "async-network"
%%%

标准库提供异步 TCP 和 UDP 套接字，以及 DNS 名称解析。
接受连接、接收数据和解析名称等需要等待网络的操作都是 {name}`Async` 动作。
TCP 和 UDP 套接字还提供{tech (key := "selectors")}[选择器]，即 {name}`TCP.Socket.Server.acceptSelector`、{name}`TCP.Socket.Client.recvSelector` 和 {name}`UDP.Socket.recvSelector`，因此可通过{ref "async-select"}[事件选择]将网络事件与其他 I/O 复用。
套接字地址由 {name}`Std.Net.SocketAddress` 和 {name}`Std.Net.IPAddr` 类型表示。
与其他选择器一样，套接字的选择器及其对应的阻塞操作都要求独占控制该套接字。
不得在同一套接字上同时使用二者。

### TCP

TCP 面向连接：客户端先与服务器建立连接，随后双方交换可靠、有序的字节流。
该协议包含确保已发送数据确实到达的机制，包括重传缺失部分；这些功能依赖已建立的连接及其关联状态。
TCP 服务器套接字接受传入连接，TCP 客户端套接字则连接服务器并交换数据。
设置服务器时，依次创建套接字、绑定地址、开始监听，然后接受连接。
设置客户端时，先创建套接字，连接到地址，再用它发送和接收数据。

{zhdocstringFrom TCP.Socket.Server +allowMissing}

{zhdocstringFrom TCP.Socket.Server.mk}

{zhdocstringFrom TCP.Socket.Server.bind}

{zhdocstringFrom TCP.Socket.Server.listen}

{zhdocstringFrom TCP.Socket.Server.accept}

{zhdocstringFrom TCP.Socket.Server.tryAccept}

{zhdocstringFrom TCP.Socket.Server.getSockName}

{zhdocstringFrom TCP.Socket.Server.noDelay}

{zhdocstringFrom TCP.Socket.Server.keepAlive}

{zhdocstringFrom TCP.Socket.Client +allowMissing}

{zhdocstringFrom TCP.Socket.Client.mk}

{zhdocstringFrom TCP.Socket.Client.bind}

{zhdocstringFrom TCP.Socket.Client.connect}

{zhdocstringFrom TCP.Socket.Client.send}

{zhdocstringFrom TCP.Socket.Client.sendAll}

{zhdocstringFrom TCP.Socket.Client.recv?}

{zhdocstringFrom TCP.Socket.Client.shutdown}

{zhdocstringFrom TCP.Socket.Client.getPeerName}

{zhdocstringFrom TCP.Socket.Client.getSockName}

{zhdocstringFrom TCP.Socket.Client.noDelay}

{zhdocstringFrom TCP.Socket.Client.keepAlive}

### UDP

与 TCP 不同，UDP 无连接：单个套接字无需先建立连接，就能与任意地址收发称为{deftech (key := "datagrams")}_数据报_的独立消息。
UDP 不提供确保数据报实际到达的机制；这需要由应用层处理。
数据报还可以通过广播或组播同时投递给多个接收方。

{zhdocstringFrom UDP.Socket.mk}

{zhdocstringFrom UDP.Socket.bind}

{zhdocstringFrom UDP.Socket.connect}

{zhdocstringFrom UDP.Socket.send}

{zhdocstringFrom UDP.Socket.sendAll}

{zhdocstringFrom UDP.Socket.recv}

{zhdocstringFrom UDP.Socket.getSockName}

{zhdocstringFrom UDP.Socket.getPeerName}

{zhdocstringFrom UDP.Socket.setBroadcast}

{zhdocstringFrom UDP.Socket.setTTL}

{zhdocstringFrom UDP.Socket.setMulticastLoop}

{zhdocstringFrom UDP.Socket.setMulticastTTL}

{zhdocstringFrom UDP.Socket.setMulticastInterface}

{zhdocstringFrom UDP.Socket.setMembership}

{zhdocstringFrom UDP.Membership +allowMissing}

### DNS

DNS 解析在名称与套接字地址之间转换。
{name}`DNS.getAddrInfo` 将主机与服务正向解析为地址列表，{name}`DNS.getNameInfo` 则将地址反向解析为主机与服务。

{zhdocstringFrom DNS.getAddrInfo}

{zhdocstringFrom DNS.getNameInfo}

{zhdocstringFrom DNS.NameInfo +allowMissing}

## 信号
%%%
file := "Signals"
tag := "Lean-__________________--IO--Asynchronous-Programming--Asynchronous-I___O--Signals"
%%%

Unix 风格的信号是随时可能从操作系统接收的异步通知。
例如，用户按下 `Ctrl-C` 时，系统会向进程发送 `SIGINT`。
{name}`Signal.Waiter` 是底层信号处理器的 Lean 表示。
可处理的信号由类型 {name}`Signal` 枚举：

{zhdocstringFrom Signal}

某些信号无法捕获，具体取决于平台。
在类 Unix 操作系统上，`SIGKILL` 和 `SIGSTOP` 无法捕获。
`SIGBUS`、`SIGFPE`、`SIGILL` 和 `SIGSEGV` 也无法处理，因为 Lean 使用 `libuv` 安装信号处理器，而 `libuv` 无法安全地捕获这些信号。
此外，Lean 运行时系统会忽略 `SIGPIPE`。
在 Windows 上，可以为 `SIGTERM` 和 `SIGABRT` 创建等待器，但它们永远不会触发。控制台关闭时会触发 `SIGHUP`，并留出约十秒进行清理。终端处于原始模式时不会投递 `SIGINT`；`SIGWINCH` 通过模拟实现，可能不够及时。

要安装信号处理器，先用 {name}`Signal.Waiter.mk` 创建信号等待器。
等待器首次使用时才会安装处理器。
可通过 {name}`Signal.Waiter.wait` 使用等待器，以便用 {name}`await` 等待信号；不过，多数场景可能更适合将 {name}`Signal.Waiter.selector` 与{ref "async-select"}[事件选择]组合，通过取消正在进行的工作并清理来响应信号。
这一模式及 {name}`Signal.Waiter` 的 API 与定时器类似；不同的是，信号到来的时间不可预测。

{name}`Signal.Waiter.mk` 的 `repeating` 参数决定等待单次信号还是重复信号。
若为 {name}`false`，一旦匹配信号到来，等待器就进入完成状态。
此后再次选择或调用 {name Signal.Waiter.wait}`wait`，都会立即返回相同数据。
若 `repeating` 为 {name}`true`，后续调用 {name Signal.Waiter.wait}`wait` 或再次选择时，会阻塞直到下一个信号到来。
重复等待器会持续监听信号，直到调用 {name}`Signal.Waiter.stop`。

{zhdocstringFrom Signal.Waiter +allowMissing}

{zhdocstringFrom Signal.Waiter.mk}

{zhdocstringFrom Signal.Waiter.wait}

{zhdocstringFrom Signal.Waiter.stop}

{zhdocstringFrom Signal.Waiter.selector}

::::example "选择器与信号"
此程序运行一个循环。
每轮迭代等待一行输入或会发送 `SIGINT` 的 `Ctrl-C`。
若收到输入，就回显该行并继续循环。
若收到 `SIGINT`，则停止迭代并终止程序。
通过 {name}`Selectable.one` 让信号处理器与传递输入行的通道竞争，以检查信号。
该通道可以参与选择，并由读取 `stdin` 的专用线程向其提供数据。

:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (CloseableChannel)

-- Blocking reader on a dedicated thread: forward each line, close on EOF.
partial def reader (stdin : IO.FS.Stream) (ch : CloseableChannel String) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    discard <| (ch.close).toBaseIO
  else
    discard <| ch.send line
    reader stdin ch

-- Echo each line; stop on EOF (channel closed) or SIGINT (Ctrl-C).
partial def echo (sigint : Signal.Waiter) (ch : CloseableChannel String) : Async Unit := do
  let more ← Selectable.one #[
    .case ch.recvSelector fun
      | some line => do IO.print (s!"got: {line}"); return true
      | none => do IO.println "done"; return false,
    .case sigint.selector fun _ => do
      IO.println "interrupted"
      return false
  ]
  if more then echo sigint ch

public def main : IO Unit := do
  let ch ← CloseableChannel.new (α := String)
  let sigint ← Signal.Waiter.mk .sigint (repeating := true)
  discard <| IO.asTask (prio := .dedicated) (reader (← IO.getStdin) ch)
  (echo sigint ch).block
```
```stdout -show
done
```
:::
::::

# 取消
%%%
file := "Cancellation"
tag := "Lean-__________________--IO--Asynchronous-Programming--Cancellation"
%%%

典型的异步应用需要处理_取消_，即放弃正在进行的工作。
例如，用户按下 `Ctrl-C` 或发生超时时，可以放弃下载并清理临时文件，而无需终止整个应用。
{name}`ContextAsync` 单子提供管理任务层次树的工具，取消一个任务时也会取消它的子任务。

取消是_协作式的_：任务必须显式检查自己是否已被取消，并自行终止。
换言之，取消是任务可以自行选择观察的事件，而非强制终止其他任务的机制。

:::paragraph
取消一棵 {name}`ContextAsync` 计算树主要有两种方式：

 * {name}`ContextAsync.run` 将可取消的任务树作为普通 {name}`Async` 任务执行。
   根任务正常返回时，会取消整棵树。
 * {name}`ContextAsync.cancel` 取消当前任务及其全部子任务。

为使取消按预期工作，应使用专为 {name}`ContextAsync` 设计的辅助函数启动并发任务。
无法这样做时，使用 {name}`ContextAsync.runIn` 将当前取消上下文与新计算关联。
:::

{zhdocstringFrom ContextAsync}

{zhdocstringFrom ContextAsync.async}

{zhdocstringFrom ContextAsync.cancel}

{zhdocstringFrom ContextAsync.run}

{zhdocstringFrom ContextAsync.runIn}

{zhdocstringFrom ContextAsync.getContext}

{zhdocstringFrom ContextAsync.background}

{zhdocstringFrom ContextAsync.disown}

{zhdocstringFrom ContextAsync.concurrently}

{zhdocstringFrom ContextAsync.concurrentlyAll}

{zhdocstringFrom ContextAsync.race}

{zhdocstringFrom ContextAsync.raceAll}

## 响应取消
%%%
file := "Reacting-to-Cancellation"
tag := "Lean-__________________--IO--Asynchronous-Programming--Cancellation--Reacting-to-Cancellation"
%%%

异步计算可以通过 {name}`ContextAsync.isCancelled` 显式轮询来响应取消。
也可以使用 {name}`ContextAsync.awaitCancellation` 阻塞，直到当前上下文被取消；这适用于取消前已无其他工作的情况，同时仍允许进行清理。
最后，还可以借助 {name}`Selector.cancelled` 或 {name}`ContextAsync.doneSelector`（二者同义），通过{tech (key := "event selection")}[事件选择]同时等待取消与其他事件。

{zhdocstringFrom ContextAsync.isCancelled}

:::example "观察取消"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
{name}`ContextAsync.isCancelled` 报告当前上下文是否已被取消。
这里使用 {name}`ContextAsync.cancel` 显式取消上下文：
```lean (name := flagOut)
#eval Async.block <| ContextAsync.run do
  let before ← ContextAsync.isCancelled
  ContextAsync.cancel .cancel
  let after ← ContextAsync.isCancelled
  return (before, after)
```
```leanOutput flagOut
(false, true)
```
:::

:::example "协作响应取消"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
由于取消是协作式的，长期运行的计算必须自行检查 {name}`ContextAsync.isCancelled`，并在被取消后停止。
此工作任务会不断记录数字，直到其上下文被取消。
这里的取消由工作任务自身在迭代三次后触发；实际应用中可能来自超时或父任务，但工作任务的响应方式相同：
```lean (name := workerOut)
def worker : ContextAsync (Array Nat) := do
  let log ← IO.mkRef (#[] : Array Nat)
  for i in [0:100] do
    if ← ContextAsync.isCancelled then break
    log.modify (·.push i)
    if i == 2 then ContextAsync.cancel .cancel
  log.get

#eval Async.block <| ContextAsync.run worker
```
```leanOutput workerOut
#[0, 1, 2]
```
:::

{zhdocstringFrom ContextAsync.awaitCancellation}

{zhdocstringFrom Selector.cancelled}

:::example "中断等待"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std.Async
open Std (CloseableChannel)
```
取消可以通过{tech (key := "event selection")}[事件选择]与其他事件一起等待。
这里的计算等待通道中的值或取消，以先发生者为准。
由于选择运行前上下文就已被取消，因此取消分支获胜，结果为 {name}`none`：
```lean (name := cancelSelOut)
def waitOrCancel (ch : CloseableChannel Nat) : ContextAsync (Option Nat) := do
  Selectable.one #[
    .case ch.recvSelector (fun n? => return n?),
    .case (← Selector.cancelled) (fun _ => return none)
  ]

#eval Async.block <| ContextAsync.run do
  let ch ← CloseableChannel.new (α := Nat)
  ContextAsync.cancel .cancel
  waitOrCancel ch
```
```leanOutput cancelSelOut
none
```
:::

{zhdocstringFrom ContextAsync.doneSelector}

{zhdocstringFrom ContextAsync.getCancellationReason}

## 取消上下文
%%%
file := "Cancellation-Contexts"
tag := "Lean-__________________--IO--Asynchronous-Programming--Cancellation--Cancellation-Contexts"
%%%

{name}`ContextAsync` 是构建于 {name}`Async` 之上的{ref "reader-monad"}[读取器]，提供对取消上下文的访问。
该上下文包含一个 ID、一个取消令牌，以及一份由互斥锁保护的可变状态；该状态编码一棵 ID 树，其中每个 ID 都有自己的取消令牌，同时保存唯一 ID 值的来源。
创建子任务时，会为其分配新 ID，并将其与当前任务关联。
取消任务时，会利用状态中的树来取消它的子任务。

{zhdocstringFrom Std.CancellationContext +allowMissing}

{zhdocstringFrom Std.CancellationContext.State +allowMissing}

{zhdocstringFrom Std.CancellationContext.new}

{zhdocstringFrom Std.CancellationContext.fork}

{zhdocstringFrom Std.CancellationContext.cancel}

{zhdocstringFrom Std.CancellationContext.isCancelled}

{zhdocstringFrom Std.CancellationContext.getCancellationReason}

{zhdocstringFrom Std.CancellationContext.done}

{zhdocstringFrom Std.CancellationContext.doneSelector}

{zhdocstringFrom Std.CancellationReason}

## 取消令牌
%%%
file := "Cancellation-Tokens"
tag := "Lean-__________________--IO--Asynchronous-Programming--Cancellation--Cancellation-Tokens"
%%%

取消令牌是一份由互斥锁保护的共享可变状态，跟踪令牌是否已被取消，并保存一组请求在取消发生时获得通知的使用方。
在底层，{name}`ContextAsync.isCancelled` 会检查当前上下文的取消令牌，再检查取消原因为 {name}`some` 还是 {name}`none`。

{zhdocstringFrom Std.CancellationToken +allowMissing}

{zhdocstringFrom Std.CancellationToken.State}

{zhdocstringFrom Std.CancellationToken.Consumer +allowMissing}
