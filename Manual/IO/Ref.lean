/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command
import Manual.ZhDocString.IO

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "可变引用" =>
%%%
tag := "Lean-__________________--IO--Mutable-References"
file := "Mutable-References"
%%%


普通的{tech (key := "state monads")}[状态单子]使用元组编码有状态计算，元组同时跟踪状态内容与计算结果；Lean 运行时系统还提供始终由可变内存单元支撑的可变引用。
可变引用的类型为 {lean}`IO.Ref`，它表明单元是可变的；读取和写入都必须显式进行。
{lean}`IO.Ref` 使用 {lean}`ST.Ref` 实现，因此完整的 {ref "mutable-st-references"}[{lean}`ST.Ref` API] 也可用于 {lean}`IO.Ref`。

{zhdocstring IO.Ref Manual.ZhDocString.IO.c145}

{zhdocstring IO.mkRef Manual.ZhDocString.IO.c146}



# 状态变换器
%%%
tag := "mutable-st-references"
%%%


在不希望出现任意副作用的场合，可变引用往往很有用。
当 Lean 无法把纯操作优化为原地修改时，可变引用能显著提速；有些算法用可变引用也比用状态单子更容易表达。
此外，它还具有其他副作用所不具备的性质：若一段代码使用的所有可变引用都在执行期间创建，且没有可变引用从该代码逃逸到其他代码，那么求值结果就是确定的。

{lean}`ST` 单子是 {lean}`IO` 的受限版本，其中可变状态是唯一的副作用，且可变引用不能逃逸。{margin}[{lean}`ST` 最早由 {citehere launchbury94}[] 描述。]
{lean}`ST` 接受一个从不用于归类任何项的类型参数。
{lean}`runST` 可执行 {lean}`ST` 动作并将其纯结果带出；它要求传入的动作能把该类型参数实例化为_任意_类型。
这个未知类型只作为函数参数存在，因此类型被它“标记”的值无法逃出其作用域。

{zhdocstring ST Manual.ZhDocString.IO.c147}

{zhdocstring runST Manual.ZhDocString.IO.c148}

与 {lean}`IO` 和 {lean}`EIO` 类似，{lean}`ST` 也有一个把自定义错误类型作为参数的变体。
这里，{lean}`ST` 对应的是 {lean}`BaseIO` 而非 {lean}`IO`，因为 {lean}`ST` 不会导致错误被抛出。

{zhdocstring EST Manual.ZhDocString.IO.c149}

{zhdocstring runEST Manual.ZhDocString.IO.c150}

{zhdocstring ST.Ref Manual.ZhDocString.IO.c151 +hideFields}

{zhdocstring ST.mkRef Manual.ZhDocString.IO.c152}

## 读取与写入
%%%
tag := "Lean-__________________--IO--Mutable-References--State-Transformers--Reading-and-Writing"
%%%

{zhdocstring ST.Ref.get Manual.ZhDocString.IO.c153}

{zhdocstring ST.Ref.set Manual.ZhDocString.IO.c154}

::::example "{name ST.Ref.get}`get` 与 {name ST.Ref.set}`set` 引发的数据竞争" (file := "Data races with get and set")
:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      if cost < (← balance.get) then
        IO.sleep (← IO.rand 10 100).toUInt32
        balance.set ((← balance.get) - cost)
    orders := orders.push o

  -- 等待所有订单完成
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance is negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
```
```stderr
Final balance is negative!
```
:::
::::

{zhdocstring ST.Ref.modify Manual.ZhDocString.IO.c155}

::::example "使用 {name ST.Ref.modify}`modify` 避免数据竞争" (file := "Avoiding data races with modify")

该程序启动 100 个线程。
每个线程模拟一次购买尝试：生成一个随机价格；若账户余额充足，就从余额中扣除该价格。
余额检查与新值计算在一次对 {name}`ST.Ref.modify` 的原子调用中完成。

:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      balance.modify fun b =>
        if cost < b then
          b - cost
        else b
    orders := orders.push o

  -- 等待所有订单完成
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
Final balance is zero or positive.
```
```stderr
```
:::
::::

{zhdocstring ST.Ref.modifyGet Manual.ZhDocString.IO.c156}

{zhdocstring ST.Ref.swap Manual.ZhDocString.IO.c157}

## 比较
%%%
tag := "Lean-__________________--IO--Mutable-References--State-Transformers--Comparisons"
%%%

{zhdocstring ST.Ref.ptrEq Manual.ZhDocString.IO.c158}

## 由 `ST` 支撑的状态单子
%%%
tag := "Lean-__________________--IO--Mutable-References--State-Transformers--ST--Backed-State-Monads"
%%%

{zhdocstring ST.Ref.toMonadStateOf Manual.ZhDocString.IO.c159}

# 并发
%%%
tag := "ref-locks"
%%%

可变引用可以用作锁机制。
_取走_引用内容后，再次尝试取走或读取它的操作都会阻塞，直至通过 {name ST.Ref.set}`set` 重新设置其内容。
这是一项可用于实现其他同步机制的底层功能；只要可能，通常应优先采用更高层的抽象。

{zhdocstring ST.Ref.take Manual.ZhDocString.IO.c160}


::::example "用引用单元充当锁" (file := "Reference Cells as Locks")
该程序启动 100 个线程。
每个线程模拟一次购买尝试：生成一个随机价格；若账户余额充足，就从余额中扣除该价格。
若余额不足，则不作扣减。
由于每个线程在检查前都会用 {name ST.Ref.take}`take` 取走余额单元，并在完成后才将其放回，因此该单元起到了锁的作用。
与使用纯函数原子修改单元内容的 {name}`ST.Ref.modify` 不同，临界区中还可以发生其他 {name}`IO` 动作。
该程序的 `main` 函数被标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe`，因为 {name ST.Ref.take}`take` 本身并不安全。

:::ioExample
```ioLean
unsafe def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)
  let validationUsed ← IO.mkRef false

  let mut orders := #[]

  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      let b ← balance.take
      if cost ≤ b then
        balance.set (b - cost)
      else
        balance.set b
        validationUsed.set true
    orders := orders.push o

  -- 等待所有订单完成
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← validationUsed.get) then
    IO.println "Validation prevented a negative balance."

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```

程序输出为：
```stdout
Sending out orders...
Validation prevented a negative balance.
Final balance is zero or positive.
```
:::
::::
