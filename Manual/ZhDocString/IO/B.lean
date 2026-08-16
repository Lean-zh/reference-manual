/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Std.Data.Iterators
import Std.Data.TreeMap
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.IO

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w u₁ u₂ w₁ w₂

/-!
本模块为参考手册动态 API 文档提供中文载体。每个载体都直接转发到对应的真实声明，
因此不会重新实现运行时行为。结构体、类型类与归纳类型在后续形状审计中按真实声明镜像。
-/

/-- 文件所有者、用户组和其他用户的权限。 -/
structure c112 where
  /-- 所有者权限。 -/
  user : _root_.IO.AccessRight := {}
  /-- 用户组权限。 -/
  group : _root_.IO.AccessRight := {}
  /-- 其他用户权限。 -/
  other : _root_.IO.AccessRight := {}

/-- `IO.FileRight.flags` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c113 := @_root_.IO.FileRight.flags

/-- `IO.setAccessRights` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c114 := @_root_.IO.setAccessRights

/-- `IO.FS.removeFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c115 := @_root_.IO.FS.removeFile

/-- `IO.FS.rename` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c116 := @_root_.IO.FS.rename

/-- `IO.FS.removeDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c117 := @_root_.IO.FS.removeDir

/-- `IO.FS.lines` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c118 := @_root_.IO.FS.lines

/-- `IO.FS.withTempFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c119 := @_root_.IO.FS.withTempFile

/-- `IO.FS.withTempDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c120 := @_root_.IO.FS.withTempDir

/-- `IO.FS.createDirAll` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c121 := @_root_.IO.FS.createDirAll

/-- `IO.FS.writeBinFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c122 := @_root_.IO.FS.writeBinFile

/-- `IO.FS.withFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c123 := @_root_.IO.FS.withFile

/-- `IO.FS.removeDirAll` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c124 := @_root_.IO.FS.removeDirAll

/-- `IO.FS.createTempFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c125 := @_root_.IO.FS.createTempFile

/-- `IO.FS.createTempDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c126 := @_root_.IO.FS.createTempDir

/-- `IO.FS.readFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c127 := @_root_.IO.FS.readFile

/-- `IO.FS.realPath` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c128 := @_root_.IO.FS.realPath

/-- `IO.FS.writeFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c129 := @_root_.IO.FS.writeFile

/-- `IO.FS.readBinFile` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c130 := @_root_.IO.FS.readBinFile

/-- `IO.FS.createDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c131 := @_root_.IO.FS.createDir

/-- `IO.getStdin` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c132 := @_root_.IO.getStdin

/-- `IO.setStdin` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c133 := @_root_.IO.setStdin

/-- `IO.withStdin` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c134 := @_root_.IO.withStdin

/-- `IO.getStdout` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c135 := @_root_.IO.getStdout

/-- `IO.setStdout` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c136 := @_root_.IO.setStdout

/-- `IO.withStdout` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c137 := @_root_.IO.withStdout

/-- `IO.getStderr` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c138 := @_root_.IO.getStderr

/-- `IO.setStderr` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c139 := @_root_.IO.setStderr

/-- `IO.withStderr` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c140 := @_root_.IO.withStderr

/-- `IO.FS.withIsolatedStreams` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c141 := @_root_.IO.FS.withIsolatedStreams

/-- `IO.currentDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c142 := @_root_.IO.currentDir

/-- `IO.appPath` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c143 := @_root_.IO.appPath

/-- `IO.appDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c144 := @_root_.IO.appDir

/-- `IO.Ref` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c145 := @_root_.IO.Ref

/-- `IO.mkRef` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c146 := @_root_.IO.mkRef

/-- `ST` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c147 := @_root_.ST

/-- `runST` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c148 := @_root_.runST

/-- `EST` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c149 := @_root_.EST

/-- `runEST` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c150 := @_root_.runEST

/-- 状态线程中的可变引用，携带底层引用与元素类型非空的证据。 -/
structure c151 (σ α : Type) where
  /-- 底层引用。 -/
  ref : _root_.ST.RefPointed.type
  /-- 元素类型非空的证据。 -/
  h : Nonempty α

/-- `ST.mkRef` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c152 := @_root_.ST.mkRef

/-- `ST.Ref.get` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c153 := @_root_.ST.Ref.get

/-- `ST.Ref.set` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c154 := @_root_.ST.Ref.set

/-- `ST.Ref.modify` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c155 := @_root_.ST.Ref.modify

/-- `ST.Ref.modifyGet` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c156 := @_root_.ST.Ref.modifyGet

/-- `ST.Ref.swap` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c157 := @_root_.ST.Ref.swap

/-- `ST.Ref.ptrEq` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c158 := @_root_.ST.Ref.ptrEq

/-- `ST.Ref.toMonadStateOf` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c159 := @_root_.ST.Ref.toMonadStateOf

/-- `ST.Ref.take` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
unsafe def c160 := @_root_.ST.Ref.take

/-- 可异步计算并最终取得 `α` 值的任务。 -/
structure c161 (α : Type u) where
  pure ::
  /-- 取得任务结果。 -/
  get : α

/-- `Task.spawn` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c162 := @_root_.Task.spawn

/-- `Task.pure` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c163 := @_root_.Task.pure

/-- `BaseIO.asTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c164 := @_root_.BaseIO.asTask

/-- `EIO.asTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c165 := @_root_.EIO.asTask

/-- `IO.asTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c166 := @_root_.IO.asTask

/-- `Task.Priority` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c167 := @_root_.Task.Priority

/-- `Task.Priority.default` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c168 := @_root_.Task.Priority.default

/-- `Task.Priority.max` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c169 := @_root_.Task.Priority.max

/-- `Task.Priority.dedicated` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c170 := @_root_.Task.Priority.dedicated

/-- `Task.get` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c171 := @_root_.Task.get

/-- `IO.wait` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c172 := @_root_.IO.wait

/-- `IO.waitAny` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c173 := @_root_.IO.waitAny

/-- `Task.map` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c174 := @_root_.Task.map

/-- `Task.bind` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c175 := @_root_.Task.bind

/-- `Task.mapList` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c176 := @_root_.Task.mapList

/-- `BaseIO.mapTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c177 := @_root_.BaseIO.mapTask

/-- `EIO.mapTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c178 := @_root_.EIO.mapTask

/-- `IO.mapTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c179 := @_root_.IO.mapTask

/-- `BaseIO.mapTasks` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c180 := @_root_.BaseIO.mapTasks

/-- `EIO.mapTasks` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c181 := @_root_.EIO.mapTasks

/-- `IO.mapTasks` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c182 := @_root_.IO.mapTasks

/-- `BaseIO.bindTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c183 := @_root_.BaseIO.bindTask

/-- `EIO.bindTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c184 := @_root_.EIO.bindTask

/-- `IO.bindTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c185 := @_root_.IO.bindTask

/-- `BaseIO.chainTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c186 := @_root_.BaseIO.chainTask

/-- `EIO.chainTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c187 := @_root_.EIO.chainTask

/-- `IO.chainTask` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c188 := @_root_.IO.chainTask

/-- `IO.cancel` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c189 := @_root_.IO.cancel

/-- `IO.checkCanceled` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c190 := @_root_.IO.checkCanceled

/-- `IO.hasFinished` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c191 := @_root_.IO.hasFinished

/-- `IO.getTaskState` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c192 := @_root_.IO.getTaskState

/-- 异步任务当前所处的状态。 -/
inductive c193 where
  /-- 等待调度。 -/
  | waiting
  /-- 正在运行。 -/
  | running
  /-- 已完成。 -/
  | finished

/-- `IO.getTID` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c194 := @_root_.IO.getTID

/-- 可由生产者解析一次、供消费者等待结果的承诺。 -/
structure c195 (α : Type) where
  private mk ::
  /-- 对应的真实承诺对象。 -/
  private prom : _root_.IO.Promise α
  /-- 结果类型非空的证据。 -/
  private h : Nonempty α

/-- `IO.Promise.new` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c196 := @_root_.IO.Promise.new

/-- `IO.Promise.isResolved` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c197 := @_root_.IO.Promise.isResolved

/-- `IO.Promise.result?` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c198 := @_root_.IO.Promise.result?

/-- `IO.Promise.result!` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c199 := @_root_.IO.Promise.result!

/-- `IO.Promise.resultD` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c200 := @_root_.IO.Promise.resultD

/-- `IO.Promise.resolve` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c201 := @_root_.IO.Promise.resolve

/-- 用于在线程之间传递值的通道。 -/
structure c202 (α : Type) where
  private mk ::
  /-- 提供实现的可关闭通道。 -/
  private inner : _root_.Std.CloseableChannel α

/-- `Std.Channel.new` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c203 := @_root_.Std.Channel.new

/-- `Std.Channel.send` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c204 := @_root_.Std.Channel.send

/-- `Std.Channel.recv` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c205 := @_root_.Std.Channel.recv

/-- `Std.Channel.forAsync` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c206 := @_root_.Std.Channel.forAsync

/-- `Std.Channel.sync` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c207 := @_root_.Std.Channel.sync

/-- `Std.Channel.Sync` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c208 := @_root_.Std.Channel.Sync

/-- `Std.CloseableChannel` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c209 := @_root_.Std.CloseableChannel

/-- `Std.CloseableChannel.new` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c210 := @_root_.Std.CloseableChannel.new

/-- 以互斥锁保护一个值。 -/
structure c211 (α : Type) where
  private mk ::
  /-- 受保护值的引用。 -/
  private ref : _root_.IO.Ref α
  /-- 底层互斥锁。 -/
  mutex : _root_.Std.BaseMutex

/-- `Std.Mutex.new` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c212 := @_root_.Std.Mutex.new

/-- `Std.Mutex.atomically` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c213 := @_root_.Std.Mutex.atomically

/-- `Std.Mutex.atomicallyOnce` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c214 := @_root_.Std.Mutex.atomicallyOnce

/-- `Std.AtomicT` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c215 := @_root_.Std.AtomicT

/-- `Std.Condvar` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c216 := @_root_.Std.Condvar

/-- `Std.Condvar.new` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c217 := @_root_.Std.Condvar.new

/-- `Std.Condvar.wait` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c218 := @_root_.Std.Condvar.wait

/-- `Std.Condvar.notifyOne` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c219 := @_root_.Std.Condvar.notifyOne

/-- `Std.Condvar.notifyAll` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c220 := @_root_.Std.Condvar.notifyAll

/-- `Std.Condvar.waitUntil` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c221 := @_root_.Std.Condvar.waitUntil


end Manual.ZhDocString.IO
