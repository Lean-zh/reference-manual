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

/--
POSIX 风格的文件权限，描述文件所有者、文件所属组的成员以及其他所有人的访问权。
-/
structure c112 where
  /-- 文件所有者的文件访问权限。 -/
  user : _root_.IO.AccessRight := {}
  /-- 文件所属组的文件访问权限。 -/
  group : _root_.IO.AccessRight := {}
  /-- 其他所有人的文件访问权限。 -/
  other : _root_.IO.AccessRight := {}

/--
将 POSIX 风格的文件权限转换为数值表示；所有者权限、用户组权限和其他用户权限各占三位。
-/
def c113 := @_root_.IO.FileRight.flags

/--
设置文件的 POSIX 风格权限。
-/
def c114 := @_root_.IO.setAccessRights

/--
从文件系统中移除（删除）一个文件。

要移除目录，请改用 `IO.FS.removeDir` 或 `IO.FS.removeDirAll`。
-/
def c115 := @_root_.IO.FS.removeFile

/--
将文件或目录 `old` 移动到新位置 `new`。

此函数与 [POSIX 的 `rename` 函数](https://pubs.opengroup.org/onlinepubs/9699919799/functions/rename.html)一致。
-/
def c116 := @_root_.IO.FS.rename

/--
移除（删除）一个目录。

如果目录非空，移除操作会失败。要连同目录内容一起移除，请使用 `IO.FS.removeDirAll`。
-/
def c117 := @_root_.IO.FS.removeDir

/--
以行数组的形式返回 UTF-8 编码文本文件的内容。

返回的各行不包含换行标记。
-/
def c118 := @_root_.IO.FS.lines

/--
以尽可能安全的方式创建临时文件，并将已打开文件的 `Handle` 及其路径一并传给 `f`。调用结束后会删除该临时文件。

文件的创建过程不存在竞态条件。只有创建该文件的用户 ID 能读写它；此外，在 UNIX 风格的平台上，任何人都不能执行该文件。

若不希望自动删除临时文件，请使用 `IO.FS.createTempFile`。
-/
def c119 := @_root_.IO.FS.withTempFile

/--
以尽可能安全的方式创建临时目录，并将其路径提供给一个 `IO` 操作。调用结束后，无论目录中的文件以何种方式或在何时创建，都会递归删除所有文件。

目录的创建过程不存在竞态条件。只有创建该目录的用户 ID 能读写它。若不希望自动删除目录内容，请使用 `IO.FS.createTempDir`。
-/
def c120 := @_root_.IO.FS.withTempDir

/--
在指定路径创建目录，并把所有缺失的父路径一并创建为目录。
-/
def c121 := @_root_.IO.FS.createDirAll

/--
将所提供的字节写入指定路径的二进制文件。
-/
def c122 := @_root_.IO.FS.writeBinFile

/--
以指定的 `mode` 打开文件 `fn`，并将得到的文件句柄传给 `f`。

文件句柄的最后一个引用被丢弃时，句柄才会关闭。如果有引用逃逸出 `f`，那么即使 `IO.FS.withFile` 已执行完毕，文件也仍保持打开。
-/
def c123 := @_root_.IO.FS.withFile

/--
以未指定的顺序删除给定目录中包含的所有文件与目录，从而彻底移除该目录。符号链接会被删除，但不会被跟随。如果任何所含条目无法删除，或在执行期间又有条目新建，则操作失败。
-/
def c124 := @_root_.IO.FS.removeDirAll

/--
以尽可能安全的方式创建临时文件，并返回已打开文件的 `Handle` 及其路径。

文件的创建过程不存在竞态条件。只有创建该文件的用户 ID 能读写它；此外，在 UNIX 风格的平台上，任何人都不能执行该文件。

调用方负责在使用后移除该文件。要确保临时文件被移除，请使用 `withTempFile`。
-/
def c125 := @_root_.IO.FS.createTempFile

/--
以尽可能安全的方式创建临时目录，并返回新目录的路径。目录的创建过程不存在竞态条件。只有创建该目录的用户 ID 能读写它。

调用方负责在使用后移除该目录。要确保临时目录被移除，请使用 `withTempDir`。
-/
def c126 := @_root_.IO.FS.createTempDir

/--
将给定路径下 UTF-8 编码文件的全部内容读取为 `String`。

如果文件内容不是有效的 UTF-8，则抛出异常；除此之外，读取文件失败时本来就可能抛出异常。
-/
def c127 := @_root_.IO.FS.readFile

/--
将路径解析为不含“.”、“..”或符号链接的绝对路径。

此函数与 [POSIX 的 `realpath` 函数](https://pubs.opengroup.org/onlinepubs/9699919799/functions/realpath.html)一致。
-/
def c128 := @_root_.IO.FS.realPath

/--
使用 UTF-8 编码将字符串内容写入指定路径的文件。
-/
def c129 := @_root_.IO.FS.writeFile

/--
将给定路径下二进制文件的全部内容读取为字节数组。
-/
def c130 := @_root_.IO.FS.readBinFile

/--
在指定路径创建目录。父目录必须已经存在。

如果无法创建目录，则抛出异常。
-/
def c131 := @_root_.IO.FS.createDir

/--
返回当前线程的标准输入流。

使用 `IO.setStdin` 可替换当前线程的标准输入流。
-/
def c132 := @_root_.IO.getStdin

/--
替换当前线程的标准输入流，并返回原来的流。

使用 `IO.getStdin` 可获取当前的标准输入流。
-/
def c133 := @_root_.IO.setStdin

/--
以指定的流 `h` 作为标准输入运行一个操作，随后恢复原来的标准输入流。
-/
def c134 := @_root_.IO.withStdin

/--
返回当前线程的标准输出流。

使用 `IO.setStdout` 可替换当前线程的标准输出流。
-/
def c135 := @_root_.IO.getStdout

/--
替换当前线程的标准输出流，并返回原来的流。

使用 `IO.getStdout` 可获取当前的标准输出流。
-/
def c136 := @_root_.IO.setStdout

/--
以指定的流 `h` 作为标准输出运行一个操作，随后恢复原来的标准输出流。
-/
def c137 := @_root_.IO.withStdout

/--
返回当前线程的标准错误流。

使用 `IO.setStderr` 可替换当前线程的标准错误流。
-/
def c138 := @_root_.IO.getStderr

/--
替换当前线程的标准错误流，并返回原来的流。

使用 `IO.getStderr` 可获取当前的标准错误流。
-/
def c139 := @_root_.IO.setStderr

/--
以指定的流 `h` 作为标准错误运行一个操作，随后恢复原来的标准错误流。
-/
def c140 := @_root_.IO.withStderr

/--
运行一个操作，其中 `stdin` 为空，并将 `stdout` 和 `stderr` 捕获到一个 `String` 中。如果 `isolateStderr` 为 `false`，则只捕获 `stdout`。
-/
def c141 := @_root_.IO.FS.withIsolatedStreams

/--
返回正在执行的进程的当前工作目录。
-/
def c142 := @_root_.IO.currentDir

/--
返回当前正在运行的可执行文件的文件名。
-/
def c143 := @_root_.IO.appPath

/--
返回当前可执行文件所在的目录。
-/
def c144 := @_root_.IO.appDir

/--
保存 `α` 类型值的可变引用单元。可以在 `IO` 单子中读取和修改这些单元。
-/
def c145 := @_root_.IO.Ref

/--
创建一个包含 `a` 的新可变引用单元。
-/
def c146 := @_root_.IO.mkRef

/--
`IO` 的受限版本，其中可变状态是唯一的副作用。

可以使用 `runST` 在非单子上下文中运行 `ST` 计算。
-/
def c147 := @_root_.ST

/--
运行一个 `ST` 计算；该计算唯一的副作用是通过 `ST.Ref` 操作可变状态。
-/
def c148 := @_root_.runST

/--
`IO` 的受限版本，其中可变状态和异常是仅有的副作用。

可以使用 `runEST` 在非单子上下文中运行 `EST` 计算。
-/
def c149 := @_root_.EST

/--
运行一个 `EST` 计算；该计算仅有的副作用是可变状态和异常。
-/
def c150 := @_root_.runEST

/--
保存 `α` 类型值的可变引用单元。可以在 `ST σ` 单子中读取和修改这些单元。
-/
structure c151 (σ α : Type) where
  /-- 保存可变值的底层运行时引用点。真实声明没有此字段的文档。 -/
  ref : _root_.ST.RefPointed.type
  /-- `α` 非空的证据，使运行时引用点能够安全地解释为 `α` 类型的引用。真实声明没有此字段的文档。 -/
  h : Nonempty α

/--
创建一个包含给定值 `a` 的新可变引用。
-/
def c152 := @_root_.ST.mkRef

/--
读取可变引用中的值。
-/
def c153 := @_root_.ST.Ref.get

/--
替换可变引用中的值。
-/
def c154 := @_root_.ST.Ref.set

/--
原子地修改可变引用单元：用一次函数调用的结果替换其中的内容。
-/
def c155 := @_root_.ST.Ref.modify

/--
原子地修改可变引用单元：用一次函数调用的结果替换其中的内容，同时计算一个要返回的值。
-/
def c156 := @_root_.ST.Ref.modifyGet

/--
原子地将可变引用单元中的值与另一个值交换，并返回该引用单元原来的值。
-/
def c157 := @_root_.ST.Ref.swap

/--
检查两个引用单元实际上是否为同一单元的别名。

即使包含相同的值，由不同次执行 `IO.mkRef` 或 `ST.mkRef` 分配的两个引用也是不同的；修改其中一个不会影响另一个。反之，同一个引用单元可以有多个别名，修改任一别名也会修改其他别名所指的同一单元。
-/
def c158 := @_root_.ST.Ref.ptrEq

/--
从引用单元创建一个 `MonadStateOf` 实例。

这样，针对[状态单子](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=state-monads) API 编写的程序便可使用可变引用单元来跟踪状态并执行。
-/
def c159 := @_root_.ST.Ref.toMonadStateOf

/--
读取并取走可变引用单元中的值。

此后若尝试读取或再次取走该引用单元，将阻塞到使用 `ST.Ref.set` 写入新值为止。
-/
unsafe def c160 := @_root_.ST.Ref.take

/--
`Task α` 是异步计算的原语。
它表示一个最终会解析为 `α` 类型值的计算，该计算可能在另一线程上进行。这类似于 Scala 中的 `Future`、Javascript 中的 `Promise` 和 Rust 中的 `JoinHandle`。

任务在运行时中使用覆写的表示。
-/
structure c161 (α : Type u) where
  /-- `Task.pure (a : α)` 构造一个已经解析为值 `a` 的任务。 -/
  pure ::
  /--
阻塞当前线程，直到给定任务执行完毕，然后返回任务结果。如果当前线程自身正在执行一个（非专用）任务，则等待期间会临时将线程池的最大大小增加一，以确保进程不会因线程池资源耗尽而死锁。请注意，当前线程解除阻塞时，可能会暂时有超过所配置线程池大小的任务同时运行，直到足够多的任务执行完毕。

在可行的情况下，应优先使用 `Task.map` 和 `Task.bind` 来建立任务依赖，而不是使用 `Task.get`，因为它们不需要以这种方式临时扩展线程池。尤其是，在任务续体中以 `(sync := true)` 调用 `Task.get` 会引发恐慌，因为此时续体显然并不“廉价”，否则还可能发生死锁。应改为返回所等待的任务，并使用 `Task.bind/IO.bindTask` 将其解包。
  -/
  get : α

/--
`spawn fn : Task α` 构造并立即启动一个新任务，以异步求值函数 `fn () : α`。

如果提供了 `prio`，它就是该任务的优先级。
-/
def c162 := @_root_.Task.spawn

/--
`Task.pure (a : α)` 构造一个已经解析为值 `a` 的任务。
-/
def c163 := @_root_.Task.pure

/--
以优先级 `prio` 在单独的 `Task` 中运行 `act`。

运行所得的 `BaseIO` 操作会立即启动任务。对 `Task` 的纯访问不会影响非纯操作 `act`。

与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c164 := @_root_.BaseIO.asTask

/--
以优先级 `prio` 在单独的 `Task` 中运行 `act`。由于 `EIO ε` 操作可能抛出 `ε` 类型的异常，任务结果是 `Except ε α`。

运行所得的 `IO` 操作会立即启动任务。对 `Task` 的纯访问不会影响非纯操作 `act`。

与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c165 := @_root_.EIO.asTask

/--
以优先级 `prio` 在单独的 `Task` 中运行 `act`。由于 `IO` 操作可能抛出 `IO.Error` 类型的异常，任务结果是 `Except IO.Error α`。

运行所得的 `BaseIO` 操作会立即启动任务。对 `Task` 的纯访问不会影响非纯操作 `act`。由于 `IO` 操作可能抛出 `IO.Error` 类型的异常，任务结果是 `Except IO.Error α`。

与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c166 := @_root_.IO.asTask

/--
任务优先级。

优先级较高的任务总是在优先级较低的任务之前调度。优先级高于 `Task.Priority.max` 的任务会在专用线程上调度。
-/
def c167 := @_root_.Task.Priority

/--
所生成任务的默认优先级，也是最低优先级：`0`。
-/
def c168 := @_root_.Task.Priority.default

/--
所生成任务的最高常规优先级：`8`。

以高于 `Task.Priority.max` 的优先级生成任务并非错误，但会为该任务生成专用工作线程。这由 `Task.Priority.dedicated` 表示。常规优先级任务会放入线程池，并按优先级顺序处理。
-/
def c169 := @_root_.Task.Priority.max

/--
表示任务应在专用线程上调度。

任何高于 `Task.Priority.max` 的优先级都会使任务立即在专用线程上调度。这对长时间运行和/或受 I/O 限制的任务尤其有用，因为为减少上下文切换，Lean 默认分配的非专用工作线程不会超过核心数。
-/
def c170 := @_root_.Task.Priority.dedicated

/--
阻塞当前线程，直到给定任务执行完毕，然后返回任务结果。如果当前线程自身正在执行一个（非专用）任务，则等待期间会临时将线程池的最大大小增加一，以确保进程不会因线程池资源耗尽而死锁。请注意，当前线程解除阻塞时，可能会暂时有超过所配置线程池大小的任务同时运行，直到足够多的任务执行完毕。

在可行的情况下，应优先使用 `Task.map` 和 `Task.bind` 来建立任务依赖，而不是使用 `Task.get`，因为它们不需要以这种方式临时扩展线程池。尤其是，在任务续体中以 `(sync := true)` 调用 `Task.get` 会引发恐慌，因为此时续体显然并不“廉价”，否则还可能发生死锁。应改为返回所等待的任务，并使用 `Task.bind/IO.bindTask` 将其解包。
-/
def c171 := @_root_.Task.get

/--
等待任务完成，然后返回其结果。
-/
def c172 := @_root_.IO.wait

/--
等待列表中的任一任务完成，然后返回其结果。
-/
def c173 := @_root_.IO.waitAny

/--
`map f x` 将函数 `f` 映射到任务 `x` 上：它会构造（并立即启动）一个新任务，等待 `x` 的值可用，然后对结果调用 `f`。

如果提供了 `prio`，它就是该任务的优先级。
如果将 `sync` 设为 true，那么当 `x` 已经完成时，`f` 在当前线程上执行；否则在 `x` 完成所在的线程上执行。此时忽略 `prio`。仅当执行 `f` 的开销很小且不会阻塞时才应这样做。
-/
def c174 := @_root_.Task.map

/--
`bind x f` 对任务 `x` 和函数 `f` 执行单子的“绑定”操作：它会构造（并立即启动）一个新任务，等待 `x` 的值可用，然后对结果调用 `f`，得到另一个任务，再运行该任务以取得结果。

如果提供了 `prio`，它就是该任务的优先级。
如果将 `sync` 设为 true，那么当 `x` 已经完成时，`f` 在当前线程上执行；否则在 `x` 完成所在的线程上执行。此时忽略 `prio`。仅当执行 `f` 的开销很小且不会阻塞时才应这样做。
-/
def c175 := @_root_.Task.bind

/--
创建一个任务；当 `tasks` 中的所有任务都完成后，该任务计算把 `f` 应用于这些任务结果所得的值。
-/
def c176 := @_root_.Task.mapList

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `BaseIO` 操作 `f`。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c177 := @_root_.BaseIO.mapTask

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `IO` 操作 `f`。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。由于 `EIO ε` 操作可能抛出 `ε` 类型的异常，任务结果是 `Except ε α`。
-/
def c178 := @_root_.EIO.mapTask

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `IO` 操作 `f`。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。由于 `IO` 操作可能抛出 `IO.Error` 类型的异常，任务结果是 `Except IO.Error α`。
-/
def c179 := @_root_.IO.mapTask

/--
创建一个新任务，等待列表 `tasks` 中的所有任务完成，然后对它们的结果运行 `IO` 操作 `f`。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c180 := @_root_.BaseIO.mapTasks

/--
创建一个新任务，等待列表 `tasks` 中的所有任务完成，然后对它们的结果运行 `EIO ε` 操作 `f`。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c181 := @_root_.EIO.mapTasks

/--
`EIO.mapTasks` 的 `IO` 特化版本。
-/
def c182 := @_root_.IO.mapTasks

/--
创建一个新任务，等待 `t` 完成，对其结果运行 `IO` 操作 `f`，然后以所得任务继续执行。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动这个新任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c183 := @_root_.BaseIO.bindTask

/--
创建一个新任务，等待 `t` 完成，对其结果运行 `EIO ε` 操作 `f`，然后以所得任务继续执行。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动这个新任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。由于 `EIO ε` 操作可能抛出 `ε` 类型的异常，任务结果是 `Except ε α`。
-/
def c184 := @_root_.EIO.bindTask

/--
创建一个新任务，等待 `t` 完成，对其结果运行 `IO` 操作 `f`，然后以所得任务继续执行。新任务的优先级为 `prio`。

运行所得的 `BaseIO` 操作会立即启动这个新任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。由于 `IO` 操作可能抛出 `IO.Error` 类型的异常，任务结果是 `Except IO.Error α`。
-/
def c185 := @_root_.IO.bindTask

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `IO` 操作 `f`。新任务的优先级为 `prio`。

这是忽略结果值的 `BaseIO.mapTask` 版本。

运行所得的 `BaseIO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c186 := @_root_.BaseIO.chainTask

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `EIO ε` 操作 `f`。新任务的优先级为 `prio`。

这是忽略结果值的 `EIO.mapTask` 版本。

运行所得的 `EIO ε` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止该操作或让它对最后一个引用被丢弃作出其他响应，`act` 应通过 `IO.checkCanceled` 显式检查取消。
-/
def c187 := @_root_.EIO.chainTask

/--
创建一个新任务，等待 `t` 完成，然后对其结果运行 `IO` 操作 `f`。新任务的优先级为 `prio`。

这是忽略结果值的 `IO.mapTask` 版本。

运行所得的 `IO` 操作会立即启动任务。与通过 `Task.spawn` 创建的纯任务不同，即使任务的最后一个引用被丢弃，此函数创建的任务仍会运行。如果此时应终止 act 或让它对最后一个引用被丢弃作出其他响应，应通过 `IO.checkCanceled` 显式检查取消。
-/
def c188 := @_root_.IO.chainTask

/--
请求协作式取消任务。任务必须显式调用 `IO.checkCanceled` 才会响应取消。
-/
def c189 := @_root_.IO.cancel

/--
检查当前任务的取消标志是否已因调用 `IO.cancel` 或丢弃任务的最后一个引用而置位。
-/
def c190 := @_root_.IO.checkCanceled

/--
检查任务是否已执行完毕；一旦完成，调用 `Task.get` 会立即返回。
-/
def c191 := @_root_.IO.hasFinished

/--
返回 Lean 运行时任务管理器中任务的当前状态。

对于派生自 `Promise` 的任务，应将 `waiting` 和 `running` 状态视为等价。
-/
def c192 := @_root_.IO.getTaskState

/--
Lean 运行时任务管理器中 `Task` 的当前状态。
-/
inductive c193 where
  /--
`Task` 正在等待运行。

它可能正在等待依赖项完成，也可能位于任务管理器队列中等待可用的运行线程。
  -/
  | waiting
  /-- `Task` 正在某个线程上运行；对于 `Promise`，则表示正在等待调用 `IO.Promise.resolve`。 -/
  | running
  /-- `Task` 已经运行完毕，结果可用；对此任务调用 `Task.get` 或 `IO.wait` 不会阻塞。 -/
  | finished

/--
返回调用线程的线程 ID。
-/
def c194 := @_root_.IO.getTID

/--
`Promise α` 允许创建一个 `Task α`，其值稍后通过调用 `resolve` 提供。

典型用法如下：
1. `let promise ← Promise.new` 创建一个承诺
2. `promise.result? : Task (Option α)` 现在可以四处传递
3. `promise.result?.get` 阻塞，直到承诺得到解析
4. `promise.resolve a` 解析该承诺
5. `promise.result?.get` 现在返回 `some a`

如果承诺在从未解析的情况下被丢弃，`promise.result?.get` 将返回 `none`。
其他处理方式请参阅 `Promise.result!/resultD`。
-/
structure c195 (α : Type) where
  private mk ::
  /-- 保存一次性解析状态和结果任务的底层承诺对象。真实声明没有此字段的文档。 -/
  private prom : _root_.IO.Promise α
  /-- `α` 非空的证据，供底层承诺的运行时表示使用。真实声明没有此字段的文档。 -/
  private h : Nonempty α

/--
创建一个新的 `Promise`。
-/
def c196 := @_root_.IO.Promise.new

/--
检查承诺是否已经解析，即访问 `result*` 是否会立即返回。
-/
def c197 := @_root_.IO.Promise.isResolved

/--
与 `Promise.result` 类似，但如果承诺在从未解析的情况下被丢弃，则解析为 `none`。
-/
def c198 := @_root_.IO.Promise.result?

/--
`Promise` 的结果任务。

该任务会阻塞，直到调用 `Promise.resolve`。如果承诺在从未解析的情况下被丢弃，对任务求值将引发恐慌；不使用致命恐慌时，则会永远阻塞。由于 `Promise.result!` 是纯值，可能无法准确得知其求值时点，因此任何*可能*对其求值 `Promise.result!` 的承诺都*必须*最终得到解析。如有疑问，应始终优先使用 `Promise.result?` 显式处理被丢弃的承诺。
-/
def c199 := @_root_.IO.Promise.result!

/--
与 `Promise.result` 类似，但如果承诺在从未解析的情况下被丢弃，则解析为 `dflt`。
-/
def c200 := @_root_.IO.Promise.resultD

/--
解析一个 `Promise`。

只有第一次调用此函数会产生效果。
-/
def c201 := @_root_.IO.Promise.resolve

/--
一种多生产者、多消费者的 FIFO 通道，既支持有界和无界缓冲，也提供异步 API。使用 `Channel.sync` 可切换到同步模式。

如果通道需要通过关闭来表示某种完成事件，请改用 `Std.CloseableChannel`。请注意，`Std.CloseableChannel` 在某些情况下需要错误处理，因此适用时通常更容易使用 `Std.Channel`。
-/
structure c202 (α : Type) where
  private mk ::
  /-- 实现异步通道操作的底层可关闭通道。真实声明没有此字段的文档。 -/
  private inner : _root_.Std.CloseableChannel α

/--
创建新通道。若：
- `capacity` 为 `none`，通道无界（默认）
- `capacity` 为 `some 0`，发送方与接收方每次都必须会合
- `capacity` 为 `some n` 且 `n > 0`，通道使用大小为 `n` 的缓冲区，缓冲区填满后开始阻塞
-/
def c203 := @_root_.Std.Channel.new

/--
通过通道发送一个值，并返回一个在传输完成后解析的任务。
-/
def c204 := @_root_.Std.Channel.send

/--
从通道接收一个值，并返回一个在传输完成后解析的任务。请注意，如果通道在传输完成前关闭，该任务可能解析为 `none`。
-/
def c205 := @_root_.Std.Channel.recv

/--
`ch.forAsync f` 对从 `ch` 接收的每条消息调用 `f`。

请注意，如果调用此函数两次，每条消息只会到达其中恰好一次调用。
-/
def c206 := @_root_.Std.Channel.forAsync

/--
此函数不执行任何操作，只是用于方便地公开通道的同步 API。
-/
def c207 := @_root_.Std.Channel.sync

/--
一种多生产者、多消费者的 FIFO 通道，既支持有界和无界缓冲，也提供同步 API。此类型只是以阻塞方式使用通道的便捷层，与原通道并无实际区别。

如果通道需要通过关闭来表示某种完成事件，请改用 `Std.CloseableChannel.Sync`。请注意，`Std.CloseableChannel.Sync` 在某些情况下需要错误处理，因此适用时通常更容易使用 `Std.Channel.Sync`。
-/
def c208 := @_root_.Std.Channel.Sync

/--
一种多生产者、多消费者的 FIFO 通道，既支持有界和无界缓冲，也提供异步 API；使用 `CloseableChannel.sync` 可切换到同步模式。

此外，与 `Std.Channel` 不同，`Std.CloseableChannel` 可在需要时关闭。这在某些情况下会带来错误处理的需要，因此适用时通常更容易使用 `Std.Channel`。
-/
def c209 := @_root_.Std.CloseableChannel

/--
创建新通道。若：
- `capacity` 为 `none`，通道无界（默认）
- `capacity` 为 `some 0`，发送方与接收方每次都必须会合
- `capacity` 为 `some n` 且 `n > 0`，通道使用大小为 `n` 的缓冲区，缓冲区填满后开始阻塞
-/
def c210 := @_root_.Std.CloseableChannel.new

/--
保护 `α` 类型共享状态的互斥原语（锁）。

`Mutex α` 类型类似于 `IO.Ref α`，但并发访问由互斥锁保护，而不是通过原子指针操作和忙等待来保护。
-/
structure c211 (α : Type) where
  private mk ::
  /-- 保存受互斥锁保护状态的引用。真实声明没有此字段的文档。 -/
  private ref : _root_.IO.Ref α
  /-- 控制对 `ref` 中共享状态进行互斥访问的底层锁。真实声明没有此字段的文档。 -/
  mutex : _root_.Std.BaseMutex

/--
创建一个新的互斥锁。
-/
def c212 := @_root_.Std.Mutex.new

/--
`mutex.atomically k` 在锁定互斥锁期间运行 `k`，使其可访问互斥锁的状态。

如果同一线程已持有底层 `BaseMutex`，再调用 `mutex.atomically` 属于未定义行为。如果代码无法避免这种情况，请考虑使用 `RecursiveMutex`。
-/
def c213 := @_root_.Std.Mutex.atomically

/--
`mutex.atomicallyOnce condvar pred k` 运行 `k`，并在 `condvar` 上等待，直到 `pred` 返回 true。`k` 和 `pred` 都可以访问互斥锁的状态。

如果同一线程已持有底层 `BaseMutex`，再调用 `mutex.atomicallyOnce` 属于未定义行为。如果代码无法避免这种情况，请考虑使用 `RecursiveMutex`。
-/
def c214 := @_root_.Std.Mutex.atomicallyOnce

/--
`AtomicT α m` 是一种单子，可在 `Mutex α` 等互斥原语内部，以外层单子 `m` 原子地执行。
该操作可以通过 `get` 和 `set` 访问互斥锁的状态 `α`。
-/
def c215 := @_root_.Std.AtomicT

/--
条件变量是一种与 `BaseMutex` 或 `Mutex` 配合使用的同步原语。

希望修改共享变量的线程必须：
1. 锁定 `BaseMutex` 或 `Mutex`
2. 操作共享变量
3. 完成后调用 `Condvar.notifyOne` 或 `Condvar.notifyAll`。请注意，这可以在解锁互斥锁之前或之后进行。

若使用 `Mutex`，等待 `Condvar` 的线程可以使用 `Mutex.atomicallyOnce` 等待条件成立。若使用 `BaseMutex`，则必须：
1. 锁定 `BaseMutex`。
2. 执行以下操作之一：
  - 使用 `Condvar.waitUntil` 在条件变量上（可能反复）等待，直到条件成立。
  - 按以下步骤手动实现等待：
    1. 检查条件
    2. 调用 `Condvar.wait`；它会释放 `BaseMutex` 并暂停执行，直到条件变量收到通知。
    3. 检查条件；如果尚未满足，则继续等待。
-/
def c216 := @_root_.Std.Condvar

/--
创建一个新的条件变量。
-/
def c217 := @_root_.Std.Condvar.new

/--
等待，直到另一线程调用 `notifyOne` 或 `notifyAll`。
-/
def c218 := @_root_.Std.Condvar.wait

/--
唤醒一个正在执行 `wait` 的其他线程。
-/
def c219 := @_root_.Std.Condvar.notifyOne

/--
唤醒所有正在执行 `wait` 的其他线程。
-/
def c220 := @_root_.Std.Condvar.notifyAll

/--
在条件变量上等待，直到谓词为真。
-/
def c221 := @_root_.Std.Condvar.waitUntil


end Manual.ZhDocString.IO
