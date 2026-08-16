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

/-- 不会抛出异常的 `IO` 单子。 -/
def c001 := @_root_.BaseIO

/-- 支持任意副作用并可抛出 `IO.Error` 类型异常的单子。 -/
def c002 := @_root_.IO

/--
一个可以对外部世界产生副作用，或抛出 `ε` 类型异常的单子。

`BaseIO` 是此单子的不抛异常版本。`IO` 则将异常类型设为 `IO.Error`。
-/
def c003 := @_root_.EIO

/-- 创建一个 IO 动作；当且仅当它被执行时，才会调用 `fn`，并返回其结果。 -/
def c004 := @_root_.IO.lazyPure

/--
将一个不会抛出异常的 `BaseIO` 动作作为 `IO` 动作运行。

此函数通常通过[自动单子提升](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=lifting-monads)隐式使用，而不是显式调用。
-/
def c005 := @_root_.BaseIO.toIO

/--
在任意其他 `EIO` 单子 中运行一个不会抛出异常的 `BaseIO` 动作。

此函数通常通过[自动单子提升](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=lifting-monads)隐式使用，而不是显式调用。
-/
def c006 := @_root_.BaseIO.toEIO

/--
将一个可能抛出 `ε` 类型异常的 `EIO ε` 动作，转换为一个不抛异常、返回 `Except` 值的 `BaseIO`
动作。
-/
def c007 := @_root_.EIO.toBaseIO

/--
使用 `f` 将其抛出的任何异常翻译为 `IO.Error`，从而把 `EIO ε` 动作转换为 `IO` 动作。
-/
def c008 := @_root_.EIO.toIO

/--
将一个可能抛出 `ε` 类型异常的 `EIO ε` 动作，转换为一个不抛异常、返回 `Except` 值的 `IO`
动作。
-/
def c009 := @_root_.EIO.toIO'

/-- 在某个其他 `EIO` 单子 中运行一个 `IO` 动作，并用 `f` 转换 `IO` 异常。 -/
def c010 := @_root_.IO.toEIO

/--
可在 `IO` 单子 中抛出的异常。

`IO.Error` 的许多构造子都对应 POSIX 错误号。在这些情况下，文档字符串会列出与该错误相对应的
POSIX 标准错误宏。该列表不一定穷尽全部情况，并且这些构造子还包含一个字段，用于保存底层错误号。
-/
inductive c011 where
  /--
  操作失败，因为文件已存在。

  这对应 POSIX 错误 `EEXIST`、`EINPROGRESS` 和 `EISCONN`。
  -/
  | alreadyExists : Option String → UInt32 → String → c011
  /--
  发生了 `IO.Error` 其他构造子未覆盖的某种错误。

  这还包括 POSIX 错误 `EFAULT`。
  -/
  | otherError : UInt32 → String → c011
  /--
  某个必需资源正忙。

  这对应 POSIX 错误 `EADDRINUSE`、`EBUSY`、`EDEADLK` 和 `ETXTBSY`。
  -/
  | resourceBusy : UInt32 → String → c011
  /--
  某个必需资源已不再可用。

  这对应 POSIX 错误 `ECONNRESET`、`EIDRM`、`ENETDOWN`、`ENETRESET`、`ENOLINK` 和
  `EPIPE`。
  -/
  | resourceVanished : UInt32 → String → c011
  /--
  某项操作不受支持。

  这对应 POSIX 错误 `EADDRNOTAVAIL`、`EAFNOSUPPORT`、`ENODEV`、`ENOPROTOOPT`、
  `ENOSYS`、`EOPNOTSUPP`、`ERANGE`、`ESPIPE` 和 `EXDEV`。
  -/
  | unsupportedOperation : UInt32 → String → c011
  /--
  操作因硬件问题而失败，例如 I/O 错误。

  这对应 POSIX 错误 `EIO`。
  -/
  | hardwareFault : UInt32 → String → c011
  /--
  操作所需的某个约束未被满足（例如目录非空）。

  这对应 POSIX 错误 `ENOTEMPTY`。
  -/
  | unsatisfiedConstraints : UInt32 → String → c011
  /--
  尝试了不恰当的 I/O 控制操作。

  这对应 POSIX 错误 `ENOTTY`。
  -/
  | illegalOperation : UInt32 → String → c011
  /--
  发生了协议错误。

  这对应 POSIX 错误 `EPROTO`、`EPROTONOSUPPORT` 和 `EPROTOTYPE`。
  -/
  | protocolError : UInt32 → String → c011
  /--
  某项操作超时。

  这对应 POSIX 错误 `ETIME` 和 `ETIMEDOUT`。
  -/
  | timeExpired : UInt32 → String → c011
  /--
  操作被中断。

  这对应 POSIX 错误 `EINTR`。
  -/
  | interrupted : String → UInt32 → String → c011
  /--
  没有这样的文件或目录。

  这对应 POSIX 错误 `ENOENT`。
  -/
  | noFileOrDirectory : String → UInt32 → String → c011
  /--
  I/O 操作的某个实参无效。

  这对应 POSIX 错误 `ELOOP`、`ENAMETOOLONG`、`EDESTADDRREQ`、`EILSEQ`、`EINVAL`、
  `EDOM`、`EBADF`、`ENOEXEC`、`ENOSTR`、`ENOTCONN` 和 `ENOTSOCK`。
  -/
  | invalidArgument : Option String → UInt32 → String → c011
  /--
  操作因权限不足而失败。

  这对应 POSIX 错误 `EACCES`、`EROFS`、`ECONNABORTED`、`EFBIG` 和 `EPERM`。
  -/
  | permissionDenied : Option String → UInt32 → String → c011
  /--
  某种资源已耗尽。

  这对应 POSIX 错误 `EMFILE`、`ENFILE`、`ENOSPC`、`E2BIG`、`EAGAIN`、`EMLINK`、
  `EMSGSIZE`、`ENOBUFS`、`ENOLCK`、`ENOMEM` 和 `ENOSR`。
  -/
  | resourceExhausted : Option String → UInt32 → String → c011
  /--
  某个实参具有错误的类型（例如需要文件时却给了目录）。

  这对应 POSIX 错误 `EISDIR`、`EBADMSG` 和 `ENOTDIR`。
  -/
  | inappropriateType : Option String → UInt32 → String → c011
  /--
  某个必需资源不存在。

  这对应 POSIX 错误 `ENXIO`、`EHOSTUNREACH`、`ENETUNREACH`、`ECHILD`、
  `ECONNREFUSED`、`ENODATA`、`ENOMSG` 和 `ESRCH`。
  -/
  | noSuchThing : Option String → UInt32 → String → c011
  /-- 遇到了意外的文件结束标记。 -/
  | unexpectedEof : c011
  /-- 发生了某种其他错误。 -/
  | userError : String → c011

/--
将 `IO.Error` 转换为描述性的字符串。

`IO.Error.userError` 会被转换为其内嵌消息。其他构造子则会以保留结构化信息的方式转换，
例如错误码和文件名，这些信息有助于诊断问题。
-/
def c012 := @_root_.IO.Error.toString

/--
将一个 `Except ε` 动作转换为 `IO` 动作。

如果该 `Except ε` 动作抛出异常，则会使用异常类型的 `ToString` 实例将其转换为 `IO.Error`
并抛出；否则返回其中的值。
-/
def c013 := @_root_.IO.ofExcept

/--
处理 `EIO ε` 动作可能抛出的任何异常，并将其转换为一个不抛异常的 `BaseIO` 动作。
-/
def c014 := @_root_.EIO.catchExceptions

/--
从字符串构造一个 `IO.Error`。

`IO.Error` 是 `IO` 单子 所抛出异常的类型。
-/
def c015 := @_root_.IO.userError

/--
迭代执行一个 `IO` 动作。从初始状态开始，反复应用该动作，直到它在 `Sum.inr` 中返回最终值。
每当它返回 `Sum.inl` 时，返回值都会被视为新的状态。
-/
def c016 := @_root_.IO.iterate

/-- 当前平台的字长，可能为 64 位或 32 位。 -/
def c017 := @_root_.System.Platform.numBits

/-- 当前平台的 LLVM 目标三元组。若 Lean 编译时缺失，则为空。 -/
def c018 := @_root_.System.Platform.target

/-- 当前平台是 Windows 吗？ -/
def c019 := @_root_.System.Platform.isWindows

/-- 当前平台是 macOS 吗？ -/
def c020 := @_root_.System.Platform.isOSX

/-- 当前平台是 [Emscripten](https://emscripten.org/) 吗？ -/
def c021 := @_root_.System.Platform.isEmscripten

/--
返回环境变量 `var` 的值；如果它不存在于环境中，则返回 `none`。
-/
def c022 := @_root_.IO.getEnv

/-- 暂停执行指定的毫秒数。 -/
def c023 := @_root_.IO.sleep

/--
以纳秒为单位，返回自某个未指定的过去时刻以来单调递增的时间。它与挂钟时间没有关系。
-/
def c024 := @_root_.IO.monoNanosNow

/--
以毫秒为单位，返回自某个未指定的过去时刻以来单调递增的时间。它与挂钟时间没有关系。
-/
def c025 := @_root_.IO.monoMsNow

/--
返回当前线程执行期间已经发生的 _心跳_ 数量。心跳 计数是线程执行的“小型”内存分配次数。

心跳 用于实现跨不同硬件更具确定性的超时。
-/
def c026 := @_root_.IO.getNumHeartbeats

/--
按给定数量调整当前线程的 心跳 计数器。这可用于为避免分配的代码增加额外“权重”，也可在从快照恢复后用来调整计数器。

心跳 是实现“确定性”超时的一种方式。心跳 计数器是当前执行线程上进行的“小型”内存分配次数。
-/
def c027 := @_root_.IO.addHeartbeats

/-- 返回调用进程的当前工作目录。 -/
def c028 := @_root_.IO.Process.getCurrentDir

/-- 设置调用进程的当前工作目录。 -/
def c029 := @_root_.IO.Process.setCurrentDir

/--
以给定退出码终止当前进程。`0` 表示成功，其他所有值都表示失败。
-/
def c030 := @_root_.IO.Process.exit

/-- 返回调用进程的进程 ID。 -/
def c031 := @_root_.IO.Process.getPID

/--
运行一个进程直到完成，并阻塞等待其终止。
子进程使用空标准输入运行；如果提供了输入，则使用指定输入。
如果子进程以退出码 0 成功终止，则返回其标准输出。
若以任何其他退出码终止，则抛出异常。

`args` 中对标准输入、输出和错误句柄的指定会被忽略。
-/
def c032 := @_root_.IO.Process.run

/--
运行一个进程直到完成，并捕获其输出和退出码。
子进程使用空标准输入运行；如果提供了输入，则使用指定输入，
当前进程会阻塞直到它运行完毕。

`args` 中对标准输入、输出和错误句柄的指定会被忽略。
-/
def c033 := @_root_.IO.Process.output

/--
使用给定配置启动一个子进程。子进程通过操作系统原语生成，因此可以用任何语言编写。

子进程与父进程并行运行。

如果子进程的标准输入是管道，请使用 `IO.Process.Child.takeStdin`，这样就能在进程终止前关闭子进程的标准输入，从而向子进程提供一个文件结束标记。
-/
def c034 := @_root_.IO.Process.spawn

/-- 子进程的标准输入、输出与错误流配置。 -/
structure StdioConfig where
  /-- 标准输入配置。 -/
  stdin : _root_.IO.Process.Stdio := .inherit
  /-- 标准输出配置。 -/
  stdout : _root_.IO.Process.Stdio := .inherit
  /-- 标准错误配置。 -/
  stderr : _root_.IO.Process.Stdio := .inherit

/--
将要生成的子进程的配置。

使用 `IO.Process.spawn` 启动子进程。当子进程应运行至完成，并捕获其输出和/或错误码时，可使用
`IO.Process.output` 与 `IO.Process.run`。
-/
structure c035 extends StdioConfig where
  /-- 命令名。 -/
  cmd : String
  /-- 命令的实参。 -/
  args : Array String := #[]
  /-- 子进程的工作目录。若为 `none`，则继承父进程当前工作目录。 -/
  cwd : Option _root_.System.FilePath := none
  /--
  为子进程添加或移除环境变量。

  子进程会继承父进程的环境，并按 `env` 中的修改进行调整。数组中的键是环境变量名。`none`
  会从环境中移除该项，`some` 则将变量设为新值；如有需要会新增该变量。变量按从左到右的顺序处理。
  -/
  env : Array (String × Option String) := #[]
  /-- 从创建它的进程继承环境变量。 -/
  inheritEnv : Bool := true
  /-- 使用 `setsid` 在新会话与新进程组中启动子进程。目前在非 POSIX 平台上无效果。 -/
  setsid : Bool := false

/-- 子进程的标准输入、输出与错误句柄的配置。 -/
structure c036 where
  /-- 进程标准输入句柄的配置。 -/
  stdin : _root_.IO.Process.Stdio := .inherit
  /-- 进程标准输出句柄的配置。 -/
  stdout : _root_.IO.Process.Stdio := .inherit
  /-- 进程标准错误句柄的配置。 -/
  stderr : _root_.IO.Process.Stdio := .inherit

/--
子进程的标准输入、输出与错误句柄应连接到管道、继承自父进程，还是为空。

如果该流是管道，则父进程可以用它与子进程通信。
-/
inductive c037 where
  /-- 该流应连接到管道。 -/
  | piped
  /-- 该流应继承自父进程。 -/
  | inherit
  /-- 该流应为空。 -/
  | null

/--
可用于通过子进程的标准输入、输出或错误流与之通信的句柄类型。

对于 `IO.Process.Stdio.piped`，此类型为 `IO.FS.Handle`。否则它是 `Unit`，因为无法进行通信。
-/
def c038 := @_root_.IO.Process.Stdio.toHandleType

/--
使用配置 `cfg` 生成的子进程。

该配置决定了子进程的标准输入、标准输出和标准错误是 `IO.FS.Handle` 还是 `Unit`。
-/
structure c039 (cfg : _root_.IO.Process.StdioConfig) where
  private mk ::
  /--
  若配置为 `IO.Process.Stdio.piped`，则为子进程的标准输入句柄；否则为 `()`。
  -/
  stdin : cfg.stdin.toHandleType
  /--
  若配置为 `IO.Process.Stdio.piped`，则为子进程的标准输出句柄；否则为 `()`。
  -/
  stdout : cfg.stdout.toHandleType
  /--
  若配置为 `IO.Process.Stdio.piped`，则为子进程的标准错误句柄；否则为 `()`。
  -/
  stderr : cfg.stderr.toHandleType

/-- 阻塞直到子进程退出，并返回其退出码。 -/
def c040 := @_root_.IO.Process.Child.wait

/--
检查子进程是否已经退出。若进程尚未退出，则返回 `none`；否则返回其退出码。
-/
def c041 := @_root_.IO.Process.Child.tryWait

/--
使用 `SIGTERM` 信号或平台上的对应机制终止子进程。

如果该进程是使用 `SpawnArgs.setsid` 启动的，则会改为终止整个进程组。
-/
def c042 := @_root_.IO.Process.Child.kill

/--
从 `Child` 对象中取出 `stdin` 字段，从而在保留对子进程引用的同时允许关闭该句柄。

文件句柄会在其最后一个引用被丢弃时关闭。关闭子进程的标准输入会导致一个文件结束标记。由于
`Child` 对象持有对标准输入的引用，因此若要在进程运行期间关闭该流，就必须执行此操作（例如在调用
`Child.wait` 后提取其退出码）。许多进程在其标准输入耗尽之前都不会终止。
-/
def c043 := @_root_.IO.Process.Child.takeStdin

/-- 进程运行至完成后的结果。 -/
structure c044 where
  /-- 进程的退出码。 -/
  exitCode : UInt32
  /-- 进程写入其标准输出的全部内容。 -/
  stdout : String
  /-- 进程写入其标准错误的全部内容。 -/
  stderr : String

/-- 为 `IO.rand` 所使用的随机数生成器状态设定种子。 -/
def c045 := @_root_.IO.setRandSeed

/--
返回 `lo` 与 `hi` 之间的一个伪随机数，并使用、更新一个已保存的随机数生成器状态。

该状态可通过 `IO.setRandSeed` 设定种子。
-/
def c046 := @_root_.IO.rand

/-- 生成一个随机布尔值。 -/
def c047 := @_root_.randBool

/-- 在区间 [lo, hi] 内生成一个随机自然数。 -/
def c048 := @_root_.randNat

/-- 随机数生成器的接口。 -/
class c049 (g : Type u) where
  /--
  `range` 返回该生成器会产生的值域。
  -/
  range : g → Nat × Nat
  /--
  `next` 操作返回一个在 `range` 所返回区间内（包含两个端点）均匀分布的自然数，以及一个新的生成器。
  -/
  next : g → Nat × g
  /--
  split 操作允许获得两个不同的随机数生成器。这在函数式程序中非常有用（例如将随机数生成器传递给递归调用时）。
  -/
  split : g → g × g

/-- “标准”随机数生成器。 -/
structure c050 where
  /-- 第一个内部状态种子。 -/
  s1 : Nat
  /-- 第二个内部状态种子。 -/
  s2 : Nat

/-- `StdGen` 返回值的范围。 -/
def c051 := @_root_.stdRange

/-- `StdGen` 的下一个值，以及更新后的生成器状态。 -/
def c052 := @_root_.stdNext

/-- 将一个 `StdGen` 拆分为两个独立状态。 -/
def c053 := @_root_.stdSplit

/-- 返回一个标准随机数生成器。 -/
def c054 := @_root_.mkStdGen

/--
从系统熵源中读取字节。它不保证具有密码学安全性。

如果 `nBytes` 为 `0`，则立即返回一个空缓冲区。
-/
def c055 := @_root_.IO.getRandomBytes

/--
使用 `ToString α` 实例将 `s` 转换为字符串，并将其打印到当前标准输出（由 `IO.getStdout` 决定）。
-/
def c056 := @_root_.IO.print

/--
使用 `ToString α` 实例将 `s` 转换为字符串，并在其后附加换行符，将其打印到当前标准输出（由
`IO.getStdout` 决定）。
-/
def c057 := @_root_.IO.println

/--
使用 `ToString α` 实例将 `s` 转换为字符串，并将其打印到当前标准错误（由 `IO.getStderr` 决定）。
-/
def c058 := @_root_.IO.eprint

/--
使用 `ToString α` 实例将 `s` 转换为字符串，并在其后附加换行符，将其打印到当前标准错误（由
`IO.getStderr` 决定）。
-/
def c059 := @_root_.IO.eprintln

/--
对已打开文件的引用。

文件句柄包装底层操作系统的文件描述符。没有显式关闭文件的操作：当文件句柄的最后一个引用被丢弃时，
文件会自动关闭。

句柄带有关联的读/写光标，用来决定在文件中的读写位置。
-/
def c060 := @_root_.IO.FS.Handle

/--
以给定 `mode` 打开位于 `fn` 的文件。

如果文件无法打开，则会抛出异常。
-/
def c061 := @_root_.IO.FS.Handle.mk

/--
文件应以读取、写入、创建并写入，或追加的哪种方式打开。

在操作系统层面，这会转换为文件句柄的模式（即一组 `open` 标志以及一个 `fdopen` 模式）。

此数据类型表示的所有模式都不会转换行结束符（即 Windows 上的 `O_BINARY`）。此外，这些模式不会在进程创建时被继承（即 Windows 上的 `O_NOINHERIT`，以及其他平台上的 `O_CLOEXEC`）。

**操作系统特有信息：**
* Windows:
  [`_open`](https://learn.microsoft.com/en-us/cpp/c-runtime-library/reference/open-wopen?view=msvc-170),
  [`_fdopen`](https://learn.microsoft.com/en-us/cpp/c-runtime-library/reference/fdopen-wfdopen?view=msvc-170)
* Linux: [`open`](https://linux.die.net/man/2/open), [`fdopen`](https://linux.die.net/man/3/fdopen)
-/
inductive c062 where
  /--
  文件应以读取方式打开。

  读/写光标会定位到文件开头。如果文件不存在，则会报错。

  * `open` 标志： `O_RDONLY`
  * `fdopen` 模式： `r`
  -/
  | read
  /--
  文件应以写入方式打开。

  如果文件已存在，则会被截断为零长度。否则会创建一个新文件。读/写光标会定位到文件开头。

  * `open` 标志： `O_WRONLY | O_CREAT | O_TRUNC`
  * `fdopen` 模式： `w`
  -/
  | write
  /--
  应创建一个新文件以供写入。

  如果文件已经存在，则会报错。会创建一个新文件，并将读/写光标定位到开头。

  * `open` 标志： `O_WRONLY | O_CREAT | O_TRUNC | O_EXCL`
  * `fdopen` 模式： `w`
  -/
  | writeNew
  /--
  文件应同时以读取和写入方式打开。

  如果文件尚不存在，则会报错。读/写光标会定位到文件开头。

  * `open` 标志： `O_RDWR`
  * `fdopen` 模式： `r+`
  -/
  | readWrite
  /--
  文件应以写入方式打开。

  如果文件尚不存在，则会创建它。如果文件已存在，则会打开它，并将读/写光标定位到文件末尾。

  * `open` 标志： `O_WRONLY | O_CREAT | O_APPEND`
  * `fdopen` 模式： `a`
  -/
  | append

/--
从该句柄中最多读取给定数量的字节。如果返回的数组为空，则表示已到达文件结束标记（EOF）。

遇到 EOF 并不会关闭句柄。后续读取仍可能阻塞并返回更多数据。
-/
def c063 := @_root_.IO.FS.Handle.read

/--
将文件句柄中剩余的全部内容读取为 UTF-8 编码字符串。如果内容不是有效的 UTF-8，则会抛出异常。

底层文件不会自动关闭，后续从该句柄读取仍可能阻塞和/或返回数据。
-/
def c064 := @_root_.IO.FS.Handle.readToEnd

/--
读取文件句柄中剩余的全部内容，直到遇到文件结束标记（EOF）。

遇到 EOF 时底层文件不会自动关闭，后续从该句柄读取仍可能阻塞和/或返回数据。
-/
def c065 := @_root_.IO.FS.Handle.readBinToEnd

/--
读取文件句柄中剩余的全部内容，直到遇到文件结束标记（EOF）。

遇到 EOF 时底层文件不会自动关闭，后续从该句柄读取仍可能阻塞和/或返回数据。
-/
def c066 := @_root_.IO.FS.Handle.readBinToEndInto

/--
从该句柄读取 UTF-8 编码文本，直到并包括下一个换行符。如果返回的字符串为空，则表示已到达文件结束标记（EOF）。

遇到 EOF 并不会关闭句柄。后续读取仍可能阻塞并返回更多数据。
-/
def c067 := @_root_.IO.FS.Handle.getLine

/--
将给定字节写入该句柄。

对句柄的写入通常会被缓冲，因此未必会立即修改磁盘上的文件。使用 `IO.FS.Handle.flush` 将缓冲区中的更改写入关联设备。
-/
def c068 := @_root_.IO.FS.Handle.write

/--
使用 UTF-8 编码将给定字符串写入该文件句柄。

对句柄的写入通常会被缓冲，因此未必会立即修改磁盘上的文件。使用 `IO.FS.Handle.flush` 将缓冲区中的更改写入关联设备。
-/
def c069 := @_root_.IO.FS.Handle.putStr

/-- 将字符串内容写入该句柄，并在其后附加一个换行符。使用 UTF-8。 -/
def c070 := @_root_.IO.FS.Handle.putStrLn

/--
刷新与该句柄关联的输出缓冲区，将任何尚未写出的数据写入关联输出设备。
-/
def c071 := @_root_.IO.FS.Handle.flush

/-- 将读/写光标回绕到该句柄所对应文件的开头。 -/
def c072 := @_root_.IO.FS.Handle.rewind

/--
将该句柄截断到其当前读/写光标位置。

此操作不会自动刷新输出缓冲区，因此输出设备的内容可能不会立刻反映这项变化。这通常不会导致问题，因为读/写光标会计入缓冲写入。然而，若先进行缓冲写入，再执行 `IO.FS.Handle.rewind`，然后执行 `IO.FS.Handle.truncate`，最后关闭文件，则可能产生一个非空文件。若不确定，请在截断前调用 `IO.FS.Handle.flush`。
-/
def c073 := @_root_.IO.FS.Handle.truncate

/-- 如果句柄引用的是 Windows 控制台或 Unix 终端，则返回 `true`。 -/
def c074 := @_root_.IO.FS.Handle.isTty

/--
获取该句柄上的排它锁或共享锁。如有必要，会阻塞等待锁可用。

当已经持有共享锁时，再获取排它锁 **并不能** 可靠地成功：这在类 Unix 系统上可行，但在 Windows 上不行。
-/
def c075 := @_root_.IO.FS.Handle.lock

/--
尝试获取该句柄上的排它锁或共享锁，成功时返回 `true`。如果无法获得锁，则不会阻塞，而是返回 `false`。

当已经持有共享锁时，再获取排它锁 **并不能** 可靠地成功：这在类 Unix 系统上可行，但在 Windows 上不行。
-/
def c076 := @_root_.IO.FS.Handle.tryLock

/-- 释放此前在该句柄上获取的任何锁。即使此前没有获取锁，也会成功。 -/
def c077 := @_root_.IO.FS.Handle.unlock

/--
POSIX 流的纯 Lean 抽象。这些流既可以表示底层 POSIX 流，也可以由 Lean 代码实现。

由于标准输入、标准输出和标准错误都是可被覆盖的 `IO.FS.Stream`，Lean 代码可以捕获并重定向输入与输出。
-/
structure c078 where
  /-- 刷新该流的输出缓冲区。 -/
  flush : _root_.IO Unit
  /--
  从该流中最多读取给定数量的字节。

  如果返回的数组为空，则表示已到达文件结束标记（EOF）。EOF 实际上不会关闭流，因此后续读取仍可能阻塞并返回更多数据。
  -/
  read : USize → _root_.IO ByteArray
  /--
  将给定字节写入该流。

  如果该流表示磁盘文件等物理输出设备，则结果可能会被缓冲。调用 `FS.Stream.flush` 以同步其内容。
  -/
  write : ByteArray → _root_.IO Unit
  /--
  从该流读取文本，直到并包括下一个换行符。

  如果返回的字符串为空，则表示已到达文件结束标记（EOF）。EOF 实际上不会关闭流，因此后续读取仍可能阻塞并返回更多数据。
  -/
  getLine : _root_.IO String
  /-- 将给定字符串写入该流。 -/
  putStr : String → _root_.IO Unit
  /-- 如果该流引用的是 Windows 控制台或 Unix 终端，则返回 `true`。 -/
  isTty : _root_.BaseIO Bool

/--
从对某个缓冲区的可变引用创建一个流。

所得流会模拟一个文件：写入时修改该引用的内容，读取时从其中读取。这些流可与 `IO.withStdin`、
`IO.setStdin` 以及标准输出和标准错误的对应操作符一起使用，以重定向输入和输出。
-/
def c079 := @_root_.IO.FS.Stream.ofBuffer

/--
从文件句柄创建一个 Lean 流。该流的每个操作都由对应的文件句柄操作实现。
-/
def c080 := @_root_.IO.FS.Stream.ofHandle

/-- 将字符串内容写入该流，并在其后附加一个换行符。 -/
def c081 := @_root_.IO.FS.Stream.putStrLn

/--
一个可以在内存中模拟文件的字节缓冲区。

使用 `IO.FS.Stream.ofBuffer` 从缓冲区创建流。
-/
structure c082 where
  /-- 缓冲区的内容。 -/
  data : ByteArray := ByteArray.empty
  /-- 缓冲区中读/写光标的位置。 -/
  pos : Nat := 0

/--
文件系统中的一条路径。

路径由一系列目录以及最后的文件名或目录名组成。它们由平台相关的分隔字符分隔（见 `System.FilePath.pathSeparator`）。
-/
structure c083 where
  /-- 路径的字符串表示。 -/
  toString : String

/--
通过在文件名列表之间插入当前平台的路径分隔符，从而构造一条路径。
-/
def c084 := @_root_.System.mkFilePath

/--
拼接两条路径，并考虑绝对路径的情况。此操作也可通过 `/` 运算符访问。

如果 `sub` 是绝对路径，则会丢弃 `p` 并返回 `sub`。如果 `sub` 是相对路径，则会用平台特定的路径分隔符将其附加到 `p` 上。
-/
def c085 := @_root_.System.FilePath.join

/--
规范化一条路径，返回一条与之等价、但可能更符合平台约定的路径。

特别地：
* 在 Windows 上，驱动器盘符会被转成大写。
* 在支持多种路径分隔符的平台上（也就是 `System.FilePath.pathSeparators` 的长度大于一时），替代分隔符会被替换为首选路径分隔符。

无法保证两条等价路径规范化后一定得到同一条路径。
-/
def c086 := @_root_.System.FilePath.normalize

/--
绝对路径从根目录或驱动器盘符开始。通过绝对路径访问文件不依赖于当前工作目录。
-/
def c087 := @_root_.System.FilePath.isAbsolute

/--
相对路径是指其解释依赖当前工作目录的路径。相对路径不会以根目录或驱动器盘符开头。
-/
def c088 := @_root_.System.FilePath.isRelative

/--
若存在，则返回路径的父目录。

如果该路径是根目录或驱动器盘符的根，则返回 `none`。否则返回该路径的父目录。
-/
def c089 := @_root_.System.FilePath.parent

/-- 在平台特定的路径分隔符处，将路径拆分为单个文件名的列表。 -/
def c090 := @_root_.System.FilePath.components

/--
如果路径的最后一个元素是文件名或目录名，则提取它。

如果最后一项是特殊名称（如 `.` 或 `..`），或者该路径是根目录，则返回 `none`。
-/
def c091 := @_root_.System.FilePath.fileName

/--
提取 `p.fileName` 的主干（不含扩展名的部分）。

如果文件名包含多个扩展名，则只移除最后一个。如果路径末尾没有文件名，则返回 `none`。

示例：
  * `("app.exe" : System.FilePath).fileStem = some "app"`
  * `("file.tar.gz" : System.FilePath).fileStem = some "file.tar"`
  * `("files/" : System.FilePath).fileStem = none`
  * `("files/picture.jpg" : System.FilePath).fileStem = some "picture"`
-/
def c092 := @_root_.System.FilePath.fileStem

/--
提取 `p.fileName` 的扩展名部分。

如果文件名包含多个扩展名，则只提取最后一个。如果路径末尾没有文件名，则返回 `none`。

示例：
  * `("app.exe" : System.FilePath).extension = some "exe"`
  * `("file.tar.gz" : System.FilePath).extension = some "gz"`
  * `("files/" : System.FilePath).extension = none`
  * `("files/picture.jpg" : System.FilePath).extension = some "jpg"`
-/
def c093 := @_root_.System.FilePath.extension

/--
将扩展名 `ext` 追加到路径 `p`。

`ext` 不应带前导 `.`，因为此函数会自行添加。如果 `ext` 为空字符串，则不会添加 `.`。

与 `System.FilePath.withExtension` 不同，此函数不会移除任何已有扩展名。
-/
def c094 := @_root_.System.FilePath.addExtension

/--
将路径 `p` 当前的扩展名替换为 `ext`；如果没有扩展名，则添加它。若路径包含多个文件扩展名，则只替换最后一个。若路径没有文件名，或者 `ext` 为空字符串，则原样返回该文件名。

`ext` 不应带前导 `.`，因为此函数会自行添加。

示例：
* `("files/picture.jpeg" : System.FilePath).withExtension "jpg" = ⟨"files/picture.jpg"⟩`
* `("files/" : System.FilePath).withExtension "zip" = ⟨"files/"⟩`
* `("files" : System.FilePath).withExtension "zip" = ⟨"files.zip"⟩`
* `("files/archive.tar.gz" : System.FilePath).withExtension "xz" = ⟨"files.tar.xz"⟩`
-/
def c095 := @_root_.System.FilePath.withExtension

/--
将路径 `p` 末尾的文件名替换为 `fname`，并将 `fname` 放入 `p` 的父目录中。

如果 `p` 没有父目录，则原样返回 `fname`。
-/
def c096 := @_root_.System.FilePath.withFileName

/--
分隔目录的字符。

在支持多种分隔符的平台上，`System.FilePath.pathSeparator` 是该平台用户期望的“理想”分隔符。`System.FilePath.pathSeparators` 列出了所有受支持的分隔符。
-/
def c097 := @_root_.System.FilePath.pathSeparator

/--
当前平台支持的所有路径分隔符字符组成的列表。

在支持多种分隔符的平台上，`System.FilePath.pathSeparator` 是该平台用户期望的“理想”分隔符。
-/
def c098 := @_root_.System.FilePath.pathSeparators

/-- 将文件扩展名与文件名分隔开的字符。 -/
def c099 := @_root_.System.FilePath.extSeparator

/--
当前平台上可执行二进制文件应使用的文件扩展名；若不存在此类扩展名，则为 `""`。
-/
def c100 := @_root_.System.FilePath.exeExtension

/--
文件元数据。

可使用 `System.FilePath.metadata`/`System.FilePath.symlinkMetadata` 访问文件的元数据。
-/
structure c101 where
  /-- 文件访问时间。 -/
  accessed : _root_.IO.FS.SystemTime
  /-- 文件修改时间。 -/
  modified : _root_.IO.FS.SystemTime
  /-- 文件的字节大小。 -/
  byteSize : UInt64
  /-- 该文件是普通文件、目录、符号链接还是其他类型的文件。 -/
  type : _root_.IO.FS.FileType
  /-- 指向该文件的硬链接数量。 -/
  numLinks : UInt64

/--
返回指定文件的元数据，并跟随符号链接。若文件不存在或无法访问元数据，则抛出异常。
-/
def c102 := @_root_.System.FilePath.metadata

/--
返回指定文件的元数据，但不跟随符号链接。若文件不存在或无法访问元数据，则抛出异常。
-/
def c103 := @_root_.System.FilePath.symlinkMetadata

/--
检查指定路径是否指向一个存在的文件。此函数会跟随符号链接。
-/
def c104 := @_root_.System.FilePath.pathExists

/--
检查指定路径是否可读取且为目录。此函数会跟随符号链接。
-/
def c105 := @_root_.System.FilePath.isDir

/-- 文件系统中某个目录内的一个条目。 -/
structure c106 where
  /-- 找到该条目的目录。 -/
  root : _root_.System.FilePath
  /-- 该条目的名称。 -/
  fileName : String

/-- 该目录项所指示文件的路径。 -/
def c107 := @_root_.IO.FS.DirEntry.path

/--
返回指定目录的内容。若文件不存在或不是目录，则抛出异常。
-/
def c108 := @_root_.System.FilePath.readDir

/--
从路径 `p` 开始遍历文件系统，并探索满足 `enter` 的目录，返回访问到的路径。

此遍历是前序遍历，即父目录会先于其任何子项出现。符号链接会被跟随。
-/
def c109 := @_root_.System.FilePath.walkDir

/--
POSIX 风格的文件权限。

`FileRight` 结构为文件所有者、其指定组成员以及其他所有人描述这些权限。
-/
structure c110 where
  /-- 该文件可被读取。 -/
  read : Bool := false
  /-- 该文件可被写入。 -/
  write : Bool := false
  /-- 该文件可被执行。 -/
  execution : Bool := false

/--
将各个 POSIX 风格文件权限转换为其传统的三位表示。

它是以下各项按位 `or` 的结果：
* 如果文件可读，则为 `0x4`，否则为 `0`。
* 如果文件可写，则为 `0x2`，否则为 `0`。
* 如果文件可执行，则为 `0x1`，否则为 `0`。

示例：
* `{read := true : AccessRight}.flags = 4`
* `{read := true, write := true : AccessRight}.flags = 6`
* `{read := true, execution := true : AccessRight}.flags = 5`
-/
def c111 := @_root_.IO.AccessRight.flags


end Manual.ZhDocString.IO
