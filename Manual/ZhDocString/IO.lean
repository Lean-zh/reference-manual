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

/-- `BaseIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c001 := @_root_.BaseIO

/-- `IO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c002 := @_root_.IO

/-- `EIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c003 := @_root_.EIO

/-- `IO.lazyPure` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c004 := @_root_.IO.lazyPure

/-- `BaseIO.toIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c005 := @_root_.BaseIO.toIO

/-- `BaseIO.toEIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c006 := @_root_.BaseIO.toEIO

/-- `EIO.toBaseIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c007 := @_root_.EIO.toBaseIO

/-- `EIO.toIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c008 := @_root_.EIO.toIO

/-- `EIO.toIO'` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c009 := @_root_.EIO.toIO'

/-- `IO.toEIO` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c010 := @_root_.IO.toEIO

/-- IO 操作可能抛出的错误。各构造子分别描述常见的操作系统错误类别，并保留错误码、路径与说明文字。 -/
inductive c011 where
  /-- 目标已存在。 -/
  | alreadyExists : Option String → UInt32 → String → c011
  /-- 其他系统错误。 -/
  | otherError : UInt32 → String → c011
  /-- 资源正忙。 -/
  | resourceBusy : UInt32 → String → c011
  /-- 资源已消失。 -/
  | resourceVanished : UInt32 → String → c011
  /-- 操作不受支持。 -/
  | unsupportedOperation : UInt32 → String → c011
  /-- 硬件故障。 -/
  | hardwareFault : UInt32 → String → c011
  /-- 约束无法满足。 -/
  | unsatisfiedConstraints : UInt32 → String → c011
  /-- 非法操作。 -/
  | illegalOperation : UInt32 → String → c011
  /-- 协议错误。 -/
  | protocolError : UInt32 → String → c011
  /-- 操作超时。 -/
  | timeExpired : UInt32 → String → c011
  /-- 操作被中断。 -/
  | interrupted : String → UInt32 → String → c011
  /-- 文件或目录不存在。 -/
  | noFileOrDirectory : String → UInt32 → String → c011
  /-- 实参无效。 -/
  | invalidArgument : Option String → UInt32 → String → c011
  /-- 权限不足。 -/
  | permissionDenied : Option String → UInt32 → String → c011
  /-- 资源耗尽。 -/
  | resourceExhausted : Option String → UInt32 → String → c011
  /-- 对象类型不适合该操作。 -/
  | inappropriateType : Option String → UInt32 → String → c011
  /-- 所请求的对象不存在。 -/
  | noSuchThing : Option String → UInt32 → String → c011
  /-- 意外到达输入末尾。 -/
  | unexpectedEof : c011
  /-- 用户产生的错误。 -/
  | userError : String → c011

/-- `IO.Error.toString` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c012 := @_root_.IO.Error.toString

/-- `IO.ofExcept` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c013 := @_root_.IO.ofExcept

/-- `EIO.catchExceptions` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c014 := @_root_.EIO.catchExceptions

/-- `IO.userError` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c015 := @_root_.IO.userError

/-- `IO.iterate` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c016 := @_root_.IO.iterate

/-- `System.Platform.numBits` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c017 := @_root_.System.Platform.numBits

/-- `System.Platform.target` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c018 := @_root_.System.Platform.target

/-- `System.Platform.isWindows` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c019 := @_root_.System.Platform.isWindows

/-- `System.Platform.isOSX` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c020 := @_root_.System.Platform.isOSX

/-- `System.Platform.isEmscripten` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c021 := @_root_.System.Platform.isEmscripten

/-- `IO.getEnv` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c022 := @_root_.IO.getEnv

/-- `IO.sleep` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c023 := @_root_.IO.sleep

/-- `IO.monoNanosNow` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c024 := @_root_.IO.monoNanosNow

/-- `IO.monoMsNow` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c025 := @_root_.IO.monoMsNow

/-- `IO.getNumHeartbeats` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c026 := @_root_.IO.getNumHeartbeats

/-- `IO.addHeartbeats` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c027 := @_root_.IO.addHeartbeats

/-- `IO.Process.getCurrentDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c028 := @_root_.IO.Process.getCurrentDir

/-- `IO.Process.setCurrentDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c029 := @_root_.IO.Process.setCurrentDir

/-- `IO.Process.exit` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c030 := @_root_.IO.Process.exit

/-- `IO.Process.getPID` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c031 := @_root_.IO.Process.getPID

/-- `IO.Process.run` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c032 := @_root_.IO.Process.run

/-- `IO.Process.output` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c033 := @_root_.IO.Process.output

/-- `IO.Process.spawn` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c034 := @_root_.IO.Process.spawn

/-- 子进程的标准输入、输出与错误流配置。 -/
structure StdioConfig where
  /-- 标准输入配置。 -/
  stdin : _root_.IO.Process.Stdio := .inherit
  /-- 标准输出配置。 -/
  stdout : _root_.IO.Process.Stdio := .inherit
  /-- 标准错误配置。 -/
  stderr : _root_.IO.Process.Stdio := .inherit

/-- 启动子进程所需的参数，包括命令、实参、工作目录、环境和标准流配置。 -/
structure c035 extends StdioConfig where
  /-- 要执行的命令。 -/
  cmd : String
  /-- 命令行实参。 -/
  args : Array String := #[]
  /-- 可选工作目录。 -/
  cwd : Option _root_.System.FilePath := none
  /-- 额外环境变量。 -/
  env : Array (String × Option String) := #[]
  /-- 是否继承当前环境。 -/
  inheritEnv : Bool := true
  /-- 是否创建新会话。 -/
  setsid : Bool := false

/-- 子进程三个标准流的配置。 -/
structure c036 where
  /-- 标准输入配置。 -/
  stdin : _root_.IO.Process.Stdio := .inherit
  /-- 标准输出配置。 -/
  stdout : _root_.IO.Process.Stdio := .inherit
  /-- 标准错误配置。 -/
  stderr : _root_.IO.Process.Stdio := .inherit

/-- 子进程标准流的连接方式。 -/
inductive c037 where
  /-- 创建管道。 -/
  | piped
  /-- 继承父进程的流。 -/
  | inherit
  /-- 连接到空设备。 -/
  | null

/-- `IO.Process.Stdio.toHandleType` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c038 := @_root_.IO.Process.Stdio.toHandleType

/-- 已启动的子进程及其可用标准流句柄。 -/
structure c039 (cfg : _root_.IO.Process.StdioConfig) where
  private mk ::
  /-- 子进程标准输入。 -/
  stdin : cfg.stdin.toHandleType
  /-- 子进程标准输出。 -/
  stdout : cfg.stdout.toHandleType
  /-- 子进程标准错误。 -/
  stderr : cfg.stderr.toHandleType

/-- `IO.Process.Child.wait` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c040 := @_root_.IO.Process.Child.wait

/-- `IO.Process.Child.tryWait` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c041 := @_root_.IO.Process.Child.tryWait

/-- `IO.Process.Child.kill` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c042 := @_root_.IO.Process.Child.kill

/-- `IO.Process.Child.takeStdin` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c043 := @_root_.IO.Process.Child.takeStdin

/-- 运行子进程后收集的退出码、标准输出和标准错误。 -/
structure c044 where
  /-- 退出码。 -/
  exitCode : UInt32
  /-- 标准输出文本。 -/
  stdout : String
  /-- 标准错误文本。 -/
  stderr : String

/-- `IO.setRandSeed` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c045 := @_root_.IO.setRandSeed

/-- `IO.rand` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c046 := @_root_.IO.rand

/-- `randBool` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c047 := @_root_.randBool

/-- `randNat` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c048 := @_root_.randNat

/-- 伪随机数生成器接口。 -/
class c049 (g : Type u) where
  /-- 生成器的数值范围。 -/
  range : g → Nat × Nat
  /-- 产生下一个数值和生成器状态。 -/
  next : g → Nat × g
  /-- 将生成器拆分为两个独立状态。 -/
  split : g → g × g

/-- 标准伪随机数生成器的状态。 -/
structure c050 where
  /-- 第一个内部种子。 -/
  s1 : Nat
  /-- 第二个内部种子。 -/
  s2 : Nat

/-- `stdRange` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c051 := @_root_.stdRange

/-- `stdNext` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c052 := @_root_.stdNext

/-- `stdSplit` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c053 := @_root_.stdSplit

/-- `mkStdGen` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c054 := @_root_.mkStdGen

/-- `IO.getRandomBytes` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c055 := @_root_.IO.getRandomBytes

/-- `IO.print` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c056 := @_root_.IO.print

/-- `IO.println` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c057 := @_root_.IO.println

/-- `IO.eprint` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c058 := @_root_.IO.eprint

/-- `IO.eprintln` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c059 := @_root_.IO.eprintln

/-- `IO.FS.Handle` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c060 := @_root_.IO.FS.Handle

/-- `IO.FS.Handle.mk` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c061 := @_root_.IO.FS.Handle.mk

/-- 打开文件时使用的模式。 -/
inductive c062 where
  /-- 只读。 -/
  | read
  /-- 写入并截断。 -/
  | write
  /-- 仅在新建文件时写入。 -/
  | writeNew
  /-- 读写。 -/
  | readWrite
  /-- 追加写入。 -/
  | append

/-- `IO.FS.Handle.read` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c063 := @_root_.IO.FS.Handle.read

/-- `IO.FS.Handle.readToEnd` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c064 := @_root_.IO.FS.Handle.readToEnd

/-- `IO.FS.Handle.readBinToEnd` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c065 := @_root_.IO.FS.Handle.readBinToEnd

/-- `IO.FS.Handle.readBinToEndInto` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c066 := @_root_.IO.FS.Handle.readBinToEndInto

/-- `IO.FS.Handle.getLine` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c067 := @_root_.IO.FS.Handle.getLine

/-- `IO.FS.Handle.write` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c068 := @_root_.IO.FS.Handle.write

/-- `IO.FS.Handle.putStr` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c069 := @_root_.IO.FS.Handle.putStr

/-- `IO.FS.Handle.putStrLn` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c070 := @_root_.IO.FS.Handle.putStrLn

/-- `IO.FS.Handle.flush` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c071 := @_root_.IO.FS.Handle.flush

/-- `IO.FS.Handle.rewind` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c072 := @_root_.IO.FS.Handle.rewind

/-- `IO.FS.Handle.truncate` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c073 := @_root_.IO.FS.Handle.truncate

/-- `IO.FS.Handle.isTty` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c074 := @_root_.IO.FS.Handle.isTty

/-- `IO.FS.Handle.lock` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c075 := @_root_.IO.FS.Handle.lock

/-- `IO.FS.Handle.tryLock` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c076 := @_root_.IO.FS.Handle.tryLock

/-- `IO.FS.Handle.unlock` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c077 := @_root_.IO.FS.Handle.unlock

/-- 字节与文本流，由读取、写入、刷新等 IO 操作组成。 -/
structure c078 where
  /-- 刷新缓冲区。 -/
  flush : _root_.IO Unit
  /-- 读取指定数量的字节。 -/
  read : USize → _root_.IO ByteArray
  /-- 写入字节。 -/
  write : ByteArray → _root_.IO Unit
  /-- 读取一行。 -/
  getLine : _root_.IO String
  /-- 写入字符串。 -/
  putStr : String → _root_.IO Unit
  /-- 判断流是否连接到终端。 -/
  isTty : _root_.BaseIO Bool

/-- `IO.FS.Stream.ofBuffer` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c079 := @_root_.IO.FS.Stream.ofBuffer

/-- `IO.FS.Stream.ofHandle` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c080 := @_root_.IO.FS.Stream.ofHandle

/-- `IO.FS.Stream.putStrLn` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c081 := @_root_.IO.FS.Stream.putStrLn

/-- 流读取操作使用的字节缓冲区及当前位置。 -/
structure c082 where
  /-- 缓冲区内容。 -/
  data : ByteArray := ByteArray.empty
  /-- 当前偏移。 -/
  pos : Nat := 0

/-- 文件系统路径。 -/
structure c083 where
  /-- 路径的字符串表示。 -/
  toString : String

/-- `System.mkFilePath` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c084 := @_root_.System.mkFilePath

/-- `System.FilePath.join` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c085 := @_root_.System.FilePath.join

/-- `System.FilePath.normalize` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c086 := @_root_.System.FilePath.normalize

/-- `System.FilePath.isAbsolute` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c087 := @_root_.System.FilePath.isAbsolute

/-- `System.FilePath.isRelative` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c088 := @_root_.System.FilePath.isRelative

/-- `System.FilePath.parent` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c089 := @_root_.System.FilePath.parent

/-- `System.FilePath.components` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c090 := @_root_.System.FilePath.components

/-- `System.FilePath.fileName` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c091 := @_root_.System.FilePath.fileName

/-- `System.FilePath.fileStem` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c092 := @_root_.System.FilePath.fileStem

/-- `System.FilePath.extension` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c093 := @_root_.System.FilePath.extension

/-- `System.FilePath.addExtension` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c094 := @_root_.System.FilePath.addExtension

/-- `System.FilePath.withExtension` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c095 := @_root_.System.FilePath.withExtension

/-- `System.FilePath.withFileName` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c096 := @_root_.System.FilePath.withFileName

/-- `System.FilePath.pathSeparator` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c097 := @_root_.System.FilePath.pathSeparator

/-- `System.FilePath.pathSeparators` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c098 := @_root_.System.FilePath.pathSeparators

/-- `System.FilePath.extSeparator` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c099 := @_root_.System.FilePath.extSeparator

/-- `System.FilePath.exeExtension` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c100 := @_root_.System.FilePath.exeExtension

/-- 文件系统对象的元数据。 -/
structure c101 where
  /-- 最近访问时间。 -/
  accessed : _root_.IO.FS.SystemTime
  /-- 最近修改时间。 -/
  modified : _root_.IO.FS.SystemTime
  /-- 字节大小。 -/
  byteSize : UInt64
  /-- 文件类型。 -/
  type : _root_.IO.FS.FileType
  /-- 硬链接数量。 -/
  numLinks : UInt64

/-- `System.FilePath.metadata` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c102 := @_root_.System.FilePath.metadata

/-- `System.FilePath.symlinkMetadata` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c103 := @_root_.System.FilePath.symlinkMetadata

/-- `System.FilePath.pathExists` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c104 := @_root_.System.FilePath.pathExists

/-- `System.FilePath.isDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c105 := @_root_.System.FilePath.isDir

/-- 目录中的一个条目。 -/
structure c106 where
  /-- 所属目录。 -/
  root : _root_.System.FilePath
  /-- 条目的文件名。 -/
  fileName : String

/-- `IO.FS.DirEntry.path` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c107 := @_root_.IO.FS.DirEntry.path

/-- `System.FilePath.readDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c108 := @_root_.System.FilePath.readDir

/-- `System.FilePath.walkDir` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c109 := @_root_.System.FilePath.walkDir

/-- 一组读取、写入和执行访问权限。 -/
structure c110 where
  /-- 可读。 -/
  read : Bool := false
  /-- 可写。 -/
  write : Bool := false
  /-- 可执行。 -/
  execution : Bool := false

/-- `IO.AccessRight.flags` 的中文动态文档载体。它保持原声明的类型与行为，并用于展示该 API 的中文说明。 -/
def c111 := @_root_.IO.AccessRight.flags

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
