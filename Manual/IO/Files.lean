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

#doc (Manual) "文件、文件句柄与流" =>
%%%
tag := "Files___-File-Handles___-and-Streams"
file := "Files, File Handles, and Streams"
%%%

Lean 在所有受支持的平台上提供一致的文件系统 API。
其中的关键概念如下：

: {deftech (key := "Files")}[文件]

  文件是操作系统提供的一种抽象，它支持随机访问持久存储的数据；这些数据按目录组成层级结构。

: {deftech (key := "Directories")}[目录]

  目录也称为_文件夹_，其中可以包含文件或其他目录。
  从根本上说，目录把名称映射到其中包含的文件和／或目录。

: {deftech (key := "File Handles")}[文件句柄]

  文件句柄（{name IO.FS.Handle}`Handle`）是对已打开以供读取和／或写入的文件的抽象引用。
  文件句柄维护一种模式，用来确定是否允许读取和／或写入；它还维护一个指向文件中特定位置的游标。
  通过文件句柄读取或写入都会推进该游标。
  文件句柄可以是{deftech (key := "buffered")}[带缓冲的]；这意味着通过文件句柄读取时，可能不会返回持久数据的当前内容，而写入时也可能不会立即修改这些内容。

: 路径

  文件主要通过{deftech (key := "paths")}_路径_（{name}`System.FilePath`）来访问。
  路径是一个目录名序列，末尾也可能是文件名。
  路径由字符串表示，其中的分隔符字符{margin}[当前平台的分隔符字符列于 {name}`System.FilePath.pathSeparators`。]用于分隔各个名称。

  路径的具体细节因平台而异。
  {deftech (key := "Absolute paths")}[绝对路径]始于{deftech (key := "root directory")}_根目录_；有些操作系统只有一个根目录，另一些则可能有多个根目录。
  相对路径不以根目录开头，需要把另一个目录作为起点。
  除普通目录外，路径还可以包含特殊目录名 `.` 和 `..`：前者指其所在目录，后者指路径中的上一级目录。

  文件名乃至路径可以一个或多个标识文件类型的{deftech (key := "extensions")}_扩展名_结尾。
  扩展名由字符 {name}`System.FilePath.extSeparator` 分隔。
  在某些平台上，可执行文件具有特殊扩展名（{name}`System.FilePath.exeExtension`）。

: {deftech (key := "Streams")}[流]

  流是文件之上的高层抽象，既提供额外功能，也隐藏文件的一些细节。
  {tech (key := "file handles")}[文件句柄]本质上只是对操作系统表示的薄封装，而流则在 Lean 中实现为名为 {lean}`IO.FS.Stream` 的结构。
  由于流在 Lean 中实现，用户代码可以创建额外的流，并与标准库提供的流无缝配合使用。

# 底层文件 API
%%%
tag := "Lean-__________________--IO--Files___-File-Handles___-and-Streams--Low-Level-File-API"
%%%

在最底层，文件通过 {name IO.FS.Handle.mk}`Handle.mk` 显式打开。
当句柄对象的最后一个引用被丢弃时，文件随即关闭。
除了确保文件句柄不再有任何引用外，没有其他显式关闭句柄的方法。


{docstring IO.FS.Handle}

{docstring IO.FS.Handle.mk}

{docstring IO.FS.Mode}

{docstring IO.FS.Handle.read}

{docstring IO.FS.Handle.readToEnd}

{docstring IO.FS.Handle.readBinToEnd}

{docstring IO.FS.Handle.readBinToEndInto}

{docstring IO.FS.Handle.getLine}

{docstring IO.FS.Handle.write}

{docstring IO.FS.Handle.putStr}

{docstring IO.FS.Handle.putStrLn}

{docstring IO.FS.Handle.flush}

{docstring IO.FS.Handle.rewind}

{docstring IO.FS.Handle.truncate}

{docstring IO.FS.Handle.isTty}

{docstring IO.FS.Handle.lock}

{docstring IO.FS.Handle.tryLock}

{docstring IO.FS.Handle.unlock}


::::example "一个文件，多个句柄" (file := "One File, Multiple Handles")
该程序持有同一文件的两个句柄。
由于每个句柄的文件 I/O 可能独立缓冲，需要让缓冲区与文件实际内容同步时，应调用 {name IO.FS.Handle.flush}`Handle.flush`。
这里，两个句柄步调一致地遍历文件，其中一个始终比另一个领先一个字节。
第一个句柄用于统计 `'A'` 的出现次数，第二个则用于把每个 `'A'` 替换为 `'!'`。
第二个句柄以 {name IO.FS.Mode.readWrite}`readWrite` 模式而非 {name IO.FS.Mode.write}`write` 模式打开，因为以 {name IO.FS.Mode.write}`write` 模式打开现有文件会用空文件替换它。
在此例中，修改只发生在不会再被读取的文件区域，因此执行期间无须刷新缓冲区；但循环结束后应刷新写句柄。

:::ioExample
```ioLean
open IO.FS (Handle)

def main : IO Unit := do
  IO.println s!"Starting contents: '{(← IO.FS.readFile "data").trimAscii}'"

  let h ← Handle.mk "data" .read
  let h' ← Handle.mk "data" .readWrite
  h'.rewind

  let mut count := 0
  let mut buf : ByteArray ← h.read 1
  while ok : buf.size = 1 do
    if Char.ofUInt8 buf[0] == 'A' then
      count := count + 1
      h'.write (ByteArray.empty.push '!'.toUInt8)
    else
      h'.write buf
    buf ← h.read 1

  h'.flush

  IO.println s!"Count: {count}"
  IO.println s!"Contents: '{(← IO.FS.readFile "data").trimAscii}'"
```

以该文件为输入运行时：
```inputFile "data"
AABAABCDAB
```

程序输出：
```stdout
Starting contents: 'AABAABCDAB'
Count: 5
Contents: '!!B!!BCD!B'
```
```stderr -show
```

此后，文件内容为：
```outputFile "data"
!!B!!BCD!B
```

:::
::::

# 流
%%%
tag := "Lean-__________________--IO--Files___-File-Handles___-and-Streams--Streams"
%%%

{docstring IO.FS.Stream}

{docstring IO.FS.Stream.ofBuffer}

{docstring IO.FS.Stream.ofHandle}

{docstring IO.FS.Stream.putStrLn}

{docstring IO.FS.Stream.Buffer}


# 路径
%%%
tag := "Lean-__________________--IO--Files___-File-Handles___-and-Streams--Paths"
%%%

路径由字符串表示。
不同平台采用不同的路径约定：有些使用斜杠（`/`）作为目录分隔符，另一些使用反斜杠（`\`）。
有些平台区分大小写，另一些则不区分。
文件名可能采用不同的 Unicode 编码与规范化形式表示；有些平台还把文件名视为字节序列而非字符串。
在一个系统上表示{tech (key := "absolute path")}[绝对路径]的字符串，在另一个系统上甚至可能不是有效路径。

为了编写尽可能兼容多个系统的 Lean 代码，最好使用 Lean 的路径操作原语，而不是直接操作字符串。
{name}`System.FilePath.join` 等辅助函数会考虑平台特有的绝对路径规则；{name}`System.FilePath.pathSeparator` 包含当前平台适用的路径分隔符；{name}`System.FilePath.exeExtension` 则包含可执行文件所需的扩展名。
请勿硬编码这些规则。

{name System.FilePath}`FilePath` 具有 {lean}`Div` 类型类的实例，因此可以使用斜杠运算符拼接路径。

{docstring System.FilePath +allowMissing}

{docstring System.mkFilePath}

{docstring System.FilePath.join}

{docstring System.FilePath.normalize}

{docstring System.FilePath.isAbsolute}

{docstring System.FilePath.isRelative}

{docstring System.FilePath.parent}

{docstring System.FilePath.components}

{docstring System.FilePath.fileName}

{docstring System.FilePath.fileStem}

{docstring System.FilePath.extension}

{docstring System.FilePath.addExtension}

{docstring System.FilePath.withExtension}

{docstring System.FilePath.withFileName}

{docstring System.FilePath.pathSeparator}

{docstring System.FilePath.pathSeparators}

{docstring System.FilePath.extSeparator}

{docstring System.FilePath.exeExtension}

# 与文件系统交互
%%%
tag := "Lean-__________________--IO--Files___-File-Handles___-and-Streams--Interacting-with-the-Filesystem"
%%%

有些路径操作会查询文件系统。

{docstring IO.FS.Metadata}

{docstring System.FilePath.metadata}

{docstring System.FilePath.symlinkMetadata}

{docstring System.FilePath.pathExists}

{docstring System.FilePath.isDir}

{docstring IO.FS.DirEntry}

{docstring IO.FS.DirEntry.path}

{docstring System.FilePath.readDir}

{docstring System.FilePath.walkDir}

{docstring IO.AccessRight +allowMissing}

{docstring IO.AccessRight.flags}

{docstring IO.FileRight}

{docstring IO.FileRight.flags}

{docstring IO.setAccessRights}

{docstring IO.FS.removeFile}

{docstring IO.FS.rename}

{docstring IO.FS.removeDir}

{docstring IO.FS.lines}

{docstring IO.FS.withTempFile}

{docstring IO.FS.withTempDir}

{docstring IO.FS.createDirAll}

{docstring IO.FS.writeBinFile}

{docstring IO.FS.withFile}

{docstring IO.FS.removeDirAll}

{docstring IO.FS.createTempFile}

{docstring IO.FS.createTempDir}

{docstring IO.FS.readFile}

{docstring IO.FS.realPath}

{docstring IO.FS.writeFile}

{docstring IO.FS.readBinFile}

{docstring IO.FS.createDir}

# 标准 I/O
%%%
tag := "stdio"
%%%

在源自 Unix 或受其启发的操作系统中，{deftech (key := "standard input")}_标准输入_、{deftech (key := "standard output")}_标准输出_和{deftech (key := "standard error")}_标准错误_是每个进程中可用的三个流的名称。
通常，程序应从标准输入读取数据，把普通输出写入标准输出，并把错误消息写入标准错误。
默认情况下，标准输入从控制台接收输入，而标准输出和标准错误向控制台输出；不过，这三个流经常被重定向到管道或文件，或从中读取。

Lean 并不直接提供对操作系统标准 I/O 设施的访问，而是用 {name IO.FS.Stream}`Stream` 对其加以封装。
此外，{lean}`IO` 单子还特别支持替换或局部覆盖这些流。
这一额外的间接层使 Lean 程序能够在内部重定向输入与输出。


{docstring IO.getStdin}

::::example "从标准输入读取" (file := "Reading from Standard Input")
本例分别使用 {lean}`IO.getStdin` 和 {lean}`IO.getStdout` 获取当前的标准输入与标准输出。
可以从前者读取，也可以向后者写入。

:::ioExample
```ioLean
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "Who is it?"
  let name ← stdin.getLine
  stdout.putStr "Hello, "
  stdout.putStrLn name
```

给定以下标准输入：
```stdin
Lean user
```
标准输出为：
```stdout
Who is it?
Hello, Lean user
```
:::
::::

{docstring IO.setStdin}

{docstring IO.withStdin}

{docstring IO.getStdout}

{docstring IO.setStdout}

{docstring IO.withStdout}

{docstring IO.getStderr}

{docstring IO.setStderr}

{docstring IO.withStderr}

{docstring IO.FS.withIsolatedStreams}

::::keepEnv
:::example "将标准 I/O 重定向到字符串" (file := "Redirecting Standard I/O to Strings")
{lean}`countdown` 函数从指定数字开始倒数，并把进度写入标准输出。
使用 `IO.FS.withIsolatedStreams` 可将该输出重定向到字符串。

```lean (name := countdown)
def countdown : Nat → IO Unit
  | 0 =>
    IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown
```

运行 {lean}`countdown` 会得到一个包含输出的字符串：
```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
```
:::
::::

# 文件与目录
%%%
tag := "Lean-__________________--IO--Files___-File-Handles___-and-Streams--Files-and-Directories"
%%%

{docstring IO.currentDir}

{docstring IO.appPath}

{docstring IO.appDir}
