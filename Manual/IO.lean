/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

import Manual.IO.Console
import Manual.IO.Files
import Manual.IO.Threads
import Manual.IO.Ref
import Manual.ZhDocString.IO

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>
%%%
tag := "io"
file := "IO"
%%%



Lean 是一种纯函数式编程语言。
Lean 代码在运行时采用严格求值；然而，类型检查所用的求值顺序——尤其是检查{tech (key := "definitional equality")}[定义相等]时——在形式上并未指定，而是依赖多种可提升性能但可能变化的启发式方法。
这意味着，如果直接加入执行副作用的操作（例如文件 I/O、异常或可变引用），程序中的副作用顺序将无法确定。
类型检查期间，连含有自由变量的项也会被归约；这会使副作用更加难以预测。
最后，Lean 逻辑的一项基本原则是：函数确实是_函数_，即把定义域中的每个元素映射到值域中的唯一元素。
若纳入控制台 I/O、任意可变状态或随机数生成等副作用，就会违反这一原则。

:::::keepEnv
```lean -show
/-- A type -/
axiom α : Type
```

可能产生副作用的程序具有一种类型（通常为 {lean}`IO α`），以便与纯函数区分。
从逻辑上说，{lean}`IO` 描述副作用的先后次序与数据依赖关系。
从 Lean 逻辑的角度看，许多基本副作用（例如读取文件）是不透明常量。
另一些则由逻辑上等价于运行时版本的代码来规定。
在运行时，精译器会生成普通代码。

:::::

# 逻辑模型
%%%
tag := "Logical-Model"
file := "Logical-Model"
%%%

:::::keepEnv
```lean -show
/-- A type -/
axiom α : Type
```
在概念上，Lean 将项的求值或归约与副作用的_执行_区分开来。
项归约由 {tech}[β]、{tech}[δ] 等规则规定，而这些归约随时可能在任意位置发生。
必须按正确顺序执行的副作用，在 Lean 逻辑中以抽象方式描述。
程序运行时，由 Lean 运行时系统负责真正实施所描述的副作用。


类型 {lean}`IO α` 描述一个通过执行副作用而运行的过程；该过程要么返回 {lean}`α` 类型的值，要么抛出错误。
可以把它看作一种以整个世界为状态的{tech (key := "state monad")}[状态单子]。
正如 {lean}`StateM Nat Bool` 类型的值在计算 {lean}`Bool` 的同时能够修改一个自然数，{lean}`IO Bool` 类型的值在计算 {lean}`Bool` 的同时也可能改变世界。
错误处理则通过在其上叠加适当的异常单子变换器来实现。

:::::

由于无法在内存中表示整个世界，实际实现使用一个抽象令牌来代表世界的状态。
程序运行时，Lean 运行时系统负责提供初始令牌；每个原语动作接收一个代表世界的令牌，并在完成后返回另一个令牌。
这既确保副作用按正确顺序发生，也明确区分了副作用的执行与 Lean 项的归约语义。



由一般递归导致的不终止，与 {name}`IO` 所描述的副作用分开处理。
可能因无限循环而不终止的程序必须定义为 {ref "partial-unsafe"}[`partial` 函数]。
从逻辑角度看，它们被视为任意常量，并不需要 {name}`IO`。

{lean}`IO` 的一项非常重要的性质是，其中的值无法“逃逸”。
除非使用少数几个明确标记为不安全的运算符，否则程序无法从 {lean}`IO Nat` 中提取出纯的 {lean}`Nat`。
这既保证了副作用的正确顺序，也保证了带副作用的程序会得到明确标记。

## `IO`、`EIO` 与 `BaseIO` 单子
%%%
tag := "io-monad"
%%%

与现实世界交互的程序通常使用两种单子：

 * {lean}`IO` 中的动作可以抛出 {lean}`IO.Error` 类型的异常，也可以修改世界。
 * {lean}`BaseIO` 中的动作不能抛出异常，但可以修改世界。

这一区分使人们只需查看动作的类型签名，就能判断它是否可能抛出异常。
{lean}`BaseIO` 动作会在需要时自动提升为 {lean}`IO`。

{zhdocstring BaseIO Manual.ZhDocString.IO.c001}

{zhdocstring IO Manual.ZhDocString.IO.c002}

{lean}`IO` 是 {lean}`EIO` 的一个实例，其中错误类型是一个参数。
具体而言，{lean}`IO` 被定义为 {lean}`EIO IO.Error`。
在某些场合（例如绑定非 Lean 库），为 {lean}`EIO` 使用自定义错误类型会很方便；这样可确保错误在这些动作与其他 {lean}`IO` 动作的边界处得到处理。

```lean -show
-- 检查上一段中的论断
example : IO = EIO IO.Error := rfl
```

{zhdocstring EIO Manual.ZhDocString.IO.c003}

{zhdocstring IO.lazyPure Manual.ZhDocString.IO.c004}

{zhdocstring BaseIO.toIO Manual.ZhDocString.IO.c005}

{zhdocstring BaseIO.toEIO Manual.ZhDocString.IO.c006}

{zhdocstring EIO.toBaseIO Manual.ZhDocString.IO.c007}

{zhdocstring EIO.toIO Manual.ZhDocString.IO.c008}

{zhdocstring EIO.toIO' Manual.ZhDocString.IO.c009}

{zhdocstring IO.toEIO Manual.ZhDocString.IO.c010}

## `IO` 中的错误与错误处理
%%%
tag := "io-monad-errors"
%%%

{lean}`IO` 单子使用的错误处理设施与其他{tech (key := "exception monad")}[异常单子]相同。
具体来说，异常的抛出与捕获使用 {name}`MonadExceptOf` {tech (key := "type class")}[类型类]的方法。
{lean}`IO` 中抛出的异常具有 {lean}`IO.Error` 类型。
该类型的构造器表示多数操作系统中会发生的底层错误，例如文件不存在。
最常用的构造器是 {name IO.Error.userError}`userError`；它涵盖其余所有情况，并包含一个描述问题的字符串。

{zhdocstring IO.Error Manual.ZhDocString.IO.c011}

{zhdocstring IO.Error.toString Manual.ZhDocString.IO.c012}

{zhdocstring IO.ofExcept Manual.ZhDocString.IO.c013}

{zhdocstring EIO.catchExceptions Manual.ZhDocString.IO.c014}

{zhdocstring IO.userError Manual.ZhDocString.IO.c015}

::::example "抛出和捕获错误" (file := "Throwing and Catching Errors")
:::ioExample
该程序反复要求输入密码，并使用异常控制流程。
异常所用的语法适用于所有异常单子，而不只适用于 {lean}`IO`。
输入错误密码时，程序会抛出异常；重复密码检查的循环会捕获该异常。
正确的密码会让控制流通过检查并终止循环；其他异常则会被重新抛出。

```ioLean
def accessControl : IO Unit := do
  IO.println "What is the password?"
  let password ← (← IO.getStdin).getLine
  if password.trimAscii.copy != "secret" then
    throw (.userError "Incorrect password")
  else return

def repeatAccessControl : IO Unit := do
  repeat
    try
      accessControl
      break
    catch
      | .userError "Incorrect password" =>
        continue
      | other =>
        throw other

def main : IO Unit := do
  repeatAccessControl
  IO.println "Access granted!"
```

使用以下输入运行时：
```stdin
publicinfo
secondtry
secret
```

程序输出：
```stdout
What is the password?
What is the password?
What is the password?
Access granted!
```
:::
::::

# 控制结构
%%%
tag := "io-monad-control"
file := "Control-Structures"
%%%

通常，使用 {lean}`IO` 编写的程序会使用{ref "monads-and-do"}[与其他单子程序相同的控制结构]。
此外还有一个 {lean}`IO` 专用的辅助函数。

{zhdocstring IO.iterate Manual.ZhDocString.IO.c016}

{include 0 Manual.IO.Console}

{include 0 Manual.IO.Ref}

{include 0 Manual.IO.Files}

# 系统与平台信息
%%%
tag := "platform-info"
file := "System-and-Platform-Information"
%%%

{zhdocstring System.Platform.numBits Manual.ZhDocString.IO.c017}

{zhdocstring System.Platform.target Manual.ZhDocString.IO.c018}

{zhdocstring System.Platform.isWindows Manual.ZhDocString.IO.c019}

{zhdocstring System.Platform.isOSX Manual.ZhDocString.IO.c020}

{zhdocstring System.Platform.isEmscripten Manual.ZhDocString.IO.c021}


# 环境变量
%%%
tag := "io-monad-getenv"
file := "Environment-Variables"
%%%

{zhdocstring IO.getEnv Manual.ZhDocString.IO.c022}

# 计时
%%%
tag := "io-timing"
file := "Timing"
%%%

{zhdocstring IO.sleep Manual.ZhDocString.IO.c023}

{zhdocstring IO.monoNanosNow Manual.ZhDocString.IO.c024}

{zhdocstring IO.monoMsNow Manual.ZhDocString.IO.c025}

{zhdocstring IO.getNumHeartbeats Manual.ZhDocString.IO.c026}

{zhdocstring IO.addHeartbeats Manual.ZhDocString.IO.c027}

# 进程
%%%
tag := "io-processes"
file := "Processes"
%%%

## 当前进程
%%%
tag := "Lean-__________________--IO--Processes--Current-Process"
%%%

{zhdocstring IO.Process.getCurrentDir Manual.ZhDocString.IO.c028}

{zhdocstring IO.Process.setCurrentDir Manual.ZhDocString.IO.c029}

{zhdocstring IO.Process.exit Manual.ZhDocString.IO.c030}

{zhdocstring IO.Process.getPID Manual.ZhDocString.IO.c031}

## 运行进程
%%%
tag := "Lean-__________________--IO--Processes--Running-Processes"
%%%

在 Lean 中运行其他程序主要有三种方式：

 1. {lean}`IO.Process.run` 同步执行另一个程序，并以字符串形式返回其标准输出。若该进程以非 `0` 错误码退出，它会抛出错误。
 2. {lean}`IO.Process.output` 以空标准输入同步执行另一个程序，并捕获其标准输出、标准错误和退出码。即使进程执行失败，也不会抛出错误。
 3. {lean}`IO.Process.spawn` 异步启动另一个程序，并返回一个可访问该进程标准输入流、标准输出流和标准错误流的数据结构。

{zhdocstring IO.Process.run Manual.ZhDocString.IO.c032}

::::example "运行程序" (file := "Running a Program")
运行时，该程序使用 Unix 工具 `cat` 将自身源代码连续拼接两次。

:::ioExample
```ioLean
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```

其输出为：
```stdout
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```
:::
::::

::::example "对文件运行程序" (file := "Running a Program on a File")

该程序使用 Unix 实用工具 `grep` 作为过滤器，查找四位回文数。
它创建一个包含从 {lean}`0` 到 {lean}`9999` 所有数字的文件，随后对该文件调用 `grep`，并从标准输出读取结果。

:::ioExample
```ioLean
def main : IO Unit := do
  -- 向子进程提供输入
  IO.FS.withFile "numbers.txt" .write fun h =>
    for i in [0:10000] do
      h.putStrLn (toString i)

  let palindromes ← IO.Process.run {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#, "numbers.txt"]
  }

  let count := palindromes.trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::


{zhdocstring IO.Process.output Manual.ZhDocString.IO.c033}

::::example "检查退出码" (file := "Checking Exit Codes")
运行时，该程序先对一个不存在的文件调用 `cat`，并显示由此得到的错误码。
然后，它使用 Unix 工具 `cat` 将自身源代码连续拼接两次。

:::ioExample
```ioLean
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
```

其输出为：
```stdout
Exit code from failed process: 1
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here

```
:::
::::


{zhdocstring IO.Process.spawn Manual.ZhDocString.IO.c034}

::::example "异步子进程" (file := "Asynchronous Subprocesses")

该程序使用 Unix 实用工具 `grep` 作为过滤器，查找四位回文数。
它把从 {lean}`0` 到 {lean}`9999` 的所有数字送入 `grep` 进程，然后读取结果。
只有当 `grep` 足够快，且输出管道足以容纳全部 90 个四位回文数时，这段代码才是正确的。

:::ioExample
```ioLean
def main : IO Unit := do
  let grep ← IO.Process.spawn {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
    stdin := .piped,
    stdout := .piped,
    stderr := .null
  }

  -- 向子进程提供输入
  for i in [0:10000] do
    grep.stdin.putStrLn (toString i)

  -- 等待 100ms 让 grep 处理数据，然后读取其输出。
  IO.sleep 100
  let count := (← grep.stdout.readToEnd).trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::

{zhdocstring IO.Process.SpawnArgs Manual.ZhDocString.IO.c035}

{zhdocstring IO.Process.StdioConfig Manual.ZhDocString.IO.c036}

{zhdocstring IO.Process.Stdio Manual.ZhDocString.IO.c037}

{zhdocstring IO.Process.Stdio.toHandleType Manual.ZhDocString.IO.c038}

{zhdocstring IO.Process.Child Manual.ZhDocString.IO.c039}

{zhdocstring IO.Process.Child.wait Manual.ZhDocString.IO.c040}

{zhdocstring IO.Process.Child.tryWait Manual.ZhDocString.IO.c041}

{zhdocstring IO.Process.Child.kill Manual.ZhDocString.IO.c042}

{zhdocstring IO.Process.Child.takeStdin Manual.ZhDocString.IO.c043}

::::example "关闭子进程的标准输入" (file := "Closing a Subprocess's Standard Input")

该程序使用 Unix 实用工具 `grep` 作为过滤器来查找四位回文数，并确保子进程成功终止。
它把从 {lean}`0` 到 {lean}`9999` 的所有数字送入 `grep` 进程，然后关闭该进程的标准输入，使其终止。
检查 `grep` 的退出码后，程序提取其结果。

:::ioExample
```ioLean
def main : IO UInt32 := do
  let grep ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := "grep",
      args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
      stdin := .piped,
      stdout := .piped,
      stderr := .null
    }).takeStdin

    -- 向子进程提供输入
    for i in [0:10000] do
      stdin.putStrLn (toString i)

    -- 返回不含标准输入句柄的子进程。
    -- 这会关闭句柄，因为已不再有
    -- 指向它的引用。
    pure child

  -- 等待 grep 终止
  if (← grep.wait) != 0 then
    IO.eprintln s!"grep terminated unsuccessfully"
    return 1

  -- 读取其输出
  let count := (← grep.stdout.readToEnd).trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
  return 0
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::

{zhdocstring IO.Process.Output Manual.ZhDocString.IO.c044}



# 随机数
%%%
tag := "Random-Numbers"
file := "Random-Numbers"
%%%

{zhdocstring IO.setRandSeed Manual.ZhDocString.IO.c045}

{zhdocstring IO.rand Manual.ZhDocString.IO.c046}

{zhdocstring randBool Manual.ZhDocString.IO.c047}

{zhdocstring randNat Manual.ZhDocString.IO.c048}

## 随机数生成器
%%%
tag := "Lean-__________________--IO--Random-Numbers--Random-Generators"
%%%

{zhdocstring RandomGen Manual.ZhDocString.IO.c049}

{zhdocstring StdGen Manual.ZhDocString.IO.c050 +hideStructureConstructor +hideFields}

{zhdocstring stdRange Manual.ZhDocString.IO.c051}

{zhdocstring stdNext Manual.ZhDocString.IO.c052}

{zhdocstring stdSplit Manual.ZhDocString.IO.c053}

{zhdocstring mkStdGen Manual.ZhDocString.IO.c054}

## 系统随机性
%%%
tag := "Lean-__________________--IO--Random-Numbers--System-Randomness"
%%%

{zhdocstring IO.getRandomBytes Manual.ZhDocString.IO.c055}

{include 0 Manual.IO.Threads}
