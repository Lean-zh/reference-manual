/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Meta.ElanCheck
import Manual.Meta.ElanCmd
import Manual.Meta.ElanOpt

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "使用 Elan 管理工具链" =>
%%%
tag := "elan"
shortContextTitle := "Elan"
%%%

Elan 是 Lean 工具链管理器。
它既负责安装{tech (key := "toolchains")}[工具链]，也负责运行工具链中的程序。
借助 Elan，可以无缝处理各种项目；每个项目都针对特定 Lean 版本进行构建，而无需手动安装和选择工具链版本。
每个项目通常配置为使用某个特定版本；该版本会按需透明地安装，而 Lean 版本的变更会自动受到跟踪。

# 选择工具链
%%%
tag := "elan-toolchain-versions"
%%%

使用 Elan 时，{envVar}`PATH` 中每个工具的版本都是一个调用正确版本的代理。
代理会为当前上下文确定适当的工具链版本，确保该版本已安装，然后调用相应工具链安装中的底层工具。
可以传入以 `+` 为前缀的参数，指示这些代理使用特定版本；因此 `lake +4.0.0` 会调用 `4.0.0` 版的 `lake`，必要时先安装它。


## 工具链标识符
%%%
tag := "elan-channels"
%%%

工具链通过工具链标识符指定；标识符可以是标识某类 Lean 发行版并可选带有来源的{deftech (key := "channel")}[通道]，也可以是由 {elan}`toolchain link` 建立的{deftech (key := "custom toolchain name")}[自定义工具链名称]。
通道可以是：

 : `stable`

  最新的 Lean 稳定发行版。Elan 会自动跟踪稳定发行版，并在新版本发布时提示升级。

 : `beta`

  最新的候选发行版。候选发行版是计划成为下一个稳定发行版的 Lean 构建，供广大用户测试。

 : `nightly`

   最新的每夜构建。每夜构建适合试用 Lean 的新功能并向开发者提供反馈。

 : 版本号或特定的每夜发行版

    每个 Lean 版本号都标识一个仅包含该发行版的通道。
    版本号前可以带有 `v`，因此 `v4.17.0` 与 `4.17.0` 等价。
    类似地，`nightly-YYYY-MM-DD` 指定相应日期的每夜发行版。
    项目的{tech (key := "toolchain file")}[工具链文件]通常应包含具体的 Lean 版本，而不是宽泛的通道，以便开发者相互协调，并构建和测试项目的旧版本。
    Lean 发行版和每夜构建有一份持续维护的归档。

 : 自定义本地工具链

    可以使用 {elan}`toolchain link` 命令，在 Elan 中为 Lean 的本地构建建立自定义工具链名称。
    这在开发 Lean 编译器本身时尤其有用。

指定{deftech (key := "origin")}[来源]会指示 Elan 从特定源安装 Lean 工具链。
默认情况下，这是 GitHub 上标识为 [`leanprover/lean4`](https://github.com/leanprover/lean4/releases) 的官方项目仓库。
如果指定来源，它应位于通道之前，并用冒号分隔，因此 `stable` 等价于 `leanprover/lean4:stable`。
安装每夜发行版时，会向来源追加 `-nightly`，因此 `leanprover/lean4:nightly-2025-03-25` 会查询 [`leanprover/lean4-nightly`](https://github.com/leanprover/lean4-nightly/releases) 仓库以下载发行版。
自定义工具链名称不使用来源。

## 确定当前工具链
%%%
tag := "elan-toolchain-config"
%%%

Elan 将工具链与目录关联，并使用当前工作目录向上最近的、已配置工具链的父目录所对应的工具链。
目录的工具链可能来自工具链文件，也可能来自使用 {ref "elan-override"}[`elan override`] 配置的覆盖项。

确定当前工具链时，首先查找为当前目录配置的工具链，然后逐级向上检查父目录，直到找到工具链版本或不再有父目录。
若某目录配置了{tech (key := "toolchain override")}[工具链覆盖项]，或包含 `lean-toolchain` 文件，则该目录已配置工具链。
较近的父目录优先于其祖先目录；如果一个目录同时有覆盖项和工具链文件，则覆盖项优先。
如果没有找到目录工具链，则以 Elan 配置的{deftech (key := "default toolchain")}[默认工具链]作为后备。

配置 Lean 工具链最常见的方式是使用{deftech (key := "toolchain file")}[工具链文件]。
工具链文件是名为 `lean-toolchain` 的文本文件，其中只有一行有效的{ref "elan-channels"}[工具链标识符]。
该文件通常位于项目根目录，并与代码一同纳入版本控制，确保项目的所有开发者使用相同版本。
更新到新的 Lean 工具链只需编辑此文件；下次打开或构建 Lean 文件时，新版本便会自动下载并运行。

在某些需要更大灵活性的高级用例中，可以配置{deftech (key := "toolchain override")}[工具链覆盖项]。
与工具链文件一样，覆盖项将工具链版本与某个目录及其子目录关联。
与工具链文件不同，覆盖项存储在 Elan 的配置中，而不是本地文件中。
它们通常用于需要不适合其他开发者的特定本地配置时，例如使用本地构建的 Lean 编译器测试项目。

# 工具链位置
%%%
tag := "elan-dir"
%%%

默认情况下，Elan 将已安装的工具链存储在用户主目录的 `.elan/toolchains` 中，其代理则保存在 `.elan/bin` 中；安装 Elan 时会将后者添加到路径。
可以使用环境变量 {envVar +def}`ELAN_HOME` 更改此位置。
为确保能找到 Elan 的文件，应在安装 Elan 之前以及所有使用 Lean 的会话中设置它。

# 命令行界面
%%%
tag := "elan-cli"
%%%

除了自动选择、安装并调用正确版本 Lean 工具的代理外，Elan 还提供用于查询和配置其设置的命令行界面。
该工具名为 `elan`。
与 {ref "lake"}[Lake] 类似，其命令行界面围绕子命令组织。

调用 Elan 时可以使用以下标志：

 : {elanOptDef flag}`--help` or {elanOptDef flag}`-h`

  详细说明当前子命令。

 : {elanOptDef flag}`--verbose` or {elanOptDef flag}`-v`

  启用详细输出。

 : {elanOptDef flag}`--version` or {elanOptDef flag}`-V`

  显示 Elan 版本。



```elanHelp
The Lean toolchain installer

USAGE:
    elan [FLAGS] <SUBCOMMAND>

FLAGS:
    -v, --verbose    Enable verbose output
    -h, --help       Prints help information
    -V, --version    Prints version information

SUBCOMMANDS:
    show           Show the active and installed toolchains
    default        Set the default toolchain
    toolchain      Modify or query the installed toolchains
    override       Modify directory toolchain overrides
    run            Run a command with an environment configured for a given toolchain
    which          Display which binary will be run for a given command
    self           Modify the elan installation
    completions    Generate completion scripts for your shell
    help           Prints this message or the help of the given subcommand(s)

DISCUSSION:
    elan manages your installations of the Lean theorem prover.
    It places `lean` and `lake` binaries in your `PATH` that automatically
    select and, if necessary, download the Lean version described in your
    project's `lean-toolchain` file. You can also install, select, run,
    and uninstall Lean versions manually using the commands of the `elan`
    executable.
```

## 查询工具链
%%%
tag := "elan-show"
%%%

{elan}`show` 命令显示当前工具链（由当前目录确定），并列出所有已安装的工具链。


```elanHelp "show"
elan-show
Show the active and installed toolchains

USAGE:
    elan show

FLAGS:
    -h, --help    Prints help information

DISCUSSION:
    Shows the name of the active toolchain and the version of `lean`.

    If there are multiple toolchains installed then all installed
    toolchains are listed as well.
```

:::elan show
显示活动工具链的名称和 `lean` 的版本。

如果安装了多个工具链，则会全部列出。
:::

下面是在含有 `lean-toolchain` 文件的项目中运行 {elan}`show` 的典型输出：
```
installed toolchains
--------------------

leanprover/lean4:nightly-2025-03-25
leanprover/lean4:v4.17.0  (resolved from default 'stable')
leanprover/lean4:v4.16.0
leanprover/lean4:v4.9.0

active toolchain
----------------

leanprover/lean4:v4.9.0 (overridden by '/PATH/TO/PROJECT/lean-toolchain')
Lean (version 4.9.0, arm64-apple-darwin23.5.0, commit 8f9843a4a5fe, Release)
```
`installed toolchains` 一节列出系统上当前可用的所有工具链。
`active toolchain` 一节标识当前工具链，并说明其选择方式。
在此例中，工具链是根据 `lean-toolchain` 文件选择的。


## 设置默认工具链
%%%
tag := "elan-default"
%%%

Elan 的配置文件指定一个{tech (key := "default toolchain")}[默认工具链]，在当前目录没有 `lean-toolchain` 文件或{tech (key := "toolchain override")}[工具链覆盖项]时使用。
通常使用 {elan}`default` 命令更改此值，而不是手动编辑该文件。

```elanHelp "default"
elan-default
Set the default toolchain

USAGE:
    elan default <toolchain>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                   help toolchain`

DISCUSSION:
    Sets the default toolchain to the one specified.
```

:::elan default "toolchain"
将默认工具链设置为 {elanMeta}`toolchain`；它应是{ref "elan-channels"}[有效的工具链标识符]，例如 `stable`、`nightly` 或 `4.17.0`。
:::

## 管理已安装的工具链
%%%
tag := "elan-toolchain"
%%%

`elan toolchain` 子命令族用于管理已安装的工具链。
工具链存储在 Elan 的{ref "elan-dir"}[工具链目录]中。

已安装的工具链可能占用大量磁盘空间。
Elan 会跟踪曾在其中调用过它的 Lean 项目，并保存一份列表。
这份项目列表可用于确定哪些工具链正在使用，并通过 {elan}`toolchain gc` 自动删除未使用的工具链版本。

```elanHelp "toolchain"
elan-toolchain
Modify or query the installed toolchains

USAGE:
    elan toolchain <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list         List installed toolchains
    install      Install a given toolchain
    uninstall    Uninstall a toolchain
    link         Create a custom toolchain by symlinking to a directory
    gc           Garbage-collect toolchains not used by any known project
    help         Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Many `elan` commands deal with *toolchains*, a single
    installation of the Lean theorem prover. `elan` supports multiple
    types of toolchains. The most basic track the official release
    channels: 'stable', 'beta', and 'nightly'; but `elan` can also
    install toolchains from the official archives and from local builds.

    Standard release channel toolchain names have the following form:

        [<origin>:]<channel>[-<date>]

        <channel>       = stable|beta|nightly|<version>
        <date>          = YYYY-MM-DD

    'channel' is either a named release channel or an explicit version
    number, such as '4.0.0'. Channel names can be optionally appended
    with an archive date, as in 'nightly-2023-06-27', in which case
    the toolchain is downloaded from the archive for that date.
    'origin' can be used to refer to custom forks of Lean on Github;
    the default is 'leanprover/lean4'. For nightly versions, '-nightly'
    is appended to the value of 'origin'.

    elan can also manage symlinked local toolchain builds, which are
    often used to for developing Lean itself. For more information see
    `elan toolchain help link`.
```

```elanHelp "toolchain" "list"
elan-toolchain-list
List installed toolchains

USAGE:
    elan toolchain list

FLAGS:
    -h, --help    Prints help information
```

:::elan toolchain list
列出当前已安装的工具链。这是 {elan}`show` 输出的一个子集。
:::

```elanHelp "toolchain" "install"
elan-toolchain-install
Install a given toolchain

USAGE:
    elan toolchain install <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see
                      `elan help toolchain`
```

:::elan toolchain install "toolchain"
安装指定的 {elanMeta}`toolchain`。
工具链名称应是{ref "elan-channels"}[适合写入 `lean-toolchain` 文件的标识符]。
:::


```elanHelp "toolchain" "uninstall"
elan-toolchain-uninstall
Uninstall a toolchain

USAGE:
    elan toolchain uninstall <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see
                      `elan help toolchain`
```

:::elan toolchain uninstall "toolchain"
卸载指定的 {elanMeta}`toolchain`。
工具链名称应为某个已安装工具链的名称。
使用 {elan}`toolchain list` 查看已安装工具链及其名称。
:::

```elanHelp "toolchain" "link"
elan-toolchain-link
Create a custom toolchain by symlinking to a directory

USAGE:
    elan toolchain link <toolchain> <path>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                   help toolchain`
    <path>

DISCUSSION:
    'toolchain' is the custom name to be assigned to the new toolchain.

    'path' specifies the directory where the binaries and libraries for
    the custom toolchain can be found. For example, when used for
    development of Lean itself, toolchains can be linked directly out of
    the Lean root directory. After building, you can test out different
    compiler versions as follows:

        $ elan toolchain link master <path/to/lean/root>
        $ elan override set master

    If you now compile a package in the current directory, the custom
    toolchain 'master' will be used.
```


:::elan toolchain link "«local-name» path"

使用在 {elanMeta}`path` 处找到的 Lean 工具链，创建名为 {elanMeta}`local-name` 的新本地工具链。

:::


```elanHelp "toolchain" "gc"
elan-toolchain-gc
Garbage-collect toolchains not used by any known project

USAGE:
    elan toolchain gc [FLAGS]

FLAGS:
        --delete    Delete collected toolchains instead of only reporting them
    -h, --help      Prints help information
        --json      Format output as JSON

DISCUSSION:
    Experimental. A toolchain is classified as 'in use' if
    * it is the default toolchain,
    * it is registered as an override, or
    * there is a directory with a `lean-toolchain` file referencing the
      toolchain and elan has been used in the directory before.

    For safety reasons, the command currently requires passing `--delete`
    to actually remove toolchains but this may be relaxed in the future
    when the implementation is deemed stable.
```

:::elan toolchain gc "[\"--delete\"] [\"--json\"]"

此命令目前仍被视为实验性命令。

确定已安装工具链中哪些正在使用，并提议删除未使用的工具链。
所有已安装的工具链都会列出，并分成正在使用和未使用两类。

如果满足以下条件，工具链会被归类为“正在使用”：
 * 它是默认工具链；
 * 它被注册为覆盖项；或者
 * 某目录的 `lean-toolchain` 文件引用了该工具链，并且此前曾在该目录中使用过 elan。

出于安全考虑，除非传入 {elanOptDef flag}`--delete` 标志，否则 {elan}`toolchain gc` 不会实际删除任何工具链。
将来当实现被认为足够成熟时，可能会放宽这一要求。
{elanOptDef flag}`--json` 标志使 {elan}`toolchain gc` 以适合其他工具处理的 JSON 格式输出已使用和未使用工具链的列表。
:::

## 管理目录覆盖项
%%%
tag := "elan-override"
%%%

目录专属的{tech (key := "toolchain overrides")}[工具链覆盖项]是一种优先于 `lean-toolchain` 文件的本地配置。
`elan override` 命令用于管理覆盖项。

```elanHelp "override"
elan-override
Modify directory toolchain overrides

USAGE:
    elan override <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list     List directory toolchain overrides
    set      Set the override toolchain for a directory
    unset    Remove the override toolchain for a directory
    help     Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Overrides configure elan to use a specific toolchain when
    running in a specific directory.

    elan will automatically select the Lean toolchain specified in
    the `lean-toolchain` file when inside a Lean package, but
    directories can also be assigned their own Lean toolchain manually
    with `elan override`. When a directory has an override then any
    time `lean` or `lake` is run inside that directory, or one of
    its child directories, the override toolchain will be invoked.

    To pin to a specific nightly:

        $ elan override set nightly-2023-09-06

    Or a specific stable release:

        $ elan override set 4.0.0

    To see the active toolchain use `elan show`. To remove the
    override and use the default toolchain again, `elan override
    unset`.
```



:::elan override list
以两列列出当前配置的所有目录覆盖项。
左列包含 Lean 版本被覆盖的目录，右列列出工具链版本。
:::


:::elan override set "toolchain"
将 {elanMeta}`toolchain` 设置为当前目录的覆盖项。
:::




:::elan override unset "[\"--nonexistent\"] [\"--path\" path]"
如果提供 {elanOptDef flag}`--nonexistent` 标志，则移除为当前不存在的目录配置的所有覆盖项。
如果提供 {elanOptDef option}`--path`，则移除为 {elanMeta}`path` 设置的覆盖项。
否则，移除当前目录的覆盖项。
:::

## 运行工具和命令
%%%
tag := "elan-run"
%%%

本节中的命令可在指定工具链中运行命令，并可在磁盘上定位特定工具链中的工具。
这适用于试验不同 Lean 版本、进行跨版本测试以及将 Elan 与其他工具集成。

```elanHelp "run"
elan-run
Run a command with an environment configured for a given toolchain

USAGE:
    elan run [FLAGS] <toolchain> <command>...

FLAGS:
    -h, --help       Prints help information
        --install    Install the requested toolchain if needed

ARGS:
    <toolchain>     Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                    help toolchain`
    <command>...

DISCUSSION:
    Configures an environment to use the given toolchain and then runs
    the specified program. The command may be any program, not just
    lean or lake. This can be used for testing arbitrary toolchains
    without setting an override.

    Commands explicitly proxied by `elan` (such as `lean` and
    `lake`) also have a shorthand for this available. The toolchain
    can be set by using `+toolchain` as the first argument. These are
    equivalent:

        $ lake +nightly build

        $ elan run --install nightly lake build
```

:::elan run "[\"--install\"] toolchain command ..."
配置环境以使用给定工具链，然后运行指定程序。
如果提供 {elanOptDef flag}`--install` 标志，则会安装该工具链。
该命令可以是任何程序，不必是 `lean` 或 `lake` 之类工具链中的命令。
这样无需设置覆盖项即可测试任意工具链。
:::

```elanHelp "which"
elan-which
Display which binary will be run for a given command

USAGE:
    elan which <command>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <command>
```

:::elan which "command"
显示 {elanMeta}`command` 在该工具链中对应二进制文件的完整路径。
:::

## 管理 Elan
%%%
tag := "elan-self"
%%%

Elan 可以管理自身的安装。
它可以自行升级、自行卸载，并帮助为许多常用 shell 配置制表符补全。

```elanHelp "self"
elan-self
Modify the elan installation

USAGE:
    elan self <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    update       Download and install updates to elan
    uninstall    Uninstall elan.
    help         Prints this message or the help of the given subcommand(s)
```


```elanHelp "self" "update"
elan-self-update
Download and install updates to elan

USAGE:
    elan self update

FLAGS:
    -h, --help    Prints help information
```
:::elan self update
下载并安装 Elan 自身的更新。
:::

:::elan self uninstall
卸载 Elan。
:::

```elanHelp "completions"
elan-completions
Generate completion scripts for your shell

USAGE:
    elan completions [shell]

FLAGS:
    -h, --help    Prints help information

ARGS:
    <shell>     [possible values: zsh, bash, fish, powershell, elvish]

DISCUSSION:
    One can generate a completion script for `elan` that is
    compatible with a given shell. The script is output on `stdout`
    allowing one to re-direct the output to the file of their
    choosing. Where you place the file will depend on which shell, and
    which operating system you are using. Your particular
    configuration may also determine where these scripts need to be
    placed.

    Here are some common set ups for the three supported shells under
    Unix and similar operating systems (such as GNU/Linux).

    BASH:

    Completion files are commonly stored in `/etc/bash_completion.d/`.
    Run the command:

        $ elan completions bash > /etc/bash_completion.d/elan.bash-completion

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    BASH (macOS/Homebrew):

    Homebrew stores bash completion files within the Homebrew directory.
    With the `bash-completion` brew formula installed, run the command:

        $ elan completions bash > $(brew --prefix)/etc/bash_completion.d/elan.bash-completion

    FISH:

    Fish completion files are commonly stored in
    `$HOME/.config/fish/completions`. Run the command:

        $ elan completions fish > ~/.config/fish/completions/elan.fish

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    ZSH:

    ZSH completions are commonly stored in any directory listed in
    your `$fpath` variable. To use these completions, you must either
    add the generated script to one of those directories, or add your
    own to this list.

    Adding a custom directory is often the safest bet if you are
    unsure of which directory to use. First create the directory; for
    this example we'll create a hidden directory inside our `$HOME`
    directory:

        $ mkdir ~/.zfunc

    Then add the following lines to your `.zshrc` just before
    `compinit`:

        fpath+=~/.zfunc

    Now you can install the completions script using the following
    command:

        $ elan completions zsh > ~/.zfunc/_elan

    You must then either log out and log back in, or simply run

        $ exec zsh

    for the new completions to take affect.

    CUSTOM LOCATIONS:

    Alternatively, you could save these files to the place of your
    choosing, such as a custom directory inside your $HOME. Doing so
    will require you to add the proper directives, such as `source`ing
    inside your login script. Consult your shells documentation for
    how to add such directives.

    POWERSHELL:

    The powershell completion scripts require PowerShell v5.0+ (which
    comes Windows 10, but can be downloaded separately for windows 7
    or 8.1).

    First, check if a profile has already been set

        PS C:\> Test-Path $profile

    If the above command returns `False` run the following

        PS C:\> New-Item -path $profile -type file -force

    Now open the file provided by `$profile` (if you used the
    `New-Item` command it will be
    `%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1`

    Next, we either save the completions file into our profile, or
    into a separate file and source it inside our profile. To save the
    completions into our profile simply use

        PS C:\> elan completions powershell >>
%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1
```

:::elan completions "shell"
为 Elan 生成 shell 补全脚本，从而在多种 shell 中启用 Elan 命令的制表符补全。
有关安装方法的说明，请参阅 `elan help completions` 的输出。
:::
