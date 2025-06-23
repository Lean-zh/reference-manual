<!--
# Lean Language Reference
-->
# Lean语言中文参考文档

## 如何贡献翻译
1. 为了避免重复工作，贡献翻译前请先开issue确定翻译范围
2. fork本仓库，修改后提交pull request

## 文档翻译与校对
- 参考 [翻译规范](https://github.com/Agda-zh/PLFA-zh/issues/1)
- [术语表](https://docs.google.com/spreadsheets/d/1HL3E_eNF3rI6dy3k7_EpSOLo1eRkBDNIEPeyTg_Eu3s/edit?usp=sharing)

## {docstring xxx}的翻译
由于{docstring xxx}会直接引用lean的源码，因此本仓库在Manual目录下创建了ZhDocString目录，其中`Manual/ZhDocString/ZhDocString.lean`定义了`zhdocstring` 
用法如下 
```{zhdocstring 原对象 翻译过的对象}```

其中翻译过的对象可以在 `Manual/ZhDocString/`下创建一个对应文件的lean文件，然后通过namespace创建一个和原对象同名的对象

如`Manual/ZhDocString/Types.lean`中创建了`ZhDoc.propext` 并提供了与`propext`对应的翻译文档

然后在原文中使用`{docstring propext}`的地方 替换为 `{zhdocstring propext ZhDoc.propext}`

`zhdocstring`会使用`propext`的签名和连接，但是会使用`ZhDoc.propext`文档块

以此来完成対{docstring xxx}的翻译

注意，源码中的文档块以`/--`开头`-/`结尾，必须対每个属性/构造子编写文档，否则会编译报错


## 特别注意

- 提交PR前务必本地执行 `deploy/generate.sh` 确保无编译错误, 无任何`error`输出, **`lake exe generate-manual --depth 2`不能保证无错误**
- 技术术语
  - 遇到未翻译过的技术术语，将其改成 `{tech key := "英文"}[中文]` 的格式 
  - 遇到技术术语的定义`{deftech}_xxx_` 时，修改为 `{deftech key := "xxx"}_中文_`
- 以 `::::` 开始到 `::::` 结束的代码块是一个整体， 需要整体注释掉重新创建一个新的翻译过的版本
- 如果某篇文档缺少tag 请添加一个，否则可能会导致问题
- `{index}[xxx]` 不需要翻译
- 如下#doc 对应的%%%块下需要添加`file := 原文件英文名` 否则将标题改为中文后，对应的静态文件名会出现错误 
```
#doc (Manual) "简介" =>
%%%
file := "Introduction"
%%%
```


## 本地编译与环境安装
**本参考手册只能在非windows环境下构建**
1. latex, 参考[本地构建](#在本地构建参考手册)
2. 安装 gcc
3. 安装  `pdftocairo`，在Debian系系统为`poppler-utils`包，在Homebrew中为`poppler`包
4. 编译: `lake exe generate-manual --depth 2`
生成的文档在`_out` 目录下

**以下为原文档readme内容**
----

# Lean参考文档

<!--
The Lean Language Reference is intended as a comprehensive, precise description of Lean. It is first and foremost a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.

This new reference has been rebuilt from the ground up in Verso. This means that all example code is type checked, the source code contains tests to ensure that it stays up-to-date with respect to changes in Lean, and we can add any features that we need to improve the documentation. Verso also makes it easy to integrate tightly with Lean, so we can show function docstrings directly, mechanically check descriptions of syntax against the actual parser, and insert cross-references automatically.
-->
该参考文档旨在对Lean进行全面、精确的描述。它首先是一份参考资料，Lean用户可以在其中查找详细信息，而不是为新用户准备的教程。

该参考文档在Verso中构建。这意味着所有示例代码都经过类型检查，源码中包含测试以保证它能随着Lean的更改而保持更新，并且我们可以根据需要添加任何有助于改进文档的功能。Verso还使与Lean集成变得容易，因此我们可以直接显示函数文档字符串，自动化地检查语法描述与实际解析器的一致性，并自动插入交叉引用。

<!--
## Reading the Manual

The latest release of this reference manual can be read [here](https://lean-lang.org/doc/reference/latest/).

For developers:
 * The output of building the current state of the `nightly-testing` branch can be read [here](https://lean-reference-manual-review.netlify.app/).
 * Each pull request in this repository causes two separate previews to be generated, one with extra information that's only useful to those actively working on the text, such as TODO notes and symbol coverage progress bars. These are posted by a bot to the PR after the first successful build.
-->

## 如何阅读该参考文档

该参考手册的最新版本可以在[这里](https://lean-lang.org/doc/reference/latest/)阅读。

对于开发者：
 * 构建当前`nightly-testing`分支状态的输出可以在[这里](https://lean-reference-manual-review.netlify.app/)阅读。
 * 本仓库中的每个pull request都会生成两个独立的预览版本，其中一个包含仅对积极参与文本工作的人员有用的额外信息，比如TODO注释和符号覆盖率进度条。这些会由机器人在首次构建成功后发布到PR中。

<!--
## Branches and Development

The two most important branches are:
 * `main` tracks the latest Lean release or release candidate
 * `nightly-testing` tracks the latest Lean nightlies

New content that addresses in-development features of Lean will be
written on `nightly-testing`, while updates to existing content may be
written either on `main` or `nightly-testing`, as appropriate. From
time to time, `main` will be merged into `nightly-testing`; when Lean
is released, the commits in `nightly-testing` are rebased onto `main`
to achieve a clean history.
-->

## 分支与开发

两个最重要的分支是：
 * `main`跟踪最新的Lean发行版或候选发行版
 * `nightly-testing`跟踪最新的Lean nightly版本

针对Lean开发中功能的新内容将在`nightly-testing`上编写，而对现有内容的更新可根据需要在`main`或`nightly-testing`上编写。每隔一段时间，`main`会合并到`nightly-testing`；当Lean发布时，`nightly-testing`中的PR会rebase到`main`上以获得干净的提交历史。

<!--
## Building the Reference Manual Locally

This reference manual contains figures that are built from LaTeX sources. To build them, you'll need the following:
 * A LaTeX installation, including LuaLaTeX and the following packages from TeXLive:
   + `scheme-minimal`
   + `latex-bin`
   + `fontspec`
   + `standalone`
   + `pgf`
   + `pdftexcmds`
   + `luatex85`
   + `lualatex-math`
   + `infwarerr`
   + `ltxcmds`
   + `xcolor`
   + `fontawesome`
   + `spath3`
   + `inter`
   + `epstopdf-pkg`
   + `tex-gyre`
   + `tex-gyre-math`
   + `unicode-math`
   + `amsmath`
   + `sourcecodepro`
 * `pdftocairo`, which can be found in the `poppler-utils` package on Debian-derived systems and the `poppler` package in Homebrew
 
Additionally, to run the style checker locally, you'll need [Vale](https://vale.sh/). It runs in CI, so this is not a necessary step to contribute.

To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 ./server.py 8880 &
```

Then open <http://localhost:8880> in your browser.
-->

## 在本地构建参考手册

本参考手册包含由LaTeX源码构建的图示。要构建它们，你需要以下内容：
 * 一个LaTeX环境，包括LuaLaTeX及TeXLive下列包：
   + `scheme-minimal`
   + `latex-bin`
   + `fontspec`
   + `standalone`
   + `pgf`
   + `pdftexcmds`
   + `luatex85`
   + `lualatex-math`
   + `infwarerr`
   + `ltxcmds`
   + `xcolor`
   + `fontawesome`
   + `spath3`
   + `inter`
   + `epstopdf-pkg`
   + `tex-gyre`
   + `tex-gyre-math`
   + `unicode-math`
   + `amsmath`
   + `sourcecodepro`
 * `pdftocairo`，在Debian系系统为`poppler-utils`包，在Homebrew中为`poppler`包

此外，如需本地运行风格检查器，你需要[Vale](https://vale.sh/)。CI中已会运行它，因此这不是贡献的必要步骤。

构建手册，请运行：

```
lake exe generate-manual --depth 2
```

然后在输出目录下开启本地web服务器：
```
python3 ./server.py 8880 &
```

然后在浏览器中打开<http://localhost:8880>。

<!--
## Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.
-->

## 如何贡献代码(向原始仓库)

更多信息请见[CONTRIBUTING.md](CONTRIBUTING.md)。