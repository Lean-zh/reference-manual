**注意: 本文档描述的是如何向[英文参考手册](https://github.com/leanprover/reference-manual) 而非本翻译文档贡献内容**

---
<!--
# External Contribution Guidelines

Thank you for helping out with the Lean reference manual!

In the interest of getting as much documentation as possible written quickly, while still maintaining a consistent voice and style and keeping the technical quality high, all contributions will either be carefully reviewed. However, because review can be very time consuming, we may decline to review some contributions. This means that slow-to-review PRs may just be closed. Nobody wants this to happen, so please get in touch to discuss your plans to contribute ahead of time so we can agree on suitable parameters.
-->

# 外部贡献指南

感谢您为 Lean 参考手册做出贡献！

为了能够快速编写尽可能多的文档，同时保持一致的语音与风格并保证技术质量，所有的贡献都将被认真审查。然而，由于审查过程可能非常耗时，我们有时可能会拒绝审查某些贡献。这意味着那些审查缓慢的 PR 可能会被直接关闭。没有人希望出现这种情况，所以请提前与我们取得联系，讨论您的贡献计划，以便我们能够就合适的贡献参数达成一致。

<!--
## Issues

Issues are a great way to communicate your priorities and needs for documentation, and they are an important input into our planning and prioritization process as we write the Lean reference manual. Please upvote issues that are important to you. Pithy technical examples as comments to documentation requests are also an incredibly useful contribution.
-->

## Issue

Issues 是传达您对文档的优先级和需求的好方式，也是我们在编写 Lean 参考手册过程中进行规划和评估优先级的重要参考。请为对您重要的问题点赞。作为文档请求评论的简明技术示例也是极具价值的贡献。

<!--
## Small Fixes

Pull requests that fix typos and small mistakes are welcome. Please don't group too many in one PR, which makes them difficult to review.
-->

## 小型 fix

欢迎提交修复错别字和小错误的 pull request。请不要将过多内容合并到一个 PR 中，否则会影响审查效率。

<!--
## Substantial Content

Please remember to get in touch ahead of time to plan a larger contribution. In general, text included in the reference manual should live up to the following:
 * Empirical claims about Lean should be tested, either via examples or hidden test cases.
 * Examples should be clearly marked as such, separating the description of the system from the illustrative examples.
 * Technical terms should be introduced using the `deftech` role and referred to using the `tech` role.
 * Write in US English, deferring to the Chicago Manual of Style 18 (CMS) when in doubt. Exceptions to this style may be added and documented.
 * One sentence per line, to make diffs easier to follow.
-->
## 实质性内容

请记得提前与我们沟通，以规划较大的内容贡献。一般来说，参考手册中包含的文本应满足以下条件：
 * 关于 Lean 的经验性断言应进行测试，可以通过示例或隐藏测试用例。
 * 示例应清晰标记，与系统描述区分开来。
 * 技术术语应使用 `deftech` 角色进行介绍，后续引用使用 `tech` 角色。
 * 使用美国英语书写，遇到不确定时参照 《Chicago Manual of Style 18 (CMS)》。例外的风格可以添加并记录。
 * 每句话单独一行，便于对比更改。

<!--
### Style

Automated tooling is not yet capable of implementing these rules perfectly, so pull requests that bring text into compliance with this guide are very welcome.
If complying with style guidelines makes the text more difficult to understand, prioritize the understandability of the text.
-->

### 风格

自动化工具尚无法完美实现这些规则，所以欢迎提交使文本符合本指南要求的 pull request。
如果遵循风格指南会让文本难以理解，请优先保证文本易于理解。

<!-- 
#### Typographical Unicode

In English-language text, use the appropriate Unicode characters for left and right quotation marks (both single and double) and em dashes. 
-->

#### 排版 Unicode

在英文文本中，请使用正确的 Unicode 左右引号（单引号和双引号）以及破折号。

<!-- 
#### Headings
Headings should be set in title case, rather than just capitalizing the first word. This is defined in CMS rule 8.160, but a good first approximation is to capitalize the first and last words, plus all words other than the following:
 * prepositions less than five letters when not used as adverbs or adjectives
 * "a", "an", "the", "to" (infinitive marker), "and", "but", "for", "or", "nor"
 * conventionally lower-case components of names, like "de" or "van"

The [Title Case Converter](https://titlecaseconverter.com/) is useful if in doubt. Remember to select "Chicago" from the list of styles. 
-->

#### 标题

标题应采用标题大小写（Title Case），而非只大写第一个单词。具体定义见 CMS rule 8.160，简要来说，应大写第一个和最后一个单词，以及除以下词外的所有词：
 * 非副词或形容词用法时不足五个字母的介词
 * "a", "an", "the", "to"（不定式标记）, "and", "but", "for", "or", "nor"
 * 名称中惯常小写的词，例如 "de" 或 "van"

如有疑问，[Title Case Converter](https://titlecaseconverter.com/) 工具很有用。记得选择 "Chicago"。

<!-- 
#### Lists
Numbered or bulleted lists should be introduced by a grammatically-complete sentence that is terminated with a colon, follow one of two options:
-->

#### 列表

编号或项目符号列表应由完整语句引入，并以冒号结尾，然后选择以下两种格式之一：
<!-- 
 * All list items contain one or more complete sentences that start with a capital letter and are punctuated accordingly.
 
 * All list items contain noun phrases or sentence fragments that begin with a lower-case letter and do not end with punctuation.
-->
 * 所有列表项都包含一个或多个完整句子，首字母大写且以标点结束。
 * 所有列表项都为名词短语或句子片段，首字母小写且无结尾标点。
 
<!-- That is to say, lists may consist of: -->

也就是说，列表可以由以下类型构成：

 <!-- 
 1. complete sentences, punctuated accordingly
 
 2. non-sentences, punctuated accordingly
 -->

 1. 完整句子，并带有相应标点

 2. 非完整句子，并相应地加标点

<!-- 
In Verso, the list and the sentence with the colon should be grouped with the `paragraph` directive.

If necessary for emphasis, a sentence that contains a list may be broken up into a vertical list element (cf Chicago rule 6.142). In this case, punctuate the list items as though they were inline in the sentence, without using a colon at the start. When using this style in this document, rememember to

 * use the `paragraph` directive so the list is typeset together with its sentence,
 * punctuate with semicolons if the list items themselves contain commas, and
 * remember the trailing "and" and period in the penultimate and final items. 
-->

在 Verso 中，列表及其引导句要合用 `paragraph` 指令进行分组。

如需强调，含有列表的句子可以拆分为纵向列表元素（参考 Chicago rule 6.142）。此时，列表项之间的标点应如同在句中出现那样，无需在开头加冒号。采用本风格时，请

 * 使用 `paragraph` 指令使列表与句子一起排版，
 * 如果列表项内含逗号，则用分号分隔列表项，
 * 记得在倒数第二项和最后一项之间加“and”和句号。


<!-- 
## Markup

The reference manual is written in Verso's manual genre.
In addition to what Verso provides, there are a number of additional roles, code block styles, and directives: 
-->

## 标记

参考手册采用 Verso 的 manual 体裁编写。
除 Verso 提供的格式外，还额外支持多个 roles、代码块风格和指令：

<!-- ### Roles

Please use the following roles where they make sense:

 * `` {lean}`TERM` `` - `TERM` is a Lean term, to be elaborated as such and included it in the rendered document with appropriate highlighting.
   The optional named argument `type` specifies an expected type, e.g. `` {lean type:="Nat"}`.succ .zero` ``

 * `` {name}`X` `` - `X` is a constant in the Lean environment.
   The optional positional argument can be used to override name resolution; if it is provided, then the positional argument is used to resolve the name but the contents of the directive are rendered.
   `` {name Lean.Elab.Command.CommandElabM}`CommandElabM` `` renders as `CommandElabM` with the metadata from the full name.

 * `` {keywordOf KIND}`KW` `` - `KW` is an atom from the syntax kind `KIND`.

 * `` {keyword}`KW` `` - `KW` is an atom from an unspecified syntax kind.
 
 * `` {tactic}`TAC` `` - `TAC` is a tactic name
 
 * `` {option}`OPT` `` - `OPT` is the name of an option

 * `{TODO}[...]` specifies a task to be rendered in draft versions of the manual -->

### 角色（Roles）

请在适用时使用以下角色：

 * `` {lean}`TERM` `` - `TERM` 是 Lean 术语，会按此 elaboration 并用高亮渲染在文档中。
   可选参数 `type` 指定期望类型，如 `` {lean type:="Nat"}`.succ .zero` ``

 * `` {name}`X` `` - `X` 是 Lean 环境中的常量。
   可选位置参数可覆盖名字解析；如传入，则用该参数解析名称但展示指令内容。
   `` {name Lean.Elab.Command.CommandElabM}`CommandElabM` `` 会用全名元数据渲染 `CommandElabM`。

 * `` {keywordOf KIND}`KW` `` - `KW` 是语法类型 `KIND` 的原子。

 * `` {keyword}`KW` `` - `KW` 是未指定语法类型的原子。
 
 * `` {tactic}`TAC` `` - `TAC` 是 tactic 名称
 
 * `` {option}`OPT` `` - `OPT` 是选项名

 * `{TODO}[...]` 在手册草稿版本中指明待办任务


<!-- 
### Code Blocks

 * `lean` specifies that the code block contains Lean commands. The named arguments are:
   * `name` - names the code block for later reference in `leanOutput`
   * `keep` - whether to keep or discard changes made to the environment (default: `true`) 
   * `error` - the code is expected to contain an error (default: `false`)

 * `leanTerm` specifies that the code block contains a Lean term. The named arguments are:
   * `name` - names the code block for later reference in `leanOutput`
   * `keep` - whether to keep or discard changes made to the environment (default: `true`) 
   * `error` - the code is expected to contain an error (default: `false`)

 * `leanOutput NAME` specifies that the code block contains an output from a prior `lean` block.
   The optional named argument `severity` restricts the output to information, warning, or error output.
   
 * `signature` specifies that the code block contains the signature of an existing constant.
 
 * `syntaxError NAME` specifies that the code block contains invalid Lean syntax, and saves the message under `NAME` for `leanOutput`.
   The optional named argument `category` specifies the syntactic category (default: `term`). 
-->

### 代码块

 * `lean` 表示代码块含 Lean 命令。可选参数：
   * `name` - 命名代码块，便于后续 `leanOutput` 引用
   * `keep` - 是否保留该代码块对环境带来的更改（默认为 `true`） 
   * `error` - 代码是否应包含错误（默认为 `false`）

 * `leanTerm` 表示包含 Lean 项的代码块。可选参数同 `lean` 块。

 * `leanOutput NAME` 表示代码块中含有先前 `lean` 代码块的输出。
    可选参数 `severity` 可指定仅显示信息、警告或错误输出。
   
 * `signature` 表示代码块含有已有常量的签名。
 
 * `syntaxError NAME` 表示代码块含无效 Lean 语法，并将报错信息存储在 `NAME` 下以供 `leanOutput`。
    可选参数 `category` 指明语法类别（默认为 `term`）。


<!-- 
### Directives

 * `:::TODO` specifies a task to be rendered in draft versions of the manual
 * `:::example NAME` indicates an example. `NAME` is a string literal that contains valid Verso inline markup.
   Unless the named argument `keep` is `true`, changes made to the Lean environment in the example are discarded.
   Within an `example`, `lean` blocks are elaborated before paragraphs, so inline `lean` roles can refer to names defined later in the example.
 * `:::planned N` describes content that is not yet written, tracked at issue `N` in this repository
 * `:::syntax` describes the syntax of a Lean construct, using a custom DSL based on Lean's quasiquotation mechanism.
   This allows the Lean parser to validate the description, while at the same time decoupling the specifics of the implementation from the structure of the documentation.
-->
 

### 指令

 * `:::TODO` 在手册草稿中表述待办任务
 * `:::example NAME` 指出示例。`NAME` 为包含有效 Verso 内联标记的字符串字面量。若没有指定 `keep` 为 `true`，则示例中对 Lean 环境的更改会被丢弃。
    在 `example` 中，`lean` 代码块会先 elaborate 然后是段落，因此内联 `lean` 角色能引用后来定义的名字。
 * `:::planned N` 描述尚未完成的内容，N 为本仓库相关 issue
 * `:::syntax` 描述 Lean 结构的语法，基于 Lean 的 quasiquotation 自定义 DSL。
   这样 Lean 解析器可校验描述，同时将实现细节与文档结构解耦。

<!-- 
## CI

The CI requires that various checks are passed.

One of them is that the text must live up to a number of rules written with Vale. The style implementation is still quite incomplete; just because your prose passes the linter doesn't mean it will necessarily be accepted!

To run the check, first install Vale. The next step is to preprocess the generated HTML to remove features that Vale can't cope with. Finally, Vale itself can be run.

To preprocess the HTML, use the script `.vale/scripts/rewrite_html.py`. It requires BeautifulSoup, so here's the overall steps to get it working the first time:

```
$ cd .vale/scripts
$ python3 -m venv venv
$ . ./venv/bin/activate # or the appropriate script for your shell, e.g. activate.fish
$ pip install beautifulsoup4
```
After that, just run
```
$ . .vale/scripts/venv/bin/activate
```
to set up the Python environment.

The next step is to run this on Verso's output. If it's in `_out/html-multi`, do this via:
```
$ cd _out
$ python ../.vale/scripts/rewrite_html.py html-multi html-vale
```

Now, run `vale`:
```
$ vale html-vale
```
-->

## CI

CI 需要通过多项检测。

其中一项规定文本必须符合用 Vale 编写的多条规则。风格实现目前还不完整；仅仅因为您的表达通过了 linter，并不意味着一定会被接受！

运行检测前，先安装 Vale。下一步处理生成的 HTML，去除 Vale 无法处理的特性。最后运行 Vale。

预处理 HTML 时，使用脚本 `.vale/scripts/rewrite_html.py`。依赖 BeautifulSoup，步骤如下：

```
$ cd .vale/scripts
$ python3 -m venv venv
$ . ./venv/bin/activate # 或按所用 shell 运行 activate.fish 等
$ pip install beautifulsoup4
```
之后，只需运行
```
$ . .vale/scripts/venv/bin/activate
```
以加载 Python 环境。

下一步就是处理 Verso 输出。如果输出目录为 `_out/html-multi`，使用：
```
$ cd _out
$ python ../.vale/scripts/rewrite_html.py html-multi html-vale
```

然后运行 `vale`：
```
$ vale html-vale
```

<!--
### Deployments from PRs

To enable contributions from external forks while allowing HTML previews, the CI does the following:
 1. `ci.yml` builds the HTML for the pull request and saves it to artifact storage
 2. `label-pr.yml` is triggered when `ci.yml` completes. It (re)labels the
    PR with `HTML available` to indicate that the artifact was built.
 3. Whenever the label is added, `pr-deploy.yml` runs _in the context
    of `main`_ with access to secrets. It can deploy the previews.

The second two steps run the CI code on `main`, not the config from the PR.
-->

 
### 从 PR 部署

为便于外部分支贡献并允许 HTML 预览，CI 执行如下流程：
 1. `ci.yml` 为 pull request 构建 HTML 并存储为 artifact
 2. `label-pr.yml` 在 `ci.yml` 完成后自动标记 PR，标注
    HTML available，表示 artifact 已构建。
 3. 每次被标记时，`pr-deploy.yml` 在 `main` 环境下运行，拥有 secrets 权限，可部署预览。

后两步均在 `main` 分支环境下执行 CI，而非 PR 的配置。