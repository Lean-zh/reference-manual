# Lean 语言参考手册（中文）

本仓库是 [Lean 语言参考手册](https://github.com/leanprover/reference-manual) 的中文版本，基于 Lean 4.34 的上游源码持续同步。手册面向需要精确查阅语言行为的读者；中文站点发布于 <https://www.leanprover.cn/reference-manual/>。

## 翻译贡献

1. 先创建 issue，说明准备翻译或校对的章节，避免重复工作。
2. fork `Lean-zh/reference-manual`，从当前 `main` 创建分支。
3. 遵循 [贡献说明](CONTRIBUTING.md)、[术语表](TERMINOLOGY.md) 与 [AI 翻译规范](AIAgentTranslatorPrompt.md)。
4. 提交前至少运行窄目标构建；涉及入口、导入或公共扩展时再运行完整构建。

翻译应保留上游最新章节、教程和构建结构，不应通过回退到旧版文件来覆盖上游更新。

## 本地构建

安装 [Elan](https://github.com/leanprover/elan) 后，在仓库根目录运行：

```sh
lake update
lake build
./generate-html.sh --mode preview
python3 ./server.py 8880
```

然后访问 <http://localhost:8880>。生成站点位于 `_out/site/`。

只检查中文 docstring 基础设施可运行：

```sh
lake build Manual.ZhDocString
```

无需安装旧版 README 所述的 LaTeX 或 `pdftocairo` 依赖；当前上游构建流程不再生成这些旧图稿。

## 中文 docstring

Lean 源码中的 `{docstring ...}` 直接读取英文文档。中文手册提供两个 Verso 块命令：

```text
{zhdocstring 原声明 ZhDoc.中文文档载体}
{zhOptionDocs 选项名 ZhDoc.中文文档载体}
```

中文载体放在 `Manual/ZhDocString/`，保持与原声明一致的构造子/字段名称和顺序。`zhdocstring` 使用原声明的签名与链接，只替换说明文本；若结构不匹配会直接报错，避免把译文挂到错误字段或构造子上。新增模块必须导入 `Manual/ZhDocString.lean`，并由手册入口的 import DAG 覆盖。

## 分支与发布

- `main` 跟踪最新 Lean 正式版或候选版。
- 上游 nightly/PR 兼容性 CI 保持原样，用于尽早发现 API 变化。
- `v*` 标签触发 `.github/workflows/release-tag.yml`，构建后更新 `Lean-zh/reference-manual` 的 `deploy` 分支。

禁止在普通翻译 PR 中手工改写或删除上游 CI。发布工作流使用当前 `deploy/prep.sh`、`deploy/build.sh`、`deploy/generate.sh` 与 `deploy/release.py` 接口。

## 上游文档

上游的详细开发与部署说明会持续变化。需要排查构建脚本或 nightly 机制时，请以当前仓库脚本及 [英文上游 README](https://github.com/leanprover/reference-manual/blob/main/README.md) 为准。
