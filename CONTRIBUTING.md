# 中文参考手册贡献说明

感谢参与 Lean 语言参考手册中文翻译。

## 开始之前

- 先在 issue 中认领范围；大型改动先讨论拆分方式。
- 从最新 `main` 开始，不要用旧中文仓库的整章文件覆盖最新上游。
- 一个 PR 聚焦一个章节或一类基础设施改动，便于审阅和回滚。
- 不要编辑与当前任务无关的章节、生成物或上游 CI。

## 翻译要求

- 保留 Lean、Verso 标记、代码和示例结构；所有示例仍须通过类型检查。
- 一句一行，减少 diff 冲突。
- 技术术语采用 [TERMINOLOGY.md](TERMINOLOGY.md)。本项目统一将 elaboration 译为“精译”，elaborator 译为“精译器”。
- 术语引用写作 ``{tech (key := "English term")}[中文术语]``；定义写作 ``{deftech (key := "English term")}_中文术语_``。若原文没有术语角色，不要擅自添加。
- `{index}[...]` 的索引键保持英文。
- `:::`、`::::` 等 Verso 容器必须整体保持嵌套平衡。
- 中文标题必须设置稳定的 ASCII `file` 与 `tag`，不要让输出路径依赖中文标题。例如：

  ```text
  #doc (Manual) "简介" =>
  %%%
  file := some "introduction"
  tag := "introduction"
  %%%
  ```

## Docstring 翻译

中文文档载体定义在 `Manual/ZhDocString/`。用法见 [README](README.md#中文-docstring)。

- 载体声明只用于携带中文 docstring，不应改变手册描述的真实 API。
- 结构体字段和归纳类型构造子应与英文声明一一对应；映射不匹配必须修正，不能靠调整顺序掩盖。
- 新增模块后更新 `Manual/ZhDocString.lean`，确保 `Manual.lean` 的 import DAG 可以构建全部中文模块。

## 检查

先运行与改动最接近的目标：

```sh
lake build Manual.ZhDocString
lake build Manual
```

涉及完整站点、链接、教程或发布脚本时再运行：

```sh
lake build
./generate-html.sh --mode preview
scripts/check-examples-isolated.sh
```

提交前还应运行：

```sh
git diff --check
git status --short
```

CI 的 `Build` 步骤必须保留。不要以只生成 HTML 代替 `lake build`。

## AI 辅助翻译

允许使用 AI 辅助，但提交者必须逐句校对、验证术语和运行构建。具体流程见 [AIAgentTranslatorPrompt.md](AIAgentTranslatorPrompt.md)。AI 生成内容不降低贡献者对技术正确性和版权合规性的责任。
