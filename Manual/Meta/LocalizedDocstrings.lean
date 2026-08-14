/-
Copyright (c) 2026 Lean-zh contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean

namespace Manual

/--
本地化手册中由语法图和 `keywordOf` 悬浮提示动态注入的 Lean 解析器文档。
未列出的声明继续使用 Lean 自带的文档字符串。
-/
def localizedSyntaxDocString? (n : Lean.Name) : Option String :=
  if n == `Lean.Parser.Command.declModifiers then
    some "`declModifiers` 是声明修饰符的集合，包括：\n\n* 文档注释 `/-- ... -/`\n* 属性列表 `@[attr1, attr2]`\n* 可见性说明符 `private` 或 `public`\n* `protected`\n* `noncomputable`\n* `unsafe`\n* `partial` 或 `nonrec`\n\n所有修饰符都是可选的，并且必须按上述顺序出现。\n`nestedDeclModifiers` 与 `declModifiers` 相同，但属性与声明打印在同一行；它用于嵌套在其他语法中的声明，例如结构体字段。"
  else if n == `Lean.Parser.Command.declId then
    some "`declId` 匹配 `foo` 或 `foo.{u,v}`：一个标识符，后面可以跟一个宇宙名称列表。"
  else if n == `Lean.Parser.Command.optDeclSig then
    some "`optDeclSig` 匹配类型可选的声明签名：先是一列绑定器，随后可以有 `: type`。"
  else if n == `Lean.Parser.Command.declSig then
    some "`declSig` 匹配类型必需的声明签名：先是一列绑定器，随后是 `: type`。"
  else if n == `Lean.Parser.Term.attrKind then
    some "`attrKind` 匹配 `(\"scoped\" <|> \"local\")?`，用于属性之前，例如 `@[local simp]`。"
  else if n == `Lean.Parser.Termination.suffix then
    some "终止提示依次为 `termination_by` 和 `decreasing_by`。"
  else if n == `Lean.Parser.Command.classAbbrev then
    some "将\n```\nclass abbrev C <params> := D_1, ..., D_n\n```\n展开为\n```\nclass C <params> extends D_1, ..., D_n\nattribute [instance] C.mk\n```"
  else if n == `Lean.Parser.Term.anonymousCtor then
    some "如果期望类型是只有一个构造器 `c` 的归纳类型，那么*匿名构造器* `⟨e, ...⟩` 等价于 `c e ...`。\n如果给出的项比 `c` 的参数更多，其余参数会组成新的匿名构造器应用。\n例如，`⟨a, b, c⟩ : α × (β × γ)` 等价于 `⟨a, ⟨b, c⟩⟩`。"
  else if n == `termIfThenElse then
    some "`if c then t else e` 是 `ite c t e`（即“如果—那么—否则”）的记法；它根据 `c` 是否为真返回 `t` 或 `e`。\n显式参数 `c : Prop` 本身没有计算内容；另有一个由实例合成得到的 `[Decidable c]` 参数，真正决定如何把 `c` 求值为真或假。\n写成 `if h : c then t else e` 时表示依赖式条件 `dite`，此时 `t` 和 `e` 可以使用 `c` 为真或假的事实。\n\n标识符中的记法约定：建议将 `if c then t else e` 写作 `ite`，并分别用 `left`、`right` 指代 `t`、`e`。"
  else if n == `prioDefault then
    some "默认优先级为 `default = 1000`；未指定优先级时使用它。"
  else if n == `prioLow then
    some "标准“低”优先级为 `low = 100`，用于优先级应低于默认值的项目。"
  else if n == `prioMid then
    some "标准“中”优先级为 `mid = 500`；它低于 `default`，高于 `low`。"
  else if n == `prioHigh then
    some "标准“高”优先级为 `high = 10000`，用于优先级应高于默认值的项目。"
  else if n == `«prio(_)» then
    some "圆括号用于对优先级表达式进行分组。"
  else if n == `Lean.Parser.Syntax.addPrio then
    some "优先级的加法。通常仅用于施加偏移，例如 `default + 1`。"
  else if n == `Lean.Parser.Syntax.subPrio then
    some "优先级的减法。通常仅用于施加偏移，例如 `default - 1`。"
  else if n == `Lean.Parser.Command.printAxioms then
    some "显示一个声明直接或间接使用的公理。请参阅[参考手册](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=validating-proofs)，了解如何解释输出。"
  else if n == `Lean.guardMsgsCmd then
    some "`/-- ... -/ #guard_msgs in cmd` 捕获命令 `cmd` 生成的消息，并检查它们是否与文档\n注释的内容匹配。\n\n基本示例：\n```lean\n/--\nerror: Unknown identifier `x`\n-/\n#guard_msgs in\nexample : α := x\n```\n这会检查确有此错误，然后消费该消息。\n\n默认情况下，该命令捕获所有消息，但可调整过滤条件。例如，只选择警告：\n```lean\n/--\nwarning: declaration uses 'sorry'\n-/\n#guard_msgs(warning) in\nexample : α := sorry\n```\n或只选择错误：\n```lean\n#guard_msgs(error) in\nexample : α := sorry\n```\n在上一个示例中，因为警告未被捕获，`sorry` 上仍会产生警告。可用下述写法彻底丢弃警告：\n```lean\n#guard_msgs(error, drop warning) in\nexample : α := sorry\n```\n\n一般而言，`#guard_msgs` 接受一组置于圆括号内、以逗号分隔的配置子句：\n```\n#guard_msgs (configElt,*) in cmd\n```\n默认配置列表为\n`(check all, whitespace := normalized, ordering := exact, positions := false, substring := false)`。\n\n消息过滤器按严重程度选择消息：\n- `info`、`warning`、`error`：具有相应严重程度的非跟踪消息；\n- `trace`：跟踪消息；\n- `all`：所有消息。\n\n过滤器可带有指定操作的前缀：\n- `check`（默认）：捕获并检查消息；\n- `drop`：丢弃消息；\n- `pass`：让消息继续传递。\n\n若未指定过滤器，则假定为 `check all`。否则从左至右处理这些过滤器，并在末尾隐式\n添加 `pass all`。\n\n空白处理（先去除开头和末尾的空白）：\n- `whitespace := exact` 要求空白完全匹配；\n- `whitespace := normalized` 在匹配前把所有换行符转换为空格（默认），从而允许拆分长行；\n- `whitespace := lax` 在匹配前把连续空白压缩为一个空格。\n\n消息排序：\n- `ordering := exact` 使用消息的原始顺序（默认）；\n- `ordering := sorted` 按字典序排列消息，便于测试消息顺序不确定的命令。\n\n位置信息：\n- `positions := true` 报告所有消息相对于 `#guard_msgs` 所在行的范围；\n- `positions := false` 不报告位置信息。\n\n子串匹配：\n- `substring := true` 检查文档注释是否为输出的子串（在空白归一化之后），适用于只关心\n  消息一部分的情况；\n- `substring := false`（默认）要求精确匹配（允许空白归一化造成的差异）。\n\n稳定输出：\n消息含有自动生成的名称（例如元变量 `?m.47`）时，输出可能随运行或 Lean 版本而变化。\n使用 `set_option pp.mvars.anonymous false` 可把匿名元变量替换为 `?_`，同时保留\n`?a` 等用户命名的元变量。也可使用 `set_option pp.mvars false` 把所有元变量替换为\n`?_`。类似地，`set_option pp.fvars.anonymous false` 会把 `_fvar.22` 之类的\n松散自由变量名替换为 `_fvar._`。\n\n例如，`#guard_msgs (error, drop all) in cmd` 表示检查错误并丢弃其他一切消息。\n\n命令精译器对 `#guard_msgs` 的代码检查有特殊支持。`#guard_msgs` 本身希望捕获代码\n检查器的警告，因此会把所附命令当作顶层命令精译。然而，命令精译器会对所有顶层命令\n运行代码检查器，其中也包括 `#guard_msgs` 自身，这会导致重复警告或警告未被捕获。\n因此，仅当顶层命令中不存在 `#guard_msgs` 时，顶层命令精译器才运行代码检查器。"
  else if n == `«term_<_» then
    some "小于关系：`x < y`。\n\n标识符中的记法约定：建议将 `<` 写作 `lt`。"
  else if n == `«term_≤_» then
    some "小于等于关系：`x ≤ y`。\n\n标识符中的记法约定：建议将 `≤` 写作 `le`。"
  else if n == `«term_>_» then
    some "`a > b` 是 `b < a` 的缩写。\n\n标识符中的记法约定：建议将 `>` 写作 `gt`。"
  else if n == `«term_≥_» then
    some "`a ≥ b` 是 `b ≤ a` 的缩写。\n\n标识符中的记法约定：建议将 `≥` 写作 `ge`。"
  else none

end Manual
