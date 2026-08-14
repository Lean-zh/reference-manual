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
  else none

end Manual
