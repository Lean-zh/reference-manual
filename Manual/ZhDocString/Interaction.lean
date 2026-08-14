import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc

universe u v w

/--
`#eval e` 会编译表达式 `e`、运行编译后的代码并打印结果值。

* 该命令会尝试使用 `ToExpr`、`Repr` 或 `ToString` 实例来打印结果。
* 若 `e` 是类型为 `m ty` 的单子值，该命令会尝试把单子 `m` 适配为 `#eval`
  支持的单子之一，包括 `IO`、`CoreM`、`MetaM`、`TermElabM` 和
  `CommandElabM`。用户可定义 `MonadEval` 实例来扩充支持的单子列表。

`#eval` 的能力会随所导入内容而平稳降级。导入 `Lean.Elab.Command` 模块可获得完整能力。

出于可靠性考虑，`#eval` 拒绝求值直接或间接依赖 `sorry` 的表达式，因为 `sorry`
可能导致运行时不稳定或崩溃。可使用 `#eval! e` 命令越过此检查。

选项：
* 若 `eval.pp` 为 `true`（默认如此），则尝试使用 `ToExpr` 实例，以便采用通常的
  美化打印器；否则仅尝试 `Repr` 和 `ToString` 实例。
* 若 `eval.type` 为 `true`（默认为 `false`），则美化打印求值结果的类型。
* 若 `eval.derive.repr` 为 `true`（默认如此），则在没有其他方式可打印结果时，
  尝试自动派生 `Repr` 实例。

另见：使用 `#reduce e` 通过项归约进行求值。
-/
def eval : Unit := ()

/--
用于适配单子的类型类。它与 `MonadLift` 相似，但在必要时，实例合成可以使用默认状态
来合成这样的实例。每个 `MonadLift` 实例都会给出一个 `MonadEval` 实例。

该类服务于 `#eval` 命令；此命令会查找 `MonadEval m CommandElabM` 或
`MonadEval m IO` 实例。
-/
class MonadEval (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  /-- 将单子 `m` 中的值求值到单子 `n` 中。 -/
  monadEval : {α : Type u} → m α → n α

/-- `MonadEval` 的传递闭包。 -/
class MonadEvalT (m : Type u → Type v) (n : Type u → Type w) where
  /-- 将单子 `m` 中的值求值到单子 `n` 中。 -/
  monadEval : {α : Type u} → m α → n α

/--
`#reduce <expression>` 将表达式 `<expression>` 归约至范式，即持续应用归约规则，
直到无法继续归约。

默认不归约表达式中的证明和类型。使用修饰项 `(proofs := true)` 和
`(types := true)` 可分别归约它们。请注意，在 Lean 中命题也是类型。

**警告：**这一操作的计算开销可能很大，复杂表达式尤其如此。

对表达式进行简单求值或执行时，请考虑使用 `#eval <expression>`。
-/
def reduceCmd : Unit := ()

/--
`#where` 描述当前作用域的状态，包括当前命名空间、`open` 打开的命名空间、
`universe` 与 `variable` 命令，以及由 `set_option` 设置的选项。
-/
def «where» : Unit := ()

/-- 显示当前 Lean 版本、目标三元组与平台信息；其中版本号来自 `Lean.versionString`。 -/
def version : Unit := ()

/--
`/-- ... -/ #guard_msgs in cmd` 捕获命令 `cmd` 生成的消息，并检查它们是否与文档
注释的内容匹配。

基本示例：
```lean
/--
error: Unknown identifier `x`
-/
#guard_msgs in
example : α := x
```
这会检查确有此错误，然后消费该消息。

默认情况下，该命令捕获所有消息，但可调整过滤条件。例如，只选择警告：
```lean
/--
warning: declaration uses 'sorry'
-/
#guard_msgs(warning) in
example : α := sorry
```
或只选择错误：
```lean
#guard_msgs(error) in
example : α := sorry
```
在上一个示例中，因为警告未被捕获，`sorry` 上仍会产生警告。可用下述写法彻底丢弃警告：
```lean
#guard_msgs(error, drop warning) in
example : α := sorry
```

一般而言，`#guard_msgs` 接受一组置于圆括号内、以逗号分隔的配置子句：
```
#guard_msgs (configElt,*) in cmd
```
默认配置列表为
`(check all, whitespace := normalized, ordering := exact, positions := false, substring := false)`。

消息过滤器按严重程度选择消息：
- `info`、`warning`、`error`：具有相应严重程度的非跟踪消息；
- `trace`：跟踪消息；
- `all`：所有消息。

过滤器可带有指定操作的前缀：
- `check`（默认）：捕获并检查消息；
- `drop`：丢弃消息；
- `pass`：让消息继续传递。

若未指定过滤器，则假定为 `check all`。否则从左至右处理这些过滤器，并在末尾隐式
添加 `pass all`。

空白处理（先去除开头和末尾的空白）：
- `whitespace := exact` 要求空白完全匹配；
- `whitespace := normalized` 在匹配前把所有换行符转换为空格（默认），从而允许拆分长行；
- `whitespace := lax` 在匹配前把连续空白压缩为一个空格。

消息排序：
- `ordering := exact` 使用消息的原始顺序（默认）；
- `ordering := sorted` 按字典序排列消息，便于测试消息顺序不确定的命令。

位置信息：
- `positions := true` 报告所有消息相对于 `#guard_msgs` 所在行的范围；
- `positions := false` 不报告位置信息。

子串匹配：
- `substring := true` 检查文档注释是否为输出的子串（在空白归一化之后），适用于只关心
  消息一部分的情况；
- `substring := false`（默认）要求精确匹配（允许空白归一化造成的差异）。

稳定输出：
消息含有自动生成的名称（例如元变量 `?m.47`）时，输出可能随运行或 Lean 版本而变化。
使用 `set_option pp.mvars.anonymous false` 可把匿名元变量替换为 `?_`，同时保留
`?a` 等用户命名的元变量。也可使用 `set_option pp.mvars false` 把所有元变量替换为
`?_`。类似地，`set_option pp.fvars.anonymous false` 会把 `_fvar.22` 之类的
松散自由变量名替换为 `_fvar._`。

例如，`#guard_msgs (error, drop all) in cmd` 表示检查错误并丢弃其他一切消息。

命令精译器对 `#guard_msgs` 的代码检查有特殊支持。`#guard_msgs` 本身希望捕获代码
检查器的警告，因此会把所附命令当作顶层命令精译。然而，命令精译器会对所有顶层命令
运行代码检查器，其中也包括 `#guard_msgs` 自身，这会导致重复警告或警告未被捕获。
因此，仅当顶层命令中不存在 `#guard_msgs` 时，顶层命令精译器才运行代码检查器。
-/
def guardMsgsCmd : Unit := ()

/--
`#guard_msgs` 的消息过滤器规范。
- `info`、`warning`、`error`：捕获具有相应严重程度的非跟踪消息；
- `trace`：捕获跟踪消息；
- `all`：捕获所有消息。

过滤器可带有下列前缀：
- `check`（默认）：捕获并检查消息；
- `drop`：丢弃消息；
- `pass`：让消息继续传递。

若未指定过滤器，则假定为 `check all`。否则从左至右处理这些过滤器，并在末尾隐式
添加 `pass all`。
-/
def guardMsgsFilter : Unit := ()

namespace Option
namespace eval

/--
启用后（默认），`#eval` 会尝试使用 `ToExpr` 实例，以便用通常的美化打印器输出结果；
禁用后则使用 `Repr` 或 `ToString` 实例。
-/
def pp : Unit := ()

/-- 启用后（默认为禁用），`#eval` 会美化打印求值结果的类型。 -/
def type : Unit := ()

namespace derive
/-- 启用后（默认），`#eval` 会在没有其他输出方式时尝试自动派生 `Repr` 实例。 -/
def repr : Unit := ()
end derive

end eval

namespace guard_msgs
/--
启用后（默认），如果预期消息与实际消息不匹配，`#guard_msgs` 会显示二者的差异；
禁用后则显示实际消息。
-/
def diff : Unit := ()
end guard_msgs
end Option

namespace Std

/--
确定当文本超出剩余空间时，应如何在组内插入换行。

- `allOrNone` 会把组内每个 `Format.line` 都变成换行，或者一个也不换行：
  ```
  [1,
   2,
   3]
  ```
- `fill` 只会把尽可能少的 `Format.line` 变成换行：
  ```
  [1, 2,
   3]
  ```
-/
inductive Format.FlattenBehavior where
  /-- 组内的 `Format.line` 要么全部变成换行，要么全部变成空格。 -/
  | allOrNone
  /-- 组内只有尽可能少的 `Format.line` 会变成换行。 -/
  | fill

open Format in
/--
表示一组字符串；这些字符串的换行位置和缩进各不相同。

给定以列数表示的具体行宽后，可以从中选出占用行数最少的字符串。

美化打印算法基于 Wadler 的论文
[_A Prettier Printer_](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf)。
-/
inductive Format where
  /-- 空格式。 -/
  | nil : Format
  /-- 当当前组无法容纳于给定列宽时，可以在此处插入换行。 -/
  | line : Format
  /--
  `align` 指示格式化器用空格填充至当前缩进层级；若当前位置已达到或越过缩进，
  则改为换行。

  若 `force` 为 `true`，即使位于已扁平化的组中，也会填充到缩进位置。

  示例：
  ```lean example
  open Std Format in
  #eval IO.println (nest 2 <| "." ++ align ++ "a" ++ line ++ "b")
  ```
  ```lean output
  . a
    b
  ```
  -/
  | align (force : Bool) : Format
  /-- 包含普通字符串的节点。若字符串含换行，格式化器会发出换行，并缩进到当前层级。 -/
  | text : String → Format
  /--
  渲染 `f` 时，`nest indent f` 将当前缩进层级增加 `indent`。

  示例：
  ```lean example
  open Std Format in
  def fmtList (l : List Format) : Format :=
    let f := joinSep l  ("," ++ Format.line)
    group (nest 1 <| "[" ++ f ++ "]")
  ```

  通常它会写在一行；但如果文本过长，格式化器会在逗号后换行，并把后续行缩进 1 列。
  -/
  | nest (indent : Int) (f : Format) : Format
  /-- 连接两个 `Format`。 -/
  | append : Format → Format → Format
  /-- 为给定的内部 `Format` 创建新的扁平化组。 -/
  | group : Format → (behavior : FlattenBehavior := FlattenBehavior.allOrNone) → Format
  /-- 用于把辅助信息（例如 `Expr`）关联到 `Format` 对象。 -/
  | tag : Nat → Format → Format

namespace Format

/-- 创建一个组，其中只有尽可能少的 `Format.line` 被渲染为换行。这等价于将
`FlattenBehavior` 设为 `fill` 后调用 `Format.group`。 -/
def fill : Unit := ()

/--
检查给定格式是否按其结构判为空。此检查会把 `.align` 节点视为空，即使对齐在渲染时可能输出空格或换行；因此返回 `true` 并不保证最终渲染的字符串为空。
-/
def isEmpty : Unit := ()

/--
检查 `Format` 是否恰为构造子 `Format.nil`。与 `Format.isEmpty` 不同，此函数不递归检查组合结构。
-/
def isNil : Unit := ()

/-- 使用 `++` 连接 `Format` 列表。 -/
def join : Unit := ()

/--
以给定格式 `sep` 分隔并连接列表。列表元素使用 `ToFormat.format` 格式化。
-/
def joinSep : Unit := ()

/-- 在每个元素前加上 `pre` 后连接给定列表。列表元素使用 `ToFormat.format` 格式化。 -/
def prefixJoin : Unit := ()

/-- 在每个元素后加上给定后缀再连接列表。列表元素使用 `ToFormat.format` 格式化。 -/
def joinSuffix : Unit := ()

/-- 将缩进层级增加默认的缩进量。 -/
def nestD : Unit := ()

/-- 默认缩进层级，即两个空格。 -/
def defIndent : Unit := ()

/-- 插入换行，随后放置 `f`，并将整体按默认缩进量嵌套。 -/
def indentD : Unit := ()

/--
创建格式 `l ++ f ++ r`，为它建立扁平化组，并按 `l` 的长度缩进内容。
该组的 `FlattenBehavior` 为 `allOrNone`；若需 `fill`，请使用
`Std.Format.bracketFill`。
-/
def bracket : Unit := ()

/--
创建格式 `"[" ++ f ++ "]"`，为它建立扁平化组，并缩进一个空格。
`sbracket` 是 “square bracket”（方括号）的缩写。
-/
def sbracket : Unit := ()

/-- 创建格式 `"(" ++ f ++ ")"`，为它建立扁平化组，并缩进一个空格。 -/
def paren : Unit := ()

/--
创建格式 `l ++ f ++ r`，为它建立扁平化组，并按 `l` 的长度缩进内容。
该组的 `FlattenBehavior` 为 `fill`；若需 `allOrNone`，请使用 `Std.Format.bracket`。
-/
def bracketFill : Unit := ()

/--
将 `Format` 渲染为字符串。
* `width`：总宽度；
* `indent`：换行后的初始缩进（后续换行可能进一步增加缩进）；
* `column`：让第一行比通常情况提前 `column` 个字符换行（当输出字符串将从第
  `column` 列开始打印时很有用）。
-/
def pretty : Unit := ()

/-- 目标输出的默认宽度，即 120 列。 -/
def defWidth : Unit := ()

/--
使用单子 `m` 中的效应和 `MonadPrettyFormat` 的方法渲染 `Format`。
每一行一经渲染就会被发出，而不等待整个文档渲染完毕。
* `w`：总宽度；
* `indent`：换行后的初始缩进（后续换行可能进一步增加缩进）。
-/
def prettyM : Unit := ()

/-- 可用于增量渲染 `Format` 对象的单子。 -/
class MonadPrettyFormat (m : Type → Type) where
  /-- 发出字符串 `s`。 -/
  pushOutput (s : String) : m Unit
  /-- 发出一个换行，随后发出 `indent` 列缩进。 -/
  pushNewline (indent : Nat) : m Unit
  /-- 获取下一个字符串将从哪一列开始发出。 -/
  currColumn : m Nat
  /-- 开始一个以 `tag` 标记的区域。 -/
  startTag (tag : Nat) : m Unit
  /-- 退出 `count` 个已打开标签的作用域。 -/
  endTags (count : Nat) : m Unit

end Format

/--
指定一种面向用户的方式，把类型 `α` 的值转换成 `Format` 对象；所得字符串不要求是
有效代码。`Repr` 类与之相似，但其实例应生成有效的 Lean 代码。
-/
class ToFormat (α : Type u) where
  /-- 将值转换成 `Format` 对象，不要求所得字符串是有效代码。 -/
  format : α → Format

end Std

/--
把某种类型的值转换为 `Format` 的标准方式。渲染所得 `Format` 后，结果应尽可能接近
可以解析回输入值的文本。
-/
class Repr (α : Type u) where
  /--
  在给定优先级下把类型 `α` 的值转换为 `Format`。可利用优先级值避免不必要的圆括号。
  -/
  reprPrec : α → Nat → Std.Format

/-- 使用 `a` 的 `Repr` 实例将其转换为 `Format`，初始优先级为 0。 -/
def repr : Unit := ()

/--
使用 `a` 的 `Repr` 实例将其转换为 `String`，并以默认的 120 列宽度渲染 `Format`。
初始优先级为 0。
-/
def reprStr : Unit := ()

namespace Repr
/--
若上下文优先级 `prec` 至少为函数应用的优先级，则给 `f` 加上圆括号。
它与 `reprArg` 配合使用，可正确地为函数应用语法添加圆括号。
-/
def addAppParen : Unit := ()
end Repr

/--
使用 `a` 的 `Repr` 实例将其转换为 `Format`，并把优先级设为函数应用的优先级。
它与 `Repr.addAppParen` 配合使用，可正确地为函数应用语法添加圆括号。
-/
def reprArg : Unit := ()

/--
辅助类，用于标记应被 `Repr` 方法视为原子的类型。`Repr (List α)` 用它判断是否应
使用 `bracketFill`。
-/
class ReprAtom (α : Type u)

end ZhDoc
