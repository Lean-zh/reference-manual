/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.NotationsMacros

/--
把语法与其来源上下文关联起来的源信息。

`SourceInfo` 的主要用途是把解析器和宏展开器的输出关联到原始源文件。解析器产生的
`Syntax.node` 通常不携带源信息；解析器只把源信息附在原子和标识符上。引用产生的
`Syntax.node` 则带有合成源信息，既把它关联到一个原始参考位置，也表明其中的原始
原子可能并非来自当前正在精译的 Lean 文件。

源信息还用于把 Lean 的输出关联到其所表示的内部数据，这是许多交互功能的基础。
在这种用途下，`Syntax.node` 也可以携带源信息。
-/
inductive SourceInfo where
  /--
  解析器从原始输入产生的记号；除位置信息外，还包含前导和尾随空白。

  前导空白是在解析完成后由 `Syntax.updateLeading` 推断的，因为解析过程中，尤其存在
  回溯时，“前一个记号”并没有良好定义。
  -/
  | original (leading : Substring.Raw) (pos : String.Pos.Raw)
      (trailing : Substring.Raw) (endPos : String.Pos.Raw)
  /--
  合成语法是由元程序或 Lean 自身（例如引用）产生的语法。它带有来自原始语法的
  源码范围，以便与源文件关联。

  反精译器也用此构造子编码产生该语法的核心语言表达式。

  合成语法的 `canonical` 标志用于这样的语法：它并非原始输入的字面组成部分，但在
  悬停信息和错误消息中应被视作“仿佛由用户写下”。它通常用于在宏展开改变标识符
  名称后仍把绑定位置连接到用户的原始语法，也用于应接收定点消息的记号。

  一般而言，宏展开应只在一个规范记号中使用某一片输入语法；一个例外是同一标识符
  被用来声明两个绑定器，例如依赖 `if` 的宏展开。此时用户悬停在该标识符上会看到
  两个绑定位置的信息。
  -/
  | synthetic (pos : String.Pos.Raw) (endPos : String.Pos.Raw) (canonical := false)
  /-- 没有位置信息的合成记号。 -/
  | protected none

/--
指定 `Syntax.node` 值的解释；它是 `Name` 的缩写。

节点种类可以是任意名称，不必指向环境中的声明。不过按照约定，节点种类通常对应于
生成它的 `Parser` 或 `ParserDescr` 声明。解析基础设施还使用若干不对应解析器声明的
内建种类，例如 `nullKind` 和 `choiceKind`。
-/
abbrev SyntaxNodeKind := _root_.Lean.SyntaxNodeKind

/--
标识符在被引用位置的上下文中可能指向的绑定。

引用中的标识符既可能指向全局声明，也可能指向引用处作用域内的命名空间。这些信息
保存在 `Syntax.ident` 构造子中，是卫生宏实现的一部分。
-/
inductive Syntax.Preresolved where
  /-- 一个可能的命名空间引用。 -/
  | namespace (ns : _root_.Lean.Name)
  /-- 一个可能的全局常量或节变量引用，并带有后续字段访问。 -/
  | decl (n : _root_.Lean.Name) (fields : List String)

/--
Lean 的语法树。

语法树在 Lean 中无处不在：解析器产生语法树，宏展开器变换语法树，精译器再精译
语法树。反精译器也会产生语法树，并把它们呈现给用户。
-/
inductive Syntax where
  /--
  因解析错误而缺失的一段语法。对 `Syntax` 使用越界索引时也会得到
  `Syntax.missing`。
  -/
  | missing : Syntax
  /--
  语法树中可以含有更多子语法的节点；`kind` 决定节点的解释。

  解析器产生的节点通常令 `info` 为 `Lean.SourceInfo.none`，源信息保存在相应标识符
  和原子的字段中。该字段有两种用途：反精译器用它关联实现交互功能的元数据；引用
  创建的节点用它把语法标记为合成语法，即使其首尾记号本身不是合成的。
  -/
  | node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  /--
  语法中不是标识符的原子组成部分。关键字（如 `def`、`fun`、`inductive`）、字面量
  （如数字和字符串）以及标点和分隔符（如 `(`、`)`、`=>`）都是原子。标识符由
  `Syntax.ident` 表示；原子也对应 `syntax` 声明中的引号字符串。
  -/
  | atom (info : SourceInfo) (val : String) : Syntax
  /--
  标识符。除源信息外，`rawVal` 是输入文件中的原始子串，`val` 是解析后的 Lean
  名称（可能含宏作用域），`preresolved` 是它可能指向的声明列表，由引用填充。
  -/
  | ident (info : SourceInfo) (rawVal : Substring.Raw) (val : _root_.Lean.Name)
      (preresolved : List Syntax.Preresolved) : Syntax

/-- 检查语法是否具有给定的种类或伪种类。非节点语法的伪种类与 `getKind` 相同。 -/
def Syntax.isOfKind (stx : _root_.Lean.Syntax) (k : _root_.Lean.SyntaxNodeKind) : Bool :=
  _root_.Lean.Syntax.isOfKind stx k

/--
取得 `Syntax.node` 的种类，或其他 `Syntax` 值的伪种类：标识符使用 `identKind`，
`Syntax.missing` 使用 `` `missing ``，原子则使用其字符串字面量。
-/
def Syntax.getKind (stx : _root_.Lean.Syntax) : _root_.Lean.SyntaxNodeKind :=
  _root_.Lean.Syntax.getKind stx

/-- 改变 `Syntax.node` 根部的种类为 `k`；其他 `Syntax` 值原样返回。 -/
def Syntax.setKind (stx : _root_.Lean.Syntax) (k : _root_.Lean.SyntaxNodeKind) : _root_.Lean.Syntax :=
  _root_.Lean.Syntax.setKind stx k

/-- 标识符约定使用的伪种类 `` `ident ``；它并不实际用作 `Syntax.node` 的种类。 -/
abbrev identKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.identKind
/-- `` `str `` 是字符串字面量（如 `"foo"`）的节点种类。 -/
abbrev strLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.strLitKind
/-- `` `interpolatedStrKind `` 是插值字符串（如 `"value = {x}"`）的节点种类。 -/
abbrev interpolatedStrKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.interpolatedStrKind
/-- `` `interpolatedStrLitKind `` 是插值字符串片段（如 `"value = {` 和 `}"`）的节点种类。 -/
abbrev interpolatedStrLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.interpolatedStrLitKind
/-- `` `char `` 是字符字面量（如 `'A'`）的节点种类。 -/
abbrev charLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.charLitKind
/-- `` `num `` 是数字字面量（如 `42` 和 `0xa1`）的节点种类。 -/
abbrev numLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.numLitKind
/-- `` `scientific `` 是科学计数法浮点字面量（如 `1.23e-3`）的节点种类。 -/
abbrev scientificLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.scientificLitKind
/-- `` `name `` 是名称字面量（如 `` `foo ``）的节点种类。 -/
abbrev nameLitKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.nameLitKind
/-- `` `fieldIdx `` 是投影索引（如 `x.2` 中的 `2`）的节点种类。 -/
abbrev fieldIdxKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.fieldIdxKind
/-- `` `group `` 用于 `Lean.Parser.group` 产生的节点，避免其在 `optional` 内与空种类混淆。 -/
abbrev groupKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.groupKind
/--
`` `null `` 是没有其他种类适用时的后备种类。重复运算符会产生空节点，而空的空节点
表示可选解析失败；`many` 等原始列表解析器也使用此种类。
-/
abbrev nullKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.nullKind
/--
`` `choice `` 表示有歧义的解析结果。解析器优先选择更长的匹配；若最长匹配不唯一，
所有结果都会保存起来，直到有类型信息时再决定使用哪一个。
-/
abbrev choiceKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.choiceKind
/--
`` `hygieneInfo `` 是 `Lean.Parser.hygieneInfo` 的节点种类。该解析器不消耗输入，却产生
捕获当前位置卫生信息的“不可见记号”，可用来生成仿佛由宏输入引入的标识符。
-/
abbrev hygieneInfoKind : _root_.Lean.SyntaxNodeKind := _root_.Lean.hygieneInfoKind

/--
带类型语法；它跟踪其中 `Syntax` 可能具有的种类。

语法引用会产生或要求种类正确的 `TSyntax`，但除此之外并无强制保证；直接使用构造子
即可轻易绕过这一约束。
-/
structure TSyntax (ks : _root_.Lean.SyntaxNodeKinds) where
  /-- 底层的 `Syntax` 值。 -/
  raw : _root_.Lean.Syntax

/--
`SyntaxNodeKinds` 是用列表实现的 `SyntaxNodeKind` 集合。单元素集合极为常见，可直接
写成名称字面量；只有空集合或多元素集合才需要列表语法。
-/
@[implicit_reducible] def SyntaxNodeKinds : Type := _root_.Lean.SyntaxNodeKinds

/-- 某一种类集合 `ks` 的带类型语法数组。 -/
abbrev TSyntaxArray (ks : _root_.Lean.SyntaxNodeKinds) := _root_.Lean.TSyntaxArray ks

/-- 不重新分配内存，把 `TSyntaxArray` 转换成 `Array Syntax`。 -/
def TSyntaxArray.raw {ks : _root_.Lean.SyntaxNodeKinds} (as : _root_.Lean.TSyntaxArray ks) :
    Array _root_.Lean.Syntax :=
  _root_.Lean.TSyntaxArray.raw as

namespace Syntax

/--
由给定分隔符交错分隔的带类型语法数组；每个语法元素的种类来自 `ks`。

分隔数组由 `,*` 等重复运算符产生。与 `Array (TSyntax ks)` 之间的强制转换会按需插入
或移除分隔符。无类型版本是 `Lean.Syntax.SepArray`。
-/
structure TSepArray (ks : _root_.Lean.SyntaxNodeKinds) (sep : String) where
  /-- 元素与分隔符按 `#[el1, sep1, el2, sep2, el3]` 的顺序排列。 -/
  elemsAndSeps : Array _root_.Lean.Syntax

/-- 从分隔数组中提取所有非分隔符元素。 -/
def TSepArray.getElems {k : _root_.Lean.SyntaxNodeKinds} {sep : String}
    (sa : _root_.Lean.Syntax.TSepArray k sep) : _root_.Lean.TSyntaxArray k :=
  _root_.Lean.Syntax.TSepArray.getElems sa

/-- 从不含分隔符的元素数组构造带类型分隔数组，并插入适当的分隔符。 -/
def TSepArray.ofElems {k : _root_.Lean.SyntaxNodeKinds} {sep : String}
    (elems : Array (_root_.Lean.TSyntax k)) : _root_.Lean.Syntax.TSepArray k sep :=
  _root_.Lean.Syntax.TSepArray.ofElems elems

/-- 在分隔数组末尾添加元素，并在需要时添加分隔符。 -/
def TSepArray.push {k : _root_.Lean.SyntaxNodeKinds} {sep : String}
    (sa : _root_.Lean.Syntax.TSepArray k sep) (e : _root_.Lean.TSyntax k) :
    _root_.Lean.Syntax.TSepArray k sep :=
  _root_.Lean.Syntax.TSepArray.push sa e

/-- 表示 Lean 项的语法。 -/
protected abbrev Term := _root_.Lean.Syntax.Term
/-- 表示命令的语法。 -/
protected abbrev Command := _root_.Lean.Syntax.Command
/-- 表示宇宙层级的语法。 -/
protected abbrev Level := _root_.Lean.Syntax.Level
/-- 表示策略的语法。 -/
protected abbrev Tactic := _root_.Lean.Syntax.Tactic
/-- 表示优先权（例如运算符优先权）的语法。 -/
protected abbrev Prec := _root_.Lean.Syntax.Prec
/-- 表示优先级（例如实例声明优先级）的语法。 -/
protected abbrev Prio := _root_.Lean.Syntax.Prio
/-- 表示标识符的语法。 -/
protected abbrev Ident := _root_.Lean.Syntax.Ident
/-- 表示字符串字面量的语法。 -/
protected abbrev StrLit := _root_.Lean.Syntax.StrLit
/-- 表示字符字面量的语法。 -/
protected abbrev CharLit := _root_.Lean.Syntax.CharLit
/-- 表示以反引号开头的名称字面量的语法。 -/
protected abbrev NameLit := _root_.Lean.Syntax.NameLit
/-- 表示数字字面量的语法。 -/
protected abbrev NumLit := _root_.Lean.Syntax.NumLit
/-- 表示可含小数部分和指数部分的科学计数法数字字面量的语法。 -/
protected abbrev ScientificLit := _root_.Lean.Syntax.ScientificLit
/-- 表示宏卫生信息的语法。 -/
protected abbrev HygieneInfo := _root_.Lean.Syntax.HygieneInfo

/-- 创建表示 Lean 项应用的语法，同时避免产生退化的空应用。 -/
def mkApp (fn : _root_.Lean.Syntax.Term) (args : _root_.Lean.TSyntaxArray `term) : _root_.Lean.Syntax.Term :=
  _root_.Lean.Syntax.mkApp fn args
/-- 创建表示 Lean 常量应用的语法，同时避免产生退化的空应用。 -/
def mkCApp (fn : _root_.Lean.Name) (args : _root_.Lean.TSyntaxArray `term) : _root_.Lean.Syntax.Term :=
  _root_.Lean.Syntax.mkCApp fn args
/--
创建给定种类的字面量。调用者负责确保 `val` 是该种类的合法原子；若提供 `info`，
则用它作为字面量的源信息。
-/
def mkLit (kind : _root_.Lean.SyntaxNodeKind) (val : String)
    (info := _root_.Lean.SourceInfo.none) : _root_.Lean.TSyntax kind :=
  _root_.Lean.Syntax.mkLit kind val info
/-- 创建字符字面量语法；若提供 `info`，则用它作为源信息。 -/
def mkCharLit (val : Char) (info := _root_.Lean.SourceInfo.none) : _root_.Lean.Syntax.CharLit :=
  _root_.Lean.Syntax.mkCharLit val info
/-- 创建字符串字面量语法；若提供 `info`，则用它作为源信息。 -/
def mkStrLit (val : String) (info := _root_.Lean.SourceInfo.none) : _root_.Lean.Syntax.StrLit :=
  _root_.Lean.Syntax.mkStrLit val info
/--
从字符串创建数字字面量语法。调用者必须确保该字符串是 `num` 记号解析器的合法记号；
若提供 `info`，则用它作为源信息。
-/
def mkNumLit (val : String) (info := _root_.Lean.SourceInfo.none) : _root_.Lean.Syntax.NumLit :=
  _root_.Lean.Syntax.mkNumLit val info
/-- 创建自然数字面量语法；若提供 `info`，则用它作为源信息。 -/
def mkNatLit (val : Nat) (info := _root_.Lean.SourceInfo.none) : _root_.Lean.Syntax.NumLit :=
  _root_.Lean.Syntax.mkNatLit val info
/--
创建科学计数法数字字面量语法。调用者必须确保字符串是合法的科学计数法字面量；若提供
`info`，则用它作为源信息。
-/
def mkScientificLit (val : String) (info := _root_.Lean.SourceInfo.none) :
    _root_.Lean.TSyntax _root_.Lean.scientificLitKind :=
  _root_.Lean.Syntax.mkScientificLit val info
/--
创建名称字面量语法。调用者必须确保字符串是合法的名称字面量；若提供 `info`，则用它
作为源信息。
-/
def mkNameLit (val : String) (info := _root_.Lean.SourceInfo.none) : _root_.Lean.Syntax.NameLit :=
  _root_.Lean.Syntax.mkNameLit val info

end Syntax

/-- 创建没有源位置的标识符。若要无捕获地指向特定常量，请改用 `mkCIdent`。 -/
def mkIdent (val : _root_.Lean.Name) : _root_.Lean.Syntax.Ident := _root_.Lean.mkIdent val
/--
创建标识符，并从 `src` 复制位置。若要无变量捕获风险地指向特定常量，请改用
`mkCIdentFrom`。
-/
def mkIdentFrom (src : _root_.Lean.Syntax) (val : _root_.Lean.Name) (canonical := false) :
    _root_.Lean.Syntax.Ident := _root_.Lean.mkIdentFrom src val canonical
/--
创建标识符，并从 `getRef` 返回的语法复制位置。若要无变量捕获风险地指向特定常量，
请改用 `mkCIdentFromRef`。
-/
def mkIdentFromRef {m : Type → Type} [Monad m] [_root_.Lean.MonadRef m]
    (val : _root_.Lean.Name) (canonical := false) : m _root_.Lean.Syntax.Ident :=
  _root_.Lean.mkIdentFromRef val canonical
/-- 创建无源位置且指向常量 `c` 的标识符，并确保它不会意外被捕获。 -/
def mkCIdent (c : _root_.Lean.Name) : _root_.Lean.Syntax.Ident := _root_.Lean.mkCIdent c
/-- 创建指向常量 `c` 的标识符，从 `src` 复制位置，并确保它不会意外被捕获。 -/
def mkCIdentFrom (src : _root_.Lean.Syntax) (c : _root_.Lean.Name) (canonical := false) :
    _root_.Lean.Syntax.Ident := _root_.Lean.mkCIdentFrom src c canonical
/--
创建指向常量 `c` 的标识符，从 `getRef` 返回的语法复制位置，并确保它不会意外被捕获。
-/
def mkCIdentFromRef {m : Type → Type} [Monad m] [_root_.Lean.MonadRef m]
    (c : _root_.Lean.Name) (canonical := false) : m _root_.Lean.Syntax :=
  _root_.Lean.mkCIdentFromRef c canonical
/-- 创建可选节点。可选节点是包含零个或一个元素的空种类节点。 -/
def mkOptionalNode (arg : Option _root_.Lean.Syntax) : _root_.Lean.Syntax :=
  _root_.Lean.mkOptionalNode arg
/-- 创建仿佛由 `Lean.Parser.group` 解析得到的分组节点。 -/
def mkGroupNode (args : Array _root_.Lean.Syntax := #[]) : _root_.Lean.Syntax :=
  _root_.Lean.mkGroupNode args
/-- 创建空洞（`_`），并从 `ref` 复制空洞的位置。 -/
def mkHole (ref : _root_.Lean.Syntax) (canonical := false) : _root_.Lean.Syntax.Term :=
  _root_.Lean.mkHole ref canonical

/--
把运行时值转换为表示该值的表层语法。

实例不必保证结果语法总能重新精译为等价值；例如，语法可以省略通常能够自动找到的
隐式实参。
-/
class Quote (α : Type) (k : _root_.Lean.SyntaxNodeKind := `term) where
  /-- 返回给定值的语法。 -/
  quote : α → _root_.Lean.TSyntax k

namespace TSyntax

/-- 从标识符语法中提取解析后的名称；语法畸形时返回 `Name.anonymous`。 -/
def getId (s : _root_.Lean.Syntax.Ident) : _root_.Lean.Name := _root_.Lean.TSyntax.getId s
/-- 解码带反引号的名称字面量并返回名称；语法畸形时返回 `Lean.Name.anonymous`。 -/
def getName (s : _root_.Lean.Syntax.NameLit) : _root_.Lean.Name := _root_.Lean.TSyntax.getName s
/-- 把数字字面量解释为自然数；语法畸形时返回 `0`。 -/
def getNat (s : _root_.Lean.Syntax.NumLit) : Nat := _root_.Lean.TSyntax.getNat s
/--
提取科学计数法数字字面量的组成部分，返回 `(n, sign, e) : Nat × Bool × Nat`。其值为
`if sign then n * 10 ^ (-e) else n * 10 ^ e`；语法畸形时返回 `(0, false, 0)`。
-/
def getScientific (s : _root_.Lean.Syntax.ScientificLit) : Nat × Bool × Nat :=
  _root_.Lean.TSyntax.getScientific s
/-- 解码字符串字面量，去掉引号并反转义转义字符；语法畸形时返回空字符串。 -/
def getString (s : _root_.Lean.Syntax.StrLit) : String := _root_.Lean.TSyntax.getString s
/-- 解码字符字面量；语法畸形时返回 `(default : Char)`。 -/
def getChar (s : _root_.Lean.Syntax.CharLit) : Char := _root_.Lean.TSyntax.getChar s
/-- 解码宏卫生信息。 -/
def getHygieneInfo (s : _root_.Lean.Syntax.HygieneInfo) : _root_.Lean.Name :=
  _root_.Lean.TSyntax.getHygieneInfo s

end TSyntax

namespace Parser

/--
指定解析表查询函数在遇到标识符时的行为。

`Lean.Parser.prattParser` 分别用一张表保存前导解析器和尾随解析器；表把记号映射到解析器。
关键字记号与标识符记号不同，故即使拼写相同也不会混淆。替代的前导标识符行为提供了
更大的灵活性，使某些场景可以避免保留关键字。

当前导记号在语法上是标识符时，当前语法类别的 `LeadingIdentBehavior` 控制解析表查询，
允许在标识符和关键字之间进行受控的双关。这用于避免为每个内建策略（如 `apply` 或
`assumption`）都创建保留符号，从而让策略名称仍可用作标识符。
-/
inductive LeadingIdentBehavior where
  /-- 若前导记号是标识符，只运行与辅助记号 `ident` 关联的标识符解析器。 -/
  | default
  /--
  若前导标识符为 `<foo>` 且记号 `<foo>` 关联了解析器 `P`，则运行 `P`；否则只运行
  与辅助记号 `ident` 关联的标识符解析器。
  -/
  | symbol
  /--
  若前导记号是标识符 `<foo>`，同时运行与 `<foo>` 关联的解析器以及与辅助记号
  `ident` 关联的标识符解析器。
  -/
  | both

end Parser
end ZhDoc.NotationsMacros
