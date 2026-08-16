/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G4

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w

/-!
本模块为第 19–20 章的列表、字符串与可选值 API 提供中文动态文档载体。
普通定义直接别名到真实声明；归纳类型与结构体逐构造子、逐字段镜像真实声明。
-/

/--
链接列表：有序列表，其中每个元素都有对下一个元素的引用。

链表上的大多数操作所花费的时间与链表的长度成正比，因为每个操作
必须遍历元素才能找到下一个元素。

`List α` 与 `Array α` 同构，但它们用于不同的事情：
* `List α` 更容易推理，而 `Array α` 被建模为 `List α` 的包装器。
* 当共享尾部的许多副本时，`List α` 作为持久数据结构可以很好地工作。当
  该值不共享，`Array α` 将具有更好的性能，因为它可以进行破坏性的操作
  更新。
-/
inductive c001 (α : Type u) where
  /-- 空列表，通常写作 `[]`。

标识符中记法的约定：

 * 标识符中 `[]` 的推荐拼写是 `nil`。 -/
  | nil : c001 α
  /-- 首元素为 `head`、其余部分为 `tail` 的列表。
通常写作 `head :: tail`。

标识符中记法的约定：

 * 标识符中 `::` 的推荐拼写是 `cons`。

 * 标识符中 `[a]` 的推荐拼写是 `singleton`。 -/
  | cons (head : α) (tail : c001 α) : c001 α

/--
构造一个单元素列表。

示例：
* `List.singleton 5 = [5]`。
* `List.singleton "green" = ["green"]`。
* `List.singleton [1, 2, 3] = [[1, 2, 3]]`
-/
def c002 := @List.singleton

/--
将一个元素添加到列表的*末尾*。

添加的元素是结果列​​表的最后一个元素。

示例：
* `List.concat ["red", "yellow"] "green" = ["red", "yellow", "green"]`
* `List.concat [1, 2, 3] 4 = [1, 2, 3, 4]`
* `List.concat [] () = [()]`
-/
def c003 := @List.concat

/--
创建一个包含 `n` 的 `a` 副本的列表。

* `List.replicate 5 "five" = ["five", "five", "five", "five", "five"]`
* `List.replicate 0 "zero" = []`
* `List.replicate 2 ' ' = [' ', ' ']`
-/
def c004 := @List.replicate

/--
创建一个包含 `n` 的 `a` 副本的列表。

这是 `List.replicate` 的尾递归版本。

* `List.replicateTR 5 "five" = ["five", "five", "five", "five", "five"]`
* `List.replicateTR 0 "zero" = []`
* `List.replicateTR 2 ' ' = [' ', ' ']`
-/
def c005 := @List.replicateTR

/--
通过按顺序将 `f` 应用于每个潜在索引（从 `0` 开始）来创建列表。

示例：
* `List.ofFn (n := 3) toString = ["0", "1", "2"]`
* `List.ofFn (fun i => #["red", "green", "blue"].get i.val i.isLt) = ["red", "green", "blue"]`
-/
def c006 := @List.ofFn

/--
附加两个列表。通常通过 `++` 运算符使用。

追加列表所需的时间与第一个列表的长度成正比：`O(|xs|)`。

示例：
* `[1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]`。
* `[] ++ [4, 5] = [4, 5]`。
* `[1, 2, 3] ++ [] = [1, 2, 3]`。
-/
def c007 := @List.append

/--
附加两个列表。通常通过 `++` 运算符使用。

追加列表所需的时间与第一个列表的长度成正比：`O(|xs|)`。

这是 `List.append` 的尾递归版本。

示例：
* `[1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]`。
* `[] ++ [4, 5] = [4, 5]`。
* `[1, 2, 3] ++ [] = [1, 2, 3]`。
-/
def c008 := @List.appendTR

/--
返回从 `0` 到 `n`（不包括）的数字列表，按升序排列。

`O(n)`。

示例：
* `range 5 = [0, 1, 2, 3, 4]`
* `range 0 = []`
* `range 2 = [0, 1]`
-/
def c009 := @List.range

/--
返回具有给定长度 `len` 的数字列表，从 `start` 开始并增加
每个元素处都有 `step`。

换句话说，`List.range' start len step` 是 `[start, start+step, ..., start+(len-1)*step]`。

示例：
 * `List.range' 0 3 (step := 1) = [0, 1, 2]`
 * `List.range' 0 3 (step := 2) = [0, 2, 4]`
 * `List.range' 0 4 (step := 2) = [0, 2, 4, 6]`
 * `List.range' 3 4 (step := 2) = [3, 5, 7, 9]`
-/
def c010 := @List.range'

/--
返回具有给定长度 `len` 的数字列表，从 `start` 开始并增加
每个元素处都有 `step`。

换句话说，`List.range'TR start len step` 是 `[start, start+step, ..., start+(len-1)*step]`。

这是 `List.range'` 的尾递归版本。

示例：
 * `List.range'TR 0 3 (step := 1) = [0, 1, 2]`
 * `List.range'TR 0 3 (step := 2) = [0, 2, 4]`
 * `List.range'TR 0 4 (step := 2) = [0, 2, 4, 6]`
 * `List.range'TR 3 4 (step := 2) = [3, 5, 7, 9]`
-/
def c011 := @List.range'TR

/--
按顺序列出 `Fin n` 的所有元素，从 `0` 开始。

示例：
* `List.finRange 0 = ([] : List (Fin 0))`
* `List.finRange 2 = ([0, 1] : List (Fin 2))`
-/
def c012 := @List.finRange

/--
列表的长度。

该函数在编译器中被重写为 `lengthTR`，它使用常量堆栈空间。

示例：
* `([] : List String).length = 0`
* `["green", "brown"].length = 2`
-/
def c013 := @List.length

/--
列表的长度。

这是`List.length`的尾递归版本，用于实现`List.length`，无需运行
堆栈空间不足。

示例：
 * `([] : List String).lengthTR = 0`
 * `["green", "brown"].lengthTR = 2`
-/
def c014 := @List.lengthTR

/--
检查列表是否为空。

`O(1)`。

示例：
* `[].isEmpty = true`
* `["grape"].isEmpty = false`
* `["apple", "banana"].isEmpty = false`
-/
def c015 := @List.isEmpty

/--
返回非空列表的第一个元素。
-/
def c016 := @List.head

/--
返回列表中的第一个元素（如果有）。如果列表为空，则返回 `none`。

使用 `List.headD` 为空列表提供后备值，或使用 `List.head!` 来对空列表进行恐慌
列表。

示例：
 * `([] : List Nat).head? = none`
 * `[3, 2, 1].head? = some 3`
-/
def c017 := @List.head?

/--
如果有，则返回列表中的第一个元素；如果列表为空，则返回 `fallback`。

使用 `List.head?` 返回 `Option`，并使用 `List.head!` 对空列表进行恐慌。

示例：
* `[].headD "empty" = "empty"`
* `[].headD 2 = 2`
* `["head", "shoulders", "knees"].headD "toes" = "head"`
-/
def c018 := @List.headD

/--
返回列表中的第一个元素。如果列表为空，则会发生恐慌并返回 `default`。

更安全的替代方案包括：
* `List.head`，需要证明列表非空，
* `List.head?`，返回 `Option`，并且
* `List.headD`，它在空列表上返回显式提供的后备值。
-/
def c019 := @List.head!

/--
删除非空列表的第一个元素，返回尾部。当参数为 时，返回 `[]`
空的。

示例：
 * `["apple", "banana", "grape"].tail = ["banana", "grape"]`
 * `["apple"].tail = []`
 * `([] : List String).tail = []`
-/
def c020 := @List.tail

/--
删除非空列表的第一个元素，返回尾部。如果列表为空，则此函数
执行时发生恐慌并返回空列表。

更安全的替代方案包括
 * `tail`，返回空列表而不惊慌，
 * `tail?`，返回 `Option`，并且
 * `tailD`，当传递空列表时返回一个后备值。

示例：
 * `["apple", "banana", "grape"].tail! = ["banana", "grape"]`
 * `["banana", "grape"].tail! = ["grape"]`
-/
def c021 := @List.tail!

/--
删除非空列表的第一个元素，返回尾部。当参数为 时，返回 `none`
空的。

替代方案包括 `List.tail`，它在失败时返回空列表，`List.tailD`，它
返回一个显式后备值和 `List.tail!`，它会在空列表上发生恐慌。

示例：
 * `["apple", "banana", "grape"].tail? = some ["banana", "grape"]`
 * `["apple"].tail? = some []`
 * `([] : List String).tail = none`
-/
def c022 := @List.tail?

/--
删除非空列表的第一个元素，返回尾部。当参数为 时，返回 `none`
空的。

替代方案包括 `List.tail`，它在失败时返回空列表，`List.tail?`，它
返回 `Option` 和 `List.tail!`，这会在空列表上发生恐慌。

示例：
 * `["apple", "banana", "grape"].tailD ["orange"] = ["banana", "grape"]`
 * `["apple"].tailD ["orange"] = []`
 * `[].tailD ["orange"] = ["orange"]`
-/
def c023 := @List.tailD

/--
返回提供的索引处的元素，从 `0` 开始计数。

换句话说，对于 `i : Fin as.length`，`as.get i` 返回列表 `i` 的第 `as` 个元素。
因为索引是一个受列表长度限制的 `Fin`，所以索引永远不会越界。

示例：
 * `["spring", "summer", "fall", "winter"].get (2 : Fin 4) = "fall"`
 * `["spring", "summer", "fall", "winter"].get (0 : Fin 4) = "spring"`
-/
def c024 := @List.get

/--
返回提供的索引处的元素，从 `0` 开始计数。如果索引超出，则返回 `fallback`
的界限。

要根据索引是否在范围内返回 `Option`，请使用 `as[i]?`。恐慌，如果
索引越界，使用`as[i]!`。

示例：
 * `["spring", "summer", "fall", "winter"].getD 2 "never" = "fall"`
 * `["spring", "summer", "fall", "winter"].getD 0 "never" = "spring"`
 * `["spring", "summer", "fall", "winter"].getD 4 "never" = "never"`
-/
def c025 := @List.getD

/--
返回非空列表的最后一个元素。

示例：
* `["circle", "rectangle"].getLast (by decide) = "rectangle"`
* `["circle"].getLast (by decide) = "circle"`
-/
def c026 := @List.getLast

/--
返回列表中的最后一个元素，如果列表为空，则返回 `none` 。

替代方案包括 `List.getLastD`，它采用空列表的后备值，以及
`List.getLast!`，在空列表上会出现恐慌。

示例：
 * `["circle", "rectangle"].getLast? = some "rectangle"`
 * `["circle"].getLast? = some "circle"`
 * `([] : List String).getLast? = none`
-/
def c027 := @List.getLast?

/--
返回列表中的最后一个元素，如果列表为空，则返回 `fallback` 。

替代方案包括 `List.getLast?`（它返回 `Option`）和 `List.getLast!`（它会出现恐慌）
在空列表上。

示例：
 * `["circle", "rectangle"].getLastD "oval" = "rectangle"`
 * `["circle"].getLastD "oval" = "circle"`
 * `([] : List String).getLastD "oval" = "oval"`
-/
def c028 := @List.getLastD

/--
返回列表中的最后一个元素。如果列表为空，则发生恐慌并返回 `default`。

更安全的替代方案包括：
* `getLast?`，返回 `Option`，
* `getLastD`，它采用空列表的后备值，以及
* `getLast`，需要证明列表非空。

示例：
* `["circle", "rectangle"].getLast! = "rectangle"`
* `["circle"].getLast! = "circle"`
-/
def c029 := @List.getLast!

/--
将列表视为将键映射到值的关联列表，返回其键的第一个值
等于指定的键。

`O(|l|)`。

示例：
* `[(1, "one"), (3, "three"), (3, "other")].lookup 3 = some "three"`
* `[(1, "one"), (3, "three"), (3, "other")].lookup 2 = none`
-/
def c030 := @List.lookup

/--
如果不为空则返回列表中最大的元素，如果为空则返回 `none` 。

示例：
* `[].max? = none`
* `[4].max? = some 4`
* `[1, 4, 2, 10, 6].max? = some 10`
-/
def c031 := @List.max?

/--
如果不为空则返回列表的最小元素，如果为空则返回 `none` 。

示例：
* `[].min? = none`
* `[4].min? = some 4`
* `[1, 4, 2, 10, 6].min? = some 1`
-/
def c032 := @List.min?

/--
计算某个元素在列表中出现的次数。

示例：
* `[1, 1, 2, 3, 5].count 1 = 2`
* `[1, 1, 2, 3, 5].count 5 = 1`
* `[1, 1, 2, 3, 5].count 4 = 0`
-/
def c033 := @List.count

/--
计算列表 `l` 中满足布尔谓词 `p` 的元素数量。

示例：
* `[1, 2, 3, 4, 5].countP (· % 2 == 0) = 2`
* `[1, 2, 3, 4, 5].countP (· < 5) = 4`
* `[1, 2, 3, 4, 5].countP (· > 5) = 0`
-/
def c034 := @List.countP

/--
返回第一个等于 `a` 的元素的索引，如果没有元素则返回列表的长度
等于 `a`。

示例：
 * `["carrot", "potato", "broccoli"].idxOf "carrot" = 0`
 * `["carrot", "potato", "broccoli"].idxOf "broccoli" = 2`
 * `["carrot", "potato", "broccoli"].idxOf "tomato" = 3`
 * `["carrot", "potato", "broccoli"].idxOf "anything else" = 3`
-/
def c035 := @List.idxOf

/--
返回等于 `a` 的第一个元素的索引，如果没有元素等于 `none`，则返回 `a`。

示例：
* `["carrot", "potato", "broccoli"].idxOf? "carrot" = some 0`
* `["carrot", "potato", "broccoli"].idxOf? "broccoli" = some 2`
* `["carrot", "potato", "broccoli"].idxOf? "tomato" = none`
* `["carrot", "potato", "broccoli"].idxOf? "anything else" = none`
-/
def c036 := @List.idxOf?

/--
返回第一个等于 `a` 的元素的索引，如果没有元素则返回列表的长度
等于 `a`。该索引以 `Fin` 形式返回，这保证了它在范围内。

示例：
 * `["carrot", "potato", "broccoli"].finIdxOf? "carrot" = some 0`
 * `["carrot", "potato", "broccoli"].finIdxOf? "broccoli" = some 2`
 * `["carrot", "potato", "broccoli"].finIdxOf? "tomato" = none`
 * `["carrot", "potato", "broccoli"].finIdxOf? "anything else" = none`
-/
def c037 := @List.finIdxOf?

/--
返回列表中谓词 `p` 返回 `true` 的第一个元素，如果没有则返回 `none`
找到了这样的元素。

`O(|l|)`。

示例：
* `[7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none`
-/
def c038 := @List.find?

/--
返回 `p` 返回 `true` 的第一个元素的索引，如果没有这样的元素，则返回 `none`
元素。该索引以 `Fin` 形式返回，这保证了它在范围内。

示例：
* `[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 5) = some (4 : Fin 7)`
* `[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 1) = none`
-/
def c039 := @List.findFinIdx?

/--
返回 `p` 返回 `true` 的第一个元素的索引，或者列表的长度（如果）
不存在这样的元素。

示例：
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = 4`
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = 7`
-/
def c040 := @List.findIdx

/--
返回 `p` 返回 `true` 的第一个元素的索引，如果没有这样的元素，则返回 `none`
元素。

示例：
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = some 4`
* `[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = none`
-/
def c041 := @List.findIdx?

/--
返回单子谓词 `p` 返回 `true` 或 `none` 的列表的第一个元素
如果没有找到这样的元素。按顺序检查列表的元素。

`O(|l|)`。

示例：
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
def c042 := @List.findM?

/--
返回按顺序将 `none` 应用到列表中每个元素的第一个非 `f` 结果。退货
`none` 如果 `f` 对列表的所有元素返回 `none`。

`O(|l|)`。

示例：
 * `[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
def c043 := @List.findSome?

/--
返回将一元函数 `none` 应用于每个元素的第一个非 `f` 结果
列表，按顺序。如果 `none` 对所有元素返回 `f`，则返回 `none`。

`O(|l|)`。

示例：
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
def c044 := @List.findSomeM?

/--
将 `List α` 转换为 `Array α`。

`O(|xs|)`。在运行时，该操作由 `List.toArrayImpl` 实现，并且花费的时间与
列表的长度。应使用 `List.toArray` 代替 `Array.mk`。

示例：
 * `[1, 2, 3].toArray = #[1, 2, 3]`
 * `["monday", "wednesday", friday"].toArray = #["monday", "wednesday", friday"].`
-/
def c045 := @List.toArray

/--
通过重复将列表中的元素推入空列表，将 `List α` 转换为 `Array α`
数组。 `O(|xs|)`。

使用 `List.toArray` 而不是直接调用该函数。在运行时，该操作实现
`List.toArray` 和 `Array.mk`。
-/
def c046 := @List.toArrayImpl

/--
将字节列表转换为 `ByteArray`。
-/
def c047 := @List.toByteArray

/--
将浮点数列表转换为 `FloatArray`。
-/
def c048 := @List.toFloatArray

/--
将列表转换为字符串，使用 `ToString.toString` 转换其元素。

生成的字符串类似于列表文字语法，元素由 `", "` 分隔，并且
括在方括号中。

生成的字符串可能不是有效的精益语法，因为没有这样的期望
`ToString` 实例。

示例：
* `[1, 2, 3].toString = "[1, 2, 3]"`
* `["cat", "dog"].toString = "[cat, dog]"`
* `["cat", "dog", ""].toString = "[cat, dog, ]"`
-/
def c049 := @List.toString

/--
稳定的归并排序。

该函数是一个简化的实现，旨在易于推理，而不是
为了效率。特别是，它使用非尾递归 `List.merge` 函数并遍历
不必要地列出。

它在运行时被已被证明等效的高效实现所取代。
-/
def c050 := @List.mergeSort

/--
合并两个列表，如果两者都是，则使用 `le` 选择结果列表的第一个元素
非空。

如果两个输入列表都根据 `le` 排序，则结果列表也根据
至 `le`。 `O(|xs| + |ys|)`。

此实现不是尾递归的，但它在运行时被经过验证的等效实现替换
尾递归合并。
-/
def c051 := @List.merge

/--
返回给定列表的有限迭代器。
迭代器按顺序生成列表的元素，然后终止。

该迭代器的单子版本是 `List.iterM`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c052 := @List.iter

/--
返回给定列表的有限迭代器。
迭代器按顺序生成列表的元素，然后终止。

该迭代器的非单子版本是 `List.iter`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c053 := @List.iterM

/--
按顺序将应用操作 `f` 应用于列表中的每个元素。

如果 `m` 也是 `Monad`，那么使用 `List.forM` 会更高效。

`List.mapA` 是一个收集结果的变体。
-/
def c054 := @List.forA

/--
按顺序将一元操作 `f` 应用于列表中的每个元素。

`List.mapM` 是一个收集结果的变体。 `List.forA` 是一个适用于任何
`Applicative`。
-/
def c055 := @List.forM

/--
将 `f` 映射到列表并使用 `<|>` 收集结果。列表末尾的结果是
`failure`。

示例：
 * `[[], [1, 2], [], [2]].firstM List.head? = some 1`
 * `[[], [], []].firstM List.head? = none`
 * `[].firstM List.head? = none`
-/
def c056 := @List.firstM

/--
计算列表元素的总和。

示例：
* `[a, b, c].sum = a + (b + (c + 0))`
* `[1, 2, 5].sum = 8`
-/
def c057 := @List.sum

/--
将函数从左侧折叠到列表上，累积以 `init` 开头的值。的
累积值使用 `f` 按顺序与列表中的每个元素组合。

示例：
 * `[a, b, c].foldl f z  = f (f (f z a) b) c`
 * `[1, 2, 3].foldl (· ++ toString ·) "" = "123"`
 * `[1, 2, 3].foldl (s!"({·} {·})") "" = "((( 1) 2) 3)"`
-/
def c058 := @List.foldl

/--
将一元函数从左侧折叠到列表上，累积以 `init` 开头的值。的
累积值使用 `f` 按顺序与列表中的每个元素组合。

示例：
```lean example
example [Monad m] (f : α → β → m α) :
    List.foldlM (m := m) f x₀ [a, b, c] = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure x₃)
  := by rfl
```
-/
def c059 := @List.foldlM

/--
通过建立对初始数据成立且被折叠操作保持的不变量，证明有关 `List.foldl` 结果的命题。

此段说明该操作的行为、边界条件及推荐用法。

示例：
```lean example
example {xs : List Nat} : xs.foldl (· + ·) 1 > 0 := by
  apply List.foldlRecOn
  . show 0 < 1; trivial
  . show ∀ (b : Nat), 0 < b → ∀ (a : Nat), a ∈ xs → 0 < b + a
    intros; omega
```
-/
def c060 := @List.foldlRecOn

/--
从右侧折叠列表，以 `init` 为初值，并用 `f` 按逆序把每个元素与累积值结合。

运行时实现具有所述优化与复杂度特性。（相关项：`O(|l|)`、`List.foldrTR`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`[a, b, c].foldr f init  = f a (f b (f c init))`。）
 * 示例见所列代码。（相关项：`[1, 2, 3].foldr (toString · ++ ·) "" = "123"`。）
 * 示例见所列代码。（相关项：`[1, 2, 3].foldr (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`。）
-/
def c061 := @List.foldr

/--
从右侧用单子函数折叠列表，以 `init` 为初值，并用 `f` 按逆序把每个元素与累积值结合。

示例：
```lean example
example [Monad m] (f : α → β → m β) :
  List.foldrM (m := m) f x₀ [a, b, c] = (do
    let x₁ ← f c x₀
    let x₂ ← f b x₁
    let x₃ ← f a x₂
    pure x₃)
  := by rfl
```
-/
def c062 := @List.foldrM

/--
通过建立对初始数据成立且被折叠操作保持的不变量，证明有关 `List.foldr` 结果的命题。

此段说明该操作的行为、边界条件及推荐用法。

示例：
```lean example
example {xs : List Nat} : xs.foldr (· + ·) 1 > 0 := by
  apply List.foldrRecOn
  . show 0 < 1; trivial
  . show ∀ (b : Nat), 0 < b → ∀ (a : Nat), a ∈ xs → 0 < a + b
    intros; omega
```
-/
def c063 := @List.foldrRecOn

/--
从右侧折叠列表，以 `init` 为初值，并用 `f` 按逆序把每个元素与累积值结合。

这是相应函数的尾递归版本，并在运行时代码中使用。（相关项：`O(|l|)`、`List.foldr`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`[a, b, c].foldrTR f init  = f a (f b (f c init))`。）
 * 示例见所列代码。（相关项：`[1, 2, 3].foldrTR (toString · ++ ·) "" = "123"`。）
 * 示例见所列代码。（相关项：`[1, 2, 3].foldrTR (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`。）
-/
def c064 := @List.foldrTR

/--
返回 `l` 中使 `p` 返回 `true` 的元素所组成的列表。

`O(|l|)`.

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filter (· > 2) = [5, 7, 7]`。）
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filter (fun _ => false) = []`。）
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filter (fun _ => true) = [1, 2, 5, 2, 7, 7]`。）
-/
def c065 := @List.filter

/--
返回 `l` 中使 `p` 返回 `true` 的元素所组成的列表。

这是相应函数的尾递归版本，并在运行时代码中使用。（相关项：`O(|l|)`、`List.filter`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filterTR (· > 2)  = [5, 7, 7]`。）
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filterTR (fun _ => false) = []`。）
* 示例见所列代码。（相关项：`[1, 2, 5, 2, 7, 7].filterTR (fun _ => true) = * [1, 2, 5, 2, 7, 7]`。）
-/
def c066 := @List.filterTR

/--
从左到右依次把单子谓词 `p` 应用于列表中的每个元素，并返回使 `p` 返回 `true` 的元素。

`O(|l|)`.

示例：
```lean example
#eval [1, 2, 5, 2, 7, 7].filterM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 1
Checking 2
Checking 5
Checking 2
Checking 7
Checking 7
```
```output
[1, 2, 2]
```
-/
def c067 := @List.filterM

/--
从右到左逆序把单子谓词 `p` 应用于列表中的每个元素，并返回使 `p` 返回 `true` 的元素；结果仍保持输入顺序。

示例：
```lean example
#eval [1, 2, 5, 2, 7, 7].filterRevM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 7
Checking 7
Checking 2
Checking 5
Checking 2
Checking 1
```
```output
[1, 2, 2]
```
-/
def c068 := @List.filterRevM

/--
把返回 `Option` 的函数应用于列表的每个元素，并收集所有非 `none` 值。

`O(|l|)`.

示例：
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMap fun x =>
  if x > 2 then some (2 * x) else none
```
```output
[10, 14, 14]
```
-/
def c069 := @List.filterMap

/--
把返回 `Option` 的函数应用于列表的每个元素，并收集所有非 `none` 值。

这是相应函数的尾递归版本，并在运行时代码中使用。（相关项：`O(|l|)`、`List.filterMap`。）

示例：
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMapTR fun x =>
  if x > 2 then some (2 * x) else none
```
```output
[10, 14, 14]
```
-/
def c070 := @List.filterMapTR

/--
把返回 `Option` 的单子函数应用于列表的每个元素，并收集所有非 `none` 值。

`O(|l|)`.

示例：
```lean example
#eval [1, 2, 5, 2, 7, 7].filterMapM fun x => do
  IO.println s!"Examining {x}"
  if x > 2 then return some (2 * x)
  else return none
```
```output
Examining 1
Examining 2
Examining 5
Examining 2
Examining 7
Examining 7
```
```output
[10, 14, 14]
```
-/
def c071 := @List.filterMapM

/--
使用 `a` 比较元素，检查 `as` 是否属于 `==`。

它与所列操作对应或等价。（相关项：`O(|as|)`、`List.elem`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`l.contains a`、`LawfulBEq α`、`l.contains a = true ↔ a ∈ l`、`l.contains a = false ↔ a ∉ l`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`[1, 4, 2, 3, 3, 7].contains 3 = true`。）
* 示例见所列代码。（相关项：`List.contains [1, 4, 2, 3, 3, 7] 5 = false`。）
-/
def c072 := @List.contains

/--
使用 `a` 比较元素，检查 `l` 是否属于 `==`。

它与所列操作对应或等价。（相关项：`O(|l|)`、`List.contains`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`l.contains a`、`LawfulBEq α`、`l.contains a = true ↔ a ∈ l`、`l.contains a = false ↔ a ∉ l`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`List.elem 3 [1, 4, 2, 3, 3, 7] = true`。）
* 示例见所列代码。（相关项：`List.elem 5 [1, 4, 2, 3, 3, 7] = false`。）
-/
def c073 := @List.elem

/--
若 `true` 对 `p` 的每个元素都返回 `true`，则返回 `l`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`O(|l|)`、`false`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`[a, b, c].all p = (p a && (p b && p c))`。）
* 示例见所列代码。（相关项：`[2, 4, 6].all (· % 2 = 0) = true`。）
* 示例见所列代码。（相关项：`[2, 4, 5, 6].all (· % 2 = 0) = false`。）
-/
def c074 := @List.all

/--
若单子谓词 `p` 对 `true` 的每个元素都返回 `l`，则返回 `O(|l|)`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`false`、`l`、。）
-/
def c075 := @List.allM

/--
若 `true` 对 `p` 的任一元素返回 `true`，则返回 `l`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`O(|l|)`、`true`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`[2, 4, 6].any (· % 2 = 0) = true`。）
* 示例见所列代码。（相关项：`[2, 4, 6].any (· % 2 = 1) = false`。）
* 示例见所列代码。（相关项：`[2, 4, 5, 6].any (· % 2 = 0) = true`。）
* 示例见所列代码。（相关项：`[2, 4, 5, 6].any (· % 2 = 1) = true`。）
-/
def c076 := @List.any

/--
若单子谓词 `p` 对 `true` 的任一元素返回 `l`，则返回 `O(|l|)`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`true`、`l`、。）
-/
def c077 := @List.anyM

/--
若 `true` 中每个元素都是 `bs`，则返回 `true`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`O(|bs|)`、`false`。）

* 示例见所列代码。（相关项：`[true, true, true].and = true`。）
* 示例见所列代码。（相关项：`[true, false, true].and = false`。）
* 示例见所列代码。（相关项：`[true, false, false].and = false`。）
* 示例见所列代码。（相关项：`[].and = true`。）
-/
def c078 := @List.and

/--
若列表 `true` 中存在值 `true`，则返回 `bs`。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。（相关项：`O(|bs|)`、`true`。）

* 示例见所列代码。（相关项：`[true, true, true].or = true`。）
* 示例见所列代码。（相关项：`[true, false, true].or = true`。）
* 示例见所列代码。（相关项：`[false, false, false].or = false`。）
* 示例见所列代码。（相关项：`[false, false, true].or = true`。）
* 示例见所列代码。（相关项：`[].or = false`。）
-/
def c079 := @List.or

/--
为 `l` 的每个元素“附加”它确实属于 `l` 的证明，得到元素相同但位于子类型 `{ x // x ∈ l }` 中的新列表。

`O(1)`.

此函数主要用于良基递归的终止性证明，使迭代操作取得的值能与原参数建立所需关系。（相关项：[相关说明](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=well-founded-recursion)、`List.map`。）
-/
def c080 := @List.attach

/--
为满足谓词 `P` 的值列表逐一“附加”证明，返回相应子类型 `{ x // P x }` 中的元素列表。

`O(1)`.
-/
def c081 := @List.attachWith

/--
忘掉子类型元素满足谓词的证明，把子类型中的项列表映射回原类型中的相应项。

它与所列操作对应或等价。（相关项：`List.attachWith`、`l.map (·.val)`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`map_subtype`、`unattach_attach`。）

此函数主要用于良基递归的终止性证明，使迭代操作取得的值能与原参数建立所需关系。（相关项：[相关说明](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=well-founded-recursion)、`simp [List.unattach, -List.map_subtype]`。）
-/
def c082 := @List.unattach

/--
给定 `α` 的每个元素都满足 `P` 的证明，把只在满足 `l : List α` 的 `l` 项上定义的部分函数映射到 `P` 上。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`O(|l|)`、`List.pmap`、`List.map`。）
-/
def c083 := @List.pmap

/--
返回只含字符 `c` 的新字符串。

此段说明该操作的行为、边界条件及推荐用法。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`String.singleton 'L' = "L"`。）
* 示例见所列代码。（相关项：`String.singleton ' ' = " "`。）
* 示例见所列代码。（相关项：`String.singleton '"' = "\""`。）
* 示例见所列代码。（相关项：`String.singleton '𝒫' = "𝒫"`。）
-/
def c084 := @String.singleton

/--
连接两个字符串，通常通过运算符 `++` 使用。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".append "def" = "abcdef"`。）
* 示例见所列代码。（相关项：`"abc" ++ "def" = "abcdef"`。）
* 示例见所列代码。（相关项：`"" ++ "" = ""`。）
-/
def c085 := @String.append

/--
按顺序连接一个字符串列表中的所有字符串。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.intercalate`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`String.join ["gr", "ee", "n"] = "green"`。）
* 示例见所列代码。（相关项：`String.join ["b", "", "l", "", "ue"] = "blue"`。）
* 示例见所列代码。（相关项：`String.join [] = ""`。）
-/
def c086 := @String.join

/--
连接字符串列表中的字符串，并在每一对相邻字符串之间放置分隔符 `s`。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`", ".intercalate ["red", "green", "blue"] = "red, green, blue"`。）
* 示例见所列代码。（相关项：`" and ".intercalate ["tea", "coffee"] = "tea and coffee"`。）
* 示例见所列代码。（相关项：`" | ".intercalate ["M", "", "N"] = "M |  | N"`。）
-/
def c087 := @String.intercalate

/--
把字符串转换为字符列表。

字符串使用 UTF-8 编码；此操作的时间与空间特性如所述。

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`"abc".toList = ['a', 'b', 'c']`。）
 * 示例见所列代码。（相关项：`"".toList = []`。）
 * 示例见所列代码。（相关项：`"\n".toList = ['\n']`。）
-/
def c088 := @String.toList

/--
检查字符串能否解释为自然数的十进制表示。

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`toNat?`、`toNat!`。）

示例：

* 示例见所列代码。（相关项：`"".isNat = false`。）

* 示例见所列代码。（相关项：`"0".isNat = true`。）

* 示例见所列代码。（相关项：`"5".isNat = true`。）

* 示例见所列代码。（相关项：`"05".isNat = true`。）

* 示例见所列代码。（相关项：`"587".isNat = true`。）

* 示例见所列代码。（相关项：`"-587".isNat = false`。）

* 示例见所列代码。（相关项：`" 5".isNat = false`。）

* 示例见所列代码。（相关项：`"2+3".isNat = false`。）

* 示例见所列代码。（相关项：`"0xff".isNat = false`。）
-/
def c089 := @String.isNat

/--
把字符串解释为自然数的十进制表示并返回该数；若不是十进制自然数则返回 `none`。

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`isNat`、`toNat?`、`some`、`toNat!`、`none`。）

示例：

* 示例见所列代码。（相关项：`"".toNat? = none`。）

* 示例见所列代码。（相关项：`"0".toNat? = some 0`。）

* 示例见所列代码。（相关项：`"5".toNat? = some 5`。）

* 示例见所列代码。（相关项：`"587".toNat? = some 587`。）

* 示例见所列代码。（相关项：`"-587".toNat? = none`。）

* 示例见所列代码。（相关项：`" 5".toNat? = none`。）

* 示例见所列代码。（相关项：`"2+3".toNat? = none`。）

* 示例见所列代码。（相关项：`"0xff".toNat? = none`。）
-/
def c090 := @String.toNat?

/--
把字符串解释为自然数的十进制表示并返回该数；若不是十进制自然数则触发恐慌。

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`isNat`、`toNat!`、`toNat?`、`none`。）

示例：

* 示例见所列代码。（相关项：`"0".toNat! = 0`。）

* 示例见所列代码。（相关项：`"5".toNat! = 5`。）

* 示例见所列代码。（相关项：`"587".toNat! = 587`。）
-/
def c091 := @String.toNat!

/--
检查字符串能否解释为整数的十进制表示。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`-`、`+`。）

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.toInt?`、`String.toInt!`。）

示例：

* 示例见所列代码。（相关项：`"".isInt = false`。）

* 示例见所列代码。（相关项：`"-".isInt = false`。）

* 示例见所列代码。（相关项：`"0".isInt = true`。）

* 示例见所列代码。（相关项：`"-0".isInt = true`。）

* 示例见所列代码。（相关项：`"5".isInt = true`。）

* 示例见所列代码。（相关项：`"587".isInt = true`。）

* 示例见所列代码。（相关项：`"-587".isInt = true`。）

* 示例见所列代码。（相关项：`"+587".isInt = false`。）

* 示例见所列代码。（相关项：`" 5".isInt = false`。）

* 示例见所列代码。（相关项：`"2-3".isInt = false`。）

* 示例见所列代码。（相关项：`"0xff".isInt = false`。）
-/
def c092 := @String.isInt

/--
把字符串解释为整数的十进制表示并返回该数；若不是十进制整数则返回 `none`。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`-`、`+`。）

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.isInt`、`String.toInt?`、`some`、`String.toInt!`、`none`。）

示例：

* 示例见所列代码。（相关项：`"".toInt? = none`。）

* 示例见所列代码。（相关项：`"-".toInt? = none`。）

* 示例见所列代码。（相关项：`"0".toInt? = some 0`。）

* 示例见所列代码。（相关项：`"5".toInt? = some 5`。）

* 示例见所列代码。（相关项：`"-5".toInt? = some (-5)`。）

* 示例见所列代码。（相关项：`"587".toInt? = some 587`。）

* 示例见所列代码。（相关项：`"-587".toInt? = some (-587)`。）

* 示例见所列代码。（相关项：`" 5".toInt? = none`。）

* 示例见所列代码。（相关项：`"2-3".toInt? = none`。）

* 示例见所列代码。（相关项：`"0xff".toInt? = none`。）
-/
def c093 := @String.toInt?

/--
把字符串解释为整数的十进制表示并返回该数；若不是十进制整数则触发恐慌。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`-`、`+`。）

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.isInt`、`String.toInt!`、`String.toInt?`、`none`。）

示例：

* 示例见所列代码。（相关项：`"0".toInt! = 0`。）

* 示例见所列代码。（相关项：`"5".toInt! = 5`。）

* 示例见所列代码。（相关项：`"587".toInt! = 587`。）

* 示例见所列代码。（相关项：`"-587".toInt! = -587`。）
-/
def c094 := @String.toInt!

/--
把字符串转换为美化打印文档，并用 `Std.Format.line` 替换字符串中的换行符。
-/
def c095 := @String.toFormat

/--
检查字符串是否为空。

空串、前缀、后缀及越界情形按所述规则处理。（相关项：`""`、`0`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"".isEmpty = true`。）
* 示例见所列代码。（相关项：`"empty".isEmpty = false`。）
* 示例见所列代码。（相关项：`" ".isEmpty = false`。）
-/
def c096 := @String.isEmpty

/--
返回字符串包含的 Unicode 码位数量。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"".length = 0`。）
* 示例见所列代码。（相关项：`"abc".length = 3`。）
* 示例见所列代码。（相关项：`"L∃∀N".length = 4`。）
-/
def c097 := @String.length

/--
`Pos s` 是 `s` 中的字节偏移，并带有该位置位于 UTF-8 字符边界上的证明。
-/
structure c098 (s : String) where
  /-- `Pos` 的底层字节偏移。 -/
  offset : String.Pos.Raw
  /-- 证明 `offset` 对字符串 `s` 有效。 -/
  isValid : offset.IsValid s

/--
字符串 `s` 的起始位置，表示为 `s.Pos`。
-/
def c099 := @String.startPos

/--
字符串 `s` 的越尾位置，表示为 `s.Pos`。
-/
def c100 := @String.endPos

/--
根据一个位置及其有效性证明，构造 `s` 上的有效位置。
-/
def c101 := @String.pos

/--
根据一个位置构造 `s` 上的有效位置；若该位置无效则返回 `none`。
-/
def c102 := @String.pos?

/--
根据一个位置构造 `s` 上的有效位置；若该位置无效则触发恐慌。
-/
def c103 := @String.pos!

/--
把字符串的一段区域复制到新字符串中。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`s`、`b`、`e`、`String`。）

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`b`、`e`、`""`。）

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`String.slice`。）
-/
def c104 := @String.extract

/--
返回字符串位置 `pos` 处的字符，并要求证明 `p` 不是越尾位置。

运行时代码会用高效实现覆盖此函数。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`("abc".pos ⟨1⟩ (by decide)).get (by decide) = 'b'`。）
* 示例见所列代码。（相关项：`("L∃∀N".pos ⟨1⟩ (by decide)).get (by decide) = '∃'`。）
-/
def c105 := @String.Pos.get

/--
返回字符串位置 `pos` 处的字符；若该位置是越尾位置则触发恐慌。

运行时代码会用高效实现覆盖此函数。
-/
def c106 := @String.Pos.get!

/--
返回字符串位置 `pos` 处的字符；若该位置是越尾位置则返回 `none`。

运行时代码会用高效实现覆盖此函数。
-/
def c107 := @String.Pos.get?

/--
用新字符替换字符串指定位置处的字符。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`("abc".pos ⟨1⟩ (by decide)).set 'B' (by decide) = "aBc"`。）
* 示例见所列代码。（相关项：`("L∃∀N".pos ⟨4⟩ (by decide)).set 'X' (by decide) = "L∃XN"`。）
-/
def c108 := @String.Pos.set

/--
用 `p` 作用于该字符所得的结果，替换字符串 `s` 中位置 `f` 处的字符。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`("abc".pos ⟨1⟩ (by decide)).modify Char.toUpper (by decide) = "aBc"`。）
-/
def c109 := @String.Pos.modify

/--
返回字符串位置 `pos` 处的字节。
-/
def c110 := @String.Pos.byte

/--
返回给定位置之前的有效位置；所给证明保证当前位置不是起始位置，因此前一位置存在。
-/
def c111 := @String.Pos.prev

/--
返回给定位置之前的有效位置；若当前位置是起始位置则触发恐慌。
-/
def c112 := @String.Pos.prev!

/--
返回给定位置之前的有效位置；若当前位置是起始位置则返回 `none`。
-/
def c113 := @String.Pos.prev?

/--
把字符串上的有效位置推进到下一个有效位置；所给证明保证当前位置不是越尾位置，因此下一位置存在。
-/
def c114 := @String.Pos.next

/--
把字符串上的有效位置推进到下一个有效位置；若当前位置是越尾位置则触发恐慌。
-/
def c115 := @String.Pos.next!

/--
把字符串上的有效位置推进到下一个有效位置；若当前位置是越尾位置则返回 `none`。
-/
def c116 := @String.Pos.next?

/--
给定 `t` 的证明，把 `s` 上的有效位置转换为 `s = t` 上的有效位置。
-/
def c117 := @String.Pos.cast

/--
给定切片 `s` 以及 `s.copy` 上的位置，取得 `s` 上的对应位置。
-/
def c118 := @String.Pos.ofCopy

/--
给定字符串中的有效位置，在该位置位于被修改位置之前时，取得设置字符后字符串中的对应位置。
-/
def c119 := @String.Pos.toSetOfLE

/--
给定字符串中的有效位置，在该位置位于被修改位置之前时，取得修改字符后字符串中的对应位置。
-/
def c120 := @String.Pos.toModifyOfLE

/--
把字符串 `s` 上的有效位置转换为切片 `s.toSlice` 上的有效位置。
-/
def c121 := @String.Pos.toSlice

/--
按照 UTF-8 编码表示 `String` 中字节位置的类型。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Nat`、`String`、`String.Pos.Raw`。）

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。（相关项：`p`、`s`、`0 ≤ p ≤ s.rawEndPos`、`p`、`String.Pos.IsValid`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`String.Pos`、`String.Pos`、`String.Pos.Raw`。）
-/
structure c122 where
  /-- 取得 `String.Pos.Raw` 的底层字节索引。 -/
  byteIdx : Nat

/--
返回字符串中给定位置（即 UTF-8 字节索引）对应的字符索引。

在所述条件下，函数按说明返回相应结果或后备结果。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨0⟩ = 0`。）
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨1⟩ = 1`。）
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨2⟩ = 2`。）
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨4⟩ = 2`。）
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨5⟩ = 3`。）
* 示例见所列代码。（相关项：`"L∃∀N".offsetOfPos ⟨50⟩ = 4`。）
-/
def c123 := @String.Pos.Raw.offsetOfPos

/--
若 `true` 是字符串 `p` 中有效的 UTF-8 位置，则返回 `s`。

字符串使用 UTF-8 编码；此操作的时间与空间特性如所述。（相关项：`p ≤ s.rawEndPos`、`p`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`String.Pos.isValid "abc" ⟨0⟩ = true`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "abc" ⟨1⟩ = true`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "abc" ⟨3⟩ = true`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "abc" ⟨4⟩ = false`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "𝒫(A)" ⟨0⟩ = true`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "𝒫(A)" ⟨1⟩ = false`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "𝒫(A)" ⟨2⟩ = false`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "𝒫(A)" ⟨3⟩ = false`。）
 * 示例见所列代码。（相关项：`String.Pos.isValid "𝒫(A)" ⟨4⟩ = true`。）
-/
def c124 := @String.Pos.Raw.isValid

/--
高效检查某位置是否位于切片 `s` 的 UTF-8 字符边界上。
-/
def c125 := @String.Pos.Raw.isValidForSlice

/--
指向字符串末尾、即最后一个字符之后的 UTF-8 字节位置。

* 示例见所列代码。（相关项：`"abc".rawEndPos = ⟨3⟩`。）
* 示例见所列代码。（相关项：`"L∃∀N".rawEndPos = ⟨8⟩`。）
-/
def c126 := @String.rawEndPos

/--
若指定字节位置大于或等于字符串越尾位置则返回 `true`，否则返回 `false`。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`(0 |> "abc".next |> "abc".next |> "abc".atEnd) = false`。）
* 示例见所列代码。（相关项：`(0 |> "abc".next |> "abc".next |> "abc".next |> "abc".next |> "abc".atEnd) = true`。）
* 示例见所列代码。（相关项：`(0 |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".atEnd) = false`。）
* 示例见所列代码。（相关项：`(0 |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".atEnd) = true`。）
* 示例见所列代码。（相关项：`"abc".atEnd ⟨4⟩ = true`。）
* 示例见所列代码。（相关项：`"L∃∀N".atEnd ⟨7⟩ = false`。）
* 示例见所列代码。（相关项：`"L∃∀N".atEnd ⟨8⟩ = true`。）
-/
def c127 := @String.Pos.Raw.atEnd

/--
返回 `p₁` 与 `p₂` 中字节索引较小的一个。
-/
def c128 := @String.Pos.Raw.min

/--
返回位置 `lo` 与 `hi` 所界定字节切片的大小。
-/
def c129 := @String.Pos.Raw.byteDistance

/--
检查两个字符串的子串是否相等；子串由起始位置及其 UTF-8 字节数指定，任一子串不存在时返回 `false`。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`BEq`、`String.Slice`。）
-/
def c130 := @String.Pos.Raw.substrEq

/--
返回字符串中指定位置 `p` 之前的位置。（相关项：`p = ⟨0⟩`、`0`、`p`、`rawEndPos`、`p`、`p`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`"L∃∀N".prev ⟨3⟩`、`⟨1⟩`、`'∃'`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.prev`、`String.Pos.prev?`、`String.pos`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".get ("abc".rawEndPos |> "abc".prev) = 'c'`。）
* 示例见所列代码。（相关项：`"L∃∀N".get ("L∃∀N".rawEndPos |> "L∃∀N".prev |> "L∃∀N".prev |> "L∃∀N".prev) = '∃'`。）
-/
def c131 := @String.Pos.Raw.prev

/--
返回字符串中位置 `p` 之后的下一个位置。（相关项：`p`、`p = s.endPos`、`p`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`p`、`String.next'`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.next`、`String.Pos.next?`、`String.pos`、`String.ValisPos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".next ⟨3⟩ = ⟨4⟩`、`3 = "abc".endPos`。）
* 示例见所列代码。（相关项：`"L∃∀N".next ⟨2⟩ = ⟨3⟩`、`2`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".get ("abc".next 0) = 'b'`。）
* 示例见所列代码。（相关项：`"L∃∀N".get (0 |> "L∃∀N".next |> "L∃∀N".next) = '∀'`。）
-/
def c132 := @String.Pos.Raw.next

/--
返回字符串中位置 `p` 之后的下一个位置；若 `p` 无效，结果未指定。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`h`、`p`、`String.next`。）

```
def next? (s : String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else s.get (s.next' p h)
```

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.next'`、`if`、`String.Pos.next`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`String.pos`。）（相关项：`String.Pos`、`let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'`。）
-/
def c133 := @String.Pos.Raw.next'

/--
像 `String.Pos.Raw.next` 一样反复推进位置，同时谓词 `p` 对当前位置字符返回 `false`；到达末尾或谓词返回 `p` 时停止。（相关项：`true`。）

示例：

* 示例见所列代码。（相关项：`let s := "   a  "; (Pos.Raw.nextUntil s Char.isWhitespace 0).get s = ' '`。）

* 示例见所列代码。（相关项：`let s := "   a  "; (Pos.Raw.nextUntil s Char.isAlpha 0).get s = 'a'`。）

* 示例见所列代码。（相关项：`let s := "a  "; (Pos.Raw.nextUntil s Char.isWhitespace 0).get s = ' '`。）
-/
def c134 := @String.Pos.Raw.nextUntil

/--
像 `String.Pos.Raw.next` 一样反复推进位置，同时谓词 `p` 对当前位置字符返回 `true`；到达末尾或谓词返回 `p` 时停止。（相关项：`false`。）

示例：

* 示例见所列代码。（相关项：`let s := "   a  "; ((0 : Pos.Raw).nextWhile s Char.isWhitespace).get s = 'a'`。）

* 示例见所列代码。（相关项：`let s := "a  "; ((0 : Pos.Raw).nextWhile s Char.isWhitespace).get s = 'a'`。）

* 示例见所列代码。（相关项：`let s := "ba  "; (Pos.Raw.nextWhile s Char.isWhitespace 0).get s = 'b'`。）
-/
def c135 := @String.Pos.Raw.nextWhile

/--
把位置的字节偏移增加 `1`；不要与 `Pos.next` 混淆。
-/
def c136 := @String.Pos.Raw.inc

/--
把 `p` 向前推进 `n` 个字节。（相关项：`HAdd`、`c`、`s`、`p`、`p + c`、`p + s`。）

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`Pos.Raw.offsetBy`。）
-/
def c137 := @String.Pos.Raw.increaseBy

/--
在左侧用 `p` 偏移 `offset`。（相关项：`HAdd`、`c`、`s`、`c + p`、`s + p`。）

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`Pos.Raw.increaseBy`。）
-/
def c138 := @String.Pos.Raw.offsetBy

/--
把位置的字节偏移减少 `1`；不要与 `Pos.prev` 混淆。
-/
def c139 := @String.Pos.Raw.dec

/--
把位置 `p` 向后移动 `n` 个字节。（相关项：`HSub`、`c`、`s`、`p`、`p - c`、`p - s`。）

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`Pos.Raw.unoffsetBy`。）
-/
def c140 := @String.Pos.Raw.decreaseBy

/--
从 `p` 中减去 `offset`。（相关项：`HSub`、`c`、`s`、`p - c`、`p - s`。）

此段说明该操作的行为、边界条件及推荐用法。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`Pos.Raw.decreaseBy`。）
-/
def c141 := @String.Pos.Raw.unoffsetBy

/--
创建一个新字符串，内容为输入字符串中由两个位置界定的区域。

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。（相关项：`""`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.extract`、`String.Slice`、`String.Slice.copy`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "red green blue" ⟨0⟩ ⟨3⟩ = "red"`。）
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "red green blue" ⟨3⟩ ⟨0⟩ = ""`。）
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "red green blue" ⟨0⟩ ⟨100⟩ = "red green blue"`。）
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "red green blue" ⟨4⟩ ⟨100⟩ = "green blue"`。）
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "L∃∀N" ⟨1⟩ ⟨2⟩ = "∃∀N"`。）
* 示例见所列代码。（相关项：`String.Pos.Raw.extract "L∃∀N" ⟨2⟩ ⟨100⟩ = ""`。）
-/
def c142 := @String.Pos.Raw.extract

/--
返回字符串位置 `p` 处的字符；若 `p` 无效，则返回后备值 `(default : Char)`，即 `'A'`，且不触发恐慌。

运行时代码会用高效实现覆盖此函数。（相关项：`String.Pos.Raw.utf8GetAux`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.get`、`String.pos`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".get ⟨1⟩ = 'b'`。）
* 示例见所列代码。（相关项：`"abc".get ⟨3⟩ = (default : Char)`、`3`。）
* 示例见所列代码。（相关项：`"L∃∀N".get ⟨2⟩ = (default : Char)`、`2`、`'∃'`。）
-/
def c143 := @String.Pos.Raw.get

/--
返回字符串位置 `p` 处的字符；若 `p` 无效则触发恐慌。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.pos?`、`String.Pos.get`。）

运行时代码会用高效实现覆盖此函数。（相关项：`String.utf8GetAux`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.get`、`String.pos!`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".get! ⟨1⟩ = 'b'`。）
-/
def c144 := @String.Pos.Raw.get!

/--
返回字符串位置 `p` 处的字符；若 `(default : Char)` 无效，则返回 `'A'`，即 `p`。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`h`、`p`、`String.get`。）

```
def getInBounds? (s : String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else some (s.get' p h)
```
围栏之后的边界情况说明仍适用。（相关项：`get'`、`if`、`¬ s.atEnd p`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`p`、`"L∃∀N".get' ⟨2⟩ (by decide) = (default : Char)`、`String.Pos.get`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`String.pos`。）
* 示例见所列代码。（相关项：`String.Pos`。）（相关项：`"abc".get' 0 (by decide) = 'a'`、`let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'`。）
-/
def c145 := @String.Pos.Raw.get'

/--
返回字符串位置 `p` 处的字符；若 `p` 无效则返回 `none`。

运行时代码会用高效实现覆盖此函数。（相关项：`String.utf8GetAux?`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.get`、`String.pos?`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".get? ⟨1⟩ = some 'b'`。）
* 示例见所列代码。（相关项：`"abc".get? ⟨3⟩ = none`。）
* 示例见所列代码。（相关项：`"L∃∀N".get? ⟨1⟩ = some '∃'`。）
* 示例见所列代码。（相关项：`"L∃∀N".get? ⟨2⟩ = none`。）
-/
def c146 := @String.Pos.Raw.get?

/--
用新字符替换字符串指定位置处的字符；若位置无效，则原样返回字符串。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.set`、`String.pos`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".set ⟨1⟩ 'B' = "aBc"`。）
* 示例见所列代码。（相关项：`"abc".set ⟨3⟩ 'D' = "abc"`。）
* 示例见所列代码。（相关项：`"L∃∀N".set ⟨4⟩ 'X' = "L∃XN"`。）
* 示例见所列代码。（相关项：`"L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"`、`'∃'`、`2`。）
以下列出相应示例或例外情况。
-/
def c147 := @String.Pos.Raw.set

/--
用 `p` 作用于该字符所得的结果替换字符串 `s` 中位置 `f` 处的字符；若 `p` 无效，则原样返回字符串。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos.set`、`String.pos`、`String.Pos`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".modify ⟨1⟩ Char.toUpper = "aBc"`。）
* 示例见所列代码。（相关项：`"abc".modify ⟨3⟩ Char.toUpper = "abc"`。）
-/
def c148 := @String.Pos.Raw.modify

/--
返回包含 `String.Slice` 前 `n` 个字符（Unicode 码位）的 `s`。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`n`、`s.toList.length`、`s.toSlice`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".take 3 == "red".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".take 1 == "r".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".take 0 == "".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".take 100 == "red green blue".toSlice`。）

* 示例见所列代码。（相关项：`"مرحبا بالعالم".take 5 == "مرحبا".toSlice`。）
-/
def c149 := @String.take

/--
创建字符串切片，其中包含 `s` 中 `pat` 能够匹配（可能反复匹配）的最长前缀。

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".takeWhile Char.isLower == "red".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeWhile 'r' == "r".toSlice`。）

* 示例见所列代码。（相关项：`"red red green blue".takeWhile "red " == "red red ".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeWhile (fun (_ : Char) => true) == "red green blue".toSlice`。）
-/
def c150 := @String.takeWhile

/--
返回包含 `String.Slice` 后 `n` 个字符（Unicode 码位）的 `s`。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`n`、`s.toList.length`、`s.toSlice`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".takeEnd 4 == "blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeEnd 1 == "e".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeEnd 0 == "".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeEnd 100 == "red green blue".toSlice`。）

* 示例见所列代码。（相关项：`"مرحبا بالعالم".takeEnd 5 == "لعالم".toSlice`。）
-/
def c151 := @String.takeEnd

/--
创建字符串切片，其中包含 `s` 中 `pat` 能够匹配（可能反复匹配）的最长后缀。

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".takeEndWhile Char.isLower == "blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeEndWhile 'e' == "e".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".takeEndWhile (fun (_ : Char) => true) == "red green blue".toSlice`。）
-/
def c152 := @String.takeEndWhile

/--
返回从字符串开头移除指定数量字符（Unicode 码位）后得到的 `String.Slice`。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`n`、`s.toList.length`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".drop 4 == "green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".drop 10 == "blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".drop 50 == "".toSlice`。）

* 示例见所列代码。（相关项：`"مرحبا بالعالم".drop 3 == "با بالعالم".toSlice`。）
-/
def c153 := @String.drop

/--
创建字符串切片，其中从 `s` 移除了 `pat` 能够匹配（可能反复匹配）的最长前缀。

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropWhile Char.isLower == " green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropWhile 'r' == "ed green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red red green blue".dropWhile "red " == "green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropWhile (fun (_ : Char) => true) == "".toSlice`。）
-/
def c154 := @String.dropWhile

/--
返回从字符串末尾移除指定数量字符（Unicode 码位）后得到的 `String.Slice`。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`n`、`s.toList.length`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".dropEnd 5 == "red green".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropEnd 11 == "red".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropEnd 50 == "".toSlice`。）

* 示例见所列代码。（相关项：`"مرحبا بالعالم".dropEnd 3 == "مرحبا بالع".toSlice`。）
-/
def c155 := @String.dropEnd

/--
创建字符串切片，其中从 `s` 移除了 `pat` 能够匹配（可能反复匹配）的最长后缀。

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropEndWhile Char.isLower == "red green ".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropEndWhile 'e' == "red green blu".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropEndWhile (fun (_ : Char) => true) == "".toSlice`。）
-/
def c156 := @String.dropEndWhile

/--
若 `pat` 匹配 `s` 的前缀，则返回余下部分，否则返回 `none`。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.dropPrefix`、`pat`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropPrefix? "red " == some "green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix? "reed " == none`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix? 'r' == some "ed green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix? Char.isLower == some "ed green blue".toSlice`。）
-/
def c157 := @String.dropPrefix?

/--
若 `pat` 匹配 `s` 的前缀，则返回余下部分，否则原样返回 `s`。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.dropPrefix?`、`none`、`pat`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropPrefix "red " == "green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix "reed " == "red green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix 'r' == "ed green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropPrefix Char.isLower == "ed green blue".toSlice`。）
-/
def c158 := @String.dropPrefix

/--
若 `pat` 匹配 `s` 的后缀，则返回余下部分，否则返回 `none`。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.dropSuffix`、`pat`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropSuffix? " blue" == some "red green".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix? "bluu " == none`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix? 'e' == some "red green blu".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix? Char.isLower == some "red green blu".toSlice`。）
-/
def c159 := @String.dropSuffix?

/--
若 `pat` 匹配 `s` 的后缀，则返回余下部分，否则原样返回 `s`。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`String.dropSuffix?`、`none`、`pat`。）

这是廉价操作，因为它不会为结果分配新字符串；需要字符串时可显式复制切片。（相关项：`String.Slice.copy`。）

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".dropSuffix " blue" == "red green".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix "bluu " == "red green blue".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix 'e' == "red green blu".toSlice`。）

* 示例见所列代码。（相关项：`"red green blue".dropSuffix Char.isLower == "red green blu".toSlice`。）
-/
def c160 := @String.dropSuffix

/--
移除字符串首尾的空白字符。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.isWhitespace`、`true`。）

示例：

* 示例见所列代码。（相关项：`"abc".trimAscii == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"   abc".trimAscii == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"abc \t  ".trimAscii == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"  abc   ".trimAscii == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"abc\ndef\n".trimAscii == "abc\ndef".toSlice`。）
-/
def c161 := @String.trimAscii

/--
返回起始位置为第一个非空白字符的切片，从而移除字符串开头的空白；若不存在非空白字符则以越尾位置为起点。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.isWhitespace`、`true`。）

示例：

* 示例见所列代码。（相关项：`"abc".trimAsciiStart == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"   abc".trimAsciiStart == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"abc \t  ".trimAsciiStart == "abc \t  ".toSlice`。）

* 示例见所列代码。（相关项：`"  abc   ".trimAsciiStart == "abc   ".toSlice`。）

* 示例见所列代码。（相关项：`"abc\ndef\n".trimAsciiStart == "abc\ndef\n".toSlice`。）
-/
def c162 := @String.trimAsciiStart

/--
返回结束位置为最后一个非空白字符之后的切片，从而移除字符串末尾的空白；若不存在非空白字符则以起始位置为终点。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.isWhitespace`、`true`。）

示例：

* 示例见所列代码。（相关项：`"abc".trimAsciiEnd == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"   abc".trimAsciiEnd == "   abc".toSlice`。）

* 示例见所列代码。（相关项：`"abc \t  ".trimAsciiEnd == "abc".toSlice`。）

* 示例见所列代码。（相关项：`"  abc   ".trimAsciiEnd == "  abc".toSlice`。）

* 示例见所列代码。（相关项：`"abc\ndef\n".trimAsciiEnd == "abc\ndef".toSlice`。）
-/
def c163 := @String.trimAsciiEnd

/--
一致地减少字符串各行的缩进：从每行开头移除相同数量的空白，使缩进最少的行不再有前导空白。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`' '`、`'\t'`。）

此段说明该操作的行为、边界条件及推荐用法。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"Here:\n  fun x =>\n    x + 1".removeLeadingSpaces = "Here:\nfun x =>\n  x + 1"`。）
* 示例见所列代码。（相关项：`"Here:\n\t\tfun x =>\n\t  \tx + 1".removeLeadingSpaces = "Here:\nfun x =>\n \tx + 1"`。）
* 示例见所列代码。（相关项：`"Here:\n\t\tfun x =>\n \n\t  \tx + 1".removeLeadingSpaces = "Here:\nfun x =>\n\n \tx + 1"`。）
-/
def c164 := @String.removeLeadingSpaces

/--
返回 `s` 的第一个字符；若 `s = ""`，则返回 `(default : Char)`。

示例：

* 示例见所列代码。（相关项：`"abc".front = 'a'`。）

* 示例见所列代码。（相关项：`"".front = (default : Char)`。）
-/
def c165 := @String.front

/--
返回 `s` 的最后一个字符；若 `s = ""`，则返回 `(default : Char)`。

示例：

* 示例见所列代码。（相关项：`"abc".back = 'c'`。）

* 示例见所列代码。（相关项：`"".back = (default : Char)`。）
-/
def c166 := @String.back

/--
查找切片 `pattern` 中模式 `s` 的第一次匹配位置；若没有匹配则返回 `s.endPos`。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`("coffee tea water".find Char.isWhitespace).get! == ' '`。）

* 示例见所列代码。（相关项：`"tea".find (fun (c : Char) => c == 'X') == "tea".endPos`。）

* 示例见所列代码。（相关项：`("coffee tea water".find "tea").get! == 't'`。）
-/
def c167 := @String.find

/--
从切片末尾向开头遍历，查找模式 `pattern` 在字符串中的第一次匹配位置；若没有匹配则返回 `none`。

此函数对当前支持的所有模式（所列例外除外）都是泛型的。（相关项：`String`、`String.Slice`。）

示例：

* 示例见所列代码。（相关项：`("coffee tea water".toSlice.revFind? Char.isWhitespace).map (·.get!) == some ' '`。）

* 示例见所列代码。（相关项：`"tea".toSlice.revFind? (fun (c : Char) => c == 'X') == none`。）
-/
def c168 := @String.revFind?

/--
检查字符串中任意位置是否存在模式 `pat` 的匹配。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"coffee tea water".contains Char.isWhitespace = true`。）

* 示例见所列代码。（相关项：`"tea".contains (fun (c : Char) => c == 'X') = false`。）

* 示例见所列代码。（相关项：`"coffee tea water".contains "tea" = true`。）
-/
def c169 := @String.contains

/--
构造新字符串，把 `pattern` 中出现的所有 `replacement` 替换为 `s`。

此函数对当前支持的所有模式都是泛型的。（相关项：`String`、`String.Slice`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".replace 'e' "" = "rd grn blu"`。）

* 示例见所列代码。（相关项：`"red green blue".replace (fun c => c == 'u' || c == 'e') "" = "rd grn bl"`。）

* 示例见所列代码。（相关项：`"red green blue".replace "e" "" = "rd grn blu"`。）

* 示例见所列代码。（相关项：`"red green blue".replace "ee" "E" = "red grEn blue"`。）

* 示例见所列代码。（相关项：`"red green blue".replace "e" "E" = "rEd grEEn bluE"`。）

* 示例见所列代码。（相关项：`"aaaaa".replace "aa" "b" = "bba"`。）

* 示例见所列代码。（相关项：`"abc".replace "" "k" = "kakbkck"`。）
-/
def c170 := @String.replace

/--
查找切片 `pattern` 中模式 `s` 的第一次匹配位置；若没有匹配则返回 `s.endPos`。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`("coffee tea water".find Char.isWhitespace).get! == ' '`。）

* 示例见所列代码。（相关项：`"tea".find (fun (c : Char) => c == 'X') == "tea".endPos`。）

* 示例见所列代码。（相关项：`("coffee tea water".find "tea").get! == 't'`。）
-/
def c171 := @String.find

/--
把函数 `f` 应用于字符串中的每个字符，并返回包含所得字符的字符串。

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`"abc123".map Char.toUpper = "ABC123"`。）
 * 示例见所列代码。（相关项：`"".map Char.toUpper = ""`。）
-/
def c172 := @String.map

/--
从开头折叠字符串，以 `init` 为初值，并用 `f` 按顺序把每个字符与累积值结合。

示例：

* 示例见所列代码。（相关项：`"coffee tea water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2`。）

* 示例见所列代码。（相关项：`"coffee tea and water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3`。）

* 示例见所列代码。（相关项：`"coffee tea water".foldl (·.push ·) "" = "coffee tea water"`。）
-/
def c173 := @String.foldl

/--
从右侧折叠字符串，以 `init` 为初值，并用 `f` 按逆序把每个字符与累积值结合。

示例：

* 示例见所列代码。（相关项：`"coffee tea water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2`。）

* 示例见所列代码。（相关项：`"coffee tea and water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3`。）

* 示例见所列代码。（相关项：`"coffee tea water".foldr (fun c s => s.push c) "" = "retaw aet eeffoc"`。）
-/
def c174 := @String.foldr

/--
检查字符串是否完全由模式 `pat` 的匹配组成。

遇到第一个决定结果的值时即短路，并按所述顺序检查元素。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"brown".all Char.isLower = true`。）

* 示例见所列代码。（相关项：`"brown and orange".all Char.isLower = false`。）

* 示例见所列代码。（相关项：`"aaaaaa".all 'a' = true`。）

* 示例见所列代码。（相关项：`"aaaaaa".all "aa" = true`。）

* 示例见所列代码。（相关项：`"aaaaaaa".all "aa" = false`。）
-/
def c175 := @String.all

/--
检查字符串中任意位置是否存在模式 `pat` 的匹配。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"coffee tea water".contains Char.isWhitespace = true`。）

* 示例见所列代码。（相关项：`"tea".contains (fun (c : Char) => c == 'X') = false`。）

* 示例见所列代码。（相关项：`"coffee tea water".contains "tea" = true`。）
-/
def c176 := @String.any

/--
字符串上的非严格不等关系，通常通过运算符 `≤` 使用。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`a ≤ b`、`¬ b < a`。）
-/
def c177 := @String.le

/--
返回两个字符串首次不同的位置。

在所述条件下，函数按说明返回相应结果或后备结果。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"tea".firstDiffPos "ten" = ⟨2⟩`。）
* 示例见所列代码。（相关项：`"tea".firstDiffPos "tea" = ⟨3⟩`。）
* 示例见所列代码。（相关项：`"tea".firstDiffPos "teas" = ⟨3⟩`。）
* 示例见所列代码。（相关项：`"teas".firstDiffPos "tea" = ⟨3⟩`。）
-/
def c178 := @String.firstDiffPos

/--
检查第二个字符串（`s`）是否以某个前缀（`p`）开头。

此函数对当前支持的所有模式都是泛型的。

空串、前缀、后缀及越界情形按所述规则处理。（相关项：`String.startsWith`。）

示例：

* 示例见所列代码。（相关项：`"red".isPrefixOf "red green blue" = true`。）

* 示例见所列代码。（相关项：`"green".isPrefixOf "red green blue" = false`。）

* 示例见所列代码。（相关项：`"".isPrefixOf "red green blue" = true`。）
-/
def c179 := @String.isPrefixOf

/--
检查第一个字符串（`s`）是否以模式（`pat`）开头。

空串、前缀、后缀及越界情形按所述规则处理。（相关项：`String.isPrefixOf`。）

示例：

* 示例见所列代码。（相关项：`"red green blue".startsWith "red" = true`。）

* 示例见所列代码。（相关项：`"red green blue".startsWith "green" = false`。）

* 示例见所列代码。（相关项：`"red green blue".startsWith "" = true`。）

* 示例见所列代码。（相关项：`"red green blue".startsWith 'r' = true`。）

* 示例见所列代码。（相关项：`"red green blue".startsWith Char.isLower = true`。）
-/
def c180 := @String.startsWith

/--
检查字符串（`s`）是否以模式（`pat`）结尾。

此函数对当前支持的所有模式都是泛型的。

示例：

* 示例见所列代码。（相关项：`"red green blue".endsWith "blue" = true`。）

* 示例见所列代码。（相关项：`"red green blue".endsWith "green" = false`。）

* 示例见所列代码。（相关项：`"red green blue".endsWith "" = true`。）

* 示例见所列代码。（相关项：`"red green blue".endsWith 'e' = true`。）

* 示例见所列代码。（相关项：`"red green blue".endsWith Char.isLower = true`。）
-/
def c181 := @String.endsWith

/--
判定两个字符串是否相等，通常通过 `DecidableEq String` 实例和运算符 `=` 使用。

运行时实现具有所述优化与复杂度特性。
-/
def c182 := @String.decEq

/--
计算字符串的哈希值。
-/
def c183 := @String.hash

/--
在 `p` 返回 `true` 的每个字符处拆分字符串。

空串、前缀、后缀及越界情形按所述规则处理。（相关项：`p`、`p`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.split`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"coffee tea water".split (·.isWhitespace) = ["coffee", "tea", "water"]`。）
* 示例见所列代码。（相关项：`"coffee  tea  water".split (·.isWhitespace) = ["coffee", "", "tea", "", "water"]`。）
* 示例见所列代码。（相关项：`"fun x =>\n  x + 1\n".split (· == '\n') = ["fun x =>", "  x + 1", ""]`。）
-/
def c184 := @String.splitToList

/--
在分隔字符串 `s` 每次出现的位置拆分字符串 `sep`；默认分隔符为 `" "`。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`sep`、`[s]`、`sep`、`n+1`、`n`、`sep`。）

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.split`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"here is some text ".splitOn = ["here", "is", "some", "text", ""]`。）
* 示例见所列代码。（相关项：`"here is some text ".splitOn "some" = ["here is ", " text "]`。）
* 示例见所列代码。（相关项：`"here is some text ".splitOn "" = ["here is some text "]`。）
* 示例见所列代码。（相关项：`"ababacabac".splitOn "aba" = ["", "bac", "c"]`。）
-/
def c185 := @String.splitOn

/--
在字符串末尾添加一个字符。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".push 'd' = "abcd"`。）
* 示例见所列代码。（相关项：`"".push 'a' = "a"`。）
-/
def c186 := @String.push

/--
在字符串末尾添加一个字符的多次重复。

若相关字符串未被共享，实现会尽可能进行原地更新而不复制。（相关项：`s`、`n`、`c`、`String.push`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`"indeed".pushn '!' 2 = "indeed!!"`。）
 * 示例见所列代码。（相关项：`"indeed".pushn '!' 0 = "indeed"`。）
 * 示例见所列代码。（相关项：`"".pushn ' ' 4 = "    "`。）
-/
def c187 := @String.pushn

/--
把 `s` 的第一个字符替换为对它应用 `Char.toUpper` 的结果；若字符串为空则返回空字符串。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.toUpper`、`'a'`、`'z'`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"orange".capitalize = "Orange"`。）
* 示例见所列代码。（相关项：`"ORANGE".capitalize = "ORANGE"`。）
* 示例见所列代码。（相关项：`"".capitalize = ""`。）
-/
def c188 := @String.capitalize

/--
把 `s` 的第一个字符替换为对它应用 `Char.toLower` 的结果；若字符串为空则返回空字符串。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.toLower`、`'A'`、`'Z'`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"Orange".decapitalize = "orange"`。）
* 示例见所列代码。（相关项：`"ORANGE".decapitalize = "oRANGE"`。）
* 示例见所列代码。（相关项：`"".decapitalize = ""`。）
-/
def c189 := @String.decapitalize

/--
把 `s` 的每个字符替换为对它应用 `Char.toUpper` 的结果。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.toUpper`、`'a'`、`'z'`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"orange".toUpper = "ORANGE"`。）
* 示例见所列代码。（相关项：`"abc123".toUpper = "ABC123"`。）
-/
def c190 := @String.toUpper

/--
把 `s` 的每个字符替换为对它应用 `Char.toLower` 的结果。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`Char.toLower`、`'A'`、`'Z'`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"ORANGE".toLower = "orange"`。）
* 示例见所列代码。（相关项：`"Orange".toLower = "orange"`。）
* 示例见所列代码。（相关项：`"ABc123".toLower = "abc123"`。）
-/
def c191 := @String.toLower

/--
遍历 `String` 中字符（Unicode 码位）的迭代器，通常由 `String.iter` 创建。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos`、`s`、`p : s.startPos`、`p.next`、`p.get`、`p = s.endPos`、`p.IsAtEnd`。）

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。（相关项：`i`、`s`、`0 ≤ i ≤ s.rawEndPos`、`i`、`i = s.rawEndPos`。）

以下列出相应示例或例外情况。
以下列出相应示例或例外情况。（相关项：`String.Iterator`。）
- 示例见所列代码。（相关项：`Iterator.next iter`、`iter`、`iter.atEnd`。）
以下列出相应示例或例外情况。（相关项：`true`。）
- 示例见所列代码。（相关项：`Iterator.forward iter n`、`Iterator.nextn iter n`、`n`。）
以下列出相应示例或例外情况。
-/
structure c192 where
  /-- 正在迭代的字符串。 -/
  s : String
  /-- 字符串 `s` 中当前的 UTF-8 字节位置。

不保证此位置对字符串有效。若位置无效，则当前字符为 `(default : Char)`，类似于在无效位置调用 `String.get`。 -/
  i : String.Pos.Raw

/--
创建位于字符串开头的迭代器。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos`、`s`、`p : s.startPos`、`p.next`、`p.get`、`p = s.endPos`、`p.IsAtEnd`。）
-/
def c193 := @String.Legacy.iter

/--
创建位于字符串开头的迭代器。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos`、`s`、`p : s.startPos`、`p.next`、`p.get`、`p = s.endPos`、`p.IsAtEnd`。）
-/
def c194 := @String.Legacy.mkIterator

/--
取得迭代器当前位置处的字符。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos`、`s`、`p : s.startPos`、`p.next`、`p.get`、`p = s.endPos`、`p.IsAtEnd`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`String.Iterator.curr'`。）

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`(default : Char)`。）
-/
def c195 := @String.Legacy.Iterator.curr

/--
取得迭代器当前位置处的字符。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`it.hasNext`、`String.Iterator.curr`。）
-/
def c196 := @String.Legacy.Iterator.curr'

/--
检查迭代器是否位于字符串最后一个字符处或其之前。
-/
def c197 := @String.Legacy.Iterator.hasNext

/--
无条件把迭代器位置向前移动一个字符。

这是旧版 API，未来版本将移除；应优先使用所列的更安全替代方案。（相关项：`String.Pos`、`s`、`p : s.startPos`、`p.next`、`p.get`、`p = s.endPos`、`p.IsAtEnd`。）

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。（相关项：`Iterator.atEnd`、`false`。）
-/
def c198 := @String.Legacy.Iterator.next

/--
无条件把迭代器位置向前移动一个字符。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`it.hasNext`、`String.Iterator.next`。）
-/
def c199 := @String.Legacy.Iterator.next'

/--
把迭代器位置向前移动指定数量的字符。

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。
-/
def c200 := @String.Legacy.Iterator.forward

/--
把迭代器位置向前移动指定数量的字符。

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。
-/
def c201 := @String.Legacy.Iterator.nextn

/--
检查迭代器是否已越过字符串开头。
-/
def c202 := @String.Legacy.Iterator.hasPrev

/--
无条件把迭代器位置向后移动一个字符。

此段说明该操作的行为、边界条件及推荐用法。
-/
def c203 := @String.Legacy.Iterator.prev

/--
把迭代器位置向后移动指定数量的字符，并在字符串开头停止。
-/
def c204 := @String.Legacy.Iterator.prevn

/--
检查迭代器是否已越过其字符串的最后一个字符。
-/
def c205 := @String.Legacy.Iterator.atEnd

/--
把迭代器位置移到字符串末尾，即最后一个字符之后。
-/
def c206 := @String.Legacy.Iterator.toEnd

/--
替换字符串中的当前字符。

此段说明该操作的行为、边界条件及推荐用法。
-/
def c207 := @String.Legacy.Iterator.setCurr

/--
向前移动迭代器，直到布尔谓词 `p` 对当前字符返回 `true`，或到达字符串末尾；若当前字符已经满足 `p`，则不做任何操作。
-/
def c208 := @String.Legacy.Iterator.find

/--
遍历字符串，在每个字符处用给定函数 `f` 更新状态，直到 `f` 返回 `none`；初始状态为 `init`。（相关项：`f`、`none`。）
-/
def c209 := @String.Legacy.Iterator.foldUntil

/--
提取两个迭代器位置之间的子串；第一个位置为子串开头，第二个位置为子串结尾。

空串、前缀、后缀及越界情形按所述规则处理。
-/
def c210 := @String.Legacy.Iterator.extract

/--
以字符串形式返回迭代器中余下的字符。
-/
def c211 := @String.Legacy.Iterator.remainingToString

/--
返回迭代器中余下的 UTF-8 字节数。
-/
def c212 := @String.Legacy.Iterator.remainingBytes

/--
字符串 `s` 中当前的 UTF-8 字节位置。

位置或迭代器仅在满足所述边界与 UTF-8 字符边界条件时有效；无效输入的结果按说明处理。（相关项：`(default : Char)`、`String.get`。）
-/
def c213 := @String.Legacy.Iterator.pos

/--
正在迭代的字符串。
-/
def c214 := @String.Legacy.Iterator.toString

/--
把字符串转换为 Lean 编译器使用的名称表示；所得名称具有层次结构，并在点号（`'.'`）处拆分字符串。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`"a.b".toName`、`a.b`、`«a.b»`、`Name.mkSimple`。）
-/
def c215 := @String.toName

/--
把字符串转换为相应的 Lean 字符串字面量语法：两端添加双引号，并按需转义内部字符。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`"abc".quote = "\"abc\""`。）
* 示例见所列代码。（相关项：`"\"".quote = "\"\\\"\""`。）
-/
def c216 := @String.quote

/--
访问字符串 UTF-8 编码中指定的字节。

运行时代码会用高效实现覆盖此函数。
-/
def c217 := @String.getUTF8Byte

/--
返回字符串的 UTF-8 编码所占的字节数。

运行时实现具有所述优化与复杂度特性。
-/
def c218 := @String.utf8ByteSize

/--
返回字符的 UTF-8 编码中的字节序列。
-/
def c219 := @String.utf8EncodeChar

/--
把以 UTF-8 编码字符串的字节数组解码为相应字符串。（相关项：[相关说明](https://en.wikipedia.org/wiki/UTF-8)。）
-/
def c220 := @String.fromUTF8

/--
把以 UTF-8 编码字符串的字节数组解码为相应字符串；若数组不是有效的 UTF-8 字符串编码则返回 `none`。（相关项：[相关说明](https://en.wikipedia.org/wiki/UTF-8)。）
-/
def c221 := @String.fromUTF8?

/--
把以 UTF-8 编码字符串的字节数组解码为相应字符串；若数组不是有效的 UTF-8 字符串编码则触发恐慌。（相关项：[相关说明](https://en.wikipedia.org/wiki/UTF-8)。）
-/
def c222 := @String.fromUTF8!

/--
把字符串编码为 UTF-8 字节数组。
-/
def c223 := @String.toUTF8

/--
把每个 `\r\n` 替换为 `\n` 以规范化行尾，但不检查是否存在孤立的 `\r` 字符。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`String.replace text "\r\n" "\n"`。）
-/
def c224 := @String.crlfToLf

/--
可选值：要么是用 `some` 包裹的底层类型值，要么是 `none`。

对 `Option` 的  与  两种情形，结果按所述规则确定。
-/
inductive c225 (α : Type u) where
  /-- 没有值。 -/
  | none : c225 α
  /-- 某个类型为 `α` 的值。 -/
  | some (val : α) : c225 α

/--
从可证明为 `some` 的可选值中提取其值。
-/
def c226 := @Option.get

/--
从 `Option` 中提取值；遇到 `none` 时触发恐慌。
-/
def c227 := @Option.get!

/--
取得可选值；遇到 `none` 时返回给定的默认值。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`@[macro_inline]`、`dflt`、`opt`、`none`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`(some "hello").getD "goodbye" = "hello"`。）
 * 示例见所列代码。（相关项：`none.getD "goodbye" = "goodbye"`。）
-/
def c228 := @Option.getD

/--
取得可选值；遇到 `none` 时以单子方式计算默认值。

它与所列操作对应或等价。（相关项：`Option.getD`。）
-/
def c229 := @Option.getDM

/--
把可选值提升到任意 `Alternative` 中，并把 `none` 送到 `failure`。
-/
def c230 := @Option.getM

/--
对 `Option` 进行分类讨论的函数。

对 `none` 的 `some` 与 `Option.elim` 两种情形，结果按所述规则确定。（相关项：`Option`。）

对 `Option.elim` 的 `Option` 与 `Option.recOn` 两种情形，结果按所述规则确定。（相关项：`Option.map`、`Option.getD`、`(some "hello").elim 0 String.length = 5`、`none.elim 0 String.length = 0`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：。）
 * 示例见所列代码。（相关项：。）
-/
def c231 := @Option.elim

/--
对 `Option` 进行单子式分类讨论的函数。

对 `none` 的 `some` 与 `Option.elimM` 两种情形，结果按所述规则确定。（相关项：`Option`。）

它与所列操作对应或等价。（相关项：`Option.elimM`、`Option.mapM`、`Option.getDM`、`Option.elim`。）
-/
def c232 := @Option.elimM

/--
若两个可选值都存在，则对它们应用函数；否则若仅有一个值存在，就返回该值且不使用函数。

对 `some (fn a b)` 的 `some a` 与 `some b` 两种情形，结果按所述规则确定。（相关项：`Option.orElse`、`some x`、`some x`、`none`、`none`、`Option.merge (· + ·) none (some 3) = some 3`、`Option.merge (· + ·) (some 2) (some 3) = some 5`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`Option.merge (· + ·) (some 2) none = some 2`。）
 * 示例见所列代码。（相关项：`Option.merge (· + ·) none none = none`。）
 * 示例见所列代码。（相关项：。）
 * 示例见所列代码。（相关项：。）
-/
def c233 := @Option.merge

/--
对 `true` 返回 `none`，对 `false` 返回 `some x`。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`(· == none)`、`BEq α`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`(none : Option Nat).isNone = true`。）
* 示例见所列代码。（相关项：`(some Nat.add).isNone = false`。）
-/
def c234 := @Option.isNone

/--
对 `true` 返回 `some x`，对 `false` 返回 `none`。
-/
def c235 := @Option.isSome

/--
检查可选值是否既存在又等于另一个值。

对 `x? : Option α` 的 `y : α` 与 `x?.isEqSome y` 两种情形，结果按所述规则确定。（相关项：`x? == some y`、、、。）
-/
def c236 := @Option.isEqSome

/--
两个可选值的最小值，并把 `none` 视为最小元素。（相关项：`Min (Option α)`。）

此段说明该操作的行为、边界条件及推荐用法。（相关项：`nightly-2025-02-27`、`none`、`min none (some x) = min (some x) none = some x`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`Option.min (some 2) (some 5) = some 2`。）
 * 示例见所列代码。（相关项：`Option.min (some 5) (some 2) = some 2`。）
 * 示例见所列代码。（相关项：`Option.min (some 2) none = none`。）
 * 示例见所列代码。（相关项：`Option.min none (some 5) = none`。）
 * 示例见所列代码。（相关项：`Option.min none none = none`。）
-/
def c237 := @Option.min

/--
两个可选值的最大值。

通常通过所列实例、运算符或字段记法使用此函数。（相关项：`Max (Option α)`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`Option.max (some 2) (some 5) = some 5`。）
* 示例见所列代码。（相关项：`Option.max (some 5) (some 2) = some 5`。）
* 示例见所列代码。（相关项：`Option.max (some 2) none = some 2`。）
* 示例见所列代码。（相关项：`Option.max none (some 5) = some 5`。）
* 示例见所列代码。（相关项：`Option.max none none = none`。）
-/
def c238 := @Option.max

/--
把次序关系提升到 `Option`，并把 `none` 作为最小元素。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`none`、`α`、`β`。）

对 `LT (Option α)` 的 `Option.lt (fun n k : Nat => n < k) none none = False` 与 `Option.lt (fun n k : Nat => n < k) none (some 3) = True` 两种情形，结果按所述规则确定。（相关项：`Option.lt (fun n k : Nat => n < k) (some 3) none = False`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`Option.lt (fun n k : Nat => n < k) (some 4) (some 5) = True`。）
 * 示例见所列代码。（相关项：`Option.lt (fun n k : Nat => n < k) (some 4) (some 4) = False`。）
 * 示例见所列代码。（相关项：。）
 * 示例见所列代码。（相关项：。）
 * 示例见所列代码。（相关项：。）
-/
def c239 := @Option.lt

/--
即使被包裹类型没有可判定相等性，与 `none` 的相等性仍然可判定。
-/
def c240 := @Option.decidableEqNone

/--
把可选值转换为含零个或一个元素的数组。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`(some "value").toArray = #["value"]`。）
* 示例见所列代码。（相关项：`none.toArray = #[]`。）
-/
def c241 := @Option.toArray

/--
把可选值转换为含零个或一个元素的列表。

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`(some "value").toList = ["value"]`。）
* 示例见所列代码。（相关项：`none.toList = []`。）
-/
def c242 := @Option.toList

/--
返回可选值的一种表示，它应能被解析为等价的可选值。

通常通过所列实例、运算符或字段记法使用此函数。（相关项：`Repr (Option α)`。）
-/
def c243 := @Option.repr

/--
格式化可选值，不要求 Lean 解析器能够解析结果。

通常通过所列实例、运算符或字段记法使用此函数。（相关项：`ToFormat (Option α)`。）
-/
def c244 := @Option.format

/--
若值不满足布尔谓词则返回 `none`，否则返回该值本身。

把 `Option` 看作可能失败的计算或至多含一个元素的容器时，此操作具有所述对应含义。（相关项：`Option`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`Option.guard (· > 2) 1 = none`。）
 * 示例见所列代码。（相关项：`Option.guard (· > 2) 5 = some 5`。）
-/
def c245 := @Option.guard

/--
对 `Option` 计算进行顺序组合。

把 `Option` 看作可能失败的计算或至多含一个元素的容器时，此操作具有所述对应含义。（相关项：`Option`。）

通常通过所列实例、运算符或字段记法使用此函数。（相关项：`>>=`、`Bind (Option α)`、`do`、[相关说明](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=generalized-field-notation)。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`none.bind (fun x => some x) = none`。）
 * 示例见所列代码。（相关项：`(some 4).bind (fun x => some x) = some 4`。）
 * 示例见所列代码。（相关项：`none.bind (Option.guard (· > 2)) = none`。）
 * 示例见所列代码。（相关项：`(some 2).bind (Option.guard (· > 2)) = none`。）
 * 示例见所列代码。（相关项：`(some 4).bind (Option.guard (· > 2)) = some 4`。）
-/
def c246 := @Option.bind

/--
若 `f` 中存在值，则在该值上运行单子动作 `o` 并返回结果；否则返回 `none`。

把 `Option` 看作可能失败的计算或至多含一个元素的容器时，此操作具有所述对应含义。
-/
def c247 := @Option.bindM

/--
展平嵌套的可选值，并保留其中找到的值。

它与所列操作对应或等价。（相关项：`List.flatten`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`none.join = none`。）
* 示例见所列代码。（相关项：`(some none).join = none`。）
* 示例见所列代码。（相关项：`(some (some v)).join = some v`。）
-/
def c248 := @Option.join

/--
把可选的单子计算转换为返回可选值的单子计算。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`m`。）

示例：
```lean example
#eval show IO (Option String) from
  Option.sequence <| some do
    IO.println "hello"
    return "world"
```
```output
hello
```
```output
some "world"
```
-/
def c249 := @Option.sequence

/--
用处理函数从失败的 `Option` 计算中恢复。

通常通过所列实例、运算符或字段记法使用此函数。（相关项：`MonadExceptOf Unit Option`。）

以下列出相应示例或例外情况。
* 示例见所列代码。（相关项：`Option.tryCatch none (fun () => some "handled") = some "handled"`。）
* 示例见所列代码。（相关项：`Option.tryCatch (some "succeeded") (fun () => some "handled") = some "succeeded"`。）
-/
def c250 := @Option.tryCatch

/--
返回参数中第一个为 `some` 的值；若两者都不是 `none` 则返回 `some`。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`<|>`、`OrElse.orElse`。）
-/
def c251 := @Option.or

/--
为 `OrElse` 实现 `<|>` 的 `Option` 语法；若第一个参数是 `some a` 则返回 `some a`，否则求值并返回第二个参数。

可使用所列 API 完成检查、转换或采用更安全的替代方式。（相关项：`or`。）
-/
def c252 := @Option.orElse

/--
检查可选值是否为 `none`，或满足某个布尔谓词。

以下列出相应示例或例外情况。
* 示例见所列代码。
* 示例见所列代码。
* 示例见所列代码。
-/
def c253 := @Option.all

/--
检查可选值是否不是 `none` 且满足某个布尔谓词。

以下列出相应示例或例外情况。
* 示例见所列代码。
* 示例见所列代码。
* 示例见所列代码。
-/
def c254 := @Option.any

/--
仅当可选值满足布尔谓词时才保留它。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`Option`、`Option.filter`、`List.filter`、`Array.filter`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`(some 5).filter (· % 2 == 0) = none`。）
 * 示例见所列代码。（相关项：`(some 4).filter (· % 2 == 0) = some 4`。）
 * 示例见所列代码。（相关项：`none.filter (fun x : Nat => x % 2 == 0) = none`。）
 * 示例见所列代码。（相关项：`none.filter (fun x : Nat => true) = none`。）
-/
def c255 := @Option.filter

/--
仅当可选值满足单子布尔谓词时才保留它。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`Option`、`Option.filterM`、`List.filterM`。）
-/
def c256 := @Option.filterM

/--
若可选值存在，则在其上执行单子动作；若不存在值则不做任何操作。

示例：
```lean example
#eval ((some 5).forM set : StateM Nat Unit).run 0
```
```output
((), 5)
```
```lean example
#eval (none.forM (fun x : Nat => set x) : StateM Nat Unit).run 0
```
```output
((), 0)
```
-/
def c257 := @Option.forM

/--
若可选值存在，则对其应用函数。

把 `Option` 看作可能失败的计算或至多含一个元素的容器时，此操作具有所述对应含义。（相关项：`List.map`、`Functor Option`。）

以下列出相应示例或例外情况。
 * 示例见所列代码。（相关项：`(none : Option Nat).map (· + 1) = none`。）
 * 示例见所列代码。（相关项：`(some 3).map (· + 1) = some 4`。）
-/
def c258 := @Option.map

/--
把某个应用函子中的函数应用于可选值；若值缺失，则无效果地返回 `none`。

它与所列操作对应或等价。（相关项：`Option.mapM`。）
-/
def c259 := @Option.mapA

/--
把某个应用函子中的函数应用于可选值；若值缺失，则无效果地返回 `none`。

此段说明该操作的行为、边界条件及推荐用法。（相关项：`f`、`none`、`none`。）

把 `Option` 看作可能失败的计算或至多含一个元素的容器时，此操作具有所述对应含义。（相关项：`List.mapM`。）

它与所列操作对应或等价。（相关项：`m`、`Option.mapA`。）
-/
def c260 := @Option.mapM

/--
为存在的可选值“附加”它确实就是该值的证明，并返回表达这一事实的子类型。

此函数主要用于良基递归的终止性证明，使迭代操作取得的值能与原参数建立所需关系。（相关项：`Option.map`。）
-/
def c261 := @Option.attach

/--
为存在的可选值“附加”某谓词成立的证明，并返回表达这一事实的子类型。

此函数主要用于良基递归的终止性证明，使迭代操作取得的值能与原参数建立所需关系。（相关项：`Option.attach`、`Option.map`。）
-/
def c262 := @Option.attachWith

/--
移除 `Option` 中的值确实就是该值的附加证明。

此函数主要用于良基递归的终止性证明，使迭代操作取得的值能与原参数建立所需关系。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`simp [Option.unattach, -Option.map_subtype]`。）

它与所列操作对应或等价。（相关项：`Option.map Subtype.val`。）
-/
def c263 := @Option.unattach

/--
给定类型的一个可选任意元素。

在所述条件下，函数按说明返回相应结果或后备结果。（相关项：`α`、`v : α`、`some v`、`none`。）
-/
noncomputable def c264 := @Option.choice

/--
给定一个可选值以及仅当该值为 `some` 时才能应用的函数，在可能时返回应用该函数的结果。

运行时实现具有所述优化与复杂度特性。（相关项：`f`、`a : α`、`o = some a`、`o`、`none`、`o`、`Option.bind`。）

示例：
```lean example
def attach (v : Option α) : Option { y : α // v = some y } :=
  v.pbind fun x h => some ⟨x, h⟩
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
def c265 := @Option.pbind

/--
给定一个可选值以及仅当该值为 `some` 时才能应用的函数，在可能时返回应用结果，否则返回后备值。

运行时实现具有所述优化与复杂度特性。（相关项：`f`、`a : α`、`o = some a`、`o`、`none`、`o`、`Option.elim`。）

示例：
```lean example
def attach (v : Option α) : Option { y : α // v = some y } :=
  v.pelim none fun x h => some ⟨x, h⟩
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
def c266 := @Option.pelim

/--
给定从 `α` 中满足 `p` 的元素到 `β` 的函数，以及可选值存在时满足 `p` 的证明，把该函数应用于这个值。

示例：
```lean example
def attach (v : Option α) : Option { y : α // v = some y } :=
  v.pmap (fun a (h : a ∈ v) => ⟨_, h⟩) (fun _ h => h)
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
def c267 := @Option.pmap

end Manual.ZhDocString.Ch19Ch20.G4
