/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Manual.ZhDocString.ZhDocString
import Std.Data.TreeSet
import Std.Data.TreeSet.Raw

namespace Manual.ZhDocString.Ch19Ch20.G3

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w

/-!
本模块为第 19–20 章的数组、树集合、列表修改与积类型 API 提供中文动态文档载体。
普通定义直接别名到真实声明；结构体逐字段镜像真实声明，以便动态文档渲染器核对形状。
-/

/--
`Array α` 是[动态数组](https://en.wikipedia.org/wiki/Dynamic_array) 的类型，其中元素来自 `α`。该类型在运行时有特殊支持。

数组在不共享时性能最佳。只要对数组的引用不超过一次，所有更新都将_破坏性地_执行。这导致性能与命令式编程语言中的可变数组相当。

数组有大小和容量。大小是数组中存在的元素数量，而容量是当前为元素分配的内存量。可以通过 `Array.size` 访问大小，但无法从Lean 代码中观察到容量。 `Array.emptyWithCapacity n` 创建一个等于 `#[]` 的数组，但内部分配了一个容量为 `n` 的数组。当大小超过容量时，需要分配以扩大数组。

从证明的角度来看，`Array α` 只是 `List α` 的包装。
-/
structure c001 (α : Type u) where
  /--
  将 `Array α` 转换为按相同顺序包含相同元素的 `List α`。

  在运行时，它由 `Array.toListImpl` 实现，其时间复杂度关于数组长度为 `O(n)`。
  -/
  toList : List α

/--
将 `List α` 转换为 `Array α`。

推荐使用函数 `List.toArray`。

在运行时，该构造子由 `List.toArrayImpl` 覆盖，其时间复杂度关于列表长度为 `O(n)`。
-/
add_decl_doc c001.mk

/--
构造一个新的空数组，初始容量为 `0`。

使用`Array.emptyWithCapacity`创建具有更大初始容量的阵列。
-/
def c002 := @Array.empty

/--
构造一个新的空数组，初始容量为 `c`。
-/
def c003 := @Array.emptyWithCapacity

/--
构造一个包含 `v` 的单元素数组。

示例：
* `Array.singleton 5 = #[5]`
* `Array.singleton "one" = #["one"]`
-/
def c004 := @Array.singleton

/--
构造一个数组，其中包含从 `0` 到 `n` 的所有数字（不包括）。

示例：
* `Array.range 5 := #[0, 1, 2, 3, 4]`
* `Array.range 0 := #[]`
* `Array.range 1 := #[0]`
-/
def c005 := @Array.range

/--
构造一个大小为 `size` 的数字数组，从 `start` 开始，每个元素增加 `step`。

换句话说，`Array.range' start size step` 是 `#[start, start+step, ..., start+(len-1)*step]`。

示例：
 * `Array.range' 0 3 (step := 1) = #[0, 1, 2]`
 * `Array.range' 0 3 (step := 2) = #[0, 2, 4]`
 * `Array.range' 0 4 (step := 2) = #[0, 2, 4, 6]`
 * `Array.range' 3 4 (step := 2) = #[3, 5, 7, 9]`
-/
def c006 := @Array.range'

/--
按顺序返回 `Fin n` 中所有元素的数组，从 `0` 开始。

示例：
* `Array.finRange 0 = (#[] : Array (Fin 0))`
* `Array.finRange 2 = (#[0, 1] : Array (Fin 2))`
-/
def c007 := @Array.finRange

/--
通过按顺序将 `f` 应用于每个潜在索引（从 `0` 开始）来创建数组。

示例：
* `Array.ofFn (n := 3) toString = #["0", "1", "2"]`
* `Array.ofFn (fun i => #["red", "green", "blue"].get i.val i.isLt) = #["red", "green", "blue"]`
-/
def c008 := @Array.ofFn

/--
创建一个包含 `v` 的 `n` 重复项的数组。

对应的`List`函数为`List.replicate`。

示例：
* `Array.replicate 2 true = #[true, true]`
* `Array.replicate 3 () = #[(), (), ()]`
* `Array.replicate 0 "anything" = #[]`
-/
def c009 := @Array.replicate

/--
添加两个数组。通常通过 `++` 操作员使用。

追加数组所需的时间与第二个数组的长度成正比。

示例：
* `#[1, 2, 3] ++ #[4, 5] = #[1, 2, 3, 4, 5]`。
* `#[] ++ #[4, 5] = #[4, 5]`。
* `#[1, 2, 3] ++ #[] = #[1, 2, 3]`。
-/
def c010 := @Array.append

/--
追加一个数组和一个列表。

花费的时间与列表的长度成正比。

示例：
* `#[1, 2, 3].appendList [4, 5] = #[1, 2, 3, 4, 5]`。
* `#[].appendList [4, 5] = #[4, 5]`。
* `#[1, 2, 3].appendList [] = #[1, 2, 3]`。
-/
def c011 := @Array.appendList

/--
在左侧填充 `xs : Array α`，并重复出现 `a : α`，直到其大小为 `n`。如果 `xs` 已至少具有 `n` 元素，则返回未修改的元素。

示例：
 * `#[1, 2, 3].leftpad 5 0 = #[0, 0, 1, 2, 3]`
 * `#["red", "green", "blue"].leftpad 4 "blank" = #["blank", "red", "green", "blue"]`
 * `#["red", "green", "blue"].leftpad 3 "blank" = #["red", "green", "blue"]`
 * `#["red", "green", "blue"].leftpad 1 "blank" = #["red", "green", "blue"]`
-/
def c012 := @Array.leftpad

/--
在右侧填充 `xs : Array α`，并重复出现 `a : α`，直到其长度为 `n`。如果 `l` 已至少具有 `n` 元素，则返回未修改的元素。

示例：
 * `#[1, 2, 3].rightpad 5 0 = #[1, 2, 3, 0, 0]`
 * `#["red", "green", "blue"].rightpad 4 "blank" = #["red", "green", "blue", "blank"]`
 * `#["red", "green", "blue"].rightpad 3 "blank" = #["red", "green", "blue"]`
 * `#["red", "green", "blue"].rightpad 1 "blank" = #["red", "green", "blue"]`
-/
def c013 := @Array.rightpad

/--
获取数组中存储的元素数。

这是一个缓存值，因此要访问的是`O(1)`。为数组分配的空间（称为“容量”）至少与其大小一样大，但也可能更大。数组的容量是Lean 代码无法观察到的内部细节。
-/
def c014 := @Array.size

/--
以平台本机无符号整数形式返回数组的大小。

这是 `Array.size` 的低级版本，直接查询运行时系统的数组表示。虽然这无法证明，但 `Array.usize` 始终返回数组的确切大小，因为该实现仅支持大小小于 `USize.size` 的数组。
-/
def c015 := @Array.usize

/--
检查数组是否为空。

如果数组的大小为 `0`，则数组为空。

示例：
* `(#[] : Array String).isEmpty = true`
* `#[1, 2].isEmpty = false`
* `#[()].isEmpty = false`
-/
def c016 := @Array.isEmpty

/--
返回 `as` 从索引 `start` 到 `stop`（不包括）的切片。生成的数组的大小为 `(min stop as.size) - start`。

如果 `start` 大于或等于 `stop`，则结果为空。如果 `stop` 大于 `as` 的大小，则使用该大小。

示例：
 * `#[0, 1, 2, 3, 4].extract 1 3 = #[1, 2]`
 * `#[0, 1, 2, 3, 4].extract 1 30 = #[1, 2, 3, 4]`
 * `#[0, 1, 2, 3, 4].extract 0 0 = #[]`
 * `#[0, 1, 2, 3, 4].extract 2 1 = #[]`
 * `#[0, 1, 2, 3, 4].extract 2 2 = #[]`
 * `#[0, 1, 2, 3, 4].extract 2 3 = #[2]`
 * `#[0, 1, 2, 3, 4].extract 2 4 = #[2, 3]`
-/
def c017 := @Array.extract

/--
返回给定索引处的元素，从 `0` 开始计数。如果索引越界，则返回回退值 `v₀`。

要根据索引是否在范围内返回 `Option`，请使用 `a[i]?`。要在索引越界时发生恐慌，请使用 `a[i]!`。

示例：
 * `#["spring", "summer", "fall", "winter"].getD 2 "never" = "fall"`
 * `#["spring", "summer", "fall", "winter"].getD 0 "never" = "spring"`
 * `#["spring", "summer", "fall", "winter"].getD 4 "never" = "never"`
-/
def c018 := @Array.getD

/--
低级索引运算符，与 C 数组读取速度一样快。

这可以避免因拆箱用作索引的 `Nat` 而产生的开销。
-/
def c019 := @Array.uget

/--
给出数组不为空的证明，返回数组的最后一个元素。

请参阅 `Array.back!` 了解如果数组为空则发生紧急情况的版本，或 `Array.back?` 了解返回选项的版本。
-/
def c020 := @Array.back

/--
返回数组的最后一个元素，如果数组为空，则返回 `none`。

请参阅 `Array.back!` 了解如果数组为空则发生紧急情况的版本，或 `Array.back` 了解需要证明数组非空的版本。
-/
def c021 := @Array.back?

/--
返回数组的最后一个元素，如果数组为空，则发生恐慌。

更安全的替代方案包括 `Array.back`（需要证明数组非空）和 `Array.back?`（返回 `Option`）。
-/
def c022 := @Array.back!

/--
返回数组的最大元素，由比较 `lt` 确定，如果数组为空，则返回 `none`。

示例：
* `(#[] : Array Nat).getMax? (· < ·) = none`
* `#["red", "green", "blue"].getMax? (·.length < ·.length) = some "green"`
* `#["red", "green", "blue"].getMax? (· < ·) = some "red"`
-/
def c023 := @Array.getMax?

/--
计算某个元素在数组中出现的次数。

示例：
* `#[1, 1, 2, 3, 5].count 1 = 2`
* `#[1, 1, 2, 3, 5].count 5 = 1`
* `#[1, 1, 2, 3, 5].count 4 = 0`
-/
def c024 := @Array.count

/--
计算数组 `as` 中满足布尔谓词 `p` 的元素数。

示例：
* `#[1, 2, 3, 4, 5].countP (· % 2 == 0) = 2`
* `#[1, 2, 3, 4, 5].countP (· < 5) = 4`
* `#[1, 2, 3, 4, 5].countP (· > 5) = 0`
-/
def c025 := @Array.countP

/--
返回等于 `a` 的第一个元素的索引，如果没有元素等于 `a`，则返回数组的大小。

示例：
 * `#["carrot", "potato", "broccoli"].idxOf "carrot" = 0`
 * `#["carrot", "potato", "broccoli"].idxOf "broccoli" = 2`
 * `#["carrot", "potato", "broccoli"].idxOf "tomato" = 3`
 * `#["carrot", "potato", "broccoli"].idxOf "anything else" = 3`
-/
def c026 := @Array.idxOf

/--
返回等于 `a` 的第一个元素的索引，如果没有元素等于 `a`，则返回 `none`。

示例：
* `#["carrot", "potato", "broccoli"].idxOf? "carrot" = some 0`
* `#["carrot", "potato", "broccoli"].idxOf? "broccoli" = some 2`
* `#["carrot", "potato", "broccoli"].idxOf? "tomato" = none`
* `#["carrot", "potato", "broccoli"].idxOf? "anything else" = none`
-/
def c027 := @Array.idxOf?

/--
返回等于 `a` 的第一个元素的索引，如果没有元素等于 `a`，则返回 `none`。该索引以 `Fin` 形式返回，这保证它在范围内。

示例：
 * `#["carrot", "potato", "broccoli"].finIdxOf? "carrot" = some 0`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "broccoli" = some 2`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "tomato" = none`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "anything else" = none`
-/
def c028 := @Array.finIdxOf?

/--
将 `Array α` 转换为包含相同顺序的相同元素的 `List α`。

在运行时，这是由 `Array.toListImpl` 实现的，并且数组的长度为 `O(n)`。
-/
def c029 := @Array.toList

/--
将数组转换为包含相同元素但顺序相反的列表。

这相当于 `Array.toList ∘ List.reverse`，但效率更高。

示例：
* `#[1, 2, 3].toListRev = [3, 2, 1]`
* `#["blue", "yellow"].toListRev = ["yellow", "blue"]`
-/
def c030 := @Array.toListRev

/--
将数组添加到列表前面。数组的元素位于结果列表的开头。

相当于`as.toList ++ l`。

示例：
* `#[1, 2].toListAppend [3, 4] = [1, 2, 3, 4]`
* `#[1, 2].toListAppend [] = [1, 2]`
* `#[].toListAppend [3, 4, 5] = [3, 4, 5]`
-/
def c031 := @Array.toListAppend

/--
将数组转换为向量。结果向量的大小就是数组的大小。
-/
def c032 := @Array.toVector

/--
返回具有给定边界的数组的子数组。

如果 `start` 或 `stop` 不是子数组的有效边界，则它们将被限制为数组的大小。此外，起始索引被限制到结束索引。
-/
def c033 := @Array.toSubarray

/--
分配一个包含子数组内容的新数组。
-/
def c034 := @Array.ofSubarray

/--
将一个元素添加到数组的末尾。生成的数组的大小比输入数组大 1。如果没有对该数组的其他引用，则就地修改它。

这需要摊销 `O(1)` 时间，因为 `Array α` 由动态数组表示。

示例：
* `#[].push "apple" = #["apple"]`
* `#["apple"].push "orange" = #["apple", "orange"]`
-/
def c035 := @Array.push

/--
删除数组的最后一个元素。如果数组为空，则原样返回。当对数组的引用是唯一的时，修改就地执行。

示例：
* `#[1, 2, 3].pop = #[1, 2]`
* `#["orange", "yellow"].pop = #["orange"]`
* `(#[] : Array String).pop = #[]`
-/
def c036 := @Array.pop

/--
从数组末尾删除满足谓词的所有元素。

删除所有满足谓词的最长连续元素序列。

示例：
* `#[0, 1, 2, 3, 4].popWhile (· > 2) = #[0, 1, 2]`
* `#[3, 2, 3, 4].popWhile (· > 2) = #[3, 2]`
* `(#[] : Array Nat).popWhile (· > 2) = #[]`
-/
def c037 := @Array.popWhile

/--
从数组中删除第一次出现的指定元素，如果不存在则不执行任何操作。

此函数在最坏情况下需要 `O(n)` 时间，因为它会向后移动所有后面的元素。

示例：
* `#[1, 2, 3].erase 2 = #[1, 3]`
* `#[1, 2, 3].erase 5 = #[1, 2, 3]`
* `#[1, 2, 3, 2, 1].erase 2 = #[1, 3, 2, 1]`
* `(#[] : List Nat).erase 2 = #[]`
-/
def c038 := @Array.erase

/--
删除第一个满足谓词 `p` 的元素。如果没有元素满足 `p`，则返回未修改的数组。

此函数在最坏情况下需要 `O(n)` 时间，因为它会向后移动所有后面的元素。

示例：
* `#["red", "green", "", "blue"].eraseP (·.isEmpty) = #["red", "green", "blue"]`
* `#["red", "green", "", "blue", ""].eraseP (·.isEmpty) = #["red", "green", "blue", ""]`
* `#["red", "green", "blue"].eraseP (·.length % 2 == 0) = #["red", "green"]`
* `#["red", "green", "blue"].eraseP (fun _ => true) = #["green", "blue"]`
* `(#[] : Array String).eraseP (fun _ => true) = #[]`
-/
def c039 := @Array.eraseP

/--
从数组中删除给定索引处的元素，而不进行运行时边界检查。

此函数需要最坏情况下的 `O(n)` 时间，因为它会将大于 `i` 的位置处的所有元素后移。

示例：
* `#["apple", "pear", "orange"].eraseIdx 0 = #["pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdx 1 = #["apple", "orange"]`
* `#["apple", "pear", "orange"].eraseIdx 2 = #["apple", "pear"]`
-/
def c040 := @Array.eraseIdx

/--
从数组中删除给定索引处的元素。如果索引越界，则会出现恐慌。

此函数需要最坏情况下的 `O(n)` 时间，因为它会将大于 `i` 的位置处的所有元素后移。
-/
def c041 := @Array.eraseIdx!

/--
从数组中删除给定索引处的元素。如果索引越界，则不执行任何操作。

此函数需要最坏情况下的 `O(n)` 时间，因为它会将大于 `i` 的位置处的所有元素后移。

示例：
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 0 = #["pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 1 = #["apple", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 2 = #["apple", "pear"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 3 = #["apple", "pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 5 = #["apple", "pear", "orange"]`
-/
def c042 := @Array.eraseIdxIfInBounds

/--
擦除重复的元素，保留每次运行的第一个元素。

`O(|as|)`。

例子：
* `#[1, 3, 2, 2, 2, 3, 3, 5].eraseReps = #[1, 3, 2, 3, 5]`
-/
def c043 := @Array.eraseReps

/--
交换数组的两个元素。当对数组的引用是唯一的时，修改就地执行。

示例：
* `#["red", "green", "blue", "brown"].swap 0 3 = #["brown", "green", "blue", "red"]`
* `#["red", "green", "blue", "brown"].swap 0 2 = #["blue", "green", "red", "brown"]`
* `#["red", "green", "blue", "brown"].swap 1 2 = #["red", "blue", "green", "brown"]`
* `#["red", "green", "blue", "brown"].swap 3 0 = #["brown", "green", "blue", "red"]`
-/
def c044 := @Array.swap

/--
交换数组的两个元素，如果任一索引超出范围，则返回数组不变。当对数组的引用是唯一的时，修改就地执行。

示例：
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 3 = #["brown", "green", "blue", "red"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 2 = #["blue", "green", "red", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 1 2 = #["red", "blue", "green", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 4 = #["red", "green", "blue", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 9 2 = #["red", "green", "blue", "brown"]`
-/
def c045 := @Array.swapIfInBounds

/--
将新元素与给定索引处的元素交换。

返回之前在 `i` 处找到的值，与一个数组配对，其中 `i` 处的值已替换为 `v`。

示例：
* `#["spinach", "broccoli", "carrot"].swapAt 1 "pepper" = ("broccoli", #["spinach", "pepper", "carrot"])`
* `#["spinach", "broccoli", "carrot"].swapAt 2 "pepper" = ("carrot", #["spinach", "broccoli", "pepper"])`
-/
def c046 := @Array.swapAt

/--
将新元素与给定索引处的元素交换。如果索引越界，则会出现恐慌。

返回之前在 `i` 处找到的值，与一个数组配对，其中 `i` 处的值已替换为 `v`。

示例：
* `#["spinach", "broccoli", "carrot"].swapAt! 1 "pepper" = (#["spinach", "pepper", "carrot"], "broccoli")`
* `#["spinach", "broccoli", "carrot"].swapAt! 2 "pepper" = (#["spinach", "broccoli", "pepper"], "carrot")`
-/
def c047 := @Array.swapAt!

/--
将数组中第一次出现的 `a` 替换为 `b`。当对数组的引用是唯一的时，修改就地执行。当 `a` 不存在时，返回未修改的数组。

示例：
* `#[1, 2, 3, 2, 1].replace 2 5 = #[1, 5, 3, 2, 1]`
* `#[1, 2, 3, 2, 1].replace 0 5 = #[1, 2, 3, 2, 1]`
* `#[].replace 2 5 = #[]`
-/
def c048 := @Array.replace

/--
替换数组中给定索引处的元素。

不执行边界检查，但该函数需要证明索引在边界内。这个证明通常可以省略，并且会自动合成。

如果没有其他引用，则该数组将被就地修改。

示例：
* `#[0, 1, 2].set 1 5 = #[0, 5, 2]`
* `#["orange", "apple"].set 1 "grape" = #["orange", "grape"]`
-/
def c049 := @Array.set

/--
在数组中设置一个元素，或者如果索引越界则发生恐慌。

如果调用时 `a` 的引用计数为 1，这将破坏性地执行更新。
-/
def c050 := @Array.set!

/--
替换数组中提供的索引处的元素。如果索引越界，则返回未修改的数组。

如果没有其他引用，则该数组将被就地修改。

示例：
* `#[0, 1, 2].setIfInBounds 1 5 = #[0, 5, 2]`
* `#["orange", "apple"].setIfInBounds 1 "grape" = #["orange", "grape"]`
* `#["orange", "apple"].setIfInBounds 5 "grape" = #["orange", "apple"]`
-/
def c051 := @Array.setIfInBounds

/--
低级修改运算符与 C 数组写入一样快。当对数组的引用是唯一的时，修改就地执行。

这可以避免因拆箱用作索引的 `Nat` 而产生的开销。
-/
def c052 := @Array.uset

/--
将给定索引处的元素（如果存在）替换为对其应用 `f` 的结果。如果索引无效，则返回未修改的数组。

示例：
 * `#[1, 2, 3].modify 0 (· * 10) = #[10, 2, 3]`
 * `#[1, 2, 3].modify 2 (· * 10) = #[1, 2, 30]`
 * `#[1, 2, 3].modify 3 (· * 10) = #[1, 2, 3]`
-/
def c053 := @Array.modify

/--
将给定索引处的元素（如果存在）替换为对其应用一元函数 `f` 的结果。如果索引无效，则返回未修改的数组，并且不会调用 `f`。

示例：
```lean example
#eval #[1, 2, 3, 4].modifyM 2 fun x => do
  IO.println s!"It was {x}"
  return x * 10
```
```output
It was 3
```
```output
#[1, 2, 30, 4]
```

```lean example
#eval #[1, 2, 3, 4].modifyM 6 fun x => do
  IO.println s!"It was {x}"
  return x * 10
```
```output
#[1, 2, 3, 4]
```
-/
def c054 := @Array.modifyM

/--
将给定索引处的元素（如果存在）替换为对其应用 `f` 的结果。如果索引无效，则返回未修改的数组。

示例：
 * `#[1, 2, 3].modifyOp 0 (· * 10) = #[10, 2, 3]`
 * `#[1, 2, 3].modifyOp 2 (· * 10) = #[1, 2, 30]`
 * `#[1, 2, 3].modifyOp 3 (· * 10) = #[1, 2, 3]`
-/
def c055 := @Array.modifyOp

/--
将元素插入到数组中指定索引处。如果索引大于数组的大小，则返回未修改的数组。

换句话说，新元素被插入到数组 `as` 中 `as` 的第一个 `i` 元素之后。

此函数在最坏情况下需要 `O(n)` 时间，因为它必须将插入的元素交换到位。

示例：
 * `#["tues", "thur", "sat"].insertIdx 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx 3 "wed" = #["tues", "thur", "sat", "wed"]`
-/
def c056 := @Array.insertIdx

/--
将元素插入到数组中指定索引处。如果索引大于数组的大小，则会发生恐慌。

换句话说，新元素被插入到数组 `as` 中 `as` 的第一个 `i` 元素之后。

此函数在最坏情况下需要 `O(n)` 时间，因为它必须将插入的元素交换到位。 `Array.insertIdx` 和 `Array.insertIdxIfInBounds` 是更安全的替代品。

示例：
 * `#["tues", "thur", "sat"].insertIdx! 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx! 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx! 3 "wed" = #["tues", "thur", "sat", "wed"]`
-/
def c057 := @Array.insertIdx!

/--
将元素插入到数组中指定索引处。如果索引大于数组的大小，则返回未修改的数组。

换句话说，新元素被插入到数组 `as` 中 `as` 的第一个 `i` 元素之后。

此函数在最坏情况下需要 `O(n)` 时间，因为它必须将插入的元素交换到位。

示例：
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 3 "wed" = #["tues", "thur", "sat", "wed"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 4 "wed" = #["tues", "thur", "sat"]`
-/
def c058 := @Array.insertIdxIfInBounds

/--
通过重复交换元素来反转数组。

如果没有其他引用，则原数组将被就地修改。

示例：
* `(#[] : Array Nat).reverse = #[]`
* `#[0, 1].reverse = #[1, 0]`
* `#[0, 1, 2].reverse = #[2, 1, 0]`
-/
def c059 := @Array.reverse

/--
返回一个新数组，其中包含 `xs` 的前 `i` 元素。如果 `xs` 的元素少于 `i` 的元素，则新数组包含 `xs` 的所有元素。

返回的数组始终是一个新数组，即使它包含与输入数组相同的元素。

示例：
* `#["red", "green", "blue"].take 1 = #["red"]`
* `#["red", "green", "blue"].take 2 = #["red", "green"]`
* `#["red", "green", "blue"].take 5 = #["red", "green", "blue"]`
-/
def c060 := @Array.take

/--
返回一个新数组，其中包含数组中满足谓词 `p` 的元素的最长前缀。

示例：
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 2) = #[0, 1]`
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 20) = #[0, 1, 2, 3, 2, 1]`
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 0) = #[]`
-/
def c061 := @Array.takeWhile

/--
删除 `xs` 的第一个 `i` 元素。如果 `xs` 的元素少于 `i` 的元素，则新数组为空。

返回的数组始终是一个新数组，即使它包含与输入数组相同的元素。

示例：
* `#["red", "green", "blue"].drop 1 = #["green", "blue"]`
* `#["red", "green", "blue"].drop 2 = #["blue"]`
* `#["red", "green", "blue"].drop 5 = #[]`
-/
def c062 := @Array.drop

/--
返回数组的前 `n` 元素。结果数组是通过重复调用 `Array.pop` 生成的。如果 `n` 大于数组的大小，则原样返回。

如果对数组的引用是唯一的，则此函数使用就地修改。

示例：
* `#[0, 1, 2, 3, 4].shrink 2 = #[0, 1]`
* `#[0, 1, 2, 3, 4].shrink 0 = #[]`
* `#[0, 1, 2, 3, 4].shrink 10 = #[0, 1, 2, 3, 4]`
-/
def c063 := @Array.shrink

/--
将数组数组的内容追加到单个数组中。生成的数组包含与嵌套数组相同的元素，并且顺序相同。

示例：
 * `#[#[5], #[4], #[3, 2]].flatten = #[5, 4, 3, 2]`
 * `#[#[0, 1], #[], #[2], #[1, 0, 1]].flatten = #[0, 1, 2, 1, 0, 1]`
 * `(#[] : Array Nat).flatten = #[]`
-/
def c064 := @Array.flatten

/--
返回一个新数组，其中包含 `as` 中偶数索引处的元素，从索引 `0` 处的元素开始。

示例：
* `#[0, 1, 2, 3, 4].getEvenElems = #[0, 2, 4]`
* `#[1, 2, 3, 4].getEvenElems = #[1, 3]`
* `#["red", "green", "blue"].getEvenElems = #["red", "blue"]`
* `(#[] : Array String).getEvenElems = #[]`
-/
def c065 := @Array.getEvenElems

/--
就地快速排序。

`qsort as lt lo hi` 使用 `lt` 来比较元素，对子数组 `as[lo...=hi]` 进行就地排序。
-/
def c066 := @Array.qsort

/--
使用 `compare` 对数组进行排序以比较元素。
-/
def c067 := @Array.qsortOrd

/--
使用插入排序对数组进行排序。

可选参数 `lt` 指定排序谓词。它默认为 `LT.lt`，它必须是可判定的才能用于排序。
-/
def c068 := @Array.insertionSort

/--
将一个元素插入到已排序的数组中，以便对结果数组进行排序。如果该元素已存在于数组中，则不会插入该元素。

排序谓词 `lt` 应该是元素的总顺序，并且数组 `as` 应相对于 `lt` 进行排序。

`Array.binInsertM` 是一个更通用的运算符，除了在 monad 中运行之外，还可以更好地控制重复元素的处理。

示例：
* `#[0, 1, 3, 5].binInsert (· < ·) 2 = #[0, 1, 2, 3, 5]`
* `#[0, 1, 3, 5].binInsert (· < ·) 1 = #[0, 1, 3, 5]`
* `#[].binInsert (· < ·) 1 = #[1]`
-/
def c069 := @Array.binInsert

/--
将元素 `k` 插入已排序数组 `as` 中，以便对结果数组进行排序。

排序谓词 `lt` 应该是元素的总顺序，并且数组 `as` 应相对于 `lt` 进行排序。

如果 `lt` 等于 `k` 的元素已存在于 `as` 中，则 `merge` 将应用于现有元素以确定结果数组中该位置的值。如果不存在等于 `k` 的元素，则使用 `add` 来确定要插入的值。
-/
def c070 := @Array.binInsertM

/--
在排序数组 `as` 中二分查找与 `k` 等效的元素。如果找到，则返回数组中的元素，否则返回 `none`。

数组`as`必须根据比较运算符`lt`进行排序，这应该是全序。

可选参数 `lo` 和 `hi` 确定要搜索的数组索引的区域。两者都是包容性的，并且默认搜索整个数组。
-/
def c071 := @Array.binSearch

/--
在排序数组 `as` 中二分查找与 `k` 等效的元素。如果找到该元素，则返回 `true`，否则返回 `false`。

数组`as`必须根据比较运算符`lt`进行排序，这应该是全序。

可选参数 `lo` 和 `hi` 确定要搜索的数组索引的区域。两者都是包容性的，并且默认搜索整个数组。
-/
def c072 := @Array.binSearchContains

/--
返回给定数组的有限迭代器。迭代器按顺序生成数组的元素，然后终止。

该迭代器的单子版本是 `Array.iterM`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c073 := @Array.iter

/--
返回从给定索引开始的给定数组的有限迭代器。迭代器按顺序生成数组的元素，然后终止。

该迭代器的单子版本是 `Array.iterFromIdxM`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c074 := @Array.iterFromIdx

/--
返回给定数组的有限一元迭代器。迭代器按顺序生成数组的元素，然后终止。没有副作用。

该迭代器的纯净版本是`Array.iter`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c075 := @Array.iterM

/--
返回从给定索引开始的给定数组的有限一元迭代器。迭代器按顺序生成数组的元素，然后终止。

该迭代器的纯净版本是`Array.iterFromIdx`。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c076 := @Array.iterFromIdxM

/--
从右侧将函数折叠到数组上，累加以 `init` 开头的值。使用 `f` 将累加值与数组的每个元素按相反顺序组合。

可选参数 `start` 和 `stop` 控制要折叠的阵列区域。折叠从`start`（不包括）到`stop`（包括）进行，因此除非`start > stop`，否则不会发生折叠。默认情况下，使用整个数组。

示例：
 * `#[a, b, c].foldr f init  = f a (f b (f c init))`
 * `#[1, 2, 3].foldr (toString · ++ ·) "" = "123"`
 * `#[1, 2, 3].foldr (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`
-/
def c077 := @Array.foldr

/--
从右侧开始在数组上折叠一元函数，累积以 `init` 开头的值。使用 `f` 将累积值与列表中的每个元素按相反顺序组合。

可选参数 `start` 和 `stop` 控制要折叠的阵列区域。折叠从`start`（不包括）到`stop`（包括）进行，因此除非`start > stop`，否则不会发生折叠。默认情况下，整个数组是折叠的。

示例：
```lean example
example [Monad m] (f : α → β → m β) :
  Array.foldrM (m := m) f x₀ #[a, b, c] = (do
    let x₁ ← f c x₀
    let x₂ ← f b x₁
    let x₃ ← f a x₂
    pure x₃)
  := by rfl
```

```lean example
example [Monad m] (f : α → β → m β) :
  Array.foldrM (m := m) f x₀ #[a, b, c] (start := 2) = (do
    let x₁ ← f b x₀
    let x₂ ← f a x₁
    pure x₂)
  := by rfl
```
-/
def c078 := @Array.foldrM

/--
从左侧折叠数组上的函数，累加以 `init` 开头的值。使用 `f` 将累加值按顺序与数组的每个元素组合。

可选参数 `start` 和 `stop` 控制要折叠的阵列区域。折叠从`start`（包含）到`stop`（不包含）进行，因此除非`start < stop`，否则不会发生折叠。默认情况下，使用整个数组。

示例：
 * `#[a, b, c].foldl f z  = f (f (f z a) b) c`
 * `#[1, 2, 3].foldl (· ++ toString ·) "" = "123"`
 * `#[1, 2, 3].foldl (s!"({·} {·})") "" = "((( 1) 2) 3)"`
-/
def c079 := @Array.foldl

/--
将一元函数从左侧折叠到列表上，累积以 `init` 开头的值。使用 `f` 将累加值按顺序与列表中的每个元素组合。

可选参数 `start` 和 `stop` 控制要折叠的阵列区域。折叠从`start`（包含）到`stop`（不包含）进行，因此除非`start < stop`，否则不会发生折叠。默认情况下，整个数组是折叠的。

示例：
```lean example
example [Monad m] (f : α → β → m α) :
    Array.foldlM (m := m) f x₀ #[a, b, c] = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure x₃)
  := by rfl
```

```lean example
example [Monad m] (f : α → β → m α) :
    Array.foldlM (m := m) f x₀ #[a, b, c] (start := 1) = (do
      let x₁ ← f x₀ b
      let x₂ ← f x₁ c
      pure x₂)
  := by rfl
```
-/
def c080 := @Array.foldlM

/--
按顺序将一元操作 `f` 应用于数组的每个元素。

可选参数 `start` 和 `stop` 控制应应用 `f` 的数组区域。迭代从`start`（包含）到`stop`（不包含）进行，因此除非`start < stop`，否则不会调用`f`。默认情况下，使用整个数组。
-/
def c081 := @Array.forM

/--
以相反的顺序从右到左将一元操作 `f` 应用于数组的每个元素。

可选参数 `start` 和 `stop` 控制应应用 `f` 的数组区域。迭代从`start`（不包括）到`stop`（包括），因此除非`start > stop`，否则不会调用`f`。默认情况下，使用整个数组。
-/
def c082 := @Array.forRevM

/--
在阵列上映射 `f` 并使用 `<|>` 收集结果。数组末尾的结果是 `failure`。

示例：
 * `#[[], [1, 2], [], [2]].firstM List.head? = some 1`
 * `#[[], [], []].firstM List.head? = none`
 * `#[].firstM List.head? = none`
-/
def c083 := @Array.firstM

/--
计算数组元素的总和。

示例：
* `#[a, b, c].sum = a + (b + (c + 0))`
* `#[1, 2, 5].sum = 8`
-/
def c084 := @Array.sum

/--
将函数应用于数组的每个元素，返回结果值数组。

示例：
* `#[a, b, c].map f = #[f a, f b, f c]`
* `#[].map Nat.succ = #[]`
* `#["one", "two", "three"].map (·.length) = #[3, 3, 5]`
* `#["one", "two", "three"].map (·.reverse) = #["eno", "owt", "eerht"]`
-/
def c085 := @Array.map

/--
将函数应用于数组的每个元素，返回结果数组。该函数是单态的：要求返回相同类型的值。内部实现使用指针相等，并且如果每个函数调用的结果与其参数指针相等，则不会分配新数组。
-/
def c086 := @Array.mapMono

/--
将一元操作 `f` 从左到右应用于数组中的每个元素，并返回结果数组。
-/
def c087 := @Array.mapM

/--
将一元操作 `f` 从左到右应用于数组中的每个元素，并返回结果数组。此外，结果数组的类型保证它包含与输入数组相同数量的元素。
-/
def c088 := @Array.mapM'

/--
将一元函数应用于数组的每个元素，返回结果数组。该函数是单态的：要求返回相同类型的值。内部实现使用指针相等，并且如果每个函数调用的结果与其参数指针相等，则不会分配新数组。
-/
def c089 := @Array.mapMonoM

/--
将函数应用于数组的每个元素以及找到该元素的索引，返回结果数组。

`Array.mapFinIdx` 是一个变体，它另外为该函数提供索引有效的证明。
-/
def c090 := @Array.mapIdx

/--
将一元操作 `f` 从左到右应用于数组中的每个元素以及元素的索引。返回结果数组。
-/
def c091 := @Array.mapIdxM

/--
将函数应用于数组的每个元素以及找到该元素的索引，返回结果数组。除了索引之外，该函数还提供了索引有效的证明。

`Array.mapIdx` 是一个变体，它不向函数提供索引有效的证据。
-/
def c092 := @Array.mapFinIdx

/--
将一元操作 `f` 应用于数组中的每个元素，以及元素的索引和索引在边界内的证明（从左到右）。返回结果数组。
-/
def c093 := @Array.mapFinIdxM

/--
应用一个将数组返回到数组的每个元素的函数。附加结果数组。

示例：
* `#[2, 3, 2].flatMap Array.range = #[0, 1, 0, 1, 2, 0, 1]`
* `#[['a', 'b'], ['c', 'd', 'e']].flatMap List.toArray = #['a', 'b', 'c', 'd', 'e']`
-/
def c094 := @Array.flatMap

/--
应用一个单子函数，该函数从左到右将数组返回到数组的每个元素。附加结果数组。
-/
def c095 := @Array.flatMapM

/--
将两个数组组合成一个成对的数组，其中第一个和第二个组件是每个输入数组的对应元素。结果数组是输入数组中较短者的长度。

示例：
* `#["Mon", "Tue", "Wed"].zip #[1, 2, 3] = #[("Mon", 1), ("Tue", 2), ("Wed", 3)]`
* `#["Mon", "Tue", "Wed"].zip #[1, 2] = #[("Mon", 1), ("Tue", 2)]`
* `#[x₁, x₂, x₃].zip #[y₁, y₂, y₃, y₄] = #[(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def c096 := @Array.zip

/--
将函数应用于两个数组的相应元素，并在较短数组的末尾停止。

示例：
* `#[1, 2].zipWith (· + ·) #[5, 6] = #[6, 8]`
* `#[1, 2, 3].zipWith (· + ·) #[5, 6, 10] = #[6, 8, 13]`
* `#[].zipWith (· + ·) #[5, 6] = #[]`
* `#[x₁, x₂, x₃].zipWith f #[y₁, y₂, y₃, y₄] = #[f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
def c097 := @Array.zipWith

/--
将函数应用于两个数组的相应元素，当两个数组中都没有更多元素时停止。如果一个数组比另一个数组短，则函数将通过 `none` 查找缺失的元素。

示例：
* `#[1, 6].zipWithAll min #[5, 2] = #[some 1, some 2]`
* `#[1, 2, 3].zipWithAll Prod.mk #[5, 6] = #[(some 1, some 5), (some 2, some 6), (some 3, none)]`
* `#[x₁, x₂].zipWithAll f #[y] = #[f (some x₁) (some y), f (some x₂) none]`
-/
def c098 := @Array.zipWithAll

/--
将数组的每个元素与其索引配对，可以选择从 `0` 以外的索引开始。

示例：
* `#[a, b, c].zipIdx = #[(a, 0), (b, 1), (c, 2)]`
* `#[a, b, c].zipIdx 5 = #[(a, 5), (b, 6), (c, 7)]`
-/
def c099 := @Array.zipIdx

/--
将数组对分成两个数组，分别包含第一个和第二个组件。

示例：
* `#[("Monday", 1), ("Tuesday", 2)].unzip = (#["Monday", "Tuesday"], #[1, 2])`
* `#[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzip = (#[x₁, x₂, x₃], #[y₁, y₂, y₃])`
* `(#[] : Array (Nat × String)).unzip = ((#[], #[]) : List Nat × List String)`
-/
def c100 := @Array.unzip

/--
返回 `as` 中的元素数组，其中 `p` 返回 `true`。

仅考虑从 `start`（含）到 `stop`（不含）的元素。该范围之外的元素将被丢弃。默认情况下，考虑整个数组。

示例：
* `#[1, 2, 5, 2, 7, 7].filter (· > 2) = #[5, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => false) = #[]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) = #[1, 2, 5, 2, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (· > 2) (start := 3) = #[7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) (start := 3) = #[2, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) (stop := 3) = #[1, 2, 5]`
-/
def c101 := @Array.filter

/--
按从左到右的顺序将一元谓词 `p` 应用于数组中的每个元素，并返回 `p` 返回 `true` 的元素数组。

仅考虑从 `start`（含）到 `stop`（不含）的元素。该范围之外的元素将被丢弃。默认情况下，检查整个数组。

例子：
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterM fun x => do
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
#[1, 2, 2]
```
-/
def c102 := @Array.filterM

/--
以相反的顺序（从右到左）对数组中的每个元素应用一元谓词 `p`，并返回 `p` 返回 `true` 的那些元素。返回列表中元素的顺序与输入列表中的顺序相同。

仅考虑从 `start`（不包括）到 `stop`（包括）的元素。该范围之外的元素将被丢弃。由于按相反顺序检查数组，因此仅在 `start > stop` 时检查元素。默认情况下，考虑整个数组。

例子：
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterRevM fun x => do
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
#[1, 2, 2]
```
-/
def c103 := @Array.filterRevM

/--
应用向数组的每个元素返回 `Option` 的函数，收集非 `none` 值。

例子：
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterMap fun x =>
  if x > 2 then some (2 * x) else none
```
```output
#[10, 14, 14]
```
-/
def c104 := @Array.filterMap

/--
应用一元函数，该函数将 `Option` 返回到数组的每个元素，并收集非 `none` 值。

仅考虑从 `start`（含）到 `stop`（不含）的元素。该范围之外的元素将被丢弃。默认情况下，考虑整个数组。

例子：
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterMapM fun x => do
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
#[10, 14, 14]
```
-/
def c105 := @Array.filterMapM

/--
过滤语法数组，将所有其他元素视为分隔符，而不是使用谓词 `p` 进行测试的元素。生成的数组包含 `p` 返回 `true` 的测试元素，并由相应的分隔符元素分隔。
-/
def c106 := @Array.filterSepElems

/--
过滤语法数组，将所有其他元素视为分隔符，而不是使用单子谓词 `p` 进行测试的元素。生成的数组包含 `p` 返回 `true` 的测试元素，并由相应的分隔符元素分隔。
-/
def c107 := @Array.filterSepElemsM

/--
返回一对数组，它们一起包含 `as` 的所有元素。第一个数组包含 `p` 返回 `true` 的元素，第二个数组包含 `p` 返回 `false` 的元素。

`as.partition p` 与 `(as.filter p, as.filter (not ∘ p))` 等效，但效率更高，因为它只需对数组执行一次传递。

示例：
 * `#[1, 2, 5, 2, 7, 7].partition (· > 2) = (#[5, 7, 7], #[1, 2, 2])`
 * `#[1, 2, 5, 2, 7, 7].partition (fun _ => false) = (#[], #[1, 2, 5, 2, 7, 7])`
 * `#[1, 2, 5, 2, 7, 7].partition (fun _ => true) = (#[1, 2, 5, 2, 7, 7], #[])`
-/
def c108 := @Array.partition

/--
根据函数 `key` 对数组 `xs` 的元素进行分组，返回一个哈希映射，其中每个组与其键相关联。组保留 `xs` 中元素的相对顺序。

例子：
```lean example
#eval #[0, 1, 2, 3, 4, 5, 6].groupByKey (· % 2)
```
```output
Std.HashMap.ofList [(0, #[0, 2, 4, 6]), (1, #[1, 3, 5])]
```
-/
def c109 := @Array.groupByKey

/--
检查 `a` 是否是 `as` 的元素，使用 `==` 进行元素比较。

`Array.elem` 是一个同义词，它采用数组之前的元素。

示例：
* `#[1, 4, 2, 3, 3, 7].contains 3 = true`
* `Array.contains #[1, 4, 2, 3, 3, 7] 5 = false`
-/
def c110 := @Array.contains

/--
检查 `a` 是否是 `as` 的元素，使用 `==` 进行元素比较。

`Array.contains` 是一个同义词，它将数组放在元素之前。

出于验证目的，`Array.elem` 简化为 `Array.contains`。

例子：
* `Array.elem 3 #[1, 4, 2, 3, 3, 7] = true`
* `Array.elem 5 #[1, 4, 2, 3, 3, 7] = false`
-/
def c111 := @Array.elem

/--
返回谓词 `p` 返回 `true` 的数组的第一个元素，如果未找到此类元素，则返回 `none`。

示例：
* `#[7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1`
* `#[7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none`
-/
def c112 := @Array.find?

/--
返回谓词 `p` 返回 `true` 的数组的最后一个元素，如果未找到此类元素，则返回 `none`。

示例：
* `#[7, 6, 5, 8, 1, 2, 6].findRev? (· < 5) = some 2`
* `#[7, 6, 5, 8, 1, 2, 6].findRev? (· < 1) = none`
-/
def c113 := @Array.findRev?

/--
返回 `p` 返回 `true` 的第一个元素的索引，如果没有这样的元素，则返回数组的大小。

示例：
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = 4`
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = 7`
-/
def c114 := @Array.findIdx

/--
返回 `p` 返回 `true` 的第一个元素的索引，如果没有这样的元素，则返回 `none`。

示例：
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = some 4`
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = none`
-/
def c115 := @Array.findIdx?

/--
查找一元谓词 `p` 返回 `true` 的数组的第一个元素的索引。按从左到右的顺序检查元素，当找到满足 `p` 的元素时终止搜索。如果数组中不存在这样的元素，则返回 `none`。
-/
def c116 := @Array.findIdxM?

/--
返回 `p` 返回 `true` 的第一个元素的索引，如果没有这样的元素，则返回 `none`。该索引以 `Fin` 形式返回，这保证它在范围内。

示例：
* `#[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 5) = some (4 : Fin 7)`
* `#[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 1) = none`
-/
def c117 := @Array.findFinIdx?

/--
返回单子谓词 `p` 返回 `true` 的数组的第一个元素，如果未找到此类元素，则返回 `none`。按顺序检查数组的元素。

单子 `m` 仅限于 `Type → Type`，以避免需要在 `p` 的类型中使用 `ULift Bool`。

例子：
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findM? fun i => do
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
def c118 := @Array.findM?

/--
返回数组的最后一个元素，对于该元素，一元谓词 `p` 返回 `true`，如果没有找到这样的元素，则返回 `none`。数组的元素从右到左反向检查。

单子 `m` 仅限于 `Type → Type`，以避免需要在 `p` 的类型中使用 `ULift Bool`。

例子：
```lean example
#eval #[7, 5, 8, 1, 2, 6, 5, 8].findRevM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 5
Almost! 6
```
```output
some 2
```
-/
def c119 := @Array.findRevM?

/--
按顺序返回将函数 `f` 应用于数组的每个元素的第一个非 `none` 结果。如果 `f` 对所有元素返回 `none`，则返回 `none`。

例子：
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSome? fun i =>
  if i < 5 then
    some (i * 10)
  else
    none
```
```output
some 10
```
-/
def c120 := @Array.findSome?

/--
按顺序返回将函数 `f` 应用于数组的每个元素的第一个非 `none` 结果。如果 `f` 为所有元素返回 `none`，则发生紧急情况。

例子：
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSome? fun i =>
  if i < 5 then
    some (i * 10)
  else
    none
```
```output
some 10
```
-/
def c121 := @Array.findSome!

/--
按顺序返回将一元函数 `f` 应用于数组的每个元素的第一个非 `none` 结果。如果 `f` 对所有元素返回 `none`，则返回 `none`。

例子：
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSomeM? fun i => do
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
def c122 := @Array.findSomeM?

/--
返回按从右到左的相反顺序将 `f` 应用于数组的每个元素的第一个非 `none` 结果。如果 `f` 对数组的所有元素返回 `none`，则返回 `none`。

示例：
 * `#[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `#[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
def c123 := @Array.findSomeRev?

/--
返回将一元函数 `f` 按相反顺序（从右到左）应用于数组的每个元素的第一个非 `none` 结果。一旦找到非 `none` 结果，就不再检查其他元素。如果 `f` 对数组的所有元素返回 `none`，则返回 `none`。

示例：
```lean example
#eval #[1, 2, 0, -4, 1].findSomeRevM? (m := Except String) fun x => do
  if x = 0 then throw "Zero!"
  else if x < 0 then return (some x)
  else return none
```
```output
Except.ok (some (-4))
```
```lean example
#eval #[1, 2, 0, 4, 1].findSomeRevM? (m := Except String) fun x => do
  if x = 0 then throw "Zero!"
  else if x < 0 then return (some x)
  else return none
```
```output
Except.error "Zero!"
```
-/
def c124 := @Array.findSomeRevM?

/--
如果 `p` 对于 `as` 的每个元素返回 `true`，则返回 `true`。

遇到第一个 `false` 时短路。

可选参数 `start` 和 `stop` 控制要检查的数组区域。仅检查索引从 `start`（含）到 `stop`（不含）的元素。默认情况下，检查整个数组。

示例：
* `#[a, b, c].all p = (p a && (p b && p c))`
* `#[2, 4, 6].all (· % 2 = 0) = true`
* `#[2, 4, 5, 6].all (· % 2 = 0) = false`
-/
def c125 := @Array.all

/--
如果一元谓词 `p` 对 `as` 的每个元素返回 `true`，则返回 `true`。

遇到第一个 `false` 时短路。按从左到右的顺序检查 `as` 中的元素。

可选参数 `start` 和 `stop` 控制要检查的数组区域。仅检查索引从 `start`（含）到 `stop`（不含）的元素。默认情况下，检查整个数组。
-/
def c126 := @Array.allM

/--
如果 `p` 对于 `as` 的任何元素返回 `true`，则返回 `true`。

遇到第一个 `true` 时短路。

可选参数 `start` 和 `stop` 控制要检查的数组区域。仅检查索引从 `start`（含）到 `stop`（不含）的元素。默认情况下，检查整个数组。

示例：
* `#[2, 4, 6].any (· % 2 = 0) = true`
* `#[2, 4, 6].any (· % 2 = 1) = false`
* `#[2, 4, 5, 6].any (· % 2 = 0) = true`
* `#[2, 4, 5, 6].any (· % 2 = 1) = true`
-/
def c127 := @Array.any

/--
如果一元谓词 `p` 对于 `as` 的任何元素返回 `true`，则返回 `true`。

遇到第一个 `true` 时短路。按从左到右的顺序检查 `as` 中的元素。

可选参数 `start` 和 `stop` 控制要检查的数组区域。仅检查索引从 `start`（含）到 `stop`（不含）的元素。默认情况下，检查整个数组。
-/
def c128 := @Array.anyM

/--
如果根据 `==` 运算符，`as` 中没有两个元素相等，则返回 `true`。

示例：
* `#["red", "green", "blue"].allDiff = true`
* `#["red", "green", "red"].allDiff = false`
* `(#[] : Array Nat).allDiff = true`
-/
def c129 := @Array.allDiff

/--
如果 `as` 和 `bs` 具有相同的长度并且它们通过 `eqv` 成对相关，则返回 `true`。

第一对不相关的元件发生短路。

示例：
* `#[1, 2, 3].isEqv #[2, 3, 4] (· < ·) = true`
* `#[1, 2, 3].isEqv #[2, 2, 4] (· < ·) = false`
* `#[1, 2, 3].isEqv #[2, 3] (· < ·) = false`
-/
def c130 := @Array.isEqv

/--
如果 `as` 是 `bs` 的前缀，则返回 `true`，否则返回 `false`。

示例：
* `#[0, 1, 2].isPrefixOf #[0, 1, 2, 3] = true`
* `#[0, 1, 2].isPrefixOf #[0, 1, 2] = true`
* `#[0, 1, 2].isPrefixOf #[0, 1] = false`
* `#[].isPrefixOf #[0, 1] = true`
-/
def c131 := @Array.isPrefixOf

/--
按字典顺序比较数组及其元素上的比较 `lt`。

具体来说，如果 `Array.lex as bs lt` 为真，则
* `bs` 大于 `as` 并且 `as` 通过 `==` 成对等效于 `bs` 的初始段，
或者
* 存在索引 `i`，例如 `lt as[i] bs[i]`，并且对于所有 `j < i`，`as[j] == bs[j]`。
-/
def c132 := @Array.lex

/--
“附加”证明，证明 `xs` 的元素实际上是 `xs` 的元素，从而生成具有相同元素但子类型为 `{ x // x ∈ xs }` 的新数组。

`O(1)`。

此函数主要用于允许使用高阶函数（例如 `Array.map`）的[有充分依据的递归](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=well-founded-recursion) 的定义来证明从列表中获取的值小于列表。这使得有根据的递归机制能够证明函数终止。
-/
def c133 := @Array.attach

/--
将各个证明“附加”到满足谓词 `P` 的值数组，返回相应子类型 `{ x // P x }` 中的元素数组。

`O(1)`。
-/
def c134 := @Array.attachWith

/--
通过忘记它们满足谓词，将子类型中的术语数组映射到类型中的相应术语。

这是 `Array.attachWith` 的逆值，也是 `xs.map (·.val)` 的同义词。

大多数情况下，用户不需要这样做。它是由诸如 `map_subtype` 之类的引理作为中间步骤引入的，并且理想情况下随后由 `unattach_attach` 进行简化。

该函数通常由精益自动插入，作为证明终止时的中间步骤。它很少在代码中显式使用。它是通过[有充分依据的递归](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=well-founded-recursion) 详细阐述定义过程中的中间步骤引入的。如果在证明状态下遇到此函数，正确的方法通常是策略 `simp [Array.unattach, -Array.map_subtype]`。
-/
def c135 := @Array.unattach

/--
将部分定义的函数（根据满足谓词 `P` 的 `α` 的术语定义）映射到数组 `xs : Array α`，并给出 `xs` 的每个元素实际上满足 `P` 的证明。

`Array.pmap`，以“部分映射”命名，相当于此类部分函数的 `Array.map`。
-/
def c136 := @Array.pmap

/--
树集。

树集按特定顺序存储特定类型的元素。它依赖于比较器函数，该函数定义键的排序并提供有效的依赖于顺序的查询，例如检索最小值或最大值。

为了确保操作按预期运行，比较器函数 `cmp` 应满足某些规则，以确保顺序一致：

* 如果 `a` 小于（或等于）`b`，则 `b` 大于（或等于）`a`
反之亦然（请参阅 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b` 并且 `b` 又小于或等于 `c`，则 `a`
小于或等于 `c`（请参阅 `TransCmp` 类型类）。

`cmp a b = Ordering.eq` 的键被认为是相同的，即同一时间只能包含其中一个。

为了避免昂贵的副本，用户应确保线性使用树集。

在内部，树集表示为大小有界树，这是一种具有高效顺序统计查找的自平衡二叉搜索树。

为了在证明中使用，应优先选择扩展树集的类型 `Std.ExtTreeSet`。该类型带有多个外延引理并提供相同的功能，但需要 `TransCmp` 实例才能使用。

这些树集包含捆绑的格式良好不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.TreeSet.Raw` 和 `Std.TreeSet.Raw.WF` 将不变量从树集中分离出来。如有疑问，请选择 `TreeSet` 而不是 `TreeSet.Raw`。
-/
structure c137 (α : Type u) (cmp : α → α → Ordering := by exact compare) where
  /-- 树映射的内部实现细节。 -/
  inner : Std.TreeMap α Unit cmp

/--
创建一个新的空树集。还可以并建议使用空集合符号 `∅` 和 `{}` 来创建空树集。 `simp` 将 `empty` 替换为 `∅`。
-/
def c138 := @Std.TreeSet.empty

/--
如果树集不包含映射，则返回 `true`。
-/
def c139 := @Std.TreeSet.isEmpty

/--
返回地图中存在的映射数量。
-/
def c140 := @Std.TreeSet.size

/--
如果集合中包含 `a` 或根据比较器 `cmp` 等于 `a` 的元素，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ t` 相当于 `t.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=`，`contains` 使用 `==` 进行相等性检查，而对于树集，两者都使用给定的比较器 `cmp`。
-/
def c141 := @Std.TreeSet.contains

/--
从匹配 `a` 的集合中检索密钥。通过要求 `a ∈ m` 的证明来确保此类密钥存在。结果保证是等于集合中的键的指针。
-/
def c142 := @Std.TreeSet.get

/--
检查是否包含给定的密钥，如果包含则返回该密钥，否则会出现恐慌。如果没有发生恐慌，则结果保证是等于集合中的键的指针。
-/
def c143 := @Std.TreeSet.get!

/--
检查是否包含给定的密钥，如果包含则返回该密钥，否则返回 `none`。 `some` 情况下的结果保证是与映射中的键相等的指针。
-/
def c144 := @Std.TreeSet.get?

/--
检查是否包含给定的密钥，如果包含则返回该密钥，否则返回 `fallback`。如果包含它们的键，则保证结果是等于集合中的键的指针。
-/
def c145 := @Std.TreeSet.getD

/--
返回 `n` 第一个最小元素。
-/
def c146 := @Std.TreeSet.atIdx

/--
返回 `n` 第一个最小元素，或者如果 `n` 至少为 `t.size`，则发生恐慌。
-/
def c147 := @Std.TreeSet.atIdx!

/--
返回 `n` 第一个最小元素，如果 `n` 至少为 `t.size`，则返回 `none`。
-/
def c148 := @Std.TreeSet.atIdx?

/--
返回 `n` 第一个最小元素，如果 `n` 至少为 `t.size`，则返回 `fallback`。
-/
def c149 := @Std.TreeSet.atIdxD

/--
给出此类元素存在的证明，检索大于或等于给定元素的最小元素。
-/
def c150 := @Std.TreeSet.getGE

/--
尝试检索大于或等于给定元素的最小元素，如果不存在这样的元素，则会出现恐慌。
-/
def c151 := @Std.TreeSet.getGE!

/--
尝试检索大于或等于给定元素的最小元素，如果不存在此类元素，则返回 `none`。
-/
def c152 := @Std.TreeSet.getGE?

/--
尝试检索大于或等于给定元素的最小元素，如果不存在此类元素，则返回 `fallback`。
-/
def c153 := @Std.TreeSet.getGED

/--
给出这样一个元素存在的证明，检索大于给定元素的最小元素。
-/
def c154 := @Std.TreeSet.getGT

/--
尝试检索大于给定元素的最小元素，如果不存在这样的元素，则会出现恐慌。
-/
def c155 := @Std.TreeSet.getGT!

/--
尝试检索大于给定元素的最小元素，如果不存在此类元素，则返回 `none`。
-/
def c156 := @Std.TreeSet.getGT?

/--
尝试检索大于给定元素的最小元素，如果不存在此类元素，则返回 `fallback`。
-/
def c157 := @Std.TreeSet.getGTD

/--
给出此类元素存在的证明，检索小于或等于给定元素的最大元素。
-/
def c158 := @Std.TreeSet.getLE

/--
尝试检索小于或等于给定元素的最大元素，如果不存在这样的元素，则会出现恐慌。
-/
def c159 := @Std.TreeSet.getLE!

/--
尝试检索小于或等于给定元素的最大元素，如果不存在此类元素，则返回 `none`。
-/
def c160 := @Std.TreeSet.getLE?

/--
尝试检索小于或等于给定元素的最大元素，如果不存在此类元素，则返回 `fallback`。
-/
def c161 := @Std.TreeSet.getLED

/--
给出这样一个元素存在的证明，检索小于给定元素的最小元素。
-/
def c162 := @Std.TreeSet.getLT

/--
尝试检索小于给定元素的最小元素，如果不存在这样的元素，则会出现恐慌。
-/
def c163 := @Std.TreeSet.getLT!

/--
尝试检索小于给定元素的最小元素，如果不存在此类元素，则返回 `none`。
-/
def c164 := @Std.TreeSet.getLT?

/--
尝试检索小于给定元素的最小元素，如果不存在此类元素，则返回 `fallback`。
-/
def c165 := @Std.TreeSet.getLTD

/--
给出树集不为空的证明，检索最小元素。
-/
def c166 := @Std.TreeSet.min

/--
尝试检索树集中的最小元素，如果该集为空，则会出现恐慌。
-/
def c167 := @Std.TreeSet.min!

/--
尝试检索树集合的最小元素，如果集合为空，则返回 `none`。
-/
def c168 := @Std.TreeSet.min?

/--
尝试检索树集的最小元素，如果树集为空，则返回 `fallback`。
-/
def c169 := @Std.TreeSet.minD

/--
给出树集不为空的证明，检索最大元素。
-/
def c170 := @Std.TreeSet.max

/--
尝试检索树集中的最大元素，如果该集为空，则会出现恐慌。
-/
def c171 := @Std.TreeSet.max!

/--
尝试检索树集中的最大元素，如果集为空，则返回 `none`。
-/
def c172 := @Std.TreeSet.max?

/--
尝试检索树集的最大元素，如果树集为空，则返回 `fallback`。
-/
def c173 := @Std.TreeSet.maxD

/--
将给定元素插入集合中。如果树集已经包含与给定元素相等（关于 `cmp`）的元素，则树集原封不动地返回。

注意：此非替换行为适用于 `TreeSet` 和 `TreeSet.Raw`。 `TreeMap`、`DTreeMap`、`TreeMap.Raw` 和 `DTreeMap.Raw` 上的 `insert` 函数的行为不同：它将覆盖现有映射。
-/
def c174 := @Std.TreeSet.insert

/--
通过迭代给定集合并调用 `insert` 将多个元素插入树集中。如果同一元素（相对于 `cmp`）出现多次，则第一次出现的元素优先。

注意：此优先行为适用于 `TreeSet` 和 `TreeSet.Raw`。 `TreeMap`、`DTreeMap`、`TreeMap.Raw` 和 `DTreeMap.Raw` 上的 `insertMany` 函数的行为有所不同：它会更喜欢最后的外观。
-/
def c175 := @Std.TreeSet.insertMany

/--
检查集合中是否存在某个元素，如果未找到则插入该元素。如果树集已经包含与给定元素相等的元素（就 `cmp` 而言），则树集原封不动地返回。

相当于（但可能比）调用 `contains`，然后调用 `insert`。
-/
def c176 := @Std.TreeSet.containsThenInsert

/--
删除给定的键（如果存在）。
-/
def c177 := @Std.TreeSet.erase

/--
通过迭代给定的集合并调用擦除来从树集中删除多个项目。
-/
def c178 := @Std.TreeSet.eraseMany

/--
从树集中删除给定函数返回 `false` 的所有元素。
-/
def c179 := @Std.TreeSet.filter

/--
返回包含 `t₁` 和 `t2 的所有映射的集合。

该功能确保`t₁` 线性使用。因此，只要 `t₁` 不共享，性能特征就遵循以下命令式描述：迭代 `t₂` 中的所有映射，将它们插入到 `t₁` 中。

因此，只要 `t₁` 未共享，此方法的运行时间就以 `t₁` 的大小呈对数缩放，并以 `t₂` 的大小呈线性缩放。
-/
def c180 := @Std.TreeSet.merge

/--
根据谓词将树集划分为两个树集。
-/
def c181 := @Std.TreeSet.partition

/--
返回树集条目上的有限迭代器。迭代器按顺序产生集合的元素，然后终止。

**终止属性：**

* `Finite` 实例：始终
* `Productive` 实例：始终
-/
def c182 := @Std.TreeSet.iter

/--
检查是否有任何元素满足谓词，如果谓词成功则短路。
-/
def c183 := @Std.TreeSet.all

/--
检查是否所有元素都满足谓词，如果谓词失败则短路。
-/
def c184 := @Std.TreeSet.any

/--
按升序将给定函数折叠到树集中的元素上。
-/
def c185 := @Std.TreeSet.foldl

/--
通过按升序将给定函数折叠到树集中的元素上，单子地计算一个值。
-/
def c186 := @Std.TreeSet.foldlM

/--
按降序将给定函数折叠到树集中的元素上。
-/
def c187 := @Std.TreeSet.foldr

/--
通过按降序将给定函数折叠到树集中的元素上，单子地计算一个值。
-/
def c188 := @Std.TreeSet.foldrM

/--
支持 `do` 块中的 `for` 循环构造。迭代按升序进行。
-/
def c189 := @Std.TreeSet.forIn

/--
按升序对树集中的每个元素执行单子操作。
-/
def c190 := @Std.TreeSet.forM

/--
将树集转换为按升序排列的元素列表。
-/
def c191 := @Std.TreeSet.toList

/--
将列表转换为树集。
-/
def c192 := @Std.TreeSet.ofList

/--
将树集转换为按升序排列的元素数组。
-/
def c193 := @Std.TreeSet.toArray

/--
将数组转换为树集。
-/
def c194 := @Std.TreeSet.ofArray

/--
没有捆绑的格式良好不变量的树集，适合在嵌套归纳类型中使用。格式良好的不变量称为 `Raw.WF`。如有疑问，请选择 `TreeSet` 而不是 `TreeSet.Raw`。关于 `Std.TreeSet.Raw` 操作的引理可在模块 `Std.Data.TreeSet.Raw.Lemmas` 中找到。

树集按特定顺序存储特定类型的元素。它依赖于比较器函数，该函数定义键的排序并提供有效的依赖于顺序的查询，例如检索最小值或最大值。

为了确保操作按预期运行，比较器函数 `cmp` 应满足某些规则，以确保顺序一致：

* 如果 `a` 小于（或等于）`b`，则 `b` 大于（或等于）`a`
反之亦然（请参阅 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b` 并且 `b` 又小于或等于 `c`，则 `a`
小于或等于 `c`（请参阅 `TransCmp` 类型类）。

`cmp a b = Ordering.eq` 的键被认为是相同的，即只有其中一个可以同时包含在单个树集中。

为了避免昂贵的副本，用户应确保线性使用树集。

在内部，树集表示为大小有界树，这是一种具有高效顺序统计查找的自平衡二叉搜索树。
-/
structure c195 (α : Type u) (cmp : α → α → Ordering := by exact compare) where
  /-- 树集合的内部实现细节。 -/
  inner : Std.TreeMap.Raw α Unit cmp

/--
树集的格式良好谓词。 `TreeSet` 的用户不需要与之交互。 `TreeSet.Raw` 的用户需要向引理提供 `WF` 的证明，并且应该使用像 `WF.empty` 和 `WF.insert` 这样的引理（它们的命名总是与它们所涉及的操作完全相同）来表明集合操作保持格式良好。该类型的构造函数是内部实现细节，用户不应访问。
-/
structure c196 {α : Type u} {cmp : α → α → Ordering}
    (t : Std.TreeSet.Raw α cmp) : Prop where
  /-- 树映射的内部实现细节。 -/
  out : t.inner.WF

/--
将 `l` 中（从零开始）索引 `n` 处的值替换为 `a`。如果索引越界，则列表将不加修改地返回。

示例：
* `["water", "coffee", "soda", "juice"].set 1 "tea" = ["water", "tea", "soda", "juice"]`
* `["water", "coffee", "soda", "juice"].set 4 "tea" = ["water", "coffee", "soda", "juice"]`
-/
def c197 := @List.set

/--
将 `l` 中（从零开始）索引 `n` 处的值替换为 `a`。如果索引越界，则列表将不加修改地返回。

这是在运行时使用的 `List.set` 的尾递归版本。

示例：
* `["water", "coffee", "soda", "juice"].set 1 "tea" = ["water", "tea", "soda", "juice"]`
* `["water", "coffee", "soda", "juice"].set 4 "tea" = ["water", "coffee", "soda", "juice"]`
-/
def c198 := @List.setTR

/--
将给定索引处的元素（如果存在）替换为对其应用 `f` 的结果。如果索引无效，则列表将不加修改地返回。

示例：
 * `[1, 2, 3].modify 0 (· * 10) = [10, 2, 3]`
 * `[1, 2, 3].modify 2 (· * 10) = [1, 2, 30]`
 * `[1, 2, 3].modify 3 (· * 10) = [1, 2, 3]`
-/
def c199 := @List.modify

/--
将给定索引处的元素（如果存在）替换为对其应用 `f` 的结果。

这是 `List.modify` 的尾递归版本。

示例：
* `[1, 2, 3].modifyTR 0 (· * 10) = [10, 2, 3]`
* `[1, 2, 3].modifyTR 2 (· * 10) = [1, 2, 30]`
* `[1, 2, 3].modifyTR 3 (· * 10) = [1, 2, 3]`
-/
def c200 := @List.modifyTR

/--
将列表的头部替换为应用 `f` 的结果。如果列表为空，则返回空列表。

示例：
 * `[1, 2, 3].modifyHead (· * 10) = [10, 2, 3]`
 * `[].modifyHead (· * 10) = []`
-/
def c201 := @List.modifyHead

/--
将 `l` 的第 `n` 尾部替换为对其应用 `f` 的结果。如果索引大于列表的长度，则返回输入而不使用 `f`。

示例：
```lean example
["circle", "square", "triangle"].modifyTailIdx 1 List.reverse
```
```output
["circle", "triangle", "square"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 1 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle", "square", "triangle"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 2 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle", "triangle"]
```
```lean example
["circle", "square", "triangle"].modifyTailIdx 5 (fun xs => xs ++ xs)
```
```output
["circle", "square", "triangle"]
```
-/
def c202 := @List.modifyTailIdx

/--
从 `l` 中删除第一次出现的 `a`。如果 `a` 未出现在 `l` 中，则返回未修改的列表。

`O(|l|)`。

示例：
* `[1, 5, 3, 2, 5].erase 5 = [1, 3, 2, 5]`
* `[1, 5, 3, 2, 5].erase 6 = [1, 5, 3, 2, 5]`
-/
def c203 := @List.erase

/--
从 `l` 中删除第一次出现的 `a`。如果 `a` 未出现在 `l` 中，则返回未修改的列表。

`O(|l|)`。

这是 `List.erase` 的尾递归版本，用于运行时代码。

示例：
* `[1, 5, 3, 2, 5].eraseTR 5 = [1, 3, 2, 5]`
* `[1, 5, 3, 2, 5].eraseTR 6 = [1, 5, 3, 2, 5]`
-/
def c204 := @List.eraseTR

/--
删除列表中的重复元素，保留第一次出现的重复元素。

`O(|l|^2)`。

示例：
* `[1, 3, 2, 2, 3, 5].eraseDups = [1, 3, 2, 5]`
* `["red", "green", "green", "blue"].eraseDups = ["red", "green", "blue"]`
-/
def c205 := @List.eraseDups

/--
删除指定索引处的元素。如果索引越界，则列表将不加修改地返回。

`O(i)`。

示例：
* `[0, 1, 2, 3, 4].eraseIdx 0 = [1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdx 1 = [0, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdx 5 = [0, 1, 2, 3, 4]`
-/
def c206 := @List.eraseIdx

/--
删除指定索引处的元素。如果索引越界，则列表将不加修改地返回。

`O(i)`。

这是 `List.eraseIdx` 的尾递归版本，在运行时使用。

示例：
* `[0, 1, 2, 3, 4].eraseIdxTR 0 = [1, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdxTR 1 = [0, 2, 3, 4]`
* `[0, 1, 2, 3, 4].eraseIdxTR 5 = [0, 1, 2, 3, 4]`
-/
def c207 := @List.eraseIdxTR

/--
删除 `p` 返回 `true` 的列表的第一个元素。如果没有元素满足 `p`，则列表原样返回。

示例：
  * `[2, 1, 2, 1, 3, 4].eraseP (· < 2) = [2, 2, 1, 3, 4]`
  * `[2, 1, 2, 1, 3, 4].eraseP (· > 2) = [2, 1, 2, 1, 4]`
  * `[2, 1, 2, 1, 3, 4].eraseP (· > 8) = [2, 1, 2, 1, 3, 4]`
-/
def c208 := @List.eraseP

/--
删除 `p` 返回 `true` 的列表的第一个元素。如果没有元素满足 `p`，则列表原样返回。

这是 `eraseP` 的尾递归版本，在运行时使用。

示例：
  * `[2, 1, 2, 1, 3, 4].erasePTR (· < 2) = [2, 2, 1, 3, 4]`
  * `[2, 1, 2, 1, 3, 4].erasePTR (· > 2) = [2, 1, 2, 1, 4]`
  * `[2, 1, 2, 1, 3, 4].erasePTR (· > 8) = [2, 1, 2, 1, 3, 4]`
-/
def c209 := @List.erasePTR

/--
擦除重复的元素，保留每次运行的第一个元素。

`O(|l|)`。

例子：
* `[1, 3, 2, 2, 2, 3, 3, 5].eraseReps = [1, 3, 2, 3, 5]`
-/
def c210 := @List.eraseReps

/--
返回 `l` 从索引 `start`（包含）到 `stop`（不包含）的切片。

示例：
* [0, 1, 2, 3, 4, 5].提取 1 2 = [1]
* [0, 1, 2, 3, 4, 5].提取 2 2 = []
* [0, 1, 2, 3, 4, 5].提取 2 4 = [2, 3]
* [0, 1, 2, 3, 4, 5].提取 2 = [2, 3, 4, 5]
* [0, 1, 2, 3, 4, 5].extract (stop := 2) = [0, 1]
-/
def c211 := @List.extract

/--
删除 `ys` 中存在的 `xs` 的所有元素。

`O(|xs| * |ys|)`。

示例：
* `[1, 1, 5, 1, 2, 4, 5].removeAll [1, 2, 2] = [5, 4, 5]`
* `[1, 2, 3, 2].removeAll [] = [1, 2, 3, 2]`
* `[1, 2, 3, 2].removeAll [3] = [1, 2, 2]`
-/
def c212 := @List.removeAll

/--
将列表 `l` 中等于 `a` 的第一个元素替换为 `b`。如果没有元素等于 `a`，则列表原样返回。

`O(|l|)`。

示例：
* `[1, 4, 2, 3, 3, 7].replace 3 6 = [1, 4, 2, 6, 3, 7]`
* `[1, 4, 2, 3, 3, 7].replace 5 6 = [1, 4, 2, 3, 3, 7]`
-/
def c213 := @List.replace

/--
将列表 `l` 中等于 `a` 的第一个元素替换为 `b`。如果没有元素等于 `a`，则列表原样返回。

`O(|l|)`。这是运行时代码中使用的 `List.replace` 的尾递归版本。

示例：
* `[1, 4, 2, 3, 3, 7].replaceTR 3 6 = [1, 4, 2, 6, 3, 7]`
* `[1, 4, 2, 3, 3, 7].replaceTR 5 6 = [1, 4, 2, 3, 3, 7]`
-/
def c214 := @List.replaceTR

/--
反转列表。

`O(|as|)`。

由于 Lean 编译器实现的“功能到位”优化，当该函数对输入列表的引用未共享时，它不会分配新列表：它只是遍历链表并反转所有节点指针。

示例：
* `[1, 2, 3, 4].reverse = [4, 3, 2, 1]`
* `[].reverse = []`
-/
def c215 := @List.reverse

/--
将列表列表连接成单个列表，保留元素的顺序。

`O(|flatten L|)`。

示例：
* `[["a"], ["b", "c"]].flatten = ["a", "b", "c"]`
* `[["a"], [], ["b", "c"], ["d", "e", "f"]].flatten = ["a", "b", "c", "d", "e", "f"]`
-/
def c216 := @List.flatten

/--
将列表列表连接成单个列表，保留元素的顺序。

`O(|flatten L|)`。这是 `List.flatten` 的尾递归版本，用于运行时代码。

示例：
* `[["a"], ["b", "c"]].flattenTR = ["a", "b", "c"]`
* `[["a"], [], ["b", "c"], ["d", "e", "f"]].flattenTR = ["a", "b", "c", "d", "e", "f"]`
-/
def c217 := @List.flattenTR

/--
将 `xs` 的元素向左旋转，将 `i % xs.length` 元素从列表的开头移动到结尾。

`O(|xs|)`。

示例：
* `[1, 2, 3, 4, 5].rotateLeft 3 = [4, 5, 1, 2, 3]`
* `[1, 2, 3, 4, 5].rotateLeft 5 = [1, 2, 3, 4, 5]`
* `[1, 2, 3, 4, 5].rotateLeft 1 = [2, 3, 4, 5, 1]`
-/
def c218 := @List.rotateLeft

/--
将 `xs` 的元素向右旋转，将 `i % xs.length` 元素从列表末尾移动到开头。

旋转后，`xs[n]` 处的元素位于索引 `(i + n) % l.length` 处。 `O(|xs|)`。

示例：
* `[1, 2, 3, 4, 5].rotateRight 3 = [3, 4, 5, 1, 2]`
* `[1, 2, 3, 4, 5].rotateRight 5 = [1, 2, 3, 4, 5]`
* `[1, 2, 3, 4, 5].rotateRight 1 = [5, 1, 2, 3, 4]`
-/
def c219 := @List.rotateRight

/--
在左侧填充 `l : List α`，并重复出现 `a : α`，直到其长度为 `n`。如果 `l` 已至少具有 `n` 元素，则返回未修改的元素。

示例：
 * `[1, 2, 3].leftpad 5 0 = [0, 0, 1, 2, 3]`
 * `["red", "green", "blue"].leftpad 4 "blank" = ["blank", "red", "green", "blue"]`
 * `["red", "green", "blue"].leftpad 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].leftpad 1 "blank" = ["red", "green", "blue"]`
-/
def c220 := @List.leftpad

/--
在左侧填充 `l : List α`，并重复出现 `a : α`，直到其长度为 `n`。如果 `l` 已至少具有 `n` 元素，则返回未修改的元素。

这是 `List.leftpad` 的尾递归版本，在运行时使用。

示例：
 * `[1, 2, 3].leftPadTR 5 0 = [0, 0, 1, 2, 3]`
 * `["red", "green", "blue"].leftPadTR 4 "blank" = ["blank", "red", "green", "blue"]`
 * `["red", "green", "blue"].leftPadTR 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].leftPadTR 1 "blank" = ["red", "green", "blue"]`
-/
def c221 := @List.leftpadTR

/--
在右侧填充 `l : List α`，并重复出现 `a : α`，直到其长度为 `n`。如果 `l` 已至少具有 `n` 元素，则返回未修改的元素。

示例：
 * `[1, 2, 3].rightpad 5 0 = [1, 2, 3, 0, 0]`
 * `["red", "green", "blue"].rightpad 4 "blank" = ["red", "green", "blue", "blank"]`
 * `["red", "green", "blue"].rightpad 3 "blank" = ["red", "green", "blue"]`
 * `["red", "green", "blue"].rightpad 1 "blank" = ["red", "green", "blue"]`
-/
def c222 := @List.rightpad

/--
将一个元素插入到列表中，且不重复。

如果该元素存在于列表中，则返回未修改的列表。否则，新元素将插入到列表的头部。

示例：
 * `[1, 2, 3].insert 0 = [0, 1, 2, 3]`
 * `[1, 2, 3].insert 4 = [4, 1, 2, 3]`
 * `[1, 2, 3].insert 2 = [1, 2, 3]`
-/
def c223 := @List.insert

/--
将元素插入列表中指定索引处。如果索引大于列表的长度，则列表将不加修改地返回。

换句话说，新元素被插入到列表`l`中`l`的第一个`i`元素之后。

示例：
 * `["tues", "thur", "sat"].insertIdx 1 "wed" = ["tues", "wed", "thur", "sat"]`
 * `["tues", "thur", "sat"].insertIdx 2 "wed" = ["tues", "thur", "wed", "sat"]`
 * `["tues", "thur", "sat"].insertIdx 3 "wed" = ["tues", "thur", "sat", "wed"]`
 * `["tues", "thur", "sat"].insertIdx 4 "wed" = ["tues", "thur", "sat"]`
-/
def c224 := @List.insertIdx

/--
将元素插入列表中指定索引处。如果索引大于列表的长度，则列表将不加修改地返回。

换句话说，新元素被插入到列表`l`中`l`的第一个`i`元素之后。

这是 `List.insertIdx` 的尾递归版本，在运行时使用。

示例：
 * `["tues", "thur", "sat"].insertIdxTR 1 "wed" = ["tues", "wed", "thur", "sat"]`
 * `["tues", "thur", "sat"].insertIdxTR 2 "wed" = ["tues", "thur", "wed", "sat"]`
 * `["tues", "thur", "sat"].insertIdxTR 3 "wed" = ["tues", "thur", "sat", "wed"]`
 * `["tues", "thur", "sat"].insertIdxTR 4 "wed" = ["tues", "thur", "sat"]`
-/
def c225 := @List.insertIdxTR

/--
将 `l` 与 `sep` 的元素交替。

`O(|l|)`。

`List.intercalate` 是一个类似的函数，它将分隔符列表与列表列表的元素交替。

示例：
* `List.intersperse "then" [] = []`
* `List.intersperse "then" ["walk"] = ["walk"]`
* `List.intersperse "then" ["walk", "run"] = ["walk", "then", "run"]`
* `List.intersperse "then" ["walk", "run", "rest"] = ["walk", "then", "run", "then", "rest"]`
-/
def c226 := @List.intersperse

/--
将 `l` 与 `sep` 的元素交替。

`O(|l|)`。

这是 `List.intersperse` 的尾递归版本，在运行时使用。

示例：
* `List.intersperseTR "then" [] = []`
* `List.intersperseTR "then" ["walk"] = ["walk"]`
* `List.intersperseTR "then" ["walk", "run"] = ["walk", "then", "run"]`
* `List.intersperseTR "then" ["walk", "run", "rest"] = ["walk", "then", "run", "then", "rest"]`
-/
def c227 := @List.intersperseTR

/--
将 `xs` 中的列表与分隔符 `sep` 交替，并附加它们。结果列表被展平。

`O(|xs|)`。

`List.intersperse` 是一个类似的函数，它将分隔符元素与列表的元素交替。

示例：
* `List.intercalate sep [] = []`
* `List.intercalate sep [a] = a`
* `List.intercalate sep [a, b] = a ++ sep ++ b`
* `List.intercalate sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
def c228 := @List.intercalate

/--
将 `xs` 中的列表与分隔符 `sep` 交替。

这是运行时使用的 `List.intercalate` 的尾递归版本。

示例：
* `List.intercalateTR sep [] = []`
* `List.intercalateTR sep [a] = a`
* `List.intercalateTR sep [a, b] = a ++ sep ++ b`
* `List.intercalateTR sep [a, b, c] = a ++ sep ++ b ++ sep ++ c`
-/
def c229 := @List.intercalateTR

/--
产品类型，通常写作`α × β`。产品类型也称为对或元组类型。这种类型的元素是成对的，其中第一个元素是 `α`，第二个元素是 `β`。

产品嵌套在右侧，因此 `(x, y, z) : α × β × γ` 相当于 `(x, (y, z)) : α × (β × γ)`。


标识符中的符号约定：

 * 标识符中 `×` 的建议拼写为 `Prod`。
-/
structure c230 (α : Type u) (β : Type v) where
  /-- 有序对的第一个元素。 -/
  fst : α
  /-- 有序对的第二个元素。 -/
  snd : β

/--
构造一个有序对。通常写作 `(x, y)`，而不是 `Prod.mk x y`。

标识符中的记法约定：

 * 标识符中 `(a, b)` 的推荐拼写是 `mk`。
-/
add_decl_doc c230.mk

/--
一种产品类型，其中类型可以是命题，通常写作`α ×' β`。

这种类型主要在内部使用，并作为证明自动化的实现细节。它在手写代码中很少有用。


标识符中的符号约定：

 * 标识符中 `×'` 的建议拼写为 `PProd`。
-/
structure c231 (α : Sort u) (β : Sort v) : Sort (max (max 1 u) v) where
  /-- 有序对的第一个元素。 -/
  fst : α
  /-- 有序对的第二个元素。 -/
  snd : β

/--
`α` 和 `β` 位于同一 Universe 的产品类型。

它被称为 `MProd` 是因为它是 *​​universe-monomorphic* 产品类型。
-/
structure c232 (α β : Type u) where
  /-- 有序对的第一个元素。 -/
  fst : α
  /-- 有序对的第二个元素。 -/
  snd : β

/--
通过对两个元素应用函数来转换一对。

示例：
* `(1, 2).map (· + 1) (· * 3) = (2, 6)`
* `(1, 2).map toString (· * 3) = ("1", 6)`
-/
def c233 := @Prod.map

/--
交换一对中的元素。

示例：
* `(1, 2).swap = (2, 1)`
* `("orange", -87).swap = (-87, "orange")`
-/
def c234 := @Prod.swap

/--
检查谓词是否适用于范围内的所有自然数。

特别是，如果 `f` 对于从 `start`（包含）到 `stop`（不包含）的所有自然数都为 true，则 `(start, stop).allI f` 返回 true。

示例：
 * `(5, 8).allI (fun j _ _ => j < 10) = (5 < 10) && (6 < 10) && (7 < 10)`
 * `(5, 8).allI (fun j _ _ => j % 2 = 0) = false`
 * `(6, 7).allI (fun j _ _ => j % 2 = 0) = true`
-/
def c235 := @Prod.allI

/--
检查谓词是否适用于范围内的任何自然数。

特别是，如果 `f` 对于从 `start`（包含）到 `stop`（不包含）的任何自然数为 true，则 `(start, stop).allI f` 返回 true。

示例：
 * `(5, 8).anyI (fun j _ _ => j == 6) = (5 == 6) || (6 == 6) || (7 == 6)`
 * `(5, 8).anyI (fun j _ _ => j % 2 = 0) = true`
 * `(6, 6).anyI (fun j _ _ => j % 2 = 0) = false`
-/
def c236 := @Prod.anyI

/--
将初始值与某个范围中的每个自然数按升序组合。

特别是，`(start, stop).foldI f init` 按升序将 `f` 应用于从 `start`（含）到 `stop`（不含）的所有数字：

示例：
* `(5, 8).foldI (fun j _ _ xs => xs.push j) #[] = (#[] |>.push 5 |>.push 6 |>.push 7)`
* `(5, 8).foldI (fun j _ _ xs => xs.push j) #[] = #[5, 6, 7]`
* `(5, 8).foldI (fun j _ _ xs => toString j :: xs) [] = ["7", "6", "5"]`
-/
def c237 := @Prod.foldI

/--
产品的字典顺序。

如果两个对的第一个元素是有序的，或者如果它们的第一个元素相等并且它们的第二个元素是有序的，则两个对按字典顺序排序。
-/
def c238 := @Prod.lexLt

/--
依赖对，其中第二个元素的类型取决于第一个元素的值。类型 `Sigma β` 通常写作 `Σ a : α, β a` 或 `(a : α) × β a`。

尽管其值是对，但 `Sigma` 有时也称为“依赖求和类型”，因为它是索引求和的类型级别版本。
-/
structure c239 {α : Type u} (β : α → Type v) where
  /-- 依值有序对的第一个分量。 -/
  fst : α
  /-- 依值有序对的第二个分量，其类型依赖于第一个分量。 -/
  snd : β fst

/--
构造依值有序对。

在类型未知的上下文中使用此构造子时，通常需要类型标注来确定 `β`，因为两个值之间所需的关系通常无法自动确定。
-/
add_decl_doc c239.mk

/--
完全宇宙多态依赖对，其中第二个元素的类型取决于第一个元素的值，并且两种类型都允许是命题。类型 `PSigma β` 通常写作 `Σ' a : α, β a` 或 `(a : α) ×' β a`。

在实践中，这种通用性导致宇宙级约束难以解决，因此 `PSigma` 很少在手动编写的代码中使用。它通常仅用于构造任意类型对的自动化。

要将值与谓词对其成立的证明配对，请使用 `Subtype`。要证明存在满足谓词的值，请使用 `Exists`。由于证明无关，以命题作为其第一个组成部分的依赖对通常没有用处：依赖于特定证明是没有意义的，因为无论如何所有证明都是相等的。
-/
structure c240 {α : Sort u} (β : α → Sort v) : Sort (max (max 1 u) v) where
  /-- 依值有序对的第一个分量。 -/
  fst : α
  /-- 依值有序对的第二个分量，其类型依赖于第一个分量。 -/
  snd : β fst

/-- 构造完全宇宙多态的依值有序对。 -/
add_decl_doc c240.mk

end Manual.ZhDocString.Ch19Ch20.G3
