/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Std.Data.HashMap
import Std.Data.HashMap.Raw
import Std.Data.HashMap.RawLemmas
import Std.Data.DHashMap
import Std.Data.DHashMap.Raw
import Std.Data.DHashMap.RawLemmas
import Std.Data.ExtHashMap
import Std.Data.TreeMap
import Std.Data.DTreeMap
import Std.Data.DTreeMap.Raw
import Std.Data.ExtHashSet
import Std.Data.TreeSet
import Std.Data.HashSet
import Std.Data.HashSet.Raw
import Std.Data.HashSet.RawLemmas
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G1

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w w'

/--
哈希映射。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

这些哈希映射包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.Data.HashMap.Raw` 和 `Std.Data.HashMap.Raw.WF` 将不变量与哈希映射分开。如有疑问，请优先选择 `HashMap` 而不是 `HashMap.Raw`。

依值哈希映射（其中键可能出现在其值的类型中）可用作 `Std.Data.DHashMap`。
-/
structure c001 (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- 哈希映射的内部实现细节。 -/
  inner : Std.DHashMap α (fun _ => β)

/--
创建一个新的空哈希映射。可以提供可选参数 `capacity` 来预先调整映射大小，以便它可以容纳给定数量的映射而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 来创建具有默认容量的空哈希映射。
-/
def c002 := @_root_.Std.HashMap.emptyWithCapacity

/--
哈希映射中存在的映射数量
-/
def c003 := @_root_.Std.HashMap.size

/--
如果哈希映射不包含映射，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使不可能从哈希映射中获取任何内容。
-/
def c004 := @_root_.Std.HashMap.isEmpty

/--
当且仅当所有键和值都相等时，两个哈希映射在 `Equiv` 意义上是等效的。
-/
structure c005 {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}
    (m₁ m₂ : Std.HashMap α β) where
  /-- 哈希映射的内部实现细节。 -/
  inner : m₁.inner.Equiv m₂.inner

/--
如果给定键存在映射，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希映射，两者都使用 `==`。
-/
def c006 := @_root_.Std.HashMap.contains

/--
符号 `m[a]` 或 `m[a]'h` 优于直接调用此函数。

检索给定键的映射。通过要求 `a ∈ m` 的证明来确保此类映射的存在。
-/
def c007 := @_root_.Std.HashMap.get

/--
符号 `m[a]!` 优于直接调用此函数。

尝试检索给定键的映射，如果不存在此类映射，则会触发 panic。
-/
def c008 := @_root_.Std.HashMap.get!

/--
符号 `m[a]?` 优于直接调用此函数。

尝试检索给定键的映射，如果不存在此类映射，则返回 `none`。
-/
def c009 := @_root_.Std.HashMap.get?

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `fallback`。
-/
def c010 := @_root_.Std.HashMap.getD

/--
从映射中检索与 `a` 匹配的键。通过要求 `a ∈ m` 的证明来确保此类映射的存在。结果保证是等于映射中的键的指针。
-/
def c011 := @_root_.Std.HashMap.getKey

/--
检查给定键的映射是否存在，如果存在则返回该键，否则会触发 panic。如果未触发 panic，结果保证是等于映射中的键的指针。
-/
def c012 := @_root_.Std.HashMap.getKey!

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于映射中的键的指针。
-/
def c013 := @_root_.Std.HashMap.getKey?

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `fallback`。如果存在映射，则保证结果是等于映射中键的指针。
-/
def c014 := @_root_.Std.HashMap.getKeyD

/--
按某种顺序返回哈希映射中存在的所有键的列表。
-/
def c015 := @_root_.Std.HashMap.keys

/--
按某种顺序返回哈希映射中存在的所有键的数组。
-/
def c016 := @_root_.Std.HashMap.keysArray

/--
按某种顺序返回哈希映射中存在的所有值的列表。
-/
def c017 := @_root_.Std.HashMap.values

/--
按某种顺序返回哈希映射中存在的所有值的数组。
-/
def c018 := @_root_.Std.HashMap.valuesArray

/--
就地修改与给定键关联的值，允许通过 `Option` 值替换函数创建新值和删除值。

此函数可确保线性使用该值。
-/
def c019 := @_root_.Std.HashMap.alter

/--
就地修改与给定键关联的值。

此函数可确保线性使用该值。
-/
def c020 := @_root_.Std.HashMap.modify

/--
检查映射中是否存在某个键，并无条件插入该键的值。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c021 := @_root_.Std.HashMap.containsThenInsert

/--
检查映射中是否存在某个键，如果未找到，则为该键插入一个值。

如果返回的 `Bool` 是 `true`，则返回的映射不变。如果 `Bool` 是 `false`，则返回的映射已插入新值。

相当于（但可能比）调用 `contains` 后跟 `insertIfNew` 更快。
-/
def c022 := @_root_.Std.HashMap.containsThenInsertIfNew

/--
删除给定键的映射（如果存在）。
-/
def c023 := @_root_.Std.HashMap.erase

/--
删除给定函数返回 `false` 的哈希映射的所有映射。
-/
def c024 := @_root_.Std.HashMap.filter

/--
通过将给定函数应用于所有映射来更新哈希映射的值，仅保留函数返回 `some` 值的那些映射。
-/
def c025 := @_root_.Std.HashMap.filterMap

/--
将给定的映射插入到映射中。如果给定键已经存在映射，则键和值都将被替换。

注意：此替换行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insert` 函数的行为不同：如果匹配的键已存在，它将返回未更改的集合。
-/
def c026 := @_root_.Std.HashMap.insert

/--
如果给定键没有映射，则将给定映射插入到映射中。否则，返回未更改的映射。
-/
def c027 := @_root_.Std.HashMap.insertIfNew

/--
检查映射中是否存在某个键，返回关联的值，如果未找到，则为该键插入一个值。

如果返回值为 `some v`，则返回的映射不变。如果是 `none`，则返回的映射已插入新值。

相当于（但可能比）调用 `get?` 后跟 `insertIfNew` 更快。
-/
def c028 := @_root_.Std.HashMap.getThenInsertIfNew?

/--
通过迭代给定集合并调用 `insert`，将多个映射插入哈希映射。如果同一键出现多次，则最后一次出现的键优先。

注意：此优先行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insertMany` 函数的行为不同：它会更喜欢第一次出现。
-/
def c029 := @_root_.Std.HashMap.insertMany

/--
通过迭代给定集合并调用 `insertIfNew`，将多个值为 `()` 的键插入到哈希映射中。如果同一个键出现多次，则第一次出现的键优先。

这主要用于实现 `HashSet.insertMany`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c030 := @_root_.Std.HashMap.insertManyIfNewUnit

/--
根据谓词将哈希映射划分为两个哈希映射。
-/
def c031 := @_root_.Std.HashMap.partition

/--
计算给定哈希映射的并集。如果一个键同时出现在两个映射中，则第二个参数中包含的条目将出现在结果中。

该函数始终将较小的映射合并到较大的映射中，因此预期运行时间为 `O(min(m₁.size, m₂.size))`。
-/
def c032 := @_root_.Std.HashMap.union

/--
返回哈希映射条目上的有限迭代器。迭代器按顺序生成映射的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c033 := @_root_.Std.HashMap.iter

/--
返回哈希映射条目上的有限迭代器。迭代器按顺序生成映射的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c034 := @_root_.Std.HashMap.keysIter

/--
返回哈希映射条目上的有限迭代器。迭代器按顺序生成映射的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c035 := @_root_.Std.HashMap.valuesIter

/--
通过将给定函数应用于所有映射来更新哈希映射的值。
-/
def c036 := @_root_.Std.HashMap.map

/--
按某种顺序将给定函数折叠到哈希映射中的映射上。
-/
def c037 := @_root_.Std.HashMap.fold

/--
通过按某种顺序将给定函数折叠到哈希映射中的映射来单子地计算值。
-/
def c038 := @_root_.Std.HashMap.foldM

/--
支持 `do` 块中的 `for` 循环构造。
-/
def c039 := @_root_.Std.HashMap.forIn

/--
按某种顺序对哈希映射中的每个映射执行单子操作。
-/
def c040 := @_root_.Std.HashMap.forM

/--
从映射列表创建哈希映射。如果同一键出现多次，则最后一次出现的键优先。
-/
def c041 := @_root_.Std.HashMap.ofList

/--
按某种顺序将哈希映射转换为映射数组。
-/
def c042 := @_root_.Std.HashMap.toArray

/--
将哈希映射按某种顺序转换为映射列表。
-/
def c043 := @_root_.Std.HashMap.toList

/--
从键数组创建哈希映射，将值 `()` 与每个键相关联。

这主要用于实现 `HashSet.ofArray`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c044 := @_root_.Std.HashMap.unitOfArray

/--
从键列表创建哈希映射，将值 `()` 与每个键相关联。

这主要用于实现 `HashSet.ofList`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c045 := @_root_.Std.HashMap.unitOfList

/--
没有内置的良构不变量的哈希映射，适合在嵌套归纳类型中使用。良构的不变量称为 `Raw.WF`。如有疑问，请优先选择 `HashMap` 而不是 `HashMap.Raw`。关于 `Std.Data.HashMap.Raw` 操作的引理可在模块 `Std.Data.HashMap.RawLemmas` 中找到。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

依值哈希映射（其中键可能出现在其值的类型中）可用作 `Std.Data.Raw.DHashMap`。
-/
structure c046 (α : Type u) (β : Type v) where
  /-- 哈希映射的内部实现细节。 -/
  inner : Std.DHashMap.Raw α (fun _ => β)

/--
哈希映射的良构谓词。 `HashMap` 的用户不需要与之交互。 `HashMap.Raw` 的用户需要向引理提供 `WF` 的证明，并且应该使用引理 `WF.empty` 和 `WF.insert`（它们的命名始终与它们所涉及的操作完全相同）来表明映射操作保持良构。
-/
structure c047 {α : Type u} {β : Type v} [BEq α] [Hashable α]
    (m : Std.HashMap.Raw α β) : Prop where
  /-- 哈希映射的内部实现细节。 -/
  out : m.inner.WF

/--
依值哈希映射。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

这些哈希映射包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.DHashMap.Raw` 和 `Std.DHashMap.Raw.WF` 将不变量与哈希映射分开。如有疑问，请优先选择 `DHashMap` 而不是 `DHashMap.Raw`。

对于由于外延性而更方便在证明中使用的变体，请参阅模块 `Std.Data.ExtDHashMap` 中定义的 `Std.ExtDHashMap`。
-/
structure c048 (α : Type u) (β : α → Type v) [BEq α] [Hashable α] where
  /-- 哈希映射的内部实现细节。 -/
  inner : Std.DHashMap.Raw α β
  /-- 哈希映射的内部实现细节。 -/
  wf : inner.WF

/--
创建一个新的空哈希映射。可以提供可选参数 `capacity` 来预先调整映射大小，以便它可以容纳给定数量的映射而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 来创建具有默认容量的空哈希映射。
-/
def c049 := @_root_.Std.DHashMap.emptyWithCapacity

/--
哈希映射中存在的映射数量
-/
def c050 := @_root_.Std.DHashMap.size

/--
如果哈希映射不包含映射，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使不可能从哈希映射中获取任何内容。
-/
def c051 := @_root_.Std.DHashMap.isEmpty

/--
当且仅当所有键和值都相等时，两个哈希映射在 `Equiv` 意义上是等效的。
-/
structure c052 {α : Type u} {β : α → Type v} {_ : BEq α} {_ : Hashable α}
    (m₁ m₂ : Std.DHashMap α β) where
  /-- 哈希映射的内部实现细节。 -/
  inner : m₁.inner.Equiv m₂.inner

/--
如果给定键存在映射，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希映射，两者都使用 `==`。
-/
def c053 := @_root_.Std.DHashMap.contains

/--
检索给定键的映射。通过要求 `a ∈ m` 的证明来确保此类映射的存在。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c054 := @_root_.Std.DHashMap.get

/--
尝试检索给定键的映射，如果不存在此类映射，则会触发 panic。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c055 := @_root_.Std.DHashMap.get!

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `none`。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c056 := @_root_.Std.DHashMap.get?

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `fallback`。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c057 := @_root_.Std.DHashMap.getD

/--
从映射中检索与 `a` 匹配的键。通过要求 `a ∈ m` 的证明来确保此类映射的存在。结果保证是等于映射中的键的指针。
-/
def c058 := @_root_.Std.DHashMap.getKey

/--
检查给定键的映射是否存在，如果存在则返回该键，否则会触发 panic。如果未触发 panic，结果保证是等于映射中的键的指针。
-/
def c059 := @_root_.Std.DHashMap.getKey!

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于映射中的键的指针。
-/
def c060 := @_root_.Std.DHashMap.getKey?

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `fallback`。如果存在映射，则保证结果是等于映射中键的指针。
-/
def c061 := @_root_.Std.DHashMap.getKeyD

/--
按某种顺序返回哈希映射中存在的所有键的列表。
-/
def c062 := @_root_.Std.DHashMap.keys

/--
按某种顺序返回哈希映射中存在的所有键的数组。
-/
def c063 := @_root_.Std.DHashMap.keysArray

/--
按某种顺序返回哈希映射中存在的所有值的列表。
-/
def c064 := @_root_.Std.DHashMap.values

/--
按某种顺序返回哈希映射中存在的所有值的数组。
-/
def c065 := @_root_.Std.DHashMap.valuesArray

/--
就地修改与给定键关联的值，允许通过 `Option` 值替换函数创建新值和删除值。

此函数可确保线性使用该值。
-/
def c066 := @_root_.Std.DHashMap.alter

/--
就地修改与给定键关联的值。

此函数可确保线性使用该值。
-/
def c067 := @_root_.Std.DHashMap.modify

/--
检查映射中是否存在某个键，并无条件插入该键的值。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c068 := @_root_.Std.DHashMap.containsThenInsert

/--
检查映射中是否存在某个键，如果未找到，则为该键插入一个值。

如果返回的 `Bool` 是 `true`，则返回的映射不变。如果 `Bool` 是 `false`，则返回的映射已插入新值。

相当于（但可能比）调用 `contains` 后跟 `insertIfNew` 更快。
-/
def c069 := @_root_.Std.DHashMap.containsThenInsertIfNew

/--
删除给定键的映射（如果存在）。
-/
def c070 := @_root_.Std.DHashMap.erase

/--
删除给定函数返回 `false` 的哈希映射的所有映射。
-/
def c071 := @_root_.Std.DHashMap.filter

/--
通过将给定函数应用于所有映射来更新哈希映射的值，仅保留函数返回 `some` 值的那些映射。
-/
def c072 := @_root_.Std.DHashMap.filterMap

/--
将给定的映射插入到映射中。如果给定键已经存在映射，则键和值都将被替换。

注意：此替换行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insert` 函数的行为不同：如果匹配的键已存在，它将返回未更改的集合。
-/
def c073 := @_root_.Std.DHashMap.insert

/--
如果给定键没有映射，则将给定映射插入到映射中。否则，返回未更改的映射。
-/
def c074 := @_root_.Std.DHashMap.insertIfNew

/--
检查映射中是否存在某个键，返回关联的值，如果未找到，则为该键插入一个值。

如果返回值为 `some v`，则返回的映射不变。如果是 `none`，则返回的映射已插入新值。

相当于（但可能比）调用 `get?` 后跟 `insertIfNew` 更快。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c075 := @_root_.Std.DHashMap.getThenInsertIfNew?

/--
通过迭代给定集合并调用 `insert`，将多个映射插入哈希映射。如果同一键出现多次，则最后一次出现的键优先。

注意：此优先行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insertMany` 函数的行为不同：它会更喜欢第一次出现。
-/
def c076 := @_root_.Std.DHashMap.insertMany

/--
根据谓词将哈希映射划分为两个哈希映射。
-/
def c077 := @_root_.Std.DHashMap.partition

/--
计算给定哈希映射的并集。如果一个键同时出现在两个映射中，则第二个参数中包含的条目将出现在结果中。

该函数始终将较小的映射合并到较大的映射中，因此预期运行时间为 `O(min(m₁.size, m₂.size))`。
-/
def c078 := @_root_.Std.DHashMap.union

/--
返回依值哈希映射条目上的有限迭代器。迭代器按顺序生成映射的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c079 := @_root_.Std.DHashMap.iter

/--
返回依值哈希映射的键上的有限迭代器。迭代器按顺序生成键，然后终止。

键和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c080 := @_root_.Std.DHashMap.keysIter

/--
返回哈希映射值的有限迭代器。迭代器按顺序产生值，然后终止。

键和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c081 := @_root_.Std.DHashMap.valuesIter

/--
通过将给定函数应用于所有映射来更新哈希映射的值。
-/
def c082 := @_root_.Std.DHashMap.map

/--
按某种顺序将给定函数折叠到哈希映射中的映射上。
-/
def c083 := @_root_.Std.DHashMap.fold

/--
通过按某种顺序将给定函数折叠到哈希映射中的映射来单子地计算值。
-/
def c084 := @_root_.Std.DHashMap.foldM

/--
支持 `do` 块中的 `for` 循环构造。
-/
def c085 := @_root_.Std.DHashMap.forIn

/--
按某种顺序对哈希映射中的每个映射执行单子操作。
-/
def c086 := @_root_.Std.DHashMap.forM

/--
从映射列表创建哈希映射。如果同一键出现多次，则最后一次出现的键优先。
-/
def c087 := @_root_.Std.DHashMap.ofList

/--
按某种顺序将哈希映射转换为映射数组。
-/
def c088 := @_root_.Std.DHashMap.toArray

/--
将哈希映射按某种顺序转换为映射列表。
-/
def c089 := @_root_.Std.DHashMap.toList

/--
没有内置的良构不变量的依值哈希映射，适合在嵌套归纳类型中使用。良构的不变量称为 `Raw.WF`。如有疑问，请优先选择 `DHashMap` 而不是 `DHashMap.Raw`。关于 `Std.Data.DHashMap.Raw` 操作的引理可在模块 `Std.Data.DHashMap.RawLemmas` 中找到。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。
-/
structure c090 (α : Type u) (β : α → Type v) where
  /-- 哈希映射中的映射数量。 -/
  size : Nat
  /-- 哈希映射的内部实现细节。 -/
  buckets : Array (Std.DHashMap.Internal.AssocList α β)

/--
哈希映射的良构谓词。 `DHashMap` 的用户不需要与之交互。 `DHashMap.Raw` 的用户需要向引理提供 `WF` 的证明，并且应该使用像 `WF.empty` 和 `WF.insert` 这样的引理（它们的命名总是与它们所涉及的操作完全相同）来表明映射操作保持良构。该类型的构造函数是内部实现细节，用户不应访问。
-/
inductive c091 : {α : Type u} → {β : α → Type v} → [BEq α] → [Hashable α] →
    Std.DHashMap.Raw α β → Prop where
  /-- 哈希映射的内部实现细节。 -/
  | wf {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} :
      0 < m.buckets.size →
      (∀ [EquivBEq α] [LawfulHashable α], Std.DHashMap.Internal.Raw.WFImp m) → c091 m
  /-- 哈希映射的内部实现细节。 -/
  | emptyWithCapacity₀ {α β : _} [BEq α] [Hashable α] {c} :
      c091 (Std.DHashMap.Internal.Raw₀.emptyWithCapacity c : Std.DHashMap.Internal.Raw₀ α β).1
  /-- 哈希映射的内部实现细节。 -/
  | insert₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.insert ⟨m, h⟩ a b).1
  /-- 哈希映射的内部实现细节。 -/
  | containsThenInsert₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.containsThenInsert ⟨m, h⟩ a b).2.1
  /-- 哈希映射的内部实现细节。 -/
  | containsThenInsertIfNew₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.containsThenInsertIfNew ⟨m, h⟩ a b).2.1
  /-- 哈希映射的内部实现细节。 -/
  | erase₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h a} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.erase ⟨m, h⟩ a).1
  /-- 哈希映射的内部实现细节。 -/
  | insertIfNew₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.insertIfNew ⟨m, h⟩ a b).1
  /-- 哈希映射的内部实现细节。 -/
  | getThenInsertIfNew?₀ {α β : _} [BEq α] [Hashable α] [LawfulBEq α]
      {m : Std.DHashMap.Raw α β} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b).2.1
  /-- 哈希映射的内部实现细节。 -/
  | filter₀ {α β : _} [BEq α] [Hashable α] {m : Std.DHashMap.Raw α β} {h f} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.filter f ⟨m, h⟩).1
  /-- 哈希映射的内部实现细节。 -/
  | constGetThenInsertIfNew?₀ {α β : _} [BEq α] [Hashable α]
      {m : Std.DHashMap.Raw α (fun _ => β)} {h a b} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b).2.1
  /-- 哈希映射的内部实现细节。 -/
  | modify₀ {α β : _} [BEq α] [Hashable α] [LawfulBEq α]
      {m : Std.DHashMap.Raw α β} {h a} {f : β a → β a} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.modify ⟨m, h⟩ a f).1
  /-- 哈希映射的内部实现细节。 -/
  | constModify₀ {α : _} {β : Type v} [BEq α] [Hashable α]
      {m : Std.DHashMap.Raw α (fun _ => β)} {h a} {f : β → β} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.Const.modify ⟨m, h⟩ a f).1
  /-- 哈希映射的内部实现细节。 -/
  | alter₀ {α β : _} [BEq α] [Hashable α] [LawfulBEq α]
      {m : Std.DHashMap.Raw α β} {h a} {f : Option (β a) → Option (β a)} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.alter ⟨m, h⟩ a f).1
  /-- 哈希映射的内部实现细节。 -/
  | constAlter₀ {α : _} {β : Type v} [BEq α] [Hashable α]
      {m : Std.DHashMap.Raw α (fun _ => β)} {h a} {f : Option β → Option β} :
      c091 m → c091 (Std.DHashMap.Internal.Raw₀.Const.alter ⟨m, h⟩ a f).1
  /-- 哈希映射的内部实现细节。 -/
  | inter₀ {α β : _} [BEq α] [Hashable α] {m₁ m₂ : Std.DHashMap.Raw α β} {h₁ h₂} :
      c091 m₁ → c091 m₂ → c091 (Std.DHashMap.Internal.Raw₀.inter ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1

/--
哈希映射。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

与常规哈希映射相比，`Std.ExtHashMap` 提供了多个外延引理，因此具有更多关于哈希映射相等性的引理。然而，这也使其失去了自由迭代哈希映射的能力。

这些哈希映射包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.HashMap.Raw` 和 `Std.HashMap.Raw.WF` 将不变量与哈希映射分开。如有疑问，请优先选择 `HashMap` 或 `ExtHashMap` 而不是 `HashMap.Raw`。

依值哈希映射（其中键可能出现在其值的类型中）在模块 `Std.Data.ExtDHashMap` 中以 `Std.ExtDHashMap` 形式提供。
-/
structure c092 (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- 哈希映射的内部实现细节。 -/
  inner : Std.ExtDHashMap α (fun _ => β)

/--
创建一个新的空哈希映射。可以提供可选参数 `capacity` 来预先调整映射大小，以便它可以容纳给定数量的映射而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 来创建具有默认容量的空哈希映射。
-/
def c093 := @_root_.Std.ExtHashMap.emptyWithCapacity

/--
哈希映射中存在的映射数量
-/
def c094 := @_root_.Std.ExtHashMap.size

/--
如果哈希映射不包含映射，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使不可能从哈希映射中获取任何内容。
-/
def c095 := @_root_.Std.ExtHashMap.isEmpty

/--
如果给定键存在映射，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希映射，两者都使用 `==`。
-/
def c096 := @_root_.Std.ExtHashMap.contains

/--
符号 `m[a]` 或 `m[a]'h` 优于直接调用此函数。

检索给定键的映射。通过要求 `a ∈ m` 的证明来确保此类映射的存在。
-/
def c097 := @_root_.Std.ExtHashMap.get

/--
符号 `m[a]!` 优于直接调用此函数。

尝试检索给定键的映射，如果不存在此类映射，则会触发 panic。
-/
def c098 := @_root_.Std.ExtHashMap.get!

/--
符号 `m[a]?` 优于直接调用此函数。

尝试检索给定键的映射，如果不存在此类映射，则返回 `none`。
-/
def c099 := @_root_.Std.ExtHashMap.get?

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `fallback`。
-/
def c100 := @_root_.Std.ExtHashMap.getD

/--
从映射中检索与 `a` 匹配的键。通过要求 `a ∈ m` 的证明来确保此类映射的存在。结果保证是等于映射中的键的指针。
-/
def c101 := @_root_.Std.ExtHashMap.getKey

/--
检查给定键的映射是否存在，如果存在则返回该键，否则会触发 panic。如果未触发 panic，结果保证是等于映射中的键的指针。
-/
def c102 := @_root_.Std.ExtHashMap.getKey!

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于映射中的键的指针。
-/
def c103 := @_root_.Std.ExtHashMap.getKey?

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `fallback`。如果存在映射，则保证结果是等于映射中键的指针。
-/
def c104 := @_root_.Std.ExtHashMap.getKeyD

/--
就地修改与给定键关联的值，允许通过 `Option` 值替换函数创建新值和删除值。

此函数可确保线性使用该值。
-/
def c105 := @_root_.Std.ExtHashMap.alter

/--
就地修改与给定键关联的值。

此函数可确保线性使用该值。
-/
def c106 := @_root_.Std.ExtHashMap.modify

/--
检查映射中是否存在某个键，并无条件插入该键的值。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c107 := @_root_.Std.ExtHashMap.containsThenInsert

/--
检查映射中是否存在某个键，如果未找到，则为该键插入一个值。

如果返回的 `Bool` 是 `true`，则返回的映射不变。如果 `Bool` 是 `false`，则返回的映射已插入新值。

相当于（但可能比）调用 `contains` 后跟 `insertIfNew` 更快。
-/
def c108 := @_root_.Std.ExtHashMap.containsThenInsertIfNew

/--
删除给定键的映射（如果存在）。
-/
def c109 := @_root_.Std.ExtHashMap.erase

/--
删除给定函数返回 `false` 的哈希映射的所有映射。
-/
def c110 := @_root_.Std.ExtHashMap.filter

/--
通过将给定函数应用于所有映射来更新哈希映射的值，仅保留函数返回 `some` 值的那些映射。
-/
def c111 := @_root_.Std.ExtHashMap.filterMap

/--
将给定的映射插入到映射中。如果给定键已经存在映射，则键和值都将被替换。

注意：此替换行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insert` 函数的行为不同：如果匹配的键已存在，它将返回未更改的集合。
-/
def c112 := @_root_.Std.ExtHashMap.insert

/--
如果给定键没有映射，则将给定映射插入到映射中。否则，返回未更改的映射。
-/
def c113 := @_root_.Std.ExtHashMap.insertIfNew

/--
检查映射中是否存在某个键，返回关联的值，如果未找到，则为该键插入一个值。

如果返回值为 `some v`，则返回的映射不变。如果是 `none`，则返回的映射已插入新值。

相当于（但可能比）调用 `get?` 后跟 `insertIfNew` 更快。
-/
def c114 := @_root_.Std.ExtHashMap.getThenInsertIfNew?

/--
通过迭代给定集合并调用 `insert`，将多个映射插入哈希映射。如果同一键出现多次，则最后一次出现的键优先。

注意：此优先行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insertMany` 函数的行为不同：它会更喜欢第一次出现。
-/
def c115 := @_root_.Std.ExtHashMap.insertMany

/--
通过迭代给定集合并调用 `insertIfNew`，将多个值为 `()` 的键插入到哈希映射中。如果同一个键出现多次，则第一次出现的键优先。

这主要用于实现 `HashSet.insertMany`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c116 := @_root_.Std.ExtHashMap.insertManyIfNewUnit

/--
通过将给定函数应用于所有映射来更新哈希映射的值。
-/
def c117 := @_root_.Std.ExtHashMap.map

/--
从映射列表创建哈希映射。如果同一键出现多次，则最后一次出现的键优先。
-/
def c118 := @_root_.Std.ExtHashMap.ofList

/--
从键数组创建哈希映射，将值 `()` 与每个键相关联。

这主要用于实现 `HashSet.ofArray`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c119 := @_root_.Std.ExtHashMap.unitOfArray

/--
从键列表创建哈希映射，将值 `()` 与每个键相关联。

这主要用于实现 `HashSet.ofList`，因此如果您正在考虑使用它，`HashSet` 或 `HashSet.Raw` 可能更适合您。
-/
def c120 := @_root_.Std.ExtHashMap.unitOfList

/--
外延依值哈希映射。

这是一个简单的分离链接哈希表。哈希映射的数据由缓存的大小和桶数组组成，其中每个桶是键值对的链表。桶的数量始终是2的幂。哈希映射在插入元素时将其大小加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保线性使用哈希映射以避免昂贵的复制。

哈希映射使用 `==`（由 `BEq` 类型类提供）来比较键，并使用 `hash`（由 `Hashable` 类型类提供）来对它们进行哈希处理。为了确保操作按预期运行，`==` 必须是等价关系，并且 `a == b` 必须隐含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

与常规依值哈希映射相比，`Std.ExtDHashMap` 提供了多个外延引理，因此具有更多关于哈希映射相等性的引理。然而，这也使其失去了自由迭代哈希映射的能力。

这些哈希映射包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.DHashMap.Raw` 和 `Std.DHashMap.Raw.WF` 将不变量与哈希映射分开。如有疑问，请优先选择 `DHashMap` 而不是 `DHashMap.Raw`。
-/
structure c121 (α : Type u) (β : α → Type v) [BEq α] [Hashable α] where
  mk' ::
  /-- 哈希映射的内部实现细节。 -/
  inner : Quotient (Std.DHashMap.isSetoid α β)

/--
创建一个新的空哈希映射。可以提供可选参数 `capacity` 来预先调整映射大小，以便它可以容纳给定数量的映射而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 来创建具有默认容量的空哈希映射。
-/
def c122 := @_root_.Std.ExtDHashMap.emptyWithCapacity

/--
哈希映射中存在的映射数量
-/
def c123 := @_root_.Std.ExtDHashMap.size

/--
如果哈希映射不包含映射，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使不可能从哈希映射中获取任何内容。
-/
def c124 := @_root_.Std.ExtDHashMap.isEmpty

/--
如果给定键存在映射，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希映射，两者都使用 `==`。
-/
def c125 := @_root_.Std.ExtDHashMap.contains

/--
检索给定键的映射。通过要求 `a ∈ m` 的证明来确保此类映射的存在。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c126 := @_root_.Std.ExtDHashMap.get

/--
尝试检索给定键的映射，如果不存在此类映射，则会触发 panic。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c127 := @_root_.Std.ExtDHashMap.get!

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `none`。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c128 := @_root_.Std.ExtDHashMap.get?

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `fallback`。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c129 := @_root_.Std.ExtDHashMap.getD

/--
从映射中检索与 `a` 匹配的键。通过要求 `a ∈ m` 的证明来确保此类映射的存在。结果保证是等于映射中的键的指针。
-/
def c130 := @_root_.Std.ExtDHashMap.getKey

/--
检查给定键的映射是否存在，如果存在则返回该键，否则会触发 panic。如果未触发 panic，结果保证是等于映射中的键的指针。
-/
def c131 := @_root_.Std.ExtDHashMap.getKey!

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于映射中的键的指针。
-/
def c132 := @_root_.Std.ExtDHashMap.getKey?

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `fallback`。如果存在映射，则保证结果是等于映射中键的指针。
-/
def c133 := @_root_.Std.ExtDHashMap.getKeyD

/--
就地修改与给定键关联的值，允许通过 `Option` 值替换函数创建新值和删除值。

此函数可确保线性使用该值。
-/
def c134 := @_root_.Std.ExtDHashMap.alter

/--
就地修改与给定键关联的值。

此函数可确保线性使用该值。
-/
def c135 := @_root_.Std.ExtDHashMap.modify

/--
检查映射中是否存在某个键，并无条件插入该键的值。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c136 := @_root_.Std.ExtDHashMap.containsThenInsert

/--
检查映射中是否存在某个键，如果未找到，则为该键插入一个值。

如果返回的 `Bool` 是 `true`，则返回的映射不变。如果 `Bool` 是 `false`，则返回的映射已插入新值。

相当于（但可能比）调用 `contains` 后跟 `insertIfNew` 更快。
-/
def c137 := @_root_.Std.ExtDHashMap.containsThenInsertIfNew

/--
删除给定键的映射（如果存在）。
-/
def c138 := @_root_.Std.ExtDHashMap.erase

/--
删除给定函数返回 `false` 的哈希映射的所有映射。
-/
def c139 := @_root_.Std.ExtDHashMap.filter

/--
通过将给定函数应用于所有映射来更新哈希映射的值，仅保留函数返回 `some` 值的那些映射。
-/
def c140 := @_root_.Std.ExtDHashMap.filterMap

/--
将给定的映射插入到映射中。如果给定键已经存在映射，则键和值都将被替换。

注意：此替换行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insert` 函数的行为不同：如果匹配的键已存在，它将返回未更改的集合。
-/
def c141 := @_root_.Std.ExtDHashMap.insert

/--
如果给定键没有映射，则将给定映射插入到映射中。否则，返回未更改的映射。
-/
def c142 := @_root_.Std.ExtDHashMap.insertIfNew

/--
检查映射中是否存在某个键，返回关联的值，如果未找到，则为该键插入一个值。

如果返回值为 `some v`，则返回的映射不变。如果是 `none`，则返回的映射已插入新值。

相当于（但可能比）调用 `get?` 后跟 `insertIfNew` 更快。

使用 `LawfulBEq` 实例将检索到的值转换为正确的类型。
-/
def c143 := @_root_.Std.ExtDHashMap.getThenInsertIfNew?

/--
通过迭代给定集合并调用 `insert`，将多个映射插入哈希映射。如果同一键出现多次，则最后一次出现的键优先。

注意：此优先行为适用于 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw`。 `HashSet` 和 `HashSet.Raw` 上的 `insertMany` 函数的行为不同：它会更喜欢第一次出现。
-/
def c144 := @_root_.Std.ExtDHashMap.insertMany

/--
通过将给定函数应用于所有映射来更新哈希映射的值。
-/
def c145 := @_root_.Std.ExtDHashMap.map

/--
从映射列表创建哈希映射。如果同一键出现多次，则最后一次出现的键优先。
-/
def c146 := @_root_.Std.ExtDHashMap.ofList

/--
哈希集。

这是一个简单的分离链接哈希表。哈希集的数据由缓存大小和桶数组组成，其中每个桶是键的链表。桶的数量始终是2的幂。插入元素后，哈希集的大小会加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保哈希集是线性使用的，以避免昂贵的复制。

哈希集使用 `==`（由 `BEq` 类型类提供）来比较元素，并使用 `hash`（由 `Hashable` 类型类提供）对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

这些哈希集包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.Data.HashSet.Raw` 和 `Std.Data.HashSet.Raw.WF` 将不变量与哈希集分开。如有疑问，请优先选择 `HashSet` 而不是 `HashSet.Raw`。
-/
structure c147 (α : Type u) [BEq α] [Hashable α] where
  /-- 哈希集合的内部实现细节。 -/
  inner : Std.HashMap α Unit

/--
创建一个新的空哈希集。可以提供可选参数 `capacity` 来预先调整集合的大小，以便它可以容纳给定数量的元素而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 创建具有默认容量的空哈希集。
-/
def c148 := @_root_.Std.HashSet.emptyWithCapacity

/--
如果哈希集不包含元素，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使对于所有 `a` 来说都是 `m.contains a = false`。
-/
def c149 := @_root_.Std.HashSet.isEmpty

/--
集合中存在的元素数量
-/
def c150 := @_root_.Std.HashSet.size

/--
两个哈希集在 `Equiv` 意义上是等效的，当且仅当它们的所有值都相等。
-/
structure c151 {α : Type u} {_ : BEq α} {_ : Hashable α}
    (m₁ m₂ : Std.HashSet α) where
  /-- 哈希映射的内部实现细节。 -/
  inner : m₁.inner.Equiv m₂.inner

/--
如果给定的键存在于集合中，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希集，两者都使用 `==`。
-/
def c152 := @_root_.Std.HashSet.contains

/--
从匹配 `a` 的集合中检索键。通过要求 `a ∈ m` 的证明来确保这样的键存在。结果保证是等于集合中的键的指针。
-/
def c153 := @_root_.Std.HashSet.get

/--
检查是否包含给定的键，如果包含则返回该键，否则会触发 panic。如果未触发 panic，则结果保证是等于集合中的键的指针。
-/
def c154 := @_root_.Std.HashSet.get!

/--
检查是否包含给定的键，如果包含则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于集合中的键的指针。
-/
def c155 := @_root_.Std.HashSet.get?

/--
检查是否包含给定的键，如果包含则返回该键，否则返回 `fallback`。如果包含它们的键，则保证结果是等于集合中的键的指针。
-/
def c156 := @_root_.Std.HashSet.getD

/--
将给定元素插入集合中。如果哈希集已包含与给定元素相等（关于 `==`）的元素，则哈希集将原样返回。

注意：这种非替换行为对于 `HashSet` 和 `HashSet.Raw` 来说是正确的。 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw` 上的 `insert` 函数的行为不同：它将覆盖现有映射。
-/
def c157 := @_root_.Std.HashSet.insert

/--
通过迭代给定集合并调用 `insert`，将多个映射插入到哈希集中。如果同一个键出现多次，则第一次出现的键优先。

注意：此优先行为适用于 `HashSet` 和 `HashSet.Raw`。 `HashMap`、`DHashMap`、`HashMap.Raw` 和 `DHashMap.Raw` 上的 `insertMany` 函数的行为有所不同：它会更喜欢最后的外观。
-/
def c158 := @_root_.Std.HashSet.insertMany

/--
删除该元素（如果存在）。
-/
def c159 := @_root_.Std.HashSet.erase

/--
从哈希集中删除给定函数返回 `false` 的所有元素。
-/
def c160 := @_root_.Std.HashSet.filter

/--
检查集合中是否存在某个元素，如果未找到则插入该元素。如果哈希集已包含与给定元素相等（关于 `==`）的元素，则哈希集将原样返回。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c161 := @_root_.Std.HashSet.containsThenInsert

/--
根据谓词将哈希集划分为两个哈希集。
-/
def c162 := @_root_.Std.HashSet.partition

/--
计算给定哈希集的并集。

此函数始终将较小的集合合并到较大的集合中，因此预期运行时间为 `O(min(m₁.size, m₂.size))`。
-/
def c163 := @_root_.Std.HashSet.union

/--
返回哈希集元素的有限迭代器。迭代器按顺序产生集合的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c164 := @_root_.Std.HashSet.iter

/--
检查是否所有元素都满足谓词，如果谓词失败则短路。
-/
def c165 := @_root_.Std.HashSet.all

/--
检查是否有任何元素满足谓词，如果谓词成功则短路。
-/
def c166 := @_root_.Std.HashSet.any

/--
按某种顺序将给定函数折叠到哈希集的元素上。
-/
def c167 := @_root_.Std.HashSet.fold

/--
通过按某种顺序将给定函数折叠到哈希集中的元素上，单子地计算一个值。
-/
def c168 := @_root_.Std.HashSet.foldM

/--
支持 `do` 块中的 `for` 循环构造。
-/
def c169 := @_root_.Std.HashSet.forIn

/--
按某种顺序对哈希集中的每个元素执行单子操作。
-/
def c170 := @_root_.Std.HashSet.forM

/--
从元素列表创建哈希集。请注意，与重复调用 `insert` 不同，如果集合包含多个相等的元素（对于 `==`），则集合中的最后一个元素将出现在返回的哈希集中。
-/
def c171 := @_root_.Std.HashSet.ofList

/--
将哈希集按某种顺序转换为元素列表。
-/
def c172 := @_root_.Std.HashSet.toList

/--
从元素数组创建哈希集。请注意，与重复调用 `insert` 不同，如果集合包含多个相等的元素（对于 `==`），则集合中的最后一个元素将出现在返回的哈希集中。
-/
def c173 := @_root_.Std.HashSet.ofArray

/--
将哈希集按某种顺序转换为元素数组。
-/
def c174 := @_root_.Std.HashSet.toArray

/--
没有内置的良构不变量的哈希集，适合在嵌套归纳类型中使用。良构的不变量称为 `Raw.WF`。如有疑问，请优先选择 `HashSet` 而不是 `HashSet.Raw`。关于 `Std.Data.HashSet.Raw` 操作的引理可在模块 `Std.Data.HashSet.RawLemmas` 中找到。

这是一个简单的分离链接哈希表。哈希集的数据由缓存大小和桶数组组成，其中每个桶是键的链表。桶的数量始终是2的幂。插入元素后，哈希集的大小会加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保哈希集是线性使用的，以避免昂贵的复制。

哈希集使用 `==`（由 `BEq` 类型类提供）来比较元素，并使用 `hash`（由 `Hashable` 类型类提供）对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。
-/
structure c175 (α : Type u) where
  /-- 哈希集合的内部实现细节。 -/
  inner : Std.HashMap.Raw α Unit

/--
哈希集的良构谓词。 `HashSet` 的用户不需要与之交互。 `HashSet.Raw` 的用户需要向引理提供 `WF` 的证明，并且应该使用像 `WF.empty` 和 `WF.insert` 这样的引理（它们的命名总是与它们所涉及的操作完全相同）来表明集合操作保持良构。
-/
structure c176 {α : Type u} [BEq α] [Hashable α]
    (m : Std.HashSet.Raw α) : Prop where
  /-- 哈希集合的内部实现细节。 -/
  out : m.inner.WF

/--
哈希集。

这是一个简单的分离链接哈希表。哈希集的数据由缓存大小和桶数组组成，其中每个桶是键的链表。桶的数量始终是2的幂。插入元素后，哈希集的大小会加倍，使得元素数量超过桶数量的 75%。

该哈希表由 `Array` 作为后备存储。用户应确保哈希集是线性使用的，以避免昂贵的复制。

哈希集使用 `==`（由 `BEq` 类型类提供）来比较元素，并使用 `hash`（由 `Hashable` 类型类提供）对它们进行哈希处理。为了确保操作按预期运行，`==` 应该是等价关系，而 `a == b` 应该蕴含 `hash a = hash b`（另请参见 `EquivBEq` 和 `LawfulHashable` 类型类）。如果 `BEq` 实例合法，即如果 `a == b` 蕴含 `a = b`，这两个条件都是自动的。

与常规哈希集相比，`Std.ExtHashSet` 提供了多个外延引理，因此具有更多关于哈希映射相等性的引理。然而，这也使其失去了自由迭代哈希集的能力。

这些哈希集包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.HashSet.Raw` 和 `Std.HashSet.Raw.WF` 将不变量与哈希集分开。如有疑问，请优先选择 `HashSet` 或 `ExtHashSet` 而不是 `HashSet.Raw`。
-/
structure c177 (α : Type u) [BEq α] [Hashable α] where
  /-- 哈希集合的内部实现细节。 -/
  inner : Std.ExtHashMap α Unit

/--
创建一个新的空哈希集。可以提供可选参数 `capacity` 来预先调整集合的大小，以便它可以容纳给定数量的元素而无需重新分配。还可以使用空集合符号 `∅` 和 `{}` 创建具有默认容量的空哈希集。
-/
def c178 := @_root_.Std.ExtHashSet.emptyWithCapacity

/--
如果哈希集不包含元素，则返回 `true`。

请注意，如果您的 `BEq` 实例不是自反的，或者您的 `Hashable` 实例不合法，则该函数有可能返回 `false`，即使对于所有 `a` 来说都是 `m.contains a = false`。
-/
def c179 := @_root_.Std.ExtHashSet.isEmpty

/--
集合中存在的元素数量
-/
def c180 := @_root_.Std.ExtHashSet.size

/--
如果给定的键存在于集合中，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ m` 相当于 `m.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行比较，而对于哈希集，两者都使用 `==`。
-/
def c181 := @_root_.Std.ExtHashSet.contains

/--
从匹配 `a` 的集合中检索键。通过要求 `a ∈ m` 的证明来确保这样的键存在。结果保证是等于集合中的键的指针。
-/
def c182 := @_root_.Std.ExtHashSet.get

/--
检查是否包含给定的键，如果包含则返回该键，否则会触发 panic。如果未触发 panic，则结果保证是等于集合中的键的指针。
-/
def c183 := @_root_.Std.ExtHashSet.get!

/--
检查是否包含给定的键，如果包含则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于集合中的键的指针。
-/
def c184 := @_root_.Std.ExtHashSet.get?

/--
检查是否包含给定的键，如果包含则返回该键，否则返回 `fallback`。如果包含它们的键，则保证结果是等于集合中的键的指针。
-/
def c185 := @_root_.Std.ExtHashSet.getD

/--
将给定元素插入集合中。如果哈希集已包含与给定元素相等（关于 `==`）的元素，则哈希集将原样返回。

注意：这种非替换行为对于 `ExtHashSet` 和 `ExtHashSet.Raw` 来说是正确的。 `ExtHashMap`、`DExtHashMap`、`ExtHashMap.Raw` 和 `DExtHashMap.Raw` 上的 `insert` 函数的行为不同：它将覆盖现有映射。
-/
def c186 := @_root_.Std.ExtHashSet.insert

/--
通过迭代给定集合并调用 `insert`，将多个映射插入到哈希集中。如果同一个键出现多次，则第一次出现的键优先。

注意：此优先行为适用于 `ExtHashSet` 和 `ExtHashSet.Raw`。 `ExtHashMap`、`DExtHashMap`、`ExtHashMap.Raw` 和 `DExtHashMap.Raw` 上的 `insertMany` 函数的行为有所不同：它会更喜欢最后的外观。
-/
def c187 := @_root_.Std.ExtHashSet.insertMany

/--
删除该元素（如果存在）。
-/
def c188 := @_root_.Std.ExtHashSet.erase

/--
从哈希集中删除给定函数返回 `false` 的所有元素。
-/
def c189 := @_root_.Std.ExtHashSet.filter

/--
检查集合中是否存在某个元素，如果未找到则插入该元素。如果哈希集已包含与给定元素相等（关于 `==`）的元素，则哈希集将原样返回。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c190 := @_root_.Std.ExtHashSet.containsThenInsert

/--
从元素列表创建哈希集。请注意，与重复调用 `insert` 不同，如果集合包含多个相等的元素（对于 `==`），则集合中的最后一个元素将出现在返回的哈希集中。
-/
def c191 := @_root_.Std.ExtHashSet.ofList

/--
从元素数组创建哈希集。请注意，与重复调用 `insert` 不同，如果集合包含多个相等的元素（对于 `==`），则集合中的最后一个元素将出现在返回的哈希集中。
-/
def c192 := @_root_.Std.ExtHashSet.ofArray

/--
依值树映射。

树映射存储键到值的分配。它依赖于比较器函数，该函数定义键的排序并提供有效的依赖于顺序的查询，例如检索最小值或最大值。

为了确保操作按预期运行，比较器函数 `cmp` 应满足一些保证顺序一致的定律：

* 如果 `a` 小于（或等于）`b`，那么 `b` 大于（或等于）`a`，反之亦然（参见 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b`，且 `b` 小于或等于 `c`，那么 `a` 小于或等于 `c`（参见 `TransCmp` 类型类）。

`cmp a b = Ordering.eq` 的键被认为是相同的，即树映射中只能有一个键为 `a` 或 `b` 的条目。查找 `a` 或 `b` 始终会产生相同的条目（如果存在）。 _dependent_ 树映射的 `get` 操作还需要一个 `LawfulEqCmp` 实例，以确保 `cmp a b = .eq` 始终隐含 `a = b`，以便它们各自的值类型相等。

为了避免昂贵的复制，用户应确保线性使用树映射。

在内部，树映射表示为大小有界树，这是一种具有高效顺序统计查找的自平衡二叉搜索树。

为了在证明中使用，应该首选扩展依值树映射的类型 `Std.ExtDTreeMap`。该类型带有多个外延引理并提供相同的功能，但需要 `TransCmp` 实例才能使用。

这些树映射包含内置的良构不变量，这意味着它们不能在嵌套归纳类型中使用。对于这些用例，`Std.DTreeMap.Raw` 和 `Std.DTreeMap.Raw.WF` 将不变量与树映射分离。如有疑问，请优先选择 `DTreeMap` 而不是 `DTreeMap.Raw`。
-/
structure c193 (α : Type u) (β : α → Type v)
    (cmp : α → α → Ordering := by exact compare) where
  /-- 树映射的内部实现细节。 -/
  inner : Std.DTreeMap.Internal.Impl α β
  /-- 树映射的内部实现细节。 -/
  wf : @Std.DTreeMap.Internal.Impl.WF α ⟨cmp⟩ β inner

/--
创建一个新的空树映射。还可以并建议使用空集合符号 `∅` 和 `{}` 来创建空树映射。 `simp` 将 `empty` 替换为 `∅`。
-/
def c194 := @_root_.Std.DTreeMap.empty

/--
返回映射中存在的映射数量。
-/
def c195 := @_root_.Std.DTreeMap.size

/--
如果树映射不包含映射，则返回 `true`。
-/
def c196 := @_root_.Std.DTreeMap.isEmpty

/--
如果存在给定键 `a` 的映射或根据比较器 `cmp` 等于 `a` 的键，则返回 `true`。还有一个 `Prop` 值的版本：`a ∈ t` 相当于 `t.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 和 `contains` 使用 `==` 进行相等性检查，而对于树映射，两者都使用给定的比较器 `cmp`。
-/
def c197 := @_root_.Std.DTreeMap.contains

/--
给出给定键的映射存在的证明，检索给定键的映射。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c198 := @_root_.Std.DTreeMap.get

/--
尝试检索给定键的映射，如果不存在此类映射，则会触发 panic。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c199 := @_root_.Std.DTreeMap.get!

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `none`。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c200 := @_root_.Std.DTreeMap.get?

/--
尝试检索给定键的映射，如果不存在此类映射，则返回 `fallback`。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c201 := @_root_.Std.DTreeMap.getD

/--
从映射中检索与 `a` 匹配的键。通过要求 `a ∈ m` 的证明来确保此类映射的存在。结果保证是等于映射中的键的指针。
-/
def c202 := @_root_.Std.DTreeMap.getKey

/--
检查给定键的映射是否存在，如果存在则返回该键，否则会触发 panic。如果未触发 panic，结果保证是等于映射中的键的指针。
-/
def c203 := @_root_.Std.DTreeMap.getKey!

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `none`。 `some` 情况下的结果保证是等于映射中的键的指针。
-/
def c204 := @_root_.Std.DTreeMap.getKey?

/--
检查给定键的映射是否存在，如果存在则返回该键，否则返回 `fallback`。如果存在映射，则保证结果是等于映射中键的指针。
-/
def c205 := @_root_.Std.DTreeMap.getKeyD

/--
按升序返回树映射中存在的所有键的列表。
-/
def c206 := @_root_.Std.DTreeMap.keys

/--
返回树映射中按升序排列的所有键的数组。
-/
def c207 := @_root_.Std.DTreeMap.keysArray

/--
按升序返回树映射中存在的所有值的列表。
-/
def c208 := @_root_.Std.DTreeMap.values

/--
返回树映射中按升序排列的所有值的数组。
-/
def c209 := @_root_.Std.DTreeMap.valuesArray

/--
就地修改与给定键关联的值，允许通过 `Option` 值替换函数创建新值和删除值。

此函数可确保线性使用该值。
-/
def c210 := @_root_.Std.DTreeMap.alter

/--
就地修改与给定键关联的值。

此函数可确保线性使用该值。
-/
def c211 := @_root_.Std.DTreeMap.modify

/--
检查映射中是否存在某个键并无条件插入该键的值。

相当于（但可能比）调用 `contains` 后跟 `insert` 更快。
-/
def c212 := @_root_.Std.DTreeMap.containsThenInsert

/--
检查映射中是否存在某个键，如果未找到，则为该键插入一个值。如果返回的 `Bool` 是 `true`，则返回的映射不变。如果 `Bool` 是 `false`，则返回的映射已插入新值。

相当于（但可能比）调用 `contains` 后跟 `insertIfNew` 更快。
-/
def c213 := @_root_.Std.DTreeMap.containsThenInsertIfNew

/--
删除给定键的映射（如果存在）。
-/
def c214 := @_root_.Std.DTreeMap.erase

/--
删除给定函数返回 `false` 的映射的所有映射。
-/
def c215 := @_root_.Std.DTreeMap.filter

/--
通过将给定函数应用于所有映射来更新映射的值，仅保留函数返回 `some` 值的映射。
-/
def c216 := @_root_.Std.DTreeMap.filterMap

/--
将给定的映射插入到映射中。如果给定键已经存在映射，则键和值都将被替换。
-/
def c217 := @_root_.Std.DTreeMap.insert

/--
如果给定键没有映射，则将给定映射插入到映射中。否则，返回未更改的映射。
-/
def c218 := @_root_.Std.DTreeMap.insertIfNew

/--
检查映射中是否存在某个键，返回关联的值，如果未找到，则为该键插入一个值。

如果返回值为 `some v`，则返回的映射不变。如果是 `none`，则返回的映射已插入新值。

相当于（但可能比）调用 `get?` 后跟 `insertIfNew` 更快。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c219 := @_root_.Std.DTreeMap.getThenInsertIfNew?

/--
通过迭代给定集合并调用 `insert` 将多个映射插入到树映射中。如果同一键出现多次，则最后一次出现的键优先。

注意：此优先行为适用于 `TreeMap`、`DTreeMap`、`TreeMap.Raw` 和 `DTreeMap.Raw`。 `TreeSet` 和 `TreeSet.Raw` 上的 `insertMany` 函数的行为不同：它会更喜欢第一次出现。
-/
def c220 := @_root_.Std.DTreeMap.insertMany

/--
根据谓词将树映射划分为两个树映射。
-/
def c221 := @_root_.Std.DTreeMap.partition

/--
返回对依值树映射的条目的有限迭代器。迭代器按顺序生成映射的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c222 := @_root_.Std.DTreeMap.iter

/--
返回依值树映射的键上的有限迭代器。迭代器按顺序生成键，然后终止。

键和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c223 := @_root_.Std.DTreeMap.keysIter

/--
返回树映射值的有限迭代器。迭代器按顺序产生值，然后终止。

键和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终存在
* `Productive` 实例：始终存在
-/
def c224 := @_root_.Std.DTreeMap.valuesIter

/--
通过将给定函数应用于所有映射来更新映射的值。
-/
def c225 := @_root_.Std.DTreeMap.map

/--
按升序将给定函数折叠到映射中的映射上。
-/
def c226 := @_root_.Std.DTreeMap.foldl

/--
按升序将给定的单子函数折叠到映射中的映射上。
-/
def c227 := @_root_.Std.DTreeMap.foldlM

/--
支持 `do` 块中的 `for` 循环构造。迭代按升序进行。
-/
def c228 := @_root_.Std.DTreeMap.forIn

/--
按升序对树映射中的每个映射执行单子操作。
-/
def c229 := @_root_.Std.DTreeMap.forM

/--
将映射列表转换为树映射。
-/
def c230 := @_root_.Std.DTreeMap.ofList

/--
将树映射转换为按升序排列的映射列表。
-/
def c231 := @_root_.Std.DTreeMap.toArray

/--
将树映射转换为按升序排列的映射列表。
-/
def c232 := @_root_.Std.DTreeMap.toList

/--
没有内置的良构不变量的依值树映射，适合在嵌套归纳类型中使用。良构的不变量称为 `Raw.WF`。如有疑问，请优先选择 `DTreeMap` 而不是 `DTreeMap.Raw`。关于 `Std.DTreeMap.Raw` 操作的引理可在模块 `Std.Data.DTreeMap.Raw.Lemmas` 中找到。

树映射存储键到值的分配。它依赖于比较器函数，该函数定义键的排序并提供有效的依赖于顺序的查询，例如检索最小值或最大值。

为了确保操作按预期运行，比较器函数 `cmp` 应满足一些保证顺序一致的定律：

* 如果 `a` 小于（或等于）`b`，那么 `b` 大于（或等于）`a`，反之亦然（参见 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b`，且 `b` 小于或等于 `c`，那么 `a` 小于或等于 `c`（参见 `TransCmp` 类型类）。

`cmp a b = Ordering.eq` 的键被认为是相同的，即树映射中只能有一个键为 `a` 或 `b` 的条目。查找 `a` 或 `b` 始终会产生相同的条目（如果存在）。 _dependent_ 树映射的 `get` 操作还需要一个 `LawfulEqCmp` 实例，以确保 `cmp a b = .eq` 始终隐含 `a = b`，以便它们各自的值类型相等。

为了避免昂贵的复制，用户应确保线性使用树映射。

在内部，树映射表示为大小有界树，这是一种具有高效顺序统计查找的自平衡二叉搜索树。
-/
structure c233 (α : Type u) (β : α → Type v)
    (_cmp : α → α → Ordering := by exact compare) where
  /-- 树映射的内部实现细节。 -/
  inner : Std.DTreeMap.Internal.Impl α β

/--
树映射的良构谓词。 `DTreeMap` 的用户不需要与之交互。 `DTreeMap.Raw` 的用户需要向引理提供 `WF` 的证明，并且应该使用像 `WF.empty` 和 `WF.insert` 这样的引理（它们的命名总是与它们所涉及的操作完全相同）来表明映射操作保持良构。该类型的构造函数是内部实现细节，用户不应访问。
-/
structure c234 {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}
    (t : Std.DTreeMap.Raw α β cmp) : Prop where
  /-- 树映射的内部实现细节。 -/
  out : @Std.DTreeMap.Internal.Impl.WF α ⟨cmp⟩ β t.inner

end Manual.ZhDocString.Ch19Ch20.G1
