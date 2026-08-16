/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lean
import Manual.ZhDocString.ZhDocString
import Std.Data.TreeMap
import Std.Data.TreeMap.Raw

namespace Manual.ZhDocString.Ch19Ch20.G6

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w

/-!
本模块为第 19–20 章的树映射、字节数组、定宽整数算术与列表比较 API 提供中文动态文档载体。
普通定义直接别名到真实声明；结构体逐字段镜像真实声明，以便动态文档渲染器核对形状。
-/

/--
树映射。

树映射存储键到值的对应关系。它依赖一个比较器函数来定义键的顺序，并提供高效的顺序相关查询，例如检索最小值或最大值。

为确保各项操作符合预期，比较器函数 `cmp` 应满足若干保证顺序一致的定律：

* 如果 `a` 小于（或等于）`b`，那么 `b` 大于（或等于）`a`，反之亦然（参见 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b`，而 `b` 又小于或等于 `c`，那么 `a` 小于或等于 `c`（参见 `TransCmp` 类型类）。

满足 `cmp a b = Ordering.eq` 的键被视为相同；也就是说，树映射中只能有一个键为 `a` 或 `b` 的条目。查找 `a` 或 `b` 总会得到同一个条目（如果存在）。

为避免高昂的复制开销，用户应确保以线性方式使用树映射。

树映射在内部表示为带大小界限的树，这是一类支持高效顺序统计查询的自平衡二叉搜索树。

在证明中，最好使用外延树映射类型 `Std.ExtTreeMap`。该类型带有多个外延性引理并提供相同的函数，但需要 `TransCmp` 实例才能使用。

这些树映射内置了良构性不变量，因此不能用于嵌套归纳类型。在这种场景中，`Std.TreeMap.Raw` 和 `Std.TreeMap.Raw.WF` 将该不变量与树映射分离。若不确定，请优先使用 `TreeMap` 而非 `TreeMap.Raw`。
-/
structure c001 (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- 内部树映射实现细节。 -/
  inner : Std.DTreeMap α (fun _ => β) cmp

/--
创建一个新的空树映射。也可以并且推荐使用空集合记法 `∅` 和 `{}` 来创建空树映射。`simp` 会将 `empty` 替换为 `∅`。
-/
def c002 := @Std.TreeMap.empty

/--
返回映射中现有对应关系的数量。
-/
def c003 := @Std.TreeMap.size

/--
如果树映射不含任何对应关系，则返回 `true`。
-/
def c004 := @Std.TreeMap.isEmpty

/--
如果树映射不含任何对应关系，则返回 `true`；这里的对应关系可以属于给定键 `a`，也可以属于依比较器判断为与 `a` 相等的键。比较器为 `cmp`。它还有一个取值为 `Prop` 的版本：`a ∈ t` 等价于 `t.contains a = true`。

请注意，这与列表的行为不同：对于列表，`∈` 使用 `=` 检查相等性，而 `contains` 使用 `==`；对于树映射，两者都使用给定的比较器 `cmp`。
-/
def c005 := @Std.TreeMap.contains

/--
给定“给定键的对应关系存在”的证明，检索该键对应的值。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c006 := @Std.TreeMap.get

/--
尝试检索给定键对应的值；如果不存在这样的对应关系，则触发 panic。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c007 := @Std.TreeMap.get!

/--
尝试检索给定键对应的值；如果不存在这样的对应关系，则返回 `none`。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c008 := @Std.TreeMap.get?

/--
尝试检索给定键对应的值；如果不存在这样的对应关系，则返回 `fallback`。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c009 := @Std.TreeMap.getD

/--
从与 `a` 匹配的对应关系中检索键。它要求提供 `a ∈ m` 的证明，以保证这样的对应关系存在。结果保证与映射中的键指针相等。
-/
def c010 := @Std.TreeMap.getKey

/--
检查给定键的对应关系是否存在；若存在则返回该键，否则触发 panic。如果未触发 panic，则结果保证与映射中的键指针相等。
-/
def c011 := @Std.TreeMap.getKey!

/--
检查给定键的对应关系是否存在；若存在则返回该键，否则返回 `none`。在结果为 `some` 时，其中的键保证与映射中的键指针相等。
-/
def c012 := @Std.TreeMap.getKey?

/--
检查给定键的对应关系是否存在；若存在则返回该键，否则返回 `fallback`。如果对应关系存在，则结果保证与映射中的键指针相等。
-/
def c013 := @Std.TreeMap.getKeyD

/--
按升序返回树映射中所有键的列表。
-/
def c014 := @Std.TreeMap.keys

/--
按升序返回树映射中所有键的数组。
-/
def c015 := @Std.TreeMap.keysArray

/--
按键的升序返回树映射中所有值的列表。
-/
def c016 := @Std.TreeMap.values

/--
按键的升序返回树映射中所有值的数组。
-/
def c017 := @Std.TreeMap.valuesArray

/--
返回键为第 `n` 小的键值对。
-/
def c018 := @Std.TreeMap.entryAtIdx

/--
返回键为第 `n` 小的键值对；如果 `n` 不小于 `t.size`，则触发 panic。
-/
def c019 := @Std.TreeMap.entryAtIdx!

/--
返回键为第 `n` 小的键值对；若无此结果则返回 `none`，具体而言，是在 `n` 不小于 `t.size` 时。
-/
def c020 := @Std.TreeMap.entryAtIdx?

/--
返回键为第 `n` 小的键值对；若无此结果则返回 `fallback`，具体而言，是在 `n` 不小于 `t.size` 时。
-/
def c021 := @Std.TreeMap.entryAtIdxD

/--
给定“存在这样的对应关系”的证明，检索最小且大于或等于给定键的键值对。
-/
def c022 := @Std.TreeMap.getEntryGE

/--
尝试检索最小且大于或等于给定键的键值对；如果不存在，则触发 panic。
-/
def c023 := @Std.TreeMap.getEntryGE!

/--
尝试检索最小且大于或等于给定键的键值对；如果不存在，则返回 `none`。
-/
def c024 := @Std.TreeMap.getEntryGE?

/--
尝试检索最小且大于或等于给定键的键值对；如果不存在，则返回 `fallback`。
-/
def c025 := @Std.TreeMap.getEntryGED

/--
给定“存在这样的对应关系”的证明，检索最小且大于给定键的键值对。
-/
def c026 := @Std.TreeMap.getEntryGT

/--
尝试检索最小且大于给定键的键值对；如果不存在，则触发 panic。
-/
def c027 := @Std.TreeMap.getEntryGT!

/--
尝试检索最小且大于给定键的键值对；如果不存在，则返回 `none`。
-/
def c028 := @Std.TreeMap.getEntryGT?

/--
尝试检索最小且大于给定键的键值对；如果不存在，则返回 `fallback`。
-/
def c029 := @Std.TreeMap.getEntryGTD

/--
给定“存在这样的对应关系”的证明，检索最大且小于或等于给定键的键值对。
-/
def c030 := @Std.TreeMap.getEntryLE

/--
尝试检索最大且小于或等于给定键的键值对；如果不存在，则触发 panic。
-/
def c031 := @Std.TreeMap.getEntryLE!

/--
尝试检索最大且小于或等于给定键的键值对；如果不存在，则返回 `none`。
-/
def c032 := @Std.TreeMap.getEntryLE?

/--
尝试检索最大且小于或等于给定键的键值对；如果不存在，则返回 `fallback`。
-/
def c033 := @Std.TreeMap.getEntryLED

/--
给定“存在这样的对应关系”的证明，检索最大且小于给定键的键值对。
-/
def c034 := @Std.TreeMap.getEntryLT

/--
尝试检索最大且小于给定键的键值对；如果不存在，则触发 panic。
-/
def c035 := @Std.TreeMap.getEntryLT!

/--
尝试检索最大且小于给定键的键值对；如果不存在，则返回 `none`。
-/
def c036 := @Std.TreeMap.getEntryLT?

/--
尝试检索最大且小于给定键的键值对；如果不存在，则返回 `fallback`。
-/
def c037 := @Std.TreeMap.getEntryLTD

/--
给定“存在这样的对应关系”的证明，检索最小且大于或等于给定键的键。
-/
def c038 := @Std.TreeMap.getKeyGE

/--
尝试检索最小且大于或等于给定键的键；如果不存在，则触发 panic。
-/
def c039 := @Std.TreeMap.getKeyGE!

/--
尝试检索最小且大于或等于给定键的键；如果不存在，则返回 `none`。
-/
def c040 := @Std.TreeMap.getKeyGE?

/--
尝试检索最小且大于或等于给定键的键；如果不存在，则返回 `fallback`。
-/
def c041 := @Std.TreeMap.getKeyGED

/--
给定“存在这样的对应关系”的证明，检索最小且大于给定键的键。
-/
def c042 := @Std.TreeMap.getKeyGT

/--
尝试检索最小且大于给定键的键；如果不存在，则触发 panic。
-/
def c043 := @Std.TreeMap.getKeyGT!

/--
尝试检索最小且大于给定键的键；如果不存在，则返回 `none`。
-/
def c044 := @Std.TreeMap.getKeyGT?

/--
尝试检索最小且大于给定键的键；如果不存在，则返回 `fallback`。
-/
def c045 := @Std.TreeMap.getKeyGTD

/--
给定“存在这样的对应关系”的证明，检索最大且小于或等于给定键的键。
-/
def c046 := @Std.TreeMap.getKeyLE

/--
尝试检索最大且小于或等于给定键的键；如果不存在，则触发 panic。
-/
def c047 := @Std.TreeMap.getKeyLE!

/--
尝试检索最大且小于或等于给定键的键；如果不存在，则返回 `none`。
-/
def c048 := @Std.TreeMap.getKeyLE?

/--
尝试检索最大且小于或等于给定键的键；如果不存在，则返回 `fallback`。
-/
def c049 := @Std.TreeMap.getKeyLED

/--
给定“存在这样的对应关系”的证明，检索最大且小于给定键的键。
-/
def c050 := @Std.TreeMap.getKeyLT

/--
尝试检索最大且小于给定键的键；如果不存在，则触发 panic。
-/
def c051 := @Std.TreeMap.getKeyLT!

/--
尝试检索最大且小于给定键的键；如果不存在，则返回 `none`。
-/
def c052 := @Std.TreeMap.getKeyLT?

/--
尝试检索最大且小于给定键的键；如果不存在，则返回 `fallback`。
-/
def c053 := @Std.TreeMap.getKeyLTD

/--
返回第 `n` 小的键。
-/
def c054 := @Std.TreeMap.keyAtIdx

/--
返回第 `n` 小的键；如果 `n` 不小于 `t.size`，则触发 panic。
-/
def c055 := @Std.TreeMap.keyAtIdx!

/--
返回第 `n` 小的键；若无此结果则返回 `none`，具体而言，是在 `n` 不小于 `t.size` 时。
-/
def c056 := @Std.TreeMap.keyAtIdx?

/--
返回第 `n` 小的键；若无此结果则返回 `fallback`，具体而言，是在 `n` 不小于 `t.size` 时。
-/
def c057 := @Std.TreeMap.keyAtIdxD

/--
给定树映射非空的证明，检索键最小的键值对。
-/
def c058 := @Std.TreeMap.minEntry

/--
尝试检索树映射中键最小的键值对；如果映射为空，则触发 panic。
-/
def c059 := @Std.TreeMap.minEntry!

/--
尝试检索树映射中键最小的键值对；如果映射为空，则返回 `none`。
-/
def c060 := @Std.TreeMap.minEntry?

/--
尝试检索树映射中键最小的键值对；如果映射为空，则返回 `fallback`。
-/
def c061 := @Std.TreeMap.minEntryD

/--
给定树映射非空的证明，检索最小的键。
-/
def c062 := @Std.TreeMap.minKey

/--
尝试检索树映射中最小的键；如果映射为空，则触发 panic。
-/
def c063 := @Std.TreeMap.minKey!

/--
尝试检索树映射中最小的键；如果映射为空，则返回 `none`。
-/
def c064 := @Std.TreeMap.minKey?

/--
尝试检索树映射中最小的键；如果映射为空，则返回 `fallback`。
-/
def c065 := @Std.TreeMap.minKeyD

/--
给定树映射非空的证明，检索键最大的键值对。
-/
def c066 := @Std.TreeMap.maxEntry

/--
尝试检索树映射中键最大的键值对；如果映射为空，则触发 panic。
-/
def c067 := @Std.TreeMap.maxEntry!

/--
尝试检索树映射中键最大的键值对；如果映射为空，则返回 `none`。
-/
def c068 := @Std.TreeMap.maxEntry?

/--
尝试检索树映射中键最大的键值对；如果映射为空，则返回 `fallback`。
-/
def c069 := @Std.TreeMap.maxEntryD

/--
给定树映射非空的证明，检索最大的键。
-/
def c070 := @Std.TreeMap.maxKey

/--
尝试检索树映射中最大的键；如果映射为空，则触发 panic。
-/
def c071 := @Std.TreeMap.maxKey!

/--
尝试检索树映射中最大的键；如果映射为空，则返回 `none`。
-/
def c072 := @Std.TreeMap.maxKey?

/--
尝试检索树映射中最大的键；如果映射为空，则返回 `fallback`。
-/
def c073 := @Std.TreeMap.maxKeyD

/--
原地修改与给定键关联的值，并允许通过一个返回 `Option` 的替换函数创建或删除值。

此函数确保以线性方式使用该值。
-/
def c074 := @Std.TreeMap.alter

/--
原地修改与给定键关联的值。

此函数确保以线性方式使用该值。
-/
def c075 := @Std.TreeMap.modify

/--
检查映射中是否存在某个键，并无条件插入该键对应的值。

等价于（但可能快于）依次调用 `contains` 和 `insert`。
-/
def c076 := @Std.TreeMap.containsThenInsert

/--
检查映射中是否存在某个键；如果未找到，则插入该键对应的值。如果返回的 `Bool` 为 `true`，返回的映射不变。如果 `Bool` 为 `false`，则返回的映射中已插入新值。

等价于（但可能快于）依次调用 `contains` 和 `insertIfNew`。
-/
def c077 := @Std.TreeMap.containsThenInsertIfNew

/--
如果给定键的对应关系存在，则将其移除。
-/
def c078 := @Std.TreeMap.erase

/--
迭代给定集合并调用 `erase`，从树映射中删除多个对应关系。
-/
def c079 := @Std.TreeMap.eraseMany

/--
移除映射中所有使给定函数返回 `false` 的对应关系。
-/
def c080 := @Std.TreeMap.filter

/--
将给定函数应用于所有对应关系以更新映射中的值，仅保留函数返回 `some` 值的对应关系。
-/
def c081 := @Std.TreeMap.filterMap

/--
将给定的对应关系插入映射。如果给定键已有对应关系，则键和值都会被替换。
-/
def c082 := @Std.TreeMap.insert

/--
如果给定键没有对应关系，则将给定的对应关系插入映射；否则原样返回映射。
-/
def c083 := @Std.TreeMap.insertIfNew

/--
检查映射中是否存在某个键并返回关联的值；如果未找到，则插入该键对应的值。

如果返回值为 `some v`，则返回的映射不变。如果返回值为 `none`，则返回的映射中已插入新值。

等价于（但可能快于）依次调用 `get?` 和 `insertIfNew`。

使用 `LawfulEqCmp` 实例将检索到的值转换为正确的类型。
-/
def c084 := @Std.TreeMap.getThenInsertIfNew?

/--
迭代给定集合并调用 `insert`，将多个对应关系插入树映射。如果同一个键出现多次，则以最后一次出现为准。

注意：`TreeMap`、`DTreeMap`、`TreeMap.Raw` 和 `DTreeMap.Raw` 都采用这种优先规则。`insertMany` 函数在 `TreeSet` 和 `TreeSet.Raw` 上的行为不同：它优先保留第一次出现的元素。
-/
def c085 := @Std.TreeMap.insertMany

/--
迭代给定集合并调用 `insertIfNew`，将多个元素插入树映射。如果同一个键出现多次，则以第一次出现为准。
-/
def c086 := @Std.TreeMap.insertManyIfNewUnit

/--
返回包含 `t₁` 和 `t₂` 中所有对应关系的映射。如果两个映射含有同一个键 `k`（按 `cmp` 判断），则使用给定函数，根据 `t₁` 和 `t₂` 中各自的值确定新值。

此函数确保以线性方式使用 `t₁`。如果合并函数也以线性方式使用 `t₁` 中各个值，即以线性方式使用第二个参数（第一个类型为 `β a` 的参数），则这些值同样只被线性使用。因此，只要 `t₁` 未被共享，其性能特征可用以下命令式过程描述：迭代 `t₂` 中的所有对应关系；若 `t₁` 尚不包含冲突的对应关系，就将其插入 `t₁`；若 `t₁` 已含冲突的对应关系，则使用给定的合并函数，将 `t₂` 中的对应关系合并到 `t₁` 的对应关系中。最后返回 `t₁`。

因此，此方法的运行时间关于 `t₁` 的大小呈对数增长，关于 `t₂` 的大小呈线性增长，只要 `t₁` 未被共享。
-/
def c087 := @Std.TreeMap.mergeWith

/--
依据谓词将一个树映射分割为两个树映射。
-/
def c088 := @Std.TreeMap.partition

/--
返回遍历树映射条目的有限迭代器。迭代器按顺序产出映射中的元素，然后终止。

**终止性质：**

* `Finite` 实例：始终成立
* `Productive` 实例：始终成立
-/
def c089 := @Std.TreeMap.iter

/--
返回遍历树映射键的有限迭代器。迭代器按顺序产出键，然后终止。

键类型和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终成立
* `Productive` 实例：始终成立
-/
def c090 := @Std.TreeMap.keysIter

/--
返回遍历树映射值的有限迭代器。迭代器按顺序产出值，然后终止。

键类型和值类型必须位于同一个宇宙中。

**终止性质：**

* `Finite` 实例：始终成立
* `Productive` 实例：始终成立
-/
def c091 := @Std.TreeMap.valuesIter

/--
将给定函数应用于所有对应关系，以更新映射中的值。
-/
def c092 := @Std.TreeMap.map

/--
检查是否所有元素都满足谓词；一旦谓词不成立便短路。
-/
def c093 := @Std.TreeMap.all

/--
检查是否有任一元素满足谓词；一旦谓词不成立便短路。
-/
def c094 := @Std.TreeMap.any

/--
按升序用给定函数折叠映射中的对应关系。
-/
def c095 := @Std.TreeMap.foldl

/--
按升序用给定的单子函数折叠映射中的对应关系。
-/
def c096 := @Std.TreeMap.foldlM

/--
按降序用给定函数折叠映射中的对应关系。
-/
def c097 := @Std.TreeMap.foldr

/--
按降序用给定的单子函数折叠映射中的对应关系。
-/
def c098 := @Std.TreeMap.foldrM

/--
为 `for` 循环构造在 `do` 块中使用提供支持。迭代按升序进行。
-/
def c099 := @Std.TreeMap.forIn

/--
按升序对树映射中的每个对应关系执行单子动作。
-/
def c100 := @Std.TreeMap.forM

/--
将对应关系列表转换为树映射。
-/
def c101 := @Std.TreeMap.ofList

/--
按升序将树映射转换为对应关系列表。
-/
def c102 := @Std.TreeMap.toList

/--
将对应关系列表转换为树映射。
-/
def c103 := @Std.TreeMap.ofArray

/--
按升序将树映射转换为对应关系列表。
-/
def c104 := @Std.TreeMap.toArray

/--
将键数组转换为树映射。
-/
def c105 := @Std.TreeMap.unitOfArray

/--
将键列表转换为树映射。
-/
def c106 := @Std.TreeMap.unitOfList

/--
不内置良构性不变量的树映射，适用于嵌套归纳类型。其良构性不变量称为 `Raw.WF`。若不确定，请优先使用 `TreeMap` 而非 `TreeMap.Raw`。关于 `Std.TreeMap.Raw` 各项操作的引理可在模块 `Std.Data.TreeMap.Raw.Lemmas` 中找到。

树映射存储键到值的对应关系。它依赖一个比较器函数来定义键的顺序，并提供高效的顺序相关查询，例如检索最小值或最大值。

为确保各项操作符合预期，比较器函数 `cmp` 应满足若干保证顺序一致的定律：

* 如果 `a` 小于（或等于）`b`，那么 `b` 大于（或等于）`a`，反之亦然（参见 `OrientedCmp` 类型类）。
* 如果 `a` 小于或等于 `b`，而 `b` 又小于或等于 `c`，那么 `a` 小于或等于 `c`（参见 `TransCmp` 类型类）。

满足 `cmp a b = Ordering.eq` 的键被视为相同；也就是说，树映射中只能有一个键为 `a` 或 `b` 的条目。查找 `a` 或 `b` 总会得到同一个条目（如果存在）。

为避免高昂的复制开销，用户应确保以线性方式使用树映射。

树映射在内部表示为带大小界限的树，这是一类支持高效顺序统计查询的自平衡二叉搜索树。
-/
structure c107 (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- 内部树映射实现细节。 -/
  inner : Std.DTreeMap.Raw α (fun _ => β) cmp

/--
树映射的良构性谓词。`TreeMap` 用户无需直接使用它。`TreeMap.Raw` 用户需要为各引理提供 `WF` 证明，并应使用 `WF.empty`、`WF.insert` 等引理（它们的名称总是与相应操作完全相同）来证明映射操作保持良构性。此类型的构造子属于内部实现细节，用户不应访问。
-/
structure c108 {α : Type u} {β : Type v} {cmp : α → α → Ordering}
    (t : Std.TreeMap.Raw α β cmp) : Prop where
  /-- 内部树映射实现细节。 -/
  out : t.inner.WF

/--
`ByteArray` 类似于 `Array UInt8`，但具有高效的运行时表示，即紧凑存储的字节缓冲区。
-/
structure c109 where
  /--
字节数组中包含的数据。

在 `Array` 与 `ByteArray` 之间转换需要线性时间。
-/
  data : Array UInt8

/--
将字节数组打包为 `ByteArray`。

在 `Array` 与 `ByteArray` 之间转换需要线性时间。
-/
add_decl_doc c109.mk

/--
构造初始容量为 `0` 的新空字节数组。

使用 `ByteArray.emptyWithCapacity` 可创建初始容量更大的数组。
-/
def c110 := @ByteArray.empty

/--
构造初始容量为 `c` 的新空字节数组。
-/
def c111 := @ByteArray.emptyWithCapacity

/--
拼接两个字节数组。

在编译后的代码中，对 `ByteArray.append` 的调用会被替换为效率高得多的 `ByteArray.fastAppend`。
-/
def c112 := @ByteArray.append

/--
使用快速数组原语拼接两个字节数组，而不是先转换为列表再转回数组。

在编译后的代码中，此函数会替换对 `ByteArray.append` 的调用。
-/
def c113 := @ByteArray.fastAppend

/--
将位于 `[srcOff, srcOff + len)` 的切片从 `src` 复制到 `[destOff, destOff + len)` 在 `dest` 中对应的位置；必要时扩展 `dest`。如果 `exact` 为 `false`，扩展时容量会加倍。
-/
def c114 := @ByteArray.copySlice

/--
返回字节数组中的字节数。

这是数组中实际包含的字节数，不同于容量；容量是当前为数组分配的内存量。
-/
def c115 := @ByteArray.size

/--
以平台相关的定宽整数形式获取数组大小。

由于 `USize` 足以寻址 Lean 所支持的每个平台上的全部内存，实际不会有元素数量超出 `ByteArray` 所用 `USize` 计数范围的实例。
-/
def c116 := @ByteArray.usize

/--
如果结果为 `true`，则 `s` 包含零个字节。
-/
def c117 := @ByteArray.isEmpty

/--
获取指定索引处的字节。调用者必须证明索引未越界。

可使用 `uget` 作为更高效的替代方案；也可使用 `get!`，它在索引越界时触发 panic。
-/
def c118 := @ByteArray.get

/--
获取指定索引处的字节。调用者必须证明索引未越界。索引用平台相关的定宽整数表示（32 位或 64 位）。

由于 `USize` 足以寻址 Lean 所支持的每个平台上的全部内存，实际不会存在其所有元素无法由某个 `ByteArray` 的 `uget` 获取的情况。
-/
def c119 := @ByteArray.uget

/--
获取指定索引处的字节。如果索引越界，则触发 panic。
-/
def c120 := @ByteArray.get!

/--
将索引从 `b`（含）到 `e`（不含）的字节复制到新的 `ByteArray`。
-/
def c121 := @ByteArray.extract

/--
将紧凑存储的字节数组转换为链表。
-/
def c122 := @ByteArray.toList

/--
将大小为 8 的 `ByteArray` 解释为大端序 `UInt64`。

如果数组大小不是 8，则触发 panic。
-/
def c123 := @ByteArray.toUInt64BE!

/--
将大小为 8 的 `ByteArray` 解释为小端序 `UInt64`。

如果数组大小不是 8，则触发 panic。
-/
def c124 := @ByteArray.toUInt64LE!

/--
从 UTF-8 表示中解码字符序列。如果这些字节不构成 Unicode 标量值序列，则返回 `none`。
-/
def c125 := @ByteArray.utf8Decode?

/--
解码并返回 `Char`，其 UTF-8 编码从 `i` 开始，位于 `bytes` 中。

如果结果为 `none`，则 `i` 不是某个字符的有效 UTF-8 编码起点。
-/
def c126 := @ByteArray.utf8DecodeChar?

/--
解码并返回 `Char`，其 UTF-8 编码从 `i` 开始，位于 `bytes` 中。

此函数要求证明存在有效的 `Char`，且它确实位于 `i`。`utf8DecodeChar?` 是另一种选择：它返回 `Option Char`，而不要求预先提供证明。
-/
def c127 := @ByteArray.utf8DecodeChar

/--
在数组末尾添加一个元素。所得数组的大小比输入数组大一。如果该数组没有其他引用，则会原地修改。

此操作的摊还时间复杂度为 `O(1)`，因为 `ByteArray` 以动态数组表示。
-/
def c128 := @ByteArray.push

/--
替换给定索引处的字节。

此函数不执行边界检查，但要求提供索引未越界的证明。通常可以省略该证明，系统会自动合成。

如果数组没有其他引用，则会原地修改。
-/
def c129 := @ByteArray.set

/--
替换给定索引处的字节。

此函数不执行边界检查，但要求提供索引未越界的证明。通常可以省略该证明，系统会自动合成。

如果数组没有其他引用，则会原地修改。
-/
def c130 := @ByteArray.uset

/--
替换给定索引处的字节。

如果数组没有其他引用，则会原地修改。

如果索引越界，则原样返回数组。
-/
def c131 := @ByteArray.set!

/--
对 `ByteArray` 执行左折叠：按索引从小到大遍历数组，并计算一个累积值。

数组的每个元素都通过函数 `f` 与此前元素得到的值合并。初始值 `init` 是处理任何元素之前的起始值。

`ByteArray.foldlM` 是此函数的单子版本。
-/
def c132 := @ByteArray.foldl

/--
对 `ByteArray` 执行单子左折叠：按索引从小到大遍历数组，并计算一个累积值。

数组的每个元素都通过单子函数 `f` 与此前元素得到的值合并。初始值 `init` 是处理任何元素之前的起始值。
-/
def c133 := @ByteArray.foldlM

/--
这是 `ForIn.forIn` 针对 `ByteArray` 的参考实现。

在编译后的代码中，它会被更高效的 `ByteArray.forInUnsafe` 替换。
-/
def c134 := @ByteArray.forIn

/--
创建位于数组开头的迭代器。
-/
def c135 := @ByteArray.iter

/--
遍历字节（`UInt8`）的迭代器，其对象是一个 `ByteArray`。

通常通过 `arr.iter` 创建，其中 `arr` 是一个 `ByteArray`。

如果位置 `i` 对数组 `arr` 有效，即 `0 ≤ i ≤ arr.size`，则称迭代器*有效*。

如果迭代器无效，大多数迭代器操作都会返回任意值。`ByteArray.Iterator` API 中的函数应当排除无效迭代器的产生，但有两个例外：

- `Iterator.next iter` 会无效，如果 `iter` 已位于数组末尾，即 `iter.atEnd` 为 `true`
- `Iterator.forward iter n`/`Iterator.nextn iter n` 会无效，如果 `n` 严格大于剩余字节数
-/
structure c136 where
  /-- 迭代器所针对的数组。 -/
  array : ByteArray
  /--
当前位置。

此位置对数组而言不一定有效，例如在 `Iterator.atEnd` 为真时仍持续调用 `Iterator.next`。若位置无效，则当前字节为 `(default : UInt8)`。
-/
  idx : Nat

/--
当前位置。

此位置对数组而言不一定有效，例如持续调用 `Iterator.next`，即使 `Iterator.atEnd` 已为真。若位置无效，则当前字节为 `(default : UInt8)`。
-/
def c137 := @ByteArray.Iterator.pos

/--
如果迭代器已经越过数组的最后一个字节，则为真。
-/
def c138 := @ByteArray.Iterator.atEnd

/--
如果迭代器有效，即尚未越过数组的最后一个字节，则为真。
-/
def c139 := @ByteArray.Iterator.hasNext

/--
如果位置不为零，则为真。
-/
def c140 := @ByteArray.Iterator.hasPrev

/--
当前位置的字节。

位置无效时返回 `(default : UInt8)`。
-/
def c141 := @ByteArray.Iterator.curr

/--
当前位置的字节。-
-/
def c142 := @ByteArray.Iterator.curr'

/--
无条件将迭代器的位置向前移动一个字节。

只有当迭代器不在数组末尾时，调用此函数才有效，**即** `Iterator.atEnd` 为 `false`；否则所得迭代器将无效。
-/
def c143 := @ByteArray.Iterator.next

/--
将迭代器的位置向前移动一个字节。-
-/
def c144 := @ByteArray.Iterator.next'

/--
将迭代器的位置向前移动若干字节。

仅当要跳过的字节数小于或等于迭代器中的剩余字节数时，所得迭代器才有效。
-/
def c145 := @ByteArray.Iterator.forward

/--
将迭代器的位置向前移动若干字节。

仅当要跳过的字节数小于或等于迭代器中的剩余字节数时，所得迭代器才有效。
-/
def c146 := @ByteArray.Iterator.nextn

/--
减小迭代器的位置。

如果位置为零，则此函数不改变迭代器。
-/
def c147 := @ByteArray.Iterator.prev

/--
将迭代器的位置向后移动若干字节。

如果要求后退的字节数多于可用字节数，则停在数组开头。
-/
def c148 := @ByteArray.Iterator.prevn

/--
迭代器中剩余的字节数。
-/
def c149 := @ByteArray.Iterator.remainingBytes

/--
将迭代器的位置移至数组末尾。

给定 `i : ByteArray.Iterator`，请注意 `i.toEnd.atEnd` 始终为 `true`。
-/
def c150 := @ByteArray.Iterator.toEnd

/--
返回字节数组中具有给定边界的字节切片。

如果 `start` 或 `stop` 不是字节切片的有效边界，则将其限制在字节数组大小以内。此外，起始索引会被限制为不超过结束索引。
-/
def c151 := @ByteArray.toByteSlice

/--
某个底层字节数组的一段区域。

字节切片包含一个字节数组，以及感兴趣区域的起始和结束索引。字节切片既能避免复制或分配空间，又比手动追踪边界更方便。感兴趣区域由所有大于或等于 `start` 且严格小于 `stop` 的索引组成。
-/
def c152 := @ByteSlice

/--
比较函数
-/
def c153 := @ByteSlice.beq

/--
底层字节数组。
-/
def c154 := @ByteSlice.byteArray

/--
检查字节切片是否包含指定的字节值。

如果切片中任一字节等于给定值，则返回 `true`，否则返回 `false`。
-/
def c155 := @ByteSlice.contains

/--
空字节切片。

此空字节切片以空字节数组为底层存储。
-/
def c156 := @ByteSlice.empty

/--
从右向左对字节切片中的字节执行折叠操作。

构造类型为 `β` 的累加器：从 `init` 开始，从末尾移向开头，依次将字节切片中的每个字节与当前累加器值合并。

示例：
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.foldr (·.toNat + ·) 0 = 6`
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.popFront.foldr (·.toNat + ·) 0 = 5`
-/
def c157 := @ByteSlice.foldr

/--
从右向左对字节切片中的字节执行单子折叠操作。

构造类型为 `β` 的累加器：从 `init` 开始，从末尾移向开头，依次以单子方式将字节切片中的每个字节与当前累加器值合并。所用单子可以允许提前终止或重复。

示例：
```lean example
#eval (ByteArray.mk #[1, 2, 3]).toByteSlice.foldrM (init := 0) fun x acc =>
  some x.toNat + acc
```
```output
some 6
```
-/
def c158 := @ByteSlice.foldrM

/--
对字节切片中的每个字节执行单子动作。

从最小索引开始，按索引递增的顺序处理字节。
-/
def c159 := @ByteSlice.forM

/--
从字节切片中取出一个字节。

索引相对于字节切片的起点，而非底层字节数组。
-/
def c160 := @ByteSlice.get

/--
从字节切片中取出一个字节；索引越界时返回默认值。

索引相对于字节切片的起点和终点，而非底层字节数组。默认值为 0。
-/
def c161 := @ByteSlice.get!

/--
从字节切片中取出一个字节；索引越界时返回默认值 `v₀`。

索引相对于字节切片的起点和终点，而非底层字节数组。
-/
def c162 := @ByteSlice.getD

/--
从 ByteArray 创建新的 ByteSlice
-/
def c163 := @ByteSlice.ofByteArray

/--
计算字节切片的大小。
-/
def c164 := @ByteSlice.size

/--
以给定边界创建字节切片的子切片。

如果 `start` 或 `stop` 不是子切片的有效边界，则将其限制在切片大小以内。此外，起始索引会被限制为不超过结束索引。

索引相对于当前切片，而非底层字节数组。
-/
def c165 := @ByteSlice.slice

/--
感兴趣区域的起始索引（含）。
-/
def c166 := @ByteSlice.start

/--
感兴趣区域的结束索引（不含）。
-/
def c167 := @ByteSlice.stop

/--
复制相关部分，将字节切片转换回字节数组。
-/
def c168 := @ByteSlice.toByteArray

/--
查找 `a` 中第一个使 `p` 返回 `true` 的字节的索引。如果 `a` 中没有字节满足 `p`，则结果为 `none`。

变体 `findFinIdx?` 还会返回“找到的索引未越界”的证明。
-/
def c169 := @ByteArray.findIdx?

/--
查找 `a` 中第一个使 `p` 返回 `true` 的字节的索引。如果 `a` 中没有字节满足 `p`，则结果为 `none`。

返回索引时还会附带它是数组中有效索引的证明。
-/
def c170 := @ByteArray.findFinIdx?

/--
对字长有符号整数取负。通常通过前缀运算符 `-` 使用。

此函数在运行时会被高效实现覆盖。
-/
def c171 := @ISize.neg

/--
对8 位有符号整数取负。通常通过前缀运算符 `-` 使用。

此函数在运行时会被高效实现覆盖。
-/
def c172 := @Int8.neg

/--
对16 位有符号整数取负。通常通过前缀运算符 `-` 使用。

此函数在运行时会被高效实现覆盖。
-/
def c173 := @Int16.neg

/--
对32 位有符号整数取负。通常通过前缀运算符 `-` 使用。

此函数在运行时会被高效实现覆盖。
-/
def c174 := @Int32.neg

/--
对64 位有符号整数取负。通常通过前缀运算符 `-` 使用。

此函数在运行时会被高效实现覆盖。
-/
def c175 := @Int64.neg

/--
对字长无符号整数取负，结果按 `USize.size` 取模。

此函数在运行时会被高效实现覆盖。
-/
def c176 := @USize.neg

/--
对8 位无符号整数取负，结果按 `UInt8.size` 取模。

`UInt8.neg a` 等价于 `255 - a + 1`。

此函数在运行时会被高效实现覆盖。
-/
def c177 := @UInt8.neg

/--
对16 位无符号整数取负，结果按 `UInt16.size` 取模。

`UInt16.neg a` 等价于 `65_535 - a + 1`。

此函数在运行时会被高效实现覆盖。
-/
def c178 := @UInt16.neg

/--
对32 位无符号整数取负，结果按 `UInt32.size` 取模。

`UInt32.neg a` 等价于 `429_4967_295 - a + 1`。

此函数在运行时会被高效实现覆盖。
-/
def c179 := @UInt32.neg

/--
对64 位无符号整数取负，结果按 `UInt64.size` 取模。

`UInt64.neg a` 等价于 `18_446_744_073_709_551_615 - a + 1`。

此函数在运行时会被高效实现覆盖。
-/
def c180 := @UInt64.neg

/--
将两个字长无符号整数相加，在溢出时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c181 := @USize.add

/--
将两个字长有符号整数相加，在溢出或下溢时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c182 := @ISize.add

/--
将两个8 位无符号整数相加，在溢出时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c183 := @UInt8.add

/--
将两个8 位有符号整数相加，在溢出或下溢时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c184 := @Int8.add

/--
将两个16 位无符号整数相加，在溢出时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c185 := @UInt16.add

/--
将两个16 位有符号整数相加，在溢出或下溢时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c186 := @Int16.add

/--
将两个32 位无符号整数相加，在溢出时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c187 := @UInt32.add

/--
将两个32 位有符号整数相加，在溢出或下溢时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c188 := @Int32.add

/--
将两个64 位无符号整数相加，在溢出时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c189 := @UInt64.add

/--
将两个64 位有符号整数相加，在溢出或下溢时回绕。通常通过 `+` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c190 := @Int64.add

/--
从另一个字长无符号整数中减去一个整数，在下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c191 := @USize.sub

/--
从另一个字长有符号整数中减去一个整数，在溢出或下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c192 := @ISize.sub

/--
从另一个8 位无符号整数中减去一个整数，在下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c193 := @UInt8.sub

/--
从另一个8 位有符号整数中减去一个整数，在溢出或下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c194 := @Int8.sub

/--
从另一个16 位无符号整数中减去一个整数，在下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c195 := @UInt16.sub

/--
从另一个16 位有符号整数中减去一个整数，在溢出或下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c196 := @Int16.sub

/--
从另一个32 位无符号整数中减去一个整数，在下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c197 := @UInt32.sub

/--
从另一个32 位有符号整数中减去一个整数，在溢出或下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c198 := @Int32.sub

/--
从另一个64 位无符号整数中减去一个整数，在下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c199 := @UInt64.sub

/--
从另一个64 位有符号整数中减去一个整数，在溢出或下溢时回绕。通常通过 `-` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c200 := @Int64.sub

/--
将两个字长无符号整数相乘，在溢出时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c201 := @USize.mul

/--
将两个字长有符号整数相乘，在溢出或下溢时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c202 := @ISize.mul

/--
将两个8 位无符号整数相乘，在溢出时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c203 := @UInt8.mul

/--
将两个8 位有符号整数相乘，在溢出或下溢时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c204 := @Int8.mul

/--
将两个16 位无符号整数相乘，在溢出时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c205 := @UInt16.mul

/--
将两个16 位有符号整数相乘，在溢出或下溢时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c206 := @Int16.mul

/--
将两个32 位无符号整数相乘，在溢出时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c207 := @UInt32.mul

/--
将两个32 位有符号整数相乘，在溢出或下溢时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c208 := @Int32.mul

/--
将两个64 位无符号整数相乘，在溢出时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c209 := @UInt64.mul

/--
将两个64 位有符号整数相乘，在溢出或下溢时回绕。通常通过 `*` 运算符使用。

此函数在运行时会被高效实现覆盖。
-/
def c210 := @Int64.mul

/--
字长无符号整数的无符号除法，舍弃余数。通常通过 `/` 运算符使用。

此操作有时称为“向下取整除法”。除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。
-/
def c211 := @USize.div

/--
字长有符号整数的截断除法，向零取整。通常通过 `/` 运算符使用。

除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。

示例：
* `ISize.div 10 3 = 3`
* `ISize.div 10 (-3) = (-3)`
* `ISize.div (-10) (-3) = 3`
* `ISize.div (-10) 3 = (-3)`
* `ISize.div 10 0 = 0`

-/
def c212 := @ISize.div

/--
8 位无符号整数的无符号除法，舍弃余数。通常通过 `/` 运算符使用。

此操作有时称为“向下取整除法”。除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。
-/
def c213 := @UInt8.div

/--
8 位有符号整数的截断除法，向零取整。通常通过 `/` 运算符使用。

除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。

示例：
* `Int8.div 10 3 = 3`
* `Int8.div 10 (-3) = (-3)`
* `Int8.div (-10) (-3) = 3`
* `Int8.div (-10) 3 = (-3)`
* `Int8.div 10 0 = 0`

-/
def c214 := @Int8.div

/--
16 位无符号整数的无符号除法，舍弃余数。通常通过 `/` 运算符使用。

此操作有时称为“向下取整除法”。除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。
-/
def c215 := @UInt16.div

/--
16 位有符号整数的截断除法，向零取整。通常通过 `/` 运算符使用。

除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。

示例：
* `Int16.div 10 3 = 3`
* `Int16.div 10 (-3) = (-3)`
* `Int16.div (-10) (-3) = 3`
* `Int16.div (-10) 3 = (-3)`
* `Int16.div 10 0 = 0`

-/
def c216 := @Int16.div

/--
32 位无符号整数的无符号除法，舍弃余数。通常通过 `/` 运算符使用。

此操作有时称为“向下取整除法”。除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。
-/
def c217 := @UInt32.div

/--
32 位有符号整数的截断除法，向零取整。通常通过 `/` 运算符使用。

除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。

示例：
* `Int32.div 10 3 = 3`
* `Int32.div 10 (-3) = (-3)`
* `Int32.div (-10) (-3) = 3`
* `Int32.div (-10) 3 = (-3)`
* `Int32.div 10 0 = 0`

-/
def c218 := @Int32.div

/--
64 位无符号整数的无符号除法，舍弃余数。通常通过 `/` 运算符使用。

此操作有时称为“向下取整除法”。除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。
-/
def c219 := @UInt64.div

/--
64 位有符号整数的截断除法，向零取整。通常通过 `/` 运算符使用。

除以零的结果定义为零。

此函数在运行时会被高效实现覆盖。

示例：
* `Int64.div 10 3 = 3`
* `Int64.div 10 (-3) = (-3)`
* `Int64.div (-10) (-3) = 3`
* `Int64.div (-10) 3 = (-3)`
* `Int64.div 10 0 = 0`

-/
def c220 := @Int64.div

/--
字长无符号整数的取模运算，计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `USize.mod 5 2 = 1`
* `USize.mod 4 2 = 0`
* `USize.mod 4 0 = 4`

-/
def c221 := @USize.mod

/--
字长有符号整数的取模运算，按 `ISize.div` 所用的向零取整约定计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `ISize.mod 5 2 = 1`
* `ISize.mod 5 (-2) = 1`
* `ISize.mod (-5) 2 = (-1)`
* `ISize.mod (-5) (-2) = (-1)`
* `ISize.mod 4 2 = 0`
* `ISize.mod 4 (-2) = 0`
* `ISize.mod 4 0 = 4`
* `ISize.mod (-4) 0 = (-4)`

-/
def c222 := @ISize.mod

/--
8 位无符号整数的取模运算，计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `UInt8.mod 5 2 = 1`
* `UInt8.mod 4 2 = 0`
* `UInt8.mod 4 0 = 4`

-/
def c223 := @UInt8.mod

/--
8 位有符号整数的取模运算，按 `Int8.div` 所用的向零取整约定计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `Int8.mod 5 2 = 1`
* `Int8.mod 5 (-2) = 1`
* `Int8.mod (-5) 2 = (-1)`
* `Int8.mod (-5) (-2) = (-1)`
* `Int8.mod 4 2 = 0`
* `Int8.mod 4 (-2) = 0`
* `Int8.mod 4 0 = 4`
* `Int8.mod (-4) 0 = (-4)`

-/
def c224 := @Int8.mod

/--
16 位无符号整数的取模运算，计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `UInt16.mod 5 2 = 1`
* `UInt16.mod 4 2 = 0`
* `UInt16.mod 4 0 = 4`

-/
def c225 := @UInt16.mod

/--
16 位有符号整数的取模运算，按 `Int16.div` 所用的向零取整约定计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `Int16.mod 5 2 = 1`
* `Int16.mod 5 (-2) = 1`
* `Int16.mod (-5) 2 = (-1)`
* `Int16.mod (-5) (-2) = (-1)`
* `Int16.mod 4 2 = 0`
* `Int16.mod 4 (-2) = 0`
* `Int16.mod 4 0 = 4`
* `Int16.mod (-4) 0 = (-4)`

-/
def c226 := @Int16.mod

/--
32 位无符号整数的取模运算，计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `UInt32.mod 5 2 = 1`
* `UInt32.mod 4 2 = 0`
* `UInt32.mod 4 0 = 4`

-/
def c227 := @UInt32.mod

/--
32 位有符号整数的取模运算，按 `Int32.div` 所用的向零取整约定计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `Int32.mod 5 2 = 1`
* `Int32.mod 5 (-2) = 1`
* `Int32.mod (-5) 2 = (-1)`
* `Int32.mod (-5) (-2) = (-1)`
* `Int32.mod 4 2 = 0`
* `Int32.mod 4 (-2) = 0`
* `Int32.mod 4 0 = 4`
* `Int32.mod (-4) 0 = (-4)`

-/
def c228 := @Int32.mod

/--
64 位无符号整数的取模运算，计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `UInt64.mod 5 2 = 1`
* `UInt64.mod 4 2 = 0`
* `UInt64.mod 4 0 = 4`

-/
def c229 := @UInt64.mod

/--
64 位有符号整数的取模运算，按 `Int64.div` 所用的向零取整约定计算一个整数除以另一个整数的余数。通常通过 `%` 运算符使用。

当除数为 `0` 时，结果为被除数，而不是报错。

此函数在运行时会被高效实现覆盖。

示例：
* `Int64.mod 5 2 = 1`
* `Int64.mod 5 (-2) = 1`
* `Int64.mod (-5) 2 = (-1)`
* `Int64.mod (-5) (-2) = (-1)`
* `Int64.mod 4 2 = 0`
* `Int64.mod 4 (-2) = 0`
* `Int64.mod 4 0 = 4`
* `Int64.mod (-4) 0 = (-4)`

-/
def c230 := @Int64.mod

/--
字长无符号整数的以 2 为底的对数。返回 `⌊max 0 (log₂ a)⌋`。

此函数在运行时会被高效实现覆盖。此定义是其逻辑模型。

示例：
 * `USize.log2 0 = 0`
 * `USize.log2 1 = 0`
 * `USize.log2 2 = 1`
 * `USize.log2 4 = 2`
 * `USize.log2 7 = 2`
 * `USize.log2 8 = 3`

-/
def c231 := @USize.log2

/--
8 位无符号整数的以 2 为底的对数。返回 `⌊max 0 (log₂ a)⌋`。

此函数在运行时会被高效实现覆盖。此定义是其逻辑模型。

示例：
 * `UInt8.log2 0 = 0`
 * `UInt8.log2 1 = 0`
 * `UInt8.log2 2 = 1`
 * `UInt8.log2 4 = 2`
 * `UInt8.log2 7 = 2`
 * `UInt8.log2 8 = 3`

-/
def c232 := @UInt8.log2

/--
16 位无符号整数的以 2 为底的对数。返回 `⌊max 0 (log₂ a)⌋`。

此函数在运行时会被高效实现覆盖。此定义是其逻辑模型。

示例：
 * `UInt16.log2 0 = 0`
 * `UInt16.log2 1 = 0`
 * `UInt16.log2 2 = 1`
 * `UInt16.log2 4 = 2`
 * `UInt16.log2 7 = 2`
 * `UInt16.log2 8 = 3`

-/
def c233 := @UInt16.log2

/--
32 位无符号整数的以 2 为底的对数。返回 `⌊max 0 (log₂ a)⌋`。

此函数在运行时会被高效实现覆盖。此定义是其逻辑模型。

示例：
 * `UInt32.log2 0 = 0`
 * `UInt32.log2 1 = 0`
 * `UInt32.log2 2 = 1`
 * `UInt32.log2 4 = 2`
 * `UInt32.log2 7 = 2`
 * `UInt32.log2 8 = 3`

-/
def c234 := @UInt32.log2

/--
64 位无符号整数的以 2 为底的对数。返回 `⌊max 0 (log₂ a)⌋`。

此函数在运行时会被高效实现覆盖。此定义是其逻辑模型。

示例：
 * `UInt64.log2 0 = 0`
 * `UInt64.log2 1 = 0`
 * `UInt64.log2 2 = 1`
 * `UInt64.log2 4 = 2`
 * `UInt64.log2 7 = 2`
 * `UInt64.log2 8 = 3`

-/
def c235 := @UInt64.log2

/--
计算字长有符号整数的绝对值。

此函数等价于 `if a < 0 then -a else a`，因此特别地，`ISize.minValue` 会映射到 `ISize.minValue`。

此函数在运行时会被高效实现覆盖。
-/
def c236 := @ISize.abs

/--
计算8 位有符号整数的绝对值。

此函数等价于 `if a < 0 then -a else a`，因此特别地，`Int8.minValue` 会映射到 `Int8.minValue`。

此函数在运行时会被高效实现覆盖。
-/
def c237 := @Int8.abs

/--
计算16 位有符号整数的绝对值。

此函数等价于 `if a < 0 then -a else a`，因此特别地，`Int16.minValue` 会映射到 `Int16.minValue`。

此函数在运行时会被高效实现覆盖。
-/
def c238 := @Int16.abs

/--
计算32 位有符号整数的绝对值。

此函数等价于 `if a < 0 then -a else a`，因此特别地，`Int32.minValue` 会映射到 `Int32.minValue`。

此函数在运行时会被高效实现覆盖。
-/
def c239 := @Int32.abs

/--
计算64 位有符号整数的绝对值。

此函数等价于 `if a < 0 then -a else a`，因此特别地，`Int64.minValue` 会映射到 `Int64.minValue`。

此函数在运行时会被高效实现覆盖。
-/
def c240 := @Int64.abs

/--
检查两个列表是否长度相同，且对应元素两两满足 `BEq`。通常通过 `==` 运算符使用。
-/
def c241 := @List.beq

/--
返回 `true`，如果 `as` 和 `bs` 长度相同，且对应元素两两满足关系 `eqv`。

复杂度为 `O(min |as| |bs|)`。遇到第一对不满足关系的元素时短路。

示例：
* `[1, 2, 3].isEqv [2, 3, 4] (· < ·) = true`
* `[1, 2, 3].isEqv [2, 2, 4] (· < ·) = false`
* `[1, 2, 3].isEqv [2, 3] (· < ·) = false`
-/
def c242 := @List.isEqv

/--
返回 `true`，如果 `l₁` 和 `l₂` 互为排列。复杂度为 `O(|l₁| * |l₂|)`。

关系 `List.Perm` 是排列的逻辑刻画。当 `BEq α` 实例与 `DecidableEq α` 对应时，`isPerm l₁ l₂ ↔ l₁ ~ l₂`（使用定理 `isPerm_iff`）。
-/
def c243 := @List.isPerm

/--
检查第一个列表是否为第二个列表的前缀。

关系 `List.IsPrefixOf` 使用逻辑相等来表达此性质。

示例：
* `[1, 2].isPrefixOf [1, 2, 3] = true`
* `[1, 2].isPrefixOf [1, 2] = true`
* `[1, 2].isPrefixOf [1] = false`
* `[1, 2].isPrefixOf [1, 1, 2, 3] = false`
-/
def c244 := @List.isPrefixOf

/--
如果第一个列表是第二个列表的前缀，则返回从第二个列表中去掉该前缀后的结果。

换言之，`isPrefixOf? l₁ l₂` 返回 `some t`，当且仅当 `l₂ == l₁ ++ t`。

示例：
* `[1, 2].isPrefixOf? [1, 2, 3] = some [3]`
* `[1, 2].isPrefixOf? [1, 2] = some []`
* `[1, 2].isPrefixOf? [1] = none`
* `[1, 2].isPrefixOf? [1, 1, 2, 3] = none`
-/
def c245 := @List.isPrefixOf?

/--
如果第一个列表是第二个列表的子序列（不要求连续），则为真；元素使用 `==` 运算符比较。

关系 `List.Sublist` 是此性质的逻辑刻画。

示例：
* `[1, 3].isSublist [0, 1, 2, 3, 4] = true`
* `[1, 3].isSublist [0, 1, 2, 4] = false`
-/
def c246 := @List.isSublist

/--
检查第一个列表是否为第二个列表的后缀。

关系 `List.IsSuffixOf` 使用逻辑相等来表达此性质。

示例：
* `[2, 3].isSuffixOf [1, 2, 3] = true`
* `[2, 3].isSuffixOf [1, 2, 3, 4] = false`
* `[2, 3].isSuffixOf [1, 2] = false`
* `[2, 3].isSuffixOf [1, 1, 2, 3] = true`
-/
def c247 := @List.isSuffixOf

/--
如果第一个列表是第二个列表的后缀，则返回从第二个列表中去掉该后缀后的结果。

换言之，`isSuffixOf? l₁ l₂` 返回 `some t`，当且仅当 `l₂ == t ++ l₁`。

示例：
 * `[2, 3].isSuffixOf? [1, 2, 3] = some [1]`
 * `[2, 3].isSuffixOf? [1, 2, 3, 4] = none`
 * `[2, 3].isSuffixOf? [1, 2] = none`
 * `[2, 3].isSuffixOf? [1, 1, 2, 3] = some [1, 1]`
-/
def c248 := @List.isSuffixOf?

/--
列表相对于其元素严格顺序的非严格顺序。

`as ≤ bs` 成立，如果 `¬ bs < as`。

如果底层 `LT α` 实例具有良好性质，则可将此关系视为字典序。具体而言，它应满足非自反性、非对称性和反对称性。这些要求在 `List.cons_le_cons_iff` 中有精确表述。若这些性质成立，则 `as ≤ bs` 当且仅当：
 * `as` 为空；或
 * `as` 和 `bs` 都非空，且 `as` 的首元素小于 `bs` 的首元素；或
 * `as` 和 `bs` 都非空、首元素相等，且 `as` 的尾部小于或等于 `bs` 的尾部。
-/
def c249 := @List.le

/--
列表相对于其元素顺序的字典序。

当满足以下条件之一时，`as < bs`：
* `as` 为空且 `bs` 非空；或
* `as` 和 `bs` 都非空，且 `as` 的首元素小于 `bs` 的首元素；或
* `as` 和 `bs` 都非空、首元素相等，且 `as` 的尾部小于 `bs` 的尾部。
-/
def c250 := @List.lt

/--
根据元素上的比较按字典序比较列表。

相对于 `lt` 的字典序定义如下：
* `[].lex (b :: bs)` 为 `true`
* `as.lex [] = false` 为 `false`
* `(a :: as).lex (b :: bs)` 为真，如果 `lt a b`，或者 `a == b` 且 `lex lt as bs` 为真。
-/
def c251 := @List.lex

end Manual.ZhDocString.Ch19Ch20.G6
