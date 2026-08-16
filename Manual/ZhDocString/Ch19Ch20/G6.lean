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
树映射.

树映射存储一个值的键分配 。 取决于比较函数
定义按键的顺序,并提供高效的依顺序查询,例如检索
最小或最大值。

为确保业务如预期的那样运作,比较方职能`cmp`应满足
某些确保一致命令的法律:

* 若为`a`小于(或等于)`b`,则`b`大于(或等于)`a`
和反之亦然(见`OrientedCmp`类型类)。
* 若为`a`小于或等于`b`和`b`反过来,小于或等于`c`,则`a`
小于或等于`c`(见《大会正式记录,第五十八届会议,补编第6号》)。`TransCmp`类型类)。

其中的键`cmp a b = Ordering.eq`被认为是相同的,即只能有一个条目
带键`a`或`b`在树映射中。 随便找`a`或`b`总是产生相同的条目,
如果有的话。

为了避免昂贵的拷贝,用户应当确保树映射线性使用.

在内部,树映射作为带大小信息的红黑树表示,一种自平衡二进制
以高效的顺序统计查询搜索树 。

用于证明,类型`Std.ExtTreeMap`应选择扩展树映射。 这个
类型带有多个延伸性lemma,并提供了相同的函数,但需要一个
`TransCmp`以实例说明需要合作。

这些树映射包含一个内置的形状不变量,这意味着它们不能
用于嵌套诱导类型。 对于这些案件,`Std.TreeMap.Raw`和
`Std.TreeMap.Raw.WF`解开树映射上的变种 当怀疑的时候,
`TreeMap`结束`TreeMap.Raw`.
-/
structure c001 (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- 内部树映射实现细节。 -/
  inner : Std.DTreeMap α (fun _ => β) cmp

/--
创建新的空树映射。 这也是可能的,并建议
使用空白的集合标记`∅`和`{}`创建空树映射。`simp`替换
`empty`与`∅`.
-/
def c002 := @Std.TreeMap.empty

/--
返回映射中映射的数量。
-/
def c003 := @Std.TreeMap.size

/--
返回`true`如果树映射中没有映射。
-/
def c004 := @Std.TreeMap.isEmpty

/--
返回`true`如果给定的键有映射`a`或等于`a`根据
与比较者比较`cmp`。还有一个`Prop`- 价值版本
其中:`a ∈ t`等同为`t.contains a = true`.

注意,这是不同的行为 与列表: 对于列表,`∈`用途`=`和`contains`用途
`==`用于平等检查,而用于树映射,两者都使用给定的比较器`cmp`.
-/
def c005 := @Std.TreeMap.contains

/--
鉴于有证据表明存在给定键的映射,请检索给定键的映射.

使用`LawfulEqCmp`实例将检索值投放到正确的类型。
-/
def c006 := @Std.TreeMap.get

/--
尝试获取给定键的映射, 如果不存在这样的映射, 则会触发 panic 。

使用`LawfulEqCmp`实例将检索值投放到正确的类型。
-/
def c007 := @Std.TreeMap.get!

/--
尝试获取给定键的映射, 返回`none`如果不存在这样的映射。

使用`LawfulEqCmp`实例将检索值投放到正确的类型。
-/
def c008 := @Std.TreeMap.get?

/--
尝试获取给定键的映射, 返回`fallback`如果不存在这样的映射。

使用`LawfulEqCmp`实例将检索值投放到正确的类型。
-/
def c009 := @Std.TreeMap.getD

/--
从匹配的映射中获取键`a`。确保这种映射由
要求证明:`a ∈ m`。结果保证与映射中的键相等。
-/
def c010 := @Std.TreeMap.getKey

/--
检查给定键的映射是否存在, 如果有, 则返回键, 否则会触发 panic 。
如果不发生恐慌,结果将保证与映射中的键相等。
-/
def c011 := @Std.TreeMap.getKey!

/--
检查给定键的映射是否存在, 如果有, 则返回该键, 否则`none`.
结果是:`some`大小写保证与映射中的键相等。
-/
def c012 := @Std.TreeMap.getKey?

/--
检查给定键的映射是否存在, 如果有, 则返回该键, 否则`fallback`.
如果映射存在,结果将保证与映射中的键相等。
-/
def c013 := @Std.TreeMap.getKeyD

/--
以升序返回树映射中所有键的列表。
-/
def c014 := @Std.TreeMap.keys

/--
以上升顺序返回树映射中所有键的数组。
-/
def c015 := @Std.TreeMap.keysArray

/--
按升序返回树映射中所有值的列表。
-/
def c016 := @Std.TreeMap.values

/--
以升序返回树映射中所有值的数组。
-/
def c017 := @Std.TreeMap.valuesArray

/--
返回键值配对`n`- 最小的钥匙
-/
def c018 := @Std.TreeMap.entryAtIdx

/--
返回键值配对`n`- 最小的钥匙,或者恐慌,如果`n`至少为`t.size`.
-/
def c019 := @Std.TreeMap.entryAtIdx!

/--
返回键值配对`n`- 最小的钥匙,或者`none`若为`n`至少为`t.size`.
-/
def c020 := @Std.TreeMap.entryAtIdx?

/--
返回键值配对`n`- 最小的钥匙,或者`fallback`若为`n`至少为`t.size`.
-/
def c021 := @Std.TreeMap.entryAtIdxD

/--
由于有证据表明存在这样的映射,所以要用最小的键来获取键值对
大于或等于给定的键。
-/
def c022 := @Std.TreeMap.getEntryGE

/--
尝试以大于或等于
给定键, 如果没有这种对, 就会触发 panic。
-/
def c023 := @Std.TreeMap.getEntryGE!

/--
尝试以大于或等于
给定键,返回`none`如果不存在这种对。
-/
def c024 := @Std.TreeMap.getEntryGE?

/--
尝试以大于或等于
给定键,返回`fallback`如果不存在这种对。
-/
def c025 := @Std.TreeMap.getEntryGED

/--
由于有证据表明存在这样的映射,所以要用最小的键来获取键值对
大于给定的键。
-/
def c026 := @Std.TreeMap.getEntryGT

/--
尝试用比给定的键更大的最小键获取键值对,
如果不存在这种配对, 就会触发 panic。
-/
def c027 := @Std.TreeMap.getEntryGT!

/--
尝试用比给定的键更大的最小键获取键值对,
返回时`none`如果不存在这种对。
-/
def c028 := @Std.TreeMap.getEntryGT?

/--
尝试用比给定的键更大的最小键获取键值对,
返回时`fallback`如果不存在这种对。
-/
def c029 := @Std.TreeMap.getEntryGTD

/--
鉴于有证据表明存在这种映射,用最大的键检索键值对。
小于或等于给定的键。
-/
def c030 := @Std.TreeMap.getEntryLE

/--
尝试以小于或等于
给定键, 如果没有这种对, 就会触发 panic。
-/
def c031 := @Std.TreeMap.getEntryLE!

/--
尝试以小于或等于
给定键,返回`none`如果不存在这种对。
-/
def c032 := @Std.TreeMap.getEntryLE?

/--
尝试以小于或等于
给定键,返回`fallback`如果不存在这种对。
-/
def c033 := @Std.TreeMap.getEntryLED

/--
鉴于有证据表明存在这种映射,用最大的键检索键值对。
小于给定的键。
-/
def c034 := @Std.TreeMap.getEntryLT

/--
尝试以比给定的键小的最大键获取键值对,
如果不存在这种配对, 就会触发 panic。
-/
def c035 := @Std.TreeMap.getEntryLT!

/--
尝试以比给定的键小的最大键获取键值对,
返回时`none`如果不存在这种对。
-/
def c036 := @Std.TreeMap.getEntryLT?

/--
尝试以比给定的键小的最大键获取键值对,
返回时`fallback`如果不存在这种对。
-/
def c037 := @Std.TreeMap.getEntryLTD

/--
鉴于有证据表明存在这样的映射 , 检索最小的键是
大于或等于给定的键。
-/
def c038 := @Std.TreeMap.getKeyGE

/--
尝试获取大于或等于
给定键, 如果没有这样的键, 就会触发 panic。
-/
def c039 := @Std.TreeMap.getKeyGE!

/--
尝试获取大于或等于
给定键,返回`none`如果不存在这种键。
-/
def c040 := @Std.TreeMap.getKeyGE?

/--
尝试获取大于或等于
给定键,返回`fallback`如果不存在这种键。
-/
def c041 := @Std.TreeMap.getKeyGED

/--
鉴于有证据表明存在这样的映射 , 检索最小的键是
大于给定的键。
-/
def c042 := @Std.TreeMap.getKeyGT

/--
尝试获取比给定的键更大的最小键,
如果不存在这种键, 就会触发 panic。
-/
def c043 := @Std.TreeMap.getKeyGT!

/--
尝试获取比给定的键更大的最小键,
返回时`none`如果不存在这种键。
-/
def c044 := @Std.TreeMap.getKeyGT?

/--
尝试获取比给定的键更大的最小键,
返回时`fallback`如果不存在这种键。
-/
def c045 := @Std.TreeMap.getKeyGTD

/--
鉴于有证据表明存在这种映射,因此检索最大的键,即
小于或等于给定的键。
-/
def c046 := @Std.TreeMap.getKeyLE

/--
尝试获取小于或等于
给定键, 如果没有这样的键, 就会触发 panic。
-/
def c047 := @Std.TreeMap.getKeyLE!

/--
尝试获取小于或等于
给定键,返回`none`如果不存在这种键。
-/
def c048 := @Std.TreeMap.getKeyLE?

/--
尝试获取小于或等于
给定键,返回`fallback`如果不存在这种键。
-/
def c049 := @Std.TreeMap.getKeyLED

/--
鉴于有证据表明存在这种映射,因此检索最大的键,即
小于给定的键。
-/
def c050 := @Std.TreeMap.getKeyLT

/--
试图获取比给定的键小的最大键,
如果不存在这种键, 就会触发 panic。
-/
def c051 := @Std.TreeMap.getKeyLT!

/--
试图获取比给定的键小的最大键,
返回时`none`如果不存在这种键。
-/
def c052 := @Std.TreeMap.getKeyLT?

/--
试图获取比给定的键小的最大键,
返回时`fallback`如果不存在这种键。
-/
def c053 := @Std.TreeMap.getKeyLTD

/--
返回`n`- 最小的钥匙
-/
def c054 := @Std.TreeMap.keyAtIdx

/--
返回`n`- 最小的钥匙,或者恐慌,如果`n`至少为`t.size`.
-/
def c055 := @Std.TreeMap.keyAtIdx!

/--
返回`n`- 最小的钥匙,或者`none`若为`n`至少为`t.size`.
-/
def c056 := @Std.TreeMap.keyAtIdx?

/--
返回`n`- 最小的钥匙,或者`fallback`若为`n`至少为`t.size`.
-/
def c057 := @Std.TreeMap.keyAtIdxD

/--
鉴于树映射并非空的证明,用最小的键检索键值对.
-/
def c058 := @Std.TreeMap.minEntry

/--
尝试用树映射中最小的键获取键值对, 如果映射是 , 就会触发 panic
空.
-/
def c059 := @Std.TreeMap.minEntry!

/--
尝试获取树映射中最小的键对, 返回`none`如果
映射为空。
-/
def c060 := @Std.TreeMap.minEntry?

/--
尝试获取树映射中最小的键对, 返回`fallback`若为
树映射为空。
-/
def c061 := @Std.TreeMap.minEntryD

/--
鉴于树映射并非空的证明, 获取最小的键 。
-/
def c062 := @Std.TreeMap.minKey

/--
尝试获取树映射中最小的键, 如果映射为空则会触发 panic 。
-/
def c063 := @Std.TreeMap.minKey!

/--
尝试获取树映射中最小的键, 返回`none`如果映射是空的。
-/
def c064 := @Std.TreeMap.minKey?

/--
尝试获取树映射中最小的键, 返回`fallback`如果树映射是空的。
-/
def c065 := @Std.TreeMap.minKeyD

/--
鉴于树映射不是空的证明,以最大的键检索键值对.
-/
def c066 := @Std.TreeMap.maxEntry

/--
试图以树映射中最大的键获取键值对, 如果映射是 , 就会触发 panic
空.
-/
def c067 := @Std.TreeMap.maxEntry!

/--
尝试以树映射中最大的键获取键对, 返回`none`如果
映射为空。
-/
def c068 := @Std.TreeMap.maxEntry?

/--
尝试以树映射中最大的键获取键对, 返回`fallback`若为
树映射为空。
-/
def c069 := @Std.TreeMap.maxEntryD

/--
鉴于树映射并非空的证明,可以检索最大的键.
-/
def c070 := @Std.TreeMap.maxKey

/--
尝试获取树映射中最大的键, 如果映射为空则会触发 panic 。
-/
def c071 := @Std.TreeMap.maxKey!

/--
尝试获取树映射中最大的键, 返回`none`如果映射是空的。
-/
def c072 := @Std.TreeMap.maxKey?

/--
尝试获取树映射中最大的键, 返回`fallback`如果树映射是空的。
-/
def c073 := @Std.TreeMap.maxKeyD

/--
修改与给定键相关的值,
允许通过一个`Option`价值较高的替换功能。

此函数确保该值被线性使用.
-/
def c074 := @Std.TreeMap.alter

/--
修改与给定键相关的值。

此函数确保该值被线性使用.
-/
def c075 := @Std.TreeMap.modify

/--
检查键是否在映射图中存在,并无条件插入键的值。

相当于(但可能更快于)呼叫`contains`接下来是`insert`.
-/
def c076 := @Std.TreeMap.containsThenInsert

/--
检查键是否在映射中存在,如果找不到,则插入键的值。
如果归来`Bool`这是`true`,则返回的映射不变。 如果`Bool`这是`false`,
然后返回的映射中插入了新的值。

相当于(但可能更快于)呼叫`contains`接下来是`insertIfNew`.
-/
def c077 := @Std.TreeMap.containsThenInsertIfNew

/--
删除给定键的映射,如果它存在。
-/
def c078 := @Std.TreeMap.erase

/--
通过在给定的集合和调用来擦除树映射上的多幅映射
`erase`.
-/
def c079 := @Std.TreeMap.eraseMany

/--
删除给定函数返回的所有映射`false`.
-/
def c080 := @Std.TreeMap.filter

/--
通过对所有映射应用给定的函数来更新映射值,保存
只有函数返回的映射`some`数值。
-/
def c081 := @Std.TreeMap.filterMap

/--
在映射中插入给定的映射。 如果已经对给定的键进行了映射, 那么两者
键和值将被替换。
-/
def c082 := @Std.TreeMap.insert

/--
如果没有给定键的映射,则将给定的映射插入映射. 否则
返回未更改的映射。
-/
def c083 := @Std.TreeMap.insertIfNew

/--
检查映射中是否存在键,返回关联值,并插入一个值,用于
未找到的键。

如果返回的值是`some v`,则返回的映射不变。 如果是的话`none`,然后是
返回的映射已插入新值。

相当于(但可能更快于)呼叫`get?`接下来是`insertIfNew`.

使用`LawfulEqCmp`实例将检索值投放到正确的类型。
-/
def c084 := @Std.TreeMap.getThenInsertIfNew?

/--
通过在给定的集合上延展和调用,在树映射中插入多幅映射
`insert`。如果同一键出现多次,则以上次发生为准。

注意: 此优先行为对`TreeMap`, `DTreeMap`, `TreeMap.Raw`和`DTreeMap.Raw`.
这个`insertMany`函数`TreeSet`和`TreeSet.Raw`行为不同:它更喜欢第一个
出现。
-/
def c085 := @Std.TreeMap.insertMany

/--
在树映射中插入多个元素, 方法是在给定的集合上延展并调用
`insertIfNew`。如果同一键出现多次,则首先发生。
-/
def c086 := @Std.TreeMap.insertManyIfNewUnit

/--
返回包含所有映射的映射`t₁`和`t₂`。如果两张映射都包含
相同的键`k`关于`cmp`,用于确定从
相应的数值`t₁`和`t₂`.

此功能确保`t₁`用于线性。 它还使用个人值在`t₁`
线性如果合并函数使用第二个参数(即类型的第一个)`β a`线性。
因此,只要`t₁`不共享, 性能特征遵循以下要求
说明: 在所有映射中以斜体表示`t₂`,插入到`t₁`若为`t₁`不包含
映射还有些冲突 若为`t₁`包含一个相互冲突的映射,使用指定的合并函数到
将映射合并到`t₂`进入映射`t₁`返回时`t₁`.

因此,这种方法的运行时间按大小对数计算`t₁`和线性大小
`t₂`只要我们...`t₁`未分摊。
-/
def c087 := @Std.TreeMap.mergeWith

/--
根据上游将树映射分割成两个树映射。
-/
def c088 := @Std.TreeMap.partition

/--
在树映射条目上返回一个有限迭代器。
迭代器按顺序输出映射的元素,然后终止.

** 终止属性:**

* `Finite`实例: 始终
* `Productive`实例: 始终
-/
def c089 := @Std.TreeMap.iter

/--
返回树映射键上的有限迭代器。
迭代器按顺序生成键,然后终止。

关键和价值类型必须生活在同一个宇宙中.

** 终止属性:**

* `Finite`实例: 始终
* `Productive`实例: 始终
-/
def c090 := @Std.TreeMap.keysIter

/--
返回对树映射值的有限迭代器。
迭代器按顺序生成数值,然后终止。

关键和价值类型必须生活在同一个宇宙中.

** 终止属性:**

* `Finite`实例: 始终
* `Productive`实例: 始终
-/
def c091 := @Std.TreeMap.valuesIter

/--
通过对所有映射应用给定的函数来更新映射值。
-/
def c092 := @Std.TreeMap.map

/--
检查所有元素是否满足了上游,短路,如果上游失败.
-/
def c093 := @Std.TreeMap.all

/--
检查任何元素是否满足上游短路, 如果上游故障 。
-/
def c094 := @Std.TreeMap.any

/--
按升序将给定的函数覆盖在映射图上。
-/
def c095 := @Std.TreeMap.foldl

/--
将给定的单子函数以上升顺序覆盖映射中的映射。
-/
def c096 := @Std.TreeMap.foldlM

/--
将给定的函数依次覆盖映射中的映射。
-/
def c097 := @Std.TreeMap.foldr

/--
将给定的单子函数依次覆盖映射中的映射。
-/
def c098 := @Std.TreeMap.foldrM

/--
支助`for`循环构造在`do`块。 迭代按升序发生.
-/
def c099 := @Std.TreeMap.forIn

/--
在树映射上按上升顺序对每张映射进行一个单子动作.
-/
def c100 := @Std.TreeMap.forM

/--
将映射列表转换为树映射。
-/
def c101 := @Std.TreeMap.ofList

/--
按升序将树映射转换为映射列表。
-/
def c102 := @Std.TreeMap.toList

/--
将映射列表转换为树映射。
-/
def c103 := @Std.TreeMap.ofArray

/--
按升序将树映射转换为映射列表。
-/
def c104 := @Std.TreeMap.toArray

/--
将一系列键转换成树映射。
-/
def c105 := @Std.TreeMap.unitOfArray

/--
将键列表转换为树映射。
-/
def c106 := @Std.TreeMap.unitOfList

/--
树映射没有内置的形状不变量,适合用于嵌套
诱导类型。 形而上学的无常`Raw.WF`。当出现疑问时,倾向于`TreeMap`
结束`TreeMap.Raw`. Lemmas 关于操作`Std.TreeMap.Raw`可在
模块`Std.Data.TreeMap.Raw.Lemmas`.

树映射存储一个值的键分配 。 取决于比较函数
定义按键的顺序,并提供高效的依顺序查询,例如检索
最小或最大值。

为确保业务如预期的那样运作,比较方职能`cmp`应满足
某些确保一致命令的法律:

* 若为`a`小于(或等于)`b`,则`b`大于(或等于)`a`
和反之亦然(见`OrientedCmp`类型类)。
* 若为`a`小于或等于`b`和`b`反过来,小于或等于`c`,则`a`
小于或等于`c`(见《大会正式记录,第五十八届会议,补编第6号》)。`TransCmp`类型类)。

其中的键`cmp a b = Ordering.eq`被认为是相同的,即只能有一个条目
带键`a`或`b`在树映射中。 随便找`a`或`b`总是产生相同的条目,
如果有的话。

为了避免昂贵的拷贝,用户应当确保树映射线性使用.

在内部,树映射作为带大小信息的红黑树表示,一种自平衡二进制
以高效的顺序统计查询搜索树 。
-/
structure c107 (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- 内部树映射实现细节。 -/
  inner : Std.DTreeMap.Raw α (fun _ => β) cmp

/--
树映射的良构性不变量. 用户`TreeMap`不需要与
这个 用户`TreeMap.Raw`需要提供证明`WF`{\fn黑体\fs22\bord1\shad0\3aHBE\4aH00\fscx67\fscy66\2cHFFFFFF\3cH808080}莱玛应该用莱玛
喜欢`WF.empty`和`WF.insert`(它们总是被命名 完全像他们的行动)
以显示映射操作保持良好的结构。 这种类型的构造器是内部的
实施细节,用户不应查阅。
-/
structure c108 {α : Type u} {β : Type v} {cmp : α → α → Ordering}
    (t : Std.TreeMap.Raw α β cmp) : Prop where
  /-- 内部树映射实现细节。 -/
  out : t.inner.WF

/--
`ByteArray`碞钩`Array UInt8`,但有一个高效的运行时间 代表作为一个包装
字节缓冲.
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
构造具有初始容量的新空字节数组`0`.

使用`ByteArray.emptyWithCapacity`以创建初始容量更大的阵列。
-/
def c110 := @ByteArray.empty

/--
构造具有初始容量的新空字节数组`c`.
-/
def c111 := @ByteArray.emptyWithCapacity

/--
附加两个字节数组。

在编译代码中,调用`ByteArray.append`换成效率更高
`ByteArray.fastAppend`.
-/
def c112 := @ByteArray.append

/--
使用快速阵列原始来附加两个字节数组,而不是将它们转换成列表和返回.

在编译代码中,此函数替换调用到`ByteArray.append`.
-/
def c113 := @ByteArray.fastAppend

/--
复制切片时`[srcOff, srcOff + len)`输入`src`改为`[destOff, destOff + len)`输入
`dest`,增长`dest`必要时。 若为`exact`这是`false`,能力
长大后会加倍。
-/
def c114 := @ByteArray.copySlice

/--
返回字节数组中的字节数。

这是数组中实际的字节数,与其容量不同,即
目前为数组分配的内存量。
-/
def c115 := @ByteArray.size

/--
将数组的大小作为平台专用的固定width整数.

因为`USize`足以解决里恩支持的每个平台上的所有记忆
实际上没有`ByteArray`含有更多元素的 s`USize`可以数.
-/
def c116 := @ByteArray.usize

/--
返回`true`何时`s`包含零字节。
-/
def c117 := @ByteArray.isEmpty

/--
在指定的索引中获取字节。 来电者必须证明指数处于极限.

使用`uget`更有效率的替代品或`get!`对于一个变体,如果
索引已超出范围。
-/
def c118 := @ByteArray.get

/--
在指定的索引中获取字节。 来电者必须证明指数处于极限. 指数
由平台特定的固定宽整数\(32位或64位)代表。

因为`USize`足够大,可以处理利恩支持的每个平台上的所有内存
实际操作中无`ByteArray`s 对`uget`无法获取全部元素。
-/
def c119 := @ByteArray.uget

/--
在指定的索引中获取字节。 如果指数超出范围,就会出现恐慌。
-/
def c120 := @ByteArray.get!

/--
复制带有索引的字节`b`\(包含)为`e`\( 独家) 到一个新
`ByteArray`.
-/
def c121 := @ByteArray.extract

/--
将组合的字节数组转换为链接列表。
-/
def c122 := @ByteArray.toList

/--
口译a`ByteArray`以8号为大号`UInt64`.

如果数组的大小不是8. Panics.
-/
def c123 := @ByteArray.toUInt64BE!

/--
口译a`ByteArray`大小 8 作为小-endian`UInt64`.

如果数组的大小不是8. Panics.
-/
def c124 := @ByteArray.toUInt64LE!

/--
解码其UTF-8代表的字符序列. 返回`none`如果字节是
而非Unicode scalar 值的序列。
-/
def c125 := @ByteArray.utf8Decode?

/--
解码并返回`Char`UTF-8 编码起始于`i`输入`bytes`.

返回`none`若为`i`不是字符的有效 UTF-8 编码的开始。
-/
def c126 := @ByteArray.utf8DecodeChar?

/--
解码并返回`Char`UTF-8 编码起始于`i`输入`bytes`.

这个功能需要证明,事实上存在有效`Char`时间`i`. `utf8DecodeChar?`这是
返回的替代函数`Option Char`而不是提前要求证据
-/
def c127 := @ByteArray.utf8DecodeChar

/--
将元素添加到数组的末尾。 产生的数组大小大于输入
数组。 如果该数组没有其它引用,则在位置上修改.

这需要摊还`O(1)`时间因为`ByteArray`以动态数组表示。
-/
def c128 := @ByteArray.push

/--
替换给定索引中的字节。

没有执行边框检查,但功能需要证明索引是边框的. 这个
证明通常可以省略,并将自动合成。

如果没有其他参考文献,则在原位修改数组。
-/
def c129 := @ByteArray.set

/--
替换给定索引中的字节。

没有执行边框检查,但功能需要证明索引是边框的. 这个
证明通常可以省略,并将自动合成。

如果没有其他参考文献,则在原位修改数组。
-/
def c130 := @ByteArray.uset

/--
替换给定索引中的字节。

如果没有其他参考文献,则在原位修改数组。

如果索引超出范围,则未修改数组返回。
-/
def c131 := @ByteArray.set!

/--
左边折叠`ByteArray`在从低指数到高指数的数组上移动,计算a
正在运行值。

数组的每个元素都与使用函数的先前元素的值结合
`f`初始值`init`是元素存在之前的起始值
已处理。

`ByteArray.foldlM`是此函数的一个元变量。
-/
def c132 := @ByteArray.foldl

/--
一个摩尼教左侧折叠`ByteArray`以便从低到高的指数排列起,
计算运行中的值。

数组的每个元素都与使用单子的先前元素的值结合
函数`f`初始值`init`是任何元素存在之前的起始值
已处理。
-/
def c133 := @ByteArray.foldlM

/--
参考执行情况`ForIn.forIn`(单位:千美元)`ByteArray`.

在编译的代码中,它被效率更高的替换`ByteArray.forInUnsafe`.
-/
def c134 := @ByteArray.forIn

/--
在数组开头创建一个延展器。
-/
def c135 := @ByteArray.iter

/--
以字节标出( I)`UInt8`页:1`ByteArray`.

通常由`arr.iter`时,`arr`是一个`ByteArray`.

迭代器是* 有效的 * 如果位置`i`是数组的 * 验证 *`arr`,含义`0 ≤ i ≤ arr.size`

如果迭代器无效, 大多数操作都会返回任意值 。 职能
联合国`ByteArray.Iterator`API应排除创建无效的传动器,但两个例外:

- `Iterator.next iter`如果`iter`已经位于数组的末尾(`iter.atEnd`这是
  `true`)
- `Iterator.forward iter n`/`Iterator.nextn iter n`如果`n`绝对大于
剩余字节数。
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
现位.

此位置不一定对数组有效, 例如如果有人继续拨打
`Iterator.next`何时`Iterator.atEnd`没错 如果职位无效,则
当前字节是`(default : UInt8)`.
-/
def c137 := @ByteArray.Iterator.pos

/--
如果移位符超过数组的最后一个字节, 则为真 。
-/
def c138 := @ByteArray.Iterator.atEnd

/--
如果迭代器是有效的, 那么它不会超过数组的最后一个字节 。
-/
def c139 := @ByteArray.Iterator.hasNext

/--
如果位置不是零, 则为真 。
-/
def c140 := @ByteArray.Iterator.hasPrev

/--
当前位置的字节 。

在无效位置上返回`(default : UInt8)`.
-/
def c141 := @ByteArray.Iterator.curr

/--
目前位置的字节。
-/
def c142 := @ByteArray.Iterator.curr'

/--
无条件将迭代器的位置向前移动一个字节。

只有当执行器不在数组的末端时,** 即** 才称此函数有效。
`Iterator.atEnd`这是`false`;否则,结果的延展器将无效。
-/
def c143 := @ByteArray.Iterator.next

/--
将迭代器的位置向前移动一个字节。 -
-/
def c144 := @ByteArray.Iterator.next'

/--
向前移动 。

生成的延时符仅在要跳过的字节数小于或等于
的字节数。
-/
def c145 := @ByteArray.Iterator.forward

/--
向前移动 。

生成的延时符仅在要跳过的字节数小于或等于
的字节数。
-/
def c146 := @ByteArray.Iterator.nextn

/--
减少迭代器的位置。

如果位置为零,则此函数为身份.
-/
def c147 := @ByteArray.Iterator.prev

/--
将执行器的位置移回数字节。

如果请求返回比可用的更多字节,则在数组开始时停止.
-/
def c148 := @ByteArray.Iterator.prevn

/--
执行器中留下的字节数 。
-/
def c149 := @ByteArray.Iterator.remainingBytes

/--
将迭代器的位置移到数组的末尾。

鉴于`i : ByteArray.Iterator`,注意`i.toEnd.atEnd`总是`true`.
-/
def c150 := @ByteArray.Iterator.toEnd

/--
返回一个字节数组的字节切片,带有给定的界限。

若为`start`或`stop`不是一个字节切片的有效界限,然后它们被夹在字节数组的大小上。
此外,起始指数被夹在结尾指数上.
-/
def c151 := @ByteArray.toByteSlice

/--
包含一些基本字节数组的区域 。

字节切片包含一个字节数组以及一个感兴趣的区域的起始和结束指数。
字节切片可以用来避免复制或分配空间,同时更方便于
用手追踪边界 兴趣所在区域由每个指数组成,两者都更大
等于或等于`start`绝对小于`stop`.
-/
def c152 := @ByteSlice

/--
比较函数
-/
def c153 := @ByteSlice.beq

/--
基础字节数组.
-/
def c154 := @ByteSlice.byteArray

/--
检查字节切片是否包含特定的字节值 。

返回`true`如果切片中的任何字节等于给定值,`false`否则。
-/
def c155 := @ByteSlice.contains

/--
空字节切片.

此空字节切片由空字节数组支持 。
-/
def c156 := @ByteSlice.empty

/--
在字节切片中将一个操作从右到左覆盖到字节.

类型累积器`β`以`init`并结合
字节切片,以当前累积器值依次移动,从尾移到起始.

实例:
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.foldr (·.toNat + ·) 0 = 6`
 * `(ByteArray.mk #[1, 2, 3]).toByteSlice.popFront.foldr (·.toNat + ·) 0 = 5`
-/
def c157 := @ByteSlice.foldr

/--
用字节切片从右到左移动到字节。

类型累积器`β`以`init`和道德结合
字节切片的字节,以当前累积值依次移动,从尾移到尾移
开始 有关寺院可允许提前终止或重复。

实例:
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
在一个字节切片的每个字节上运行一个单子动作.

字节从最低指数开始处理,向上移动.
-/
def c159 := @ByteSlice.forM

/--
从字节切片中提取一个字节。

指数相对于字节切片的起始,而不是基础字节数组.
-/
def c160 := @ByteSlice.get

/--
从字节切片中提取一个字节,或当索引超出界限时返回默认值。

该指数相对于字节切片的起始和结尾,而不是基础字节数组. 这个
默认值为 0。
-/
def c161 := @ByteSlice.get!

/--
从字节切片中提取一个字节,或返回默认值`v₀`当索引退出时
范围。

该指数相对于字节切片的起始和结尾,而不是基础字节数组.
-/
def c162 := @ByteSlice.getD

/--
创建一个字节阵列的新字节Slice
-/
def c163 := @ByteSlice.ofByteArray

/--
计算字节切片的大小。
-/
def c164 := @ByteSlice.size

/--
创建带有指定界限的字节切片的子切片。

若为`start`或`stop`对子切片无效,然后按切片大小夹住。
此外,起始指数被夹在结尾指数上.

指数是相对于当前切片,而不是基础字节数组.
-/
def c165 := @ByteSlice.slice

/--
利益区的起始指数(含).
-/
def c166 := @ByteSlice.start

/--
利益区域的结束指数(排他性)。
-/
def c167 := @ByteSlice.stop

/--
通过复制相关部分将一个字节切片返回到一个字节数组。
-/
def c168 := @ByteSlice.toByteArray

/--
查找第一个字节的索引`a`对其中`p`返回时`true`如果没有字节
输入`a`满意`p`,那么结果是`none`.

变体`findFinIdx?`附加返回找到的索引为边框的证明。
-/
def c169 := @ByteArray.findIdx?

/--
查找第一个字节的索引`a`对其中`p`返回时`true`如果没有字节
输入`a`满意`p`,那么结果是`none`.

返回索引的同时,还要证明它是数组中有效的索引。
-/
def c170 := @ByteArray.findFinIdx?

/--
忽略字大小的签名整数。 通常通过`-`前缀运算符。

这一功能在运行时随着高效的执行而过时。
-/
def c171 := @ISize.neg

/--
取消8位签名整数。 通常通过`-`前缀运算符。

这一功能在运行时随着高效的执行而过时。
-/
def c172 := @Int8.neg

/--
忽略16位签名整数 。 通常通过`-`前缀运算符。

这一功能在运行时随着高效的执行而过时。
-/
def c173 := @Int16.neg

/--
忽略32位签名整数 。 通常通过`-`前缀运算符。

这一功能在运行时随着高效的执行而过时。
-/
def c174 := @Int32.neg

/--
忽略64位签名整数 。 通常通过`-`前缀运算符。

这一功能在运行时随着高效的执行而过时。
-/
def c175 := @Int64.neg

/--
忽略单词大小的无符号整数,计算出的modulo`USize.size`.

这一功能在运行时随着高效的执行而过时。
-/
def c176 := @USize.neg

/--
忽略8位无符号整数, 计算modulo`UInt8.size`.

`UInt8.neg a`等同为`255 - a + 1`.

这一功能在运行时随着高效的执行而过时。
-/
def c177 := @UInt8.neg

/--
忽略 16 位无符号整数, 计算 modulo`UInt16.size`.

`UInt16.neg a`等同为`65_535 - a + 1`.

这一功能在运行时随着高效的执行而过时。
-/
def c178 := @UInt16.neg

/--
忽略32位无符号整数,计算出modulo`UInt32.size`.

`UInt32.neg a`等同为`429_4967_295 - a + 1`.

这一功能在运行时随着高效的执行而过时。
-/
def c179 := @UInt32.neg

/--
忽略64位无符号整数, 计算模组`UInt64.size`.

`UInt64.neg a`等同为`18_446_744_073_709_551_615 - a + 1`.

这一功能在运行时随着高效的执行而过时。
-/
def c180 := @UInt64.neg

/--
添加两个单词大小的无符号整数,在溢出时包裹。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c181 := @USize.add

/--
添加两个字大小的签名整数, 绕过或下流。 通常通过
联合国`+`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c182 := @ISize.add

/--
添加两个8位无符号整数,在溢出时绕行。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c183 := @UInt8.add

/--
添加两个 8 位签名整数, 绕过或下流 。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c184 := @Int8.add

/--
添加两个16位无符号整数,在溢出时包裹。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c185 := @UInt16.add

/--
添加两个 16 位签名整数, 绕过或下流 。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c186 := @Int16.add

/--
添加两个32位无符号整数,在溢出时包裹。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c187 := @UInt32.add

/--
添加两个32位签名整数,在过度或下流上绕行。 通常通过
`+`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c188 := @Int32.add

/--
添加两个64位无符号整数,在溢出时包裹。 通常通过`+`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c189 := @UInt64.add

/--
添加两个64位签名整数, 绕过或下流。 通常通过
`+`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c190 := @Int64.add

/--
将一个字位大小的无符号整数从另一个字位中减掉,在下流上包裹. 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c191 := @USize.sub

/--
将一个字大小的签名整数从另一个字数中减去,然后在流量过多或不足时绕过。 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c192 := @ISize.sub

/--
将一个8位的无符号整数从另一个减掉,在下流上包裹。 通常访问
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c193 := @UInt8.sub

/--
将一个8位签名整数从另一个中减掉,在过度或下流上包裹。 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c194 := @Int8.sub

/--
将一个16位的无符号整数从另一个减掉,然后在下流上包裹。 通常访问
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c195 := @UInt16.sub

/--
将一个 16 位签名整数从另一个减掉, 绕过或下流。 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c196 := @Int16.sub

/--
将一个32位无符号的整数从另一个整数中减掉,在下流上包裹。 通常访问
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c197 := @UInt32.sub

/--
将一个32位签名的整数从另一个中减掉,在过度或下流上包裹。 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c198 := @Int32.sub

/--
将一个64位的无符号整数从另一个减掉,在下流上包裹。 通常访问
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c199 := @UInt64.sub

/--
将一个64位签名整数从另一个中减去,在流量过多或不足时绕行。 通常情况下
通过`-`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c200 := @Int64.sub

/--
乘以两个单词大小的无符号整数,在溢出时包裹. 通常通过
`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c201 := @USize.mul

/--
乘以两个字大小的签名整数,在流量过大或不足时包裹. 通常访问
通过`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c202 := @ISize.mul

/--
乘以两个8位无符号整数,在溢出时包裹. 通常通过`*`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c203 := @UInt8.mul

/--
乘以两个8位签名整数,在过度或下流上包裹. 通常通过
联合国`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c204 := @Int8.mul

/--
乘以两个16位无符号整数,在溢出时包裹. 通常通过`*`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c205 := @UInt16.mul

/--
乘以两个16位签名整数,在过度或下流上包裹. 通常通过
联合国`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c206 := @Int16.mul

/--
乘以两个32位无符号整数,在溢出时包裹. 通常通过`*`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c207 := @UInt32.mul

/--
乘以两个32位的签名整数,在过度或不足流量上环绕. 通常通过
联合国`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c208 := @Int32.mul

/--
乘以两个64位无符号整数,在溢出时包裹. 通常通过`*`
操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c209 := @UInt64.mul

/--
乘以两个64位的签名整数,在过度或下流上包裹. 通常通过
联合国`*`操作员。

这一功能在运行时随着高效的执行而过时。
-/
def c210 := @Int64.mul

/--
未签名的字形无符号整数的除法,丢弃其余的. 通常访问
通过`/`操作员。

这一行动有时被称为“地面分区”。 由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。
-/
def c211 := @USize.div

/--
字型签名整数的截断除法,四舍五入为零。 通常通过
`/`操作员。

由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。

实例:
* `ISize.div 10 3 = 3`
* `ISize.div 10 (-3) = (-3)`
* `ISize.div (-10) (-3) = 3`
* `ISize.div (-10) 3 = (-3)`
* `ISize.div 10 0 = 0`
-/
def c212 := @ISize.div

/--
8位无符号整数的无符号除法,丢弃其余的. 通常访问
通过`/`操作员。

这一行动有时被称为“地面分区”。 由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。
-/
def c213 := @UInt8.div

/--
8位签名整数的截断除法,四舍五入为零。 通常通过`/`
操作员。

由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。

实例:
* `Int8.div 10 3 = 3`
* `Int8.div 10 (-3) = (-3)`
* `Int8.div (-10) (-3) = 3`
* `Int8.div (-10) 3 = (-3)`
* `Int8.div 10 0 = 0`
-/
def c214 := @Int8.div

/--
16位无符号整数的未签名除法,丢弃其余的. 通常访问
通过`/`操作员。

这一行动有时被称为“地面分区”。 由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。
-/
def c215 := @UInt16.div

/--
十六位签名整数的截断除法,四舍五入为零。 通常通过`/`
操作员。

由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。

实例:
* `Int16.div 10 3 = 3`
* `Int16.div 10 (-3) = (-3)`
* `Int16.div (-10) (-3) = 3`
* `Int16.div (-10) 3 = (-3)`
* `Int16.div 10 0 = 0`
-/
def c216 := @Int16.div

/--
对32位无符号整数进行无符号除法,丢弃其余的. 通常访问
通过`/`操作员。

这一行动有时被称为“地面分区”。 由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。
-/
def c217 := @UInt32.div

/--
32位签名整数的截断除法,四舍五入为零。 通常通过`/`
操作员。

由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。

实例:
* `Int32.div 10 3 = 3`
* `Int32.div 10 (-3) = (-3)`
* `Int32.div (-10) (-3) = 3`
* `Int32.div (-10) 3 = (-3)`
* `Int32.div 10 0 = 0`
-/
def c218 := @Int32.div

/--
未签名的64位无符号整数除法,丢弃其余的. 通常访问
通过`/`操作员。

这一行动有时被称为“地面分区”。 由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。
-/
def c219 := @UInt64.div

/--
64位签名整数的截断除法,四舍五入为零。 通常通过`/`
操作员。

由零除法被定义为零.

这一功能在运行时随着高效的执行而过时。

实例:
* `Int64.div 10 3 = 3`
* `Int64.div 10 (-3) = (-3)`
* `Int64.div (-10) (-3) = 3`
* `Int64.div (-10) 3 = (-3)`
* `Int64.div 10 0 = 0`
-/
def c220 := @Int64.div

/--
单词大小无符号整数的modulo运算符,在除去一个时计算剩余数
由另一个整数。 通常通过`%`操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
* `USize.mod 5 2 = 1`
* `USize.mod 4 2 = 0`
* `USize.mod 4 0 = 4`
-/
def c221 := @USize.mod

/--
单词大小签名整数的 modulo 运算符,在除去一个时计算剩余数
以 T 四舍五入的常规进行整数`ISize.div`。通常通过`%`
操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
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
8 位无符号整数的 modulo 运算符, 在除一个时计算剩余数
由另一个整数。 通常通过`%`操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
* `UInt8.mod 5 2 = 1`
* `UInt8.mod 4 2 = 0`
* `UInt8.mod 4 0 = 4`
-/
def c223 := @UInt8.mod

/--
8 位签名整数的 modulo 运算符, 在除一个时计算剩余数
以 T 四舍五入的常规进行整数`Int8.div`。通常通过`%`
操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
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
16 位无符号整数的 modulo 运算符,在除去一个时计算剩余数
由另一个整数。 通常通过`%`操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
* `UInt16.mod 5 2 = 1`
* `UInt16.mod 4 2 = 0`
* `UInt16.mod 4 0 = 4`
-/
def c225 := @UInt16.mod

/--
16 位签名整数的 modulo 运算符,在除去一个时计算剩余数
以 T 四舍五入的常规进行整数`Int16.div`。通常通过`%`
操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
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
32 位无符号整数的 modulo 运算符, 在除一个时计算剩余数
由另一个整数。 通常通过`%`操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
* `UInt32.mod 5 2 = 1`
* `UInt32.mod 4 2 = 0`
* `UInt32.mod 4 0 = 4`
-/
def c227 := @UInt32.mod

/--
32 位签名整数的 modulo 运算符, 在除一个时计算剩余数
以 T 四舍五入的常规进行整数`Int32.div`。通常通过`%`
操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
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
64 位无符号整数的 modulo 运算符,在除去一个时计算剩余数
由另一个整数。 通常通过`%`操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
* `UInt64.mod 5 2 = 1`
* `UInt64.mod 4 2 = 0`
* `UInt64.mod 4 0 = 4`
-/
def c229 := @UInt64.mod

/--
64 位签名整数的 modulo 运算符, 在除一个时计算剩余数
以 T 四舍五入的常规进行整数`Int64.div`。通常通过`%`
操作员。

当分辨器是`0`,结果是红利而不是错误。

这一功能在运行时随着高效的执行而过时。

实例:
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
词形大小无符号整数的基二对数. 返回`⌊max 0 (log₂ a)⌋`.

这一功能在运行时随着高效的执行而过时。 这个定义是
逻辑模型。

实例:
 * `USize.log2 0 = 0`
 * `USize.log2 1 = 0`
 * `USize.log2 2 = 1`
 * `USize.log2 4 = 2`
 * `USize.log2 7 = 2`
 * `USize.log2 8 = 3`
-/
def c231 := @USize.log2

/--
8位无符号整数的基二对数. 返回`⌊max 0 (log₂ a)⌋`.

这一功能在运行时随着高效的执行而过时。 这个定义是
逻辑模型。

实例:
 * `UInt8.log2 0 = 0`
 * `UInt8.log2 1 = 0`
 * `UInt8.log2 2 = 1`
 * `UInt8.log2 4 = 2`
 * `UInt8.log2 7 = 2`
 * `UInt8.log2 8 = 3`
-/
def c232 := @UInt8.log2

/--
16位无符号整数的基二对数. 返回`⌊max 0 (log₂ a)⌋`.

这一功能在运行时随着高效的执行而过时。 这个定义是
逻辑模型。

实例:
 * `UInt16.log2 0 = 0`
 * `UInt16.log2 1 = 0`
 * `UInt16.log2 2 = 1`
 * `UInt16.log2 4 = 2`
 * `UInt16.log2 7 = 2`
 * `UInt16.log2 8 = 3`
-/
def c233 := @UInt16.log2

/--
基二对数32位无符号整数. 返回`⌊max 0 (log₂ a)⌋`.

这一功能在运行时随着高效的执行而过时。 这个定义是
逻辑模型。

实例:
 * `UInt32.log2 0 = 0`
 * `UInt32.log2 1 = 0`
 * `UInt32.log2 2 = 1`
 * `UInt32.log2 4 = 2`
 * `UInt32.log2 7 = 2`
 * `UInt32.log2 8 = 3`
-/
def c234 := @UInt32.log2

/--
基二对数64位无符号整数. 返回`⌊max 0 (log₂ a)⌋`.

这一功能在运行时随着高效的执行而过时。 这个定义是
逻辑模型。

实例:
 * `UInt64.log2 0 = 0`
 * `UInt64.log2 1 = 0`
 * `UInt64.log2 2 = 1`
 * `UInt64.log2 4 = 2`
 * `UInt64.log2 7 = 2`
 * `UInt64.log2 8 = 3`
-/
def c235 := @UInt64.log2

/--
计算单词大小签名整数的绝对值。

此函数相当于`if a < 0 then -a else a`,特别是,`ISize.minValue`将会是
映射到`ISize.minValue`.

这一功能在运行时随着高效的执行而过时。
-/
def c236 := @ISize.abs

/--
计算一个8位签名整数的绝对值。

此函数相当于`if a < 0 then -a else a`,特别是,`Int8.minValue`将会是
映射到`Int8.minValue`.

这一功能在运行时随着高效的执行而过时。
-/
def c237 := @Int8.abs

/--
计算16位签名整数的绝对值。

此函数相当于`if a < 0 then -a else a`,特别是,`Int16.minValue`将会是
映射到`Int16.minValue`.

这一功能在运行时随着高效的执行而过时。
-/
def c238 := @Int16.abs

/--
计算一个32位签名整数的绝对值。

此函数相当于`if a < 0 then -a else a`,特别是,`Int32.minValue`将会是
映射到`Int32.minValue`.

这一功能在运行时随着高效的执行而过时。
-/
def c239 := @Int32.abs

/--
计算64位签名整数的绝对值。

此函数相当于`if a < 0 then -a else a`,特别是,`Int64.minValue`将会是
映射到`Int64.minValue`.

这一功能在运行时随着高效的执行而过时。
-/
def c240 := @Int64.abs

/--
检查两个列表的长度是否相同, 其元素是否对齐`BEq`。通常使用
通过`==`操作员。
-/
def c241 := @List.beq

/--
返回`true`若为`as`和`bs`长度相同, 且彼此相对`eqv`.

`O(min |as| |bs|)`。在第一对无关元件上的短路。

实例:
* `[1, 2, 3].isEqv [2, 3, 4] (· < ·) = true`
* `[1, 2, 3].isEqv [2, 2, 4] (· < ·) = false`
* `[1, 2, 3].isEqv [2, 3] (· < ·) = false`
-/
def c242 := @List.isEqv

/--
返回`true`若为`l₁`和`l₂`是彼此的表层。`O(|l₁| * |l₂|)`.

关系`List.Perm`是一种对表层的逻辑定性。 当`BEq α`实例
对应于`DecidableEq α`, `isPerm l₁ l₂ ↔ l₁ ~ l₂`(使用定理)`isPerm_iff`).
-/
def c243 := @List.isPerm

/--
检查第一个列表是否是第二个列表的前缀 。

关系`List.IsPrefixOf`在逻辑平等方面表达这种财产。

实例:
* `[1, 2].isPrefixOf [1, 2, 3] = true`
* `[1, 2].isPrefixOf [1, 2] = true`
* `[1, 2].isPrefixOf [1] = false`
* `[1, 2].isPrefixOf [1, 1, 2, 3] = false`
-/
def c244 := @List.isPrefixOf

/--
如果第一个列表是第二个列表的前缀,则返回放弃前缀的结果.

也就是说,`isPrefixOf? l₁ l₂`返回时`some t`何时`l₂ == l₁ ++ t`.

实例:
* `[1, 2].isPrefixOf? [1, 2, 3] = some [3]`
* `[1, 2].isPrefixOf? [1, 2] = some []`
* `[1, 2].isPrefixOf? [1] = none`
* `[1, 2].isPrefixOf? [1, 1, 2, 3] = none`
-/
def c245 := @List.isPrefixOf?

/--
如果第一个列表是第二个列表中潜在的非毗连的子序列,那么比较
含有`==`操作员。

关系`List.Sublist`是此属性的逻辑特性。

实例:
* `[1, 3].isSublist [0, 1, 2, 3, 4] = true`
* `[1, 3].isSublist [0, 1, 2, 4] = false`
-/
def c246 := @List.isSublist

/--
检查第一个列表是否是第二个列表的后缀 。

关系`List.IsSuffixOf`在逻辑平等方面表达这种财产。

实例:
* `[2, 3].isSuffixOf [1, 2, 3] = true`
* `[2, 3].isSuffixOf [1, 2, 3, 4] = false`
* `[2, 3].isSuffixOf [1, 2] = false`
* `[2, 3].isSuffixOf [1, 1, 2, 3] = true`
-/
def c247 := @List.isSuffixOf

/--
如果第一个列表是第二个列表的后缀,则返回从
接下来

也就是说,`isSuffixOf? l₁ l₂`返回时`some t`何时`l₂ == t ++ l₁`.

实例:
 * `[2, 3].isSuffixOf? [1, 2, 3] = some [1]`
 * `[2, 3].isSuffixOf? [1, 2, 3, 4] = none`
 * `[2, 3].isSuffixOf? [1, 2] = none`
 * `[2, 3].isSuffixOf? [1, 1, 2, 3] = some [1, 1]`
-/
def c248 := @List.isSuffixOf?

/--
在严格订购其要素方面不严格订购清单。

`as ≤ bs`若为`¬ bs < as`.

这种关系可作为一个词典顺序处理,如果其基础是:`LT α`实例
行为良好。 特别是,它应该具有不可伸缩性,不对称性,反对称性. 这些
所需经费的准确表述载于`List.cons_le_cons_iff`。如果这些持有,那么`as ≤ bs`若为
并且只有在:
 * `as`为空,或
 * 两者`as`和`bs`是非空的,和头部`as`小于头部`bs`,或
 * 两者`as`和`bs`他们的头是相等的,尾巴是`as`小于或小于
等于尾部为`bs`.
-/
def c249 := @List.le

/--
清单的排列顺序与清单内容的排列顺序。

`as < bs`若为
* `as`是空的, 并且`bs`不为空,或
* 两者`as`和`bs`是非空的,和头部`as`小于头部`bs`,或
* 两者`as`和`bs`他们的头是相等的,尾巴是`as`低于
尾端为`bs`.
-/
def c250 := @List.lt

/--
比较其要素的词汇表。

词汇顺序:`lt`为:
* `[].lex (b :: bs)`这是`true`
* `as.lex [] = false`这是`false`
* `(a :: as).lex (b :: bs)`如果`lt a b`或`a == b`和`lex lt as bs`没错
-/
def c251 := @List.lex

end Manual.ZhDocString.Ch19Ch20.G6
