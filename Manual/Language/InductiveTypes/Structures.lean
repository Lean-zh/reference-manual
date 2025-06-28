/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option guard_msgs.diff true

/-
#doc (Manual) "Structure Declarations" =>
%%%
tag := "structures"
%%%
-/

#doc (Manual) "结构体声明" =>
%%%
file := "Structure Declarations"
tag := "structures"
%%%


/-
:::syntax command (title := "Structure Declarations")
```grammar
$_:declModifiers
structure $d:declId $_:bracketedBinder* $[: $_]?
  $[extends $[$[$_ : ]?$_],*]?
  where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$_],*]?
```

Declares a new structure type.
:::
-/

:::syntax command (title := "结构体声明")
```grammar
$_:declModifiers
structure $d:declId $_:bracketedBinder* $[: $_]?
  $[extends $[$[$_ : ]?$_],*]?
  where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$_],*]?
```

声明一个新的结构体类型。
:::

/-
{deftech}[Structures] are inductive types that have only a single constructor and no indices.
In exchange for these restrictions, Lean generates code for structures that offers a number of conveniences: projection functions are generated for each field, an additional constructor syntax based on field names rather than positional arguments is available, a similar syntax may be used to replace the values of certain named fields, and structures may extend other structures.
Just like other inductive types, structures may be recursive; they are subject to the same restrictions regarding strict positivity.
Structures do not add any expressive power to Lean; all of their features are implemented in terms of code generation.
-/

{deftech key := "Structures"}_结构体_ 是只有一个构造子、无下标的归纳类型。
作为这些约束的交换，Lean 会为结构体自动生成一些便捷功能：为每个字段生成投影函数、允许基于字段名（而非位置参数）的新构造语法、同样可以按指定字段名修改值，并且结构体可以扩展其它结构体。
结构体和其它归纳类型一样，可以递归定义；它们必须遵守严格正性限制。
结构体本身并没有带来 Lean 表达力的增强；它们的所有特性都是通过代码生成机制实现的。

/-
```lean (show := false)
-- Test claim about recursive above

/--
error: (kernel) arg #1 of 'RecStruct.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
structure RecStruct where
  next : RecStruct → RecStruct

```
-/

```lean (show := false)
-- 测试上面关于递归的断言

/--
error: (kernel) arg #1 of 'RecStruct.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
structure RecStruct where
  next : RecStruct → RecStruct

```

/-
# Structure Parameters
%%%
tag := "structure-params"
%%%
-/

# 结构体参数
%%%
file := "Structure Parameters"
tag := "structure-params"
%%%

/-
Just like ordinary inductive type declarations, the header of the structure declaration contains a signature that may specify both parameters and a resulting universe.
Structures may not define {tech}[indexed families].
-/

与普通归纳类型声明相同，结构体声明的头部可以包含参数和结果宇宙层级。
结构体不能定义 {tech key := "indexed families"}[索引族]。

/-
# Fields
%%%
tag := "structure-fields"
%%%
-/

# 字段
%%%
file := "Fields"
tag := "structure-fields"
%%%

/-
Each field of a structure declaration corresponds to a parameter of the constructor.
Auto-implicit arguments are inserted in each field separately, even if their names coincide, and the fields become constructor parameters that quantify over types.
-/

结构体声明的每个字段，都对应构造子的一个参数。
每个字段中都会独立插入自动隐式参数,即使名称相同，且这些字段会成为构造子的参数以量化类型。

/-
:::: example "Auto-implicit parameters in structure fields"

The structure {lean}`MyStructure` contains a field whose type is an auto-implicit parameter:

```lean
structure MyStructure where
  field1 : α
  field2 : α
```
The type constructor {name}`MyStructure` takes two universe parameters:
```signature
MyStructure.{u, v} : Type (max u v)
```
The resulting type is in `Type` rather than `Sort` because the constructor fields quantify over types in `Sort`. In particular, both fields in its constructor {name}`MyStructure.mk` take an implicit type parameter:
```signature
MyStructure.mk.{u, v}
  (field1 : {α : Sort u} → α)
  (field2 : {α : Sort v} → α)
  : MyStructure.{u,v}
```

::::
-/

:::: example "结构体字段中的自动隐式参数"

结构体 {lean}`MyStructure` 包含一个字段，其类型是自动隐式参数：

```lean
structure MyStructure where
  field1 : α
  field2 : α
```
类型构造子 {name}`MyStructure` 需要两个宇宙参数：
```signature
MyStructure.{u, v} : Type (max u v)
```

由于构造子字段量化于 `Sort` 中的类型，因此其结果类型是 `Type`，而非 `Sort`。具体来说，构造子 {name}`MyStructure.mk` 的两个字段都带有隐式类型参数：
```signature
MyStructure.mk.{u, v}
  (field1 : {α : Sort u} → α)
  (field2 : {α : Sort v} → α)
  : MyStructure.{u,v}
```

::::

/-
For each field, a {deftech}[projection function] is generated that extracts the field's value from the underlying type's constructor.
This function is in the structure's name's namespace.
Structure field projections are handled specially by the elaborator (as described in the {ref "structure-inheritance"}[section on structure inheritance]), which performs extra steps beyond looking up a namespace.
When field types depend on prior fields, the types of the dependent projection functions are written in terms of earlier projections, rather than explicit pattern matching.
-/

对于每个字段，都会自动生成一个 {deftech key := "projection function"}_投影函数_，用于从构造子中提取字段的值。
这个函数在结构体名称对应的命名空间中。
结构体字段投影由繁释器特别处理（具体见 {ref "structure-inheritance"}[结构体继承]），其行为比仅查找命名空间要复杂。
当字段类型依赖于之前字段时，依赖型投影函数的类型会使用之前的投影表达，而不是显式模式匹配。

/-
:::: example "Dependent projection types"

The structure {lean}`ArraySized` contains a field whose type depends on both a structure parameter and an earlier field:
```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```

The signature of the projection function {name ArraySized.size_eq_length}`size_eq_length` takes the structure type's parameter as an implicit parameter and refers to the earlier field using the corresponding projection:
```signature
ArraySized.size_eq_length.{u}
  {α : Type u} {length : Nat}
  (self : ArraySized α length)
  : self.array.size = length
```

::::
-/

:::: example "依赖型投影类型"

结构体 {lean}`ArraySized` 包含一个字段，其类型依赖于结构体参数和先前字段：
```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```

投影函数 {name ArraySized.size_eq_length}`size_eq_length` 的签名中，会隐式带入结构体类型的参数，通过先前的投影引用之前的字段：
```signature
ArraySized.size_eq_length.{u}
  {α : Type u} {length : Nat}
  (self : ArraySized α length)
  : self.array.size = length
```

::::

/-
Structure fields may have default values, specified with `:=`.
These values are used if no explicit value is provided.
-/

结构体字段可以通过 `:=` 指定默认值。
如果没有提供该字段的显式值，则使用默认值。

/-
::: example "Default values"

An adjacency list representation of a graph can be represented as an array of lists of {lean}`Nat`.
The size of the array indicates the number of vertices, and the outgoing edges from each vertex are stored in the array at the vertex's index.
Because the default value {lean}`#[]` is provided for the field {name Graph.adjacency}`adjacency`, the empty graph {lean}`Graph.empty` can be constructed without providing any field values.
```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
:::
-/

::: example "默认值"

图的邻接表可用一个 {lean}`Nat` 列表的数组表示。
数组大小代表顶点数，数组中每个元素（通过顶点下标访问）存储对应顶点的出边。
由于 {name Graph.adjacency}`adjacency` 字段提供了默认值 {lean}`#[]`，空图 {lean}`Graph.empty` 在构造时无需提供字段值。
```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
:::

/-
Structure fields may additionally be accessed via their index, using dot notation.
Fields are numbered beginning with `1`.
-/

结构体字段还可以通过索引以点号访问。
字段编号从 `1` 开始。

/-
# Structure Constructors
%%%
tag := "structure-constructors"
%%%
-/

# 结构体构造子
%%%
file := "Structure Constructors"
tag := "structure-constructors"
%%%

/-
Structure constructors may be explicitly named by providing the constructor name and `::` prior to the fields.
If no name is explicitly provided, then the constructor is named `mk` in the structure type's namespace.
{ref "declaration-modifiers"}[Declaration modifiers] may additionally be provided along with an explicit constructor name.
-/

结构体构造子可以通过在字段前加构造子名称与 `::` 显式命名。
若未显式指定名称，则构造子在结构体命名空间中名为 `mk`。
{ref "declaration-modifiers"}[声明修饰符] 也可被用于显式构造子名称前。

/-
::: example "Non-default constructor name"
The structure  {lean}`Palindrome` contains a string and a proof that the string is the same when reversed:

```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```

Its constructor is named {name}`Palindrome.ofString`, rather than `Palindrome.mk`.

:::
-/

::: example "非默认构造子名称"
结构体 {lean}`Palindrome` 包含一个字符串以及显示该字符串反转与原字相等的证明：

```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```

其构造子为 {name}`Palindrome.ofString`，而非 `Palindrome.mk`。

:::

/-
::: example "Modifiers on structure constructor"
The structure {lean}`NatStringBimap` maintains a finite bijection between natural numbers and strings.
It consists of a pair of maps, such that the keys each occur as values exactly once in the other map.
Because the constructor is private, code outside the defining module can't construct new instances and must use the provided API, which maintains the invariants of the type.
Additionally, providing the default constructor name explicitly is an opportunity to attach a {tech}[documentation comment] to the constructor.

```lean
structure NatStringBimap where
  /--
  Build a finite bijection between some
  natural numbers and strings
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some (NatStringBimap.mk (map.natToString.insert nat string) (map.stringToNat.insert string nat))
```
:::
-/

::: example "结构体构造子的修饰符"
结构体 {lean}`NatStringBimap` 表示自然数与字符串之间的有限双射。
它由一对映射组成，每个映射的键在另一个映射的值中也仅出现一次。
由于构造子被声明为 private，定义模块之外的代码无法直接构造新实例，只能通过维护类型不变性的 API 构造。
同时，显式指定默认构造子名称时，可以给构造子加上 {tech key := "documentation comment"}[文档注释]。

```lean
structure NatStringBimap where
  /--
  在一些自然数和字符串之间构建一个有限双射
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some (NatStringBimap.mk (map.natToString.insert nat string) (map.stringToNat.insert string nat))
```
:::

/-
Because structures are represented by single-constructor inductive types, their constructors can be invoked or matched against using {tech}[anonymous constructor syntax].
Additionally, structures may be constructed or matched against using {deftech}_structure instance_ notation, which includes the names of the fields together with values for them.
-/

由于结构体本质上就是单构造子的归纳类型，其构造子既可以直接调用或用于{tech key := "anonymous constructor syntax"}[匿名构造子语法]下的模式匹配,
也可以用 {deftech key := "structure instance"}_结构体实例_ 记法（含有实字段名和值）进行构造或模式匹配。

/-
::::syntax term (title := "Structure Instances")

```grammar
{ $_,*
  $[: $ty:term]? }
```

Constructs a value of a constructor type given values for named fields.
Field specifiers may take two forms:
```grammar (of := Lean.Parser.Term.structInstField)
$x := $y
```

```grammar (of := Lean.Parser.Term.structInstField)
$f:ident
```

A {syntaxKind}`structInstLVal` is a field name (an identifier), a field index (a natural number), or a term in square brackets, followed by a sequence of zero or more subfields.
Subfields are either a field name or index preceded by a dot, or a term in square brackets.

This syntax is elaborated to applications of structure constructors.
The values provided for fields are by name, and they may be provided in any order.
The values provided for subfields are used to initialize fields of constructors of structures that are themselves found in fields.
Terms in square brackets are not allowed when constructing a structure; they are used in structure updates.

Field specifiers that do not contain `:=` are field abbreviations.
In this context, the identifier `f` is an abbreviation for `f := f`; that is, the value of `f` in the current scope is used to initialize the field `f`.

Every field that does not have a default value must be provided.
If a tactic is specified as the default argument, then it is run at elaboration time to construct the argument's value.

In a pattern context, field names are mapped to patterns that match the corresponding projection, and field abbreviations bind a pattern variable that is the field's name.
Default arguments are still present in patterns; if a pattern does not specify a value for a field with a default value, then the pattern only matches the default.

The optional type annotation allows the structure type to be specified in contexts where it is not otherwise determined.
::::
-/


::::syntax term (title := "结构体实例")

```grammar
{ $_,*
  $[: $ty:term]? }
```

指定字段名及其值来构造一个结构体类型的值。
字段说明可有两种形式：
```grammar (of := Lean.Parser.Term.structInstField)
$x := $y
```

```grammar (of := Lean.Parser.Term.structInstField)
$f:ident
```
{syntaxKind}`structInstLVal` 可以是字段名（标识符）、字段索引（自然数），或带中括号的项，并可接零个或多个子字段。
子字段可以是带点的字段名或索引，也可以是带中括号的项。

该语法在繁释时会转换为结构体构造子的应用。
字段以名称分配，顺序不限。
子字段赋值用于初始化嵌套在字段中的结构体的字段。
在构造结构体时不允许带中括号的项，中括号用于结构体更新。

不带 `:=` 的字段被认为是字段缩写。
此时，标识符 `f` 等价于 `f := f`，即作用域中的 `f` 会被用于字段赋值。

所有无默认值的字段，都需要明确提供。
如果默认参数指定为 tactic，那么在繁释阶段会运行 tactic 求得参数值。

在模式匹配语境下，字段名映射到能匹配相应投影的模式，字段缩写可直接绑定同名模式变量。
默认参数同样适用于模式；如果模式未指定带默认值字段的值，则模式只匹配默认值。

可选类型注解允许在类型无法直接唯一确定时明确指定结构体类型。
::::

/-
:::::keepEnv

::::example "Patterns and default values"
The structure {name}`AugmentedIntList` contains a list together with some extra information, which is empty if omitted:
```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```

When testing whether the list is empty, the function {name AugmentedIntList.isEmpty}`isEmpty` is also testing whether the {name AugmentedIntList.augmentation}`augmentation` field is empty, because the omitted field's default value is also used in pattern contexts:
```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
::::
:::::
-/

:::::keepEnv

::::example "模式与默认值"
结构体 {name}`AugmentedIntList` 包含一个整数列表及一些可选额外信息（默认为空字符串）：
```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```
在测试列表是否为空时，函数 {name AugmentedIntList.isEmpty}`isEmpty` 还会检测字段 {name AugmentedIntList.augmentation}`augmentation` 是否为空；因为忽略字段会采用默认值，模式匹配同样如此：

```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
::::
:::::

/-
:::syntax term (title := "Structure Updates")
```grammar
{$e:term with
  $_,*
  $[: $ty:term]?}
```
Updates a value of a constructor type.
The term that precedes the {keywordOf Lean.Parser.Term.structInst}`with` clause is expected to have a structure type; it is the value that is being updated.
A new instance of the structure is created in which every field not specified is copied from the value that is being updated, and the specified fields are replaced with their new values.
When updating a structure, array values may also be replaced by including the index to be updated in square brackets.
This updating does not require that the index expression be in bounds for the array, and out-of-bounds updates are discarded.
:::
-/

:::syntax term (title := "结构体更新")
```grammar
{$e:term with
  $_,*
  $[: $ty:term]?}
```
对构造子类型的值进行更新。
{keywordOf Lean.Parser.Term.structInst}`with` 子句之前的项应为结构体类型值，即待更新的原值。
新的结构体实例中，所有未指定的字段都从原始值拷贝，指定字段被覆盖为新值。
更新结构体时，也可以通过中括号带索引更新数组字段。
索引表达式不要求越界，越界更新会被忽略。
:::

/-
::::example "Updating arrays"
:::keepEnv
Updating structures may use array indices as well as projection names.
Updates at indices that are out of bounds are ignored:

```lean name:=arrayUpdate
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
:::
::::
-/

::::example "数组更新"
:::keepEnv
结构体更新可以用字段名，也可以用数组索引。
越界索引的更新会被直接忽略：

```lean name:=arrayUpdate
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
:::
::::

/-
Values of structure types may also be declared using {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where`, followed by definitions for each field.
This may only be used as part of a definition, not in an expression context.
-/

结构体类型的值也可以使用 {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where`，
在定义后为每个字段赋值，只能用于定义体，不能在通用表达式中用。

/-
::::example "`where` for structures"
:::keepEnv
The product type in Lean is a structure named {name}`Prod`.
Products can be defined using their projections:
```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
:::
::::
-/

::::example "结构体中的 `where`"
:::keepEnv
Lean 中的乘积类型是名为 {name}`Prod` 的结构体。
可以用字段投影方式来给乘积类型赋值：
```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
:::
::::

/-
# Structure Inheritance
%%%
tag := "structure-inheritance"
%%%
-/

# 结构体继承
%%%
file := "Structure Inheritance"
tag := "structure-inheritance"
%%%

/-
Structures may be declared as extending other structures using the optional {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` clause.
The resulting structure type has all of the fields of all of the parent structure types.
If the parent structure types have overlapping field names, then all overlapping field names must have the same type.
-/

结构体可以通过可选的 {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` 子句继承其它结构体。
结果结构体类型将包含所有父结构体的全部字段。
如果父结构体字段有重名，所有同名字段必须同类型。


继承结果结构体有一个 {deftech key := "field resolution order"}_字段解析顺序_，决定字段的最终取值。
一般来说，该顺序采用 [C3 线性化](https://en.wikipedia.org/wiki/C3_linearization)。
即字段解析顺序是所有父结构体列表的一个全序排列（保留 extends 语句顺序），如果无法形成 C3 线性化，则采用启发式算法排序。
结构体自身在解析顺序中最前。

字段解析顺序用于计算可选字段的默认值。
如未指定字段值，则使用解析顺序中第一个定义了默认的值。
默认值中若引用了其它字段，也采用字段解析顺序；这意味着子结构体如重写了父结构体的默认字段，也可影响父结构体的默认字段的计算结果。
由于子结构体自带最高优先级，因此子结构体中的默认值优先生效于父结构体。

/-
```lean (show := false) (keep := false)
-- If the overlapping fields have different default values, then the default value from the first
-- parent structure in the resolution order that includes the field is used.
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/--
info: structure Q'' : Type
number of parameters: 0
parents:
  Q''.toQ : Q
  Q''.toQ' : Q'
fields:
  Q.x : Nat :=
    0
constructor:
  Q''.mk (toQ : Q) : Q''
field notation resolution order:
  Q'', Q, Q'
-/
#guard_msgs in
#print Q''

/-- info: 0 -/
#guard_msgs in
#eval ({} : Q'').x

/--
info: structure Q''' : Type
number of parameters: 0
parents:
  Q'''.toQ' : Q'
  Q'''.toQ : Q
fields:
  Q'.x : Nat :=
    3
constructor:
  Q'''.mk (toQ' : Q') : Q'''
field notation resolution order:
  Q''', Q', Q
-/
#guard_msgs in
#print Q'''

/-- info: 3 -/
#guard_msgs in
#eval ({} : Q''').x

-- Defaults use local values
structure A where
  n : Nat := 0
deriving Repr
structure B extends A where
  k : Nat := n
deriving Repr
structure C extends A where
  n := 5
deriving Repr
structure C' extends A where
  n := 3
deriving Repr

structure D extends B, C, C'
deriving Repr
structure D' extends B, C', C
deriving Repr

#eval ({} : D).k

#eval ({} : D').k

```
-/

```lean (show := false) (keep := false)
-- 若同名字段默认值不同，使用解析顺序中第一个父结构体定义的默认
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/--
info: structure Q'' : Type
number of parameters: 0
parents:
  Q''.toQ : Q
  Q''.toQ' : Q'
fields:
  Q.x : Nat :=
    0
constructor:
  Q''.mk (toQ : Q) : Q''
field notation resolution order:
  Q'', Q, Q'
-/
#guard_msgs in
#print Q''

/-- info: 0 -/
#guard_msgs in
#eval ({} : Q'').x

/--
info: structure Q''' : Type
number of parameters: 0
parents:
  Q'''.toQ' : Q'
  Q'''.toQ : Q
fields:
  Q'.x : Nat :=
    3
constructor:
  Q'''.mk (toQ' : Q') : Q'''
field notation resolution order:
  Q''', Q', Q
-/
#guard_msgs in
#print Q'''

/-- info: 3 -/
#guard_msgs in
#eval ({} : Q''').x

-- 默认值使用本地值
structure A where
  n : Nat := 0
deriving Repr
structure B extends A where
  k : Nat := n
deriving Repr
structure C extends A where
  n := 5
deriving Repr
structure C' extends A where
  n := 3
deriving Repr

structure D extends B, C, C'
deriving Repr
structure D' extends B, C', C
deriving Repr

#eval ({} : D).k

#eval ({} : D').k

```

/-
When the new structure extends existing structures, the new structure's constructor takes the existing structure's information as additional arguments.
Typically, this is in the form of a constructor parameter for each parent structure type.
This parent value contains all of the parent's fields.
If the parents' fields overlap, however, then the subset of non-overlapping fields from one or more of the parents is included instead of an entire value of the parent structure to prevent duplicating field information.
-/

结构体继承其它结构体时，新结构体的构造子会接受父类型的信息作为附加参数。
通常每个父结构体会作为一个参数传递，其值包含父结构体的全部字段。
如果父结构体有重叠字段，则只保留不重叠的那部分，以避免字段重复。

/-
There is no subtyping relation between a parent structure type and its children.
Even if structure `B` extends structure `A`, a function expecting an `A` will not accept a `B`.
However, conversion functions are generated that convert a structure into each of its parents.
These conversion functions are called {deftech}_parent projections_.
Parent projections are in the child structure's namespace, and their name is the parent structure's name preceded by `to`.
-/
父类型与子类型之间没有子类型关系。
即使结构体 `B` 继承于 `A`，期望 `A` 的函数也不会接受 `B` 类型。
但系统会自动生成转换函数，将结构体转为各自的父结构体类型。
这些转换函数称为 {deftech key := "parent projections"}_父投影_。
父投影函数定义在子结构体的命名空间中，形式为父类型名加前缀 `to`。

/-
::: example "Structure type inheritance with overlapping fields"
In this example, a {lean}`Textbook` is a {lean}`Book` that is also an {lean}`AcademicWork`:

```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```

Because the field `author` occurs in both {lean}`Book` and {lean}`AcademicWork`, the constructor {name}`Textbook.mk` does not take both parents as arguments.
Its signature is:
```signature
Textbook.mk (toBook : Book) (discipline : String) : Textbook
```

The conversion functions are:
```signature
Textbook.toBook (self : Textbook) : Book
```
```signature
Textbook.toAcademicWork (self : Textbook) : AcademicWork
```

The latter combines the `author` field of the included {lean}`Book` with the unbundled `Discipline` field, and is equivalent to:
```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean (show := false)
-- check claim of equivalence
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```

:::
-/

::: example "结构体类型继承与字段重叠"
In this example, a {lean}`Textbook` is a {lean}`Book` that is also an {lean}`AcademicWork`:

```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```

因为 `author` 字段同时出现在 {lean}`Book` 与 {lean}`AcademicWork`，所以 {name}`Textbook.mk` 构造子只需传入一个父实例。
其签名为：
```signature
Textbook.mk (toBook : Book) (discipline : String) : Textbook
```

转换函数为：
```signature
Textbook.toBook (self : Textbook) : Book
```
```signature
Textbook.toAcademicWork (self : Textbook) : AcademicWork
```

后一函数会将包含的 {lean}`Book` 的 `author` 字段与独立的 `Discipline` 字段组合，等价于：
```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean (show := false)
-- 检验等价
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```

:::

/-
The resulting structure's projections can be used as if its fields are simply the union of the parents' fields.
The Lean elaborator automatically generates an appropriate projection when fields are used.
Likewise, the field-based initialization and structure update notations hide the details of the encoding of inheritance.
The encoding is, however, visible when using the constructor's name, when using {tech}[anonymous constructor syntax], or when referring to fields by their index rather than their name.
-/

最终结构体的投影用法上就像字段是所有父结构体字段的并集一样。
Lean 的繁释器会在使用字段时自动生成合适的投影。
同样，基于字段的初始化与结构体更新语法可以隐藏继承实现的细节。
但如果直接使用构造子名称、{tech key := "anonymous constructor syntax"}[匿名构造子语法]，或者按索引而非字段名称引用字段时，这些细节是可见的。

/-
:::: example "Field Indices and Structure Inheritance"

```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```

Evaluating the first field index of {name}`coords` yields the underlying {name}`Pair`, rather than the contents of the field `fst`:
```lean name:=coords1
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```

The elaborator translates {lean}`coords.fst` into {lean}`coords.toPair.fst`.

````lean (show := false) (keep := false)
example (t : Triple α) : t.fst = t.toPair.fst := rfl
````
::::
-/

:::: example "字段索引与结构体继承"

```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```

对 {name}`coords` 的第一字段索引求值时，得到的是 {name}`Pair`，而不是字段 `fst` 的值：
```lean name:=coords1
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```

繁释器会自动将 {lean}`coords.fst` 转换为 {lean}`coords.toPair.fst`。

````lean (show := false) (keep := false)
example (t : Triple α) : t.fst = t.toPair.fst := rfl
````
::::

/-
:::: example "No structure subtyping"
:::keepEnv
Given these definitions of even numbers, even prime numbers, and a concrete even prime:
```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
it is a type error to apply {name}`printEven` directly to {name}`two`:
```lean (error := true) (name := printTwo)
#check printEven two
```
```leanOutput printTwo
Application type mismatch: In the application
  printEven two
the argument
  two
has type
  EvenPrime : Type
but is expected to have type
  EvenNumber : Type
```
because values of type {name}`EvenPrime` are not also values of type {name}`EvenNumber`.
:::
::::
-/

:::: example "无结构体子类型关系"
:::keepEnv
如下定义偶数、偶质数和具体偶质数：
```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
直接将 {name}`printEven` 应用于 {name}`two` 会产生类型错误：
```lean (error := true) (name := printTwo)
#check printEven two
```
```leanOutput printTwo
Application type mismatch: In the application
  printEven two
the argument
  two
has type
  EvenPrime : Type
but is expected to have type
  EvenNumber : Type
```
因为 {name}`EvenPrime` 类型的值并非 {name}`EvenNumber` 类型值。
:::
::::


```lean (show := false) (keep := false)
structure A where
  x : Nat
  y : Int
structure A' where
  x : Int
structure B where
  foo : Nat
structure C extends A where
  z : String
/-- info: C.mk (toA : A) (z : String) : C -/
#guard_msgs in
#check C.mk

def someC : C where
  x := 1
  y := 2
  z := ""

/--
error: type mismatch
  someC
has type
  C : Type
but is expected to have type
  A : Type
-/
#guard_msgs in
#check (someC : A)

structure D extends A, B where
  z : String
/-- info: D.mk (toA : A) (toB : B) (z : String) : D -/
#guard_msgs in
#check D.mk
structure E extends A, B where
  x := 44
  z : String
/-- info: E.mk (toA : A) (toB : B) (z : String) : E -/
#guard_msgs in
#check E.mk
/--
error: field type mismatch, field 'x' from parent 'A'' has type
  Int : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
structure F extends A, A' where

```

/-
The {keywordOf Lean.Parser.Command.print}`#print` command displays the most important information about structure types, including the {tech}[parent projections], all the fields with their default values, the constructor, and the {tech}[field resolution order].
When working with deep hierarchies that contain inheritance diamonds, this information can be very useful.
-/

{keywordOf Lean.Parser.Command.print}`#print` 命令能展示所有结构体类型的重要信息，包括 {tech key := "parent projections"}[父投影]、所有字段（含默认值）、构造子及 {tech key := "field resolution order"}[字段解析顺序]。
对于包含复杂继承菱形的层次结构而言，这些信息非常有用。

/-
::: example "{keyword}`#print` and Structure Types"

This collection of structure types models a variety of bicycles, both electric and non-electric and both ordinary-sized and large family bicycles.
The final structure type, {lean}`ElectricFamilyBike`, contains a diamond in its inheritance graph, because both {lean}`FamilyBike` and {lean}`ElectricBike` extend {lean}`Bicycle`.

```lean
structure Vehicle where
  wheels : Nat

structure Bicycle extends Vehicle where
  wheels := 2

structure ElectricVehicle extends Vehicle where
  batteries : Nat := 1

structure FamilyBike extends Bicycle where
  wheels := 3

structure ElectricBike extends Bicycle, ElectricVehicle

structure ElectricFamilyBike
    extends FamilyBike, ElectricBike where
  batteries := 2
```

The {keywordOf Lean.Parser.Command.print}`#print` command displays the important information about each structure type:
```lean (name := el)
#print ElectricBike
```
```leanOutput el
structure ElectricBike : Type
number of parameters: 0
parents:
  ElectricBike.toBicycle : Bicycle
  ElectricBike.toElectricVehicle : ElectricVehicle
fields:
  Vehicle.wheels : Nat :=
    2
  ElectricVehicle.batteries : Nat :=
    1
constructor:
  ElectricBike.mk (toBicycle : Bicycle) (batteries : Nat) : ElectricBike
field notation resolution order:
  ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

An {lean}`ElectricFamilyBike` has three wheels by default because {lean}`FamilyBike` precedes {lean}`Bicycle` in its resolution order:
```lean  (name := elFam)
#print ElectricFamilyBike
```
```leanOutput elFam
structure ElectricFamilyBike : Type
number of parameters: 0
parents:
  ElectricFamilyBike.toFamilyBike : FamilyBike
  ElectricFamilyBike.toElectricBike : ElectricBike
fields:
  Vehicle.wheels : Nat :=
    3
  ElectricVehicle.batteries : Nat :=
    2
constructor:
  ElectricFamilyBike.mk (toFamilyBike : FamilyBike) (batteries : Nat) : ElectricFamilyBike
field notation resolution order:
  ElectricFamilyBike, FamilyBike, ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

:::
-/

::: example "{keyword}`#print` 与结构体类型"

以下是关于自行车的结构体抽象，涵盖电动/非电动、大型/普通家庭自行车。
最后一种结构体 {lean}`ElectricFamilyBike` 形成了继承图中的“菱形”，因为 {lean}`FamilyBike` 和 {lean}`ElectricBike` 都继承自 {lean}`Bicycle`。


```lean
structure Vehicle where
  wheels : Nat

structure Bicycle extends Vehicle where
  wheels := 2

structure ElectricVehicle extends Vehicle where
  batteries : Nat := 1

structure FamilyBike extends Bicycle where
  wheels := 3

structure ElectricBike extends Bicycle, ElectricVehicle

structure ElectricFamilyBike
    extends FamilyBike, ElectricBike where
  batteries := 2
```

{keywordOf Lean.Parser.Command.print}`#print` 可以显示各结构体类型的重要信息：
```lean (name := el)
#print ElectricBike
```
```leanOutput el
structure ElectricBike : Type
number of parameters: 0
parents:
  ElectricBike.toBicycle : Bicycle
  ElectricBike.toElectricVehicle : ElectricVehicle
fields:
  Vehicle.wheels : Nat :=
    2
  ElectricVehicle.batteries : Nat :=
    1
constructor:
  ElectricBike.mk (toBicycle : Bicycle) (batteries : Nat) : ElectricBike
field notation resolution order:
  ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

默认情况下，{lean}`ElectricFamilyBike` 有三轮，因为在解析顺序中 {lean}`FamilyBike` 优先于
```lean  (name := elFam)
#print ElectricFamilyBike
```
```leanOutput elFam
structure ElectricFamilyBike : Type
number of parameters: 0
parents:
  ElectricFamilyBike.toFamilyBike : FamilyBike
  ElectricFamilyBike.toElectricBike : ElectricBike
fields:
  Vehicle.wheels : Nat :=
    3
  ElectricVehicle.batteries : Nat :=
    2
constructor:
  ElectricFamilyBike.mk (toFamilyBike : FamilyBike) (batteries : Nat) : ElectricFamilyBike
field notation resolution order:
  ElectricFamilyBike, FamilyBike, ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

:::
