namespace ZhDoc

/-
/--
`SizeOf` is a typeclass automatically derived for every inductive type,
which equips the type with a "size" function to `Nat`.
The default instance defines each constructor to be `1` plus the sum of the
sizes of all the constructor fields.

This is used for proofs by well-founded induction, since every field of the
constructor has a smaller size than the constructor itself,
and in many cases this will suffice to do the proof that a recursive function
is only called on smaller values.
If the default proof strategy fails, it is recommended to supply a custom
size measure using the `termination_by` argument on the function definition.
-/
class SizeOf (α : Sort u) where
  /-- The "size" of an element, a natural number which decreases on fields of
  each inductive type. -/
  sizeOf : α → Nat
-/

/--
`SizeOf` 是每一个归纳类型都会自动派生的类型类，
它为该类型提供了一个到 `Nat` 的 “大小” 函数。
默认实例会为每个构造子定义其 “大小” 等于 `1` 加上该构造子所有字段的“大小”之和。

这个机制通常用于良构（well-founded）证明，因为构造子的每个字段的“大小”都比整体构造子本身小，
在许多情况下这就足以证明递归函数只会作用于更小的值。
如果默认的证明策略失败，通常建议在函数定义时通过 `termination_by` 参数自定义一个大小度量。
-/
class SizeOf (α : Sort u) where
  /-- 一个元素的“大小”，是一个自然数，在每个归纳类型的字段上会递减。 -/
  sizeOf : α → Nat


/-
Default value: true

by default the inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters.
Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into Prop.
In the Init package, we define subsingletons, and we use this option to disable the check.
This option may be deleted in the future after we improve the validator
-/

/--
默认情况下，如果归纳类型/结构体命令生成的宇宙不是零（universe level 0），即使对某些宇宙参数来说有可能是零，也会报告错误。
原因：除非这个类型是子单元（subsingleton），否则这几乎不是用户想要的，因为它只能消去到 Prop（命题）。
在 Init 前导库包中，我们定义了子单元，并通过此选项关闭该检查。
在将来改进验证器之后，此选项可能会被删除。
-/
def Option.bootstrap.inductiveCheckResultingUniverse := Prop

end ZhDoc
