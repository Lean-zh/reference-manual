import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.RecursiveDefs.WF

/--
具有规范良基关系的类型。

实例用于证明以良基递归定义的函数会终止：递归调用必须使某个度量按照良基关系减小。
这个关系可以组合递归函数各形参上的良基关系。
-/
class WellFoundedRelation (α : Sort u) where
  /-- `α` 上的一个良基关系。 -/
  rel : α → α → Prop
  /-- `rel` 确实良基的证明。 -/
  wf : _root_.WellFounded rel

namespace Parser.Attr

/--
带有 `wf_preprocess` 属性的定理，会在处理以良基递归定义的函数时使用。它们会被应用于
函数体，以加入额外假设，例如把 `if c then _ else _` 替换为
`if h : c then _ else _`，或把 `xs.map` 替换为 `xs.attach.map`。另见 `wfParam`。

警告：这些重写只会为了构造逻辑定义而应用于声明，并不影响编译后的代码。尤其是，
如果重写删除无关子项，或把项隐藏在绑定变量之下而改变求值顺序，就可能使一个编译后
发散的函数在没有显式 `partial` 关键字时仍被接受。因此，除非定理同时保持运行时行为，
否则应避免给它添加 `[wf_preprocess]` 标记。
-/
def wf_preprocess : Unit := ()

end Parser.Attr

/--
`wfParam` 小工具在通过良基递归构造递归函数时供内部使用；它用于跟踪哪个形参适合由
系统自动引入 `List.attach`（或类似操作）。
-/
def wfParam : Unit := ()

namespace Option

/--
启用或禁用指定模块及其子模块的追踪。对 `trace.Elab.definition.wf` 而言，启用后会显示
良基递归精译过程的诊断信息。

默认值为 `false`。
-/
def traceElabDefinitionWf : Bool := false

end Option

namespace WellFounded

/--
良基不动点。若对某个值，假设所有按良基关系小于它的值都满足动机 `C`，便足以推出
当前值也满足 `C`，那么所有值都满足 `C`。

此函数用于良基递归的精译过程。
-/
def fix : Unit := ()

end WellFounded

/--
良基关系的逆像仍然良基。
-/
def invImage : Unit := ()

/--
如果 `α` 的所有元素在关系 `r` 下都是可及的，那么关系 `r` 是 `WellFounded` 的。
若关系是 `WellFounded` 的，就不存在沿该关系的无限下降。

如果函数定义中递归调用的实参按照一个良基关系减小，那么该函数终止。
良基关系有时也称为 *Artinian* 关系，或称其满足“降链条件”。
-/
inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
  /-- 若所有元素在 `r` 下都可及，则 `r` 良基。 -/
  | intro (h : ∀ a, _root_.Acc r a) : WellFounded r

/--
`Acc` 是可及性谓词。给定关系 `r`（例如 `<`）和值 `x`，`Acc r x` 表示 `x` 在
`r` 下可及：

若不存在无限序列 `... < y₂ < y₁ < y₀ < x`，则 `x` 可及。
-/
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  如果对每个满足 `r y x` 的 `y`，`y` 也可及，那么 `x` 可及。注意，若不存在满足
  `r y x` 的 `y`，则 `x` 可及；这样的 `x` 称为一个*基本情形*。
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

end ZhDoc.RecursiveDefs.WF
