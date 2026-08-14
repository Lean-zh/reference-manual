import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Defs.Option

/--
启用“宽松”模式时，任何非空的原子标识符都可以成为自动绑定的隐式局部变量
（参见选项 `autoImplicit`）。

默认值为 `true`。
-/
def relaxedAutoImplicit : Bool := true

/--
声明头中未绑定的局部变量会成为隐式参数。在默认启用的“宽松”模式下，任何原子
标识符都符合条件；否则，只有单个字符后跟若干数字的标识符符合条件。例如，
`def f (x : Vector α n) : Vector α n :=` 会自动引入隐式变量 `{α n}`。

默认值为 `true`。
-/
def autoImplicit : Bool := true

end ZhDoc.Defs.Option
