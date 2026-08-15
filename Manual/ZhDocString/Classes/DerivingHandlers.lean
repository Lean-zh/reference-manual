import Lean
import Manual.ZhDocString.ZhDocString

namespace ZhDoc.Classes.DerivingHandlers

/--
为一个类注册派生处理器。此函数应当在 `initialize` 块中调用。

`DerivingHandler` 接收它所处理的全部类型的完全限定名。例如，
`deriving instance Foo for Bar, Baz` 会调用 ``fooHandler #[`Bar, `Baz]``。
-/
def registerDerivingHandler (_className : Name) (_handler : Array Name → Bool) : Unit :=
  ()

end ZhDoc.Classes.DerivingHandlers
