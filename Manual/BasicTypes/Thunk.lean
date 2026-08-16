/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.ZhDocString.Ch19Ch20.G2

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "惰性计算" =>
%%%
tag := "Thunk"
%%%

{deftech (key := "thunk")}_惰性计算_会延迟某个值的计算。
具体来说，{name}`Thunk` 类型用于在编译后的代码中把某个值的计算延迟到显式请求它时才进行——这种请求称为对惰性计算进行 {deftech (key := "force")}_强制求值_。
计算出的值会被保存下来，因此后续请求不会重复计算。
仅在显式请求时、并且至多只计算一次，称为 {deftech (key := "lazy evaluation")}_惰性求值_。{index}[call-by-need]
这种缓存机制对 Lean 的逻辑不可见；在逻辑中，{name}`Thunk` 等价于一个从 {name}`Unit` 出发的函数。


# 逻辑模型
%%%
tag := "Thunk-model"
%%%

惰性计算的逻辑模型是一个单字段结构体，其中包含一个从 {lean}`Unit` 出发的函数。
该结构体的字段是私有的，因此不能直接访问这个函数本身。
取而代之，应使用 {name}`Thunk.get`。
从逻辑的角度看，它们是等价的；之所以提供 {name}`Thunk.get`，是为了让编译器能够用实现惰性求值的平台原语来覆盖它。

{zhdocstring Thunk Manual.ZhDocString.Ch19Ch20.G2.c198}

# 运行时表示
%%%
tag := "Thunk-runtime"
%%%

:::figure "惰性计算的内存布局" (tag := "thunkffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean 对象头"),
  ("m_value", .object, twoLine "保存的值" "lean_object *"),
  ("m_closure", .object, twoLine "闭包" "lean_object *")
]
```
:::

惰性计算是 Lean 运行时支持的原语对象类型之一。
对象头中包含一个特定的标记，用于表明该对象是惰性计算。

:::paragraph
惰性计算有两个字段：
 * `m_value` 是指向已保存值的指针；如果该值尚未计算出来，它就是空指针。
 * `m_closure` 是一个闭包，应在需要计算该值时调用。

运行时系统维持如下不变量：闭包和已保存值中必有一个是空指针。
如果两者都是空指针，则说明该惰性计算正在另一个线程上被强制求值。
:::

当惰性计算被 {tech (key := "force")}[强制求值] 时，运行时系统会先检查保存的值是否已经算出；若已算出，就直接返回它。
否则，它会尝试通过原子地将闭包与空指针交换来获取该闭包上的锁。
如果成功获取锁，就调用闭包来计算该值；算出的值会存入保存值字段，并丢弃对该闭包的引用。
如果没有获取到锁，则说明另一个线程已经在计算该值；系统会等待其完成。

# 强制转换
%%%
tag := "Thunk-coercions"
%%%

:::leanSection
```lean -show
variable {α : Type u} {e : α}
```
存在从任意类型 {lean}`α` 到 {lean}`Thunk α` 的强制转换，它会把项 {lean}`e` 转换成 {lean}`Thunk.mk fun () => e`。
由于精译器会 {ref "coercion-insertion"}[展开强制转换]，原始项 {lean}`e` 的求值会被延迟；这种强制转换并不等价于 {name}`Thunk.pure`。
:::

:::example "惰性列表"

惰性列表是可能包含惰性计算的列表。
构造子 {name LazyList.delayed}`delayed` 会使列表的一部分按需计算。
```lean
inductive LazyList (α : Type u) where
  | nil
  | cons : α → LazyList α → LazyList α
  | delayed : Thunk (LazyList α) → LazyList α
deriving Inhabited
```

通过强制求值其中嵌入的所有惰性计算，可以把惰性列表转换为普通列表。
```lean
def LazyList.toList : LazyList α → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
  | .delayed xs => xs.get.toList
```

惰性列表上的许多操作都可以在不强制求值所嵌入惰性计算的前提下实现，而是继续构造新的惰性计算。
由于存在强制转换，{name LazyList.delayed}`delayed` 的主体不需要显式调用 {name}`Thunk.mk`。
```lean
def LazyList.take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x <| .delayed <| take n xs
  | n + 1, .delayed xs => .delayed <| take (n + 1) xs.get

def LazyList.ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (init := .nil) fun i xs =>
    .delayed <| LazyList.cons (f i) xs

def LazyList.append (xs ys : LazyList α) : LazyList α :=
  .delayed <|
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys
```

惰性通常对 Lean 程序是不可见的：没有办法检查某个惰性计算是否已经被强制求值。
不过，可以使用 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 来观察惰性计算的求值过程。
```lean
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val
```

惰性列表 {lean}`xs` 与 {lean}`ys` 在求值时会输出跟踪信息。
```lean
def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")
```

把 {lean}`xs` 转换为普通列表会强制求值其中嵌入的所有惰性计算：
```lean (name := lazy1)
#eval xs.toList
```
```leanOutput lazy1
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy1
[0, 1, 2]
```

同样地，把 {lean}`xs.append ys` 转换为普通列表也会强制求值其中嵌入的惰性计算：
```lean (name := lazy2)
#eval xs.append ys |>.toList
```
```leanOutput lazy2
xs: 0
xs: 1
xs: 2
ys: 0
ys: 1
ys: 2
```
```leanOutput lazy2
[0, 1, 2, 0, 1, 2]
```

在强制求值之前把 {lean}`xs` 追加到自身，只会产生一组跟踪信息，因为每个惰性计算的代码只会被求值一次：
```lean (name := lazy3)
#eval xs.append xs |>.toList
```
```leanOutput lazy3
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy3
[0, 1, 2, 0, 1, 2]
```

最后，对 {lean}`xs.append ys` 取前缀时，只会求值 {lean}`ys` 中的一部分惰性计算：
```lean (name := lazy4)
#eval xs.append ys |>.take 4 |>.toList
```
```leanOutput lazy4
xs: 0
xs: 1
xs: 2
ys: 0
```
```leanOutput lazy4
[0, 1, 2, 0]
```
:::


# 接口参考
%%%
tag := "Thunk-api"
%%%

{zhdocstring Thunk.get Manual.ZhDocString.Ch19Ch20.G2.c199}

{zhdocstring Thunk.map Manual.ZhDocString.Ch19Ch20.G2.c200}

{zhdocstring Thunk.pure Manual.ZhDocString.Ch19Ch20.G2.c201}

{zhdocstring Thunk.bind Manual.ZhDocString.Ch19Ch20.G2.c202}
