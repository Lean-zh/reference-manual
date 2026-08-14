/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


open Lean.Grind

#doc (Manual) "整合 `grind` 的功能" =>

:::paragraph
这个示例展示了 {tactic}`grind` 的各个子模块如何无缝整合。
特别地，我们可以：
* 使用自定义模式对库中的定理进行实例化，
* 执行分类讨论，
* 进行线性整数算术推理，包括模性条件，以及
* 进行 Gröbner 基推理
而完全无需显式给出指令来驱动这些推理模式之间的交互。
:::

在这个示例中，我们先使用一个“仿造”的实数版本，以及 `sin` 和 `cos` 函数。
当然，若改用 Mathlib 中对应的版本，这个例子也能[无需任何修改](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/grind/trig.lean)地工作！


:::TODO
给 `instCommRingR` 写一个 `sorry` 会导致运行时崩溃，原因尚不清楚。
:::

```lean
axiom R : Type


@[instance] axiom instCommRingR : Lean.Grind.CommRing R


axiom sin : R → R
axiom cos : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1
```

:::paragraph
第一步是告诉 grind：只要它看到涉及 {name}`sin` 或 {name}`cos` 的目标，就把三角恒等式“写到白板上”：

```lean
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x
```

注意，这里我们为同一个定理使用了*两个*不同的模式，因此即使 {tactic}`grind` 只看到其中一个函数，也会对该定理进行实例化。
如果希望更保守一些，只在 {name}`sin` 和 {name}`cos` 同时出现时才实例化该定理，那么可以使用多模式：

```lean -keep
grind_pattern trig_identity => cos x, sin x
```

对于这个例子，这两种做法都可以。
:::

::::leanSection
```lean -show
variable {x : R}
```

:::paragraph
由于 `grind` 会立刻注意到三角恒等式，我们可以证明如下目标：
```lean
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind
```
这里 {tactic}`grind` 的行为如下：

1. 它注意到 {lean}`cos x` 和 {lean}`sin x`，于是实例化三角恒等式。

2. 它注意到这在 {inst}`CommRing R` 上是一个多项式，于是将其交给 Gröbner 基模块。
   此时并不会进行实际计算：这是该环中的第一条多项式关系，因此 Gröbner 基会更新为 {lean}`[(cos x)^2 + (sin x)^2 - 1]`。

3. 它注意到目标左右两边都是 {inst}`CommRing R` 上的多项式，于是将它们送往 Gröbner 基模块做规范化。

由于它们模去 {lean}`(cos x)^2 + (sin x)^2 = 1` 后的范式相同，它们所在的等价类会被合并，目标因此得证。

:::


:::paragraph
当需要 {tech}[合一闭包] 时，我们也可以做这种推理：
```lean
example (f : R → Nat) :
    f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind
```

```lean -show
variable (f : R → Nat) (n : Nat)
```

和前面一样，{tactic}`grind` 会实例化三角恒等式，注意到 {lean}`(cos x + sin x)^2` 与 {lean}`2 * cos x * sin x + 1` 在模去 {lean}`(cos x)^2 + (sin x)^2 = 1` 后相等，
于是把这两个代数表达式放入同一个等价类，再把函数应用 {lean}`f ((cos x + sin x)^2)` 与 {lean}`f (2 * cos x * sin x + 1)` 放入同一个等价类，
从而关闭目标。
:::

注意，这里我们使用的是任意函数 {typed}`f : R → Nat`；下面来看看 `grind` 在完成 Gröbner 基步骤之后，是否还能继续使用一些线性整数算术推理：
```lean
example (f : R → Nat) :
    4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```


这里 {tactic}`grind` 首先推出，这个目标可化简为某个 {typed}`n : Nat` 上的 {lean}`4 * n ≠ 2 + n`（也就是像上面那样识别出那两个函数应用相等），然后利用模性推出矛盾。



最后，我们还可以混入一些分类讨论：
```lean
example (f : R → Nat) :
    max 3 (4 * f ((cos x + sin x)^2)) ≠
      2 + f (2 * cos x * sin x + 1) := by
  grind
```
和前面一样，{tactic}`grind` 首先完成识别这两个函数应用所需的实例化与 Gröbner 基计算。
不过，仅靠 `cutsat` 算法本身无法处理 {lean}`max 3 (4 * n) ≠ 2 + n`。
接着，在实例化 {lean}`Nat.max_def`（这是自动发生的，因为标准库中有相应标注）之后——该定理断言 {lean}`∀ {n m : Nat}, max n m = if n ≤ m then m else n`——{tactic}`grind` 就可以对这个不等式做分类讨论。
在分支 {lean}`3 ≤ 4 * n` 中，`cutsat` 再次利用模性证明 `4 * n ≠ 2 + n`。
在分支 {lean}`4 * n < 3` 中，`cutsat` 很快确定 {lean}`n = 0`，继而注意到 {lean}`4 * 0 ≠ 2 + 0`。

当然，这仍是一个相当人为的例子！
但在实践中，这种不同推理模式之间的自动整合非常强大：负责跟踪已实例化定理与等价类的中央“白板”，能够把相关项和等式交给合适的模块（这里是 `cutsat` 和 Gröbner 基），这些模块随后又能把新的事实返回给白板。

::::
