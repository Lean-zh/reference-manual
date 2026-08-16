/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Manual.ZhDocString.ZhDocString

namespace Manual.ZhDocString.Ch19Ch20.G5

set_option linter.unusedVariables false
set_option autoImplicit true

universe u v w

/-!
本模块为第 19–20 章的自然数、整数和有限自然数 API 提供中文动态文档载体。
普通定义直接别名到真实声明；归纳类型和结构体按真实构造子与字段镜像。
-/

/--
从零开始的自然数。

内核和编译器都会对此类型作特殊处理，并用高效实现覆盖它。二者都使用快速的任意精度算术库（通常是 [GMP](https://gmplib.org/)）；运行时，足够小的 `Nat` 值不装箱。
-/
inductive c001 : Type where
  /--
  零，即最小的自然数。
  
  通常应避免显式写 `Nat.zero`，而使用字面量 `0`；前者是 [simp 规范形](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=simp-normal-forms)。
  -/
  | zero : c001
  /--
  自然数 `n` 的后继。
  
  通常应避免使用 `Nat.succ n`，而使用 `n + 1`；前者是 [simp 规范形](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=simp-normal-forms)。
  -/
  | succ : c001 → c001

/--
自然数的前驱比它小一；`0` 的前驱定义为 `0`。

该定义在编译器中由高效实现覆盖；这里给出的是逻辑模型。
-/
noncomputable def c002 := @Nat.pred

/--
自然数加法，通常通过 `+` 运算符使用。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。
-/
noncomputable def c003 := @Nat.add

/--
自然数减法，结果在 `0` 处截断，通常通过 `-` 运算符使用。

若结果本应小于零，则结果取零。

内核和编译器都会用任意精度算术库的高效实现覆盖此定义；这里给出的是逻辑模型。

示例：
* `5 - 3 = 2`
* `8 - 2 = 6`
* `8 - 8 = 0`
* `8 - 20 = 0`
-/
noncomputable def c004 := @Nat.sub

/--
自然数乘法，通常通过 `*` 运算符使用。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。
-/
noncomputable def c005 := @Nat.mul

/--
自然数除法会舍弃余数；除以 `0` 返回 `0`，通常通过 `/` 运算符使用。

这种运算有时称为“向下取整除法”。

运行时会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `21 / 3 = 7`
 * `21 / 5 = 4`
 * `0 / 22 = 0`
 * `5 / 0 = 0`
-/
noncomputable def c006 := @Nat.div

/--
取模运算计算一个自然数除以另一个自然数所得的余数，通常通过 `%` 运算符使用。除数为 `0` 时返回被除数，而不会报错。

`Nat.mod` 是 `Nat.modCore` 的包装器，它对两种情况作特殊处理，以获得更好的定义归约：
 * `Nat.mod 0 m` 应归约为 `0`，这对所有项 `m : Nat` 都成立。
 * `Nat.mod n (m + n + 1)` 应归约为 `n`，这针对具体的 `Nat` 字面量 `n`。

这些归约让 `Fin n` 字面量表现良好，因为 `OfNat` 的 `Fin` 实例使用 `Nat.mod`。特别地，`(0 : Fin (n + 1)).val` 应按定义归约为 `0`。`Nat.modCore` 能处理所有数，但其定义归约不如这里方便。

运行时会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `7 % 2 = 1`
 * `9 % 3 = 0`
 * `5 % 7 = 5`
 * `5 % 0 = 5`
 * `show ∀ (n : Nat), 0 % n = 0 from fun _ => rfl`
 * `show ∀ (m : Nat), 5 % (m + 6) = 5 from fun _ => rfl`
-/
noncomputable def c007 := @Nat.mod

/--
取模运算计算一个自然数除以另一个自然数所得的余数，通常通过 `%` 运算符使用。除数为 `0` 时返回被除数，而不会报错。

这是 `Nat.mod` 的核心实现。它能对任意两个封闭自然数算出正确结果；但当 `Nat` 含有自由变量时，它缺少一些方便的[定义归约](https://lean-lang.org/doc/reference/4.34.0-rc1/find/?domain=Verso.Genre.Manual.section&name=type-system)。包装器 `Nat.mod` 会特殊处理这些情况，然后调用 `Nat.modCore`。

运行时会用高效实现覆盖此函数；这里给出的是逻辑模型。
-/
noncomputable def c008 := @Nat.modCore

/--
自然数的幂运算，通常通过 `^` 运算符使用。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。
-/
noncomputable def c009 := @Nat.pow

/--
自然数的以二为底的对数，返回 `⌊max 0 (log₂ n)⌋`。

运行时会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `Nat.log2 0 = 0`
 * `Nat.log2 1 = 0`
 * `Nat.log2 2 = 1`
 * `Nat.log2 4 = 2`
 * `Nat.log2 7 = 2`
 * `Nat.log2 8 = 3`
-/
noncomputable def c010 := @Nat.log2

/--
将值的二进制表示左移指定的位数，通常通过 `<<<` 运算符使用。

示例：
 * `1 <<< 2 = 4`
 * `1 <<< 3 = 8`
 * `0 <<< 3 = 0`
 * `0xf1 <<< 4 = 0xf10`
-/
noncomputable def c011 := @Nat.shiftLeft

/--
将值的二进制表示右移指定的位数，通常通过 `>>>` 运算符使用。

示例：
 * `4 >>> 2 = 1`
 * `8 >>> 2 = 2`
 * `8 >>> 3 = 1`
 * `0 >>> 3 = 0`
 * `0xf13a >>> 8 = 0xf1`
-/
noncomputable def c012 := @Nat.shiftRight

/--
按位异或，通常通过 `^^^` 运算符使用。

仅当对应位恰好在一个输入中置位时，结果的该位才置位。
-/
noncomputable def c013 := @Nat.xor

/--
按位或，通常通过 `|||` 运算符使用。

只要对应位在至少一个输入中置位，结果的该位便置位。
-/
noncomputable def c014 := @Nat.lor

/--
按位与，通常通过 `&&&` 运算符使用。

仅当对应位在两个输入中都置位时，结果的该位才置位。
-/
noncomputable def c015 := @Nat.land

/--
用于实现 `Nat` 按位运算符的辅助函数。

所得 `Nat` 的每一位，都是把 `f` 应用于两个输入 `Nat` 的对应位所得；处理范围直到任一输入中最高的置位。
-/
noncomputable def c016 := @Nat.bitwise

/--
返回 `true` 的条件是从最低位起第 `(n+1)` 位为 `1`；若返回 `false`，则该位为 `0`。
-/
noncomputable def c017 := @Nat.testBit

/--
返回两个自然数中较小的一个，通常通过 `Min.min` 使用。

返回 `n` 的条件是 `n ≤ m`；返回 `m` 的条件是 `m ≤ n`。

示例：
* `min 0 5 = 0`
* `min 4 5 = 4`
* `min 4 3 = 3`
* `min 8 8 = 8`
-/
noncomputable def c018 := @Nat.min

/--
返回两个自然数中较大的一个，通常通过 `Max.max` 使用。

返回 `m` 的条件是 `n ≤ m`；返回 `n` 的条件是 `m ≤ n`。

示例：
* `max 0 5 = 5`
* `max 4 5 = 5`
* `max 4 3 = 4`
* `max 8 8 = 8`
-/
noncomputable def c019 := @Nat.max

/--
计算两个自然数的最大公约数，即能同时整除二者的最大自然数。

特别地，一个数与 `0` 的最大公约数就是该数本身。

这一基于欧几里得算法的参考实现会在内核和编译器中被任意精度算术的高效实现覆盖；这里给出的是逻辑模型。

示例：
* `Nat.gcd 10 15 = 5`
* `Nat.gcd 0 5 = 5`
* `Nat.gcd 7 0 = 7`
-/
noncomputable def c020 := @Nat.gcd

/--
`m` 与 `n` 的最小公倍数是能同时被 `m` 和 `n` 整除的最小自然数；若 `0` 是 `m` 或 `n` 中的任一个，则返回 `0`。

示例：
 * `Nat.lcm 9 6 = 18`
 * `Nat.lcm 9 3 = 9`
 * `Nat.lcm 0 3 = 0`
 * `Nat.lcm 3 0 = 0`
-/
noncomputable def c021 := @Nat.lcm

/--
自然数 `n` 是二的幂，是指存在某个 `k : Nat` 使得 `n = 2 ^ k`。
-/
noncomputable def c022 := @Nat.isPowerOfTwo

/--
返回大于或等于 `n` 的最小二次幂。

示例：
* `Nat.nextPowerOfTwo 0 = 1`
* `Nat.nextPowerOfTwo 1 = 1`
* `Nat.nextPowerOfTwo 2 = 2`
* `Nat.nextPowerOfTwo 3 = 4`
* `Nat.nextPowerOfTwo 5 = 8`
-/
noncomputable def c023 := @Nat.nextPowerOfTwo

/--
自然数的布尔相等比较，通常通过 `==` 运算符使用。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。
-/
noncomputable def c024 := @Nat.beq

/--
自然数的布尔小于等于比较。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `Nat.ble 2 5 = true`
 * `Nat.ble 5 2 = false`
 * `Nat.ble 5 5 = true`
-/
noncomputable def c025 := @Nat.ble

/--
自然数的布尔小于比较。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `Nat.blt 2 5 = true`
 * `Nat.blt 5 2 = false`
 * `Nat.blt 5 5 = false`
-/
noncomputable def c026 := @Nat.blt

/--
自然数相等性的判定过程，通常通过 `DecidableEq Nat` 实例使用。

内核和编译器都会用任意精度算术库的高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `Nat.decEq 5 5 = isTrue rfl`
 * `(if 3 = 4 then "yes" else "no") = "no"`
 * `show 12 = 12 by decide`
-/
noncomputable def c027 := @Nat.decEq

/--
自然数非严格不等式的判定过程，通常通过 `DecidableLE Nat` 实例使用。

示例：
 * `(if 3 ≤ 4 then "yes" else "no") = "yes"`
 * `(if 6 ≤ 4 then "yes" else "no") = "no"`
 * `show 12 ≤ 12 by decide`
 * `show 5 ≤ 12 by decide`
-/
noncomputable def c028 := @Nat.decLe

/--
自然数严格不等式的判定过程，通常通过 `DecidableLT Nat` 实例使用。

示例：
 * `(if 3 < 4 then "yes" else "no") = "yes"`
 * `(if 4 < 4 then "yes" else "no") = "no"`
 * `(if 6 < 4 then "yes" else "no") = "no"`
 * `show 5 < 12 by decide`
-/
noncomputable def c029 := @Nat.decLt

/--
自然数的非严格（弱）不等式，通常通过 `≤` 运算符使用。
-/
inductive c030 (n : Nat) : Nat → Prop where
  /--
  非严格不等式具有自反性：`n ≤ n`。
  -/
  | refl : c030 n n
  /--
  若 `n ≤ m`，则 `n ≤ m + 1`。
  -/
  | step : c030 n m → c030 n (Nat.succ m)

/--
自然数的严格不等式，通常通过 `<` 运算符使用。

其定义为 `n < m = n + 1 ≤ m`。
-/
noncomputable def c031 := @Nat.lt

/--
将函数对初始值应用指定次数。

换言之，迭代 `f` 共 `n` 次，作用于 `a`。

示例：
* `Nat.repeat f 3 a = f <| f <| f <| a`
* `Nat.repeat (· ++ "!") 4 "Hello" = "Hello!!!!"`
-/
noncomputable def c032 := @Nat.repeat

/--
将函数对初始值应用指定次数。

换言之，迭代 `f` 共 `n` 次，作用于 `a`。

这是 `Nat.repeat` 的尾递归版本，供运行时使用。

示例：
* `Nat.repeatTR f 3 a = f <| f <| f <| a`
* `Nat.repeatTR (· ++ "!") 4 "Hello" = "Hello!!!!"`
-/
noncomputable def c033 := @Nat.repeatTR

/--
迭代应用函数 `f`：从初始值 `init` 开始，共执行 `n` 次；每一步按递增顺序，把 `f` 应用于当前值以及下一个小于 `n` 的自然数。

示例：
* `Nat.fold 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.fold 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.fold 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
noncomputable def c034 := @Nat.fold

/--
迭代应用函数 `f`：从初始值 `init` 开始，共执行 `n` 次；每一步按递增顺序，把 `f` 应用于当前值以及下一个小于 `n` 的自然数。

这是 `Nat.fold` 的尾递归版本，供运行时使用。

示例：
* `Nat.foldTR 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.foldTR 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.foldTR 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
noncomputable def c035 := @Nat.foldTR

/--
迭代应用单子函数 `f`：从初始值 `init` 开始，共执行 `n` 次；每一步按递增顺序，把 `f` 应用于当前值以及下一个小于 `n` 的自然数。
-/
noncomputable def c036 := @Nat.foldM

/--
迭代应用函数 `f`：从初始值 `init` 开始，共执行 `n` 次；每一步按递减顺序，把 `f` 应用于当前值以及下一个小于 `n` 的自然数。

示例：
* `Nat.foldRev 3 f init = (f 0 (by simp) <| f 1 (by simp) <| f 2 (by simp) init)`
* `Nat.foldRev 4 (fun i _ xs => xs.push i) #[] = #[3, 2, 1, 0]`
* `Nat.foldRev 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
noncomputable def c037 := @Nat.foldRev

/--
迭代应用单子函数 `f`：从初始值 `init` 开始，共执行 `n` 次；每一步按递减顺序，把 `f` 应用于当前值以及下一个小于 `n` 的自然数。
-/
noncomputable def c038 := @Nat.foldRevM

/--
按递增顺序，对所有小于某个界的数执行单子动作。

示例：
````lean example
#eval Nat.forM 5 fun i _ => IO.println i
````
````output
0
1
2
3
4
````
-/
noncomputable def c039 := @Nat.forM

/--
按递减顺序，对所有小于某个界的数执行单子动作。

示例：
````lean example
#eval Nat.forRevM 5 fun i _ => IO.println i
````
````output
4
3
2
1
0
````
-/
noncomputable def c040 := @Nat.forRevM

/--
检查对每个严格小于给定界的数，`f` 是否都返回 `true`。

示例：
* `Nat.all 4 (fun i _ => i < 5) = true`
* `Nat.all 7 (fun i _ => i < 5) = false`
* `Nat.all 7 (fun i _ => i % 2 = 0) = false`
* `Nat.all 1 (fun i _ => i % 2 = 0) = true`
-/
noncomputable def c041 := @Nat.all

/--
检查对每个严格小于给定界的数，`f` 是否都返回 `true`。

这是与 `Nat.all` 等价的尾递归版本，供运行时使用。

示例：
* `Nat.allTR 4 (fun i _ => i < 5) = true`
* `Nat.allTR 7 (fun i _ => i < 5) = false`
* `Nat.allTR 7 (fun i _ => i % 2 = 0) = false`
* `Nat.allTR 1 (fun i _ => i % 2 = 0) = true`
-/
noncomputable def c042 := @Nat.allTR

/--
检查是否存在某个小于给定界的数，使 `f` 返回 `true`。

示例：
* `Nat.any 4 (fun i _ => i < 5) = true`
* `Nat.any 7 (fun i _ => i < 5) = true`
* `Nat.any 7 (fun i _ => i % 2 = 0) = true`
* `Nat.any 1 (fun i _ => i % 2 = 1) = false`
-/
noncomputable def c043 := @Nat.any

/--
检查是否存在某个小于给定界的数，使 `f` 返回 `true`。

这是与 `Nat.any` 等价的尾递归版本，供运行时使用。

示例：
* `Nat.anyTR 4 (fun i _ => i < 5) = true`
* `Nat.anyTR 7 (fun i _ => i < 5) = true`
* `Nat.anyTR 7 (fun i _ => i % 2 = 0) = true`
* `Nat.anyTR 1 (fun i _ => i % 2 = 1) = false`
-/
noncomputable def c044 := @Nat.anyTR

/--
检查单子谓词 `p` 是否对所有小于给定界的数都返回 `true`。按递增顺序检查，`p` 一旦返回 false，便不再检查后续数字。
-/
noncomputable def c045 := @Nat.allM

/--
检查是否存在某个小于给定界的数，使单子谓词 `p` 返回 `true`。按递增顺序检查，`p` 一旦返回 true，便不再检查后续数字。
-/
noncomputable def c046 := @Nat.anyM

/--
将自然数转换为 8 位无符号整数，溢出时回绕。

运行时会用高效实现覆盖此函数。

示例：
* `Nat.toUInt8 5 = 5`
* `Nat.toUInt8 255 = 255`
* `Nat.toUInt8 256 = 0`
* `Nat.toUInt8 259 = 3`
* `Nat.toUInt8 32770 = 2`
-/
noncomputable def c047 := @Nat.toUInt8

/--
将自然数转换为 16 位无符号整数，溢出时回绕。

运行时会用高效实现覆盖此函数。

示例：
* `Nat.toUInt16 5 = 5`
* `Nat.toUInt16 255 = 255`
* `Nat.toUInt16 32770 = 32770`
* `Nat.toUInt16 65537 = 1`
-/
noncomputable def c048 := @Nat.toUInt16

/--
将自然数转换为 32 位无符号整数，溢出时回绕。

运行时会用高效实现覆盖此函数。

示例：
* `Nat.toUInt32 5 = 5`
* `Nat.toUInt32 65_539 = 65_539`
* `Nat.toUInt32 4_294_967_299 = 3`
-/
noncomputable def c049 := @Nat.toUInt32

/--
将自然数转换为 64 位无符号整数，溢出时回绕。

运行时会用高效实现覆盖此函数。

示例：
* `Nat.toUInt64 5 = 5`
* `Nat.toUInt64 65539 = 65539`
* `Nat.toUInt64 4_294_967_299 = 4_294_967_299`
* `Nat.toUInt64 18_446_744_073_709_551_620 = 4`
-/
noncomputable def c050 := @Nat.toUInt64

/--
将任意精度自然数转换为无符号机器字大小的整数，溢出时回绕。

运行时会用高效实现覆盖此函数。
-/
noncomputable def c051 := @Nat.toUSize

/--
将自然数转换为 8 位有符号整数，溢出时回绕到负数。

示例：
 * `Nat.toInt8 53 = 53`
 * `Nat.toInt8 127 = 127`
 * `Nat.toInt8 128 = -128`
 * `Nat.toInt8 255 = -1`
-/
noncomputable def c052 := @Nat.toInt8

/--
将自然数转换为 16 位有符号整数，溢出时回绕到负数。

示例：
 * `Nat.toInt16 127 = 127`
 * `Nat.toInt16 32767 = 32767`
 * `Nat.toInt16 32768 = -32768`
 * `Nat.toInt16 32770 = -32766`
-/
noncomputable def c053 := @Nat.toInt16

/--
将自然数转换为 32 位有符号整数，溢出时回绕到负数。

示例：
 * `Nat.toInt32 127 = 127`
 * `Nat.toInt32 32770 = 32770`
 * `Nat.toInt32 2_147_483_647 = 2_147_483_647`
 * `Nat.toInt32 2_147_483_648 = -2_147_483_648`
-/
noncomputable def c054 := @Nat.toInt32

/--
将自然数转换为 64 位有符号整数，溢出时回绕到负数。

示例：
 * `Nat.toInt64 127 = 127`
 * `Nat.toInt64 2_147_483_648 = 2_147_483_648`
 * `Nat.toInt64 9_223_372_036_854_775_807 = 9_223_372_036_854_775_807`
 * `Nat.toInt64 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
 * `Nat.toInt64 18_446_744_073_709_551_618 = 0`
-/
noncomputable def c055 := @Nat.toInt64

/--
将任意精度自然数转换为机器字大小的有符号整数，溢出时回绕。

运行时会用高效实现覆盖此函数。
-/
noncomputable def c056 := @Nat.toISize

/--
将自然数转换为最接近的 64 位浮点数；若超出 `Float` 的范围，则得到无穷浮点值。
-/
noncomputable def c057 := @Nat.toFloat

/--
将自然数转换为最接近的 32 位浮点数；若超出 `Float32` 的范围，则得到无穷浮点值。
-/
noncomputable def c058 := @Nat.toFloat32

/--
当一个 `Nat` 小于 `0x110000`，且不在代理码点范围（含端点的 `0xd800` 到 `0xdfff`）内时，它表示有效的 Unicode 码点。
-/
noncomputable def c059 := @Nat.isValidChar

/--
将自然数转换为其十进制字符串表示。
-/
noncomputable def c060 := @Nat.repr

/--
以给定进制返回自然数的十进制表示所对应的数字字符列表。若进制大于 `16`，则返回 `'*'` 来表示大于 `0xf` 的数字。

示例：
* `Nat.toDigits 10 0xff = ['2', '5', '5']`
* `Nat.toDigits 8 0xc = ['1', '4']`
* `Nat.toDigits 16 0xcafe = ['c', 'a', 'f', 'e']`
* `Nat.toDigits 80 200 = ['2', '*']`
-/
noncomputable def c061 := @Nat.toDigits

/--
返回 `n` 的单个数字字符表示，假定所用进制不大于 `16`；返回 `'*'` 表示 `n > 15`。

示例：
 * `Nat.digitChar 5 = '5'`
 * `Nat.digitChar 12 = 'c'`
 * `Nat.digitChar 15 = 'f'`
 * `Nat.digitChar 16 = '*'`
 * `Nat.digitChar 85 = '*'`
-/
noncomputable def c062 := @Nat.digitChar

/--
将自然数转换为字符串，其中以 Unicode 下标数字字符表示其十进制形式。

示例：
 * `Nat.toSubscriptString 0 = "₀"`
 * `Nat.toSubscriptString 35 = "₃₅"`
-/
noncomputable def c063 := @Nat.toSubscriptString

/--
将自然数转换为字符串，其中以 Unicode 上标数字字符表示其十进制形式。

示例：
 * `Nat.toSuperscriptString 0 = "⁰"`
 * `Nat.toSuperscriptString 35 = "³⁵"`
-/
noncomputable def c064 := @Nat.toSuperscriptString

/--
将自然数转换为与其十进制表示对应的 Unicode 上标数字字符列表。

示例：
 * `Nat.toSuperDigits 0 = ['⁰']`
 * `Nat.toSuperDigits 35 = ['³', '⁵']`
-/
noncomputable def c065 := @Nat.toSuperDigits

/--
将自然数转换为与其十进制表示对应的 Unicode 下标数字字符列表。

示例：
 * `Nat.toSubDigits 0 = ['₀']`
 * `Nat.toSubDigits 35 = ['₃', '₅']`
-/
noncomputable def c066 := @Nat.toSubDigits

/--
将小于 `10` 的自然数转换为相应的 Unicode 下标数字字符；其他数返回 `'*'`。

示例：
* `Nat.subDigitChar 3 = '₃'`
* `Nat.subDigitChar 7 = '₇'`
* `Nat.subDigitChar 10 = '*'`
-/
noncomputable def c067 := @Nat.subDigitChar

/--
将小于 `10` 的自然数转换为相应的 Unicode 上标数字字符；其他数返回 `'*'`。

示例：
* `Nat.superDigitChar 3 = '³'`
* `Nat.superDigitChar 7 = '⁷'`
* `Nat.superDigitChar 10 = '*'`
-/
noncomputable def c068 := @Nat.superDigitChar

/--
`Nat` 的递归器，使用 `0` 表示 `Nat.zero`，使用 `n + 1` 表示 `Nat.succ`。

除此以外，它与默认递归器 `Nat.rec` 相同；`induction` 策略默认用它处理 `Nat`。
-/
noncomputable def c069 := @Nat.recAux

/--
`Nat` 的分类讨论原理，使用 `0` 表示 `Nat.zero`，使用 `n + 1` 表示 `Nat.succ`。

除此以外，它与默认递归器 `Nat.casesOn` 相同；它是 `Nat` 的默认分类讨论原理，由 `Nat` 上的 `cases` 策略使用。
-/
noncomputable def c070 := @Nat.casesAuxOn

/--
自然数上的强归纳。

归纳假设是所有小于给定数的数都满足动机，而目标是证明该给定数也满足动机。
-/
noncomputable def c071 := @Nat.strongRecOn

/--
基于自然数强归纳的分类讨论。
-/
noncomputable def c072 := @Nat.caseStrongRecOn

/--
为通过反复减法进行自然数除法的递归模式定制的归纳原理。
-/
noncomputable def c073 := @Nat.div.inductionOn

/--
自然数的归纳原理，包含两种情形：
* `n = 0`，并且动机对 `0` 成立；
* `n > 0`，目标是证明动机对 `n` 成立，并可假设其对 `n / 2` 成立。
-/
noncomputable def c074 := @Nat.div2Induction

/--
为推理 `Nat.mod` 的递归模式而定制的归纳原理。
-/
noncomputable def c075 := @Nat.mod.inductionOn

/--
整数。

编译器会对此类型作特殊处理，并用高效实现覆盖它。运行时对 `Int` 使用特殊表示：直接存储“小”有符号数，而较大的数使用快速任意精度算术库（通常是 [GMP](https://gmplib.org/)）。“小数”是可用比平台指针大小少一位编码的整数（即 64 位架构上为 63 位，32 位架构上为 31 位）。
-/
inductive c076 : Type where
  /--
  自然数也是整数。
  
  此构造子覆盖非负整数（从 `0` 到 `∞`）。
  -/
  | ofNat : Nat → c076
  /--
  自然数后继的负数是整数。
  
  此构造子覆盖负整数（从 `-1` 到 `-∞`）。
  -/
  | negSucc : Nat → c076

/--
以另一个整数返回该整数的“符号”：
* 正数返回 `1`；
* 负数返回 `-1`；
* `0` 返回 `0`。

示例：
* `Int.sign 34 = 1`
* `Int.sign 2 = 1`
* `Int.sign 0 = 0`
* `Int.sign -1 = -1`
* `Int.sign -362 = -1`
-/
noncomputable def c077 := @Int.sign

/--
整数的绝对值是它到 `0` 的距离。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `(7 : Int).natAbs = 7`
 * `(0 : Int).natAbs = 0`
 * `(-11 : Int).natAbs = 11`
-/
noncomputable def c078 := @Int.natAbs

/--
将整数转换为自然数；负数转换为 `0`。

示例：
* `(7 : Int).toNat = 7`
* `(0 : Int).toNat = 0`
* `(-7 : Int).toNat = 0`
-/
noncomputable def c079 := @Int.toNat

/--
将整数转换为自然数；负数返回 `none`。

示例：
* `(7 : Int).toNat? = some 7`
* `(0 : Int).toNat? = some 0`
* `(-7 : Int).toNat? = none`
-/
noncomputable def c080 := @Int.toNat?

/--
将任意精度整数转换为机器字大小的有符号整数，上溢或下溢时回绕。

运行时会用高效实现覆盖此函数。
-/
noncomputable def c081 := @Int.toISize

/--
将任意精度整数转换为 8 位整数，上溢或下溢时回绕。

示例：
* `Int.toInt8 48 = 48`
* `Int.toInt8 (-115) = -115`
* `Int.toInt8 (-129) = 127`
* `Int.toInt8 (128) = -128`
-/
noncomputable def c082 := @Int.toInt8

/--
将任意精度整数转换为 16 位整数，上溢或下溢时回绕。

示例：
* `Int.toInt16 48 = 48`
* `Int.toInt16 (-129) = -129`
* `Int.toInt16 (128) = 128`
* `Int.toInt16 70000 = 4464`
* `Int.toInt16 (-40000) = 25536`
-/
noncomputable def c083 := @Int.toInt16

/--
将任意精度整数转换为 32 位整数，上溢或下溢时回绕。

示例：
* `Int.toInt32 48 = 48`
* `Int.toInt32 (-129) = -129`
* `Int.toInt32 70000 = 70000`
* `Int.toInt32 (-40000) = -40000`
* `Int.toInt32 2147483648 = -2147483648`
* `Int.toInt32 (-2147483649) = 2147483647`
-/
noncomputable def c084 := @Int.toInt32

/--
将任意精度整数转换为 64 位整数，上溢或下溢时回绕。

运行时会用高效实现覆盖此函数。

示例：
* `Int.toInt64 48 = 48`
* `Int.toInt64 (-40_000) = -40_000`
* `Int.toInt64 2_147_483_648 = 2_147_483_648`
* `Int.toInt64 (-2_147_483_649) = -2_147_483_649`
* `Int.toInt64 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
* `Int.toInt64 (-9_223_372_036_854_775_809) = 9_223_372_036_854_775_807`
-/
noncomputable def c085 := @Int.toInt64

/--
返回整数的十进制字符串表示。
-/
noncomputable def c086 := @Int.repr

/--
整数加法，通常通过 `+` 运算符使用。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `(7 : Int) + (6 : Int) = 13`
 * `(6 : Int) + (-6 : Int) = 0`
-/
noncomputable def c087 := @Int.add

/--
整数减法，通常通过 `-` 运算符使用。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `(63 : Int) - (6 : Int) = 57`
* `(7 : Int) - (0 : Int) = 7`
* `(0 : Int) - (7 : Int) = -7`
-/
noncomputable def c088 := @Int.sub

/--
两个自然数的不截断减法。

示例：
* `Int.subNatNat 5 2 = 3`
* `Int.subNatNat 2 5 = -3`
* `Int.subNatNat 0 13 = -13`
-/
noncomputable def c089 := @Int.subNatNat

/--
整数取负，通常通过前缀 `-` 运算符使用。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `-(6 : Int) = -6`
 * `-(-6 : Int) = 6`
 * `(12 : Int).neg = -12`
-/
noncomputable def c090 := @Int.neg

/--
自然数取负。

示例：
* `Int.negOfNat 6 = -6`
* `Int.negOfNat 0 = 0`
-/
noncomputable def c091 := @Int.negOfNat

/--
整数乘法，通常通过 `*` 运算符使用。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
 * `(63 : Int) * (6 : Int) = 378`
 * `(6 : Int) * (-6 : Int) = -36`
 * `(7 : Int) * (0 : Int) = 0`
-/
noncomputable def c092 := @Int.mul

/--
整数的自然数次幂，通常通过 `^` 运算符使用。

示例：
* `(2 : Int) ^ 4 = 16`
* `(10 : Int) ^ 0 = 1`
* `(0 : Int) ^ 10 = 0`
* `(-7 : Int) ^ 3 = -343`
-/
noncomputable def c093 := @Int.pow

/--
以自然数计算两个整数的最大公约数，即能同时整除二者的最大自然数；数与 `0` 的最大公约数是该数的绝对值。

此实现使用 `Nat.gcd`；内核和编译器都会用任意精度算术的高效实现覆盖后者。

示例：
* `Int.gcd 10 15 = 5`
* `Int.gcd 10 (-15) = 5`
* `Int.gcd (-6) (-9) = 3`
* `Int.gcd 0 5 = 5`
* `Int.gcd (-7) 0 = 7`
-/
noncomputable def c094 := @Int.gcd

/--
以自然数计算两个整数的最小公倍数，即能被二者绝对值整除的最小自然数。

示例：
 * `Int.lcm 9 6 = 18`
 * `Int.lcm 9 (-6) = 18`
 * `Int.lcm 9 3 = 9`
 * `Int.lcm 9 (-3) = 9`
 * `Int.lcm 0 3 = 0`
 * `Int.lcm (-3) 0 = 0`
-/
noncomputable def c095 := @Int.lcm

/--
使用 E 舍入约定的整数除法，通常通过 `/` 运算符使用。除以零定义为零，而不是错误。

在 E 舍入约定（欧几里得除法）下，`Int.emod x y` 满足 `0 ≤ Int.emod x y < Int.natAbs y`（当 `y ≠ 0` 时）；而 `Int.ediv` 是满足 `Int.emod x y + (Int.ediv x y) * y = x`（当 `y ≠ 0` 时）的唯一函数。

因此，`Int.ediv x y` 等于 `⌊x / y⌋`（当 `y > 0` 时），或等于 `⌈x / y⌉`（当 `y < 0` 时）。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `(7 : Int) / (0 : Int) = 0`
* `(0 : Int) / (7 : Int) = 0`
* `(12 : Int) / (6 : Int) = 2`
* `(12 : Int) / (-6 : Int) = -2`
* `(-12 : Int) / (6 : Int) = -2`
* `(-12 : Int) / (-6 : Int) = 2`
* `(12 : Int) / (7 : Int) = 1`
* `(12 : Int) / (-7 : Int) = -1`
* `(-12 : Int) / (7 : Int) = -2`
* `(-12 : Int) / (-7 : Int) = 2`
-/
noncomputable def c096 := @Int.ediv

/--
使用 E 舍入约定的整数取模，通常通过 `%` 运算符使用。

在 E 舍入约定（欧几里得除法）下，`Int.emod x y` 满足 `0 ≤ Int.emod x y < Int.natAbs y`（当 `y ≠ 0` 时）；而 `Int.ediv` 是满足 `Int.emod x y + (Int.ediv x y) * y = x`（当 `y ≠ 0` 时）的唯一函数。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `(7 : Int) % (0 : Int) = 7`
* `(0 : Int) % (7 : Int) = 0`
* `(12 : Int) % (6 : Int) = 0`
* `(12 : Int) % (-6 : Int) = 0`
* `(-12 : Int) % (6 : Int) = 0`
* `(-12 : Int) % (-6 : Int) = 0`
* `(12 : Int) % (7 : Int) = 5`
* `(12 : Int) % (-7 : Int) = 5`
* `(-12 : Int) % (7 : Int) = 2`
* `(-12 : Int) % (-7 : Int) = 2`
-/
noncomputable def c097 := @Int.emod

/--
使用 T 舍入约定的整数除法。

在 [T 舍入约定][t-rounding]（截断除法）下，所有舍入都趋向零。除以 0 定义为 0。在此约定下，`Int.tmod a b + b * (Int.tdiv a b) = a`。

[t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `(7 : Int).tdiv (0 : Int) = 0`
* `(0 : Int).tdiv (7 : Int) = 0`
* `(12 : Int).tdiv (6 : Int) = 2`
* `(12 : Int).tdiv (-6 : Int) = -2`
* `(-12 : Int).tdiv (6 : Int) = -2`
* `(-12 : Int).tdiv (-6 : Int) = 2`
* `(12 : Int).tdiv (7 : Int) = 1`
* `(12 : Int).tdiv (-7 : Int) = -1`
* `(-12 : Int).tdiv (7 : Int) = -1`
* `(-12 : Int).tdiv (-7 : Int) = 1`
-/
noncomputable def c098 := @Int.tdiv

/--
使用 T 舍入约定的整数取模。

在 [T 舍入约定][t-rounding]（截断除法）下，所有舍入都趋向零。除以 0 定义为 0，且 `Int.tmod a 0 = a`。

在此约定下，`Int.tmod a b + b * (Int.tdiv a b) = a`。此外，`Int.natAbs (Int.tmod a b) = Int.natAbs a % Int.natAbs b`；当 `b` 不整除 `a` 时，`Int.tmod a b` 与 `a` 同号。

[t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `(7 : Int).tmod (0 : Int) = 7`
* `(0 : Int).tmod (7 : Int) = 0`
* `(12 : Int).tmod (6 : Int) = 0`
* `(12 : Int).tmod (-6 : Int) = 0`
* `(-12 : Int).tmod (6 : Int) = 0`
* `(-12 : Int).tmod (-6 : Int) = 0`
* `(12 : Int).tmod (7 : Int) = 5`
* `(12 : Int).tmod (-7 : Int) = 5`
* `(-12 : Int).tmod (7 : Int) = -5`
* `(-12 : Int).tmod (-7 : Int) = -5`
-/
noncomputable def c099 := @Int.tmod

/--
平衡除法。

它返回使 `b * (Int.bdiv a b) + Int.bmod a b = a` 成立的唯一整数。

示例：
* `(7 : Int).bdiv 0 = 0`
* `(0 : Int).bdiv 7 = 0`
* `(12 : Int).bdiv 6 = 2`
* `(12 : Int).bdiv 7 = 2`
* `(12 : Int).bdiv 8 = 2`
* `(12 : Int).bdiv 9 = 1`
* `(-12 : Int).bdiv 6 = -2`
* `(-12 : Int).bdiv 7 = -2`
* `(-12 : Int).bdiv 8 = -1`
* `(-12 : Int).bdiv 9 = -1`
-/
noncomputable def c100 := @Int.bdiv

/--
平衡取模。

这个整数取模版本使用平衡舍入约定，保证 `-m / 2 ≤ Int.bmod x m < m/2` 在 `m ≠ 0` 时成立，且 `Int.bmod x m` 与 `x` 模 `m` 同余。

若 `m = 0`，则 `Int.bmod x m = x`。

示例：
* `(7 : Int).bmod 0 = 7`
* `(0 : Int).bmod 7 = 0`
* `(12 : Int).bmod 6 = 0`
* `(12 : Int).bmod 7 = -2`
* `(12 : Int).bmod 8 = -4`
* `(12 : Int).bmod 9 = 3`
* `(-12 : Int).bmod 6 = 0`
* `(-12 : Int).bmod 7 = 2`
* `(-12 : Int).bmod 8 = -4`
* `(-12 : Int).bmod 9 = -3`
-/
noncomputable def c101 := @Int.bmod

/--
使用 F 舍入约定的整数除法。

在 F 舍入约定（向下取整除法）下，`Int.fdiv x y` 满足 `Int.fdiv x y = ⌊x / y⌋`；`Int.fmod` 是满足 `Int.fmod x y + (Int.fdiv x y) * y = x` 的唯一函数。

示例：
* `(7 : Int).fdiv (0 : Int) = 0`
* `(0 : Int).fdiv (7 : Int) = 0`
* `(12 : Int).fdiv (6 : Int) = 2`
* `(12 : Int).fdiv (-6 : Int) = -2`
* `(-12 : Int).fdiv (6 : Int) = -2`
* `(-12 : Int).fdiv (-6 : Int) = 2`
* `(12 : Int).fdiv (7 : Int) = 1`
* `(12 : Int).fdiv (-7 : Int) = -2`
* `(-12 : Int).fdiv (7 : Int) = -2`
* `(-12 : Int).fdiv (-7 : Int) = 1`
-/
noncomputable def c102 := @Int.fdiv

/--
使用 F 舍入约定的整数取模。

在 F 舍入约定（向下取整除法）下，`Int.fdiv x y` 满足 `Int.fdiv x y = ⌊x / y⌋`；`Int.fmod` 是满足 `Int.fmod x y + (Int.fdiv x y) * y = x` 的唯一函数。

示例：

* `(7 : Int).fmod (0 : Int) = 7`
* `(0 : Int).fmod (7 : Int) = 0`

* `(12 : Int).fmod (6 : Int) = 0`
* `(12 : Int).fmod (-6 : Int) = 0`
* `(-12 : Int).fmod (6 : Int) = 0`
* `(-12 : Int).fmod (-6 : Int) = 0`

* `(12 : Int).fmod (7 : Int) = 5`
* `(12 : Int).fmod (-7 : Int) = -2`
* `(-12 : Int).fmod (7 : Int) = 2`
* `(-12 : Int).fmod (-7 : Int) = -5`
-/
noncomputable def c103 := @Int.fmod

/--
按位非，通常通过前缀 `~~~` 运算符使用。

把整数解释为二进制补码下的无限位序列，并逐位取反。

示例：
* `~~~(0 : Int) = -1`
* `~~~(1 : Int) = -2`
* `~~~(-1 : Int) = 0`
-/
noncomputable def c104 := @Int.not

/--
按位右移，通常通过 `>>>` 运算符使用。

把整数解释为二进制补码下的无限位序列，并将其向右移位。

示例：
* `( 0b0111 : Int) >>> 1 =  0b0011`
* `( 0b1000 : Int) >>> 1 =  0b0100`
* `(-0b1000 : Int) >>> 1 = -0b0100`
* `(-0b0111 : Int) >>> 1 = -0b0100`
-/
noncomputable def c105 := @Int.shiftRight

/--
整数的非严格不等式，通常通过 `≤` 运算符使用。

把 `a ≤ b` 定义为 `b - a ≥ 0`，其中使用 `Int.NonNeg`。
-/
noncomputable def c106 := @Int.le

/--
整数的严格不等式，通常通过 `<` 运算符使用。

`a < b` 在 `a + 1 ≤ b` 时成立。
-/
noncomputable def c107 := @Int.lt

/--
判定两个整数是否相等，通常通过 `DecidableEq Int` 实例使用。

编译器会用高效实现覆盖此函数；这里给出的是逻辑模型。

示例：
* `show (7 : Int) = (3 : Int) + (4 : Int) by decide`
* `if (6 : Int) = (3 : Int) * (2 : Int) then "yes" else "no" = "yes"`
* `(¬ (6 : Int) = (3 : Int)) = true`
-/
noncomputable def c108 := @Int.decEq

/--
小于某个上界的自然数。

具体而言，`Fin n` 是自然数 `i`，并带有约束 `i < n`；它是含有 `n` 个元素的规范类型。
-/
structure c109 (n : Nat) : Type where
  /--
  严格小于 `n` 的数。
  
  `Fin.val` 是强制转换，因此任何 `Fin n` 都可在需要 `Nat` 的位置使用。
  -/
  val : Nat
  /--
  数 `val` 严格小于上界 `n`。
  -/
  isLt : val < n

/--
构造 `Fin n`，所需数据为 `i : Nat` 以及 `i < n` 的证明。
-/
add_decl_doc c109.mk

/--
`Fin (n+1)` 的最大值，即 `n`。

示例：
* `Fin.last 4 = (4 : Fin 5)`
* `(Fin.last 0).val = (0 : Nat)`
-/
noncomputable def c110 := @Fin.last

/--
后继，同时增大上界。

这不同于加 `1`；后者会回绕。

示例：
* `(2 : Fin 3).succ = (3 : Fin 4)`
* `(2 : Fin 3) + 1 = (0 : Fin 3)`
-/
noncomputable def c111 := @Fin.succ

/--
`Fin (n+1)` 中非零元素的前驱，同时减小上界。

示例：
* `(4 : Fin 8).pred (by decide) = (3 : Fin 7)`
* `(1 : Fin 2).pred (by decide) = (0 : Fin 1)`
-/
noncomputable def c112 := @Fin.pred

/--
模 `n` 加法，通常通过 `+` 运算符调用。

示例：
* `(2 : Fin 8) + (2 : Fin 8) = (4 : Fin 8)`
* `(2 : Fin 3) + (2 : Fin 3) = (1 : Fin 3)`
-/
noncomputable def c113 := @Fin.add

/--
将自然数加到 `Fin` 上，同时增大上界。

这是 `Fin.succ` 的推广。

`Fin.addNat` 是此函数的另一版本，其 `Nat` 参数位于第二位。

示例：
* `Fin.natAdd 3 (5 : Fin 8) = (8 : Fin 11)`
* `Fin.natAdd 1 (0 : Fin 8) = (1 : Fin 9)`
* `Fin.natAdd 1 (2 : Fin 8) = (3 : Fin 9)`
-/
noncomputable def c114 := @Fin.natAdd

/--
将自然数加到 `Fin` 上，同时增大上界。

这是 `Fin.succ` 的推广。

`Fin.natAdd` 是此函数的另一版本，其 `Nat` 参数位于第一位。

示例：
* `Fin.addNat (5 : Fin 8) 3 = (8 : Fin 11)`
* `Fin.addNat (0 : Fin 8) 1 = (1 : Fin 9)`
* `Fin.addNat (1 : Fin 8) 2 = (3 : Fin 10)`
-/
noncomputable def c115 := @Fin.addNat

/--
模 `n` 乘法，通常通过 `*` 运算符调用。

示例：
* `(2 : Fin 10) * (2 : Fin 10) = (4 : Fin 10)`
* `(2 : Fin 10) * (7 : Fin 10) = (4 : Fin 10)`
* `(3 : Fin 10) * (7 : Fin 10) = (1 : Fin 10)`
-/
noncomputable def c116 := @Fin.mul

/--
模 `n` 减法，通常通过 `-` 运算符调用。

示例：
* `(5 : Fin 11) - (3 : Fin 11) = (2 : Fin 11)`
* `(3 : Fin 11) - (5 : Fin 11) = (9 : Fin 11)`
-/
noncomputable def c117 := @Fin.sub

/--
从 `Fin` 中减去自然数，同时缩小上界。

这是 `Fin.pred` 的推广，并保证不会下溢或回绕。

示例：
* `(5 : Fin 9).subNat 2 (by decide) = (3 : Fin 7)`
* `(5 : Fin 9).subNat 0 (by decide) = (5 : Fin 9)`
* `(3 : Fin 9).subNat 3 (by decide) = (0 : Fin 6)`
-/
noncomputable def c118 := @Fin.subNat

/--
有界数的除法，通常通过 `/` 运算符调用。

结果与 `/` 运算符在 `Nat` 上所计算的值相同；特别地，除以 `0` 的结果是 `0`。

示例：
 * `(5 : Fin 10) / (2 : Fin 10) = (2 : Fin 10)`
 * `(5 : Fin 10) / (0 : Fin 10) = (0 : Fin 10)`
 * `(5 : Fin 10) / (7 : Fin 10) = (0 : Fin 10)`
-/
noncomputable def c119 := @Fin.div

/--
有界数的取模，通常通过 `%` 运算符调用。

结果与 `%` 运算符在 `Nat` 上所计算的值相同。
-/
noncomputable def c120 := @Fin.mod

/--
有界数相对于某个 `Nat` 的取模。

结果与 `%` 运算符在 `Nat` 上所计算的值相同。
-/
noncomputable def c121 := @Fin.modn

/--
有界数的以二为底的对数。

结果与 `Nat.log2` 的计算结果相同；特别地，`0` 的结果是 `0`。

示例：
 * `(8 : Fin 10).log2 = (3 : Fin 10)`
 * `(7 : Fin 10).log2 = (2 : Fin 10)`
 * `(4 : Fin 10).log2 = (2 : Fin 10)`
 * `(3 : Fin 10).log2 = (1 : Fin 10)`
 * `(1 : Fin 10).log2 = (0 : Fin 10)`
 * `(0 : Fin 10).log2 = (0 : Fin 10)`
-/
noncomputable def c122 := @Fin.log2

/--
有界数按位左移，溢出时回绕。

示例：
* `(1 : Fin 10) <<< (1 : Fin 10) = (2 : Fin 10)`
* `(1 : Fin 10) <<< (3 : Fin 10) = (8 : Fin 10)`
* `(1 : Fin 10) <<< (4 : Fin 10) = (6 : Fin 10)`
-/
noncomputable def c123 := @Fin.shiftLeft

/--
有界数按位右移。

该运算符对应逻辑移位而非算术移位；新补入的位始终为 `0`。

示例：
 * `(15 : Fin 16) >>> (1 : Fin 16) = (7 : Fin 16)`
 * `(15 : Fin 16) >>> (2 : Fin 16) = (3 : Fin 16)`
 * `(15 : Fin 17) >>> (2 : Fin 17) = (3 : Fin 17)`
-/
noncomputable def c124 := @Fin.shiftRight

/--
按位与。
-/
noncomputable def c125 := @Fin.land

/--
按位或。
-/
noncomputable def c126 := @Fin.lor

/--
按位异或。
-/
noncomputable def c127 := @Fin.xor

/--
提取底层 `Nat` 值。

此函数是 `Fin.val` 的同义函数，后者是 simp 规范形。`Fin.val` 也是一个强制转换，因此 `Fin n` 类型的值会在需要时自动转换为 `Nat`。
-/
noncomputable def c128 := @Fin.toNat

/--
返回 `a` 模 `n` 所得的 `Fin n`。

假设 `NeZero n` 保证 `Fin n` 非空。
-/
noncomputable def c129 := @Fin.ofNat

/--
利用两个上界相等的证明，使受其中一个上界约束的值可用于另一个上界。

换言之，当 `eq : n = m` 时，`Fin.cast eq i` 把 `i : Fin n` 转换为 `Fin m`。
-/
noncomputable def c130 := @Fin.cast

/--
将上界替换为另一个适合该值的上界。

即使不知道具体值，也可利用嵌入 `i` 中的证明把它转换到更大的上界。

示例：
```lean example
example : Fin 12 := (7 : Fin 10).castLT (by decide : 7 < 12)
```
```lean example
example (i : Fin 10) : Fin 12 :=
  i.castLT <| by
    cases i; simp; omega
```
-/
noncomputable def c131 := @Fin.castLT

/--
将上界放宽为一个不小于它的上界。

另见 `Fin.castAdd`：该版本用加法表示更大的上界，而非显式的不等式证明。
-/
noncomputable def c132 := @Fin.castLE

/--
将上界放宽为一个不小于它的上界。

另见会增大上界的加法函数 `Fin.natAdd` 和 `Fin.addNat`，以及使用显式不等式证明的版本 `Fin.castLE`。
-/
noncomputable def c133 := @Fin.castAdd

/--
将上界放宽一。
-/
noncomputable def c134 := @Fin.castSucc

/--
把一个值替换为它与该类型最大值之差。

把 `Fin n` 的值看作序列 `0`、`1`、…、`n-2`、`n-1`，`Fin.rev` 会找出反向序列中的对应元素。换言之，它把 `0` 映射到 `n-1`，把 `1` 映射到 `n-2`，依此类推，并把 `n-1` 映射到 `0`。

示例：
 * `(5 : Fin 6).rev = (0 : Fin 6)`
 * `(0 : Fin 6).rev = (5 : Fin 6)`
 * `(2 : Fin 5).rev = (2 : Fin 5)`
-/
noncomputable def c135 := @Fin.rev

/--
类型 `Fin 0` 无元素，因此可由它导出任意结果。

这类似于 `Empty.elim`。可将其看作由编译器检查的“代码路径不可达”断言，或看作一个逻辑矛盾：由此可推出 `False`，进而推出任何命题。
-/
noncomputable def c136 := @Fin.elim0

/--
将 `Fin n` 能表示的所有值与初始值组合，从 `n - 1` 开始向右嵌套。

示例：
 * `Fin.foldr 3 (·.val + ·) (0 : Nat) = (0 : Fin 3).val + ((1 : Fin 3).val + ((2 : Fin 3).val + 0))`
-/
noncomputable def c137 := @Fin.foldr

/--
在 `Fin n` 上自右向左折叠单子函数，从 `n-1` 开始。

步骤顺序如下：
```
Fin.foldrM n f xₙ = do
  let xₙ₋₁ ← f (n-1) xₙ
  let xₙ₋₂ ← f (n-2) xₙ₋₁
  ...
  let x₀ ← f 0 x₁
  pure x₀
```
-/
noncomputable def c138 := @Fin.foldrM

/--
将 `Fin n` 能表示的所有值与初始值组合，从 `0` 开始向左嵌套。

示例：
 * `Fin.foldl 3 (· + ·.val) (0 : Nat) = ((0 + (0 : Fin 3).val) + (1 : Fin 3).val) + (2 : Fin 3).val`
-/
noncomputable def c139 := @Fin.foldl

/--
在 `Fin n` 的所有值上自左向右折叠单子函数，从 `0` 开始。

步骤顺序如下：
```
Fin.foldlM n f x₀ = do
  let x₁ ← f x₀ 0
  let x₂ ← f x₁ 1
  ...
  let xₙ ← f xₙ₋₁ (n-1)
  pure xₙ
```
-/
noncomputable def c140 := @Fin.foldlM

/--
把依赖索引的函数应用于所有小于给定上界 `n` 的值，从 `0` 和一个累加器开始。

具体而言，`Fin.hIterate P init f` 等于
```lean
  init |> f 0 |> f 1 |> ... |> f (n-1)
```

关于 `Fin.hIterate` 的定理可用一般定理 `Fin.hIterate_elim` 或其他更专门的定理证明。

`Fin.hIterateFrom` 是一个变体，它接受自定义起始值而不总是从 `0` 开始。
-/
noncomputable def c141 := @Fin.hIterate

/--
把依赖索引的函数 `f` 应用于 `[i:n]` 中的所有值，从 `i` 和初始累加器 `a` 开始。

具体而言，`Fin.hIterateFrom P f i a` 等于
```lean
  a |> f i |> f (i + 1) |> ... |> f (n - 1)
```

关于 `Fin.hIterateFrom` 的定理可用一般定理 `Fin.hIterateFrom_elim` 或其他更专门的定理证明。

`Fin.hIterate` 是一个始终从 `0` 开始的变体。
-/
noncomputable def c142 := @Fin.hIterateFrom

/--
对底层 `Nat` 值归纳，以证明 `Fin (n + 1)` 中的一个命题。

归纳包含：
 * `zero` 是基本情形，证明 `motive 0`；
 * `succ` 是归纳步骤：假设动机对 `i : Fin n` 成立（提升到 `Fin (n + 1)` 时使用 `Fin.castSucc`），并证明它对 `i.succ` 成立。

`Fin.inductionOn` 是把 `Fin` 作为第一个参数的版本；`Fin.cases` 是相应的分类讨论算子；`Fin.reverseInduction` 则从最大值而非 `0` 开始。
-/
noncomputable def c143 := @Fin.induction

/--
对底层 `Nat` 值归纳，以证明 `Fin (n + 1)` 中的一个命题。

归纳包含：
 * `zero` 是基本情形，证明 `motive 0`；
 * `succ` 是归纳步骤：假设动机对 `i : Fin n` 成立（提升到 `Fin (n + 1)` 时使用 `Fin.castSucc`），并证明它对 `i.succ` 成立。

`Fin.induction` 是把 `Fin` 作为最后一个参数的版本。
-/
noncomputable def c144 := @Fin.inductionOn

/--
对底层 `Nat` 值作反向归纳，以证明 `Fin (n + 1)` 中的一个命题。

归纳包含：
* `last` 是基本情形，证明 `motive (Fin.last n)`；
* `cast` 是归纳步骤：假设动机对 `(j : Fin n).succ` 成立，并证明它对前驱 `j.castSucc` 成立。

`Fin.induction` 是非反向的归纳原理。
-/
noncomputable def c145 := @Fin.reverseInduction

/--
对底层 `Nat` 值分类讨论，以证明 `Fin (n + 1)` 中的一个命题。

两种情形为：
* `zero`，用于值形如 `(0 : Fin (n + 1))` 时；
* `succ`，用于值形如 `(j : Fin n).succ` 时。

相应的归纳原理是 `Fin.induction`。
-/
noncomputable def c146 := @Fin.cases

/--
对底层 `Nat` 值分类讨论，以证明 `Fin (n + 1)` 中的命题：检查该值是可表示的最大值，还是某个值的前驱。

两种情形为：
 * `last`，用于值为 `Fin.last n` 时；
 * `cast`，用于值形如 `(j : Fin n).succ` 时。

相应的归纳原理是 `Fin.reverseInduction`。
-/
noncomputable def c147 := @Fin.lastCases

/--
`i : Fin (m + n)` 的分类讨论算子，分别处理 `i < m` 与 `m ≤ i < m + n` 两种情形。

第一种情形 `i < m` 由 `left` 处理；此时 `i` 可表示为 `Fin.castAdd n (j : Fin m)`。

第二种情形 `m ≤ i < m + n` 由 `right` 处理；此时 `i` 可表示为 `Fin.natAdd m (j : Fin n)`。
-/
noncomputable def c148 := @Fin.addCases

/--
`Fin` 的归纳原理，把给定的 `i : Fin n` 看作连续应用 `i` 次 `Fin.succ` 所得。

归纳情形为：
 * `zero`：证明动机对 `(0 : Fin (n + 1))` 成立，这适用于所有上界 `n`；
 * `succ`：证明动机对 `Fin.succ` 应用于任意 `Fin` 后的值成立，这适用于任意上界 `n`。

与 `Fin.induction` 不同，这里的动机会量化上界，且上界随每个归纳步骤变化。`Fin.succRecOn` 是把 `Fin` 参数放在第一位的版本。
-/
noncomputable def c149 := @Fin.succRec

/--
`Fin` 的归纳原理，把给定的 `i : Fin n` 看作连续应用 `i` 次 `Fin.succ` 所得。

归纳情形为：
 * `zero`：证明动机对 `(0 : Fin (n + 1))` 成立，这适用于所有上界 `n`；
 * `succ`：证明动机对 `Fin.succ` 应用于任意 `Fin` 后的值成立，这适用于任意上界 `n`。

与 `Fin.induction` 不同，这里的动机会量化上界，且上界随每个归纳步骤变化。`Fin.succRec` 是把 `Fin` 参数放在最后一位的版本。
-/
noncomputable def c150 := @Fin.succRecOn

end Manual.ZhDocString.Ch19Ch20.G5
