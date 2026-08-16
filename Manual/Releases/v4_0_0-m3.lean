/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

set_option linter.verso.markup.codeBlock false

#doc (Manual) "Lean 4.0.0-m3 (2022-01-31)" =>
%%%
tag := "release-v4.0.0-m3"
file := "v4.0.0-m3"
%%%

````markdown
这是 Lean 4 的第三个里程碑版本，也是正式发布前计划中的最后一个里程碑版本。
自上一个里程碑以来，近 3000 次提交对系统的许多部分进行了改进和扩展，
我们如今已经接近完成为 Lean 4 设想的所有主要特性。

贡献者：
```
$ git shortlog -s -n v4.0.0-m2..v4.0.0-m3
  1719  Leonardo de Moura
   725  Sebastian Ullrich
   149  Wojciech Nawrocki
    93  Daniel Selsam
    82  Gabriel Ebner
    36  Joscha
    35  Daniel Fabian
    21  tydeu
    14  Mario Carneiro
    13  larsk21
    12  Jannis Limperg
    11  Chris Lovett
     8  Henrik Böving
     4  François G. Dorais
     4  Siddharth
     3  Joe Hendrix
     3  Scott Morrison
     3  ammkrn
     2  Josh Levine
     2  Mac
     2  Mac Malone
     2  Simon Hudon
     2  pcpthm
     1  Anders Christiansen Sørby
     1  Andrei Cheremskoy
     1  Arthur Paulino
     1  Christian Pehle
     1  Formally Verified Waffle Maker
     1  Hunter Monroe
     1  Jan Hrcek
     1  Joshua Seaton
     1  Kevin Buzzard
     1  Lorenz Leutgeb
     1  Mauricio Collares
     1  Michael Burge
     1  Paul Brinkmeier
     1  Reijo Jaakkola
     1  Severen Redwood
     1  Siddharth Bhat
     1  Tom Ball
     1  Varun Gandhi
     1  WojciechKarpiel
     1  Xavier Noria
     1  gabriel-doriath-dohler
     1  zygi
     1  Бакиновский Максим
```
````
