import Manual.ZhDocString
import VersoManual

open Verso.Genre Manual

#doc (Manual) "中文文档字符串扩展冒烟测试" =>
%%%
file := "ZhDocString Smoke Test"
tag := "zhdocstring-smoke"
%%%

{zhdocstring Quotient ZhDoc.Quotient}

{zhOptionDocs pp.match ZhDoc.Option.pp.match}
