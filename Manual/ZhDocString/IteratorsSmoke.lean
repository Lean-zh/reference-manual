import Manual.ZhDocString.Iterators

open Verso.Genre Manual
open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

set_option verso.docstring.allowMissing true

#doc (Manual) "Iterators 中文动态文档冒烟测试" =>
%%%
file := "Iterators 中文动态文档冒烟测试"
tag := "iterators-中文动态文档冒烟测试"
%%%

{zhdocstring Iter Manual.ZhDocString.Iterators.c001}

{zhdocstring IterM Manual.ZhDocString.Iterators.c002}

{zhdocstring IterStep Manual.ZhDocString.Iterators.c003}

{zhdocstring Iter.Step Manual.ZhDocString.Iterators.c004}

{zhdocstring IterM.Step Manual.ZhDocString.Iterators.c005}

{zhdocstring Iterator Manual.ZhDocString.Iterators.c006}

{zhdocstring PlausibleIterStep Manual.ZhDocString.Iterators.c007}

{zhdocstring PlausibleIterStep.yield Manual.ZhDocString.Iterators.c008}

{zhdocstring PlausibleIterStep.skip Manual.ZhDocString.Iterators.c009}

{zhdocstring PlausibleIterStep.done Manual.ZhDocString.Iterators.c010}

{zhdocstring Finite Manual.ZhDocString.Iterators.c011}

{zhdocstring Productive Manual.ZhDocString.Iterators.c012}

{zhdocstring Iter.ensureTermination Manual.ZhDocString.Iterators.c013}

{zhdocstring IterM.ensureTermination Manual.ZhDocString.Iterators.c014}

{zhdocstring IteratorAccess Manual.ZhDocString.Iterators.c015}

{zhdocstring IterM.nextAtIdx? Manual.ZhDocString.Iterators.c016}

{zhdocstring IteratorLoop Manual.ZhDocString.Iterators.c017}

{zhdocstring IteratorLoop.defaultImplementation Manual.ZhDocString.Iterators.c018}

{zhdocstring LawfulIteratorLoop Manual.ZhDocString.Iterators.c019}

{zhdocstring Std.Shrink Manual.ZhDocString.Iterators.c020}

{zhdocstring Std.Shrink.inflate Manual.ZhDocString.Iterators.c021}

{zhdocstring Std.Shrink.deflate Manual.ZhDocString.Iterators.c022}

{zhdocstring Iter.empty Manual.ZhDocString.Iterators.c023}

{zhdocstring IterM.empty Manual.ZhDocString.Iterators.c024}

{zhdocstring Iter.repeat Manual.ZhDocString.Iterators.c025}

{zhdocstring Iter.step Manual.ZhDocString.Iterators.c026}

{zhdocstring IterM.step Manual.ZhDocString.Iterators.c027}

{zhdocstring Iter.finitelyManySteps Manual.ZhDocString.Iterators.c028}

{zhdocstring IterM.finitelyManySteps Manual.ZhDocString.Iterators.c029}

{zhdocstring IterM.TerminationMeasures.Finite Manual.ZhDocString.Iterators.c030}

{zhdocstring Iter.finitelyManySkips Manual.ZhDocString.Iterators.c031}

{zhdocstring IterM.finitelyManySkips Manual.ZhDocString.Iterators.c032}

{zhdocstring IterM.TerminationMeasures.Productive Manual.ZhDocString.Iterators.c033}

{zhdocstring Iter.fold Manual.ZhDocString.Iterators.c034}

{zhdocstring Iter.foldM Manual.ZhDocString.Iterators.c035}

{zhdocstring Iter.length Manual.ZhDocString.Iterators.c036}

{zhdocstring Iter.any Manual.ZhDocString.Iterators.c037}

{zhdocstring Iter.anyM Manual.ZhDocString.Iterators.c038}

{zhdocstring Iter.all Manual.ZhDocString.Iterators.c039}

{zhdocstring Iter.allM Manual.ZhDocString.Iterators.c040}

{zhdocstring Iter.find? Manual.ZhDocString.Iterators.c041}

{zhdocstring Iter.findM? Manual.ZhDocString.Iterators.c042}

{zhdocstring Iter.findSome? Manual.ZhDocString.Iterators.c043}

{zhdocstring Iter.findSomeM? Manual.ZhDocString.Iterators.c044}

{zhdocstring Iter.atIdx? Manual.ZhDocString.Iterators.c045}

{zhdocstring Iter.atIdxSlow? Manual.ZhDocString.Iterators.c046}

{zhdocstring IterM.drain Manual.ZhDocString.Iterators.c047}

{zhdocstring IterM.fold Manual.ZhDocString.Iterators.c048}

{zhdocstring IterM.foldM Manual.ZhDocString.Iterators.c049}

{zhdocstring IterM.length Manual.ZhDocString.Iterators.c050}

{zhdocstring IterM.any Manual.ZhDocString.Iterators.c051}

{zhdocstring IterM.anyM Manual.ZhDocString.Iterators.c052}

{zhdocstring IterM.all Manual.ZhDocString.Iterators.c053}

{zhdocstring IterM.allM Manual.ZhDocString.Iterators.c054}

{zhdocstring IterM.find? Manual.ZhDocString.Iterators.c055}

{zhdocstring IterM.findM? Manual.ZhDocString.Iterators.c056}

{zhdocstring IterM.findSome? Manual.ZhDocString.Iterators.c057}

{zhdocstring IterM.findSomeM? Manual.ZhDocString.Iterators.c058}

{zhdocstring IterM.atIdx? Manual.ZhDocString.Iterators.c059}

{zhdocstring Iter.toArray Manual.ZhDocString.Iterators.c060}

{zhdocstring IterM.toArray Manual.ZhDocString.Iterators.c061}

{zhdocstring Iter.toList Manual.ZhDocString.Iterators.c062}

{zhdocstring IterM.toList Manual.ZhDocString.Iterators.c063}

{zhdocstring Iter.toListRev Manual.ZhDocString.Iterators.c064}

{zhdocstring IterM.toListRev Manual.ZhDocString.Iterators.c065}

{zhdocstring IterM.mk Manual.ZhDocString.Iterators.c066}

{zhdocstring Iter.toIterM Manual.ZhDocString.Iterators.c067}

{zhdocstring Iter.take Manual.ZhDocString.Iterators.c068}

{zhdocstring Iter.takeWhile Manual.ZhDocString.Iterators.c069}

{zhdocstring Iter.toTake Manual.ZhDocString.Iterators.c070}

{zhdocstring Iter.drop Manual.ZhDocString.Iterators.c071}

{zhdocstring Iter.dropWhile Manual.ZhDocString.Iterators.c072}

{zhdocstring Iter.stepSize Manual.ZhDocString.Iterators.c073}

{zhdocstring Iter.map Manual.ZhDocString.Iterators.c074}

{zhdocstring Iter.mapM Manual.ZhDocString.Iterators.c075}

{zhdocstring Iter.mapWithPostcondition Manual.ZhDocString.Iterators.c076}

{zhdocstring Iter.uLift Manual.ZhDocString.Iterators.c077}

{zhdocstring Iter.flatMap Manual.ZhDocString.Iterators.c078}

{zhdocstring Iter.flatMapM Manual.ZhDocString.Iterators.c079}

{zhdocstring Iter.flatMapAfter Manual.ZhDocString.Iterators.c080}

{zhdocstring Iter.flatMapAfterM Manual.ZhDocString.Iterators.c081}

{zhdocstring Iter.filter Manual.ZhDocString.Iterators.c082}

{zhdocstring Iter.filterM Manual.ZhDocString.Iterators.c083}

{zhdocstring Iter.filterWithPostcondition Manual.ZhDocString.Iterators.c084}

{zhdocstring Iter.filterMap Manual.ZhDocString.Iterators.c085}

{zhdocstring Iter.filterMapM Manual.ZhDocString.Iterators.c086}

{zhdocstring Iter.filterMapWithPostcondition Manual.ZhDocString.Iterators.c087}

{zhdocstring Iter.zip Manual.ZhDocString.Iterators.c088}

{zhdocstring Iter.attachWith Manual.ZhDocString.Iterators.c089}

{zhdocstring IterM.toIter Manual.ZhDocString.Iterators.c090}

{zhdocstring IterM.take Manual.ZhDocString.Iterators.c091}

{zhdocstring IterM.takeWhile Manual.ZhDocString.Iterators.c092}

{zhdocstring IterM.takeWhileM Manual.ZhDocString.Iterators.c093}

{zhdocstring IterM.takeWhileWithPostcondition Manual.ZhDocString.Iterators.c094}

{zhdocstring IterM.toTake Manual.ZhDocString.Iterators.c095}

{zhdocstring IterM.drop Manual.ZhDocString.Iterators.c096}

{zhdocstring IterM.dropWhile Manual.ZhDocString.Iterators.c097}

{zhdocstring IterM.dropWhileM Manual.ZhDocString.Iterators.c098}

{zhdocstring IterM.dropWhileWithPostcondition Manual.ZhDocString.Iterators.c099}

{zhdocstring IterM.stepSize Manual.ZhDocString.Iterators.c100}

{zhdocstring IterM.map Manual.ZhDocString.Iterators.c101}

{zhdocstring IterM.mapM Manual.ZhDocString.Iterators.c102}

{zhdocstring IterM.mapWithPostcondition Manual.ZhDocString.Iterators.c103}

{zhdocstring IterM.uLift Manual.ZhDocString.Iterators.c104}

{zhdocstring IterM.flatMap Manual.ZhDocString.Iterators.c105}

{zhdocstring IterM.flatMapM Manual.ZhDocString.Iterators.c106}

{zhdocstring IterM.flatMapAfter Manual.ZhDocString.Iterators.c107}

{zhdocstring IterM.flatMapAfterM Manual.ZhDocString.Iterators.c108}

{zhdocstring IterM.filter Manual.ZhDocString.Iterators.c109}

{zhdocstring IterM.filterM Manual.ZhDocString.Iterators.c110}

{zhdocstring IterM.filterWithPostcondition Manual.ZhDocString.Iterators.c111}

{zhdocstring IterM.filterMap Manual.ZhDocString.Iterators.c112}

{zhdocstring IterM.filterMapM Manual.ZhDocString.Iterators.c113}

{zhdocstring IterM.filterMapWithPostcondition Manual.ZhDocString.Iterators.c114}

{zhdocstring IterM.zip Manual.ZhDocString.Iterators.c115}

{zhdocstring IterM.attachWith Manual.ZhDocString.Iterators.c116}

{zhdocstring Iter.inductSkips Manual.ZhDocString.Iterators.c117}

{zhdocstring IterM.inductSkips Manual.ZhDocString.Iterators.c118}

{zhdocstring Iter.inductSteps Manual.ZhDocString.Iterators.c119}

{zhdocstring IterM.inductSteps Manual.ZhDocString.Iterators.c120}

{zhdocstring Std.Iterators.PostconditionT Manual.ZhDocString.Iterators.c121}

{zhdocstring Std.Iterators.PostconditionT.run Manual.ZhDocString.Iterators.c122}

{zhdocstring Std.Iterators.PostconditionT.lift Manual.ZhDocString.Iterators.c123}

{zhdocstring Std.Iterators.PostconditionT.liftWithProperty Manual.ZhDocString.Iterators.c124}

{zhdocstring Iter.IsPlausibleIndirectOutput Manual.ZhDocString.Iterators.c125}

{zhdocstring HetT Manual.ZhDocString.Iterators.c126}

{zhdocstring IterM.stepAsHetT Manual.ZhDocString.Iterators.c127}

{zhdocstring HetT.lift Manual.ZhDocString.Iterators.c128}

{zhdocstring HetT.prun Manual.ZhDocString.Iterators.c129}

{zhdocstring HetT.pure Manual.ZhDocString.Iterators.c130}

{zhdocstring HetT.map Manual.ZhDocString.Iterators.c131}

{zhdocstring HetT.pmap Manual.ZhDocString.Iterators.c132}

{zhdocstring HetT.bind Manual.ZhDocString.Iterators.c133}

{zhdocstring HetT.pbind Manual.ZhDocString.Iterators.c134}

{zhdocstring Iter.Equiv Manual.ZhDocString.Iterators.c135}

{zhdocstring IterM.Equiv Manual.ZhDocString.Iterators.c136}
