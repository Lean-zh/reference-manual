import Manual.Monads

open Verso.Genre Manual

#doc (Manual) "第 18 章中文动态文档冒烟测试" =>
%%%
file := "Chapter 18 ZhDocString Smoke Test"
tag := "chapter-18-zhdocstring-smoke"
%%%

{zhdocstring Functor Manual.ZhDocString.Monads.Core.Functor}

{zhdocstring Pure Manual.ZhDocString.Monads.Core.Pure}

{zhdocstring Seq Manual.ZhDocString.Monads.Core.Seq}

{zhdocstring SeqLeft Manual.ZhDocString.Monads.Core.SeqLeft}

{zhdocstring SeqRight Manual.ZhDocString.Monads.Core.SeqRight}

{zhdocstring Applicative Manual.ZhDocString.Monads.Core.Applicative}

{zhdocstring Alternative Manual.ZhDocString.Monads.Core.Alternative}

{zhdocstring Bind Manual.ZhDocString.Monads.Core.Bind}

{zhdocstring Monad Manual.ZhDocString.Monads.Core.Monad}

{zhdocstring discard Manual.ZhDocString.Monads.Core.discard}

{zhdocstring guard Manual.ZhDocString.Monads.Core.guard}

{zhdocstring optional Manual.ZhDocString.Monads.Core.optional}

{zhdocstring andM Manual.ZhDocString.Monads.Core.andM}

{zhdocstring orM Manual.ZhDocString.Monads.Core.orM}

{zhdocstring notM Manual.ZhDocString.Monads.Core.notM}

{zhdocstring Bind.kleisliRight Manual.ZhDocString.Monads.Core.Bind.kleisliRight}

{zhdocstring Bind.kleisliLeft Manual.ZhDocString.Monads.Core.Bind.kleisliLeft}

{zhdocstring Functor.mapRev Manual.ZhDocString.Monads.Core.Functor.mapRev}

{zhdocstring Bind.bindLeft Manual.ZhDocString.Monads.Core.Bind.bindLeft}

{zhdocstring LawfulFunctor Manual.ZhDocString.Monads.Core.LawfulFunctor}

{zhdocstring LawfulApplicative Manual.ZhDocString.Monads.Core.LawfulApplicative}

{zhdocstring LawfulMonad Manual.ZhDocString.Monads.Core.LawfulMonad}

{zhdocstring LawfulMonad.mk' Manual.ZhDocString.Monads.Core.LawfulMonad.mk'}

{zhdocstring MonadLift Manual.ZhDocString.Monads.Core.MonadLift}

{zhdocstring MonadLiftT Manual.ZhDocString.Monads.Core.MonadLiftT}

{zhOptionDocs autoLift Manual.ZhDocString.Monads.Core.autoLift}

{zhdocstring MonadFunctor Manual.ZhDocString.Monads.Core.MonadFunctor}

{zhdocstring MonadFunctorT Manual.ZhDocString.Monads.Core.MonadFunctorT}

{zhdocstring MonadControl Manual.ZhDocString.Monads.Core.MonadControl}

{zhdocstring MonadControlT Manual.ZhDocString.Monads.Core.MonadControlT}

{zhdocstring control Manual.ZhDocString.Monads.Core.control}

{zhdocstring controlAt Manual.ZhDocString.Monads.Core.controlAt}

{zhdocstring ForIn Manual.ZhDocString.Monads.Core.ForIn}

{zhdocstring ForIn' Manual.ZhDocString.Monads.Core.ForIn'}

{zhdocstring ForInStep Manual.ZhDocString.Monads.Core.ForInStep}

{zhdocstring ForInStep.value Manual.ZhDocString.Monads.Core.ForInStep.value}

{zhdocstring ForM Manual.ZhDocString.Monads.Core.ForM}

{zhdocstring ForM.forIn Manual.ZhDocString.Monads.Core.ForM.forIn}

{zhdocstring EStateM Manual.ZhDocString.Monads.Except.eStateM}

{zhdocstring EStateM.Result Manual.ZhDocString.Monads.Except.EStateM.Result}

{zhdocstring EStateM.run Manual.ZhDocString.Monads.Except.EStateM.run}

{zhdocstring EStateM.run' Manual.ZhDocString.Monads.Except.EStateM.run'}

{zhdocstring EStateM.adaptExcept Manual.ZhDocString.Monads.Except.EStateM.adaptExcept}

{zhdocstring EStateM.fromStateM Manual.ZhDocString.Monads.Except.EStateM.fromStateM}

{zhdocstring EStateM.Backtrackable Manual.ZhDocString.Monads.Except.EStateM.Backtrackable}

{zhdocstring EStateM.nonBacktrackable Manual.ZhDocString.Monads.Except.EStateM.nonBacktrackable}

{zhdocstring EStateM.map Manual.ZhDocString.Monads.Except.EStateM.map}

{zhdocstring EStateM.pure Manual.ZhDocString.Monads.Except.EStateM.pure}

{zhdocstring EStateM.bind Manual.ZhDocString.Monads.Except.EStateM.bind}

{zhdocstring EStateM.orElse Manual.ZhDocString.Monads.Except.EStateM.orElse}

{zhdocstring EStateM.orElse' Manual.ZhDocString.Monads.Except.EStateM.orElse'}

{zhdocstring EStateM.seqRight Manual.ZhDocString.Monads.Except.EStateM.seqRight}

{zhdocstring EStateM.tryCatch Manual.ZhDocString.Monads.Except.EStateM.tryCatch}

{zhdocstring EStateM.throw Manual.ZhDocString.Monads.Except.EStateM.throw}

{zhdocstring EStateM.get Manual.ZhDocString.Monads.Except.EStateM.get}

{zhdocstring EStateM.set Manual.ZhDocString.Monads.Except.EStateM.set}

{zhdocstring EStateM.modifyGet Manual.ZhDocString.Monads.Except.EStateM.modifyGet}

{zhdocstring Except Manual.ZhDocString.Monads.Except.Except}

{zhdocstring Except.pure Manual.ZhDocString.Monads.Except.Except.pure}

{zhdocstring Except.bind Manual.ZhDocString.Monads.Except.Except.bind}

{zhdocstring Except.map Manual.ZhDocString.Monads.Except.Except.map}

{zhdocstring Except.mapError Manual.ZhDocString.Monads.Except.Except.mapError}

{zhdocstring Except.tryCatch Manual.ZhDocString.Monads.Except.Except.tryCatch}

{zhdocstring Except.orElseLazy Manual.ZhDocString.Monads.Except.Except.orElseLazy}

{zhdocstring Except.isOk Manual.ZhDocString.Monads.Except.Except.isOk}

{zhdocstring Except.toOption Manual.ZhDocString.Monads.Except.Except.toOption}

{zhdocstring Except.toBool Manual.ZhDocString.Monads.Except.Except.toBool}

{zhdocstring MonadExcept Manual.ZhDocString.Monads.Except.MonadExcept}

{zhdocstring MonadExcept.ofExcept Manual.ZhDocString.Monads.Except.MonadExcept.ofExcept}

{zhdocstring MonadExcept.orElse Manual.ZhDocString.Monads.Except.MonadExcept.orElse}

{zhdocstring MonadExcept.orelse' Manual.ZhDocString.Monads.Except.MonadExcept.orelse'}

{zhdocstring MonadExceptOf Manual.ZhDocString.Monads.Except.MonadExceptOf}

{zhdocstring throwThe Manual.ZhDocString.Monads.Except.throwThe}

{zhdocstring tryCatchThe Manual.ZhDocString.Monads.Except.tryCatchThe}

{zhdocstring MonadFinally Manual.ZhDocString.Monads.Except.MonadFinally}

{zhdocstring ExceptT Manual.ZhDocString.Monads.Except.exceptT}

{zhdocstring ExceptT.lift Manual.ZhDocString.Monads.Except.ExceptT.lift}

{zhdocstring ExceptT.run Manual.ZhDocString.Monads.Except.ExceptT.run}

{zhdocstring ExceptT.pure Manual.ZhDocString.Monads.Except.ExceptT.pure}

{zhdocstring ExceptT.bind Manual.ZhDocString.Monads.Except.ExceptT.bind}

{zhdocstring ExceptT.bindCont Manual.ZhDocString.Monads.Except.ExceptT.bindCont}

{zhdocstring ExceptT.tryCatch Manual.ZhDocString.Monads.Except.ExceptT.tryCatch}

{zhdocstring ExceptT.mk Manual.ZhDocString.Monads.Except.ExceptT.mk}

{zhdocstring ExceptT.map Manual.ZhDocString.Monads.Except.ExceptT.map}

{zhdocstring ExceptT.adapt Manual.ZhDocString.Monads.Except.ExceptT.adapt}

{zhdocstring ExceptCpsT Manual.ZhDocString.Monads.Except.exceptCpsT}

{zhdocstring ExceptCpsT.runCatch Manual.ZhDocString.Monads.Except.ExceptCpsT.runCatch}

{zhdocstring ExceptCpsT.runK Manual.ZhDocString.Monads.Except.ExceptCpsT.runK}

{zhdocstring ExceptCpsT.run Manual.ZhDocString.Monads.Except.ExceptCpsT.run}

{zhdocstring ExceptCpsT.lift Manual.ZhDocString.Monads.Except.ExceptCpsT.lift}

{zhdocstring Id ZhDoc.Monads.State.Id}

{zhdocstring Id.run ZhDoc.Monads.State.Id.run}

{zhdocstring OptionT ZhDoc.Monads.State.OptionT}

{zhdocstring OptionT.run ZhDoc.Monads.State.OptionT.run}

{zhdocstring OptionT.lift ZhDoc.Monads.State.OptionT.lift}

{zhdocstring OptionT.mk ZhDoc.Monads.State.OptionT.mk}

{zhdocstring OptionT.pure ZhDoc.Monads.State.OptionT.pure}

{zhdocstring OptionT.bind ZhDoc.Monads.State.OptionT.bind}

{zhdocstring OptionT.fail ZhDoc.Monads.State.OptionT.fail}

{zhdocstring OptionT.orElse ZhDoc.Monads.State.OptionT.orElse}

{zhdocstring OptionT.tryCatch ZhDoc.Monads.State.OptionT.tryCatch}

{zhdocstring MonadReader ZhDoc.Monads.State.MonadReader}

{zhdocstring MonadReaderOf ZhDoc.Monads.State.MonadReaderOf}

{zhdocstring readThe ZhDoc.Monads.State.readThe}

{zhdocstring MonadWithReader ZhDoc.Monads.State.MonadWithReader}

{zhdocstring MonadWithReaderOf ZhDoc.Monads.State.MonadWithReaderOf}

{zhdocstring withTheReader ZhDoc.Monads.State.withTheReader}

{zhdocstring ReaderT ZhDoc.Monads.State.ReaderT}

{zhdocstring ReaderM ZhDoc.Monads.State.ReaderM}

{zhdocstring ReaderT.run ZhDoc.Monads.State.ReaderT.run}

{zhdocstring ReaderT.read ZhDoc.Monads.State.ReaderT.read}

{zhdocstring ReaderT.adapt ZhDoc.Monads.State.ReaderT.adapt}

{zhdocstring ReaderT.pure ZhDoc.Monads.State.ReaderT.pure}

{zhdocstring ReaderT.bind ZhDoc.Monads.State.ReaderT.bind}

{zhdocstring ReaderT.orElse ZhDoc.Monads.State.ReaderT.orElse}

{zhdocstring ReaderT.failure ZhDoc.Monads.State.ReaderT.failure}

{zhdocstring MonadState ZhDoc.Monads.State.MonadState}

{zhdocstring get ZhDoc.Monads.State.get}

{zhdocstring modify ZhDoc.Monads.State.modify}

{zhdocstring modifyGet ZhDoc.Monads.State.modifyGet}

{zhdocstring getModify ZhDoc.Monads.State.getModify}

{zhdocstring MonadStateOf ZhDoc.Monads.State.MonadStateOf}

{zhdocstring getThe ZhDoc.Monads.State.getThe}

{zhdocstring modifyThe ZhDoc.Monads.State.modifyThe}

{zhdocstring modifyGetThe ZhDoc.Monads.State.modifyGetThe}

{zhdocstring StateM ZhDoc.Monads.State.StateM}

{zhdocstring StateT ZhDoc.Monads.State.StateT}

{zhdocstring StateT.run ZhDoc.Monads.State.StateT.run}

{zhdocstring StateT.get ZhDoc.Monads.State.StateT.get}

{zhdocstring StateT.set ZhDoc.Monads.State.StateT.set}

{zhdocstring StateT.orElse ZhDoc.Monads.State.StateT.orElse}

{zhdocstring StateT.failure ZhDoc.Monads.State.StateT.failure}

{zhdocstring StateT.run' ZhDoc.Monads.State.StateT.run'}

{zhdocstring StateT.bind ZhDoc.Monads.State.StateT.bind}

{zhdocstring StateT.modifyGet ZhDoc.Monads.State.StateT.modifyGet}

{zhdocstring StateT.lift ZhDoc.Monads.State.StateT.lift}

{zhdocstring StateT.map ZhDoc.Monads.State.StateT.map}

{zhdocstring StateT.pure ZhDoc.Monads.State.StateT.pure}

{zhdocstring StateCpsT ZhDoc.Monads.State.StateCpsT}

{zhdocstring StateCpsT.lift ZhDoc.Monads.State.StateCpsT.lift}

{zhdocstring StateCpsT.runK ZhDoc.Monads.State.StateCpsT.runK}

{zhdocstring StateCpsT.run' ZhDoc.Monads.State.StateCpsT.run'}

{zhdocstring StateCpsT.run ZhDoc.Monads.State.StateCpsT.run}

{zhdocstring STWorld ZhDoc.Monads.State.STWorld}

{zhdocstring StateRefT' ZhDoc.Monads.State.StateRefT'}

{zhdocstring StateRefT'.get ZhDoc.Monads.State.StateRefT'.get}

{zhdocstring StateRefT'.set ZhDoc.Monads.State.StateRefT'.set}

{zhdocstring StateRefT'.modifyGet ZhDoc.Monads.State.StateRefT'.modifyGet}

{zhdocstring StateRefT'.run ZhDoc.Monads.State.StateRefT'.run}

{zhdocstring StateRefT'.run' ZhDoc.Monads.State.StateRefT'.run'}

{zhdocstring StateRefT'.lift ZhDoc.Monads.State.StateRefT'.lift}
