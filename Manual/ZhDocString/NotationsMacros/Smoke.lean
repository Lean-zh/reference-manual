import Manual.NotationsMacros

open Verso.Genre Manual

#doc (Manual) "第 23 章中文动态文档冒烟测试" =>
%%%
file := "Chapter 23 ZhDocString Smoke Test"
tag := "chapter-23-zhdocstring-smoke"
%%%

{zhdocstring Lean.MacroM Manual.ZhDocString.NotationsMacros.Core.MacroM}

{zhdocstring Lean.Macro.expandMacro? Manual.ZhDocString.NotationsMacros.Core.Macro.expandMacro?}

{zhdocstring Lean.Macro.trace Manual.ZhDocString.NotationsMacros.Core.Macro.trace}

{zhdocstring Lean.Macro.throwUnsupported Manual.ZhDocString.NotationsMacros.Core.Macro.throwUnsupported}

{zhdocstring Lean.Macro.Exception.unsupportedSyntax Manual.ZhDocString.NotationsMacros.Core.Macro.Exception.unsupportedSyntax}

{zhdocstring Lean.Macro.throwError Manual.ZhDocString.NotationsMacros.Core.Macro.throwError}

{zhdocstring Lean.Macro.throwErrorAt Manual.ZhDocString.NotationsMacros.Core.Macro.throwErrorAt}

{zhdocstring Lean.Macro.withFreshMacroScope Manual.ZhDocString.NotationsMacros.Core.Macro.withFreshMacroScope}

{zhdocstring Lean.Macro.addMacroScope Manual.ZhDocString.NotationsMacros.Core.Macro.addMacroScope}

{zhdocstring Lean.Macro.hasDecl Manual.ZhDocString.NotationsMacros.Core.Macro.hasDecl}

{zhdocstring Lean.Macro.getCurrNamespace Manual.ZhDocString.NotationsMacros.Core.Macro.getCurrNamespace}

{zhdocstring Lean.Macro.resolveNamespace Manual.ZhDocString.NotationsMacros.Core.Macro.resolveNamespace}

{zhdocstring Lean.Macro.resolveGlobalName Manual.ZhDocString.NotationsMacros.Core.Macro.resolveGlobalName}

{zhdocstring Lean.PrettyPrinter.Unexpander Manual.ZhDocString.NotationsMacros.Core.PrettyPrinter.Unexpander}

{zhdocstring Lean.PrettyPrinter.UnexpandM Manual.ZhDocString.NotationsMacros.Core.PrettyPrinter.UnexpandM}

{zhOptionDocs backward.do.legacy ZhDoc.NotationsMacros.Do.backwardDoLegacy}

{zhdocstring Lean.Elab.Do.Context ZhDoc.NotationsMacros.Do.Context}

{zhdocstring Lean.Elab.Do.MonadInfo ZhDoc.NotationsMacros.Do.MonadInfo}

{zhdocstring Lean.Elab.Do.CodeLiveness ZhDoc.NotationsMacros.Do.CodeLiveness}

{zhdocstring Lean.Elab.Do.ContInfoRef.toContInfo ZhDoc.NotationsMacros.Do.ContInfoRef.toContInfo}

{zhdocstring Lean.Elab.Do.ContInfo ZhDoc.NotationsMacros.Do.ContInfo}

{zhdocstring Lean.Elab.Do.DoOpsRef.toDoOps ZhDoc.NotationsMacros.Do.DoOpsRef.toDoOps}

{zhdocstring Lean.Elab.Do.DoOps ZhDoc.NotationsMacros.Do.DoOps}

{zhdocstring Lean.Elab.Do.DoElab ZhDoc.NotationsMacros.Do.DoElab}

{zhincludeDocstring Lean.Elab.Do.doElemElabAttribute ZhDoc.NotationsMacros.Do.doElemElabAttribute}

{zhdocstring Lean.Elab.Do.elabDoElem ZhDoc.NotationsMacros.Do.elabDoElem}

{zhdocstring Lean.Elab.Do.elabDoSeq ZhDoc.NotationsMacros.Do.elabDoSeq}

{zhdocstring Lean.Elab.Do.elabDoElems1 ZhDoc.NotationsMacros.Do.elabDoElems1}

{zhdocstring Lean.Elab.Do.mkMonadApp ZhDoc.NotationsMacros.Do.mkMonadApp}

{zhdocstring Lean.Elab.Do.mkPureApp ZhDoc.NotationsMacros.Do.mkPureApp}

{zhdocstring Lean.Elab.Do.mkBindApp ZhDoc.NotationsMacros.Do.mkBindApp}

{zhdocstring Lean.Elab.Do.mkPUnitUnit ZhDoc.NotationsMacros.Do.mkPUnitUnit}

{zhdocstring Lean.Elab.Do.DoElemCont ZhDoc.NotationsMacros.Do.DoElemCont}

{zhdocstring Lean.Elab.Do.DoElemContKind ZhDoc.NotationsMacros.Do.DoElemContKind}

{zhdocstring Lean.Elab.Do.DoElemCont.ensureUnit ZhDoc.NotationsMacros.Do.DoElemCont.ensureUnit}

{zhdocstring Lean.Elab.Do.DoElemCont.ensureUnitAt ZhDoc.NotationsMacros.Do.DoElemCont.ensureUnitAt}

{zhdocstring Lean.Elab.Do.DoElemCont.ensureHasTypeAt ZhDoc.NotationsMacros.Do.DoElemCont.ensureHasTypeAt}

{zhdocstring Lean.Elab.Do.DoElemCont.continueWithUnit ZhDoc.NotationsMacros.Do.DoElemCont.continueWithUnit}

{zhdocstring Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode ZhDoc.NotationsMacros.Do.DoElemCont.elabAsSyntacticallyDeadCode}

{zhdocstring Lean.Elab.Do.DoElemCont.mkBindUnlessPure ZhDoc.NotationsMacros.Do.DoElemCont.mkBindUnlessPure}

{zhdocstring Lean.Elab.Do.DoElemCont.withDuplicableCont ZhDoc.NotationsMacros.Do.DoElemCont.withDuplicableCont}

{zhdocstring Lean.Elab.Do.getReturnCont ZhDoc.NotationsMacros.Do.getReturnCont}

{zhdocstring Lean.Elab.Do.getBreakCont ZhDoc.NotationsMacros.Do.getBreakCont}

{zhdocstring Lean.Elab.Do.getContinueCont ZhDoc.NotationsMacros.Do.getContinueCont}

{zhdocstring Lean.Elab.Do.enterLoopBody ZhDoc.NotationsMacros.Do.enterLoopBody}

{zhincludeDocstring Lean.Elab.Do.controlInfoElemAttribute ZhDoc.NotationsMacros.Do.controlInfoElemAttribute}

{zhdocstring Lean.Elab.Do.ControlInfoHandler ZhDoc.NotationsMacros.Do.ControlInfoHandler}

{zhdocstring Lean.Elab.Do.ControlInfo ZhDoc.NotationsMacros.Do.ControlInfo}

{zhdocstring Lean.Elab.Do.ControlInfo.pure ZhDoc.NotationsMacros.Do.ControlInfo.pure}

{zhdocstring Lean.Elab.Do.ControlInfo.empty ZhDoc.NotationsMacros.Do.ControlInfo.empty}

{zhdocstring Lean.Elab.Do.ControlInfo.sequence ZhDoc.NotationsMacros.Do.ControlInfo.sequence}

{zhdocstring Lean.Elab.Do.ControlInfo.alternative ZhDoc.NotationsMacros.Do.ControlInfo.alternative}

{zhdocstring Lean.Elab.Do.inferControlInfoElem ZhDoc.NotationsMacros.Do.inferControlInfoElem}

{zhdocstring Lean.Elab.Do.inferControlInfoSeq ZhDoc.NotationsMacros.Do.inferControlInfoSeq}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofElem ZhDoc.NotationsMacros.Do.InferControlInfo.ofElem}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofSeq ZhDoc.NotationsMacros.Do.InferControlInfo.ofSeq}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofOptionSeq ZhDoc.NotationsMacros.Do.InferControlInfo.ofOptionSeq}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofLetOrReassign ZhDoc.NotationsMacros.Do.InferControlInfo.ofLetOrReassign}

{zhdocstring Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow ZhDoc.NotationsMacros.Do.InferControlInfo.ofLetOrReassignArrow}

{zhdocstring Lean.Elab.Do.MutVar ZhDoc.NotationsMacros.Do.MutVar}

{zhdocstring Lean.Elab.Do.declareMutVar ZhDoc.NotationsMacros.Do.declareMutVar}

{zhdocstring Lean.Elab.Do.declareMutVars ZhDoc.NotationsMacros.Do.declareMutVars}

{zhdocstring Lean.Elab.Do.throwUnlessMutVarDeclared ZhDoc.NotationsMacros.Do.throwUnlessMutVarDeclared}

{zhdocstring Lean.Elab.Do.throwUnlessMutVarsDeclared ZhDoc.NotationsMacros.Do.throwUnlessMutVarsDeclared}

{zhdocstring Lean.Elab.Do.EffectForwarder ZhDoc.NotationsMacros.Do.EffectForwarder}

{zhdocstring Lean.Elab.Do.EffectForwarder.ofCont ZhDoc.NotationsMacros.Do.EffectForwarder.ofCont}

{zhdocstring Lean.Elab.Do.EffectForwarder.lift ZhDoc.NotationsMacros.Do.EffectForwarder.lift}

{zhdocstring Lean.Elab.Do.EffectForwarder.restoreCont ZhDoc.NotationsMacros.Do.EffectForwarder.restoreCont}

{zhdocstring Lean.Syntax ZhDoc.NotationsMacros.Syntax}

{zhdocstring Lean.Syntax.Preresolved ZhDoc.NotationsMacros.Syntax.Preresolved}

{zhdocstring Lean.SyntaxNodeKind ZhDoc.NotationsMacros.SyntaxNodeKind}

{zhdocstring Lean.Syntax.isOfKind ZhDoc.NotationsMacros.Syntax.isOfKind}

{zhdocstring Lean.Syntax.getKind ZhDoc.NotationsMacros.Syntax.getKind}

{zhdocstring Lean.Syntax.setKind ZhDoc.NotationsMacros.Syntax.setKind}

{zhdocstring Lean.identKind ZhDoc.NotationsMacros.identKind}

{zhdocstring Lean.strLitKind ZhDoc.NotationsMacros.strLitKind}

{zhdocstring Lean.interpolatedStrKind ZhDoc.NotationsMacros.interpolatedStrKind}

{zhdocstring Lean.interpolatedStrLitKind ZhDoc.NotationsMacros.interpolatedStrLitKind}

{zhdocstring Lean.charLitKind ZhDoc.NotationsMacros.charLitKind}

{zhdocstring Lean.numLitKind ZhDoc.NotationsMacros.numLitKind}

{zhdocstring Lean.scientificLitKind ZhDoc.NotationsMacros.scientificLitKind}

{zhdocstring Lean.nameLitKind ZhDoc.NotationsMacros.nameLitKind}

{zhdocstring Lean.fieldIdxKind ZhDoc.NotationsMacros.fieldIdxKind}

{zhdocstring Lean.groupKind ZhDoc.NotationsMacros.groupKind}

{zhdocstring Lean.nullKind ZhDoc.NotationsMacros.nullKind}

{zhdocstring Lean.choiceKind ZhDoc.NotationsMacros.choiceKind}

{zhdocstring Lean.hygieneInfoKind ZhDoc.NotationsMacros.hygieneInfoKind}

{zhdocstring Lean.SourceInfo ZhDoc.NotationsMacros.SourceInfo}

{zhdocstring Lean.TSyntax ZhDoc.NotationsMacros.TSyntax}

{zhdocstring Lean.SyntaxNodeKinds ZhDoc.NotationsMacros.SyntaxNodeKinds}

{zhdocstring Lean.TSyntaxArray ZhDoc.NotationsMacros.TSyntaxArray}

{zhdocstring Lean.TSyntaxArray.raw ZhDoc.NotationsMacros.TSyntaxArray.raw}

{zhdocstring Lean.Syntax.TSepArray ZhDoc.NotationsMacros.Syntax.TSepArray}

{zhdocstring Lean.Syntax.TSepArray.getElems ZhDoc.NotationsMacros.Syntax.TSepArray.getElems}

{zhdocstring Lean.Syntax.TSepArray.elemsAndSeps ZhDoc.NotationsMacros.Syntax.TSepArray.elemsAndSeps}

{zhdocstring Lean.Syntax.TSepArray.ofElems ZhDoc.NotationsMacros.Syntax.TSepArray.ofElems}

{zhdocstring Lean.Syntax.TSepArray.push ZhDoc.NotationsMacros.Syntax.TSepArray.push}

{zhdocstring Lean.Term ZhDoc.NotationsMacros.Syntax.Term}

{zhdocstring Lean.Command ZhDoc.NotationsMacros.Syntax.Command}

{zhdocstring Lean.Syntax.Level ZhDoc.NotationsMacros.Syntax.Level}

{zhdocstring Lean.Syntax.Tactic ZhDoc.NotationsMacros.Syntax.Tactic}

{zhdocstring Lean.Prec ZhDoc.NotationsMacros.Syntax.Prec}

{zhdocstring Lean.Prio ZhDoc.NotationsMacros.Syntax.Prio}

{zhdocstring Lean.Ident ZhDoc.NotationsMacros.Syntax.Ident}

{zhdocstring Lean.StrLit ZhDoc.NotationsMacros.Syntax.StrLit}

{zhdocstring Lean.CharLit ZhDoc.NotationsMacros.Syntax.CharLit}

{zhdocstring Lean.NameLit ZhDoc.NotationsMacros.Syntax.NameLit}

{zhdocstring Lean.NumLit ZhDoc.NotationsMacros.Syntax.NumLit}

{zhdocstring Lean.ScientificLit ZhDoc.NotationsMacros.Syntax.ScientificLit}

{zhdocstring Lean.HygieneInfo ZhDoc.NotationsMacros.Syntax.HygieneInfo}

{zhdocstring Lean.mkIdent ZhDoc.NotationsMacros.mkIdent}

{zhdocstring Lean.mkIdentFrom ZhDoc.NotationsMacros.mkIdentFrom}

{zhdocstring Lean.mkIdentFromRef ZhDoc.NotationsMacros.mkIdentFromRef}

{zhdocstring Lean.mkCIdent ZhDoc.NotationsMacros.mkCIdent}

{zhdocstring Lean.mkCIdentFrom ZhDoc.NotationsMacros.mkCIdentFrom}

{zhdocstring Lean.mkCIdentFromRef ZhDoc.NotationsMacros.mkCIdentFromRef}

{zhdocstring Lean.Syntax.mkApp ZhDoc.NotationsMacros.Syntax.mkApp}

{zhdocstring Lean.Syntax.mkCApp ZhDoc.NotationsMacros.Syntax.mkCApp}

{zhdocstring Lean.Syntax.mkLit ZhDoc.NotationsMacros.Syntax.mkLit}

{zhdocstring Lean.Syntax.mkCharLit ZhDoc.NotationsMacros.Syntax.mkCharLit}

{zhdocstring Lean.Syntax.mkStrLit ZhDoc.NotationsMacros.Syntax.mkStrLit}

{zhdocstring Lean.Syntax.mkNumLit ZhDoc.NotationsMacros.Syntax.mkNumLit}

{zhdocstring Lean.Syntax.mkNatLit ZhDoc.NotationsMacros.Syntax.mkNatLit}

{zhdocstring Lean.Syntax.mkScientificLit ZhDoc.NotationsMacros.Syntax.mkScientificLit}

{zhdocstring Lean.Syntax.mkNameLit ZhDoc.NotationsMacros.Syntax.mkNameLit}

{zhdocstring Lean.mkOptionalNode ZhDoc.NotationsMacros.mkOptionalNode}

{zhdocstring Lean.mkGroupNode ZhDoc.NotationsMacros.mkGroupNode}

{zhdocstring Lean.mkHole ZhDoc.NotationsMacros.mkHole}

{zhdocstring Lean.Quote ZhDoc.NotationsMacros.Quote}

{zhdocstring Lean.TSyntax.getId ZhDoc.NotationsMacros.TSyntax.getId}

{zhdocstring Lean.TSyntax.getName ZhDoc.NotationsMacros.TSyntax.getName}

{zhdocstring Lean.TSyntax.getNat ZhDoc.NotationsMacros.TSyntax.getNat}

{zhdocstring Lean.TSyntax.getScientific ZhDoc.NotationsMacros.TSyntax.getScientific}

{zhdocstring Lean.TSyntax.getString ZhDoc.NotationsMacros.TSyntax.getString}

{zhdocstring Lean.TSyntax.getChar ZhDoc.NotationsMacros.TSyntax.getChar}

{zhdocstring Lean.TSyntax.getHygieneInfo ZhDoc.NotationsMacros.TSyntax.getHygieneInfo}

{zhdocstring Lean.Parser.LeadingIdentBehavior ZhDoc.NotationsMacros.Parser.LeadingIdentBehavior}
