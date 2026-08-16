import Manual.BuildTools

open Verso.Genre Manual

#doc (Manual) "第 24 章中文动态文档冒烟测试" =>
%%%
file := "Chapter 24 ZhDocString Smoke Test"
tag := "chapter-24-zhdocstring-smoke"
%%%

{zhdocstring Lake.ScriptM ZhDoc.BuildTools.Lake.ScriptM}

{zhdocstring Lake.MonadLakeEnv ZhDoc.BuildTools.Lake.MonadLakeEnv}

{zhdocstring Lake.getLakeEnv ZhDoc.BuildTools.Lake.getLakeEnv}

{zhdocstring Lake.getNoCache ZhDoc.BuildTools.Lake.getNoCache}

{zhdocstring Lake.getTryCache ZhDoc.BuildTools.Lake.getTryCache}

{zhdocstring Lake.getPkgUrlMap ZhDoc.BuildTools.Lake.getPkgUrlMap}

{zhdocstring Lake.getElanToolchain ZhDoc.BuildTools.Lake.getElanToolchain}

{zhdocstring Lake.getEnvLeanPath ZhDoc.BuildTools.Lake.getEnvLeanPath}

{zhdocstring Lake.getEnvLeanSrcPath ZhDoc.BuildTools.Lake.getEnvLeanSrcPath}

{zhdocstring Lake.getEnvSharedLibPath ZhDoc.BuildTools.Lake.getEnvSharedLibPath}

{zhdocstring Lake.getElanInstall? ZhDoc.BuildTools.Lake.getElanInstall?}

{zhdocstring Lake.getElanHome? ZhDoc.BuildTools.Lake.getElanHome?}

{zhdocstring Lake.getElan? ZhDoc.BuildTools.Lake.getElan?}

{zhdocstring Lake.getLeanInstall ZhDoc.BuildTools.Lake.getLeanInstall}

{zhdocstring Lake.getLeanSysroot ZhDoc.BuildTools.Lake.getLeanSysroot}

{zhdocstring Lake.getLeanSrcDir ZhDoc.BuildTools.Lake.getLeanSrcDir}

{zhdocstring Lake.getLeanLibDir ZhDoc.BuildTools.Lake.getLeanLibDir}

{zhdocstring Lake.getLeanIncludeDir ZhDoc.BuildTools.Lake.getLeanIncludeDir}

{zhdocstring Lake.getLeanSystemLibDir ZhDoc.BuildTools.Lake.getLeanSystemLibDir}

{zhdocstring Lake.getLean ZhDoc.BuildTools.Lake.getLean}

{zhdocstring Lake.getLeanc ZhDoc.BuildTools.Lake.getLeanc}

{zhdocstring Lake.getLeanSharedLib ZhDoc.BuildTools.Lake.getLeanSharedLib}

{zhdocstring Lake.getLeanAr ZhDoc.BuildTools.Lake.getLeanAr}

{zhdocstring Lake.getLeanCc ZhDoc.BuildTools.Lake.getLeanCc}

{zhdocstring Lake.getLeanCc? ZhDoc.BuildTools.Lake.getLeanCc?}

{zhdocstring Lake.getLakeInstall ZhDoc.BuildTools.Lake.getLakeInstall}

{zhdocstring Lake.getLakeHome ZhDoc.BuildTools.Lake.getLakeHome}

{zhdocstring Lake.getLakeSrcDir ZhDoc.BuildTools.Lake.getLakeSrcDir}

{zhdocstring Lake.getLakeLibDir ZhDoc.BuildTools.Lake.getLakeLibDir}

{zhdocstring Lake.getLake ZhDoc.BuildTools.Lake.getLake}

{zhdocstring Lake.MonadWorkspace ZhDoc.BuildTools.Lake.MonadWorkspace}

{zhdocstring Lake.getRootPackage ZhDoc.BuildTools.Lake.getRootPackage}

{zhdocstring Lake.findPackageByName? ZhDoc.BuildTools.Lake.findPackageByName?}

{zhdocstring Lake.findPackageByKey? ZhDoc.BuildTools.Lake.findPackageByKey?}

{zhdocstring Lake.findModule? ZhDoc.BuildTools.Lake.findModule?}

{zhdocstring Lake.findLeanExe? ZhDoc.BuildTools.Lake.findLeanExe?}

{zhdocstring Lake.findLeanLib? ZhDoc.BuildTools.Lake.findLeanLib?}

{zhdocstring Lake.findExternLib? ZhDoc.BuildTools.Lake.findExternLib?}

{zhdocstring Lake.getLeanPath ZhDoc.BuildTools.Lake.getLeanPath}

{zhdocstring Lake.getLeanSrcPath ZhDoc.BuildTools.Lake.getLeanSrcPath}

{zhdocstring Lake.getSharedLibPath ZhDoc.BuildTools.Lake.getSharedLibPath}

{zhdocstring Lake.getAugmentedLeanPath ZhDoc.BuildTools.Lake.getAugmentedLeanPath}

{zhdocstring Lake.getAugmentedLeanSrcPath ZhDoc.BuildTools.Lake.getAugmentedLeanSrcPath}

{zhdocstring Lake.getAugmentedSharedLibPath ZhDoc.BuildTools.Lake.getAugmentedSharedLibPath}

{zhdocstring Lake.getAugmentedEnv ZhDoc.BuildTools.Lake.getAugmentedEnv}

{zhincludeDocstring Lake.Package.defaultTargets ZhDoc.BuildTools.Config.Package.defaultTargets}

{zhincludeDocstring Lake.Dependency.version ZhDoc.BuildTools.Config.Dependency.version}

{zhincludeDocstring Lake.DSL.declField ZhDoc.BuildTools.Config.DSL.declField}

{zhincludeDocstring Lake.DSL.postUpdateDecl ZhDoc.BuildTools.Config.DSL.postUpdateDecl}

{zhincludeDocstring Lake.DSL.fromClause ZhDoc.BuildTools.Config.DSL.fromClause}

{zhdocstring Lake.LeanLibConfig ZhDoc.BuildTools.Config.LeanLibConfig}

{zhdocstring Lake.LeanExeConfig ZhDoc.BuildTools.Config.LeanExeConfig}

{zhincludeDocstring Lake.DSL.externLibCommand ZhDoc.BuildTools.Config.DSL.externLibCommand}

{zhincludeDocstring Lake.DSL.targetCommand ZhDoc.BuildTools.Config.DSL.targetCommand}

{zhincludeDocstring Lake.DSL.packageFacetDecl ZhDoc.BuildTools.Config.DSL.packageFacetDecl}

{zhincludeDocstring Lake.DSL.libraryFacetDecl ZhDoc.BuildTools.Config.DSL.libraryFacetDecl}

{zhincludeDocstring Lake.DSL.moduleFacetDecl ZhDoc.BuildTools.Config.DSL.moduleFacetDecl}

{zhdocstring Lake.BuildType ZhDoc.BuildTools.Config.BuildType}

{zhdocstring Lake.Glob ZhDoc.BuildTools.Config.Glob}

{zhdocstring Lake.LeanOption ZhDoc.BuildTools.Config.LeanOption}

{zhdocstring Lake.Backend ZhDoc.BuildTools.Config.Backend}

{zhincludeDocstring Lake.DSL.scriptDecl ZhDoc.BuildTools.Config.DSL.scriptDecl}

{zhdocstring Lake.ScriptM ZhDoc.BuildTools.Lake.ScriptM}

{zhincludeDocstring Lake.DSL.dirConst ZhDoc.BuildTools.Config.DSL.dirConst}

{zhincludeDocstring Lake.DSL.getConfig ZhDoc.BuildTools.Config.DSL.getConfig}

{zhincludeDocstring Lake.DSL.metaIf ZhDoc.BuildTools.Config.DSL.metaIf}

{zhincludeDocstring Lake.DSL.cmdDo ZhDoc.BuildTools.Config.DSL.cmdDo}

{zhincludeDocstring Lake.DSL.runIO ZhDoc.BuildTools.Config.DSL.runIO}
