import Manual.ZhDocString.IO

open Verso.Genre Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "IO 中文动态文档冒烟测试" =>
%%%
file := "IO 中文动态文档冒烟测试"
tag := "io-中文动态文档冒烟测试"
%%%

{zhdocstring BaseIO Manual.ZhDocString.IO.c001}

{zhdocstring IO Manual.ZhDocString.IO.c002}

{zhdocstring EIO Manual.ZhDocString.IO.c003}

{zhdocstring IO.lazyPure Manual.ZhDocString.IO.c004}

{zhdocstring BaseIO.toIO Manual.ZhDocString.IO.c005}

{zhdocstring BaseIO.toEIO Manual.ZhDocString.IO.c006}

{zhdocstring EIO.toBaseIO Manual.ZhDocString.IO.c007}

{zhdocstring EIO.toIO Manual.ZhDocString.IO.c008}

{zhdocstring EIO.toIO' Manual.ZhDocString.IO.c009}

{zhdocstring IO.toEIO Manual.ZhDocString.IO.c010}

{zhdocstring IO.Error Manual.ZhDocString.IO.c011}

{zhdocstring IO.Error.toString Manual.ZhDocString.IO.c012}

{zhdocstring IO.ofExcept Manual.ZhDocString.IO.c013}

{zhdocstring EIO.catchExceptions Manual.ZhDocString.IO.c014}

{zhdocstring IO.userError Manual.ZhDocString.IO.c015}

{zhdocstring IO.iterate Manual.ZhDocString.IO.c016}

{zhdocstring System.Platform.numBits Manual.ZhDocString.IO.c017}

{zhdocstring System.Platform.target Manual.ZhDocString.IO.c018}

{zhdocstring System.Platform.isWindows Manual.ZhDocString.IO.c019}

{zhdocstring System.Platform.isOSX Manual.ZhDocString.IO.c020}

{zhdocstring System.Platform.isEmscripten Manual.ZhDocString.IO.c021}

{zhdocstring IO.getEnv Manual.ZhDocString.IO.c022}

{zhdocstring IO.sleep Manual.ZhDocString.IO.c023}

{zhdocstring IO.monoNanosNow Manual.ZhDocString.IO.c024}

{zhdocstring IO.monoMsNow Manual.ZhDocString.IO.c025}

{zhdocstring IO.getNumHeartbeats Manual.ZhDocString.IO.c026}

{zhdocstring IO.addHeartbeats Manual.ZhDocString.IO.c027}

{zhdocstring IO.Process.getCurrentDir Manual.ZhDocString.IO.c028}

{zhdocstring IO.Process.setCurrentDir Manual.ZhDocString.IO.c029}

{zhdocstring IO.Process.exit Manual.ZhDocString.IO.c030}

{zhdocstring IO.Process.getPID Manual.ZhDocString.IO.c031}

{zhdocstring IO.Process.run Manual.ZhDocString.IO.c032}

{zhdocstring IO.Process.output Manual.ZhDocString.IO.c033}

{zhdocstring IO.Process.spawn Manual.ZhDocString.IO.c034}

{zhdocstring IO.Process.SpawnArgs Manual.ZhDocString.IO.c035}

{zhdocstring IO.Process.StdioConfig Manual.ZhDocString.IO.c036}

{zhdocstring IO.Process.Stdio Manual.ZhDocString.IO.c037}

{zhdocstring IO.Process.Stdio.toHandleType Manual.ZhDocString.IO.c038}

{zhdocstring IO.Process.Child Manual.ZhDocString.IO.c039}

{zhdocstring IO.Process.Child.wait Manual.ZhDocString.IO.c040}

{zhdocstring IO.Process.Child.tryWait Manual.ZhDocString.IO.c041}

{zhdocstring IO.Process.Child.kill Manual.ZhDocString.IO.c042}

{zhdocstring IO.Process.Child.takeStdin Manual.ZhDocString.IO.c043}

{zhdocstring IO.Process.Output Manual.ZhDocString.IO.c044}

{zhdocstring IO.setRandSeed Manual.ZhDocString.IO.c045}

{zhdocstring IO.rand Manual.ZhDocString.IO.c046}

{zhdocstring randBool Manual.ZhDocString.IO.c047}

{zhdocstring randNat Manual.ZhDocString.IO.c048}

{zhdocstring RandomGen Manual.ZhDocString.IO.c049}

{zhdocstring StdGen Manual.ZhDocString.IO.c050}

{zhdocstring stdRange Manual.ZhDocString.IO.c051}

{zhdocstring stdNext Manual.ZhDocString.IO.c052}

{zhdocstring stdSplit Manual.ZhDocString.IO.c053}

{zhdocstring mkStdGen Manual.ZhDocString.IO.c054}

{zhdocstring IO.getRandomBytes Manual.ZhDocString.IO.c055}

{zhdocstring IO.print Manual.ZhDocString.IO.c056}

{zhdocstring IO.println Manual.ZhDocString.IO.c057}

{zhdocstring IO.eprint Manual.ZhDocString.IO.c058}

{zhdocstring IO.eprintln Manual.ZhDocString.IO.c059}

{zhdocstring IO.FS.Handle Manual.ZhDocString.IO.c060}

{zhdocstring IO.FS.Handle.mk Manual.ZhDocString.IO.c061}

{zhdocstring IO.FS.Mode Manual.ZhDocString.IO.c062}

{zhdocstring IO.FS.Handle.read Manual.ZhDocString.IO.c063}

{zhdocstring IO.FS.Handle.readToEnd Manual.ZhDocString.IO.c064}

{zhdocstring IO.FS.Handle.readBinToEnd Manual.ZhDocString.IO.c065}

{zhdocstring IO.FS.Handle.readBinToEndInto Manual.ZhDocString.IO.c066}

{zhdocstring IO.FS.Handle.getLine Manual.ZhDocString.IO.c067}

{zhdocstring IO.FS.Handle.write Manual.ZhDocString.IO.c068}

{zhdocstring IO.FS.Handle.putStr Manual.ZhDocString.IO.c069}

{zhdocstring IO.FS.Handle.putStrLn Manual.ZhDocString.IO.c070}

{zhdocstring IO.FS.Handle.flush Manual.ZhDocString.IO.c071}

{zhdocstring IO.FS.Handle.rewind Manual.ZhDocString.IO.c072}

{zhdocstring IO.FS.Handle.truncate Manual.ZhDocString.IO.c073}

{zhdocstring IO.FS.Handle.isTty Manual.ZhDocString.IO.c074}

{zhdocstring IO.FS.Handle.lock Manual.ZhDocString.IO.c075}

{zhdocstring IO.FS.Handle.tryLock Manual.ZhDocString.IO.c076}

{zhdocstring IO.FS.Handle.unlock Manual.ZhDocString.IO.c077}

{zhdocstring IO.FS.Stream Manual.ZhDocString.IO.c078}

{zhdocstring IO.FS.Stream.ofBuffer Manual.ZhDocString.IO.c079}

{zhdocstring IO.FS.Stream.ofHandle Manual.ZhDocString.IO.c080}

{zhdocstring IO.FS.Stream.putStrLn Manual.ZhDocString.IO.c081}

{zhdocstring IO.FS.Stream.Buffer Manual.ZhDocString.IO.c082}

{zhdocstring System.FilePath Manual.ZhDocString.IO.c083}

{zhdocstring System.mkFilePath Manual.ZhDocString.IO.c084}

{zhdocstring System.FilePath.join Manual.ZhDocString.IO.c085}

{zhdocstring System.FilePath.normalize Manual.ZhDocString.IO.c086}

{zhdocstring System.FilePath.isAbsolute Manual.ZhDocString.IO.c087}

{zhdocstring System.FilePath.isRelative Manual.ZhDocString.IO.c088}

{zhdocstring System.FilePath.parent Manual.ZhDocString.IO.c089}

{zhdocstring System.FilePath.components Manual.ZhDocString.IO.c090}

{zhdocstring System.FilePath.fileName Manual.ZhDocString.IO.c091}

{zhdocstring System.FilePath.fileStem Manual.ZhDocString.IO.c092}

{zhdocstring System.FilePath.extension Manual.ZhDocString.IO.c093}

{zhdocstring System.FilePath.addExtension Manual.ZhDocString.IO.c094}

{zhdocstring System.FilePath.withExtension Manual.ZhDocString.IO.c095}

{zhdocstring System.FilePath.withFileName Manual.ZhDocString.IO.c096}

{zhdocstring System.FilePath.pathSeparator Manual.ZhDocString.IO.c097}

{zhdocstring System.FilePath.pathSeparators Manual.ZhDocString.IO.c098}

{zhdocstring System.FilePath.extSeparator Manual.ZhDocString.IO.c099}

{zhdocstring System.FilePath.exeExtension Manual.ZhDocString.IO.c100}

{zhdocstring IO.FS.Metadata Manual.ZhDocString.IO.c101}

{zhdocstring System.FilePath.metadata Manual.ZhDocString.IO.c102}

{zhdocstring System.FilePath.symlinkMetadata Manual.ZhDocString.IO.c103}

{zhdocstring System.FilePath.pathExists Manual.ZhDocString.IO.c104}

{zhdocstring System.FilePath.isDir Manual.ZhDocString.IO.c105}

{zhdocstring IO.FS.DirEntry Manual.ZhDocString.IO.c106}

{zhdocstring IO.FS.DirEntry.path Manual.ZhDocString.IO.c107}

{zhdocstring System.FilePath.readDir Manual.ZhDocString.IO.c108}

{zhdocstring System.FilePath.walkDir Manual.ZhDocString.IO.c109}

{zhdocstring IO.AccessRight Manual.ZhDocString.IO.c110}

{zhdocstring IO.AccessRight.flags Manual.ZhDocString.IO.c111}

{zhdocstring IO.FileRight Manual.ZhDocString.IO.c112}

{zhdocstring IO.FileRight.flags Manual.ZhDocString.IO.c113}

{zhdocstring IO.setAccessRights Manual.ZhDocString.IO.c114}

{zhdocstring IO.FS.removeFile Manual.ZhDocString.IO.c115}

{zhdocstring IO.FS.rename Manual.ZhDocString.IO.c116}

{zhdocstring IO.FS.removeDir Manual.ZhDocString.IO.c117}

{zhdocstring IO.FS.lines Manual.ZhDocString.IO.c118}

{zhdocstring IO.FS.withTempFile Manual.ZhDocString.IO.c119}

{zhdocstring IO.FS.withTempDir Manual.ZhDocString.IO.c120}

{zhdocstring IO.FS.createDirAll Manual.ZhDocString.IO.c121}

{zhdocstring IO.FS.writeBinFile Manual.ZhDocString.IO.c122}

{zhdocstring IO.FS.withFile Manual.ZhDocString.IO.c123}

{zhdocstring IO.FS.removeDirAll Manual.ZhDocString.IO.c124}

{zhdocstring IO.FS.createTempFile Manual.ZhDocString.IO.c125}

{zhdocstring IO.FS.createTempDir Manual.ZhDocString.IO.c126}

{zhdocstring IO.FS.readFile Manual.ZhDocString.IO.c127}

{zhdocstring IO.FS.realPath Manual.ZhDocString.IO.c128}

{zhdocstring IO.FS.writeFile Manual.ZhDocString.IO.c129}

{zhdocstring IO.FS.readBinFile Manual.ZhDocString.IO.c130}

{zhdocstring IO.FS.createDir Manual.ZhDocString.IO.c131}

{zhdocstring IO.getStdin Manual.ZhDocString.IO.c132}

{zhdocstring IO.setStdin Manual.ZhDocString.IO.c133}

{zhdocstring IO.withStdin Manual.ZhDocString.IO.c134}

{zhdocstring IO.getStdout Manual.ZhDocString.IO.c135}

{zhdocstring IO.setStdout Manual.ZhDocString.IO.c136}

{zhdocstring IO.withStdout Manual.ZhDocString.IO.c137}

{zhdocstring IO.getStderr Manual.ZhDocString.IO.c138}

{zhdocstring IO.setStderr Manual.ZhDocString.IO.c139}

{zhdocstring IO.withStderr Manual.ZhDocString.IO.c140}

{zhdocstring IO.FS.withIsolatedStreams Manual.ZhDocString.IO.c141}

{zhdocstring IO.currentDir Manual.ZhDocString.IO.c142}

{zhdocstring IO.appPath Manual.ZhDocString.IO.c143}

{zhdocstring IO.appDir Manual.ZhDocString.IO.c144}

{zhdocstring IO.Ref Manual.ZhDocString.IO.c145}

{zhdocstring IO.mkRef Manual.ZhDocString.IO.c146}

{zhdocstring ST Manual.ZhDocString.IO.c147}

{zhdocstring runST Manual.ZhDocString.IO.c148}

{zhdocstring EST Manual.ZhDocString.IO.c149}

{zhdocstring runEST Manual.ZhDocString.IO.c150}

{zhdocstring ST.Ref Manual.ZhDocString.IO.c151}

{zhdocstring ST.mkRef Manual.ZhDocString.IO.c152}

{zhdocstring ST.Ref.get Manual.ZhDocString.IO.c153}

{zhdocstring ST.Ref.set Manual.ZhDocString.IO.c154}

{zhdocstring ST.Ref.modify Manual.ZhDocString.IO.c155}

{zhdocstring ST.Ref.modifyGet Manual.ZhDocString.IO.c156}

{zhdocstring ST.Ref.swap Manual.ZhDocString.IO.c157}

{zhdocstring ST.Ref.ptrEq Manual.ZhDocString.IO.c158}

{zhdocstring ST.Ref.toMonadStateOf Manual.ZhDocString.IO.c159}

{zhdocstring ST.Ref.take Manual.ZhDocString.IO.c160}

{zhdocstring Task Manual.ZhDocString.IO.c161}

{zhdocstring Task.spawn Manual.ZhDocString.IO.c162}

{zhdocstring Task.pure Manual.ZhDocString.IO.c163}

{zhdocstring BaseIO.asTask Manual.ZhDocString.IO.c164}

{zhdocstring EIO.asTask Manual.ZhDocString.IO.c165}

{zhdocstring IO.asTask Manual.ZhDocString.IO.c166}

{zhdocstring Task.Priority Manual.ZhDocString.IO.c167}

{zhdocstring Task.Priority.default Manual.ZhDocString.IO.c168}

{zhdocstring Task.Priority.max Manual.ZhDocString.IO.c169}

{zhdocstring Task.Priority.dedicated Manual.ZhDocString.IO.c170}

{zhdocstring Task.get Manual.ZhDocString.IO.c171}

{zhdocstring IO.wait Manual.ZhDocString.IO.c172}

{zhdocstring IO.waitAny Manual.ZhDocString.IO.c173}

{zhdocstring Task.map Manual.ZhDocString.IO.c174}

{zhdocstring Task.bind Manual.ZhDocString.IO.c175}

{zhdocstring Task.mapList Manual.ZhDocString.IO.c176}

{zhdocstring BaseIO.mapTask Manual.ZhDocString.IO.c177}

{zhdocstring EIO.mapTask Manual.ZhDocString.IO.c178}

{zhdocstring IO.mapTask Manual.ZhDocString.IO.c179}

{zhdocstring BaseIO.mapTasks Manual.ZhDocString.IO.c180}

{zhdocstring EIO.mapTasks Manual.ZhDocString.IO.c181}

{zhdocstring IO.mapTasks Manual.ZhDocString.IO.c182}

{zhdocstring BaseIO.bindTask Manual.ZhDocString.IO.c183}

{zhdocstring EIO.bindTask Manual.ZhDocString.IO.c184}

{zhdocstring IO.bindTask Manual.ZhDocString.IO.c185}

{zhdocstring BaseIO.chainTask Manual.ZhDocString.IO.c186}

{zhdocstring EIO.chainTask Manual.ZhDocString.IO.c187}

{zhdocstring IO.chainTask Manual.ZhDocString.IO.c188}

{zhdocstring IO.cancel Manual.ZhDocString.IO.c189}

{zhdocstring IO.checkCanceled Manual.ZhDocString.IO.c190}

{zhdocstring IO.hasFinished Manual.ZhDocString.IO.c191}

{zhdocstring IO.getTaskState Manual.ZhDocString.IO.c192}

{zhdocstring IO.TaskState Manual.ZhDocString.IO.c193}

{zhdocstring IO.getTID Manual.ZhDocString.IO.c194}

{zhdocstring IO.Promise Manual.ZhDocString.IO.c195}

{zhdocstring IO.Promise.new Manual.ZhDocString.IO.c196}

{zhdocstring IO.Promise.isResolved Manual.ZhDocString.IO.c197}

{zhdocstring IO.Promise.result? Manual.ZhDocString.IO.c198}

{zhdocstring IO.Promise.result! Manual.ZhDocString.IO.c199}

{zhdocstring IO.Promise.resultD Manual.ZhDocString.IO.c200}

{zhdocstring IO.Promise.resolve Manual.ZhDocString.IO.c201}

{zhdocstring Std.Channel Manual.ZhDocString.IO.c202}

{zhdocstring Std.Channel.new Manual.ZhDocString.IO.c203}

{zhdocstring Std.Channel.send Manual.ZhDocString.IO.c204}

{zhdocstring Std.Channel.recv Manual.ZhDocString.IO.c205}

{zhdocstring Std.Channel.forAsync Manual.ZhDocString.IO.c206}

{zhdocstring Std.Channel.sync Manual.ZhDocString.IO.c207}

{zhdocstring Std.Channel.Sync Manual.ZhDocString.IO.c208}

{zhdocstring Std.CloseableChannel Manual.ZhDocString.IO.c209}

{zhdocstring Std.CloseableChannel.new Manual.ZhDocString.IO.c210}

{zhdocstring Std.Mutex Manual.ZhDocString.IO.c211}

{zhdocstring Std.Mutex.new Manual.ZhDocString.IO.c212}

{zhdocstring Std.Mutex.atomically Manual.ZhDocString.IO.c213}

{zhdocstring Std.Mutex.atomicallyOnce Manual.ZhDocString.IO.c214}

{zhdocstring Std.AtomicT Manual.ZhDocString.IO.c215}

{zhdocstring Std.Condvar Manual.ZhDocString.IO.c216}

{zhdocstring Std.Condvar.new Manual.ZhDocString.IO.c217}

{zhdocstring Std.Condvar.wait Manual.ZhDocString.IO.c218}

{zhdocstring Std.Condvar.notifyOne Manual.ZhDocString.IO.c219}

{zhdocstring Std.Condvar.notifyAll Manual.ZhDocString.IO.c220}

{zhdocstring Std.Condvar.waitUntil Manual.ZhDocString.IO.c221}
