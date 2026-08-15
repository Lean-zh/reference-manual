/-
Copyright (c) 2026 Lean 中文社区. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean 中文社区
-/
import Lake.Config.Monad
import Lake.DSL
import Manual.ZhDocString.ZhDocString

open Lean System

namespace ZhDoc.BuildTools.Config

/--
模块构建目标所共有的配置选项。
-/
structure LeanConfig where
  /--
  构建模块所采用的模式（例如 `debug`、`release`）。
  默认为 `release`。
  -/
  buildType : _root_.Lake.BuildType := .release
  /--
  传给由 `lake serve` 启动的 Lean 语言服务器（即 `lean --server`）以及编译模块 Lean
  源文件时所用 `lean` 的额外选项 `Array`。
  -/
  leanOptions : Array _root_.Lean.LeanOption := #[]
  /--
  编译模块的 Lean 源文件时传给 `lean` 的额外实参。
  -/
  moreLeanArgs : Array String := #[]
  /--
  编译模块的 Lean 源文件时传给 `lean` 的额外实参。

  与 `moreLeanArgs` 不同，这些实参不影响构建结果的跟踪，因此改变它们不会触发重新构建。
  它们位于 `moreLeanArgs` **之前**。
  -/
  weakLeanArgs : Array String := #[]
  /--
  编译由 `lean` 从模块 C 源文件生成的内容时，传给 `leanc` 的额外实参。

  Lake 已根据 `buildType` 传入一些标志，但可以通过添加 `-O0` 和 `-UNDEBUG` 等方式改变它们。
  -/
  moreLeancArgs : Array String := #[]
  /--
  传给由 `lake serve` 启动的 Lean 语言服务器（即 `lean --server`）的额外选项。
  -/
  moreServerOptions : Array _root_.Lean.LeanOption := #[]
  /--
  编译由 `lean` 从模块 C 源文件生成的内容时，传给 `leanc` 的额外实参。

  与 `moreLeancArgs` 不同，这些实参不影响构建结果的跟踪，因此改变它们不会触发重新构建。
  它们位于 `moreLeancArgs` **之前**。
  -/
  weakLeancArgs : Array String := #[]
  /--
  链接（静态和共享）时使用的额外目标对象。
  它们位于原生分面路径**之后**。
  -/
  moreLinkObjs : _root_.Lake.TargetArray FilePath := #[]
  /--
  链接时传给 `leanc` 的额外目标库（例如用于共享库或二进制可执行文件）。
  它们位于其他链接对象路径**之后**。
  -/
  moreLinkLibs : _root_.Lake.TargetArray _root_.Lake.Dynlib := #[]
  /--
  链接时传给 `leanc` 的额外实参（例如用于共享库或二进制可执行文件）。
  它们位于链接对象路径**之后**。
  -/
  moreLinkArgs : Array String := #[]
  /--
  链接时传给 `leanc` 的额外实参（例如用于共享库或二进制可执行文件）。
  它们位于链接对象路径**之后**。

  与 `moreLinkArgs` 不同，这些实参不影响构建结果的跟踪，因此改变它们不会触发重新构建。
  它们位于 `moreLinkArgs` **之前**。
  -/
  weakLinkArgs : Array String := #[]
  /--
  构建模块时应使用的编译器后端（例如 `C`、`LLVM`）。
  默认为 `C`。
  -/
  backend : _root_.Lake.Backend := .default
  /--
  断言 Lake 是否应假定 Lean 模块与平台无关。

  * 若为 `false`，Lake 会将 `System.Platform.target` 加入代码单元（例如包或库）内的模块跟踪。
    这会强制 Lean 代码在不同平台上重新精译。

  * 若为 `true`，Lake 会从模块跟踪中排除依赖平台的元素（例如预编译模块、外部库），从而避免在
    不同平台上重新精译。请注意，这不会影响当前代码单元之外的模块。例如，依赖某个依赖平台库的
    平台无关包仍然依赖平台。

  * 若为 `none`，Lake 会自然构造跟踪。也就是说，当模块依赖平台相关产物时就将其纳入跟踪，
    否则不会强制模块依赖平台。

  此处不会检查正确性，因此配置可以作出不实声明而 Lake 不会发现。默认为 `none`。
  -/
  platformIndependent : Option Bool := none
  /--
  在模块精译期间（通过 `lean --load-dynlib`）加载的动态库目标数组。
  -/
  dynlibs : _root_.Lake.TargetArray _root_.Lake.Dynlib := #[]
  /--
  在模块精译期间（通过 `lean --plugin`）加载的 Lean 插件目标数组。
  -/
  plugins : _root_.Lake.TargetArray _root_.Lake.Dynlib := #[]
  /--
  此包或库是否应视为面向模块系统设计。

  启用后，只要某模块导入此代码单元的模块却没有使用模块系统（即没有 `module` 头部），Lake 就会
  发出警告。这既适用于下游使用者，也适用于同一包中的非模块文件，表明该代码单元的 API 预期采用
  模块系统的可见性与精译语义。

  导入方可在自己的包或库上设置 `allowNonModules := true` 来选择不接收该警告。

  默认为 `false`。
  -/
  requiresModuleSystem : Bool := false
  /--
  此包或库是否允许非模块系统文件而不发出警告。

  默认情况下，若此代码单元中的非模块系统文件导入了来自设置了 `requiresModuleSystem` 的代码单元
  （可能包括其自身）的模块，Lake 会发出警告。将此项设为 `true` 会抑制这些警告，表示该代码单元
  明知自己混用了非模块系统文件和模块系统依赖。

  默认为 `false`。
  -/
  allowNonModules : Bool := false

/-- Lean 库的声明式配置。 -/
structure LeanLibConfig (name : Name) extends LeanConfig where
  /--
  包源目录中包含该库 Lean 源文件的子目录。默认就是上述 `srcDir`。

  （它会作为 `-R` 选项传给 `lean`。）
  -/
  srcDir : FilePath := "."
  /--
  库的根模块。
  这些根的子模块（例如 `Lib` 的 `Lib.Foo`）也视为库的一部分。
  默认值是仅包含目标名称的单个根。
  -/
  roots : Array Name := #[name]
  /--
  要为库构建的模块 `Glob` 的 `Array`。
  默认为库的每个 `roots` 各有一个 `Glob.one`。

  子模块通配模式会构建其目录内的每个源文件。
  通配模式所匹配文件的本地导入（即工作区中的其他模块）也会递归构建。
  -/
  globs : Array _root_.Lake.Glob := roots.map _root_.Lake.Glob.one
  /--
  库产物的名称。
  用作其静态和动态二进制文件名的基础。
  默认为经过名称改编的目标名称。
  -/
  libName : String := ""
  /--
  在 Windows 上，此库的静态和共享二进制文件是否应带 `lib` 前缀。

  与 Unix 不同，Windows 不要求原生库以 `lib` 开头，且按惯例通常也不这样命名。不过，为了在所有
  平台上采用一致命名，用户可能希望启用此选项。

  默认为 `false`。
  -/
  libPrefixOnWindows : Bool := false
  /-- 在可执行文件模块之前构建的目标 `Array`。 -/
  needs : Array _root_.Lake.PartialBuildKey := #[]
  /--
  **已弃用。请改用 `needs`。**
  在库模块之前构建的目标名称 `Array`。
  -/
  extraDepTargets : Array Name := #[]
  /--
  是否将库的每个模块编译为原生共享库，并在每次导入该模块时加载。这会加速元程序求值，并让
  解释器能够运行标记为 `@[extern]` 的函数。

  默认为 `false`。
  -/
  precompileModules : Bool := false
  /--
  对库执行不带其他参数的 `lake build` 时要构建的库分面 `Array`。
  例如，`#[LeanLib.sharedFacet]` 会构建共享库分面。
  -/
  defaultFacets : Array Name := #[_root_.Lake.LeanLib.leanArtsFacet]
  /--
  要构建并组合成库的静态库和共享库的模块分面。若 `shouldExport` 为 true，模块分面应导出用户可能
  希望在库中查找的所有符号。例如，Lean 解释器会使用已链接库中的导出符号。

  默认为单元素的 `Module.oExportFacet`（若 `shouldExport`）或 `Module.oFacet`。也就是从 Lean 源码
  编译得到的目标文件，其中可能带有导出的 Lean 符号。
  -/
  nativeFacets (shouldExport : Bool) : Array (_root_.Lake.ModuleFacet FilePath) :=
    #[if shouldExport then _root_.Lake.Module.oExportFacet else _root_.Lake.Module.oFacet]
  /--
  下游包是否可以 `import all` 此库的模块。

  启用后，下游用户能够访问模块的 `private` 内部实现，包括未标记为 `@[expose]` 的定义体。
  将来这也可能阻止依赖于 `private` 定义无法从其所在包外部访问这一事实的编译器优化。

  默认为 `false`。
  -/
  allowImportAll : Bool := false

/-- Lean 可执行文件的声明式配置。 -/
structure LeanExeConfig (name : Name) extends LeanConfig where
  /--
  包源目录中包含该可执行文件 Lean 源文件的子目录。默认就是上述 `srcDir`。

  （它会作为 `-R` 选项传给 `lean`。）
  -/
  srcDir : FilePath := "."
  /--
  二进制可执行文件的根模块。
  应包含一个作为程序入口点的 `main` 定义。

  构建该根时会递归构建其本地导入（即工作区中的其他模块）。

  默认为目标名称。
  -/
  root : Name := name
  /--
  二进制可执行文件的名称。
  默认为将目标名称中的每个 `.` 替换为 `-` 后所得的名称。
  -/
  exeName : String := name.toStringWithSep "-" (escape := false)
  /-- 在可执行文件模块之前构建的目标 `Array`。 -/
  needs : Array _root_.Lake.PartialBuildKey := #[]
  /--
  **已弃用。请改用 `needs`。**
  在可执行文件模块之前构建的目标名称 `Array`。
  -/
  extraDepTargets : Array Name := #[]
  /--
  通过向 Lean 解释器公开可执行文件中的符号，让该可执行文件能够解释 Lean 文件（例如通过
  `Lean.Elab.runFrontend`）。

  从实现上说，在 Windows 上会把 Lean 共享库链接到可执行文件；在其他系统上则用 `-rdynamic`
  链接可执行文件。这会增大 Linux 上的二进制文件，并且在 Windows 上要求 `libInit_shared.dll` 和
  `libleanshared.dll` 与可执行文件位于同一位置或属于 `PATH`（例如通过 `lake exe`）。因此，只应在
  必要时启用此功能。

  默认为 `false`。
  -/
  supportInterpreter : Bool := false
  /--
  要构建并组合成可执行文件的模块分面。
  若 `shouldExport` 为 true，模块分面应导出用户可能希望在可执行文件中查找的所有符号。例如，
  Lean 解释器会使用可执行文件中导出的符号。因此，若 `supportInterpreter := true`，
  `shouldExport` 就会为 `true`。

  默认为单元素的 `Module.oExportFacet`（若 `shouldExport`）或 `Module.oFacet`。也就是从 Lean 源码
  编译得到的目标文件，其中可能带有导出的 Lean 符号。
  -/
  nativeFacets (shouldExport : Bool) : Array (_root_.Lake.ModuleFacet FilePath) :=
    #[if shouldExport then _root_.Lake.Module.oExportFacet else _root_.Lake.Module.oFacet]

/--
Lake 中与 CMake 的
[`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670) 对应的类型。
-/
inductive BuildType
  /--
  调试优化、启用断言、启用自定义调试代码，并在可执行文件中包含调试信息（因此可以在调试器中
  单步执行代码，并将地址转换为源文件:行号）。例如，编译 C 代码时传入 `-O0 -g`。
  -/
  | debug
  /--
  经过优化，*带*调试信息，但不含调试代码或断言（例如编译 C 代码时传入
  `-O3 -g -DNDEBUG`）。
  -/
  | relWithDebInfo
  /--
  与 `release` 相同，但优化目标是大小而非速度（例如编译 C 代码时传入 `-Os -DNDEBUG`）。
  -/
  | minSizeRel
  /--
  高优化级别，并且不含调试信息、调试代码或断言（例如编译 C 代码时传入 `-O3 -DNDEBUG`）。
  -/
  | release

/-- 一组模块名称的规格。 -/
inductive Glob
  /-- 仅选择指定的模块名称。 -/
  | one : Name → Glob
  /-- 选择指定模块的所有子模块，但不选择模块本身。 -/
  | submodules : Name → Glob
  /-- 选择指定模块及其所有子模块。 -/
  | andSubmodules : Name → Glob

/-- Lean 会像通过 `-D` 传入一样使用的选项。 -/
structure LeanOption where
  /-- 选项的名称。 -/
  name : Name
  /-- 选项的值。 -/
  value : _root_.Lean.LeanOptionValue

/--
用于编译 Lean 的编译器后端。
-/
inductive Backend
  /--
  强制使用 C 后端。
  -/
  | c
  /--
  强制使用 LLVM 后端。
  -/
  | llvm
  /--
  使用默认后端。可由更具体的配置覆盖。
  -/
  | default

/--
`Script` 所用单子的类型。

它是带有 Lake 配置信息的 `IO` 单子。
-/
abbrev ScriptM := _root_.Lake.LakeT IO

namespace Package

/--
默认构建的包目标名称（即对包执行不带其他参数的 `lake build` 时所构建的目标）。
-/
def defaultTargets (self : _root_.Lake.Package) : Array Name := self.defaultTargets

end Package

namespace Dependency

/--
依赖项的目标版本。
-/
def version (self : _root_.Lake.Dependency) : _root_.Lake.InputVer := self.version

end Dependency

namespace DSL

open Lean Parser Elab Command
open _root_.Lake.DSL

/-- 声明式配置中的字段赋值。 -/
syntax declField := ident " := " term

/--
为包声明一个执行于 `lake update` 之后的钩子。
在此包或其下游依赖项之一成功执行 `lake update` 之后运行该单子动作。

**示例**

此功能让 Mathlib 能够在 `lake update` 后同步 Lean 工具链并运行 `cache get`：

```
lean_exe cache
post_update pkg do
  let wsToolchainFile := (← getRootPackage).dir / "lean-toolchain"
  let mathlibToolchain ← IO.FS.readFile <| pkg.dir / "lean-toolchain"
  IO.FS.writeFile wsToolchainFile mathlibToolchain
  let exeFile ← runBuild cache.fetch
  let exitCode ← env exeFile.toString #["get"]
  if exitCode ≠ 0 then
    error s!"{pkg.name}: failed to fetch cache"
```
-/
scoped syntax (name := postUpdateDecl)
  optional(docComment) optional(Term.attributes)
  "post_update " (ppSpace simpleBinder)? (declValSimple <|> declValDo)
: command

syntax fromPath := term
syntax fromGit := &"git " term:max ("@" term:max)? ("/" term)?
syntax fromSource := fromGit <|> fromPath

/--
指定获取包依赖项的具体来源。
从远程来源下载的依赖项会放入工作区的 `packagesDir`。

**路径依赖项**

```
from <path>
```

Lake 会加载相对于依赖方包目录的固定 `path` 所指位置上的包。

**Git 依赖项**

```
from git <url> [@ <rev>] [/ <subDir>]
```

Lake 会克隆固定 Git `url` 上可用的 Git 仓库，并检出指定的修订版本 `rev`。修订版本可以是提交
哈希、分支或标签。若未提供，Lake 默认使用 `master`。检出后，Lake 会加载位于 `subDir` 中的包
（若没有指定子目录，则加载仓库根目录中的包）。
-/
syntax fromClause := " from " fromSource

/--
定义新的外部库包目标。只有一种形式：

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  /- build term of type `FetchM (Job FilePath)` -/
```

`pkg` 参数（及其类型说明符）可省略。
其类型为 `NPackage _package.name`，以可证明地表明所提供的包就是定义该目标的包。

该项应构建外部库的**静态**库。
-/
scoped syntax (name := externLibCommand)
  (docComment)? (Term.attributes)? "extern_lib " externLibDeclSpec
: command

/--
定义新的包分面。只有一种形式：

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build term of type `FetchM (Job α)` -/
```

`pkg` 参数（及其类型说明符）可省略。
-/
scoped syntax (name := packageFacetDecl)
  (docComment)? (Term.attributes)? "package_facet " buildDeclSig
: command

/--
定义新的库分面。只有一种形式：

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build term of type `FetchM (Job α)` -/
```

`lib` 参数（及其类型说明符）可省略。
-/
scoped syntax (name := libraryFacetDecl)
  (docComment)? (Term.attributes)? "library_facet " buildDeclSig
: command

/--
定义新的模块分面。只有一种形式：

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build term of type `FetchM (Job α)` -/
```

`mod` 参数（及其类型说明符）可省略。
-/
scoped syntax (name := moduleFacetDecl)
  (docComment)? (Term.attributes)? "module_facet " buildDeclSig
: command

/--
定义新的 Lake 脚本。

**示例**

```
/-- Display a greeting -/
script «script-name» (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args[0]'h}!"
  else
    IO.println "Hello, world!"
  return 0
```
-/
scoped syntax (name := scriptDecl)
  (docComment)? optional(Term.attributes) "script " scriptDeclSpec
: command

/--
在 Lakefile 精译期间展开为包目录路径的宏。
-/
scoped syntax (name := dirConst) "__dir__" : term

/--
在 Lakefile 精译期间展开为指定配置选项的宏；若尚未设置该选项，则展开为 `none`。

配置实参可以通过 Lake 命令行界面（使用 `-K` 选项）设置，也可以通过 `require` 语句中的 `with`
子句设置。
-/
scoped syntax (name := getConfig) "get_config? " ident : term

/--
`meta if` 命令有两种形式：

```lean
meta if <c:term> then <a:command>
meta if <c:term> then <a:command> else <b:command>
```

若项 `c`（在精译时）求值得到 true，它会展开为命令 `a`。否则，它会展开为命令 `b`（若提供了
`else` 子句）。

例如，可以使用此命令来指定仅在特定平台上可用的外部库目标：

```lean
meta if System.Platform.isWindows then
extern_lib winOnlyLib := ...
else meta if System.Platform.isOSX then
extern_lib macOnlyLib := ...
else meta if System.Platform.isLinux then
extern_lib linuxOnlyLib := ...
```
-/
scoped syntax (name := metaIf)
  "meta " "if " term " then " cmdDo (" else " cmdDo)?
: command

/--
`do` 命令语法把多个缩进相同的命令组合在一起。
随后可将这组命令传给通常只接受单个命令的另一条命令（例如 `meta if`）。
-/
syntax cmdDo := ("do" many1Indent(command)) <|> command

/--
在精译时执行一个类型为 `IO α` 的项，并通过 `ToExpr α` 生成对应于所得结果的表达式。
-/
scoped syntax:lead (name := runIO) "run_io " doSeq : term

end DSL
end ZhDoc.BuildTools.Config
