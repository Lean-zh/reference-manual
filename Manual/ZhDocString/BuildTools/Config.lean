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

/-- 工作区的声明式配置。 -/
structure WorkspaceConfig where
  /--
  Lake 下载远程依赖项的目录。
  默认为 `defaultPackagesDir`（即 `.lake/packages`）。
  -/
  packagesDir : FilePath := _root_.Lake.defaultPackagesDir

/-- `Package` 的声明式配置。 -/
structure PackageConfig (p : Name) (n : Name) extends WorkspaceConfig, LeanConfig where
  /-- **供内部使用。** 此包是否为 Lean 本身。 -/
  bootstrap : Bool := false

  /-- 每当使用此包时要构建的目标名称 `Array`。 -/
  extraDepTargets : Array Name := #[]

  /--
  是否将包的每个模块编译为原生共享库，并在每次导入该模块时加载。这会加速元程序求值，并让
  解释器能够运行标记为 `@[extern]` 的函数。

  默认为 `false`。
  -/
  precompileModules : Bool := false

  /--
  传给由 `lake serve` 启动的 Lean 语言服务器（即 `lean --server`）的额外实参；既用于此包，也用于
  同一会话中从此包浏览的任何包。
  -/
  moreGlobalServerArgs : Array String := #[]

  /--
  包含包的 Lean 源文件的目录。
  默认为包目录。

  （它会作为 `-R` 选项传给 `lean`。）
  -/
  srcDir : FilePath := "."

  /--
  Lake 应将包的构建结果输出到的目录。
  默认为 `defaultBuildDir`（即 `.lake/build`）。
  -/
  buildDir : FilePath := _root_.Lake.defaultBuildDir

  /--
  Lake 应将包的二进制 Lean 库（例如 `.olean`、`.ilean` 文件）输出到的构建子目录。
  默认为 `defaultLeanLibDir`（即 `lib`）。
  -/
  leanLibDir : FilePath := _root_.Lake.defaultLeanLibDir

  /--
  Lake 应将包的原生库（例如 `.a`、`.so`、`.dll` 文件）输出到的构建子目录。
  默认为 `defaultNativeLibDir`（即 `lib`）。
  -/
  nativeLibDir : FilePath := _root_.Lake.defaultNativeLibDir

  /--
  Lake 应将包的二进制可执行文件输出到的构建子目录。
  默认为 `defaultBinDir`（即 `bin`）。
  -/
  binDir : FilePath := _root_.Lake.defaultBinDir

  /--
  Lake 应将包的中间结果（例如 `.c` 和 `.o` 文件）输出到的构建子目录。
  默认为 `defaultIrDir`（即 `ir`）。
  -/
  irDir : FilePath := _root_.Lake.defaultIrDir

  /--
  用于上传和下载此包发行版的 GitHub 仓库 URL。
  若为 `none`（默认值），下载时 Lake 使用包的下载来源 URL（若它是依赖项），上传时使用 `gh` 的默认值。
  -/
  releaseRepo : Option String := none

  /--
  GitHub 云端发行版构建归档的自定义名称。
  若为 `none`（默认值），Lake 使用 `{(pkg-)name}-{System.Platform.target}.tar.gz`。
  -/
  buildArchive : Option String := none

  /--
  将此包用作依赖项时，是否优先下载（来自 GitHub 的）预构建发行版，而不是从源代码构建此包。
  -/
  preferReleaseBuild : Bool := false

  /--
  当此包是工作区根时，由 `lake test` 使用的脚本、可执行文件或库的名称。要指向另一包中的定义，
  请使用语法 `<pkg>/<def>`。

  脚本驱动会以 `testDriverArgs` 中配置的实参为先、命令行界面上指定的实参为后（例如通过
  `lake lint -- <args>...`），由 `lake test` 运行。可执行文件驱动会先构建，再像脚本一样运行。
  库则只会被构建。
  -/
  testDriver : String := ""

  /--
  传给包的测试驱动的实参。
  这些实参位于通过 `lake test -- <args>...` 从命令行传入的实参之前。
  -/
  testDriverArgs : Array String := #[]

  /--
  当此包是工作区根时，由 `lake lint` 使用的脚本或可执行文件的名称。要指向另一包中的定义，
  请使用语法 `<pkg>/<def>`。

  脚本驱动会以 `lintDriverArgs` 中配置的实参为先、命令行界面上指定的实参为后（例如通过
  `lake lint -- <args>...`），由 `lake lint` 运行。可执行文件驱动会先构建，再像脚本一样运行。
  -/
  lintDriver : String := ""

  /--
  传给包的代码检查器的实参。
  这些实参位于通过 `lake lint -- <args>...` 从命令行传入的实参之前。
  -/
  lintDriverArgs : Array String := #[]

  /--
  包版本。版本形式为：

  ```
  v!"<major>.<minor>.<patch>[-<specialDescr>]"
  ```

  带有 `-` 后缀的版本视为“预发行版”。

  Lake 建议按以下准则递增版本：

  * **主版本递增**（例如 v1.3.0 → v2.0.0）
    表示包中有重大的破坏性变更。
    不应期望包使用者无需手动干预就能更新到新版本。

  * **次版本递增**（例如 v1.3.0 → v1.4.0）
    表示通常应向后兼容的重要变更。
    应期望包使用者自动更新到此版本，并能轻松修复任何破坏和/或警告。

  * **补丁版本递增**（例如 v1.3.0 → v1.3.1）
    保留用于错误修复和小幅润色。
    应期望包使用者自动更新，且除了使用者依赖已修复错误之行为的边缘情况外，不应出现重大破坏。

  **请注意，任何版本递增都可能发生不向后兼容的变更。**
  这是因为 Lean 当前的性质（例如传递导入、丰富的元编程、证明中的可约性）使得为包定义完全稳定的
  接口并不可行。不同版本级别只表示变更预期的重要程度以及预计迁移的难度。

  `0.x.x` 形式的版本视为首次正式发行之前的开发版本。与预发行版一样，它们不必严格遵循上述准则。

  未定义版本的包默认为 `0.0.0`。
  -/
  version : _root_.Lake.StdVer := {}

  /--
  此包仓库中应视为版本的 Git 标签。
  包索引（例如 Reservoir）可利用此信息确定与已发行版本对应的 Git 修订版本。

  默认为“类似版本”的标签，即以 `v` 开头、后跟数字的标签。
  -/
  versionTags : _root_.Lake.StrPat := _root_.Lake.defaultVersionTags

  /-- 包的简短描述（例如供 Reservoir 使用）。 -/
  description : String := ""

  /--
  与包关联的自定义关键词。
  Reservoir 可使用包的关键词对相关包进行分组，让使用者更容易发现它们。

  合适的关键词包括领域（例如 `math`、`software-verification`、`devtool`）、具体子主题（例如
  `topology`、`cryptology`）和重要实现细节（例如 `dsl`、`ffi`、`cli`）。例如，Lake 的关键词可以是
  `devtool`、`cli`、`dsl`、`package-manager` 和 `build-system`。
  -/
  keywords : Array String := #[]

  /--
  指向包相关信息的 URL。

  Reservoir 已会包含指向包的 GitHub 仓库的链接（若包来自那里）。因此，建议使用者在此指定其他内容
  （如果要指定的话）。
  -/
  homepage : String := ""

  /--
  包的许可证（若有）。
  应为有效的 [SPDX 许可证表达式][1]。

  Reservoir 要求包使用 OSI 批准的许可证才能纳入其索引，目前仅支持单标识符 SPDX 表达式。
  OSI 批准的 SPDX 许可证标识符列表见 [SPDX 许可证列表][2]。

  [1]: https://spdx.github.io/spdx-spec/v3.0/annexes/SPDX-license-expressions/
  [2]: https://spdx.org/licenses/
  -/
  license : String := ""

  /--
  包含包许可证信息的文件。

  这些应是使用者分发包源代码时预期附带的许可证文件；某些许可证可能需要多个文件。例如，
  Apache 2.0 许可证要求在 `NOTICE` 文件存在时，将它与许可证一起复制。

  默认为 `#["LICENSE"]`。
  -/
  licenseFiles : Array FilePath := #["LICENSE"]

  /--
  包的 README 路径。

  README 应为包含包概述的 Markdown 文件。Reservoir 会在包页面上显示该文件渲染后的 HTML。
  可以使用非标准位置，分别为 Reservoir 和 GitHub 提供不同的 README。

  默认为 `README.md`。
  -/
  readmeFile : FilePath := "README.md"

  /--
  Reservoir 是否应将包纳入其索引。
  设为 `false` 时，Reservoir 不会将包加入索引；若它已在索引中，则会在 Reservoir 下次更新时移除。
  -/
  reservoir : Bool := true

  /--
  是否为包启用 Lake 的本地离线产物缓存。

  包的产物（即构建产品）会存入与 Lean 工具链关联的缓存，从而在各本地副本间共享。
  使用大型项目或大型依赖项的多个副本时，这可以显著减少初次构建时间和磁盘占用。

  需要注意的是，支持产物缓存的构建目标不会存储在构建目录中的通常位置。因此，依赖产物特定位置的
  自定义构建脚本可能需要禁用此功能。

  若为 `none`（默认值），则按顺序回退到：
  * `LAKE_ARTIFACT_CACHE` 环境变量（若已设置）。
  * 工作区根的 `enableArtifactCache` 配置（若已设置且此包是依赖项）。
  * **Lake 的默认值**：包可以使用缓存中的产物，但不能写入缓存。
  -/
  enableArtifactCache? : Option Bool := none

  /--
  启用本地产物缓存后，Lake 是否应将所有缓存产物复制到构建目录。这可确保外部使用者能在构建目录中
  找到构建结果。

  若为 `none`（默认值），则按顺序回退到：
  * `LAKE_RESTORE_ARTIFACTS` 环境变量（若已设置）。
  * 工作区根的 `restoreAllArtifacts` 配置（若已设置且此包是依赖项）。
  * **Lake 的默认值**：`false`。
  -/
  restoreAllArtifacts? : Option Bool := none

  /--
  此包的原生库在 Windows 上是否应带 `lib` 前缀。

  与 Unix 不同，Windows 不要求原生库以 `lib` 开头，且按惯例通常也不这样命名。不过，为了在所有
  平台上采用一致命名，使用者可能希望启用此选项。

  默认为 `false`。
  -/
  libPrefixOnWindows : Bool := false

  /--
  下游包是否可以 `import all` 此包的模块。

  启用后，下游使用者能够访问模块的 `private` 内部实现，包括未标记为 `@[expose]` 的定义体。
  将来这也可能阻止依赖于 `private` 定义无法从其所在包外部访问这一事实的编译器优化。

  默认为 `false`。
  -/
  allowImportAll : Bool := false

  /--
  是否对包运行 Lake 的内置代码检查器。

  * `true` — 始终运行内置代码检查。若还配置了代码检查驱动，则先运行内置代码检查。
  * `false` — 默认从不运行内置代码检查。若也未配置代码检查驱动，`lake check-lint` 将以非零代码退出。
  * `none`（默认值）— 当前等同于 `false`。将来的版本中，未配置代码检查驱动时，`none` 会运行内置
    代码检查（即作为回退时等同于 `true`）。
  -/
  builtinLint? : Option Bool := none

  /--
  此包是否预期仅在单一工具链（包的工具链）上工作。

  这会告知 Lake 的工具链更新过程（在 `lake update` 中）优先采用此包的工具链，也无需在 Lake 缓存中
  按工具链版本区分此包的输入到输出映射。

  默认为 `false`。
  -/
  fixedToolchain : Bool := false

/--
`Dependency` 表示包的一个依赖项。
它指定另一个包所依赖的包。
此结构编码 `require` 领域特定语言语法中包含的信息。
-/
structure Dependency where
  /--
  依赖项的包名称。
  此名称必须与其配置文件中声明的名称一致，因为该名称用于索引其目标数据类型。为此，包名称还必须
  在依赖关系图中的所有包之间唯一。
  -/
  name : Name
  /--
  用于区分 Lake 注册表中同名包的附加限定符。在 Reservoir 中，这是包所有者。
  -/
  scope : String
  /--
  依赖项的目标版本。
  -/
  version : _root_.Lake.InputVer
  /--
  依赖项的来源。
  若无来源，则在默认注册表（例如 Reservoir）中查找依赖项。
  支持的来源见 `DependencySrc` 的文档。
  -/
  src? : Option _root_.Lake.DependencySrc
  /--
  传给依赖项包配置的实参。
  -/
  opts : _root_.Lean.NameMap String

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
  /-- 在库模块之前构建的目标 `Array`。 -/
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

namespace Package

/--
默认构建的包目标名称（即对包执行不带其他参数的 `lake build` 时所构建的目标）。
-/
def defaultTargets (self : _root_.Lake.Package) : Array Name := self.defaultTargets

end Package

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
为包定义新的自定义目标。只有一种形式：

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  /- build term of type `FetchM (Job α)` -/
```

`pkg` 参数（及其类型说明符）可省略。
其类型为 `NPackage _package.name`，以可证明地表明所提供的包就是定义该目标的包。
-/
scoped syntax (name := targetCommand)
  (docComment)? (Term.attributes)? "target " buildDeclSig
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
/-- 显示问候语 -/
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
