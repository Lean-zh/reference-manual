import VersoManual

open Lean
open Verso ArgParse Doc Elab Code
open Verso.Doc.Elab.PartElabM
open Verso.Code.Highlighted.WebAssets
open SubVerso.Highlighting

namespace Verso.Genre.Manual

section
variable {m}
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]

structure ZhDocstringOpts where
  enName : Ident × Name
  zhName : Ident × Name
  allowMissing : Bool
  hideFields : Bool := false
  hideStructureConstructor : Bool := false
  label : Option String := none

meta def ZhDocstringOpts.parse : ArgParse m ZhDocstringOpts :=
  ZhDocstringOpts.mk <$>
    .positional `enName .documentableName <*>
    .positional `zhName .documentableName <*>
    .flagM `allowMissing (verso.docstring.allowMissing.get <$> getOptions)
      "缺少文档字符串时仅警告" <*>
    .flag `hideFields false <*>
    .flag `hideStructureConstructor false <*>
    .named `label .string true

meta instance : FromArgs ZhDocstringOpts m := ⟨ZhDocstringOpts.parse⟩
end

private meta def translatedBlocks (names : List Name) (blame : Syntax)
    (docs? : Option String) : DocElabM (Array Term) := do
  let some docs := docs? | return #[]
  let some ast := MD4Lean.parse docs
    | throwErrorAt blame "无法将中文文档字符串解析为 Markdown"
  ast.blocks.mapM (blockFromMarkdownWithLean names)

private def finalNameComponent : Name → String
  | .anonymous => ""
  | .str _ s => s
  | .num _ n => toString n

private def translatedDeclLabel : Block.Docstring.DeclType → String
  | .structure false .. => "结构体"
  | .structure true .. => "类型类"
  | .def .safe => "定义"
  | .def .unsafe => "不安全定义"
  | .def .partial => "部分定义"
  | .opaque .unsafe => "不安全不透明定义"
  | .opaque _ => "不透明定义"
  | .inductive _ _ false => "归纳类型"
  | .inductive _ 0 true => "归纳命题"
  | .inductive _ _ true => "归纳谓词"
  | .axiom _ => "公理"
  | .theorem => "定理"
  | .ctor n _ => s!"{n} 的构造子"
  | .quotPrim _ => "原语"
  | .recursor .unsafe => "不安全递归器"
  | .recursor _ => "递归器"
  | .other => ""

/--
Render the declaration and signatures of `enName`, using documentation text from `zhName`.
The two declarations must have matching constructors and fields; mismatches are errors rather than
silently attaching a translation to the wrong declaration.
-/
@[block_command]
meta def zhdocstring : BlockCommandOf ZhDocstringOpts
  | ⟨(enStx, enName), (zhStx, zhName), allowMissing, hideFields, hideCtor, customLabel⟩ => do
    withOptions (verso.docstring.allowMissing.set · allowMissing) do
      Doc.PointOfInterest.save (← getRef) enName.toString (detail? := some "中文文档")
      let body ← translatedBlocks [enName, zhName] zhStx (← getDocString? (← getEnv) zhName)
      let enDeclType ← Block.Docstring.DeclType.ofName enName
        (hideFields := hideFields) (hideStructureConstructor := hideCtor)
      let zhDeclType ← Block.Docstring.DeclType.ofName zhName
        (hideFields := hideFields) (hideStructureConstructor := hideCtor)
      let enSignature ← Signature.forName enName
      let extras ← translatedExtras enStx enName zhName enDeclType zhDeclType
      let altNames ← getStoredSuggestions enName
      let customLabel := customLabel.orElse fun _ =>
        let label := translatedDeclLabel enDeclType
        if label.isEmpty then none else some label
      ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstring $(quote enName) $(quote enDeclType)
            $(quote enSignature) $(quote customLabel) $(quote altNames.toArray))
          #[$(body ++ extras),*])
where
  translatedExtras (blame : Syntax) (enName zhName : Name)
      (enDeclType zhDeclType : Block.Docstring.DeclType) : DocElabM (Array Term) := do
    match enDeclType, zhDeclType with
    | .structure enIsClass enCtor? _ enFields enParents _,
      .structure _ zhCtor? _ zhFields zhParents _ =>
      if enCtor?.isSome != zhCtor?.isSome then
        throwErrorAt blame "中英文结构体的构造子可见性不匹配：{enName} / {zhName}"
      let ctorRow : Option Term ← match enCtor?, zhCtor? with
        | some enCtor, some zhCtor => do
          if finalNameComponent enCtor.name != finalNameComponent zhCtor.name then
            throwErrorAt blame
              "中英文结构体构造子映射不匹配：{enCtor.name} / {zhCtor.name}"
          let header := if enIsClass then "实例构造子" else "构造子"
          let desc ← translatedBlocks [enName, enCtor.name, zhName, zhCtor.name]
            blame zhCtor.docstring?
          let sig ← `(Verso.Doc.Block.other
            (Verso.Genre.Manual.Block.internalSignature $(quote enCtor.hlName) none) #[$desc,*])
          some <$> ``(Verso.Doc.Block.other
            (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])
        | none, none => pure none
        | _, _ => throwErrorAt blame "中英文结构体的构造子不匹配：{enName} / {zhName}"

      if enParents.size != zhParents.size then
        throwErrorAt blame "中英文结构体父类型数量不匹配：{enName} / {zhName}"
      for (enParent, zhParent) in enParents.zip zhParents do
        if finalNameComponent enParent.name != finalNameComponent zhParent.name then
          throwErrorAt blame
            "中英文结构体父类型映射不匹配：{enParent.name} / {zhParent.name}"

      let parentsRow : Option Term ← do
        if enParents.isEmpty then pure none
        else
          let inh ← ``(Verso.Doc.Block.other
            (Verso.Genre.Manual.Block.inheritance $(quote enName) $(quote enParents)) #[])
          some <$> ``(Verso.Doc.Block.other
            (Verso.Genre.Manual.Block.docstringSection "扩展") #[$inh])

      let enFields := enFields.filter (·.subobject?.isNone)
      let zhFields := zhFields.filter (·.subobject?.isNone)
      if enFields.size != zhFields.size then
        throwErrorAt blame "中英文结构体字段数不匹配：{enName} / {zhName}"
      let fieldSigs : Array Term ← (enFields.zip zhFields).mapM fun (enField, zhField) => do
        if finalNameComponent enField.projFn != finalNameComponent zhField.projFn then
          throwErrorAt blame "中英文字段映射不匹配：{enField.projFn} / {zhField.projFn}"
        let inheritedFrom : Option Nat :=
          enField.fieldFrom.head?.bind (fun n => enParents.findIdx? (·.name == n.name))
        let desc ← translatedBlocks
          [enName, enField.projFn, zhName, zhField.projFn] blame zhField.docString?
        let inheritedNote : Array Term ←
          if inheritedFrom.isSome then
            pure #[← ``(Verso.Doc.Block.para
              #[Verso.Doc.Inline.text "继承自父结构。"]) ]
          else pure #[]
        ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.fieldSignature $(quote enField.visibility)
            $(quote enField.fieldName) $(quote enField.type) none
            $(quote <| enParents.map (·.parent))) #[$(inheritedNote ++ desc),*])
      let fieldsRow : Option Term ←
        if fieldSigs.isEmpty then pure none
        else some <$> ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstringSection $(quote <|
            if enIsClass then "方法" else "字段")) #[$fieldSigs,*])
      pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray

    | .inductive enCtors .., .inductive zhCtors .. => do
      if enCtors.size != zhCtors.size then
        throwErrorAt blame "中英文归纳类型构造子数量不匹配：{enName} / {zhName}"
      let ctorSigs : Array Term ← (enCtors.zip zhCtors).mapM fun (enCtor, zhCtor) =>
        withTheReader Core.Context ({· with currNamespace := enName}) do
          if finalNameComponent enCtor.name != finalNameComponent zhCtor.name then
            throwErrorAt blame "中英文构造子映射不匹配：{enCtor.name} / {zhCtor.name}"
          let desc ← translatedBlocks [enName, enCtor.name, zhName, zhCtor.name]
            blame zhCtor.docstring?
          ``(Verso.Doc.Block.other
            (Verso.Genre.Manual.Block.constructorSignature $(quote enCtor.signature)) #[$desc,*])
      pure #[← ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.docstringSection "构造子") #[$ctorSigs,*])]

    | .structure .., _ =>
      throwErrorAt blame "{enName} 是结构体，但中文文档载体 {zhName} 不是结构体"
    | .inductive .., _ =>
      throwErrorAt blame "{enName} 是归纳类型，但中文文档载体 {zhName} 不是归纳类型"
    | _, .structure .. =>
      throwErrorAt blame "中文文档载体 {zhName} 是结构体，但 {enName} 不是结构体"
    | _, .inductive .. =>
      throwErrorAt blame "中文文档载体 {zhName} 是归纳类型，但 {enName} 不是归纳类型"
    | _, _ => pure #[]

/--
Insert only the translated documentation body from `zhName`, without rendering a declaration
signature. This is the translated counterpart of `includeDocstring` for use inside syntax blocks.
-/
@[block_command]
meta def zhincludeDocstring : BlockCommandOf ZhDocstringOpts
  | ⟨(_enStx, enName), (zhStx, zhName), _allowMissing, _hideFields,
      _hideStructureConstructor, _customLabel⟩ => do
    let body ← translatedBlocks [enName, zhName] zhStx (← getDocString? (← getEnv) zhName)
    ``(Doc.Block.concat #[$body,*])

section
variable {m}
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]

structure ZhOptionDocsOpts where
  enName : Ident
  zhName : Ident × Name

meta def ZhOptionDocsOpts.parse : ArgParse m ZhOptionDocsOpts :=
  ZhOptionDocsOpts.mk <$>
    .positional `enName .ident "选项名" <*>
    .positional `zhName .documentableName

meta instance : FromArgs ZhOptionDocsOpts m := ⟨ZhOptionDocsOpts.parse⟩
end

def Block.zhOptionDocs (name : Name) (defaultValue : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.zhOptionDocs
  data := ToJson.toJson (name, defaultValue)

/-- Render an option's real name and default value with a translated documentation carrier. -/
@[block_command]
meta def zhOptionDocs : BlockCommandOf ZhOptionDocsOpts
  | ⟨enName, (zhStx, zhName)⟩ => do
    let optDecl ← getOptionDecl enName.getId
    Doc.PointOfInterest.save enName.raw optDecl.declName.toString
    let contents ← translatedBlocks [zhName] zhStx (← getDocString? (← getEnv) zhName)
    ``(Verso.Doc.Block.other
      (Verso.Genre.Manual.Block.zhOptionDocs $(quote enName.getId)
        $(quote <| highlightDataValue optDecl.defValue)) #[$contents,*])

open Verso.Search in
def zhOptionDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs optionDomain "编译器选项" "doc-option-domain"
    |>.setFont { family := .code }

open Verso.Genre.Manual.Markdown in
@[block_extension zhOptionDocs]
def zhOptionDocs.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle optionDomain "编译器选项"
    |>.addQuickJumpMapper optionDomain zhOptionDomainMapper

  traverse id info _ := do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | do reportError "遍历选项时无法反序列化中文文档数据"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {
        term := Doc.Inline.code name.getString!
        subterm := some <| Doc.Inline.code name.toString
      }
    modify fun st => st.saveDomainObject optionDomain name.toString id
    pure none

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
        | do reportError "生成 HTML 时无法反序列化中文选项文档数据"; pure .empty
      let x : Html := Html.text true name.toString
      let xref ← HtmlT.state
      let idAttr := xref.htmlId id
      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"选项"</span>
          <pre class="signature hl lean block">{{x}}</pre>
          <div class="text">
            <p>"默认值：" <code class="hl lean inline">{{← defaultValue.toHtml (g := Manual)}}</code></p>
            {{← contents.mapM goB}}
          </div>
        </div>
      }}

  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (name, _defaultValue) ← FromJson.fromJson? (α := Name × Highlighted) info
    pure #[
      (name.toString, {{<code>{{name.toString}}</code>}}),
      (s!"{name}（选项）", {{<code>{{name.toString}}</code>"（选项）"}})
    ]
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}

end Verso.Genre.Manual
