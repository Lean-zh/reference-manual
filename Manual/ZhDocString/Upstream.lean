/-
Chinese documentation for upstream additions. Signatures, constructors, and fields are read from
real declarations. Each translation is keyed by its full declaration name and checked against the
original text, so an upstream documentation change cannot silently use an obsolete translation.
-/
import Manual.Meta.GrindTactic
import Manual.ZhDocString.ZhDocString

open Lean Verso ArgParse Doc Elab Code
open Verso.Doc.Elab.PartElabM

open Manual

namespace Verso.Genre.Manual

private meta def upstreamTranslations : Except String Json :=
  Json.parse (include_str "UpstreamDocs.json")

meta def upstreamTranslation (key source : String) : CoreM String := do
  let json ← ofExcept upstreamTranslations
  let records ← ofExcept json.getArr?
  for record in records do
    if (record.getObjValAs? String "name").toOption == some key then
      let expected ← ofExcept (record.getObjValAs? String "source")
      unless source == expected do
        throwError "上游文档已改变，须重新核对中文翻译：{key}"
      let translated ← ofExcept (record.getObjValAs? String "translation")
      if translated.trimAscii.toString.isEmpty then
        throwError "中文翻译不能为空：{key}"
      return translated
  throwError "缺少上游新增文档的中文翻译：{key}"

meta def upstreamDocString? (name : Name) : CoreM (Option String) := do
  let some docs ← Lean.findDocString? (← getEnv) name | return none
  if docs.isEmpty then return none
  return some (← upstreamTranslation name.toString docs)

@[block_command]
meta def zhdocstringFrom : BlockCommandOf DocstringConfig
  | ⟨(x, name), allowMissing, hideFields, hideCtor, customLabel⟩ => do
    let opts : Options → Options := (verso.docstring.allowMissing.set · allowMissing)

    withOptions opts do
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "中文文档")
      let blockStx ←
        match ← upstreamDocString? name with
        | none => pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs
            | throwErrorAt x "Failed to parse docstring as Markdown"

          ast.blocks.mapM (blockFromMarkdownWithLean [name])

      if !(← Docstring.getAllowDeprecated) && Lean.Linter.isDeprecated (← getEnv) name then
        Lean.logError m!"'{name}' is deprecated.\n\nSet option 'verso.docstring.allowDeprecated' to 'true' to allow documentation for deprecated names."

      let declType ← Block.Docstring.DeclType.ofName name (hideFields := hideFields) (hideStructureConstructor := hideCtor)

      let signature ← Signature.forName name

      let extras ← getExtras name declType

      let altNames ← getStoredSuggestions name

      ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature) $(quote <| customLabel.orElse fun _ => some (translatedDeclLabel declType)) $(quote altNames.toArray)) #[$(blockStx ++ extras),*])
where
  getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor? _ fieldInfo parents _ => do
      let ctorRow : Option Term ← constructor?.mapM fun constructor => do
        let header := if isClass then "实例构造子" else "构造子"
        let sigDesc : Array Term ←
          if let some docs ← upstreamDocString? constructor.name then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure (#[] : Array Term)
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "扩展"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

      let fieldsRow : Option Term ← do
        let header := if isClass then "方法" else "字段"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs ← upstreamDocString? i.projFn then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean <| name :: (constructor?.map ([·.name])).getD [])
            else
              pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
        if fieldSigs.isEmpty then pure none
        else some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])

      pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
    | .inductive ctors .. => do
      let ctorSigs : Array Term ←
        -- Elaborate constructor docs in the type's NS
        ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
          let sigDesc ←
            if let some docs ← upstreamDocString? c.name then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "构造子") #[$ctorSigs,*])]
    | _ => pure #[]

@[block_command]
meta def zhincludeDocstringFrom : BlockCommandOf DocstringConfig
  | ⟨(_stx, name), _allowMissing, _hideFields, _hideCtor, _label⟩ => do
    let body ← translatedBlocks [name] (← getRef) (← upstreamDocString? name)
    ``(Doc.Block.concat #[$body,*])

section
variable {m} [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]
structure TranslatedOptionOpts where
  name : Ident
meta instance : FromArgs TranslatedOptionOpts m :=
  ⟨TranslatedOptionOpts.mk <$> .positional `name .ident "选项名"⟩
end

@[block_command]
meta def zhOptionDocsFrom : BlockCommandOf TranslatedOptionOpts
  | ⟨name⟩ => do
    let opt ← getOptionDecl name.getId
    let docs ← upstreamTranslation ("option:" ++ name.getId.toString) opt.descr
    let body ← translatedBlocks [] (← getRef) (some docs)
    ``(Doc.Block.other
      (Block.zhOptionDocs $(quote name.getId) $(quote <| highlightDataValue opt.defValue)) #[$body,*])


@[directive]
meta def zhgrindTactic : DirectiveExpanderOf TacticDocsOptions
  | opts, more => do
    let tactic ← Manual.getGrindTactic opts.name opts.allowMissing
    let docs? ← upstreamDocString? tactic.name
    Doc.PointOfInterest.save (← getRef) tactic.name.toString
    let contents ←
      if opts.replace then pure #[]
      else if let some d := docs? then
        let some ast := MD4Lean.parse d
          | throwError "无法解析中文 grind 策略文档"
        ast.blocks.mapM (blockFromMarkdownWithLean [])
      else pure #[]
    let userContents ← more.mapM elabBlock
    let toShow := opts.show.getD tactic.show
    ``(Doc.Block.other
      (Manual.Block.grindTactic $(quote tactic.name) $(quote toShow) $(quote docs?))
      #[$(contents ++ userContents),*])

end Verso.Genre.Manual
