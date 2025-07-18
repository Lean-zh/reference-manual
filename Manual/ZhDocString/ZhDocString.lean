import Std.Data.HashSet

import VersoManual
import Verso

import Verso.Doc.Elab.Monad
import SubVerso.Highlighting

import MD4Lean

open Lean
open Std (HashSet)

open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse
open Verso.Code.Highlighted.WebAssets
open Verso.Doc.Elab

open SubVerso.Highlighting

namespace Verso.Genre.Manual

section
variable {m}
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]

structure ZhDocstringOpts where
  enName : Ident × Name
  zhName : Ident × Name
  label : Option String := none

def ZhDocstringOpts.parse : ArgParse m ZhDocstringOpts :=
  ZhDocstringOpts.mk <$>
    .positional ``enName .documentableName <*>
    .positional ``zhName .documentableName <*>
    .named `label .string true
end


@[block_role_expander zhdocstring]
def zhdocstring : BlockRoleExpander
  | args, #[] => do
    let ⟨enName, zhName, customLabel⟩  ← ZhDocstringOpts.parse.run args
    let blockStx ←
      match ← getDocString? (← getEnv) zhName.2 with
      | none => pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwError "Failed to parse docstring as Markdown"
        ast.blocks.mapM (blockFromMarkdownWithLean [zhName.2])

    let enDeclType ← Block.Docstring.DeclType.ofName enName.2 (hideFields := false) (hideStructureConstructor := false)
    let zhDeclType ← Block.Docstring.DeclType.ofName zhName.2 (hideFields := false) (hideStructureConstructor := false)

    let enSignature ← Signature.forName enName.2

    let extras ← getExtras enName.2 zhName.2 enDeclType zhDeclType

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote enName.2) $(quote enDeclType) $(quote enSignature) $(quote customLabel)) #[$(blockStx ++ extras),*])]

  | _args, more => throwErrorAt more[0]! "Unexpected block argument"
where
    getExtras (enName: Name) (zhName : Name) (enDeclType : Block.Docstring.DeclType) (zhDeclType:Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match enDeclType with
    | .structure enIsClass enConstructor? _ enFieldInfo enParents _ => do
      match zhDeclType with
      | .structure zhIsClass zhConstructor? _ zhFieldInfo zhParents _ => do
        match enConstructor? with
        | none => pure (#[] : Array Term)
        | some enConstructor =>
          let ctorRow : Option Term ← zhConstructor?.mapM fun zhConstructor => do
            let header := if zhIsClass then "Instance Constructor" else "Constructor"
            let sigDesc : Array Term ←
              if let some docs := zhConstructor.docstring? then
                let some mdAst := MD4Lean.parse docs
                  | throwError "Failed to parse docstring as Markdown"
                mdAst.blocks.mapM (blockFromMarkdownWithLean [enName, enConstructor.name])
              else pure (#[] : Array Term)
            let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote enConstructor.hlName) none) #[$sigDesc,*])
            ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

          let parentsRow : Option Term ← do
            if enParents.isEmpty then pure none
            else
              let header := "Extends"
              let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote enName) $(quote zhParents)) #[])
              some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

          let fieldsRow : Option Term ← do
            let header := if enIsClass then "Methods" else "Fields"
            -- 由于field不会打印namespace，所以这里直接采用zhFieldInfo
            let fieldInfo := zhFieldInfo.filter (·.subobject?.isNone)
            let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
              let inheritedFrom : Option Nat :=
                i.fieldFrom.head?.bind (fun n => enParents.findIdx? (·.name == n.name))
              let sigDesc : Array Term ←
                if let some docs := i.docString? then
                  let some mdAst := MD4Lean.parse docs
                    | throwError "Failed to parse docstring as Markdown"
                  mdAst.blocks.mapM (blockFromMarkdownWithLean <| enName :: (zhConstructor?.map ([·.name])).getD [])
                else
                  pure (#[] : Array Term)
              ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| zhParents.map (·.parent))) #[$sigDesc,*])
            if fieldSigs.isEmpty then pure none
            else some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])

          pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
      | _ => pure #[]
    | .inductive enCtors .. => do
      match zhDeclType with
      | .inductive zhCtors .. => do
        let ctorSigs : Array Term ←
          if enCtors.size = zhCtors.size then
            -- Elaborate constructor docs in the type's NS
            -- 原代码有一句 withTheReader Core.Context ({· with currNamespace := enName})
            (enCtors.zip zhCtors).mapM fun c =>
            do
              let sigDesc ←
                if let some docs := c.2.docstring? then
                  let some mdAst := MD4Lean.parse docs
                    | throwError "Failed to parse docstring as Markdown"
                  mdAst.blocks.mapM (blockFromMarkdownWithLean [enName, c.1.name])
                else pure (#[] : Array Term)
              ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.1.signature)) #[$sigDesc,*])
          else
            pure #[]
          pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
      | _ => pure #[]
    | _ => pure #[]

section
variable {m}
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadEnv m]
variable [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadWithOptions m]
variable [Lean.Elab.MonadInfoTree m]

structure zhOptionDocsOpts where
  enName : Ident
  zhName : Ident × Name

def zhOptionDocsOpts.parse : ArgParse m zhOptionDocsOpts :=
  zhOptionDocsOpts.mk <$>
    .positional ``enName .ident <*>
    .positional ``zhName .documentableName


end

def Block.zhOptionDocs (name : Name) (defaultValue : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.zhOptionDocs
  data := ToJson.toJson (name, defaultValue)

@[block_role_expander zhOptionDocs]
def zhOptionDocs : BlockRoleExpander
  | args, #[] => do
    let ⟨ enName, zhName ⟩  ← zhOptionDocsOpts.parse.run args
    let optDecl ← getOptionDecl enName.1.getId
    let blockStx ←
      match ← getDocString? (← getEnv) zhName.2 with
      | none => pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwError "Failed to parse docstring as Markdown"
        ast.blocks.mapM (blockFromMarkdownWithLean [zhName.2])
    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.zhOptionDocs $(quote enName.1.getId) $(quote <| highlightDataValue optDecl.defValue)) #[$blockStx,*])]

  | _, more => throwErrorAt more[0]! "Unexpected block argument"

open Verso.Genre.Manual.Markdown in
@[block_extension zhOptionDocs]
def zhOptionDocs.descr : BlockDescr where
  init st := st
    |>.setDomainTitle optionDomain "Compiler options"

  traverse id info _ := do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | do logError "Failed to deserialize docstring data while traversing an option"; pure none

    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    modify fun st => st.saveDomainObject optionDomain name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML for an option"; pure .empty
      let x : Html := Html.text true <| Name.toString name

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"option"</span>
          <pre class="signature hl lean block">{{x}}</pre>
          <div class="text">
            <p>"默认值: " <code class="hl lean inline">{{← defaultValue.toHtml}}</code></p>
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (name, _defaultValue) ← FromJson.fromJson? (α := Name × Highlighted) info
    pure #[
      (name.toString, {{<code>{{name.toString}}</code>}}),
      (s!"{name.toString} (Option)", {{<code>{{name.toString}}</code>" (Option)"}})
    ]
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]

end Verso.Genre.Manual
