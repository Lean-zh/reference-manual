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

    let declType ← Block.Docstring.DeclType.ofName enName.2 (hideFields := false) (hideStructureConstructor := false)

    let signature ← Signature.forName enName.2

    let extras ← getExtras enName.2 declType

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote enName.2) $(quote declType) $(quote signature) $(quote customLabel)) #[$(blockStx ++ extras),*])]

  | _args, more => throwErrorAt more[0]! "Unexpected block argument"
where
    getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor? _ fieldInfo parents _ => do
      let ctorRow : Option Term ← constructor?.mapM fun constructor => do
        let header := if isClass then "Instance Constructor" else "Constructor"
        let sigDesc : Array Term ←
          if let some docs := constructor.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure (#[] : Array Term)
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "Extends"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

      let fieldsRow : Option Term ← do
        let header := if isClass then "Methods" else "Fields"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs := i.docString? then
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
            if let some docs := c.docstring? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
    | _ => pure #[]

end Verso.Genre.Manual
