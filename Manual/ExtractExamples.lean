/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/

import Manual.Meta.Example
import VersoManual
open Lean
open Verso Doc Multi
open Verso.Genre Manual
open Std (HashMap)

/--
A monad for traversing all example directives in a document, and
extracting them into individual files in a directory structured as the
document is structured. In the `Array (Array String × String)`, the
first string is the path to the example file we're writing, and the
second is the body of the example.
-/
abbrev ExtractM := ReaderT (Array String) (StateT (Array (Array String × String)) (BuildLogT IO))

partial def extractExamples (_mode : Mode) (cfg : Manual.Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do

  let code := (← part text |>.run #[] |>.run #[]).snd
  let dest := cfg.destination / "extracted-examples"
  -- Translated titles can share a slug. Start with a clean output directory and disambiguate
  -- collisions, so every example is checked and deleted or renamed examples cannot survive.
  if ← dest.pathExists then IO.FS.removeDirAll dest
  let mut used : Std.HashSet String := {}
  for (ctx, content) in code do

    let base := ctx.map (Slug.toString ∘ String.sluggify)
      |>.foldl (init := dest) (· / ·)
      |>.withExtension "lean"
    let mut filename := base
    let mut suffix := 1
    while used.contains filename.toString do
      filename := base.withFileName s!"{base.fileStem.getD "example"}-{suffix}.lean"
      suffix := suffix + 1
    used := used.insert filename.toString
    filename.parent.forM fun p => IO.FS.createDirAll p
    IO.FS.writeFile filename content
  IO.println s!"Extracted {code.size} independent Lean examples."

where
  part : Part Manual → ExtractM Unit
    | .mk _ titleString metadata intro subParts =>
      let extractionTitle := metadata.bind (·.file) |>.getD titleString
      withReader (·.push extractionTitle) do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → ExtractM Unit
    | .other which contents => do
      if which.name == `Manual.example then
        match FromJson.fromJson? which.data (α := Manual.ExampleBlockJson) with
        | .error e => reportError s!"Error deserializing example data: {e}"
        | .ok (descrString, _, _, _, liveText) =>
          let context ← read
          let some txt := liveText
            | return ()
          let extractionTitle :=
            which.properties[`Manual.exampleExtractionContext]?.getD descrString
          modify fun saved =>
            saved.push (context.push extractionTitle, txt)
      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()
