import Lean
import Std
import ProofWidgets

open Lean Meta Server ProofWidgets Json Jsx

namespace ProofWidgets
open Lean Server Elab Command Lsp

/-- Parameters for editing the text document through the Language Server Protocol.
    These are used by the button to make edits on click and change the cursor position. -/
structure EditParams where
  edit : Lsp.TextDocumentEdit
  newCursorPos? : Option Lsp.Position := none
deriving RpcEncodable

namespace EditParams

/-- Replace `range` with `newText` and then place the cursor at the end of the new text. -/
def ofReplaceRange (meta : Server.DocumentMeta) (range : Lsp.Range)
    (newText : String) : EditParams :=
  let edit := { textDocument := { uri := meta.uri, version? := meta.version }
                edits        := #[{ range, newText }] }
  let newCursorPos? := some {
    line := range.start.line
    character := range.start.character + newText.codepointPosToUtf16Pos newText.length
  }
  { edit, newCursorPos? }

/-- Insert a line with the given text, a useful special case of replacing a range. -/
def insertLine (meta : Server.DocumentMeta) (line : Nat) 
    (indent : Nat) (text : String) : EditParams :=
  let newText := "".pushn ' ' indent ++ text
  let pos := { line := line, character := 0 }
  EditParams.ofReplaceRange meta ⟨pos, pos⟩ newText

end EditParams


section DynamicButton

/-!

## Buttons

Most of the interaction in the point-and-click interface happens through buttons.
These are implemented as a React JS Component using `ProofWidgets`.
-/

-- TODO: Make these inductive types
/-- Styling parameters for buttons. -/
structure DynamicButtonStylingProps where
  variant : String := "outlined" -- 'text' | 'outlined' | 'contained'
  color : String := "primary" -- 'inherit' | 'primary' | 'secondary' | 'success' | 'error' | 'info' | 'warning'
  size : String := "medium" -- 'small' | 'medium' | 'large'

/-- The parameters that can be supplied to a button.
    Buttons can optionally insert text in the editor and render HTML on click.
    They can also be made to vanish on click. -/
structure DynamicButtonProps extends DynamicButtonStylingProps where
  label : String
  edit? : Option EditParams := none
  html? : Option Html := none
  vanish : Bool := false
  key   :=   label  -- this is needed for technical reasons to do with rendering React components
deriving RpcEncodable

/-- The implementation of the button as a component with the logic specified in the JavaScript code.
    Run `lake build customWidgetJs` to build this JavaScript file. -/
@[widget_module] def DynamicButton : Component DynamicButtonProps where
  javascript := include_str ".." / ".." / "build" / "js" / "dynamicButton.js"

/-- A wrapper around `DynamicButton` that requires an `Lsp.Range` instead of `EditParams`.
    This is usually much more convenient in practice. -/
structure DynamicEditButtonProps extends DynamicButtonStylingProps where
  label : String
  range? : Option Lsp.Range := none
  insertion? : Option String := none
  html? : Option Html := none
  vanish : Bool := false
deriving RpcEncodable

/-- The logic for generating a `DynamicButton` from the `DynamicEditButtonParams`. -/
@[server_rpc_method]
def DynamicEditButton.rpc (props : DynamicEditButtonProps) : RequestM (RequestTask Html) := do
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let editParams? : Option EditParams := do 
      let range ← props.range?
      let insertion ← props.insertion?
      return .ofReplaceRange doc.meta range insertion
    return .ofComponent DynamicButton (children := #[])
      { label := props.label
        edit? := editParams?
        html? := props.html?
        vanish := props.vanish
        variant := props.variant
        color := props.color
        size := props.size }

/-- The implementation of `DynamicEditButtons` using `DynamicEditButtons.rpc`. -/
@[widget_module] def DynamicEditButton : Component DynamicEditButtonProps :=
  mk_rpc_widget% DynamicEditButton.rpc

end DynamicButton

section

open MonadExceptOf Elab Tactic

-- Jovan's `tree_rewrite_def`

partial def reduceProjection (e : Expr) : ExceptT MessageData MetaM Expr :=
  e.withAppRev fun f revArgs => match f with
    | .proj _ i b => do
      let some value ← project? b i | throw m! "could not project expression {b}"
      reduceProjection (value.betaRev revArgs)
    | _ => return e

def replaceByDefAux (e : Expr) : ExceptT MessageData MetaM Expr := do
  if let .letE _ _ v b _ := e then return b.instantiate1 v
  e.withAppRev fun f revArgs => match f with
    | .const name us => do
      let info ← getConstInfoDefn name
      let result := info.value.instantiateLevelParams info.levelParams us
      if ← isDefEq result f then
        reduceProjection (result.betaRev revArgs)
      else
        throw m! "could not replace {f} by its definition"
    | _ => do
      let result ← reduceProjection (f.betaRev revArgs)
      if result == e then throw m! "could not find a definition for {e}"
      else return result

def replaceByDef (pos : SubExpr.Pos) (e : Expr) : MetaM Expr := do
  match ← (replaceSubexpr replaceByDefAux pos e).run with
  | .error e => throwError e
  | .ok result => return result

def unfoldDefinitionAtGoalLoc (mvarId : MVarId) : SubExpr.GoalLocation → MetaM MVarId
  | .hyp _ => pure mvarId
  | .hypType fvarId pos =>
    mvarId.withContext do
      let hypType ← fvarId.getType 
      mvarId.replaceLocalDeclDefEq fvarId =<<
        replaceByDef pos hypType
  | .hypValue _ _ => pure mvarId -- TODO: Implement this case
  | .target pos => 
    mvarId.withContext do
      let target ← mvarId.getType
      mvarId.replaceTargetDefEq =<< 
        replaceByDef pos target

syntax (name := unfold) "unfold" " at" (term <|> "⊢") " position " str : tactic

@[tactic unfold]
def unfoldTac : Tactic
  | `(tactic| unfold at ⊢ position $pos:str) => do
    let loc : SubExpr.GoalLocation := .target (.fromString! pos.getString)
    liftMetaTactic1 (unfoldDefinitionAtGoalLoc · loc)
  | `(tactic| unfold at $h:term position $pos:str) => do
    let fvarId ← getFVarId h
    let loc : SubExpr.GoalLocation := .hypType fvarId (.fromString! pos.getString)
    liftMetaTactic1 (unfoldDefinitionAtGoalLoc · loc)
  | _ => throwUnsupportedSyntax

end

section

structure UIProps extends PanelWidgetProps where
  range : Lsp.Range
deriving RpcEncodable

@[server_rpc_method]
def Unfold.rpc (props : UIProps) : RequestM (RequestTask Html) := do
  -- let doc ← RequestM.readDoc
  let #[loc] := props.selectedLocations | return .pure <p>Select a sub-expression to unfold.</p>
  let .some goal := props.goals.find? (·.mvarId == loc.mvarId) | return .pure <p>No goals found.</p>
  let tacticStr : String ← 
    goal.ctx.val.runMetaM {} do -- following `SelectInsertConv`
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        match loc.loc with
          | .target pos => do
              return s!"unfold at ⊢ position \"{pos.toString}\""
          | .hypType fvarId pos => do
              let hypName ← fvarId.getUserName
              return s!"unfold at {hypName.toString} position \"{pos.toString}\""
          | _ => return ""  
  return .pure (
        <DynamicEditButton 
          label={"Unfold definition"} 
          range?={props.range} 
          insertion?={tacticStr} 
          variant={"contained"} 
          size={"small"} />
      )

@[widget_module]
def Unfold : Component UIProps := 
  mk_rpc_widget% Unfold.rpc

elab stx:"unfold?" : tactic => do
  let range := (← getFileMap).rangeOfStx? stx 
  savePanelWidgetInfo stx ``Unfold do
    return json% { range : $(range) }

end

section Test

def f := Nat.add

example : f 1 2 = 3 := by
  unfold? -- click on `f 1 2`
  sorry

end Test