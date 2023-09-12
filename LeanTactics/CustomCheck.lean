import Lean

open Lean Elab

elab "#" ι:ident : command =>
  for c in (← resolveGlobalConstWithInfos ι) do
    addCompletionInfo <| .id ι c (danglingDot := false) {} none

# Syntax