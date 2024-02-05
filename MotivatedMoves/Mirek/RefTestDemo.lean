import MotivatedMoves.Mirek.RefTest

#eval (testRef.get : IO Nat)

open scoped ProofWidgets.Jsx in
#html <TestRef />

#eval (testRef.get : IO Nat)
