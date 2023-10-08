import TreeMoves.Tree

/-!
The `unification_step` move allows the user to work on instantiating a metavariable that appears in a
reflexive relation, but matching it with the head expression on the other side of the relation

Loop through the tree to the selected position, introducing free and meta variables.
Check that the selection is in positive position, and is one side of a reflexive relation, and that the selected side, 
after whnfD has a meta variables head. The other side must have a constant as the head.
Forall telescope the type of this constant, to find which arguments are implicit and explicit.
this can work for non-constant heads as well, where we assume all arguments are explicit.
for each explicit argument, introduce a new meta variable. Construct the conjunction of the equalities
of these variables to the respective arguments, and construct the proof that this conjunction proves the original relation.
To check that the constructed assignment of the metavariable is possible, use `isDefEq mvar e` instead of `mvarId.assign e`.
The value we return is a combination of the TreeProof, and the list of new meta variables, so that we can bind them
in the right position.
-/

