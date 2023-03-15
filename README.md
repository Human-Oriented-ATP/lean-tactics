# Human-oriented tactics in Lean

## Setup
1. Download [Lean][1].
2. Download this repository.
3. Go into the `lean3` or `lean4` folder.
4. Run `leanpkg configure` within that folder.  This will download mathlib.
5. Run `leanproject get-mathlib-cache` within that folder.  This will make running Lean files much faster.
6. Open a file (e.g. `lean3/src/change_goal.lean`) in Visual Studio Code to try out examples.

## Tactics written so far in Lean 3

Reasoning tactics:
- `mp`.  Applies modus ponens, adding the resulting statement to the hypothesis. 
- `use_theorem`.  Applies the given theorem to the current goal.  If the conclusion of the theorem matches our goal, then applies the theorem.  Otherwise, if the theorem is an iff or equality, rewrites the goal using the theorem.  Otherwise, fails.
- `begins_with_forall_quantifier`, `begins_with_exists_quantifier`.  Checks if a given expression begins with the specified quantifier.
- `contains_constant`.  Checks if a given expression contains a particular constant (e.g. “degree” or “5”).  Useful for syntax-matching.
- `collect_subexprs`.  Recursively breaks up an expression into all of its subexpressions.  Useful for syntax-matching.
- `collect_nat_subexprs`.  Recursively breaks up an expression into all of its subexpressions.  Useful for syntax-matching on terms that can be compared with inequalities.
- `without_quantifiers`. Recursively peels all quantifiers from an expression.  Useful for quotienting.

Library-retrieval tactics:
- `get_thm_decls`.  Gets all theorems accessible within the current context (with an option to restrict to all theorems relevant to a particular subject area e.g. graph theory). 
- `get_thm_decl`, `get_thm_statement`, `get_thm_proof`.  Gets theorems by name.

Debugging-specific tactics:
- `print_expr_type`.  Given a Lean expression, says whether it is a variable, constant, lambda expression, function application, etc.

## Tactics written so far in Lean 4
\- 

[1]:	https://leanprover.github.io/download/