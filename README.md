# Human-oriented tactics in Lean

## Lean 3 Setup
1. Download [Lean][1].
2. Download VSCode and its Lean3 extension.
3. Download [mathlib-tools][2] in order to have access to the `leanproject` command.
4. `git clone` this repository.
5. Open the `lean3` folder
	- Run `leanpkg configure` within that folder.  This will download mathlib.
	-  Run `leanproject get-mathlib-cache` within that folder.  This will make running Lean files much faster.
6. Open the `lean3`  folder in VSCode (not the parent folder).
	- Open a file (e.g. `lean3/src/change_goal.lean`) in VSCode to try out examples.

## Lean 4 Setup
1. Download VSCode.
2. Install its Lean4 extension.
4. `git clone` this repository.
5. Open the `lean4` folder of that repository and run `lake update`. This will download mathlib4 which you will then find in the folder `lake-packages`.
7. Test that your install of mathlib has worked. For example, you could create a file like this: 
```
import Mathlib.Data.Vector.Basic

#check Vector
```
It might take a while for Lean4 to build Mathlib in the background, you should see an info text that tells you the file that is currently being built. 
8. For more convenience, you can get the mathlib cache files as described in the readme of https://github.com/leanprover-community/mathlib4

## Tactics written so far in Lean 3

High-level reasoning tactics:
- `mp`.  Applies modus ponens, adding the resulting statement to the hypothesis. 
- `use_theorem`.  Applies the given theorem to the current goal.  If the conclusion of the theorem matches our goal, then applies the theorem.  Otherwise, if the theorem is an iff or equality, rewrites the goal using the theorem.  Otherwise, fails.
- `get_strongest_syntactic_match`.  Returns name of theorem that most strongly matches the goal.  Right now, “strongest match” means “longest common substring”, but this can be updated to something more robust later.

Low-level reasoning tactics:
- `begins_with_forall_quantifier`, `begins_with_exists_quantifier`.  Checks if a given expression begins with the specified quantifier.
- `without_quantifiers`. Recursively peels all quantifiers from an expression.  Useful for quotienting.
- `contains_constant`.  Checks if a given expression contains a particular constant (e.g. “degree” or “5”).  Useful for syntax-matching.
- `eq_ignoring_locals`. Checks if two expressions are equal, ignoring “holes” filled with local constants or variables.  Useful for syntax-matching.
- `collect_subexprs` and `collect_nat_subexprs`.  Recursively breaks up an expression into all of its subexpressions.  Useful for syntax-matching (and `nat` version is useful for syntax-matching between terms that can be compared with inequalities).
- `contains_subexpr` and `contains_nat_subexpr`.  Checks expressions for particular subexpressions.
- `is_upper_bound_on` and `is_lower_bound_on`.  A theorem `is_upper_bound_on` an expression `e` when the theorem is an equality or inequality with an expression depending on `e` on the lesser side.  The name is a bit misleading, because if `e` is in the denominator, it actually gives a lower bound.  Analogous for `is_lower_bound_on`.
- `add_theorem_to_hypothesis`.   Adds theorem by name.
- `in_hypothesis`. Checks if theorem is already in hypothesis (potentially under a different name).

Library-retrieval tactics:
- `get_thm_decls`.  Gets all theorems accessible within the current context (with an option to restrict to all theorems relevant to a particular subject area e.g. graph theory). 
- `get_thm_decl`, `get_thm_statement`, `get_thm_proof`.  Gets theorems by name.
- `get_all_theorems_with_const`.  Gets theorem that contain a specific constant e.g. “degree” or “5.”
- `get_all_theorems_with_subexpr`.  Gets all theorems that contain a specific subexpression e.g. `|V| choose 2`.
- `extract_to_expand_inequality`.   If the goal is an inequality A \< C, and there are two inequalities A \< B and B \< C in the library, add those inequalities to the hypothesis.
- `get_upper_bounds_on` and `get_lower_bounds_on`.  Gets all theorems (equalities and inequalities) that provide the given bounds on the argument expression.

Debugging tactics:
- `print_expr_type`.  Given a Lean expression, says whether it is a variable, constant, lambda expression, function application, etc.

## Tactics written so far in Lean 4
\- 

[1]:	https://leanprover.github.io/download/
[2]:	https://github.com/leanprover-community/mathlib-tools
