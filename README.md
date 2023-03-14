# Human-oriented tactics in Lean

## Setup
1. Download [Lean][1].
2. Download this repository.
3. Go into the `lean3` or `lean4` folder.
4. Run `leanpkg configure` within that folder.  This will download mathlib.
5. Run `leanproject get-mathlib-cache` within that folder.  This will make running Lean files much faster.
6. Open a file (e.g. `lean3/src/change_goal.lean`) in Visual Studio Code to try out examples.

## Tactics written so far in Lean 3
- `use_theorem`.  Applies the given theorem to the current goal.  If the conclusion of the theorem matches our goal, then applies the theorem.  Otherwise, if the theorem is an iff or equality, rewrites the goal using the theorem.  Otherwise, fails.

There are also some debugging-specific tactics like:
- `print_expr_type`.  Given a Lean expression, says whether it is a variable, constant, lambda expression, function application, etc.

## Tactics written so far in Lean 4
\- 

[1]:	https://leanprover.github.io/download/