# Motivated Proof Moves

## Implemented moves

The files in this folder define the tree representation of the proof state, and various moves for manipulating it. The representation uses the `Expr` type defined in Lean which is used by Lean for representing Lean expressions. Almost all moves are interacted with by the user through shift-clicking on expressions.

- **TreeLemmas** defines the binders and logical operators that are used to represent the tree. It also has many lemmas that are used for unfolding and putting back the binders and logical operators.

- **Tree** defines how to make and how to match on these nodes of a tree expression, and how to recurse through them. It also defines a function that turns a regular Lean expression into a tree expression.

- **TreeApply** defines the infrastructure for using a known result to modify the tree. The known result can either be part of the proof state, or be a library result. This is used for the `apply`, `rewrite` and `ordered rewrite` moves. When using a result from inside the tree, we can either delete this result from the tree, or leave it in place. Often it helps to clear used result from the proof state, but sometimes the hypothesis needs to be used multiple times. The moves have support for unfolding any binder in the hypothesis, including side goals and hypotheses in the hypothesis. For example hypotheses in the hypothesis will usually get turned into new goals. The algorithm for this is not quite complete and it is not completely clear how it should work, but it works fine in the examples I've done. See the *TreeRewrite* section for an example.

    The `apply` move depends on the polarity of the selected location, where the polarity of a subexpression is defined to be positive if replacing the expression by a weaker statement (or true) is a valid move, and the polarity is negative if replacing the expression by a stronger statement (or false) is a valid move. In a positive position, `apply` matches the hypothesis to the target and closes the target. In a negative position, the hypothesis is assumed to have the form `p → q`. I then matches `p` to the target and replaces it by `q`.

- **TreeRewrite** defines the `rewrite` move, which uses a hypothesis `a = b` to match `a` to the target and replace it by `b`, or the other way around. This improves on Lean's rewrite tactic, because this cannot rewrite in an expression that is contains a bound variable. So for example in `{a : ℕ | a + 1 = 1}` our rewrite tactic could replace `a + 1` by `1 + a`.

    For example, if the hypothesis says that `∀ g : G, ∃ n : ℕ, g = h ^ n` (i.e. `n ↦ h^n` is surjective), then this can be used for rewriting at any term of type `G`. If the goal is `∀ g : G, p g` for some predicate `p`, then the rewrite turns it into `∀ n : ℕ, p (h ^ n)`. But if the variable `g` appears somewhere else in the predicate, then the new goal will be `∀ g : G, ∀ n : ℕ, p (h ^ n)`. In that case, you could repeat the rewrite step with the same hypothesis, but this would create another binder `∀ n_2 : ℕ,`, and that is not what we want.
    
    There are two ways to solve this, and both should eventually be implemented. One would be to have a rewrite move that can rewrite in multiple positions at the same time, and the other would be to add `g = h ^ n` as a hypothesis. This hypothesis is different from the original hypothesis since it doesn't have its binders. So just like how the user can choose whether the original hypothesis stays in the context, they could choose whether the instantiated version of the hypothesis is put in the context.

    Another example is the common scenario in analysis where the goal if of the form `x + ε₁ < ε₂`, where `ε₁` and `ε₂` are positive reals, and `ε₁` is a metavariable that is allowed to depend on `ε₂`. We can first move `ε₁` to the other side using the right library result, to get to `x < ε₂ - ε₁`. Then we can rewrite using the result that `∀ a : ℝ, a > 0 → ∃ b : ℝ, b > 0 ∧ ∃ c : ℝ, c > 0 ∧ a - b = c` (This might not be a result in mathlib in this form, but we could add it to the environment ourselves so that it is still included in the library search). This will instantiate `a` as `ε₂`, and `ε₁` as `b`. After this we can use the `tree_search` move (see below) to discharge the positivity conditions automatically. After this, we should be left with the goal `x < c`, so effectively we have removed the `ε₁` from the equation. A difficulty with this lemma is that it might not get picked up by the library search because the searched pattern is too general. This could be solved by changing way in which the relevance of a lemma is scored, because matching on `a - b` requires the `b` to be matched with a metavariable, whereas the other lemmas that would show up do not have this requirement, so they could be given a lower score. Alternatively (or additionally), the result could be phrased as `c ≤ a - b`, and then used with the `rewrite_ord` move instead.

- **TreeRewriteOrd** defines the `rewrite_ord` move, which uses a hypothesis `a ≤ b` (or `a < b`, or another relation definitionally equal to `≤` or `<`) and just like `rewrite` replaces `a` by `b` or vice versa. To do this, the idea of polarity of a subexpression is extended from propositions to general preorders: a position is positive if replacing it by a bigger value is a valid move, and is negative if replacing it by a smaller value is a valid move. To determine whether a position is positive or negative and to prove it, we use a type class that allows us to determine whether a function is non-decreasing or non-increasing. Some functions that have instances of this type class are `≤`, `<`, `+`, `-`, `⊆`, `⊂`, and set notation `{a : α | ..}`. `rewrite_ord` can be thought of as being a generalization of `apply` (but `apply` closes the target instead of replacing it by `True`). Unfortunately ordered rewriting under a multiplication is not yet implemented, and it is tricky because multiplication could either be non-decreasing or non-increasing depending on the sign of the number multiplied by.

- **TreeRewriteDef** defines the `rewrite_def` move, which replaces an expression by its definition. This works when the head of the selected expression is a constant that has a definition, or if the head is a projection that can be evaluated. It could be extended to unfold a let expression (ζ-expansion). Or to unfold a match expression or if-then-else expression (but from my limited testing this seems a bit tricky).

- **LibrarySearch** and **DiscrTree** define the infrastructure for library search. Discrimination trees are used to store all imported results and look them up efficiently. This implementation is based on the DiscrTree implementation in Lean, but extends the matching capability.
    - This implementation keeps track of the number of terms that had to match in order for the result to show up, and this 'score' is used to determine the order in which library results are considered and shown to the user.
    - It allows for matching to happen under binders, so that a result like `∀ n : ℕ, ∑ i in Finset.range n, i = n * (n - 1) / 2` can be found by matching the left side.
    - It allows for library results in the discrimination tree to specify when two stars/metavariables are the same. This means that the pattern `a* + a*` in the discrimination tree will only match if the value on both sides of `+` is the same, and if so, this will get a higher score than the pattern `a* + b*`.
    Before using the library search features, the discrimination trees need to be build, which takes 3-4 minutes, but we should be able to cache this information permanently.
    In total 5 discrimination trees are built, 2 for applying in positive and negative position, 1 for rewriting and 2 for ordered rewriting in positive and negative position.

- **TreeInduction** defines the `induction` move, which tries to apply the recursion principle to eliminate a forall variable, or a hypothesis. For example it splits hypotheses as follows:

    - `p ∧ q` splits into separate hypotheses `p` and `q`.
    - `∃ a : α, p` splits into variable `∀ a : α` and hypothesis `p`.
    - `p ∨ q` splits the goal into two duplicate goals, one with hypothesis `p` and one with hypothesis `q`.

    When applied to a `Nat`, it does usual recursion. When applied to a rational it replaces the variable by `Rat.mk' num den`, for `num` a natural and `den` an integer.

    However the function `Rat.mk'` is an implementation detail, so to improve the functionality, instead of always using the built-in recursor, we should have a small library of induction results for each type, so that the user can choose from these. This would also allow for strong induction on natural numbers, and it would allow for splitting a hypothesis `p ∨ q` into one goal with hypothesis `p` and another goal with hypotheses `¬ p` and `q`.

- **TreeNormalize** defines the `tree_simp` and `tree_push_neg` moves. It defines a the framework for using Lean's simp function with any simp context and discharger on the selected subexpression. `tree_simp` uses the standard `simp` lemmas, and `tree_push_neg` only uses lemmas for pushing negations.

- **TreeSearch** defines the `tree_search` move, which does a very basic search through the proofstate to check if there is any goal that is equal to a hypothesis or equal to another goal, and if so, closes it. This could easily be extended to check for unification instead of equality.

- **PrintTree** defines the delaboration function for tree expressions. This allows us to choose how the tree is represented to the user, and also to specify which parts of the expression can be clicked on and what subexpression position is associated to this click.

- **TreeMoves** imports all of the moves, so to load all moves, just write `import TreeMoves.TreeMoves`.

## Future moves
I still have to add `Or` and `Not` as nodes in the tree representation. There are still moves left that have not been implemented yet:

- **Renaming variables / α-conversion** Currently, using library results causes the original variable names to also appear in the resulting proof state. One way to solve this problem is to allow the user to select a binder and type in a new name for this variable. Name ambiguities are clarified adding a `_n` suffix to the name, where `n` is the smallest available number.

- **Instantiating meta variables** Instead of using a predefined way of constructing an element, we can let the user to select any function (possibly of arity 0) that appears in the problem state, whose return type is the type we want to construct. If the arity is 0, then this is equivalent to instantiating metavariables, and for each higher arity a new metavariable is created.

- **Constructing structures/inductive types**. In some sense this is the inverse of induction, which deconstructs structures/inductive types. Just like with induction, we could make a version that is based on the definition of the type, but more generally we would want to have a library which stores a bunch of ways to construct elements of various types. Some example usages would be
    - replacing a goal `p ∨ q` by either `p` or `q`.
    - constructing a rational by giving the numerator and denominator.
    - constructing an element of a quotient type by giving an element of the original type.
    
- **Naming subexpressions** This requires `let` statements to be a part of the tree representation. The user would click on one or more identical expressions, and provide a name, and then these expressions are replaced by this new variable, and a `let` statement appears for the variable. Another move for a `let` expression would be to abstract it, i.e. forget the `let` definition.

