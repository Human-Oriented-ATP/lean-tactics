------------------------------------------------
------------------------------------------------
-- Dealing with finite, simple graphs.  From the ground up. --
------------------------------------------------
------------------------------------------------
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.hasse -- path graphs
import combinatorics.simple_graph.partition -- bipartite graphs
.

open_locale big_operators -- enable ∑ notation
open simple_graph

universes u
variables {V : Type u}  
          --{G : simple_graph V}  -- the graph is simple
          --[fintype V]           -- the graph is finite (necessary for vertex set cardinality to be computed)
          --[decidable_rel G.adj] -- whether two vertices are adjacent is decidable (necessary for vertex degree to be computed)
          --[decidable_eq V]      -- whether two vertices are equal is decidable (necessary for edge_set cardinality to be computed)


------------------------------------------------
-- Setting up shorthand notations. --
------------------------------------------------
notation  X `[G]` := @finset.univ X _   -- V[G]
notation `E[` X `]`   := X.edge_finset -- E[G]
notation `∣∣` X `∣∣`  := X.card         -- ∣∣(V[G])∣∣ or ∣∣E[G]∣∣

------------------------------------------------
-- Tag allowable graph theory theorems --
------------------------------------------------
@[user_attribute]
meta def graph_theory_attr : user_attribute :=
{ name := `graph_theory,
  descr := "A tag for all allowable graph_theory theorems our machine can use." }

------------------------------------------------
-- The allowable theorems --
------------------------------------------------

-- In a simple graph, a vertex connects to at most (n-1) other vertices --
@[graph_theory] 
theorem degree_bound (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∀ v : V, G.degree v ≤ ∣∣(V[G])∣∣ - 1 :=
begin
  intros v,
  have := simple_graph.degree_lt_card_verts G v, 
  rw finset.card_univ, apply nat.le_pred_of_lt, assumption,
end

-- The degree-sum formula: the sum of the degrees = twice the number of edges --
@[graph_theory] 
theorem degree_sum (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∑v,  G.degree v = 2 * ∣∣E[G]∣∣ :=
begin
  apply sum_degrees_eq_twice_card_edges G,
end

-- Handshaking lemma : the sum of degrees is even --
@[graph_theory] 
theorem degree_sum_even (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  even (∑v,  G.degree v) :=
begin
  rw degree_sum, simp,
end 

-- Graphs have at most (n choose 2) edges --
@[graph_theory] 
theorem edge_bound (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
begin 
  have ds := degree_sum G, -- syntactic match to this theorem, so lets add it to hypothesis
  have db := degree_bound G, -- syntactic match to this theorem, so lets add it to hypothesis
  rw nat.choose_two_right, -- expand out "choose", since there is nothing else involving "choose" in hypotheses or library

  -- we HAVE something to do with |E| =  something to do with degree
  -- then we HAVE something to do with degree <= something to do with |V|
  -- and we WANT something to do with |E| <= something to do with |V|
  -- so the steps should be clear, abstractly, in the "quotient graph"

  -- first isolate |E|, applying that it has something to do with degree
  replace ds : G.edge_finset.card = (∑v,  G.degree v) / 2 := by {rw ds, simp},
  rw ds, clear ds,-- rewrite the goal using that |E| 

 -- then apply that degree can be bounded by something to do with |V|
  replace db : ∀ (v : V), v ∈ (V[G]) → G.degree v ≤ ∣∣(V[G])∣∣ - 1 := by {intros v h, exact db v},
  have h := finset.sum_le_sum db, dsimp at h, rw finset.sum_const at h, -- apply this theorem to get a closer syntactic match to the goal
  apply nat.div_le_div_right, exact h, -- tidy to get a closer syntactic match to the goal

end

-- Every path is bipartite --
-- @[graph_theory] 
-- def is_bipartite (G : simple_graph V) := G.partitionable 2
-- theorem path_is_bipartite (n : ℕ) : ∀n : ℕ, is_bipartite (path_graph n) :=
-- begin 
--   intro n,
--   rw is_bipartite,
--   rw partitionable,
--   -- the odd-indexed vertices go in one partition
--   -- the even-indexed vertices go in the other
-- end