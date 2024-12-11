# Autogeneralize
## Troubleshooting the computation rule issue

### The issue

It's possible for the `autogeneralize` algorithm to get stuck in situations where
- there are two terms in the original proof that are definitionally equal (technically, one of the terms could be present at the type level, and that is typically the situation in which the error arises) 
- after `autogeneralizing` a constant `c` in the proof, one of these terms generalizes and is no longer definitionally equal to the other one 
- the type mismatch created by this makes the generalized proof invalid

Ideally, we would want `autogeneralize` to also generalize the portion of the proof where the mismatch occurs. A few possible approaches to this are listed below.

### **Approach 1:** Making multiple calls to `autogeneralize` (manual approach)

A quick fix to the problem, but not a very satisfactory one, is to manually identify terms in the proof that need to be generalized in order for the conflicts to be resolved, and then make a sequence of calls to the `autogeneralize` tactic, each generalizing a term that conflicts with the main one.

### **Approach 2:** Recognizing mismatches with anti-unification and automatically making additional calls to `autogeneralize` 

A natural improvement to **Approach 1** would be to automatically identify the list of terms that need to be generalized and then generate a sequence of tactic calls that generalize these terms in the right order.

This would require intercepting the error messages when they occur and extracting the relevant terms from them. The error messages produce a pair of conflicting terms which may agree in some portions and differ in others; an *anti-unification* algorithm (Anshula's idea) would be able to pull out precisely where the conflicting terms occur and suggest which other terms to generalize. 

### **Approach 3:** Pre-processing the proof term to make applications of computation rules explicit

It's possible that `autogeneralizing` in the presence of related constants would be made easier if applications of computation rules in the proof were *explicit*, rather than implicit. This approach would require traversing the proof term and performing explicit casting of terms along definitional equalities.

### **Approach 4:** Re-designing `autogeneralize` around the bi-directional typing algorithm

The idea here is roughly to have the expected type constraints "flow" down into the term, generalizing sub-terms that don't exactly meet their required type constraint.
