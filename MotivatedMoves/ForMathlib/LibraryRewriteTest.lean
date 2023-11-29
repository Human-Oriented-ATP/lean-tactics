import MotivatedMoves.ForMathlib.LibraryRewrite
import Mathlib.Algebra.Group.Defs

example [Group G] (g h : G) : (g * g⁻¹) * h = h := by
  rw (config := { occs := .pos [1] }) [mul_inv_self g]
  rw (config := { occs := .pos [1] }) [Group.toCancelMonoid.proof_2 h]