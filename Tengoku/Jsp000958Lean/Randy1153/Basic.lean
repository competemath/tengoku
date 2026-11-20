import Tengoku.Jsp000958Lean.Randy1153.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic facts about the Randy 1153 interpolation objects

This module develops elementary consequences of the frozen statement
interface.  It does not introduce a second representation of nodes or of the
Lagrange and Lebesgue functions.
-/

namespace Randy1153

open Polynomial

noncomputable section

/-- Two node families with the same enumerating function are equal; the
remaining fields are propositions.
@isnad1 id=eq.1h3v.s4.280765371d85 from=translated src=- shape=675044bd vocab=cbc498f0
-/
@[ext]
lemma NodeFamily.ext {n : ℕ} {x y : NodeFamily n} (h : x.point = y.point) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Distinct indices in a node family have distinct values.
@isnad1 id=ne.1h4v.s4.604f47f1c262 from=translated src=- shape=72eeac5c vocab=cbc498f0
-/
lemma NodeFamily.point_ne {n : ℕ} (nodes : NodeFamily n) {i j : Fin n}
    (hij : i ≠ j) : nodes.point i ≠ nodes.point j :=
  fun h => hij (nodes.injective h)

/-- The literal fundamental function is one at its own node.
@isnad1 id=eq.0h3v.s4.9eed6ae1aae0 from=translated src=- shape=ea0a3969 vocab=ea9054ee
-/
@[simp]
lemma lagrangeFundamental_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeFundamental nodes k (nodes.point k) = 1 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_self nodes k

/-- The literal fundamental function vanishes at every other node.
@isnad1 id=eq.1h4v.s5.f4fa712af071 from=translated src=- shape=218bc66a vocab=ea9054ee
-/
@[simp]
lemma lagrangeFundamental_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    lagrangeFundamental nodes k (nodes.point j) = 0 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_of_ne nodes hjk

/-- A Lagrange fundamental polynomial has exactly the expected natural
degree.  The presence of `k : Fin n` already implies `0 < n`.
@isnad1 id=eq.0h3v.s4.4c760a6ce22d from=translated src=- shape=19d46099 vocab=6dc8071c
-/
lemma natDegree_lagrangeBasis {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).natDegree = n - 1 := by
  simpa only [lagrangeBasis, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.natDegree_basis nodes.injective.injOn (Finset.mem_univ k))

/-- Degree bound used by interpolation and uniqueness arguments.
@isnad1 id=le.0h3v.s4.77aa5d983da2 from=translated src=- shape=19d46099 vocab=54bac9a2
-/
lemma natDegree_lagrangeBasis_le {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).natDegree ≤ n - 1 :=
  (natDegree_lagrangeBasis nodes k).le

/-- The polynomial degree version of `natDegree_lagrangeBasis`.
@isnad1 id=eq.0h3v.s5.c366eb762c7c from=translated src=- shape=36239535 vocab=0afe2f60
-/
lemma degree_lagrangeBasis {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).degree = (n - 1 : ℕ) := by
  simpa only [lagrangeBasis, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.degree_basis nodes.injective.injOn (Finset.mem_univ k))

/-- The Lebesgue function is pointwise nonnegative.
@isnad1 id=le.0h3v.s4.50ecbc6b2d67 from=translated src=- shape=33fe603d vocab=39cedbf7
-/
lemma lebesgueFunction_nonneg {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    0 ≤ lebesgueFunction nodes t := by
  simp only [lebesgueFunction]
  positivity

/-- At every interpolation node, the Lebesgue function equals one.
@isnad1 id=eq.0h3v.s4.99dccae20e9a from=translated src=- shape=09fff802 vocab=a2a01cd5
-/
@[simp]
lemma lebesgueFunction_at_node {n : ℕ} (nodes : NodeFamily n) (j : Fin n) :
    lebesgueFunction nodes (nodes.point j) = 1 := by
  classical
  rw [lebesgueFunction, Fintype.sum_eq_single j]
  · simp
  · intro k hjk
    simp [lagrangeFundamental_of_ne nodes hjk.symm]

end

end Randy1153
