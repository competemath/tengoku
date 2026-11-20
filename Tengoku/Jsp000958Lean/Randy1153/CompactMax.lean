import Tengoku.Jsp000958Lean.Randy1153.Interpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact-interval maximum conveniences

The frozen statement module already proves continuity, compact attainment,
and the strict-bound witness equivalence.  This file adds the order-theoretic
consequences and interpolation estimates that later proof modules consume.
-/

namespace Randy1153

open Polynomial

noncomputable section

/-- Every value on a nonempty closed interval is bounded by `lebesgueOn`.
@isnad1 id=le.2h5v.s5.ea9f30cfa07b from=translated src=- shape=87730385 vocab=f650876d
-/
lemma lebesgueFunction_le_lebesgueOn {n : ℕ} (nodes : NodeFamily n)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) :
    lebesgueFunction nodes t ≤ lebesgueOn nodes a b := by
  obtain ⟨u, hu, hsup, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [hsup]
  exact hmax t ht

/-- A compact interval supremum of the Lebesgue function is nonnegative.
@isnad1 id=le.1h4v.s4.2a97cb0c55ae from=translated src=- shape=902bbb25 vocab=2fee5efb
-/
lemma lebesgueOn_nonneg {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (hab : a ≤ b) : 0 ≤ lebesgueOn nodes a b := by
  exact (lebesgueFunction_nonneg nodes a).trans
    (lebesgueFunction_le_lebesgueOn nodes hab ⟨le_rfl, hab⟩)

/-- A universal upper bound on the interval bounds its compact supremum.
@isnad1 id=iff.1h5v.s5.f738651b5f62 from=translated src=- shape=84dfb4ee vocab=f650876d
-/
lemma lebesgueOn_le_iff {n : ℕ} (nodes : NodeFamily n) {a b C : ℝ}
    (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ C ↔
      ∀ t ∈ Set.Icc a b, lebesgueFunction nodes t ≤ C := by
  constructor
  · intro h t ht
    exact (lebesgueFunction_le_lebesgueOn nodes hab ht).trans h
  · intro h
    obtain ⟨t, ht, hsup, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    rw [hsup]
    exact h t ht

/-- Enlarging a nonempty closed interval can only increase its Lebesgue
supremum.
@isnad1 id=le.3h6v.s5.e17dc168a1fa from=translated src=- shape=cd871541 vocab=2fee5efb
-/
lemma lebesgueOn_mono_Icc {n : ℕ} (nodes : NodeFamily n)
    {a b c d : ℝ} (hab : a ≤ b) (hca : c ≤ a) (hbd : b ≤ d) :
    lebesgueOn nodes a b ≤ lebesgueOn nodes c d := by
  obtain ⟨t, ht, hsup, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [hsup]
  exact lebesgueFunction_le_lebesgueOn nodes (hca.trans (hab.trans hbd))
    ⟨hca.trans ht.1, ht.2.trans hbd⟩

/-- If an interpolation node lies in the interval, the interval supremum is
at least one.
@isnad1 id=le.2h5v.s5.3fee5db10e22 from=translated src=- shape=2f4d3c40 vocab=64a7dc38
-/
lemma one_le_lebesgueOn_of_node_mem {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {a b : ℝ} (hab : a ≤ b) (hk : nodes.point k ∈ Set.Icc a b) :
    1 ≤ lebesgueOn nodes a b := by
  simpa only [lebesgueFunction_at_node] using
    lebesgueFunction_le_lebesgueOn nodes hab hk

/-- On the full source interval, every nonempty node family has Lebesgue
supremum at least one.
@isnad1 id=le.0h3v.s5.b8e5fd07d530 from=translated src=- shape=a24a7aec vocab=98704b02
-/
lemma one_le_lebesgueOn {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    1 ≤ lebesgueOn nodes (-1) 1 :=
  one_le_lebesgueOn_of_node_mem nodes k (by norm_num) (nodes.mem_Icc k)

/-- The finite nodal maximum is nonnegative.
@isnad1 id=le.1h3v.s5.279043825ed7 from=translated src=- shape=7b76429d vocab=41f8faaa
-/
lemma nodalMax_nonneg {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) : 0 ≤ nodalMax nodes p hn := by
  let k : Fin n := ⟨0, hn⟩
  exact (abs_nonneg (p.eval (nodes.point k))).trans
    (abs_eval_node_le_nodalMax nodes p hn k)

/-- The Lagrange inequality with a common nodal bound, uniformly over a
closed interval.
@isnad1 id=le.5h7v.s6.41a758219534 from=translated src=- shape=668289cd vocab=24ff5452
-/
lemma abs_eval_le_mul_lebesgueOn {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (M : ℝ) (hM0 : 0 ≤ M)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (hM : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ M) :
    |p.eval t| ≤ M * lebesgueOn nodes a b := by
  exact (abs_eval_le_mul_lebesgueFunction nodes p hp M t hM).trans
    (mul_le_mul_of_nonneg_left
      (lebesgueFunction_le_lebesgueOn nodes hab ht) hM0)

/-- Conventional maximum-norm interpolation inequality, uniformly over a
closed interval.
@isnad1 id=le.4h6v.s6.bbee2c27a087 from=translated src=- shape=bead4ca7 vocab=8f84a2a3
-/
lemma abs_eval_le_nodalMax_mul_lebesgueOn {n : ℕ}
    (nodes : NodeFamily n) (p : ℝ[X]) (hp : p.degree < n)
    (hn : 0 < n) {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) :
    |p.eval t| ≤ nodalMax nodes p hn * lebesgueOn nodes a b := by
  exact (abs_eval_le_nodalMax_mul_lebesgueFunction nodes p hp hn t).trans
    (mul_le_mul_of_nonneg_left
      (lebesgueFunction_le_lebesgueOn nodes hab ht)
      (nodalMax_nonneg nodes p hn))

end

end Randy1153
