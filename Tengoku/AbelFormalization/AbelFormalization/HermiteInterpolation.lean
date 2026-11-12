import Tengoku.AbelFormalization.AbelFormalization.HermiteContour
import Tengoku.AbelFormalization.AbelFormalization.AnalyticMultiplicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Contour Hermite interpolation, including coincident nodes

The exact contour remainder supplies all interpolation jets.  When nodes
coincide their multiplicities add; no distinctness hypothesis is imposed.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=le.0h4v.s4.1be97a1c780d from=translated src=- shape=dd14d4c3 vocab=2df37d9f
-/
theorem multiplicity_le_nodeMultiplicity (δ : ι → ℂ) (m : ι → ℕ) (i : ι) :
    m i ≤ nodeMultiplicity δ m (δ i) := by
  classical
  exact Finset.single_le_sum_of_canonicallyOrdered
    (show i ∈ Finset.univ.filter (fun j => δ j = δ i) by simp)

/--
@isnad1 id=iff.0h4v.s5.c31541fc4f3a from=translated src=- shape=25c3bf1f vocab=7449dc1c
-/
theorem nodeMultiplicity_pos_iff (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) :
    0 < nodeMultiplicity δ m ξ ↔ ∃ i, δ i = ξ ∧ 0 < m i := by
  classical
  simp only [nodeMultiplicity, Finset.sum_pos_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- A node polynomial has no boundary zero if every node is in the disk.
@isnad1 id=ne.2h5v.s6.75e372d7a9e0 from=translated src=- shape=836d4f1d vocab=fea6060e
-/
theorem nodePolynomial_eval_ne_zero_on_sphere (δ : ι → ℂ) (m : ι → ℕ) {R : ℝ}
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) R) :
    (nodePolynomial δ m).eval ζ ≠ 0 := by
  rw [nodePolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro he
  have hs : δ i ∈ sphere (0 : ℂ) R := he ▸ hζ
  exact (ne_of_lt (mem_ball.mp (hδ i))) (mem_sphere.mp hs)

/-- The explicit contour polynomial has the required interpolation degree.
@isnad1 id=lt.0h5v.s5.0cc66885dab0 from=translated src=- shape=0b4ae7a6 vocab=2fb6a6cb
-/
theorem hermiteContour_node_degree_lt (f : ℂ → ℂ) (δ : ι → ℂ) (m : ι → ℕ) (R : ℝ) :
    (hermiteContourPolynomial f (nodePolynomial δ m) R).degree <
      (totalMultiplicity m : WithBot ℕ) := by
  simpa only [nodePolynomial_natDegree] using
    hermiteContourPolynomial_degree_lt f (nodePolynomial δ m) R

end AbelFormalization
