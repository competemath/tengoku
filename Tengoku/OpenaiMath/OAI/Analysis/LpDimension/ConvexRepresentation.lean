import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.Model

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
universe uE uI uΩ

namespace SubpolynomialLp

lemma independent_of_affine_sum {E : Type uE} {I : Type uI} [Fintype E] (z : I → E → ℝ)
    (hz : AffineIndependent ℝ z) (hs : ∀ i, ∑ e, z i e = 1) :
    LinearIndependent ℝ z := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hsum := congrArg (fun v : E → ℝ => ∑ e, v e) hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.sum_const_zero] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, hs, mul_one] at hsum
  exact hz.eq_zero_of_sum_eq_zero hsum hw i hi

lemma hyperplane_convex_representation {E : Type uE} [Fintype E] {K : Set (E → ℝ)}
    (hK : ∀ z ∈ K, ∑ e, z e = 1) {v : E → ℝ} (hv : v ∈ convexHull ℝ K) :
    ∃ k ≤ Fintype.card E, ∃ (z : Fin k → E → ℝ) (w : Fin k → ℝ),
      (∀ i, z i ∈ K) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = v := by
  classical
  obtain ⟨I, hI, z, w, hz, hi, hw, hws, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let e := (Fintype.equivFin I).symm
  have hlin := independent_of_affine_sum z hi (fun i => hK _ (hz ⟨i,rfl⟩))
  have hc : Fintype.card I ≤ Fintype.card E := by
    simpa using hlin.fintype_card_le_finrank
  refine ⟨Fintype.card I, hc, z ∘ e, w ∘ e, ?_, ?_, ?_, ?_⟩
  · intro i; exact hz ⟨e i, rfl⟩
  · intro i; exact (hw (e i)).le
  · exact (e.sum_comp w).trans hws
  · exact (e.sum_comp (fun i => w i • z i)).trans hsum

end SubpolynomialLp

end

end OAI
