/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Hedberg

/-!
# The order-one Hardy--Littlewood--Sobolev estimate in dimension three

The exponent used by the pressure decomposition is `m = 5/2`, `s = 15`.
The proof is Hedberg's pointwise estimate followed by the strong maximal
estimate.  The a.e. maximal-data hypothesis is exposed so that zero data and
finite truncations can be handled by the consuming pressure lemma.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The constant in the three-dimensional order-one HLS estimate. -/
def hlsRieszConstant : ℝ≥0∞ :=
  (hedbergNearConstant + hedbergFarConstant) *
    (maximalStrongConstant (5 / 2 : ℝ)) ^ (1 / 15 : ℝ)

/--
@isnad1 id=ne.2h2v.s7.8072b99bc152 from=translated src=- shape=0a137cbb vocab=12dcc2db
-/
theorem maximalMajorant_ne_zero_of_integral_ne_zero
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hI0 : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ≠ 0) (z : Vec3) :
    maximalMajorant f z ≠ 0 := by
  intro hz
  have hM := isMaximalMajorant_maximalMajorant f
  have hball : ∀ n : ℕ,
      (∫⁻ w in Metric.ball z ((n : ℝ) + 1), ENNReal.ofReal |f w|) = 0 := by
    intro n
    have h := hM z ((n : ℝ) + 1) (by positivity)
    rw [hz, zero_mul] at h
    exact bot_unique h
  have hunion : (⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1)) = Set.univ := by
    ext w
    simp only [mem_iUnion, mem_ball, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (dist z w)
    refine ⟨n, ?_⟩
    rw [dist_comm]
    linarith only [hn]
  have hglobal : (∫⁻ w, ENNReal.ofReal |f w|) = 0 := by
    have hglobal' : (∫⁻ w in ⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1),
        ENNReal.ofReal |f w|) = 0 := by
      apply le_antisymm
      · calc
          (∫⁻ w in ⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1),
              ENNReal.ofReal |f w|) ≤
              ∑' n : ℕ, ∫⁻ w in Metric.ball z ((n : ℝ) + 1),
                ENNReal.ofReal |f w| := lintegral_iUnion_le _ _
          _ = 0 := by simp [hball]
      · exact bot_le
    simpa [hunion] using hglobal'
  have hfzero : (fun w : Vec3 => ENNReal.ofReal |f w|) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff'
      (by simpa only [Real.norm_eq_abs] using
        (hf.norm.ennreal_ofReal).aemeasurable)).mp hglobal
  have hIzero : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hfzero] with w hw
    simp [hw]
  exact hI0 hIzero

end CKN.Foundation.Euclidean
