/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Fuchsian.Covolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Ford-type covering criterion for finite covolume

`OrbicurveCores.Fuchsian.hasFiniteCovolume_of_cover`: if `Γ ≤ SL(2, ℝ)` contains a translation
`z ↦ z + w` (`w > 0`) and finitely many elements `gᵢ` whose open isometric discs
`{|cᵢ z + dᵢ| < 1}` cover a period `[a, a + w]` of the real axis, then `Γ` has finite covolume.

Proof: shrink the discs slightly (compactness of `[a, a + w]`), which gives `ρ < 1` and `η > 0`
such that every point of the strip below height `η` lies in some `{|cᵢ z + dᵢ| < ρ}`. The
reduction "translate into the strip; if below height `η`, apply `gᵢ`" multiplies the imaginary
part by at least `ρ⁻²` at each step, so it ends in the strip above height `η`, which has finite
area `w / η`. Discreteness of `Γ` is not needed.
-/

open MeasureTheory Matrix UpperHalfPlane Set Topology Filter
open scoped MatrixGroups ENNReal NNReal

namespace OrbicurveCores.Fuchsian

/-- The strip `a ≤ Re z ≤ b`, `Im z ≥ η > 0`, has finite hyperbolic area. -/
lemma volume_strip_lt_top (a b η : ℝ) (hη : 0 < η) :
    volume {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} < ∞ := by
  rw [volume_eq_lintegral]
  set f : ℂ → ℝ≥0∞ := fun z ↦ (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)
  set T : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Ici η)
  have hsub : ((↑) '' {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} : Set ℂ) ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [T, Complex.measurableEquivRealProd] using hz
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' T = Icc a b ×ˢ Ici η := by
    ext p; simp [T]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hg : Measurable fun y : ℝ ↦ (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by fun_prop
  have hfeq : ∀ p : ℝ × ℝ, (Complex.measurableEquivRealProd.symm p).im = p.2 := by
    intro p; simp [Complex.measurableEquivRealProd]
  simp_rw [hfeq]
  rw [lintegral_prod (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
    (hg.comp measurable_snd).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  have hint := (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hη).2
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  refine lt_of_le_of_lt (le_of_eq ?_) hint
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := lt_trans hη hy
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _), ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.rpow_neg hy0.le, Real.rpow_two, Real.norm_of_nonneg hy0.le]
  ring

end OrbicurveCores.Fuchsian
