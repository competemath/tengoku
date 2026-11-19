/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerDensity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeSlices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Slicing a corner through its parent pair

Fix the first line's position at `c`, the last intercept, and the corner code.
The remaining common-position integral is controlled by the parent pair's
double-projection density.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Common-position mass with first-line position, last intercept, and corner code fixed.-/
noncomputable def cornerParentSliceMass (a b c κ : ℝ) (D : Set (CornerCoordinates m))
    (z y x : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ w, D.indicator 1
    (cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z)

/--
@isnad1 id=eq.1h9v.s8.89ea51f9a8eb from=translated src=- shape=95a1a9e6 vocab=7f01d2b9
-/
theorem cornerParent_cornerFromCode_positions {a c : ℝ} (hca : c ≠ a) (b κ : ℝ)
    (w y x z : EuclideanSpace ℝ (Fin m)) :
    cornerParent a (cornerFromCode a b c κ (lineAt a w ((c - a)⁻¹ • (y - w))) x z) =
      pairFromData a b c (w, (x + b • ((a - b)⁻¹ • (z - κ • y)), y)) := by
  dsimp only [cornerParent, cornerFromCode]
  rw [atHeight_lineAt_of_positions hca.symm]
  simp [atHeight, pairFromData, lineAt]

/--
@isnad1 id=eq.2h7v.s9.871e24035b04 from=translated src=- shape=0b0ffa02 vocab=da056bbb
-/
theorem cornerDensity_eq_parentSlices {a c : ℝ} (hca : c ≠ a) (b κ : ℝ)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z = codeJacobian m a b *
      ∫⁻ y, ∫⁻ x, pairJacobian m a b c * cornerParentSliceMass a b c κ D z y x := by
  let f : Line m → ℝ≥0∞ := fun p ↦
    cornerFirstDensity a b c κ D z (lineAt a p.1 ((c - a)⁻¹ • (p.2 - p.1)))
  have hf : Measurable f := (measurable_cornerFirstDensity a b c κ hD z).comp
    (by unfold lineAt; fun_prop)
  have hi : (∫⁻ g, cornerFirstDensity a b c κ D z g) =
      codeJacobian m a c * ∫⁻ p, f p := by
    calc
      _ = ∫⁻ g, f (twoSlice a c g) := by
        apply lintegral_congr
        intro g
        dsimp only [f, twoSlice_apply]
        rw [lineAt_twoSlice hca]
      _ = ∫⁻ p, f p ∂(codeJacobian m a c • volume) :=
        (measurePreserving_twoSlice hca.symm).lintegral_comp hf
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
  have hswap (y : EuclideanSpace ℝ (Fin m)) : (∫⁻ w, f (w, y)) =
      ∫⁻ x, cornerParentSliceMass a b c κ D z y x := by
    have hm : Measurable (fun p : Line m ↦ D.indicator (1 : CornerCoordinates m → ℝ≥0∞)
        (cornerFromCode a b c κ (lineAt a p.1 ((c - a)⁻¹ • (y - p.1))) p.2 z)) :=
      (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
    exact lintegral_lintegral_swap hm.aemeasurable
  rw [cornerDensity_eq_lintegral a b c κ hD, hi]
  have hp : pairJacobian m a b c ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ hp]
  rw [show (∫⁻ p, f p) = ∫⁻ y, ∫⁻ w, f (w, y) by
    simpa only [Measure.volume_eq_prod] using lintegral_prod_symm' f hf]
  simp_rw [hswap]
  simp only [pairJacobian, codeJacobian, pow_two, mul_assoc]

end NKBesicovitch.Projection
