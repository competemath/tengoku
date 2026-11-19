/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeDensity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PairDensity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.TwoSlice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The pointwise pair-code marginal identity

At dual heights the second position is forced by the first position and the
code. The explicit coordinate integrals identify the two densities pointwise.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=eq.1h4v.s7.3dea3d888262 from=translated src=- shape=ff3a0cdb vocab=6090e29d
-/
theorem lineAt_twoSlice {a t : ℝ} (hta : t ≠ a) (g : Line m) :
    lineAt a (atHeight a g) ((t - a)⁻¹ • (atHeight t g - atHeight a g)) = g := by
  have h : atHeight t g - atHeight a g = (t - a) • g.2 := by
    unfold atHeight
    module
  rw [h, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hta), one_smul, lineAt_atHeight]

/--
@isnad1 id=eq.4h8v.s8.a464fa0b5ec4 from=translated src=- shape=0b0a8c44 vocab=911672b1
-/
theorem pairCode_pairFromData_dual {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) (w y z : EuclideanSpace ℝ (Fin m)) :
    pairCode a b c (pairFromData a t (dualTime a b c t)
      (w, (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
        (z - (c * (b - a) / (t - a)) • y)))) = z := by
  have hd := dualTime_ne_base hab hc hta htb
  have hB : (b - a) / (dualTime a b c t - a) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hd)
  have hp := pairProjections_pairFromData hta hd
    (w, (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
      (z - (c * (b - a) / (t - a)) • y)))
  rw [pairProjections_eq] at hp
  have hy := congrArg Prod.fst hp
  have hz := congrArg Prod.snd hp
  dsimp only at hy hz
  rw [pairCode_eq_dual_projections hab hc hta htb,
    hy, hz, smul_smul, mul_inv_cancel₀ hB, one_smul]
  module

/--
@isnad1 id=eq.4h8v.s8.6c916550f73a from=translated src=- shape=d95e4604 vocab=432d8d1c
-/
theorem pairFromData_dual_eq_pairFromCode {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) (w y z : EuclideanSpace ℝ (Fin m)) :
    pairFromData a t (dualTime a b c t)
      (w, (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
        (z - (c * (b - a) / (t - a)) • y))) =
      pairFromCode a b c (lineAt a w ((t - a)⁻¹ • (y - w))) z := by
  have h := pairFromCode_pairCode hab c
    (pairFromData a t (dualTime a b c t)
      (w, (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
        (z - (c * (b - a) / (t - a)) • y))))
  rw [pairCode_pairFromData_dual hab hc hta htb] at h
  exact h.symm

/--
@isnad1 id=eq.4h7v.s8.e337f2a49db8 from=translated src=- shape=0d0a0bf1 vocab=dd84ea60
-/
theorem pairProjections_pairFromCode_dual {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) (g : Line m) (z : EuclideanSpace ℝ (Fin m)) :
    pairProjections a t (dualTime a b c t) (pairFromCode a b c g z) =
      (atHeight t g, ((b - a) / (dualTime a b c t - a))⁻¹ •
        (z - (c * (b - a) / (t - a)) • atHeight t g)) := by
  have hp := pairFromData_dual_eq_pairFromCode hab hc hta htb
    (atHeight a g) (atHeight t g) z
  rw [lineAt_twoSlice hta] at hp
  rw [← hp, pairProjections_pairFromData hta (dualTime_ne_base hab hc hta htb)]

/--
@isnad1 id=eq.4h5v.s7.06edc7d1f951 from=translated src=- shape=8d37281d vocab=e4924207
-/
theorem codeJacobian_dual {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) :
    ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹| *
      ENNReal.ofReal |((dualTime a b c t - a) ^ m)⁻¹| = codeJacobian m a b := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, ← mul_inv, ← mul_pow,
    div_mul_cancel₀ _ (sub_ne_zero.mpr (dualTime_ne_base hab hc hta htb))]
  rfl

/--
@isnad1 id=eq.2h7v.s9.1e68f9c35f7f from=translated src=- shape=8ba538dd vocab=c5a95f87
-/
theorem codeDensity_eq_twoSlice_lintegral {a b t : ℝ} (hta : t ≠ a)
    (c : ℝ) {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c W z =
      (codeJacobian m a b * ENNReal.ofReal |((t - a) ^ m)⁻¹|) *
        ∫⁻ y, ∫⁻ w, W.indicator 1
          (pairFromCode a b c (lineAt a w ((t - a)⁻¹ • (y - w))) z) := by
  let f : Line m → ℝ≥0∞ := fun p ↦ W.indicator 1
    (pairFromCode a b c (lineAt a p.1 ((t - a)⁻¹ • (p.2 - p.1))) z)
  have hF : Continuous (fun p : Line m ↦
      pairFromCode a b c (lineAt a p.1 ((t - a)⁻¹ • (p.2 - p.1))) z) := by
    unfold pairFromCode lineAt atHeight
    fun_prop
  have hf : Measurable f := (measurable_const.indicator hW).comp hF.measurable
  have hi : (∫⁻ g, W.indicator 1 (pairFromCode a b c g z)) =
      ENNReal.ofReal |((t - a) ^ m)⁻¹| * ∫⁻ p, f p := by
    calc
      _ = ∫⁻ g, f (twoSlice a t g) := by
        apply lintegral_congr
        intro g
        dsimp only [f, twoSlice_apply]
        rw [lineAt_twoSlice hta]
      _ = ∫⁻ p, f p ∂(ENNReal.ofReal |((t - a) ^ m)⁻¹| • volume) :=
        (measurePreserving_twoSlice hta.symm).lintegral_comp hf
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
  rw [codeDensity_eq_lintegral a b c hW, hi, ← mul_assoc]
  congr 1
  simpa only [Measure.volume_eq_prod] using
    (lintegral_prod_symm' (μ := (volume : Measure (EuclideanSpace ℝ (Fin m)))) (ν := volume) f hf)

/-- The exact marginal formula for the explicit density representatives, at every code value.
@isnad1 id=eq.5h7v.s9.dfc93df2fce2 from=translated src=- shape=97f9f53b vocab=fac909e2
-/
theorem codeDensity_eq_marginal {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) {W : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c W z =
      ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹| *
        ∫⁻ y, pairDensity a t (dualTime a b c t) W
          (y, ((b - a) / (dualTime a b c t - a))⁻¹ •
            (z - (c * (b - a) / (t - a)) • y)) := by
  rw [codeDensity_eq_twoSlice_lintegral hta c hW]
  simp_rw [pairDensity, pairFromData_dual_eq_pairFromCode hab hc hta htb]
  have hq : pairJacobian m a t (dualTime a b c t) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hq, ← mul_assoc]
  congr 1
  rw [pairJacobian, mul_left_comm, codeJacobian_dual hab hc hta htb]
  exact mul_comm _ _

end NKBesicovitch.Projection
