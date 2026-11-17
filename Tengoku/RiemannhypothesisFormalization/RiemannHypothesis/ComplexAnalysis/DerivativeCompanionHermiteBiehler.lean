/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Linarith
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A derivative-companion Hermite--Biehler sign bridge

This module formalizes one elementary norm inequality associated with the
Hermite--Biehler viewpoint.  It does **not** formalize the classical
Hermite--Biehler theorem, polynomial interlacing, de Branges spaces, or their
converses.

For a complex-valued function `F`, the two derivative companions at `z` are

`F z + I * deriv F z` and `F z - I * deriv F z`.

The strict dominance of the first companion is exactly the strict
anti-Herglotz sign of the logarithmic derivative `F'/F`.  The pointwise
equivalence is valid even when `F z = 0`: totalized division makes `F'/F = 0`,
while the two companion norms are then equal, so both strict propositions are
false.
-/

namespace OverflowResidueRH

open Complex

/-- Pointwise derivative-companion norm dominance.  This is a lightweight
Hermite--Biehler-style inequality, not the full classical theory.-/
def DerivativeCompanionHermiteBiehlerAt (F : ℂ → ℂ) (z : ℂ) : Prop :=
  ‖F z + Complex.I * deriv F z‖ > ‖F z - Complex.I * deriv F z‖

/-- Derivative-companion norm dominance throughout the open upper half-plane.-/
def DerivativeCompanionHermiteBiehlerUHP (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → DerivativeCompanionHermiteBiehlerAt F z

/-- Algebraic core: for arbitrary complex values `a` and `b`, dominance of
`a + I b` over `a - I b` is equivalent to `Im (b/a) < 0`.

The zero-denominator case is included: when `a = 0`, both norms are equal and
Lean's totalized quotient `b / 0` is zero.-/
theorem norm_add_I_mul_gt_norm_sub_I_mul_iff_div_im_neg
    (a b : ℂ) :
    ‖a + Complex.I * b‖ > ‖a - Complex.I * b‖ ↔
      (b / a).im < 0 := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hnormSq : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    have hsquare :
        ‖a - Complex.I * b‖ < ‖a + Complex.I * b‖ ↔
          Complex.normSq (a - Complex.I * b) <
            Complex.normSq (a + Complex.I * b) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).symm
    have hdiv :
        (b / a).im =
          (b.im * a.re - b.re * a.im) / Complex.normSq a := by
      rw [Complex.div_im]
      ring
    have hdivneg :
        (b.im * a.re - b.re * a.im) / Complex.normSq a < 0 ↔
          b.im * a.re - b.re * a.im < 0 := by
      constructor
      · intro h
        exact neg_of_div_neg_left h hnormSq.le
      · intro h
        exact div_neg_of_neg_of_pos h hnormSq
    change ‖a - Complex.I * b‖ < ‖a + Complex.I * b‖ ↔
      (b / a).im < 0
    rw [hsquare, hdiv, hdivneg]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    norm_num
    constructor <;> intro h <;> nlinarith

/-- Pointwise derivative-companion dominance is exactly strict negativity of
the totalized logarithmic derivative.  No nonvanishing or differentiability
hypothesis is needed for this algebraic statement.-/
theorem derivativeCompanionHermiteBiehlerAt_iff_logDerivative_im_neg
    (F : ℂ → ℂ) (z : ℂ) :
    DerivativeCompanionHermiteBiehlerAt F z ↔
      (logDerivativeResponse F z).im < 0 := by
  exact norm_add_I_mul_gt_norm_sub_I_mul_iff_div_im_neg
    (F z) (deriv F z)

/-- A strict derivative-companion inequality forces nonvanishing at that
point.  This records explicitly why the strict global predicate cannot hold
at a zero of `F`.-/
theorem DerivativeCompanionHermiteBiehlerAt.ne_zero
    {F : ℂ → ℂ} {z : ℂ}
    (h : DerivativeCompanionHermiteBiehlerAt F z) :
    F z ≠ 0 := by
  intro hzero
  unfold DerivativeCompanionHermiteBiehlerAt at h
  rw [hzero, zero_add, zero_sub, norm_neg] at h
  exact (lt_irrefl _ h)

/-- **Global derivative-companion bridge.** Upper-half-plane companion norm
dominance is equivalent to strict anti-Herglotz behavior of `F'/F`.-/
theorem derivativeCompanionHermiteBiehlerUHP_iff_strictAntiHerglotz
    (F : ℂ → ℂ) :
    DerivativeCompanionHermiteBiehlerUHP F ↔
      StrictAntiHerglotzUHP (logDerivativeResponse F) := by
  unfold DerivativeCompanionHermiteBiehlerUHP StrictAntiHerglotzUHP
  constructor
  · intro h z hz
    exact (derivativeCompanionHermiteBiehlerAt_iff_logDerivative_im_neg F z).mp
      (h z hz)
  · intro h z hz
    exact (derivativeCompanionHermiteBiehlerAt_iff_logDerivative_im_neg F z).mpr
      (h z hz)

end OverflowResidueRH
