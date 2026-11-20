/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PhaseBridge
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Derivatives of the real sine cardinal functions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- The ordinary product-rule expression, with each differentiated factor singled out.-/
def sineCardinalDerivative (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase j,
    (∏ l ∈ (Finset.univ.erase j).erase k,
      Real.sin ((t - θ l) / 2) / Real.sin ((θ j - θ l) / 2)) *
    (Real.cos ((t - θ k) / 2) / 2 / Real.sin ((θ j - θ k) / 2))

/--
@isnad1 id=hasderiv.0h5v.s7.6085776a069a from=translated src=- shape=5a9e92ef vocab=1693401e
-/
lemma hasDerivAt_sine_ratio (θ : Fin n → ℝ) (j k : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      Real.sin ((s - θ k) / 2) / Real.sin ((θ j - θ k) / 2))
      (Real.cos ((t - θ k) / 2) / 2 / Real.sin ((θ j - θ k) / 2)) t := by
  have hangle : HasDerivAt (fun s : ℝ => (s - θ k) / 2) (1 / 2) t :=
    ((hasDerivAt_id t).sub_const (θ k)).div_const 2
  simpa only [mul_one_div] using
    hangle.sin.div_const (Real.sin ((θ j - θ k) / 2))

/--
@isnad1 id=hasderiv.0h4v.s5.c823d09a111a from=translated src=- shape=16f49eee vocab=92fe2407
-/
lemma hasDerivAt_sineCardinal (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    HasDerivAt (sineCardinal θ j) (sineCardinalDerivative θ j t) t := by
  unfold sineCardinal sineCardinalDerivative
  convert! (HasDerivAt.fun_finsetProd
      (u := Finset.univ.erase j)
      (fun k _ => hasDerivAt_sine_ratio θ j k t)) using 1

/--
@isnad1 id=differen.0h3v.s5.69f27173aa5e from=translated src=- shape=a5160c54 vocab=b9e1f7b2
-/
lemma differentiable_sineCardinal (θ : Fin n → ℝ) (j : Fin n) :
    Differentiable ℝ (sineCardinal θ j) :=
  fun t => (hasDerivAt_sineCardinal θ j t).differentiableAt

/--
@isnad1 id=eq.0h4v.s5.5b191f6416fd from=translated src=- shape=0737cb32 vocab=a100e3d4
-/
lemma deriv_sineCardinal (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    deriv (sineCardinal θ j) t = sineCardinalDerivative θ j t :=
  (hasDerivAt_sineCardinal θ j t).deriv

/--
@isnad1 id=eq.1h4v.s7.8ff25457297a from=translated src=- shape=0833cb04 vocab=5c7b201c
-/
lemma sineCardinalDerivative_at_other (θ : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    sineCardinalDerivative θ j (θ i) =
      (∏ l ∈ (Finset.univ.erase j).erase i,
        Real.sin ((θ i - θ l) / 2) / Real.sin ((θ j - θ l) / 2)) *
      ((1 : ℝ) / 2 / Real.sin ((θ j - θ i) / 2)) := by
  unfold sineCardinalDerivative
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    have himem : i ∈ (Finset.univ.erase j).erase k :=
      Finset.mem_erase.mpr ⟨Ne.symm hki,
        Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩⟩
    have hzero : (∏ l ∈ (Finset.univ.erase j).erase k,
        Real.sin ((θ i - θ l) / 2) / Real.sin ((θ j - θ l) / 2)) = 0 := by
      apply Finset.prod_eq_zero himem
      simp
    rw [hzero, zero_mul]
  · intro hi
    exact (hi (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)).elim

/-- Every off-diagonal cardinal zero is simple for a distinct phase family.
@isnad1 id=ne.2h4v.s6.8e94ce06f8d4 from=translated src=- shape=3b108d86 vocab=705e1bab
-/
lemma deriv_sineCardinal_at_other_ne_zero (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) {i j : Fin n} (hij : i ≠ j) :
    deriv (sineCardinal θ j) (θ i) ≠ 0 := by
  rw [deriv_sineCardinal, sineCardinalDerivative_at_other θ hij]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    have hli := (Finset.mem_erase.mp hl).1
    have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    exact div_ne_zero (sine_denominator_ne_zero θ hθ (Ne.symm hli))
      (sine_denominator_ne_zero θ hθ (Ne.symm hlj))
  · exact div_ne_zero (by norm_num) (sine_denominator_ne_zero θ hθ (Ne.symm hij))

end

end UnitCircleInterpolation
