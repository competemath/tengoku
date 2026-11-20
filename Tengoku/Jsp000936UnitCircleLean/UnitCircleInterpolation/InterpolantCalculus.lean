/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CayleyCardinal
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.SineDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Global calculus and full-turn signs of the actual sine interpolants -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

def sineInterpolantDerivative (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * sineCardinalDerivative θ j t

/--
@isnad1 id=hasderiv.0h4v.s5.b1b74f6af2af from=translated src=- shape=fbba1116 vocab=ad7b43f8
-/
lemma hasDerivAt_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (sineInterpolant θ c) (sineInterpolantDerivative θ c t) t := by
  unfold sineInterpolant sineInterpolantDerivative
  convert! HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hasDerivAt_sineCardinal θ j t).const_mul (c j)) using 1

/--
@isnad1 id=differen.0h3v.s6.25cc626e0d7d from=translated src=- shape=76cfec7a vocab=42d9450b
-/
lemma differentiable_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Differentiable ℝ (sineInterpolant θ c) :=
  fun t => (hasDerivAt_sineInterpolant θ c t).differentiableAt

/--
@isnad1 id=eq.0h4v.s5.ce9940031530 from=translated src=- shape=f7ea7d62 vocab=9b5270ce
-/
lemma deriv_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    deriv (sineInterpolant θ c) t = sineInterpolantDerivative θ c t :=
  (hasDerivAt_sineInterpolant θ c t).deriv

/--
@isnad1 id=continuo.0h3v.s4.5781c43210d5 from=translated src=- shape=908bf8aa vocab=08fe2199
-/
lemma continuous_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Continuous (sineInterpolant θ c) :=
  (differentiable_sineInterpolant θ c).continuous

/--
@isnad1 id=continuo.0h3v.s4.dbe34b48b5df from=translated src=- shape=93394161 vocab=41166213
-/
lemma continuous_sineCardinalDerivative (θ : Fin n → ℝ) (j : Fin n) :
    Continuous (sineCardinalDerivative θ j) := by
  unfold sineCardinalDerivative
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul
  · apply continuous_finsetProd
    intro l hl
    exact (Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).div_const 2)).div_const _
  · exact ((Real.continuous_cos.comp
      ((continuous_id.sub continuous_const).div_const 2)).div_const 2).div_const _

/--
@isnad1 id=continuo.0h3v.s4.c4f230270e93 from=translated src=- shape=908bf8aa vocab=4f0dfc6e
-/
lemma continuous_sineInterpolantDerivative (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Continuous (sineInterpolantDerivative θ c) := by
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_sineCardinalDerivative θ j)

/--
@isnad1 id=eq.0h4v.s6.8072cb68c8ba from=translated src=- shape=2a74bfab vocab=a0846f99
-/
lemma sineInterpolant_add_two_pi (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolant θ c (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineInterpolant θ c t := by
  unfold sineInterpolant
  simp_rw [sineCardinal_add_two_pi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
@isnad1 id=eq.0h4v.s6.a2231f8439f4 from=translated src=- shape=2a74bfab vocab=c35d45bb
-/
lemma sineInterpolantDerivative_add_two_pi (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolantDerivative θ c (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineInterpolantDerivative θ c t := by
  have hl := (hasDerivAt_sineInterpolant θ c (t + 2 * Real.pi)).comp t
    ((hasDerivAt_id t).add_const (2 * Real.pi))
  have hr := (hasDerivAt_sineInterpolant θ c t).const_mul ((-1 : ℝ) ^ (n - 1))
  have heq : (fun u => sineInterpolant θ c (u + 2 * Real.pi)) =
      (fun u => (-1 : ℝ) ^ (n - 1) * sineInterpolant θ c u) :=
    funext (sineInterpolant_add_two_pi θ c)
  simp only [Function.comp_def, id_eq, mul_one] at hl
  rw [heq] at hl
  exact hl.unique hr

/--
@isnad1 id=iff.0h4v.s6.cb53b7d51144 from=translated src=- shape=af1415d8 vocab=dd79333d
-/
lemma sineInterpolant_add_two_pi_eq_zero_iff (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolant θ c (t + 2 * Real.pi) = 0 ↔ sineInterpolant θ c t = 0 := by
  rw [sineInterpolant_add_two_pi, mul_eq_zero]
  simp only [pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0), false_or]

/--
@isnad1 id=iff.0h4v.s6.5946bb9004a4 from=translated src=- shape=af1415d8 vocab=e121b31d
-/
lemma sineInterpolantDerivative_add_two_pi_eq_zero_iff
    (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolantDerivative θ c (t + 2 * Real.pi) = 0 ↔
      sineInterpolantDerivative θ c t = 0 := by
  rw [sineInterpolantDerivative_add_two_pi, mul_eq_zero]
  simp only [pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0), false_or]

end

end UnitCircleInterpolation
