import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLowerBound
import Tengoku.Seed.Analysis.Complex.Liouville

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit primitive L-function growth and derivative bounds

The positive-half-plane truncation estimate bounds the function uniformly
in conductor and height. Cauchy's inequalities then give bounds for every
derivative on disks contained in that half-plane.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

def primitiveLFunctionGrowthBudget (q : ℕ) (δ H : ℝ) : ℝ :=
  1 + (Real.sqrt q * (1 + Real.log q)) * (1 + H / δ)

/--
@isnad1 id=le.3h3v.s6.8da6b37fca06 from=translated src=- shape=7e33eb0d vocab=808901ba
-/
theorem norm_LFunction_le_of_re_pos {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ primitiveLFunctionGrowthBudget q s.re ‖s‖ := by
  have ht := norm_LFunction_sub_characterDirichletPartialSum_le_of_re_pos hq χ hχ 1 (by norm_num) s hs
  simp only [characterDirichletPartialSum_one, Nat.cast_one, Real.one_rpow, mul_one] at ht
  have hn := norm_add_le (DirichletCharacter.LFunction χ s - 1) (1 : ℂ)
  simp only [sub_add_cancel, norm_one] at hn
  unfold primitiveLFunctionGrowthBudget
  linarith

/--
@isnad1 id=le.5h5v.s6.f39319e573dc from=translated src=- shape=492c17f0 vocab=808901ba
-/
theorem norm_LFunction_le_on_re_norm {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (δ H : ℝ) (hδ : 0 < δ) (s : ℂ) (hs : δ ≤ s.re) (hH : ‖s‖ ≤ H) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ primitiveLFunctionGrowthBudget q δ H := by
  apply (norm_LFunction_le_of_re_pos hq χ hχ s (hδ.trans_le hs)).trans
  unfold primitiveLFunctionGrowthBudget
  have hlog := Real.log_natCast_nonneg q
  have hH0 : 0 ≤ H := (norm_nonneg s).trans hH
  gcongr

/--
@isnad1 id=le.4h5v.s6.ba1cebf25648 from=translated src=- shape=e1293c30 vocab=a0f740c0
-/
theorem norm_LFunction_le_on_closedBall {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (R : ℝ) (hR : R < s.re) (z : ℂ) (hz : z ∈ closedBall s R) :
    ‖DirichletCharacter.LFunction χ z‖ ≤
      primitiveLFunctionGrowthBudget q (s.re - R) (‖s‖ + R) := by
  have hdist : ‖z - s‖ ≤ R := mem_closedBall_iff_norm.mp hz
  have hre := (abs_le.mp (Complex.abs_re_le_norm (z - s))).1
  simp only [Complex.sub_re] at hre
  apply norm_LFunction_le_on_re_norm hq χ hχ (s.re - R) (‖s‖ + R) (by linarith) z
  · linarith
  · exact norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)

/--
@isnad1 id=le.4h5v.s7.d325851b1164 from=translated src=- shape=face85f6 vocab=2a389671
-/
theorem norm_iteratedDeriv_LFunction_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (R : ℝ) (hR0 : 0 < R) (hR : R < s.re) (n : ℕ) :
    ‖iteratedDeriv n (DirichletCharacter.LFunction χ) s‖ ≤
      n.factorial * primitiveLFunctionGrowthBudget q (s.re - R) (‖s‖ + R) / R ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0
    (DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)).diffContOnCl
  intro z hz
  exact norm_LFunction_le_on_closedBall hq χ hχ s R hR z (sphere_subset_closedBall hz)

/--
@isnad1 id=le.4h4v.s7.9dc3b4ebb038 from=translated src=- shape=15b1bb1e vocab=7f215ffc
-/
theorem norm_deriv_LFunction_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (R : ℝ) (hR0 : 0 < R) (hR : R < s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤
      primitiveLFunctionGrowthBudget q (s.re - R) (‖s‖ + R) / R := by
  simpa using norm_iteratedDeriv_LFunction_le hq χ hχ s R hR0 hR 1

end TwinPrime.Analytic
