import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.GeneralLowerAsymptotic
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.GeneralUpperAsymptotic
import Tengoku.Seed.Analysis.Asymptotics.Theta
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Baseline fixed-dimensional asymptotic order

This packages (A2) and (B2) as the `Θ_k` conclusion in part (C).
-/

open Asymptotics Filter

namespace BurningPath

/-- The standard fixed-`k` scale `n^(k/(k+1))`.-/
noncomputable def pathTokenStandardScale (k n : ℕ) : ℝ :=
  (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ))

/--
@isnad1 id=le.0h2v.s4.f92dcd689c42 from=translated src=- shape=5ffe46ab vocab=b15e01e4
-/
theorem pathTokenStandardScale_nonneg (k n : ℕ) :
    0 ≤ pathTokenStandardScale k n := by
  unfold pathTokenStandardScale
  positivity

/--
@isnad1 id=lt.1h2v.s4.9c7cd499188b from=translated src=- shape=cee548f2 vocab=bd6aa9fd
-/
theorem pathTokenStandardScale_pos {k n : ℕ} (hn : 0 < n) :
    0 < pathTokenStandardScale k n := by
  unfold pathTokenStandardScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

/-- The constructive upper estimate gives the `O` half of part (C).
@isnad1 id=isbigo.1h1v.s4.38f93d8398a6 from=translated src=- shape=45b0721c vocab=a0bf3575
-/
theorem pathTokenBurning_isBigO_standardScale (k : ℕ) (hk : 2 ≤ k) :
    (fun n ↦ (pathTokenBurningNumberTotal k n : ℝ)) =O[atTop]
      pathTokenStandardScale k := by
  let C := generalUpperConstant k + 1
  have hupper :=
    eventually_pathTokenBurningRatio_le_generalUpperConstant_add
      k (by omega) (show (0 : ℝ) < 1 by norm_num)
  refine IsBigO.of_bound C ?_
  filter_upwards [hupper, eventually_gt_atTop 0] with n hn hnpos
  have hscale : 0 < pathTokenStandardScale k n :=
    pathTokenStandardScale_pos hnpos
  have hn' :
      (pathTokenBurningNumberTotal k n : ℝ) /
          pathTokenStandardScale k n ≤ C := by
    simpa [C, pathTokenBurningRatio, pathTokenAsymptoticScale_eq_rpow,
      pathTokenStandardScale] using hn
  have hmul :
      (pathTokenBurningNumberTotal k n : ℝ) ≤
        C * pathTokenStandardScale k n := by
    exact (div_le_iff₀ hscale).mp hn'
  simpa [Real.norm_eq_abs, abs_of_nonneg,
    pathTokenStandardScale_nonneg] using hmul

/-- The volume lower estimate gives the reverse `O` half of part (C).
@isnad1 id=isbigo.1h1v.s4.cb3ee58128e6 from=translated src=- shape=2fc77fa1 vocab=a0bf3575
-/
theorem standardScale_isBigO_pathTokenBurning (k : ℕ) (hk : 2 ≤ k) :
    pathTokenStandardScale k =O[atTop]
      (fun n ↦ (pathTokenBurningNumberTotal k n : ℝ)) := by
  let c := volumeLowerConstant k / 2
  have hc : 0 < c := by
    dsimp [c]
    exact half_pos (volumeLowerConstant_pos k)
  have hlower :=
    eventually_generalLowerAsymptotic k hk
      (show 0 < volumeLowerConstant k / 2 by exact hc)
  refine IsBigO.of_bound c⁻¹ ?_
  filter_upwards [hlower, eventually_gt_atTop 0] with n hn hnpos
  have hscaleNonneg := pathTokenStandardScale_nonneg k n
  have hburnNonneg :
      0 ≤ (pathTokenBurningNumberTotal k n : ℝ) := by positivity
  have hlower' :
      c * pathTokenStandardScale k n ≤
        (pathTokenBurningNumberTotal k n : ℝ) := by
    have hn' := hn
    change
      (volumeLowerConstant k - volumeLowerConstant k / 2) *
          pathTokenStandardScale k n ≤
        (pathTokenBurningNumberTotal k n : ℝ) at hn'
    have heq :
        volumeLowerConstant k - volumeLowerConstant k / 2 = c := by
      dsimp [c]
      ring
    rwa [heq] at hn'
  have hdiv :
      pathTokenStandardScale k n ≤
        (pathTokenBurningNumberTotal k n : ℝ) / c := by
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hlower')
  have hbound :
      pathTokenStandardScale k n ≤
        c⁻¹ * (pathTokenBurningNumberTotal k n : ℝ) := by
    simpa [div_eq_inv_mul] using hdiv
  simpa [Real.norm_eq_abs, abs_of_nonneg hscaleNonneg,
    abs_of_nonneg hburnNonneg] using hbound

/-- Part (C): `b(F_k(P_n)) = Θ_k(n^(k/(k+1)))`.
@isnad1 id=istheta.1h1v.s4.38e7a8dbf7f7 from=translated src=- shape=45b0721c vocab=62509c4f
-/
theorem pathTokenBurning_isTheta_standardScale (k : ℕ) (hk : 2 ≤ k) :
    (fun n ↦ (pathTokenBurningNumberTotal k n : ℝ)) =Θ[atTop]
      pathTokenStandardScale k :=
  ⟨pathTokenBurning_isBigO_standardScale k hk,
    standardScale_isBigO_pathTokenBurning k hk⟩

/--
Once the constructive upper bound supplies real boundedness, the general
lower estimate also has the usual real-valued liminf formulation.
@isnad1 id=le.1h1v.s4.9352b1ae7bd7 from=translated src=- shape=12e37351 vocab=d66ce403
-/
theorem generalLowerAsymptotic_real_liminf (k : ℕ) (hk : 2 ≤ k) :
    volumeLowerConstant k ≤ liminf (pathTokenBurningRatio k) atTop := by
  have hupper :
      ∀ᶠ n in atTop,
        pathTokenBurningRatio k n ≤ generalUpperConstant k + 1 :=
    eventually_pathTokenBurningRatio_le_generalUpperConstant_add
      k (by omega) (by norm_num)
  have hcob :
      atTop.IsCoboundedUnder (· ≥ ·) (pathTokenBurningRatio k) :=
    isCoboundedUnder_ge_of_eventually_le atTop hupper
  have hbdd :
      atTop.IsBoundedUnder (· ≥ ·) (pathTokenBurningRatio k) :=
    by
      change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, pathTokenBurningRatio k n ≥ b
      exact ⟨0, Eventually.of_forall (pathTokenBurningRatio_nonneg k)⟩
  apply (le_liminf_iff' hcob hbdd).2
  intro c hc
  exact eventually_constant_le_pathTokenBurningRatio k (by omega) hc

/-- Real liminf form of the exact two-token lower bound.
@isnad1 id=le.0h0v.s6.9ea2f943c5a8 from=translated src=- shape=f785669c vocab=786772e5
-/
theorem twoTokenLowerAsymptotic_liminf :
    ((3 / 4 : ℝ) ^ (3 : ℝ)⁻¹) ≤
      liminf
        (fun n : ℕ ↦
          (pathTokenBurningNumberTotal 2 n : ℝ) /
            (n : ℝ) ^ (2 / 3 : ℝ))
        atTop := by
  have h := generalLowerAsymptotic_real_liminf 2 (by omega)
  norm_num [volumeLowerConstant, volumeLowerPowerConstant] at h
  have hfun :
      pathTokenBurningRatio 2 =
        fun n : ℕ ↦
          (pathTokenBurningNumberTotal 2 n : ℝ) /
            (n : ℝ) ^ (2 / 3 : ℝ) := by
    funext n
    rw [pathTokenBurningRatio, pathTokenAsymptoticScale_eq_rpow]
    norm_num
  rw [hfun] at h
  convert h using 1
  norm_num [one_div]

end BurningPath
