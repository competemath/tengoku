import Tengoku.Seed.NumberTheory.ModularForms.QExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

variable {h : ℝ} {F : ℍ → ℂ} {c : ℕ → ℂ}

/--
@isnad1 id=lt.1h2v.s4.66e1842663ee from=translated src=- shape=4f8cc68a vocab=6bddaf06
-/
lemma norm_qParam_lt_one_of_pos (hh : 0 < h) (τ : ℍ) : ‖𝕢 h (τ : ℂ)‖ < 1 := by
  rw [Periodic.norm_qParam, Real.exp_lt_one_iff, neg_mul, coe_im, neg_mul, neg_div, neg_lt_zero]
  exact div_pos (by positivity [τ.im_pos]) hh

/--
@isnad1 id=hassum.4h4v.s7.90b7e2ce5768 from=translated src=- shape=d171886d vocab=fa8ece86
-/
lemma hasSum_cuspFunction_punctured (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m : ℕ => c m * q ^ m) (cuspFunction h F q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_nonzero h (F ∘ ofComplex) hq1
  have h3 : cuspFunction h F q = F τ := by
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos h1] at h2
    exact h2
  have h4 : 𝕢 h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hF τ

/--
@isnad1 id=hasfpowe.2h3v.s7.6136bf69597d from=translated src=- shape=5ab8b080 vocab=5554f41f
-/
lemma hasFPowerSeriesOnBall_update (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_mul, mul_comm] using
        (hasSum_cuspFunction_punctured hh hF (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm] using hasSum_cuspFunction_punctured hh hF hy hy'

def discFun (h : ℝ) (F : ℍ → ℂ) (c : ℕ → ℂ) : ℂ → ℂ := update (cuspFunction h F) 0 (c 0)

/--
@isnad1 id=hassum.3h4v.s7.e78bdf6d1a27 from=translated src=- shape=df0900a8 vocab=c77ab699
-/
lemma hasSum_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun m : ℕ => c m * q ^ m) (discFun h F c q) := by
  have hy : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe]; simpa using hq
  have h := (hasFPowerSeriesOnBall_update hh hF).hasSum hy
  rw [zero_add] at h
  simpa [discFun, mul_comm] using h

/--
@isnad1 id=eq.2h4v.s6.66bcd57ecf14 from=translated src=- shape=7ddb5566 vocab=f6ec553d
-/
lemma apply_eq_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (τ : ℍ) : F τ = discFun h F c (𝕢 h (τ : ℂ)) :=
  (hF τ).unique (hasSum_discFun hh hF (norm_qParam_lt_one_of_pos hh τ))

/--
@isnad1 id=differen.2h3v.s7.dd5f41f8926f from=translated src=- shape=1d000111 vocab=210626b7
-/
lemma differentiableOn_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    DifferentiableOn ℂ (discFun h F c) (Metric.ball 0 1) := by
  have h1 := (hasFPowerSeriesOnBall_update hh hF).differentiableOn
  rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h1

/--
@isnad1 id=continuo.3h4v.s6.5edb1dafa900 from=translated src=- shape=379b69a1 vocab=8ae5ec38
-/
lemma continuousAt_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    ContinuousAt (discFun h F c) q :=
  ((differentiableOn_discFun hh hF).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

/--
@isnad1 id=eq.0h3v.s4.ec919bbc012a from=translated src=- shape=1e3f4c5f vocab=f5988985
-/
lemma discFun_zero : discFun h F c 0 = c 0 := by simp [discFun]

/--
@isnad1 id=tendsto.2h3v.s6.3f31f7bef95d from=translated src=- shape=30bdf4ce vocab=8fb7c62d
-/
theorem tendsto_atImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    Tendsto F atImInfty (𝓝 (c 0)) := by
  have h1 : Tendsto (fun τ : ℍ => discFun h F c (𝕢 h (τ : ℂ))) atImInfty (𝓝 (discFun h F c 0)) :=
    (continuousAt_discFun hh hF (q := 0) (by simp)).tendsto.comp (qParam_tendsto_atImInfty hh)
  rw [discFun_zero] at h1
  exact h1.congr fun τ => (apply_eq_discFun hh hF τ).symm

end Realized

end ModularCurve

/--
@isnad1 id=tendsto.2h3v.s6.7fc1b7a52a0a from=translated src=- shape=e87e1540 vocab=8fb7c62d
-/
theorem solution (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (c 0)) :=
  ModularCurve.Realized.tendsto_atImInfty hh hc

end
