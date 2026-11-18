import Tengoku.Seed.NumberTheory.ModularForms.NormTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant

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
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
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
@isnad1 id=hassum.3h4v.s7.4a019cc43923 from=translated src=- shape=df0900a8 vocab=24a943e6
-/
lemma hasSum_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun m : ℕ => c m * q ^ m) (discFun h F c q) := by
  have hy : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe]; simpa using hq
  have h := (hasFPowerSeriesOnBall_update hh hF).hasSum hy
  rw [zero_add] at h
  simpa [discFun, mul_comm] using h

/--
@isnad1 id=eq.2h4v.s6.c9e04d8d8c69 from=translated src=- shape=7ddb5566 vocab=d884ee37
-/
lemma apply_eq_discFun (hh : 0 < h) (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (τ : ℍ) : F τ = discFun h F c (𝕢 h (τ : ℂ)) :=
  (hF τ).unique (hasSum_discFun hh hF (norm_qParam_lt_one_of_pos hh τ))

/--
@isnad1 id=differen.2h3v.s7.28d3b9b57f19 from=translated src=- shape=1d000111 vocab=06b9a25a
-/
lemma differentiableOn_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    DifferentiableOn ℂ (discFun h F c) (Metric.ball 0 1) := by
  have h1 := (hasFPowerSeriesOnBall_update hh hF).differentiableOn
  rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h1

/--
@isnad1 id=continuo.3h4v.s6.61ce9db4d87c from=translated src=- shape=379b69a1 vocab=e333305c
-/
lemma continuousAt_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    ContinuousAt (discFun h F c) q :=
  ((differentiableOn_discFun hh hF).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

/--
@isnad1 id=eq.0h3v.s4.0bcd63392554 from=translated src=- shape=1e3f4c5f vocab=a56edf84
-/
lemma discFun_zero : discFun h F c 0 = c 0 := by simp [discFun]

/--
@isnad1 id=mdiffere.2h3v.s7.08495e7a3234 from=translated src=- shape=6ae28dc9 vocab=7b866695
-/
theorem mdifferentiable (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => discFun h F c (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖𝕢 h z‖ < 1 := by
      have := norm_qParam_lt_one_of_pos hh ⟨z, hz⟩
      simpa using this
    exact (((differentiableOn_discFun hh hF).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hzq))).comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  simp only [Function.comp_apply, apply_eq_discFun hh hF, ofComplex_apply_of_im_pos hz]

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

/--
@isnad1 id=isbounde.2h3v.s6.2cf9217f82d9 from=translated src=- shape=b242f1e2 vocab=bcdae71f
-/
theorem isBoundedAtImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    IsBoundedAtImInfty F :=
  (tendsto_atImInfty hh hF).isBigO_one ℝ

/--
@isnad1 id=eq.3h4v.s7.5ad8f3f83046 from=translated src=- shape=ef755aab vocab=a32911fb
-/
theorem coeff_unique {d : ℕ → ℂ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => d m * 𝕢 h (τ : ℂ) ^ m) (F τ)) : c = d := by
  have hc := hasFPowerSeriesOnBall_update hh hF
  have hd := hasFPowerSeriesOnBall_update hh hF'

  have hlim : ∀ {e : ℕ → ℂ}, HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (e 0)) (.ofScalars ℂ e) 0 1 →
      Tendsto (cuspFunction h F) (𝓝[≠] 0) (𝓝 (e 0)) := by
    intro e he
    have h1 : Tendsto (update (cuspFunction h F) 0 (e 0)) (𝓝[≠] 0) (𝓝 (e 0)) := by
      have := he.hasFPowerSeriesAt.continuousAt.tendsto
      rw [update_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using update_of_ne hz ..
  have h0 : c 0 = d 0 := tendsto_nhds_unique (hlim hc) (hlim hd)
  have hd' : HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ d) 0 1 := h0 ▸ hd
  have heq := hc.hasFPowerSeriesAt.eq_formalMultilinearSeries hd'.hasFPowerSeriesAt
  funext m
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) heq

end Realized

end ModularCurve

open ModularCurve in
/--
@isnad1 id=eq.3h3v.s8.6daeabb8ad5a from=translated src=- shape=e468de73 vocab=e4d59e39
-/
theorem solution {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ} (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) {m : ℕ} (hm : m ≠ 0) : c m = 0 := by
  have hslash : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hinv, neg_zero, zpow_zero, mul_one]
  let f : ModularForm 𝒮ℒ 0 :=
    { toFun := F
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, rfl⟩ := hA
        exact hslash γ
      holo' := Realized.mdifferentiable one_pos hF
      bdd_at_cusps' := fun {cusp} hc => by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ]
        exact Realized.isBoundedAtImInfty one_pos hF }
  obtain ⟨κ, hκ⟩ := ModularForm.eq_const_of_weight_zero f
  have hFκ : ∀ τ : ℍ, F τ = κ := fun τ => by
    exact congr_fun hκ τ

  have hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => (Pi.single (M := fun _ => ℂ) 0 κ m) * 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    rw [hFκ τ]
    have := hasSum_ite_eq 0 κ
    refine this.congr_fun fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  have heq := Realized.coeff_unique one_pos hF hF'
  rw [heq, Pi.single_apply, ite_eq_right hm]

end
