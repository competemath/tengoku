import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_tendsto_slash_div_qParam_pow_of_conj_T_pow_mem

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace WCuspOrdAux

/--
@isnad1 id=ex.3h4v.s7.fed69ee2cae1 from=translated src=- shape=79e77955 vocab=7e65be02
-/
theorem exists_tendsto_div_qParam_pow {Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ'.strictPeriods) (F : ModularForm Γ' k) (hF : F ≠ 0) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => F τ / Function.Periodic.qParam h τ ^ n) atImInfty (𝓝 a) := by
  have hper : Function.Periodic ((F : ℍ → ℂ) ∘ ofComplex) h := SlashInvariantFormClass.periodic_comp_ofComplex F hΓ
  have hG : AnalyticAt ℂ (cuspFunction h F) 0 := ModularFormClass.analyticAt_cuspFunction_zero F hh hΓ
  haveI : Fact (IsCusp OnePoint.infty Γ') := ⟨Γ'.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction h F z = 0 := by
    intro h0
    apply hF
    have hsum := fun τ : ℍ =>
      hasSum_qExpansion hh hper (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
    have hps := hasFPowerSeriesOnBall_cuspFunction hh hG hsum
    have hp0 := hps.hasFPowerSeriesAt.locally_zero_iff.mp h0
    rw [← ModularForm.qExpansion_eq_zero_iff hh hΓ F]
    ext m
    have e := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff m) hp0
    simp [FormalMultilinearSeries.coeff_ofScalars] at e
    exact e
  obtain ⟨n, g, hg, hg0, hfg⟩ := hG.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  refine ⟨n, g 0, hg0, ?_⟩
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam h τ) atImInfty (𝓝[≠] 0) :=
    (Function.Periodic.qParam_tendsto hh).comp UpperHalfPlane.tendsto_coe_atImInfty
  have hlim : Tendsto (fun z : ℂ => cuspFunction h F z / z ^ n) (𝓝[≠] 0) (𝓝 (g 0)) := by
    have hgc : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hgc.congr' ?_
    have hfg' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), cuspFunction h F z = (z - 0) ^ n • g z := hfg.filter_mono nhdsWithin_le_nhds
    filter_upwards [hfg', self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, mul_div_cancel_left₀ _ (pow_ne_zero n hz0')]
  refine (hlim.comp hq).congr (fun τ => ?_)
  simp only [Function.comp_apply]
  rw [UpperHalfPlane.eq_cuspFunction τ hh.ne' hper]

/--
@isnad1 id=eq.0h1v.s9.996b6ff8d97e from=translated src=- shape=4844cffe vocab=cb177661
-/
theorem mapGL_T_zpow (n : ℤ) :
    Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n) = Matrix.GeneralLinearGroup.upperRightHom (n : ℝ) := by
  simp only [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]

end WCuspOrdAux

open WCuspOrdAux in

/--
@isnad1 id=ex.3h5v.s11.184cb56a550c from=translated src=- shape=acbc9169 vocab=51816979
-/
theorem WCuspOrdAux.slash_main
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) := by
  let F := ModularForm.translate f (σ : GL (Fin 2) ℝ)
  have hΓ' : ((h : ℝ)) ∈ (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ))⁻¹ •
      (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
      ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    refine Subgroup.mem_map.mpr ⟨σ * ModularGroup.T ^ h * σ⁻¹, hper, ?_⟩
    rw [map_mul, map_mul, map_inv, ← zpow_natCast, mapGL_T_zpow, Int.cast_natCast]
    rfl
  have hF : F ≠ 0 := by
    intro h0
    apply hf
    have hc : ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) = 0 := by
      have e1 : ((F : ℍ → ℂ)) = ((0 : ModularForm _ k) : ℍ → ℂ) := congrArg DFunLike.coe h0
      rw [FunLike.coe_zero] at e1
      exact e1
    rw [← FunLike.coe_zero_iff]
    have e : (f : ℍ → ℂ) = ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) ∣[k] ((σ : GL (Fin 2) ℝ))⁻¹ := by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [e, hc, SlashAction.zero_slash]
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  obtain ⟨n, a, ha, hlim⟩ := exists_tendsto_div_qParam_pow hhR hΓ' F hF
  exact ⟨n, a, ha, hlim⟩

/--
@isnad1 id=ex.3h5v.s11.184cb56a550c from=translated src=- shape=acbc9169 vocab=51816979
-/
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ≠ 0)
    (σ : SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hper : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ) :
    ∃ (n : ℕ) (a : ℂ), a ≠ 0 ∧
      Tendsto (fun τ : ℍ => ((f : ℍ → ℂ) ∣[k] (σ : GL (Fin 2) ℝ)) τ / Function.Periodic.qParam h τ ^ n)
        atImInfty (𝓝 a) :=
  WCuspOrdAux.slash_main Γ k f hf σ h hh hper

