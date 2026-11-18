import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt

set_option autoImplicit false

noncomputable section

open _root_.Complex open _root_.Real open _root_.UpperHalfPlane open _root_.Function open _root_.Filter open _root_.Polynomial open _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLightBdd

section CuspCriterion

variable {N : ℕ}

/--
@isnad1 id=isbounde.0h0v.s8.a443ea96338b from=translated src=- shape=451f6dce vocab=263ed9cb
-/
lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

/--
@isnad1 id=isbounde.0h1v.s8.f33768f72c2c from=translated src=- shape=06c18666 vocab=65b1bbd9
-/
lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

/--
@isnad1 id=eq.0h1v.s9.2f5646ba3b04 from=translated src=- shape=87e9d799 vocab=a4a269c4
-/
lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

/--
@isnad1 id=periodic.0h1v.s5.307a22a71491 from=translated src=- shape=ebc4bdb0 vocab=3e5782a9
-/
lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

/--
@isnad1 id=periodic.0h2v.s8.2e4b03ac59fe from=translated src=- shape=2278e424 vocab=4046b8a1
-/
lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

/--
@isnad1 id=mdiffere.0h1v.s8.daa6b50887c3 from=translated src=- shape=28a1ef6d vocab=a57ebf8f
-/
lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

/--
@isnad1 id=mdiffere.1h2v.s9.6eac709d05ea from=translated src=- shape=3c3d77be vocab=9ed14d55
-/
lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

/--
@isnad1 id=analytic.3h2v.s7.2cd82fc8dc71 from=translated src=- shape=59ef79a2 vocab=19da8d4b
-/
lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

/--
@isnad1 id=eq.0h1v.s8.f0c5acc49384 from=translated src=- shape=15c04e4c vocab=e522a9b5
-/
lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

/--
@isnad1 id=eq.0h1v.s8.437bc416d1e1 from=translated src=- shape=b2ac6171 vocab=410d4c90
-/
lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

/--
@isnad1 id=eq.2h3v.s7.55ac418b75be from=translated src=- shape=31a908b9 vocab=f8303012
-/
lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

/--
@isnad1 id=eq.0h0v.s6.5e05fa10df7a from=translated src=- shape=ae8fa524 vocab=db8d97ee
-/
lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

/--
@isnad1 id=eq.1h2v.s5.eef4706f04bb from=translated src=- shape=55d416ad vocab=ff4ad4eb
-/
lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

/--
@isnad1 id=eq.4h3v.s8.30500c81409c from=translated src=- shape=5e5984d4 vocab=ddb4bc45
-/
theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

open Asymptotics in

/--
@isnad1 id=isbigo.5h3v.s8.8607adad7397 from=translated src=- shape=f9fec9c7 vocab=d007e462
-/
theorem isBigO_qParam_pow_of_qExpansion_coeff_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f)
    {k : ℕ} (hcoeff : ∀ n ≤ k, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] fun τ ↦ (Periodic.qParam h τ) ^ (k + 1) := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hideriv : ∀ i < k + 1, iteratedDeriv i (cuspFunction h f) 0 = 0 := by
    intro i hi
    have hci := hcoeff i (Nat.lt_succ_iff.mp hi)
    rw [qExpansion_coeff] at hci
    have hfac : ((i.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    exact (mul_eq_zero.mp hci).resolve_left hfac
  have hord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanal).mpr hideriv
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt hanal).mp hord
  have hOcf : (cuspFunction h f) =O[𝓝 0] fun q : ℂ ↦ q ^ (k + 1) := by
    have hg1 : g =O[𝓝 (0 : ℂ)] (fun _ : ℂ ↦ (1 : ℂ)) := hgan.continuousAt.isBigO_one ℂ
    refine ((isBigO_refl (fun q : ℂ ↦ q ^ (k + 1)) (𝓝 0)).mul hg1).congr' ?_
      (.of_forall fun q ↦ mul_one _)
    filter_upwards [hfac] with q hq
    rw [hq, sub_zero, smul_eq_mul]
  refine (hOcf.comp_tendsto (qParam_tendsto_atImInfty hh)).congr' ?_ (.of_forall fun τ ↦ rfl)
  exact .of_forall fun τ ↦ eq_cuspFunction τ hh.ne' hfper

open Asymptotics ModularForm in

/--
@isnad1 id=isbigo.1h2v.s6.cff030e5b51c from=translated src=- shape=d110e423 vocab=e5a63f7d
-/
theorem qParam_pow_isBigO_discPow {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * k)) =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ k) := by
  refine .trans (IsBigO.of_bound 1 (.of_forall fun τ ↦ le_of_eq ?_)) (exp_isBigO_discriminant.pow k)
  rw [one_mul, norm_pow, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le,
    pow_mul, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, UpperHalfPlane.coe_im]
  congr 2
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

open ModularForm in
set_option maxHeartbeats 1600000 in

/--
@isnad1 id=eq.1h3v.s8.245a01f1717d from=translated src=- shape=2d8a5bf5 vocab=78b23c58
-/
lemma qExpansion_discPow_coeff_eq_zero_of_lt [NeZero N] (k : ℕ) {j : ℕ} (hj : j < N * k) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff j = 0 := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper
    (mdiff_discPow k) (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split_ifs with hN
  · exact coeff_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero
      (Nat.div_lt_of_lt_mul (Nat.mul_comm N k ▸ hj))
  · rfl

open Asymptotics ModularForm in

/--
@isnad1 id=isbounde.5h3v.s10.febb5dbe5fc4 from=translated src=- shape=79e92887 vocab=3b00eff6
-/
theorem isBoundedAtImInfty_of_coeff_lt {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n < N * M, (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsBoundedAtImInfty F := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    simpa using hfbd
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNM : N * M - 1 + 1 = N * M := Nat.sub_add_cancel (Nat.mul_pos (Nat.pos_of_ne_zero hN) hMpos)
  have hGO : G =O[atImInfty] fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * M - 1 + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd fun n hn => hcoeff n (by omega)
  rw [hNM] at hGO
  have hGO' : G =O[atImInfty] (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ M) :=
    hGO.trans (qParam_pow_isBigO_discPow hN M)
  have hfdeq : ∀ τ : ℍ, F τ = G τ / (ModularForm.discriminant τ) ^ M := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ)]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty (fun τ : ℍ ↦ ‖G τ / (ModularForm.discriminant τ : ℂ) ^ M‖) :=
    div_isBoundedUnder_of_isBigO hGO'
  have hfun : (fun τ : ℍ ↦ ‖F τ‖) = fun τ : ℍ ↦ ‖G τ / (ModularForm.discriminant τ : ℂ) ^ M‖ :=
    funext fun τ => by rw [hfdeq τ]
  have hbnd' : IsBoundedUnder (· ≤ ·) atImInfty (fun τ : ℍ ↦ ‖F τ‖) := by
    rw [hfun]; exact hbnd
  change F =O[atImInfty] (1 : ℍ → ℝ)
  exact (isBigO_one_iff ℝ).mpr hbnd'

open ModularForm in

/--
@isnad1 id=eq.4h4v.s9.5618081fa8ad from=translated src=- shape=c51feabf vocab=68d3f826
-/
theorem qExpansion_coeff_eq_zero_of_isBoundedAtImInfty [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ ofComplex) N)
    (hFbd : IsBoundedAtImInfty F) :
    ∀ n < N * M, (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  intro n hn
  rw [qExpansion_mul (analyticAt_cuspFunction_zero_of hFhol hFper hFbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow M)
        (periodic_discPow_comp_ofComplex M N) (isBoundedAtImInfty_discPow M)),
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [qExpansion_discPow_coeff_eq_zero_of_lt M (show j < N * M by omega), mul_zero]

end CuspCriterion

end WLightBdd

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

open WLightBdd in
/--
@isnad1 id=iff.3h3v.s8.6d70d7110adf from=translated src=- shape=be90a6cc vocab=91f4000a
-/
theorem solution (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsBoundedAtImInfty F ↔
      ∀ n < N * M,
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by
  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  have hFbd' : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M) := by
    rwa [show (⇑CuspForm.discriminant : ℍ → ℂ) = ModularForm.discriminant from
      CuspForm.coe_discriminant]
  exact ⟨qExpansion_coeff_eq_zero_of_isBoundedAtImInfty hFhol hFper,
    isBoundedAtImInfty_of_coeff_lt (NeZero.ne N) (mdiff_mul_discPow hFhol M)
      (hFper.mul (periodic_discPow_comp_ofComplex M N)) hFbd'⟩
