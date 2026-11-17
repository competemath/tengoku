import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinSeries_ramanujan_system_qExpansion_int.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex Filter Function
open scoped Real Topology MatrixGroups Manifold ModularForm ArithmeticFunction.sigma

noncomputable section

namespace EisensteinSeries
export _root_.EisensteinSeries (E_qExpansion_coeff E2_slash_action E2 D2 E2_eq_tsum_cexp r)
namespace RamanujanSystemInt
open _root_.EisensteinSeries

local notation "𝕢₁" => Periodic.qParam 1

/--
@isnad1 id=eq.0h1v.s5.c26476b6a097 from=translated src=- shape=b44dcb99 vocab=4d80dbb4
-/
theorem qParam_one_eq (z : ℂ) : 𝕢₁ z = cexp (2 * π * I * z) := by
  simp [Periodic.qParam]

/--
@isnad1 id=lt.0h1v.s4.457a3b4f3ae5 from=translated src=- shape=096985cf vocab=6bddaf06
-/
theorem norm_qParam_one_lt_one (τ : ℍ) : ‖𝕢₁ τ‖ < 1 := by
  simpa using τ.norm_qParam_lt_one 1

/--
@isnad1 id=lt.0h1v.s4.6c32cb5ee31a from=translated src=- shape=2fec93ab vocab=6bddaf06
-/
theorem norm_qParam_one_pos (τ : ℍ) : 0 < ‖𝕢₁ τ‖ := by
  rw [qParam_one_eq]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)

/--
@isnad1 id=eq.0h1v.s5.2c6658f6a92b from=translated src=- shape=1c63c504 vocab=697a44d5
-/
theorem norm_qParam_one (z : ℂ) : ‖𝕢₁ z‖ = Real.exp (-2 * π * z.im) := by
  rw [Periodic.norm_qParam, div_one]

def PolyGrowth (a : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ k

def IsQS (a : ℕ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n => a n * 𝕢₁ τ ^ n) (f τ)

/--
@isnad1 id=summable.2h2v.s6.192cdc942af5 from=translated src=- shape=a56b3633 vocab=0b47f1eb
-/
theorem summable_succ_pow_mul_geometric {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k (by simpa [Real.norm_of_nonneg hr0.le] using hr)
  have h1 := (summable_nat_add_iff 1).mpr h0
  refine (h1.mul_left r⁻¹).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/--
@isnad1 id=summable.3h2v.s6.aec0d6d3359b from=translated src=- shape=891c1251 vocab=c0f482a0
-/
theorem PolyGrowth.summable_norm_mul {a : ℕ → ℂ} (ha : PolyGrowth a) {r : ℝ} (hr0 : 0 < r)
    (hr : r < 1) : Summable fun n => ‖a n‖ * r ^ n := by
  obtain ⟨C, k, hC, h⟩ := ha
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (h n) (by positivity)) ?_
  simpa [mul_assoc] using (summable_succ_pow_mul_geometric hr0 hr k).mul_left C

/--
@isnad1 id=summable.1h2v.s5.da63c6863988 from=translated src=- shape=9e8f4422 vocab=56dfade5
-/
theorem PolyGrowth.summable_norm {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => ‖a n * 𝕢₁ τ ^ n‖ := by
  simpa [norm_mul, norm_pow] using
    ha.summable_norm_mul (norm_qParam_one_pos τ) (norm_qParam_one_lt_one τ)

/--
@isnad1 id=summable.1h2v.s6.7d85ed8ff2a0 from=translated src=- shape=63dbf26a vocab=5270e201
-/
theorem PolyGrowth.summable {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => a n * 𝕢₁ τ ^ n :=
  (ha.summable_norm τ).of_norm

/--
@isnad1 id=polygrow.1h1v.s4.367c61ae2670 from=translated src=- shape=a2e5556e vocab=d460c31e
-/
theorem PolyGrowth.theta {a : ℕ → ℂ} (ha : PolyGrowth a) : PolyGrowth fun n => (n : ℂ) * a n := by
  obtain ⟨C, k, hC, h⟩ := ha
  refine ⟨C, k + 1, hC, fun n => ?_⟩
  rw [norm_mul, Complex.norm_natCast, pow_succ]
  have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc (n : ℝ) * ‖a n‖ ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) ^ k) :=
        mul_le_mul h1 (h n) (norm_nonneg _) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ k * ((n : ℝ) + 1)) := by ring

/--
@isnad1 id=le.0h2v.s6.c93d18520dbf from=translated src=- shape=f3c94906 vocab=d8552bb1
-/
theorem sigma_le_succ_pow (k n : ℕ) : ((σ k n : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := by
  have h := ArithmeticFunction.sigma_le_pow_succ k n
  calc ((σ k n : ℕ) : ℝ) ≤ ((n ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (n : ℝ) ^ (k + 1) := by push_cast; ring
    _ ≤ ((n : ℝ) + 1) ^ (k + 1) := by
        gcongr; linarith

/--
@isnad1 id=polygrow.0h2v.s5.274484e878c3 from=translated src=- shape=d0aaaea9 vocab=3aac795c
-/
theorem PolyGrowth.eisenstein (c : ℂ) (k : ℕ) :
    PolyGrowth fun n => if n = 0 then 1 else c * ((σ k n : ℕ) : ℂ) := by
  refine ⟨‖c‖ + 1, k + 1, by positivity, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := one_le_pow₀ (by simp)
  dsimp only
  split_ifs with hn
  · simp only [norm_one]
    nlinarith [norm_nonneg c]
  · rw [norm_mul, Complex.norm_natCast]
    calc ‖c‖ * (σ k n : ℝ) ≤ ‖c‖ * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; exact sigma_le_succ_pow k n
      _ ≤ (‖c‖ + 1) * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; linarith

/--
@isnad1 id=isqs.2h4v.s5.0349d6dee322 from=translated src=- shape=1a6cbde9 vocab=a0bef1ab
-/
theorem IsQS.sub {a b : ℕ → ℂ} {f g : ℍ → ℂ} (hf : IsQS a f) (hg : IsQS b g) :
    IsQS (fun n => a n - b n) (fun τ => f τ - g τ) := by
  intro τ
  simpa [sub_mul] using (hf τ).sub (hg τ)

/--
@isnad1 id=isqs.1h3v.s5.96060ed9a16c from=translated src=- shape=fdaa34e4 vocab=6eaf885a
-/
theorem IsQS.const_mul {a : ℕ → ℂ} {f : ℍ → ℂ} (c : ℂ) (hf : IsQS a f) :
    IsQS (fun n => c * a n) (fun τ => c * f τ) := by
  intro τ
  simpa [mul_assoc] using (hf τ).mul_left c

/--
@isnad1 id=isqs.4h4v.s6.95ad28aaae71 from=translated src=- shape=19ee4ceb vocab=3f58f373
-/
theorem IsQS.mul {a b : ℕ → ℂ} {f g : ℍ → ℂ} (ha : PolyGrowth a) (hb : PolyGrowth b)
    (hf : IsQS a f) (hg : IsQS b g) :
    IsQS (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2) (fun τ => f τ * g τ) := by
  intro τ
  beta_reduce
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n => a n * 𝕢₁ τ ^ n) (g := fun n => b n * 𝕢₁ τ ^ n)
    (ha.summable_norm τ) (hb.summable_norm τ)
  have hs : Summable fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (a kl.1 * 𝕢₁ τ ^ kl.1) * (b kl.2 * 𝕢₁ τ ^ kl.2) :=
    summable_sum_mul_antidiagonal_of_summable_norm'
      (f := fun n => a n * 𝕢₁ τ ^ n) (g := fun n => b n * 𝕢₁ τ ^ n)
      (ha.summable_norm τ) (ha.summable τ) (hb.summable_norm τ) (hb.summable τ)
  rw [(hf τ).tsum_eq, (hg τ).tsum_eq] at hprod
  rw [hprod]
  convert hs.hasSum using 1
  funext n
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

/--
@isnad1 id=isbounde.2h2v.s4.ca4460e82c68 from=translated src=- shape=aa6b2d2c vocab=893a1401
-/
theorem IsQS.isBoundedAtImInfty {a : ℕ → ℂ} {f : ℍ → ℂ} (ha : PolyGrowth a) (hf : IsQS a f) :
    IsBoundedAtImInfty f := by
  rw [isBoundedAtImInfty_iff]
  set r : ℝ := Real.exp (-2 * π) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := Real.pi_pos
    linarith
  refine ⟨∑' n, ‖a n‖ * r ^ n, 1, fun z hz => ?_⟩
  refine (hf z).norm_le_of_bounded (ha.summable_norm_mul hr0 hr1).hasSum fun n => ?_
  rw [norm_mul, norm_pow]
  gcongr
  rw [norm_qParam_one, hr, Real.exp_le_exp, coe_im]
  have := Real.pi_pos
  nlinarith

/--
@isnad1 id=eq.0h0v.s5.86b610922e63 from=translated src=- shape=6e92bb20 vocab=19ebe89d
-/
theorem cuspFunction_one_zero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
  simp [cuspFunction, Periodic.cuspFunction]
  exact Filter.Tendsto.limUnder_eq (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)

theorem IsQS.eq_zero {c : ℕ → ℂ} (h : ∀ τ : ℍ, HasSum (fun n => c n * 𝕢₁ τ ^ n) 0) (n : ℕ) :
    c n = 0 := by
  have hana : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := by
    rw [cuspFunction_one_zero]; exact analyticAt_const
  have h' : ∀ τ : ℍ, HasSum (fun m => c m • 𝕢₁ τ ^ m) ((0 : ℍ → ℂ) τ) := by
    intro τ; simpa only [smul_eq_mul, Pi.zero_apply] using h τ
  have H := hasFPowerSeriesOnBall_cuspFunction one_pos hana h'
  rw [cuspFunction_one_zero] at H
  have hp := H.hasFPowerSeriesAt.eq_zero
  have := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hp
  simpa [FormalMultilinearSeries.coeff_ofScalars, FormalMultilinearSeries.coeff_eq_zero.mpr
    (FormalMultilinearSeries.zero_apply (𝕜 := ℂ) (E := ℂ) (F := ℂ) n)] using this

/--
@isnad1 id=eq.2h3v.s5.f259a87cdf4a from=translated src=- shape=2cc3ef9b vocab=70e85a86
-/
theorem IsQS.unique {c : ℕ → ℂ} {f : ℍ → ℂ} (hf : IsQS c f) (h0 : ∀ τ, f τ = 0) (n : ℕ) :
    c n = 0 :=
  IsQS.eq_zero (fun τ => h0 τ ▸ hf τ) n

open Derivative in
/--
@isnad1 id=isqs.2h2v.s5.8a84011bd134 from=translated src=- shape=47d9d29a vocab=32ad1003
-/
theorem IsQS.theta {a : ℕ → ℂ} {f : ℍ → ℂ} (ha : PolyGrowth a) (hf : IsQS a f) :
    IsQS (fun n => (n : ℂ) * a n) (D f) := by
  intro τ

  set y : ℝ := τ.im / 2 with hy
  have hy0 : 0 < y := by have := τ.im_pos; positivity
  set U : Set ℂ := {w : ℂ | y < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by
    show y < (τ : ℂ).im
    rw [coe_im]; have := τ.im_pos; linarith

  set F : ℕ → ℂ → ℂ := fun n w => a n * cexp (2 * π * I * w) ^ n with hF
  have hFq : ∀ (n : ℕ) (w : ℂ), F n w = a n * 𝕢₁ w ^ n := by
    intro n w; simp [hF, qParam_one_eq]
  have hFd : ∀ (n : ℕ) (w : ℂ), HasDerivAt (F n)
      (a n * (n * cexp (2 * π * I * w) ^ (n - 1) * (cexp (2 * π * I * w) * (2 * π * I)))) w := by
    intro n w
    have h1 : HasDerivAt (fun w : ℂ => 2 * π * I * w) (2 * π * I) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * π * I)
    have h2 := h1.cexp
    have h3 := h2.pow n
    exact h3.const_mul (a n)
  have hFdiff : ∀ n, DifferentiableOn ℂ (F n) U :=
    fun n w _ => (hFd n w).differentiableAt.differentiableWithinAt

  set r : ℝ := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ ‖a n‖ * r ^ n := by
    intro n w hw
    rw [hFq, norm_mul, norm_pow]
    gcongr
    rw [norm_qParam_one, hr, Real.exp_le_exp]
    have := Real.pi_pos
    have hw' : y < w.im := hw
    nlinarith
  have hsum := Complex.hasSum_deriv_of_summable_norm (ha.summable_norm_mul hr0 hr1) hFdiff hUo
    hbound hτU

  have hev : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] fun w => ∑' n, F n w := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    rw [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    have := (hf ⟨w, hw⟩).tsum_eq
    simp only [hFq]
    exact this.symm
  have hderiv : deriv (f ∘ ofComplex) τ = deriv (fun w => ∑' n, F n w) τ := hev.deriv_eq
  simp only [normalizedDerivOfComplex, hderiv]
  have h2 := hsum.mul_left (2 * π * I)⁻¹
  convert h2 using 1
  all_goals try rfl
  funext n
  rw [(hFd n τ).deriv, ← qParam_one_eq]
  have hpi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp

open Derivative

/--
@isnad1 id=eq.0h1v.s10.47f32946618b from=translated src=- shape=b678224e vocab=c8efcb1a
-/
theorem det_coe_SL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (γ.map (Int.castRingHom ℝ))
  simpa using this

/--
@isnad1 id=eq.0h2v.s10.5d2dc78b48ee from=translated src=- shape=19adbe5c vocab=79df1863
-/
theorem denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

/--
@isnad1 id=hasderiv.1h3v.s10.9aa12a80bbe1 from=translated src=- shape=15545270 vocab=83ea327c
-/
theorem hasDerivAt_comp_smul {F : ℍ → ℂ} (hF : MDiff F) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (γ • ofComplex z))
      (deriv (F ∘ ofComplex) ↑(γ • τ) * (1 / denom (γ : GL (Fin 2) ℝ) τ ^ 2)) τ := by
  have hs := (hasStrictDerivAt_smul (g := (γ : GL (Fin 2) ℝ))
    (by rw [det_coe_SL]; exact one_pos) τ).hasDerivAt
  have hF' : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ↑(γ • τ))
      ↑((γ : GL (Fin 2) ℝ) • ofComplex (τ : ℂ)) := by
    rw [ofComplex_apply]
    exact (mdifferentiableAt_iff.mp (hF _)).hasDerivAt
  have := hF'.comp (τ : ℂ) hs
  convert this using 1
  all_goals try rfl
  · ext z
    simp only [Function.comp_apply, ofComplex_apply]
    rfl
  · rw [det_coe_SL]; push_cast; ring

/--
@isnad1 id=hasderiv.0h3v.s11.77ea43995862 from=translated src=- shape=6bc24241 vocab=146c431c
-/
theorem hasDerivAt_denom_zpow (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z ^ (-k))
      ((-k : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) * ((γ 1 0 : ℤ) : ℂ)) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hlin : HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z) ((γ 1 0 : ℤ) : ℂ) τ := by
    simp_rw [denom_SL]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have hz := (hasDerivAt_zpow (-k) (denom (γ : GL (Fin 2) ℝ) τ) (Or.inl hden)).comp (τ : ℂ) hlin
  push_cast at hz
  exact hz

/--
@isnad1 id=eq.1h4v.s11.33adb223ba13 from=translated src=- shape=5c756db3 vocab=e62f64b8
-/
theorem D_apply_smul {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    D F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) * D (F ∣[k] γ) τ
        + k * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ * F (γ • τ) := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hprod := (hasDerivAt_comp_smul hF γ τ).mul (hasDerivAt_denom_zpow k γ τ)
  have hev : ((F ∣[k] γ) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ => F (γ • ofComplex z) * denom (γ : GL (Fin 2) ℝ) z ^ (-k) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    rw [Function.comp_apply, ModularForm.SL_slash_apply, ofComplex_apply_of_im_pos hz]
  have hD := hprod.congr_of_eventuallyEq hev
  simp only [Derivative.normalizedDerivOfComplex]
  rw [hD.deriv]
  have e1 : denom (γ : GL (Fin 2) ℝ) τ ^ (-k - 1) =
      (denom (γ : GL (Fin 2) ℝ) τ ^ k)⁻¹ * (denom (γ : GL (Fin 2) ℝ) τ)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ hden, zpow_neg_one, zpow_neg]
  have e2 : denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) =
      denom (γ : GL (Fin 2) ℝ) τ ^ k * denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [zpow_add₀ hden]; norm_cast
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := zpow_ne_zero k hden
  rw [e1, e2, zpow_neg]
  simp only [ofComplex_apply, Function.comp_def]
  field_simp
  ring

/--
@isnad1 id=eq.2h4v.s11.c5fe8444189d from=translated src=- shape=5921279b vocab=e37a6c72
-/
theorem D_apply_smul_of_invariant {F : ℍ → ℂ} (hF : MDiff F) (k : ℕ) (γ : SL(2, ℤ))
    (hinv : F ∣[(k : ℤ)] γ = F) (τ : ℍ) :
    D F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ (k + 2) * D F τ
        + k * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ (k + 1) * F τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hFw : F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * F τ := by
    have h := congrFun hinv τ
    rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast] at h
    rw [← h]; field_simp
  have h := D_apply_smul hF k γ τ
  rw [hinv, hFw] at h
  rw [h, show ((k : ℤ) + 2 : ℤ) = ((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  push_cast
  ring

/--
@isnad1 id=eq.0h0v.s6.5b9c7c253483 from=translated src=- shape=3bc0b771 vocab=99c52e58
-/
theorem K_eq : (1 / (2 * riemannZeta 2) : ℂ) = -12 * ((2 * π * I)⁻¹) ^ 2 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

/--
@isnad1 id=eq.0h2v.s11.ea8fad4312f7 from=translated src=- shape=afd4dc5b vocab=ee477f8c
-/
theorem E2_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    E2 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * E2 τ
      + 12 * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := congrFun (E2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D2] at h
  rw [K_eq, zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at h
  have h2 : E2 (γ • τ) = (E2 τ - -12 * ((2 * π * I)⁻¹) ^ 2 *
      (2 * π * I * ((γ 1 0 : ℤ) : ℂ) / denom (γ : GL (Fin 2) ℝ) τ)) *
        denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [← h]; field_simp
  rw [h2]
  field_simp
  ring

/--
@isnad1 id=hasderiv.0h2v.s10.da2a5663e9d2 from=translated src=- shape=676302b2 vocab=0a2b415d
-/
theorem hasDerivAt_D2 (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (D2 γ ∘ ofComplex)
      (-(2 * π * I) * ((γ 1 0 : ℤ) : ℂ) ^ 2 / denom (γ : GL (Fin 2) ℝ) τ ^ 2) τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hlin : HasDerivAt (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z) ((γ 1 0 : ℤ) : ℂ) τ := by
    simp_rw [denom_SL]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h := (hlin.inv hden).const_mul (2 * π * I * ((γ 1 0 : ℤ) : ℂ))
  have hev : (fun z : ℂ => 2 * π * I * ((γ 1 0 : ℤ) : ℂ) * (denom (γ : GL (Fin 2) ℝ) z)⁻¹)
      =ᶠ[𝓝 (τ : ℂ)] (D2 γ ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    simp only [Function.comp_apply, D2, ofComplex_apply_of_im_pos hz, div_eq_mul_inv]
  convert h.congr_of_eventuallyEq hev.symm using 1
  all_goals try rfl
  field_simp

/--
@isnad1 id=eq.0h2v.s10.b716054f9b22 from=translated src=- shape=3d6602d8 vocab=8b9b41c9
-/
theorem D_E2_slash (γ : SL(2, ℤ)) (τ : ℍ) :
    D (E2 ∣[(2 : ℤ)] γ) τ =
      D E2 τ + (1 / (2 * riemannZeta 2)) * ((γ 1 0 : ℤ) : ℂ) ^ 2 / denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [E2_slash_action γ]
  have h1 : HasDerivAt (E2 ∘ ofComplex) (deriv (E2 ∘ ofComplex) τ) τ :=
    (mdifferentiableAt_iff.mp (E2_mdifferentiable τ)).hasDerivAt
  have h3 := h1.sub ((hasDerivAt_D2 γ τ).const_mul (1 / (2 * riemannZeta 2)))
  have hfun : ((E2 - (1 / (2 * riemannZeta 2)) • D2 γ) ∘ ofComplex) =
      (E2 ∘ ofComplex) - fun z => (1 / (2 * riemannZeta 2)) * (D2 γ ∘ ofComplex) z := by
    funext z; simp [smul_eq_mul]
  simp only [normalizedDerivOfComplex]
  rw [hfun, h3.deriv]
  field_simp
  ring

/--
@isnad1 id=eq.0h2v.s11.57159f488d1e from=translated src=- shape=2aaa1217 vocab=395a074c
-/
theorem D_E2_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    D E2 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 4 * D E2 τ
      + 2 * (2 * π * I)⁻¹ * ((γ 1 0 : ℤ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ ^ 3 * E2 τ
      + 12 * ((2 * π * I)⁻¹) ^ 2 * ((γ 1 0 : ℤ) : ℂ) ^ 2 * denom (γ : GL (Fin 2) ℝ) τ ^ 2 := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [D_apply_smul E2_mdifferentiable 2 γ τ, D_E2_slash, E2_apply_smul, K_eq,
    show ((2 : ℤ) + 2 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
  push_cast
  field_simp
  ring

def A4 : ℍ → ℂ := (12 : ℂ) • D E2 - E2 * E2 + ⇑ModularForm.E₄

def B6 : ℍ → ℂ := (3 : ℂ) • D ⇑ModularForm.E₄ - E2 * ⇑ModularForm.E₄ + ⇑ModularForm.E₆

def C8 : ℍ → ℂ :=
  (2 : ℂ) • D ⇑ModularForm.E₆ - E2 * ⇑ModularForm.E₆ + ⇑ModularForm.E₄ * ⇑ModularForm.E₄

/--
@isnad1 id=eq.0h1v.s8.ec2b73928f43 from=translated src=- shape=b6fc8da3 vocab=4de10245
-/
theorem A4_apply (τ : ℍ) : A4 τ = 12 * D E2 τ - E2 τ * E2 τ + ModularForm.E₄ τ := by
  simp [A4, smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s9.9339dcaef2cb from=translated src=- shape=c8ca05de vocab=0bbbae67
-/
theorem B6_apply (τ : ℍ) :
    B6 τ = 3 * D ⇑ModularForm.E₄ τ - E2 τ * ModularForm.E₄ τ + ModularForm.E₆ τ := by
  simp [B6, smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s10.58a4570e72cd from=translated src=- shape=57866641 vocab=6565c846
-/
theorem C8_apply (τ : ℍ) : C8 τ =
    2 * D ⇑ModularForm.E₆ τ - E2 τ * ModularForm.E₆ τ + ModularForm.E₄ τ * ModularForm.E₄ τ := by
  simp [C8, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s9.c76069e12e4d from=translated src=- shape=9039d4c9 vocab=271cb1e1
-/
theorem E_slash_eq {k : ℤ} (F : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) : (⇑F) ∣[k] γ = ⇑F := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn F _ ⟨γ, rfl⟩

/--
@isnad1 id=eq.0h4v.s10.22d6510a9af8 from=translated src=- shape=30829f2b vocab=45e625ab
-/
theorem E_apply_smul {k : ℕ} (F : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    F (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * F τ := by
  have hden : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (E_slash_eq F γ) τ
  rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast] at h
  rw [← h]; field_simp

/--
@isnad1 id=eq.0h2v.s10.1957119cf6bd from=translated src=- shape=f4a8ebf9 vocab=df1fd0b6
-/
theorem A4_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    A4 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 4 * A4 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  rw [A4_apply, A4_apply, D_E2_apply_smul, E2_apply_smul, h4]
  ring

/--
@isnad1 id=eq.0h2v.s10.db1b801c8e5e from=translated src=- shape=f4a8ebf9 vocab=e989afd1
-/
theorem B6_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    B6 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 6 * B6 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  have h6 := E_apply_smul (k := 6) ModularForm.E₆ γ τ
  have hD := D_apply_smul_of_invariant (ModularFormClass.holo ModularForm.E₄) 4 γ
    (E_slash_eq (k := 4) ModularForm.E₄ γ) τ
  rw [B6_apply, B6_apply, hD, E2_apply_smul, h4, h6]
  push_cast
  ring

/--
@isnad1 id=eq.0h2v.s10.7a178ce05aef from=translated src=- shape=f4a8ebf9 vocab=afbbf702
-/
theorem C8_apply_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    C8 (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 8 * C8 τ := by
  have h4 := E_apply_smul (k := 4) ModularForm.E₄ γ τ
  have h6 := E_apply_smul (k := 6) ModularForm.E₆ γ τ
  have hD := D_apply_smul_of_invariant (ModularFormClass.holo ModularForm.E₆) 6 γ
    (E_slash_eq (k := 6) ModularForm.E₆ γ) τ
  rw [C8_apply, C8_apply, hD, E2_apply_smul, h4, h6]
  push_cast
  ring

open PowerSeries

def e2c (n : ℕ) : ℂ := if n = 0 then 1 else -24 * ((σ 1 n : ℕ) : ℂ)

def e4c (n : ℕ) : ℂ := if n = 0 then 1 else 240 * ((σ 3 n : ℕ) : ℂ)

def e6c (n : ℕ) : ℂ := if n = 0 then 1 else -504 * ((σ 5 n : ℕ) : ℂ)

/--
@isnad1 id=polygrow.0h0v.s1.0ab58c183616 from=translated src=- shape=49959d42 vocab=faa740a4
-/
theorem polyGrowth_e2c : PolyGrowth e2c := PolyGrowth.eisenstein _ _
/--
@isnad1 id=polygrow.0h0v.s1.349caf6416da from=translated src=- shape=49959d42 vocab=6c6dc222
-/
theorem polyGrowth_e4c : PolyGrowth e4c := PolyGrowth.eisenstein _ _
/--
@isnad1 id=polygrow.0h0v.s1.47c7a14e195b from=translated src=- shape=49959d42 vocab=294e2bfe
-/
theorem polyGrowth_e6c : PolyGrowth e6c := PolyGrowth.eisenstein _ _

/--
@isnad1 id=isqs.0h0v.s1.6b7ae2b0e487 from=translated src=- shape=25b03439 vocab=9a468f99
-/
theorem isQS_E2 : IsQS e2c E2 := by
  intro τ
  have hσ : PolyGrowth fun n => ((σ 1 n : ℕ) : ℂ) :=
    ⟨1, 2, zero_le_one, fun n => by
      rw [Complex.norm_natCast, one_mul]; exact sigma_le_succ_pow 1 n⟩
  have hg := hσ.summable τ
  have h1 : ∑' n : ℕ+, ((σ 1 n : ℕ) : ℂ) * cexp (2 * π * I * τ) ^ (n : ℕ) =
      ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [← qParam_one_eq,
      tsum_pnat_eq_tsum_succ (f := fun n => ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n), hg.tsum_eq_zero_add]
    simp
  have hE : E2 τ = 1 + (-24) * ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [E2_eq_tsum_cexp, h1]; ring
  rw [hE]
  convert (hasSum_ite_eq 0 (1 : ℂ)).add (hg.hasSum.mul_left (-24)) using 1
  funext n
  simp only [e2c]
  split_ifs with hn
  · subst hn; simp
  · ring

scoped instance : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
  ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩

/--
@isnad1 id=isqs.0h2v.s9.225334cebdbc from=translated src=- shape=1e007855 vocab=f4520869
-/
theorem isQS_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    IsQS (fun n => coeff n (qExpansion 1 ⇑F)) ⇑F := by
  intro τ
  simpa only [smul_eq_mul] using hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ

/--
@isnad1 id=isqs.0h0v.s8.181ddab85b0b from=translated src=- shape=8dcc0693 vocab=6f66f0e8
-/
theorem isQS_E4 : IsQS e4c ModularForm.E₄ := by
  have h := isQS_of_levelOne ModularForm.E₄
  convert h using 2 with n
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  simp only [e4c]
  split_ifs
  · rfl
  · push_cast; ring

/--
@isnad1 id=isqs.0h0v.s8.e92e922c3b44 from=translated src=- shape=8dcc0693 vocab=8b28b2fd
-/
theorem isQS_E6 : IsQS e6c ModularForm.E₆ := by
  have h := isQS_of_levelOne ModularForm.E₆
  convert h using 2 with n
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  simp only [e6c]
  split_ifs
  · rfl
  · push_cast; ring

def mkLevelOne (k : ℕ) (f : ℍ → ℂ)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * f τ)
    (hmd : MDiff f) (hbd : IsBoundedAtImInfty f) : ModularForm 𝒮ℒ (k : ℤ) :=
  have hinv : ∀ γ : SL(2, ℤ), f ∣[(k : ℤ)] γ = f := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hcov, zpow_neg, zpow_natCast]
    have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    field_simp
  { toFun := f
    slash_action_eq' := fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      exact hinv γ
    holo' := hmd
    bdd_at_cusps' := fun {c} hc => by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
      intro γ _
      rw [hinv γ]
      exact hbd }

/--
@isnad1 id=eq.3h3v.s10.5d9455a0e51d from=translated src=- shape=13f605c3 vocab=8737bcea
-/
@[scoped simp] theorem mkLevelOne_apply (k : ℕ) (f : ℍ → ℂ) (hcov) (hmd) (hbd) (τ : ℍ) :
    mkLevelOne k f hcov hmd hbd τ = f τ := rfl

/--
@isnad1 id=eq.6h4v.s10.dbda08c02ca0 from=translated src=- shape=10ab61f0 vocab=4b4feff6
-/
theorem coeff_eq_zero_of_covariant (k : ℕ) (hk : (k : ℤ) < 12) {a : ℕ → ℂ} {f : ℍ → ℂ}
    (hf : IsQS a f) (ha0 : a 0 = 0) (hmd : MDiff f) (hbd : IsBoundedAtImInfty f)
    (hcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * f τ)
    (n : ℕ) : a n = 0 := by
  set F : ModularForm 𝒮ℒ (k : ℤ) := mkLevelOne k f hcov hmd hbd with hFdef
  have hFq : ∀ m, a m = coeff m (qExpansion 1 ⇑F) := fun m =>
    ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL (f := F)
      (fun τ => by simpa only [smul_eq_mul, hFdef, mkLevelOne_apply] using hf τ) m
  have h0 : coeff 0 (qExpansion 1 ⇑F) = 0 := (hFq 0).symm.trans ha0
  have hG : F.toCuspForm h0 = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  have hf0 : ∀ τ, f τ = 0 := fun τ => by
    have := congrArg (fun G : CuspForm 𝒮ℒ (k : ℤ) => G τ) hG
    simpa [ModularForm.toCuspForm_apply, hFdef, mkLevelOne_apply] using this
  exact hf.unique hf0 n

def cauchy (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

/--
@isnad1 id=mdiffere.0h0v.s8.9146da90ad2a from=translated src=- shape=d88b448d vocab=1f53e3ef
-/
theorem mdiff_E4 : MDiff (⇑ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.holo _
/--
@isnad1 id=mdiffere.0h0v.s8.0f3cc9b3ce1a from=translated src=- shape=d88b448d vocab=c2bf97e9
-/
theorem mdiff_E6 : MDiff (⇑ModularForm.E₆ : ℍ → ℂ) := ModularFormClass.holo _
/--
@isnad1 id=mdiffere.0h0v.s6.245dfa6e1ec1 from=translated src=- shape=6f732746 vocab=c3e7c3c4
-/
theorem mdiff_D_E2 : MDiff (D E2) := normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable
/--
@isnad1 id=mdiffere.0h0v.s8.9da325ae2231 from=translated src=- shape=e97a031b vocab=84567967
-/
theorem mdiff_D_E4 : MDiff (D ⇑ModularForm.E₄) := normalizedDerivOfComplex_mdifferentiable mdiff_E4
/--
@isnad1 id=mdiffere.0h0v.s8.3f9eb80af6c2 from=translated src=- shape=e97a031b vocab=052aff39
-/
theorem mdiff_D_E6 : MDiff (D ⇑ModularForm.E₆) := normalizedDerivOfComplex_mdifferentiable mdiff_E6

/--
@isnad1 id=isbounde.0h0v.s2.f2f622059302 from=translated src=- shape=25b03439 vocab=14540859
-/
theorem bdd_E2 : IsBoundedAtImInfty E2 := isQS_E2.isBoundedAtImInfty polyGrowth_e2c
/--
@isnad1 id=isbounde.0h0v.s8.ba5c870723b7 from=translated src=- shape=451f6dce vocab=9ed8efa7
-/
theorem bdd_E4 : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) :=
  isQS_E4.isBoundedAtImInfty polyGrowth_e4c
/--
@isnad1 id=isbounde.0h0v.s8.ee37328687c0 from=translated src=- shape=451f6dce vocab=29fcb9d0
-/
theorem bdd_E6 : IsBoundedAtImInfty (⇑ModularForm.E₆ : ℍ → ℂ) :=
  isQS_E6.isBoundedAtImInfty polyGrowth_e6c
/--
@isnad1 id=isbounde.0h0v.s2.50a04cfe05b8 from=translated src=- shape=0072ad64 vocab=2b52e0d3
-/
theorem bdd_D_E2 : IsBoundedAtImInfty (D E2) :=
  (isQS_E2.theta polyGrowth_e2c).isBoundedAtImInfty polyGrowth_e2c.theta
/--
@isnad1 id=isbounde.0h0v.s8.911777ab842a from=translated src=- shape=7cbb4e04 vocab=0d31ff80
-/
theorem bdd_D_E4 : IsBoundedAtImInfty (D ⇑ModularForm.E₄) :=
  (isQS_E4.theta polyGrowth_e4c).isBoundedAtImInfty polyGrowth_e4c.theta
/--
@isnad1 id=isbounde.0h0v.s8.60a950cb3f84 from=translated src=- shape=7cbb4e04 vocab=3cd97184
-/
theorem bdd_D_E6 : IsBoundedAtImInfty (D ⇑ModularForm.E₆) :=
  (isQS_E6.theta polyGrowth_e6c).isBoundedAtImInfty polyGrowth_e6c.theta

/--
@isnad1 id=eq.0h1v.s5.e258ff2418ce from=translated src=- shape=b784c189 vocab=7041b0ef
-/
theorem identity_A (n : ℕ) : 12 * ((n : ℂ) * e2c n) - (cauchy e2c e2c n - e4c n) = 0 := by
  refine coeff_eq_zero_of_covariant 4 (by norm_num)
    (a := fun n => 12 * ((n : ℂ) * e2c n) - (cauchy e2c e2c n - e4c n)) (f := A4) ?_ ?_ ?_ ?_
    A4_apply_smul n
  · intro τ
    have h := (((isQS_E2.theta polyGrowth_e2c).const_mul 12).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e2c isQS_E2).sub isQS_E4)) τ
    have e : A4 τ = 12 * D E2 τ - (E2 τ * E2 τ - ModularForm.E₄ τ) := by rw [A4_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c]
  · exact ((mdiff_D_E2.const_smul (12 : ℂ)).sub (E2_mdifferentiable.mul E2_mdifferentiable)).add
      mdiff_E4
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (12 : ℂ) bdd_D_E2)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E2))) bdd_E4

/--
@isnad1 id=eq.0h1v.s5.4dd497e68233 from=translated src=- shape=4b037577 vocab=d1d972a5
-/
theorem identity_B (n : ℕ) : 3 * ((n : ℂ) * e4c n) - (cauchy e2c e4c n - e6c n) = 0 := by
  refine coeff_eq_zero_of_covariant 6 (by norm_num)
    (a := fun n => 3 * ((n : ℂ) * e4c n) - (cauchy e2c e4c n - e6c n)) (f := B6) ?_ ?_ ?_ ?_
    B6_apply_smul n
  · intro τ
    have h := (((isQS_E4.theta polyGrowth_e4c).const_mul 3).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e4c isQS_E4).sub isQS_E6)) τ
    have e : B6 τ = 3 * D ⇑ModularForm.E₄ τ - (E2 τ * ModularForm.E₄ τ - ModularForm.E₆ τ) := by
      rw [B6_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c, e6c]
  · exact ((mdiff_D_E4.const_smul (3 : ℂ)).sub (E2_mdifferentiable.mul mdiff_E4)).add mdiff_E6
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (3 : ℂ) bdd_D_E4)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E4))) bdd_E6

/--
@isnad1 id=eq.0h1v.s5.4ef3c8d2ce45 from=translated src=- shape=8e355970 vocab=d1d972a5
-/
theorem identity_C (n : ℕ) :
    2 * ((n : ℂ) * e6c n) - (cauchy e2c e6c n - cauchy e4c e4c n) = 0 := by
  refine coeff_eq_zero_of_covariant 8 (by norm_num)
    (a := fun n => 2 * ((n : ℂ) * e6c n) - (cauchy e2c e6c n - cauchy e4c e4c n)) (f := C8)
    ?_ ?_ ?_ ?_ C8_apply_smul n
  · intro τ
    have h := (((isQS_E6.theta polyGrowth_e6c).const_mul 2).sub
      ((isQS_E2.mul polyGrowth_e2c polyGrowth_e6c isQS_E6).sub
        (isQS_E4.mul polyGrowth_e4c polyGrowth_e4c isQS_E4))) τ
    have e : C8 τ = 2 * D ⇑ModularForm.E₆ τ -
        (E2 τ * ModularForm.E₆ τ - ModularForm.E₄ τ * ModularForm.E₄ τ) := by
      rw [C8_apply]; ring
    rw [e]; exact h
  · simp [cauchy, e2c, e4c, e6c]
  · exact ((mdiff_D_E6.const_smul (2 : ℂ)).sub (E2_mdifferentiable.mul mdiff_E6)).add
      (mdiff_E4.mul mdiff_E4)
  · exact Filter.BoundedAtFilter.add (Filter.BoundedAtFilter.add
      (Filter.BoundedAtFilter.smul (2 : ℂ) bdd_D_E6)
      (Filter.BoundedAtFilter.neg (Filter.BoundedAtFilter.mul bdd_E2 bdd_E6)))
      (Filter.BoundedAtFilter.mul bdd_E4 bdd_E4)

/--
@isnad1 id=eq.0h2v.s8.f4eded8acb83 from=translated src=- shape=2c822b26 vocab=096a998f
-/
theorem coeff_X_mul_derivative (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * derivative ℤ φ) = (n : ℤ) * coeff n φ := by
  cases n with
  | zero => simp [coeff_zero_X_mul]
  | succ m => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/--
@isnad1 id=eq.0h3v.s7.4258abe8fde4 from=translated src=- shape=46034deb vocab=899f8197
-/
theorem coeff_ofNat_mul (c : ℕ) [c.AtLeastTwo] (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n ((OfNat.ofNat c : PowerSeries ℤ) * φ) = (OfNat.ofNat c : ℤ) * coeff n φ := by
  rw [show (OfNat.ofNat c : PowerSeries ℤ) = C (OfNat.ofNat c : ℤ) from by simp, coeff_C_mul]

/--
@isnad1 id=eq.0h3v.s8.b92ce21846d1 from=translated src=- shape=159f6324 vocab=0aa553f6
-/
theorem cast_coeff_mul (φ ψ : PowerSeries ℤ) (n : ℕ) :
    ((coeff n (φ * ψ) : ℤ) : ℂ) =
      cauchy (fun m => ((coeff m φ : ℤ) : ℂ)) (fun m => ((coeff m ψ : ℤ) : ℂ)) n := by
  rw [PowerSeries.coeff_mul, cauchy]; push_cast; rfl

/--
@isnad1 id=eq.0h1v.s7.d558ab7b8297 from=translated src=- shape=baf2ada1 vocab=3140eca4
-/
theorem cast_coeff_P (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)) : ℤ) :
      ℂ) = e2c n := by
  rw [coeff_mk, e2c, ArithmeticFunction.sigma_one_apply]
  split_ifs <;> push_cast <;> ring

/--
@isnad1 id=eq.0h1v.s7.14cfa62e1700 from=translated src=- shape=89d317c0 vocab=7415a45f
-/
theorem cast_coeff_Q (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3) :
      ℤ) : ℂ) = e4c n := by
  rw [coeff_mk, e4c, ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

/--
@isnad1 id=eq.0h1v.s7.14e8a2c01519 from=translated src=- shape=249ca2a0 vocab=35097e4a
-/
theorem cast_coeff_R (n : ℕ) :
    ((coeff n (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
      ℤ) : ℂ) = e6c n := by
  rw [coeff_mk, e6c, ArithmeticFunction.sigma_apply]
  split_ifs <;> push_cast <;> ring

end EisensteinSeries.RamanujanSystemInt
open scoped _root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries _root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt
open scoped _root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries

end
open scoped _root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries _root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.EisensteinSeries.RamanujanSystemInt

open EisensteinSeries.RamanujanSystemInt PowerSeries in

/--
@isnad1 id=and.3h3v.s9.79a8e20d1550 from=translated src=- shape=bd1f6a76 vocab=89824294
-/
theorem solution
    (P Q R : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))
    (hQ : Q = PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)
    (hR : R = PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
    12 * (PowerSeries.X * PowerSeries.derivative ℤ P) = P ^ 2 - Q ∧
      3 * (PowerSeries.X * PowerSeries.derivative ℤ Q) = P * Q - R ∧
        2 * (PowerSeries.X * PowerSeries.derivative ℤ R) = P * R - Q ^ 2 := by
  have hPc : ∀ n, ((coeff n P : ℤ) : ℂ) = e2c n := fun n => hP ▸ cast_coeff_P n
  have hQc : ∀ n, ((coeff n Q : ℤ) : ℂ) = e4c n := fun n => hQ ▸ cast_coeff_Q n
  have hRc : ∀ n, ((coeff n R : ℤ) : ℂ) = e6c n := fun n => hR ▸ cast_coeff_R n
  have hPf : (fun n => ((coeff n P : ℤ) : ℂ)) = e2c := funext hPc
  have hQf : (fun n => ((coeff n Q : ℤ) : ℂ)) = e4c := funext hQc
  have hRf : (fun n => ((coeff n R : ℤ) : ℂ)) = e6c := funext hRc
  refine ⟨?_, ?_, ?_⟩
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, sq, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, hPf, hPc, hQc]
    push_cast
    linear_combination identity_A n
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, hPf, hQf, hQc, hRc]
    push_cast
    linear_combination identity_B n
  · refine PowerSeries.ext fun n => Int.cast_injective (α := ℂ) ?_
    rw [coeff_ofNat_mul, coeff_X_mul_derivative, map_sub, sq, Int.cast_mul, Int.cast_mul,
      Int.cast_sub, cast_coeff_mul, cast_coeff_mul, hPf, hQf, hRf, hRc]
    push_cast
    linear_combination identity_C n
