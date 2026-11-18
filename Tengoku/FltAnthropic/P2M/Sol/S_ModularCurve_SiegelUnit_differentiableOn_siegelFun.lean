import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction
import Tengoku.FltAnthropic.Theorems.Thm_jacobiTheta_two_eq_tprod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun

set_option autoImplicit false

noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped Manifold
open scoped Real MatrixGroups

namespace E97cSHol

def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

/--
@isnad1 id=eq.0h4v.s5.d91fe9073790 from=translated src=- shape=6b4addea vocab=a9b0a9ff
-/
theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

/--
@isnad1 id=eq.0h3v.s4.152aee1f1c10 from=translated src=- shape=e59f7ef4 vocab=51dfd744
-/
theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

/--
@isnad1 id=lt.1h1v.s4.1c539d532580 from=translated src=- shape=57faaa14 vocab=dc089444
-/
theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

def P (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - qq τ ^ (n + 1))

/--
@isnad1 id=multipli.1h1v.s6.d13bc0407b10 from=translated src=- shape=1c50effb vocab=8c9ef8df
-/
theorem multipliable_P {τ : ℂ} (hτ : 0 < τ.im) : Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow (norm_qq_lt_one hτ)

/--
@isnad1 id=multipli.1h3v.s6.0f0a42d99f48 from=translated src=- shape=5e5b2675 vocab=b137e65d
-/
theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/--
@isnad1 id=multipli.1h4v.s6.3e459d52e644 from=translated src=- shape=966906a6 vocab=9a1191e0
-/
theorem multipliable_b {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ n * qa N r s τ := by
  simpa using multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 0

/--
@isnad1 id=multipli.1h4v.s6.430a4ea77aef from=translated src=- shape=4e97db60 vocab=8c729807
-/
theorem multipliable_b_succ {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * qa N r s τ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 1

/--
@isnad1 id=multipli.1h4v.s6.7f6fae7a1db5 from=translated src=- shape=81213acc vocab=1a49fcab
-/
theorem multipliable_c {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ)⁻¹ 1

def w (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + (1 - τ) / 2

/--
@isnad1 id=eq.1h5v.s8.de89acab0af8 from=translated src=- shape=5c412ca3 vocab=dfd3b974
-/
theorem jtp_term (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) (n : ℕ) :
    (1 - cexp (2 * π * I * (n + 1) * τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ)) =
      (1 - qq τ ^ (n + 1)) * ((1 - qq τ ^ n * qa N r s τ) *
        (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : cexp (2 * π * I * (n + 1) * τ) = qq τ ^ (n + 1) := by
    rw [show 2 * π * I * (n + 1) * τ = ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) by push_cast; ring,
      Complex.exp_nat_mul, qq]
  have e2 : cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ) = -(qq τ ^ n * qa N r s τ) := by
    have : π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ =
        (n : ℂ) * (2 * π * I * τ) + 2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + π * I := by
      unfold w; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, qq, qa]
    ring
  have e3 : cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ) =
      -(qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := by
    have : π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ =
        ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) + -(2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ)) +
          -(π * I) := by
      unfold w; push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_neg, Complex.exp_pi_mul_I, qq, qa]
    ring
  rw [e1, e2, e3]; ring

/--
@isnad1 id=eq.2h4v.s5.633e7c4751da from=translated src=- shape=eadda7a1 vocab=541423a2
-/
theorem theta_eq (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (w N r s τ) τ = P τ * sprod N r s τ := by
  rw [jacobiTheta_two_eq_tprod _ _ hτ, tprod_congr (jtp_term N hN r s τ)]
  have hP := multipliable_P hτ
  have hb := multipliable_b hτ N r s
  have hb1 := multipliable_b_succ hτ N r s
  have hc := multipliable_c hτ N r s
  have hbc : Multipliable fun n : ℕ => (1 - qq τ ^ n * qa N r s τ) *
      (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := (hb.hasProd.mul hc.hasProd).multipliable
  have h3 : ∏' n : ℕ, (1 - qq τ ^ n * qa N r s τ) =
      (1 - qq τ ^ 0 * qa N r s τ) * ∏' n : ℕ, (1 - qq τ ^ (n + 1) * qa N r s τ) :=
    tprod_eq_zero_mul' hb1
  rw [hP.tprod_mul hbc, hb.tprod_mul hc, h3, pow_zero, one_mul, mul_assoc, ← hb1.tprod_mul hc]
  simp only [P, sprod]

/--
@isnad1 id=eq.0h2v.s6.912eee1c61a2 from=translated src=- shape=8103178f vocab=41ee74ac
-/
theorem one_sub_eta_q (n : ℕ) (τ : ℂ) : 1 - ModularForm.eta_q n τ = 1 - qq τ ^ (n + 1) := by
  simp only [ModularForm.eta_q, Function.Periodic.qParam, qq]
  congr 3
  push_cast
  ring

/--
@isnad1 id=ne.1h1v.s4.49560ae43ea4 from=translated src=- shape=555d9df8 vocab=f7686e4f
-/
theorem P_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : P τ ≠ 0 := by
  have h := ModularForm.eta_tprod_ne_zero (z := τ) hτ
  rwa [tprod_congr (fun n => one_sub_eta_q n τ)] at h

/--
@isnad1 id=differen.0h3v.s6.d701ad31b5c6 from=translated src=- shape=bd6aa1dd vocab=2a15c139
-/
theorem differentiable_w (N : ℕ) (r s : ℤ) : Differentiable ℂ (w N r s) := by
  unfold w; fun_prop

/--
@isnad1 id=differen.0h3v.s6.e902d5fbd259 from=translated src=- shape=bd6aa1dd vocab=d7cb6f7c
-/
theorem differentiable_pref (N : ℕ) (r s : ℤ) : Differentiable ℂ (pref N r s) := by
  unfold pref; fun_prop

/--
@isnad1 id=differen.1h4v.s6.a536a66117fe from=translated src=- shape=34214ff9 vocab=f8acb45a
-/
theorem differentiableAt_theta_w (N : ℕ) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun z => jacobiTheta₂ (w N r s z) z) τ := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (w N r s τ, τ) :=
    (hasFDerivAt_jacobiTheta₂ (w N r s τ) hτ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z => (w N r s z, z)) τ :=
    ((differentiable_w N r s) τ).prodMk differentiableAt_id
  have h3 : DifferentiableAt ℂ ((fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) ∘ (fun z => (w N r s z, z))) τ :=
    DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f := fun z => (w N r s z, z)) τ h1 h2
  exact h3

/--
@isnad1 id=differen.1h1v.s6.9b02510e9470 from=translated src=- shape=f4fff64d vocab=9484b7ce
-/
theorem differentiableAt_P {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ P τ := by
  have h := ModularForm.differentiableAt_eta_tprod (z := τ) hτ
  have hfun : (fun x => ∏' n, (1 - ModularForm.eta_q n x)) = P := by
    funext x
    exact tprod_congr (fun n => one_sub_eta_q n x)
  rwa [hfun] at h

/--
@isnad1 id=eq.2h4v.s6.9c67741a03eb from=translated src=- shape=0e06f07a vocab=9c15782d
-/
theorem siegelFun_eq_theta (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * (jacobiTheta₂ (w N r s τ) τ / P τ) := by
  rw [siegelFun_eq, theta_eq N hN r s hτ, mul_div_cancel_left₀ _ (P_ne_zero hτ)]

/--
@isnad1 id=differen.0h3v.s6.4056058fd9e7 from=translated src=- shape=a989ef13 vocab=cfdc1730
-/
theorem differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) {z : ℂ | 0 < z.im} := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [siegelFun_level_zero]
    exact differentiableOn_const 0
  · have h : DifferentiableOn ℂ (fun z => pref N r s z * (jacobiTheta₂ (w N r s z) z / P z)) {z : ℂ | 0 < z.im} :=
      fun z hz => (((differentiable_pref N r s) z).mul
        ((differentiableAt_theta_w N r s hz).div (differentiableAt_P hz) (P_ne_zero hz))).differentiableWithinAt
    exact h.congr fun z hz => siegelFun_eq_theta N hN r s hz

/--
@isnad1 id=mdiffere.0h3v.s6.eb923c4feb1b from=translated src=- shape=901e2339 vocab=460daacc
-/
theorem mdifferentiable_siegelFun (N : ℕ) (r s : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => ModularCurve.siegelFun N r s (τ : ℂ)) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hd : DifferentiableAt ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) (τ : ℂ) :=
    (differentiableOn_siegelFun N r s).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp only [Function.comp_apply, id_eq] at hz
  simp only [Function.comp_apply, hz]

end E97cSHol

open scoped Manifold in
open ModularCurve in
/--
@isnad1 id=and.0h3v.s7.6501dbd4320d from=translated src=- shape=d5429169 vocab=7a5cbed3
-/
theorem solution (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) :=
  ⟨E97cSHol.differentiableOn_siegelFun N r s, E97cSHol.mdifferentiable_siegelFun N r s⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
