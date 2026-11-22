/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.SpherePackingOrig.SpherePacking.ForMathlib.AtImInfty
import Tengoku.LeanPool.LeanPool.LeanModularForms.Modularforms.SlashActionAuxil
import Tengoku.Seed.NumberTheory.ModularForms.QExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # ResToImagAxis -/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup Filter Asymptotics

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def _root_.Tengoku.LeanPool.ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t => if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ := ResToImagAxis F

/--
@isnad1 id=eq.0h1v.s3.b49013cb37a0 from=translated src=- shape=4eb8c70f vocab=005f6f28
-/
@[simp] lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

/--
@isnad1 id=eq.0h2v.s3.bb3c535fd7b5 from=translated src=- shape=75d3678e vocab=005f6f28
-/
@[simp] lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[fun_prop]
noncomputable def Tengoku.LeanPool.ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[fun_prop]
noncomputable def Tengoku.LeanPool.ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[fun_prop]
noncomputable def Tengoku.LeanPool.ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

/--
@isnad1 id=differen.2h2v.s7.a3e1f3838507 from=translated src=- shape=268c82c5 vocab=0882a626
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDiff F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have hcdiff := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at hcdiff
  have h_diff :
      DifferentiableAt ℝ (fun t : ℝ => F (ofComplex (Complex.I * t))) t := by
    have : IsScalarTower ℝ ℂ ℂ := IsScalarTower.complexToReal
    have := hcdiff.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _
    exact this
  apply h_diff.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

/--
Restriction and slash action under S: $(F |_k S) (it) = (it)^{-k} * F(it)$
@isnad1 id=eq.1h3v.s7.3298c258926d from=translated src=- shape=13d7c76d vocab=fdbac47f
-/
theorem Tengoku.LeanPool.ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' :=
    UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  simpa [ResToImagAxis, ht, hz'def] using (by
    rw [modular_slash_S_apply, h]; simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')] :
    (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z')

/--
Realness, positivity and essential positivity are closed under the addition and multiplication.
@isnad1 id=real.0h1v.s2.d1d73f4fbc01 from=translated src=- shape=b52b80f4 vocab=ce04f404
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ => c) := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, ofReal_im]

/--
@isnad1 id=real.0h0v.s3.8b1480bc9841 from=translated src=- shape=73724039 vocab=0883ab22
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ => 0) := ResToImagAxis.Real.const 0

/--
@isnad1 id=real.0h0v.s3.bd7212182541 from=translated src=- shape=73724039 vocab=0883ab22
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ => 1) := ResToImagAxis.Real.const 1

/--
@isnad1 id=real.1h1v.s4.97c1918ced80 from=translated src=- shape=f5caf165 vocab=196e1581
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) : ResToImagAxis.Real (-F)
    := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/--
@isnad1 id=real.2h2v.s5.90d634ca753c from=translated src=- shape=767eb5d9 vocab=0be59303
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht; have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/--
@isnad1 id=real.2h2v.s5.402eeb6f0d71 from=translated src=- shape=767eb5d9 vocab=f201d9d0
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF hG.neg

/--
@isnad1 id=real.2h2v.s5.38b5896244ba from=translated src=- shape=767eb5d9 vocab=7ecbcbcc
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht; have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/--
@isnad1 id=real.1h2v.s6.8029cb5f6b5f from=translated src=- shape=b8187976 vocab=9426085f
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/--
@isnad1 id=real.1h2v.s5.f8d9b75515cd from=translated src=- shape=200be179 vocab=f6f72a13
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (n : ℕ) :
    ResToImagAxis.Real (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Real.one
  | succ n hn => exact hn.mul hF

/--
@isnad1 id=pos.1h1v.s4.450e865ecae0 from=translated src=- shape=494aa614 vocab=3f70337c
-/
theorem Tengoku.LeanPool.ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ => c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ResToImagAxis, ht, hc]⟩

/--
@isnad1 id=pos.0h0v.s3.af3965650100 from=translated src=- shape=73724039 vocab=2dc59fad
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ => 1) :=
  ResToImagAxis.Pos.const 1 one_pos

/--
@isnad1 id=pos.2h2v.s5.b19f6a225070 from=translated src=- shape=767eb5d9 vocab=65b0eeda
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  rw [Pos]; refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht; have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, add_pos hFpos hGpos]

/--
@isnad1 id=pos.2h2v.s5.31dfd73f7b89 from=translated src=- shape=767eb5d9 vocab=df7ee124
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  rw [Pos]; refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht; have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht; have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal hFpos hGpos
  simp [ResToImagAxis, ht, hFreal, hGreal, mul_pos hFpos hGpos]

/--
@isnad1 id=pos.2h2v.s6.a1acd9208a9a from=translated src=- shape=88b7e112 vocab=4d322483
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  rw [Pos]; refine ⟨Real.smul hF.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht; have hFpos := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hFpos
  simp [ResToImagAxis, ht, mul_pos hc hFpos]

/--
@isnad1 id=pos.1h2v.s5.41db0e0f60ce from=translated src=- shape=200be179 vocab=c91e40a6
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.Pos.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (n : ℕ) :
    ResToImagAxis.Pos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Pos.one
  | succ n hn => exact hn.mul hF

/--
@isnad1 id=eventual.1h1v.s3.55fecbd3c240 from=translated src=- shape=cdb3b71b vocab=26a7484e
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.from_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) :
    ResToImagAxis.EventuallyPos F :=
  ⟨hF.1, 1, one_pos, fun t ht ↦ hF.2 t (by linarith)⟩

/--
@isnad1 id=eventual.0h0v.s3.27c81e984f7f from=translated src=- shape=73724039 vocab=924efb49
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.one :
    ResToImagAxis.EventuallyPos (fun _ => 1) :=
  ResToImagAxis.EventuallyPos.from_pos ResToImagAxis.Pos.one

/--
@isnad1 id=eventual.1h1v.s4.bdc02bbb7a24 from=translated src=- shape=494aa614 vocab=b770d2ec
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.const (c : ℝ) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun _ => c) :=
  ResToImagAxis.EventuallyPos.from_pos (ResToImagAxis.Pos.const c hc)

/--
@isnad1 id=eventual.2h2v.s5.82c8a52f4dbe from=translated src=- shape=767eb5d9 vocab=a10c3a8f
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  rw [EventuallyPos]; refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2; obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have hFpos_t := hFpos t ((le_max_left ..).trans ht)
  have hGpos_t := hGpos t ((le_max_right ..).trans ht)
  have htpos : 0 < t := by grind
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos]
  exact add_pos hFpos_t hGpos_t

/--
@isnad1 id=eventual.2h2v.s5.9034d9294aa7 from=translated src=- shape=767eb5d9 vocab=0ca1212b
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  rw [EventuallyPos]; refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2; obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos; have hGreal_t := hG.1 t htpos
  have hFpos_t := hFpos t ((le_max_left ..).trans ht)
  have hGpos_t := hGpos t ((le_max_right ..).trans ht)
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hGreal_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, Pi.mul_apply,
    mul_re, hFreal_t, hGreal_t, mul_zero, sub_zero]
  exact mul_pos hFpos_t hGpos_t

/--
@isnad1 id=eventual.1h2v.s5.d404f638436e from=translated src=- shape=200be179 vocab=5d85313e
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

/--
@isnad1 id=eventual.2h2v.s6.cf17102472ad from=translated src=- shape=88b7e112 vocab=604daf05
-/
@[fun_prop]
theorem Tengoku.LeanPool.ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  rw [EventuallyPos]; refine ⟨ResToImagAxis.Real.smul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2; refine ⟨t₀, hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := by grind
  have hFreal_t := hF.1 t htpos; have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hFpos_t
  simp [ResToImagAxis, htpos, mul_pos hc hFpos_t]

/-- If `F` is real-valued, then `F` is equal to the real part of itself on imaginary axis. -/
theorem Tengoku.LeanPool.ResToImagAxis.Real.eq_real_part {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (t : ℝ) :
    F.resToImagAxis t = (F.resToImagAxis t).re := by
  simp only [Function.resToImagAxis, ResToImagAxis]
  split_ifs with ht
  exacts [Complex.ext rfl (by simpa [Function.resToImagAxis, ResToImagAxis, ht]
    using (hF t ht)), rfl]

/-!
## Polynomial decay of functions with exponential bounds

This section establishes that if a function `F : ℍ → ℂ` is `O(exp(-c * im τ))` at infinity,
then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

One application is to cusp forms, which satisfy such exponential decay bounds.
-/

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
the restriction to the imaginary axis `t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
@isnad1 id=isbigo.2h2v.s6.41f8cafd2f45 from=translated src=- shape=df11b42f vocab=aa4c4d27
-/
lemma _root_.Tengoku.LeanPool.isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ} (_hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t => Real.exp (-c * t) := by
  rw [Asymptotics.isBigO_iff] at hF ⊢
  obtain ⟨C, hC⟩ := hF; use C
  rw [Filter.eventually_atImInfty] at hC; obtain ⟨A, hA⟩ := hC
  filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have him : z.im = t := by change (Complex.I * t).im = t; simp
  simpa [him] using hA z (by simpa [him] using le_of_max_le_left ht)

/--
The analytic kernel: if `g : ℝ → ℂ` is eventually bounded by `C * exp(-b * t)` for some
`b > 0`, then `t^s * g(t) → 0` as `t → ∞` for any real power `s`.

This follows from the fact that `t^s * exp(-b * t) → 0` (mathlib's
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`) combined with the big-O transfer lemma.
@isnad1 id=tendsto.2h3v.s6.d2d1cd4a80f0 from=translated src=- shape=f6b71ebf vocab=69c3a4c3
-/
lemma _root_.Tengoku.LeanPool.tendsto_rpow_mul_of_isBigO_exp {g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b)
    (hg : g =O[atTop] fun t => rexp (-b * t)) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0) := by
  refine ((isBigO_refl _ _).mul (Complex.isBigO_ofReal_right.mpr hg)).trans_tendsto ?_
  refine (tendsto_ofReal_iff.mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
@isnad1 id=tendsto.2h3v.s6.1e9e2ef729be from=translated src=- shape=afeed482 vocab=4bf36b6e
-/
theorem _root_.Tengoku.LeanPool.tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hc hF)

/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
@isnad1 id=tendsto.0h5v.s7.b07ad9193135 from=translated src=- shape=113de58b vocab=b71584cb
-/
theorem _root_.Tengoku.LeanPool.cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa only [strictPeriods_Gamma] using AddSubgroup.mem_zmultiples (n : ℝ)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ => rexp (-(2 * π / n) * τ.im) := by
    convert CuspFormClass.exp_decay_atImInfty hn_pos hmem (f := f) using 2 with τ; field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s

/-!
## Fourier expansion approach for polynomial decay

This section provides an alternative approach to polynomial decay that works directly from
Fourier expansions. If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`, which gives `t^s * F(it) → 0`.

This is useful for functions with q-expansions starting at a positive index (like `(E₂E₄ - E₆)²`).
-/

/--
If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
and the coefficients are absolutely summable at height `im z = c`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`.

The key bound is: for `im z ≥ c`,
  `‖F(z)‖ ≤ (∑_m ‖a_m‖ · exp(-2π c m)) · exp(-2π n₀ · im z)`
@isnad1 id=isbigo.4h4v.s7.7eccf7173c59 from=translated src=- shape=38597bc0 vocab=5b39ca27
-/
lemma _root_.Tengoku.LeanPool.isBigO_atImInfty_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (_hn₀ : 0 < n₀) (_hc : 0 < c)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    F =O[atImInfty] fun z : ℍ => rexp (-(2 * π * (n₀ : ℝ)) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' m, ‖a m‖ * rexp (-(2 * π * c) * m), ?_⟩
  rw [Filter.eventually_atImInfty]
  refine ⟨c, fun z hz => ?_⟩
  rw [hF z, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  -- Real part of 2πi(m+n₀)z is -2π(m+n₀)·im z
  have hexp_re m : (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z).re = -(2 * π) * (m + n₀) * z.im := by
    simp only [Nat.cast_add, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, add_re, natCast_re,
      add_im, natCast_im, coe_re, zero_add, coe_im, zero_sub, neg_mul]
  -- Key bound: for y ≥ c, exp(-(2π)(m+n₀)y) ≤ exp(-(2πc)m) * exp(-(2πc)n₀)
  have hexp_bound (m : ℕ) :
      rexp (-(2 * π) * (↑m + ↑n₀) * z.im) ≤
        rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have _ : (↑m + ↑n₀) * z.im ≥ (↑m + ↑n₀) * c := by nlinarith
    nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀), z.im_pos]
  -- Summability of norms
  have hsum_norms : Summable fun m => ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (ha.mul_right (rexp (-(2 * π * c) * n₀)))
    simp only [norm_mul, norm_exp, hexp_re]
    calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
        ≤ ‖a m‖ * (rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀)) :=
          mul_le_mul_of_nonneg_left (hexp_bound m) (norm_nonneg _)
      _ = ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by ring
  have hsum_norms' : Summable fun m => ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
    convert hsum_norms with m; rw [norm_mul, norm_exp, hexp_re]
  -- Main calculation
  calc ‖∑' m, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖
      ≤ ∑' m, ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_norms
    _ = ∑' m, ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
        simp only [norm_mul, norm_exp, hexp_re]
    _ ≤ ∑' m, ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hsum_norms'
          (ha.mul_right (rexp (-(2 * π) * n₀ * z.im)))
        have hsplit : rexp (-(2 * π) * (↑m + ↑n₀) * z.im) =
            rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
          rw [← Real.exp_add]; ring_nf
        have hexp_m : rexp (-(2 * π) * m * z.im) ≤ rexp (-(2 * π * c) * m) := by
          rw [Real.exp_le_exp]
          have key : (m : ℝ) * z.im ≥ m * c := by nlinarith
          nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), z.im_pos]
        calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
            = ‖a m‖ * rexp (-(2 * π) * m * z.im) * rexp (-(2 * π) * n₀ * z.im) := by
              rw [hsplit]; ring
          _ ≤ ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
              exact mul_le_mul_of_nonneg_left hexp_m (norm_nonneg _)
    _ = (∑' m, ‖a m‖ * rexp (-(2 * π * c) * m)) * rexp (-(2 * π) * n₀ * z.im) := tsum_mul_right
    _ = _ := by ring_nf

/--
If `F` has a Fourier expansion starting at index `n₀ > 0` with absolutely summable coefficients
at height `c > 0`, then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

This converts a Fourier expansion representation directly into polynomial decay on the
imaginary axis.
@isnad1 id=tendsto.4h5v.s7.f0a9b3f64e42 from=translated src=- shape=fcee6b39 vocab=7c220bd7
-/
theorem _root_.Tengoku.LeanPool.tendsto_rpow_mul_resToImagAxis_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (hn₀ : 0 < n₀) (hc : 0 < c)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * Complex.exp (2 * π * Complex.I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) (s : ℝ) :
    Tendsto (fun t : ℝ => t ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity)
    (isBigO_atImInfty_of_fourier_shift hn₀ hc hF ha) s

/-- Extract the imaginary part condition at a specific point from `ResToImagAxis.Real`.
@isnad1 id=eq.3h3v.s5.22de042a8154 from=translated src=- shape=044125f0 vocab=ee92b944
-/
lemma Tengoku.LeanPool.ResToImagAxis.Real.im_eq_zero_at {F : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    (F z).im = 0 := by subst hz; simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF t ht

/-- Extract the positivity condition at a specific point from `ResToImagAxis.Pos`.
@isnad1 id=lt.3h3v.s5.54977b9f1c1a from=translated src=- shape=56353add vocab=41b2515f
-/
lemma Tengoku.LeanPool.ResToImagAxis.Pos.re_pos_at {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    0 < (F z).re := by subst hz; simpa [Function.resToImagAxis, ResToImagAxis, ht] using hF.2 t ht

/-- Tendsto conversion: if F tends to c at atImInfty, then F.resToImagAxis tends to c at atTop.
@isnad1 id=tendsto.1h2v.s5.de19c4236b95 from=translated src=- shape=e3090b0a vocab=47b5b138
-/
lemma _root_.Tengoku.LeanPool.tendsto_resToImagAxis_of_tendsto_atImInfty {F : ℍ → ℂ} {c : ℂ}
    (hF : Tendsto F atImInfty (nhds c)) :
    Tendsto F.resToImagAxis atTop (nhds c) := by
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨A, hA⟩ := Filter.eventually_atImInfty.mp (Metric.tendsto_nhds.mp hF ε hε)
  refine ⟨max A 1, fun t ht ↦ ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right ht)
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  simp_all
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
