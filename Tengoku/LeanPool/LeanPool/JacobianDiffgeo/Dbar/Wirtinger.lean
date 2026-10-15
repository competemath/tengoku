/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku

/-!
# Wirtinger derivatives and the Cauchy–Riemann bridge

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.1). Mathlib-only planar file: no
project imports, no manifold variables, so downstream planar consumers (`planar-stokes-atoms`,
`residue-calculus`, `monodromy`, ...) can import it without dragging in the manifold stack (D10).

* `wirtingerD`, `wirtingerDbar` : the Wick/Wirtinger derivatives of a function `ℂ → ℂ`, defined as
  plain (junk-tolerant) functions via `fderiv ℝ`.
* `fderiv_apply_eq_wirtinger` : the workhorse decomposition of the real differential on the basis
  `{1, I}`.
* The Cauchy–Riemann bridge: `DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ wirtingerDbar f z =
0`
  (hand-built; mathlib has no `Analysis/Complex/CauchyRiemann.lean` at the pin).
* The `(0,1)` chain rule `wirtingerDbar_comp_differentiableAt` (transition law for `Form01`).
* Regularity of the operator: `contDiffOn_wirtingerDbar`, `continuous_wirtingerDbar`,
  `hasCompactSupport_wirtingerDbar`.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace RS

variable (f g : ℂ → ℂ) (z w c : ℂ)

/-- The Wirtinger `∂` (holomorphic) derivative, `(∂f/∂x - i ∂f/∂y)/2` in real coordinates. Junk
`0` if `f` is not `ℝ`-differentiable at `z`. -/
def wirtingerD (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

/-- The Wirtinger `dbar` (anti-holomorphic) derivative, `(∂f/∂x + i ∂f/∂y)/2` in real coordinates.
Junk `0` if `f` is not `ℝ`-differentiable at `z`. -/
def wirtingerDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-! ### The Wirtinger decomposition of an `ℝ`-linear map -/

/-- `ℝ`-linear maps `ℂ → ℂ` decompose as `v ↦ a v + b v-bar` (values on the basis `1, I`).
@isnad1 id=eq.0h2v.s10.24c809032905 from=translated src=- shape=91e81cc8 vocab=c5b28081
-/
theorem clm_apply_eq_add_conj_smul (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (L 1 - Complex.I * L Complex.I) / 2 * v
        + (L 1 + Complex.I * L Complex.I) / 2 * (starRingEnd ℂ) v := by
  have hv : L v = (v.re : ℝ) • L 1 + (v.im : ℝ) • L Complex.I := by
    conv_lhs => rw [show v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one]; exact (Complex.re_add_im v).symm]
    rw [L.map_add, L.map_smul, L.map_smul]
  rw [hv]
  apply Complex.ext <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im] <;>
    ring

/-- **THE workhorse**: the Wirtinger decomposition of the real differential.
@isnad1 id=eq.1h3v.s9.0202991c852a from=translated src=- shape=f614781d vocab=642dd732
-/
theorem fderiv_apply_eq_wirtinger (_hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ f z v = wirtingerD f z * v + wirtingerDbar f z * (starRingEnd ℂ) v :=
  clm_apply_eq_add_conj_smul (fderiv ℝ f z) v

/-! ### Arithmetic -/

/--
@isnad1 id=eq.2h3v.s7.78d1319b5931 from=translated src=- shape=e769d39e vocab=e297559e
-/
theorem wirtingerDbar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDbar (f + g) z = wirtingerDbar f z + wirtingerDbar g z := by
  simp only [wirtingerDbar, fderiv_add hf hg]
  simp
  ring

/--
@isnad1 id=eq.2h3v.s7.0eda21c2076b from=translated src=- shape=e769d39e vocab=b1f049ff
-/
theorem wirtingerDbar_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDbar (f - g) z = wirtingerDbar f z - wirtingerDbar g z := by
  simp only [wirtingerDbar, fderiv_sub hf hg]
  simp
  ring

/--
@isnad1 id=eq.0h2v.s4.b974fb1f3fe5 from=translated src=- shape=13ed95b9 vocab=26bea8f7
-/
theorem wirtingerDbar_neg : wirtingerDbar (-f) z = -wirtingerDbar f z := by
  simp only [wirtingerDbar, fderiv_neg]
  simp
  ring

/--
@isnad1 id=eq.1h3v.s7.2b7bedaf4e5d from=translated src=- shape=551cada5 vocab=e4e20878
-/
theorem wirtingerDbar_const_mul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtingerDbar (fun w => c * f w) z = c * wirtingerDbar f z := by
  simp only [wirtingerDbar, fderiv_const_mul hf]
  simp
  ring

/--
@isnad1 id=eq.1h3v.s5.428d17c547dc from=translated src=- shape=bead67ce vocab=40f9badd
-/
theorem wirtingerDbar_congr_nhds (h : f =ᶠ[nhds z] g) : wirtingerDbar f z = wirtingerDbar g z := by
  simp only [wirtingerDbar, h.fderiv_eq]

/--
@isnad1 id=eq.0h1v.s4.f96d2d0b1d4d from=translated src=- shape=a02ef23e vocab=d3d88ed5
-/
theorem wirtingerDbar_zero : wirtingerDbar (0 : ℂ → ℂ) z = 0 := by
  simp [wirtingerDbar]

/--
@isnad1 id=eq.0h2v.s4.974cfc33efa4 from=translated src=- shape=c6e03d06 vocab=d3d88ed5
-/
theorem wirtingerDbar_const (c : ℂ) : wirtingerDbar (fun _ : ℂ => c) z = 0 := by
  simp [wirtingerDbar]

/-! ### Holomorphy ↔ Cauchy–Riemann -/

/--
@isnad1 id=eq.1h2v.s6.6a6275142189 from=translated src=- shape=64e000da vocab=de13c515
-/
theorem wirtingerDbar_eq_zero_of_differentiableAt (hf : DifferentiableAt ℂ f z) :
    wirtingerDbar f z = 0 := by
  have hr : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  have h1 : fderiv ℝ f z 1 = deriv f z := by
    rw [hr, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul, mul_one]
  have hI : fderiv ℝ f z Complex.I = deriv f z * Complex.I := by
    rw [hr, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
  simp only [wirtingerDbar, h1, hI]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (deriv f z / 2) * hI2

/--
@isnad1 id=eq.1h2v.s6.3ec8427340df from=translated src=- shape=4d9a7e7a vocab=e05b262e
-/
theorem wirtingerD_eq_deriv (hf : DifferentiableAt ℂ f z) : wirtingerD f z = deriv f z := by
  have hr : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  have h1 : fderiv ℝ f z 1 = deriv f z := by
    rw [hr, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul, mul_one]
  have hI : fderiv ℝ f z Complex.I = deriv f z * Complex.I := by
    rw [hr, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
  simp only [wirtingerD, h1, hI]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(deriv f z) / 2) * hI2

/-- **Cauchy–Riemann bridge** (hand-built; no mathlib counterpart at the pin).
@isnad1 id=differen.2h2v.s7.4c909fe2a851 from=translated src=- shape=9a88a372 vocab=329d7483
-/
theorem differentiableAt_of_wirtingerDbar_eq_zero (hf : DifferentiableAt ℝ f z)
    (h : wirtingerDbar f z = 0) : DifferentiableAt ℂ f z := by
  set L' := fderiv ℝ f z with hL'
  have key : ∀ v, L' v = wirtingerD f z * v := by
    intro v
    have hd := fderiv_apply_eq_wirtinger f z hf v
    rw [← hL'] at hd
    rw [hd, h]
    ring
  have hCR : L' Complex.I = Complex.I * L' 1 := by
    rw [key, key, mul_one]
    ring
  have hHom : ((L' 1 • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ) = L' := by
    ext v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    rw [map_add, map_add, L'.map_smul, L'.map_smul]
    simp only [ContinuousLinearMap.coe_restrictScalars', smul_apply,
      ContinuousLinearMap.id_apply, hCR, smul_eq_mul, Complex.real_smul]
    ring
  exact (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) (h := hf.hasFDerivAt) (H := hHom)).differentiableAt

/--
@isnad1 id=iff.0h2v.s7.364efd0b1f69 from=translated src=- shape=d6cc5f32 vocab=329d7483
-/
theorem differentiableAt_iff_wirtingerDbar_eq_zero :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ wirtingerDbar f z = 0 :=
  ⟨fun h => ⟨h.restrictScalars ℝ, wirtingerDbar_eq_zero_of_differentiableAt f z h⟩,
   fun ⟨hf, h⟩ => differentiableAt_of_wirtingerDbar_eq_zero f z hf h⟩

/--
@isnad1 id=differen.3h2v.s7.ef9ad679ce01 from=translated src=- shape=bf649d30 vocab=250f8c97
-/
theorem differentiableOn_of_wirtingerDbar_eq_zero {s : Set ℂ} (_hs : IsOpen s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (h : ∀ z ∈ s, wirtingerDbar f z = 0) :
    DifferentiableOn ℂ f s :=
  fun z hz =>
      (differentiableAt_of_wirtingerDbar_eq_zero f z (hf z hz) (h z hz)).differentiableWithinAt

/--
@isnad1 id=analytic.3h2v.s7.e7fe0f27840d from=translated src=- shape=bf649d30 vocab=3f09823b
-/
theorem analyticOnNhd_of_wirtingerDbar_eq_zero {s : Set ℂ} (hs : IsOpen s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (h : ∀ z ∈ s, wirtingerDbar f z = 0) :
    AnalyticOnNhd ℂ f s :=
  (differentiableOn_of_wirtingerDbar_eq_zero f hs hf h).analyticOnNhd hs

/-! ### The `(0,1)` chain rule -/

/-- Internal helper: the real differential of `f ∘ τ` at `v`, expressed through the Wirtinger
data of `f` at `τ z` and the (complex) derivative of `τ` at `z`. -/
private theorem fderiv_comp_apply_eq {τ : ℂ → ℂ} (hF : DifferentiableAt ℝ f (τ z))
    (hτ : DifferentiableAt ℂ τ z) (v : ℂ) :
    fderiv ℝ (f ∘ τ) z v =
      wirtingerD f (τ z) * (deriv τ z * v)
        + wirtingerDbar f (τ z) * (starRingEnd ℂ) (deriv τ z * v) := by
  have hτ' : ∀ v, fderiv ℝ τ z v = deriv τ z * v := by
    intro v
    have hr : fderiv ℝ τ z = (fderiv ℂ τ z).restrictScalars ℝ := hτ.fderiv_restrictScalars ℝ
    rw [hr, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul]
  have hcomp : fderiv ℝ (f ∘ τ) z = (fderiv ℝ f (τ z)).comp (fderiv ℝ τ z) :=
    fderiv_comp z hF (hτ.restrictScalars ℝ)
  have hv : fderiv ℝ (f ∘ τ) z v = fderiv ℝ f (τ z) (fderiv ℝ τ z v) := by
    rw [hcomp]; simp [ContinuousLinearMap.comp_apply]
  rw [hv, hτ']
  exact fderiv_apply_eq_wirtinger f (τ z) hF (deriv τ z * v)

/-- **(0,1) chain rule** along a holomorphic map — the transition law of `(0,1)`-coefficients.
@isnad1 id=eq.2h3v.s8.84df2674ad52 from=translated src=- shape=50d3bbb1 vocab=9cb9a9e4
-/
theorem wirtingerDbar_comp_differentiableAt {τ : ℂ → ℂ} (hF : DifferentiableAt ℝ f (τ z))
    (hτ : DifferentiableAt ℂ τ z) :
    wirtingerDbar (f ∘ τ) z = (starRingEnd ℂ) (deriv τ z) * wirtingerDbar f (τ z) := by
  have h1 := fderiv_comp_apply_eq f z hF hτ (1 : ℂ)
  have h2 := fderiv_comp_apply_eq f z hF hτ Complex.I
  simp only [mul_one] at h1
  simp only [map_mul, Complex.conj_I] at h2
  change (fderiv ℝ (f ∘ τ) z 1 + Complex.I * fderiv ℝ (f ∘ τ) z Complex.I) / 2 = _
  rw [h1, h2]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination
    (wirtingerD f (τ z) * deriv τ z / 2
      - wirtingerDbar f (τ z) * (starRingEnd ℂ) (deriv τ z) / 2) * hI2

/-- Companion `∂`-chain-rule (the `(1,0)` transition law).
@isnad1 id=eq.2h3v.s7.3e1d023dc172 from=translated src=- shape=fe1f3f6a vocab=9ccf3b8b
-/
theorem wirtingerD_comp_differentiableAt {τ : ℂ → ℂ} (hF : DifferentiableAt ℝ f (τ z))
    (hτ : DifferentiableAt ℂ τ z) :
    wirtingerD (f ∘ τ) z = deriv τ z * wirtingerD f (τ z) := by
  have h1 := fderiv_comp_apply_eq f z hF hτ (1 : ℂ)
  have h2 := fderiv_comp_apply_eq f z hF hτ Complex.I
  simp only [mul_one] at h1
  simp only [map_mul, Complex.conj_I] at h2
  change (fderiv ℝ (f ∘ τ) z 1 - Complex.I * fderiv ℝ (f ∘ τ) z Complex.I) / 2 = _
  rw [h1, h2]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination
    (wirtingerDbar f (τ z) * (starRingEnd ℂ) (deriv τ z) / 2
      - wirtingerD f (τ z) * deriv τ z / 2) * hI2

/-! ### Regularity of the operator -/

/--
@isnad1 id=contdiff.2h2v.s6.a434cc258821 from=translated src=- shape=206f3b7e vocab=b8bcaaa3
-/
theorem contDiffOn_wirtingerDbar {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (wirtingerDbar f) s := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hf).2
  have h1 : ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z 1) s :=
    hfd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z Complex.I) s :=
    hfd.clm_apply contDiffOn_const
  have : ContDiffOn ℝ ∞ (fun z => (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2) s :=
    ((h1.add (contDiffOn_const.mul hI))).div_const 2
  exact this

/--
@isnad1 id=continuo.1h1v.s6.c336575212f5 from=translated src=- shape=09c1a234 vocab=61e5931a
-/
theorem continuous_wirtingerDbar (hf : ContDiff ℝ ∞ f) : Continuous (wirtingerDbar f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have h1 : Continuous (fun z => fderiv ℝ f z 1) := hfd.clm_apply continuous_const
  have hI : Continuous (fun z => fderiv ℝ f z Complex.I) := hfd.clm_apply continuous_const
  have : Continuous (fun z => (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2) :=
    (h1.add (continuous_const.mul hI)).div_const 2
  exact this

/--
@isnad1 id=hascompa.1h1v.s5.ee09d735d459 from=translated src=- shape=7861e8ca vocab=5ba4f1a9
-/
theorem hasCompactSupport_wirtingerDbar (hf : HasCompactSupport f) :
    HasCompactSupport (wirtingerDbar f) := by
  apply hf.mono'
  intro x hx
  by_contra hxt
  apply hx
  simp [wirtingerDbar, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]

end RS
