/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from $[0, ∞)$ to $[1, ∞)$.

## Main definitions

- `Real.arcosh`: An inverse function of `Real.cosh` as a function from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshPartialEquiv`: `Real.cosh` and `Real.arcosh` bundled as a `PartialEquiv`
  from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshOpenPartialHomeomorph`: `Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to
  $(1, ∞)$.

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

- `Real.cosh_bijOn`, `Real.cosh_injOn`, `Real.cosh_surjOn`: `Real.cosh` is bijective, injective and
  surjective as a function from $[0, ∞)$ to $[1, ∞)$

- `Real.arcosh_bijOn`, `Real.arcosh_injOn`, `Real.arcosh_surjOn`: `Real.arcosh` is bijective,
  injective and surjective as a function from $[1, ∞)$ to $[0, ∞)$

- `Real.continuousOn_arcosh`: arcosh is continuous on $[1, ∞)$

- `Real.differentiableOn_arcosh`, `Real.contDiffOn_arcosh`: `Real.arcosh` is
  differentiable, and continuously differentiable on $(1, ∞)$

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
def arcosh (x : ℝ) :=
  log (x + √(x ^ 2 - 1))

/--
@isnad1 id=eq.1h1v.s5.18f1fdb11de6 from=seed src=0 shape=02c24b7d vocab=4d9dcde2
-/
theorem exp_arcosh {x : ℝ} (hx : 1 ≤ x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

/--
@isnad1 id=eq.0h0v.s3.48b4f8408b92 from=seed src=0 shape=3c26ae4f vocab=573f068a
-/
@[simp]
theorem arcosh_zero : arcosh 1 = 0 := by simp [arcosh]

/--
@isnad1 id=eq.1h1v.s6.de67a0cf748f from=seed src=0 shape=46144792 vocab=e3feb533
-/
lemma add_sqrt_self_sq_sub_one_inv {x : ℝ} (hx : 1 ≤ x) :
    (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two, sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx)), sub_sub_cancel]

/-- `arcosh` is the right inverse of `cosh` over $[1, ∞)$.
@isnad1 id=eq.1h1v.s4.74344ec08b0f from=seed src=0 shape=cc7bc718 vocab=ad031027
-/
theorem cosh_arcosh {x : ℝ} (hx : 1 ≤ x) : cosh (arcosh x) = x := by
  rw [arcosh, cosh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring

/--
@isnad1 id=iff.1h1v.s5.ccffc1936d3f from=seed src=0 shape=a6d5929f vocab=f6c28eba
-/
theorem arcosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arcosh x = 0 ↔ x = 1 := by
  rw [← exp_injective.eq_iff, exp_arcosh hx, exp_zero]
  grind

/--
@isnad1 id=eq.1h1v.s5.ae62dc91b6f5 from=seed src=0 shape=c6706fde vocab=772a107b
-/
theorem sinh_arcosh {x : ℝ} (hx : 1 ≤ x) : sinh (arcosh x) = √(x ^ 2 - 1) := by
  rw [arcosh, sinh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring

/--
@isnad1 id=eq.1h1v.s5.f9dcbd9ee942 from=seed src=0 shape=3a1991fb vocab=9ab7575f
-/
theorem tanh_arcosh {x : ℝ} (hx : 1 ≤ x) : tanh (arcosh x) = √(x ^ 2 - 1) / x := by
  rw [tanh_eq_sinh_div_cosh, sinh_arcosh hx, cosh_arcosh hx]

/-- `arcosh` is the left inverse of `cosh` over $[0, ∞)$.
@isnad1 id=eq.1h1v.s4.602068fa52de from=seed src=0 shape=cc7bc718 vocab=ad031027
-/
theorem arcosh_cosh {x : ℝ} (hx : 0 ≤ x) : arcosh (cosh x) = x := by
  rw [arcosh, ← exp_eq_exp, exp_log (by positivity), ← eq_sub_iff_add_eq', exp_sub_cosh,
    ← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx), ← sinh_sq, sq_sqrt (pow_two_nonneg _)]

/--
@isnad1 id=le.1h1v.s4.f2ba4773d731 from=seed src=0 shape=35bd48ee vocab=f6c28eba
-/
theorem arcosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arcosh x := by
  apply log_nonneg
  calc
    1 ≤ x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity

/--
@isnad1 id=lt.1h1v.s4.7fde418b9d35 from=seed src=0 shape=35bd48ee vocab=bc7fbf71
-/
theorem arcosh_pos {x : ℝ} (hx : 1 < x) : 0 < arcosh x := by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity

/-- This holds for `Ioi 0` instead of only `Ici 1` due to junk values.
@isnad1 id=strictmo.0h0v.s3.3a0c64d90283 from=seed src=0 shape=f2a09be3 vocab=b30a4d0c
-/
theorem strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi 0) := by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) ↦ show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy ↦ by gcongr

/-- This holds for `0 < x, y ≤ 1` due to junk values.
@isnad1 id=iff.2h2v.s5.7de9b721a45d from=seed src=0 shape=1d32bf94 vocab=0678502f
-/
theorem arcosh_le_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x ≤ arcosh y ↔ x ≤ y :=
  strictMonoOn_arcosh.le_iff_le hx hy

/-- This holds for `0 < x, y ≤ 1` due to junk values.
@isnad1 id=iff.2h2v.s5.5dda4b06b7a7 from=seed src=0 shape=55f320c1 vocab=bc7fbf71
-/
theorem arcosh_lt_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x < arcosh y ↔ x < y :=
  strictMonoOn_arcosh.lt_iff_lt hx hy

/-- `Real.cosh` as a `PartialEquiv` from $[0, ∞)$ to $[1, ∞)$. -/
def coshPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr

/--
@isnad1 id=continuo.0h0v.s4.3fd374ebf669 from=seed src=0 shape=f2a09be3 vocab=82310f97
-/
theorem continuousOn_arcosh : ContinuousOn arcosh (Ici 1) :=
  have {x : ℝ} (hx : x ∈ Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (by fun_prop) (by grind [MapsTo])

/-- `Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to $(1, ∞)$. -/
def coshOpenPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_arcosh.mono Ioi_subset_Ici_self

/--
@isnad1 id=hasstric.1h1v.s6.e06d95637502 from=seed src=0 shape=d369529f vocab=3bda9a1f
-/
theorem hasStrictDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) :
    HasStrictDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x := by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq, sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)

/--
@isnad1 id=hasderiv.1h1v.s6.87be3ebeb857 from=seed src=0 shape=d369529f vocab=cccb20d2
-/
theorem hasDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x :=
  (hasStrictDerivAt_arcosh hx).hasDerivAt

/--
@isnad1 id=differen.1h1v.s6.589c972cbcd1 from=seed src=0 shape=d1db726c vocab=552a1f65
-/
theorem differentiableAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : DifferentiableAt ℝ arcosh x :=
  (hasDerivAt_arcosh hx).differentiableAt

/--
@isnad1 id=differen.0h0v.s5.16c7b0baff5a from=seed src=0 shape=33637d11 vocab=1c368b18
-/
theorem differentiableOn_arcosh : DifferentiableOn ℝ arcosh (Ioi 1) := fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt

/--
@isnad1 id=contdiff.1h2v.s5.a762db981c44 from=seed src=0 shape=e6dc2d86 vocab=8907e557
-/
theorem contDiffAt_arcosh {n : WithTop ℕ∞} {x : ℝ} (hx : x ∈ Ioi 1) : ContDiffAt ℝ n arcosh x := by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq, sinh_eq_zero]
  exact (arcosh_pos hx).ne'

/--
@isnad1 id=contdiff.0h1v.s5.a7a2d7735813 from=seed src=0 shape=b334a4de vocab=6eddde59
-/
theorem contDiffOn_arcosh {n : WithTop ℕ∞} : ContDiffOn ℝ n arcosh (Ioi 1) := fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt

/-- The function `Real.arcosh` is real analytic.
@isnad1 id=analytic.1h1v.s5.7b6db518fcb6 from=seed src=0 shape=d1db726c vocab=462d4818
-/
@[fun_prop]
lemma analyticAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : AnalyticAt ℝ arcosh x :=
  (contDiffAt_arcosh hx).analyticAt

/-- The function `Real.arcosh` is real analytic.
@isnad1 id=analytic.1h2v.s5.2453fa49fa31 from=seed src=0 shape=0a6b7fd2 vocab=8d1edfe1
-/
lemma analyticWithinAt_arcosh {s : Set ℝ} {x : ℝ} (hx : x ∈ Ioi 1) :
    AnalyticWithinAt ℝ arcosh s x :=
  (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

/-- The function `Real.arcosh` is real analytic.
@isnad1 id=analytic.1h1v.s5.12ba6e297e92 from=seed src=0 shape=fb93f2a4 vocab=002a3018
-/
theorem analyticOnNhd_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOnNhd ℝ arcosh s :=
  fun _ hx ↦ analyticAt_arcosh (hs hx)

/-- The function `Real.arcosh` is real analytic.
@isnad1 id=analytic.1h1v.s5.caafb79fe5c5 from=seed src=0 shape=fb93f2a4 vocab=66708905
-/
lemma analyticOn_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOn ℝ arcosh s :=
  contDiffOn_arcosh.analyticOn.mono hs

/--
@isnad1 id=bijon.0h0v.s4.f64077cbf88f from=seed src=0 shape=1ec14745 vocab=f89eee24
-/
theorem cosh_bijOn : BijOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.bijOn

/--
@isnad1 id=injon.0h0v.s3.dece0d809103 from=seed src=0 shape=f2a09be3 vocab=d0f7b06a
-/
theorem cosh_injOn : InjOn cosh (Ici 0) := coshPartialEquiv.injOn

/--
@isnad1 id=surjon.0h0v.s4.cf25f538190e from=seed src=0 shape=1ec14745 vocab=11281cb8
-/
theorem cosh_surjOn : SurjOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.surjOn

/--
@isnad1 id=bijon.0h0v.s4.355d19ead1b6 from=seed src=0 shape=1ec14745 vocab=b4a68d5e
-/
theorem arcosh_bijOn : BijOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.bijOn

/--
@isnad1 id=injon.0h0v.s3.551b0c16ace6 from=seed src=0 shape=f2a09be3 vocab=ee943a53
-/
theorem arcosh_injOn : InjOn arcosh (Ici 1) := coshPartialEquiv.symm.injOn

/--
@isnad1 id=surjon.0h0v.s4.8932d121120d from=seed src=0 shape=1ec14745 vocab=493eeb5b
-/
theorem arcosh_surjOn : SurjOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.surjOn

end Real
