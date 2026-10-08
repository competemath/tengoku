/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Deriv.Abs
public import Tengoku.Seed.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiability of the norm in a real normed vector space

This file provides basic results about the differentiability of the norm in a real vector space.
Most are of the following kind: if the norm has some differentiability property
(`DifferentiableAt`, `ContDiffAt`, `HasStrictFDerivAt`, `HasFDerivAt`) at `x`, then so it has
at `t • x` when `t ≠ 0`.

## Main statements

* `ContDiffAt.contDiffAt_norm_smul`: If the norm is continuously differentiable up to order `n`
  at `x`, then so it is at `t • x` when `t ≠ 0`.
* `differentiableAt_norm_smul`: If `t ≠ 0`, the norm is differentiable at `x` if and only if
  it is at `t • x`.
* `HasFDerivAt.hasFDerivAt_norm_smul`: If the norm has a Fréchet derivative `f` at `x` and `t ≠ 0`,
  then it has `(SignType t) • f` as a Fréchet derivative at `t · x`.
* `fderiv_norm_smul` : `fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x)`,
  this holds without any differentiability assumptions.
* `DifferentiableAt.fderiv_norm_self`: if the norm is differentiable at `x`,
  then `fderiv ℝ (‖·‖) x x = ‖x‖`.
* `norm_fderiv_norm`: if the norm is differentiable at `x` then the operator norm of its derivative
  is `1` (on a non-trivial space).

## Tags

differentiability, norm

-/

public section

open ContinuousLinearMap Filter NNReal Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : WithTop ℕ∞} {f : StrongDual ℝ E} {x : E} {t : ℝ}

variable (E) in
/--
@isnad1 id=not.0h1v.s6.84c3154ba45d from=seed src=0 shape=7f9e5821 vocab=209bb54f
-/
theorem not_differentiableAt_norm_zero [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E 0
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

/--
@isnad1 id=contdiff.2h4v.s7.fa0ab0f6ee86 from=seed src=0 shape=265a3ff7 vocab=967ef5c4
-/
theorem ContDiffAt.contDiffAt_norm_smul (ht : t ≠ 0) (h : ContDiffAt ℝ n (‖·‖) x) :
    ContDiffAt ℝ n (‖·‖) (t • x) := by
  have h1 : ContDiffAt ℝ n (fun y ↦ t⁻¹ • y) (t • x) := (contDiff_const_smul t⁻¹).contDiffAt
  have h2 : ContDiffAt ℝ n (fun y ↦ |t| * ‖y‖) x := h.const_smul |t|
  conv at h2 => enter [4]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 1
  ext y
  simp only [Function.comp_apply]
  rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]

/--
@isnad1 id=iff.1h4v.s7.c517e223c36f from=seed src=0 shape=48c902f6 vocab=967ef5c4
-/
theorem contDiffAt_norm_smul_iff (ht : t ≠ 0) :
    ContDiffAt ℝ n (‖·‖) x ↔ ContDiffAt ℝ n (‖·‖) (t • x) where
  mp h := h.contDiffAt_norm_smul ht
  mpr hd := by
    convert! hd.contDiffAt_norm_smul (inv_ne_zero ht)
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

/--
@isnad1 id=contdiff.1h4v.s7.01ffbe1b3587 from=seed src=0 shape=c81cc053 vocab=967ef5c4
-/
theorem ContDiffAt.contDiffAt_norm_of_smul (h : ContDiffAt ℝ n (‖·‖) (t • x)) :
    ContDiffAt ℝ n (‖·‖) x := by
  rcases eq_or_ne n 0 with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E by
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E <| h.differentiableAt hn
  · exact contDiffAt_norm_smul_iff ht |>.2 h

/--
@isnad1 id=hasstric.2h4v.s8.2ef1e1e86c72 from=seed src=0 shape=1353eb68 vocab=d888e086
-/
theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
    (ht : t ≠ 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  have h1 : HasStrictFDerivAt (fun y ↦ t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id ℝ E) (t • x) :=
    hasStrictFDerivAt_id (t • x) |>.const_smul t⁻¹
  have h2 : HasStrictFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 with y
  · rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  ext y
  simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
  rw [eq_inv_mul_iff_mul_eq₀ ht, ← mul_assoc, self_mul_sign]

/--
@isnad1 id=hasstric.2h4v.s8.77ba84a082cc from=seed src=0 shape=8160e3a7 vocab=a5796607
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne

/--
@isnad1 id=hasstric.2h4v.s7.feb3a13dbbee from=seed src=0 shape=b15e8d19 vocab=d1ea0ee6
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'

/--
@isnad1 id=hasfderi.2h4v.s8.5da5f71eac25 from=seed src=0 shape=1353eb68 vocab=0f20a9f1
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul
    (ht : t ≠ 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  have h1 : HasFDerivAt (fun y ↦ t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id ℝ E) (t • x) :=
    hasFDerivAt_id (t • x) |>.const_smul t⁻¹
  have h2 : HasFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 2 with y
  · simp only [Function.comp_apply]
    rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  · ext y
    simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
    rw [eq_inv_mul_iff_mul_eq₀ ht, ← mul_assoc, self_mul_sign]

/--
@isnad1 id=hasfderi.2h4v.s8.cba300173bfb from=seed src=0 shape=8160e3a7 vocab=112025b1
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne

/--
@isnad1 id=hasfderi.2h4v.s7.e5c4c70e9abb from=seed src=0 shape=b15e8d19 vocab=3422ffb9
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'

/--
@isnad1 id=iff.1h3v.s7.61dd23b452a8 from=seed src=0 shape=e67672a6 vocab=fde83e0e
-/
theorem differentiableAt_norm_smul (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (hd.hasFDerivAt.hasFDerivAt_norm_smul ht).differentiableAt
  mpr hd := by
    convert! (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

/--
@isnad1 id=differen.1h3v.s7.2537524ed488 from=seed src=0 shape=b6c990fb vocab=fde83e0e
-/
theorem DifferentiableAt.differentiableAt_norm_of_smul (h : DifferentiableAt ℝ (‖·‖) (t • x)) :
    DifferentiableAt ℝ (‖·‖) x := by
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E from (hasFDerivAt_of_subsingleton _ _).differentiableAt
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E h
  · exact differentiableAt_norm_smul ht |>.2 h

/--
@isnad1 id=eq.1h2v.s8.9f7fdf424398 from=seed src=0 shape=88c0ef3c vocab=c5be4976
-/
theorem DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv, lineDeriv]
  have (t : ℝ) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs, ← norm_smul, add_smul, one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t ↦ 1 + t)
    rw [deriv_comp, deriv_abs, deriv_const_add_id]
    · simp
    · exact differentiableAt_abs (by simp)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by simp)).comp _ (differentiableAt_id.const_add _)

variable (x t) in
/--
@isnad1 id=eq.0h3v.s9.b76531f5abcb from=seed src=0 shape=680a90e9 vocab=961fd0c8
-/
theorem fderiv_norm_smul :
    fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x) := by
  cases subsingleton_or_nontrivial E
  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
        exact fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd

/--
@isnad1 id=eq.1h3v.s8.9d62cb2e4f0e from=seed src=0 shape=72c6fada vocab=583e7b3d
-/
theorem fderiv_norm_smul_pos (ht : 0 < t) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

/--
@isnad1 id=eq.1h3v.s8.594392ded265 from=seed src=0 shape=d8d9cb54 vocab=e6eec1f5
-/
theorem fderiv_norm_smul_neg (ht : t < 0) :
    fderiv ℝ (‖·‖) (t • x) = -fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

/--
@isnad1 id=eq.1h2v.s8.495d2dd29d7d from=seed src=0 shape=6620875f vocab=9098ac04
-/
theorem norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := fun hx ↦ not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
    _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := le_opNorm _ _
