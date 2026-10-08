/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
public import Tengoku.Seed.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard three-lines Theorem

In this file we present a proof of Hadamard's three-lines Theorem.

## Main result

- `norm_le_interp_of_mem_verticalClosedStrip` :
  Hadamard three-line theorem: If `f` is a bounded function, continuous on
  `re ⁻¹' [l, u]` and differentiable on `re ⁻¹' (l, u)`, then for
  `M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})`, that is `M(x)` is the supremum of the absolute value
  of `f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [l, u]` the inequality
  `‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))` holds.
  This can be seen to be equivalent to the statement
  that `log M(re z)` is a convex function on `[0, 1]`.

- `norm_le_interp_of_mem_verticalClosedStrip'` :
  Variant of the above lemma in simpler terms. In particular, it makes no mention of the helper
  functions defined in this file.

## Main definitions

- `Complex.HadamardThreeLines.verticalStrip` :
    The vertical strip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.verticalClosedStrip` :
    The vertical strip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.sSupNormIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of the vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of any vertical strip.

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupNormIm` on the edges of the
    vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

## Note

The proof follows from Phragmén-Lindelöf when both frontiers are not everywhere zero.
We then use a limit argument to cover the case when either of the sides are `0`.
-/

@[expose] public section


open Set Filter Function Complex Topology

namespace Complex
namespace HadamardThreeLines

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Ioo a b`. -/
def verticalStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The vertical strip in the complex plane containing all `z ∈ ℂ` such that `z.re ∈ Icc a b`. -/
def verticalClosedStrip (a : ℝ) (b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The supremum of the norm of `f` on imaginary lines. (Fixed real part)
This is also known as the function `M` -/
noncomputable def sSupNormIm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (x : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' re ⁻¹' {x})

section invInterpStrip

variable {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (z : ℂ)

/--
The inverse of the interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the inverse of the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Shifting this by a positive epsilon allows us to prove the case when either of the boundaries
is zero. -/
noncomputable def invInterpStrip (ε : ℝ) : ℂ :=
  (ε + sSupNormIm f 0) ^ (z - 1) * (ε + sSupNormIm f 1) ^ (-z)

/-- A function useful for the proofs steps. We will aim to show that it is bounded by 1. -/
noncomputable def F [NormedSpace ℂ E] (ε : ℝ) := fun z ↦ invInterpStrip f z ε • f z

/-- `sSup` of `norm` is nonneg applied to the image of `f` on the vertical line `re z = x`
@isnad1 id=le.0h3v.s4.5a74249ae24f from=seed src=0 shape=08e87887 vocab=28740b6d
-/
lemma sSupNormIm_nonneg (x : ℝ) : 0 ≤ sSupNormIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/-- `sSup` of `norm` translated by `ε > 0` is positive applied to the image of `f` on the
vertical line `re z = x`
@isnad1 id=lt.1h4v.s5.b7b038c56872 from=seed src=0 shape=8bfb42c8 vocab=9200ceff
-/
lemma sSupNormIm_eps_pos {ε : ℝ} (hε : ε > 0) (x : ℝ) : 0 < ε + sSupNormIm f x := by
  linarith [sSupNormIm_nonneg f x]

/-- Useful rewrite for the absolute value of `invInterpStrip`
@isnad1 id=eq.1h4v.s6.70a372eada28 from=seed src=0 shape=ad9f7060 vocab=ad47d23d
-/
lemma norm_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    ‖invInterpStrip f z ε‖ =
    (ε + sSupNormIm f 0) ^ (z.re - 1) * (ε + sSupNormIm f 1) ^ (-z.re) := by
  simp only [invInterpStrip, norm_mul]
  repeat rw [← ofReal_add]
  repeat rw [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp

/-- The function `invInterpStrip` is `diffContOnCl`.
@isnad1 id=diffcont.1h3v.s6.307f9dfca586 from=seed src=0 shape=74839bcb vocab=99f4000d
-/
lemma diffContOnCl_invInterpStrip {ε : ℝ} (hε : ε > 0) :
    DiffContOnCl ℂ (fun z ↦ invInterpStrip f z ε) (verticalStrip 0 1) := by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const differentiable_id 1) _
    left
    rw [← ofReal_add, ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id)
    apply Or.inl
    rw [← ofReal_add, ofReal_ne_zero]
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

/-- If `f` is bounded on the unit vertical strip, then `f` is bounded by `sSupNormIm` there.
@isnad1 id=le.2h3v.s6.e90e0af7725f from=seed src=0 shape=f54a8f8d vocab=222a489b
-/
lemma norm_le_sSupNormIm (f : ℂ → E) (z : ℂ) (hD : z ∈ verticalClosedStrip 0 1)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ ≤ sSupNormIm f (z.re) := by
  refine le_csSup ?_ ?_
  · revert hB; gcongr
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

/-- Alternative version of `norm_le_sSupNormIm` with a strict inequality and a positive `ε`.
@isnad1 id=lt.3h4v.s6.ecee0dba7811 from=seed src=0 shape=32ab69ac vocab=8d90b368
-/
lemma norm_lt_sSupNormIm_eps (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hD : z ∈ verticalClosedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ < ε + sSupNormIm f (z.re) :=
  lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

variable [NormedSpace ℂ E]

set_option backward.isDefEq.respectTransparency.types false in
/-- When the function `f` is bounded above on a vertical strip, then so is `F`.
@isnad1 id=bddabove.2h3v.s6.361f85e4221e from=seed src=0 shape=1fa1dd97 vocab=ce99a7a6
-/
lemma F_BddAbove (f : ℂ → E) (ε : ℝ) (hε : ε > 0)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    BddAbove ((norm ∘ (F f ε)) '' verticalClosedStrip 0 1) := by
  -- Rewriting goal
  simp only [F, comp_apply, invInterpStrip]
  rw [bddAbove_def] at *
  rcases hB with ⟨B, hB⟩
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0) ^ (-(1 : ℝ)))) * max 1 ((ε + sSupNormIm f 1) ^ (-(1 : ℝ)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hset
  specialize hB (‖f z‖) (by simpa [image_congr, mem_image, comp_apply] using ⟨z, hset, rfl⟩)
  -- Proof that the bound is correct
  simp only [norm_smul, norm_mul, ← ofReal_add]
  gcongr
    -- Bounding individual terms
  · by_cases hM0_one : 1 ≤ ε + sSupNormIm f 0
    -- `1 ≤ sSupNormIm f 0`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
    -- `0 < sSupNormIm f 0 < 1`
    · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re]
      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
  · by_cases hM1_one : 1 ≤ ε + sSupNormIm f 1
    -- `1 ≤ sSupNormIm f 1`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_one_of_one_le_of_nonpos
        hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
    -- `0 < sSupNormIm f 1 < 1`
    · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
        (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]

/-- Proof that `F` is bounded by one on the edges.
@isnad1 id=le.3h4v.s6.6fc47701ee6d from=seed src=0 shape=cb1b0a3c vocab=2c3a18bc
-/
lemma F_edge_le_one (f : ℂ → E) (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ re ⁻¹' {0, 1}) :
    ‖F f ε z‖ ≤ 1 := by
  simp only [F, norm_smul, norm_invInterpStrip f z hε]
  rcases hz with hz0 | hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

/--
@isnad1 id=le.4h4v.s7.71f8984b7d8a from=seed src=0 shape=9ec135c2 vocab=04575dd5
-/
theorem norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip (f : ℂ → E) (ε : ℝ) (hε : 0 < ε)
    (z : ℂ) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F f ε z‖ ≤ 1 := by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx ↦ F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero, div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro x hx
  simpa using! (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

end invInterpStrip

-----

variable {E : Type*} [NormedAddCommGroup E] (f : ℂ → E)

/--
The interpolation of `sSupNormIm` on the two boundaries.
In other words, this is the right side of the target inequality:
`|f(z)| ≤ |M(0) ^ (1-z)| * |M(1) ^ z|`.

Note that if `sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0` then the power is not continuous
since `0 ^ 0 = 1`. Hence the use of `ite`. -/
noncomputable def interpStrip (z : ℂ) : ℂ :=
  if sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    then 0
    else sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z

/-- Rewrite for `InterpStrip` when `0 < sSupNormIm f 0` and `0 < sSupNormIm f 1`.
@isnad1 id=eq.2h3v.s6.2dcee0917bb7 from=seed src=0 shape=8b773637 vocab=aca369ab
-/
lemma interpStrip_eq_of_pos (z : ℂ) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, ite_false, or_false]

/-- Rewrite for `InterpStrip` when `0 = sSupNormIm f 0` or `0 = sSupNormIm f 1`.
@isnad1 id=eq.1h3v.s5.f4cff6ab0a83 from=seed src=0 shape=06200d98 vocab=90ea726c
-/
lemma interpStrip_eq_of_zero (z : ℂ) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) :
    interpStrip f z = 0 :=
  ite_eq_left h

/-- Rewrite for `InterpStrip` on the open vertical strip.
@isnad1 id=eq.1h3v.s6.54f1e24980cf from=seed src=0 shape=1dc861f3 vocab=20ac2bb3
-/
lemma interpStrip_eq_of_mem_verticalStrip (z : ℂ) (hz : z ∈ verticalStrip 0 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  · rw [interpStrip_eq_of_zero _ z h]
    rcases h with h0 | h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero, eq_comm]
      simp only [Complex.ext_iff, one_re, ne_of_lt hz.2, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [Complex.ext_iff, zero_re, ne_of_lt hz.1, false_and, not_false_eq_true]
  · replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) :=
      ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f z h.1 h.2

/--
@isnad1 id=diffcont.0h2v.s5.e02b4a9b37a5 from=seed src=0 shape=2ac89a4c vocab=249a50a7
-/
lemma diffContOnCl_interpStrip :
    DiffContOnCl ℂ (interpStrip f) (verticalStrip 0 1) := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f _ h]; exact diffContOnCl_const
  -- Case nowhere 0
  · rcases h with ⟨h0, h1⟩
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub differentiableAt_id 1) _
      left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id
      · left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]

/-- The correct generalization of `interpStrip` to produce bounds in the general case. -/
noncomputable def interpStrip' (f : ℂ → E) (l u : ℝ) (z : ℂ) : ℂ :=
  if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0
    then 0
    else sSupNormIm f l ^ (1 - ((z - l) / (u - l))) * sSupNormIm f u ^ ((z - l) / (u - l))

/-- An auxiliary function to prove the general statement of Hadamard's three lines theorem. -/
def scale (f : ℂ → E) (l u : ℝ) : ℂ → E := fun z ↦ f (l + z • (u - l))

/-- The transformation on ℂ that is used for `scale` maps the closed strip ``re ⁻¹' [l, u]``
  to the closed strip ``re ⁻¹' [0, 1]``.
@isnad1 id=mem.2h3v.s6.4836d198a4f6 from=seed src=0 shape=7fc76015 vocab=2102b4ce
-/
lemma scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip {l u : ℝ} (hul : l < u) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : l + z * (u - l) ∈ verticalClosedStrip l u := by
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc] at hz ⊢
  constructor <;> nlinarith [hz.1, hz.2, hul]

/-- The norm of the function `scale f l u` is bounded above on the closed strip `re⁻¹' [0, 1]`.
@isnad1 id=bddabove.2h4v.s6.b629517370eb from=seed src=0 shape=b85fd7d1 vocab=177d2b9a
-/
lemma scale_bddAbove {f : ℂ → E} {l u : ℝ} (hul : l < u)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    BddAbove ((norm ∘ scale f l u) '' verticalClosedStrip 0 1) := by
  refine hB.mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨l + z * (u - l), scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip hul hz, rfl⟩

/-- A bound to the norm of `f` on the line `z.re = l` induces a bound to the norm of
  `scale f l u z` on the line `z.re = 0`.
@isnad1 id=le.2h6v.s6.b41ed6d9c052 from=seed src=0 shape=c2256684 vocab=ee1d4d23
-/
lemma scale_bound_left {f : ℂ → E} {l u a : ℝ} (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) :
    ∀ z ∈ re ⁻¹' {0}, ‖scale f l u z‖ ≤ a := by
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  intro z hz
  exact ha (↑l + z * (↑u - ↑l)) (by simp [hz])

/-- A bound to the norm of `f` on the line `z.re = u` induces a bound to the norm of `scale f l u z`
  on the line `z.re = 1`.
@isnad1 id=le.2h6v.s6.a53ded846b92 from=seed src=0 shape=b23693aa vocab=ee1d4d23
-/
lemma scale_bound_right {f : ℂ → E} {l u b : ℝ} (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ∀ z ∈ re ⁻¹' {1}, ‖scale f l u z‖ ≤ b := by
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  intro z hz
  exact hb (↑l + z * (↑u - ↑l)) (by simp [hz])

/-- The supremum of the norm of `scale f l u` on the line `z.re = 0` is the same as the supremum
  of `f` on the line `z.re = l`.
@isnad1 id=eq.1h4v.s5.87b745053c07 from=seed src=0 shape=91d6bbd1 vocab=317c7dbb
-/
lemma sSupNormIm_scale_left (f : ℂ → E) {l u : ℝ} (hul : l < u) :
    sSupNormIm (scale f l u) 0 = sSupNormIm f l := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {0} = f '' re ⁻¹' {l} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp [hz₂]
  rw [this]

/-- The supremum of the norm of `scale f l u` on the line `z.re = 1` is the same as
  the supremum of `f` on the line `z.re = u`.
@isnad1 id=eq.1h4v.s5.e5fc735d57f6 from=seed src=0 shape=fe7a7459 vocab=317c7dbb
-/
lemma sSupNormIm_scale_right (f : ℂ → E) {l u : ℝ} (hul : l < u) :
    sSupNormIm (scale f l u) 1 = sSupNormIm f u := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {1} = f '' re ⁻¹' {u} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        grind [Complex.div_re, Complex.normSq_ofReal, sub_re, ofReal_re, ofReal_im, mul_eq_zero]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

/-- A technical lemma relating the bounds given by the three lines lemma on a general strip
to the bounds for its scaled version on the strip `re ⁻¹' [0, 1]`.
@isnad1 id=eq.1h5v.s6.981eca2666a8 from=seed src=0 shape=c0fcb4a4 vocab=045dc0f3
-/
lemma interpStrip_scale (f : ℂ → E) {l u : ℝ} (hul : l < u) (z : ℂ) : interpStrip (scale f l u)
    ((z - ↑l) / (↑u - ↑l)) = interpStrip' f l u z := by
  simp only [interpStrip, interpStrip']
  simp_rw [sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

variable [NormedSpace ℂ E]

/--
@isnad1 id=le.4h4v.s7.b248dbc293a5 from=seed src=0 shape=01f985b2 vocab=74d44eb8
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip_eps (ε : ℝ) (hε : ε > 0) (z : ℂ)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖f z‖ ≤ ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : ℂ)‖ := by
  simp only [norm_mul, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _,
    sub_re, one_re]
  rw [← mul_inv_le_iff₀', ← one_mul (((ε + sSupNormIm f 1) ^ z.re)), ← mul_inv_le_iff₀,
    ← Real.rpow_neg_one, ← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, norm_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1 - z.re)]

/--
@isnad1 id=eventual.3h3v.s7.25db7b1798dd from=seed src=0 shape=a9a235c1 vocab=090c978d
-/
lemma eventuallyle (z : ℂ) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1)) (hz : z ∈ verticalStrip 0 1) :
    (fun _ : ℝ ↦ ‖f z‖) ≤ᶠ[𝓝[>] 0]
    (fun ε ↦ ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : ℂ)‖) := by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using
    norm_le_interpStrip_of_mem_verticalClosedStrip_eps f ε hε z hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))

/--
@isnad1 id=le.3h3v.s6.8b36edd793c8 from=seed src=0 shape=cb751ae3 vocab=87207127
-/
lemma norm_le_interpStrip_of_mem_verticalStrip_zero (z : ℂ)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z ∈ verticalStrip 0 1) :
    ‖f z‖ ≤ ‖interpStrip f z‖ := by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_of_mem_verticalStrip _ _ hz]
    convert! ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add]
      have : ∀ x ∈ Ioi 0, (x + sSupNormIm f 0) ^ (1 - z.re) * (x + sSupNormIm f 1) ^ z.re
          = ‖((x + sSupNormIm f 0 : ℝ) ^ (1 - z) * (x + sSupNormIm f 1 : ℝ) ^ z : ℂ)‖ := by
              intro x hx
              simp only [norm_mul]
              repeat rw [norm_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _,
        norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

/--
**Hadamard three-line theorem** on `re ⁻¹' [0, 1]`: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [0, 1]` and differentiable on open strip `re ⁻¹' (0, 1)`, then for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ M(0) ^ (1 - z.re) * M(1) ^ z.re` holds.
@isnad1 id=le.3h3v.s6.b7128e1c359a from=seed src=0 shape=e35a75cf vocab=87207127
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (f : ℂ → E) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ ≤ ‖interpStrip f z‖ := by
  apply le_on_closure (fun w hw ↦ norm_le_interpStrip_of_mem_verticalStrip_zero f w hd hB hw)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

/-- **Hadamard three-line theorem** on `re ⁻¹' [0, 1]` (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [0, 1]` and differentiable on open strip
`re ⁻¹' (0, 1)`. If, for all `z.re = 0`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, similarly, for all
`z.re = 1`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [0, 1]` the inequality `‖f(z)‖ ≤ a ^ (1 - z.re) * b ^ z.re` holds.
@isnad1 id=le.5h5v.s7.4701567fbee4 from=seed src=0 shape=078b2b23 vocab=9b93563f
-/
lemma norm_le_interp_of_mem_verticalClosedStrip₀₁' (f : ℂ → E) {z : ℂ} {a b : ℝ}
    (hz : z ∈ verticalClosedStrip 0 1) (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (ha : ∀ z ∈ re ⁻¹' {0}, ‖f z‖ ≤ a) (hb : ∀ z ∈ re ⁻¹' {1}, ‖f z‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - z.re) * b ^ z.re := by
  have : ‖interpStrip f z‖ ≤ sSupNormIm f 0 ^ (1 - z.re) * sSupNormIm f 1 ^ z.re := by
    by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    · rw [interpStrip_eq_of_zero f z h, norm_zero, mul_nonneg_iff]
      left
      exact ⟨Real.rpow_nonneg (sSupNormIm_nonneg f _) _,
        Real.rpow_nonneg (sSupNormIm_nonneg f _) _ ⟩
    · rcases h with ⟨h0, h1⟩
      rw [ne_comm] at h0 h1
      simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
      simp only [norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h0).mp (sSupNormIm_nonneg f _)) _]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h1).mp (sSupNormIm_nonneg f _)) _]
      simp only [sub_re, one_re, le_refl]
  apply (norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ f hz hd hB).trans (this.trans _)
  apply mul_le_mul_of_nonneg _ _ (Real.rpow_nonneg (sSupNormIm_nonneg f _) _)
  · apply (Real.rpow_nonneg _ _)
    specialize hb 1
    simp only [mem_preimage, one_re, mem_singleton_iff, forall_true_left] at hb
    exact (norm_nonneg _).trans hb
  · gcongr
    · exact sSupNormIm_nonneg f _
    · exact sub_nonneg.mpr hz.2
    rw [sSupNormIm]
    apply csSup_le _
    · simpa [comp_apply, mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] using ha
    · use ‖(f 0)‖, 0
      simp
  · apply Real.rpow_le_rpow (sSupNormIm_nonneg f _) _ hz.1
    · rw [sSupNormIm]
      apply csSup_le _
      · simpa [comp_apply, mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] using hb
      · use ‖(f 1)‖, 1
        simp only [mem_preimage, one_re, mem_singleton_iff, comp_apply,
          and_self]

/-- The transformation on ℂ that is used for `scale` maps the strip ``re ⁻¹' (l, u)``
  to the strip ``re ⁻¹' (0, 1)``.
@isnad1 id=mem.2h3v.s6.90976f2943c1 from=seed src=0 shape=7fc76015 vocab=242f4a40
-/
lemma scale_id_mem_verticalStrip_of_mem_verticalStrip {l u : ℝ} (hul : l < u) {z : ℂ}
    (hz : z ∈ verticalStrip 0 1) : l + z * (u - l) ∈ verticalStrip l u := by
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm, ← sub_lt_sub_iff_right l, add_sub_assoc, sub_self, add_zero]
  nth_rewrite 2 [← one_mul (u - l)]
  gcongr

/-- If z is on the closed strip `re ⁻¹' [l, u]`, then `(z - l) / (u - l)` is on the closed strip
  `re ⁻¹' [0, 1]`.
@isnad1 id=mem.2h3v.s6.840a5830b520 from=seed src=0 shape=92cdcfbb vocab=d3230052
-/
lemma mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z : ℂ} {l u : ℝ} (hul : l < u)
    (hz : z ∈ verticalClosedStrip l u) : z / (u - l) - l / (u - l) ∈ verticalClosedStrip 0 1 := by
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (by linarith : u - l ≠ 0), ← div_eq_mul_one_div]
  constructor
  · gcongr
    exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u - l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2

/-- The function `scale f l u` is `diffContOnCl`.
@isnad1 id=diffcont.2h4v.s6.b01f56636f20 from=seed src=0 shape=4817cb1c vocab=799e7848
-/
lemma scale_diffContOnCl {f : ℂ → E} {l u : ℝ} (hul : l < u)
    (hd : DiffContOnCl ℂ f (verticalStrip l u)) :
    DiffContOnCl ℂ (scale f l u) (verticalStrip 0 1) := by
  unfold scale
  apply DiffContOnCl.comp (s := verticalStrip l u) hd
  · apply DiffContOnCl.const_add
    apply DiffContOnCl.smul_const
    exact Differentiable.diffContOnCl differentiable_id
  · rw [MapsTo]
    intro z hz
    exact scale_id_mem_verticalStrip_of_mem_verticalStrip hul hz

/-- A technical lemma needed in the proof. -/
private lemma fun_arg_eq {l u : ℝ} (hul : l < u) (z : ℂ) :
    (↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)) * (↑u - ↑l)) = z := by
  rw [sub_mul, div_mul_comm, div_self (by norm_cast; linarith),
    div_mul_comm, div_self (by norm_cast; linarith)]
  simp

/-- Another technical lemma needed in the proof. -/
private lemma bound_exp_eq {l u : ℝ} (hul : l < u) (z : ℂ) :
    (z / (↑u - ↑l)).re - ((l : ℂ) / (↑u - ↑l)).re = (z.re - l) / (u - l) := by
  norm_cast
  rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im, mul_div_assoc,
    div_mul_eq_div_div_swap, div_self (by norm_cast; linarith),
    ← div_eq_mul_one_div]
  simp only [mul_zero, zero_div, add_zero]
  rw [← div_sub_div_same]

/--
**Hadamard three-line theorem**: If `f` is a bounded function, continuous on the
closed strip `re ⁻¹' [l, u]` and differentiable on open strip `re ⁻¹' (l, u)`, then for
`M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})` we have that for all `z` in the closed strip
`re ⁻¹' [a,b]` the inequality
`‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))`
holds.
@isnad1 id=le.4h5v.s6.cef48315867a from=seed src=0 shape=da2ff44a vocab=4166120b
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip {l u : ℝ} (hul : l < u)
    {f : ℂ → E} {z : ℂ}
    (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    ‖f z‖ ≤ ‖interpStrip' f l u z‖ := by
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz)
    (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  simp only [scale, smul_eq_mul] at hgoal
  rw [fun_arg_eq hul, div_sub_div_same, interpStrip_scale f hul z] at hgoal
  exact hgoal

/-- **Hadamard three-line theorem** (Variant in simpler terms): Let `f` be a
bounded function, continuous on the closed strip `re ⁻¹' [l, u]` and differentiable on open strip
`re ⁻¹' (l, u)`. If, for all `z.re = l`, `‖f z‖ ≤ a` for some `a ∈ ℝ` and, similarly, for all
`z.re = u`, `‖f z‖ ≤ b` for some `b ∈ ℝ` then for all `z` in the closed strip
`re ⁻¹' [l, u]` the inequality
`‖f(z)‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l))`
holds.
@isnad1 id=le.6h7v.s8.ca55100d9c0a from=seed src=0 shape=a1fb3fa4 vocab=edad394e
-/
lemma norm_le_interp_of_mem_verticalClosedStrip' {f : ℂ → E} {z : ℂ} {a b l u : ℝ}
    (hul : l < u) (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u))
    (ha : ∀ z ∈ re ⁻¹' {l}, ‖f z‖ ≤ a) (hb : ∀ z ∈ re ⁻¹' {u}, ‖f z‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by
  have hgoal := norm_le_interp_of_mem_verticalClosedStrip₀₁' (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz) (scale_diffContOnCl hul hd)
    (scale_bddAbove hul hB) (scale_bound_left ha) (scale_bound_right hb)
  simp only [scale, smul_eq_mul, sub_re] at hgoal
  rw [fun_arg_eq hul, bound_exp_eq hul] at hgoal
  exact hgoal

end HadamardThreeLines
end Complex
