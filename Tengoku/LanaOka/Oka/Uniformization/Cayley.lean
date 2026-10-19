/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.LanaOka.Oka.Uniformization.KoebeMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cayley map

`cayley z = (z - i) / (z + i)` maps the upper half-plane onto the unit disc, with inverse
`cayleyInv w = i (1 + w) / (1 - w)`.
-/

open Complex Metric Set

namespace Uniformization

/-- The Cayley map `z ↦ (z - i) / (z + i)` from `ℍ` onto the unit disc. -/
noncomputable def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley map `w ↦ i (1 + w) / (1 - w)` from the unit disc onto `ℍ`. -/
noncomputable def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this; linarith

theorem one_sub_ne_zero_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, mem_ball_zero_iff, norm_one] at hw
  exact lt_irrefl _ hw

theorem cayley_mem_ball {z : ℂ} (hz : 0 < z.im) : cayley z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, cayley, norm_div, div_lt_one (norm_pos_iff.mpr (add_I_ne_zero hz))]
  have h1 : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem im_cayleyInv_pos {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 0 < (cayleyInv w).im := by
  have hd := one_sub_ne_zero_of_mem_ball hw
  have hw1 : normSq w < 1 := normSq_lt_one hw
  have hpos : 0 < normSq (1 - w) := normSq_pos.mpr hd
  have : (cayleyInv w).im = (1 - normSq w) / normSq (1 - w) := by
    rw [cayleyInv, div_im]
    simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im,
      normSq_apply]
    field_simp
    ring
  rw [this]
  exact div_pos (by linarith) hpos

theorem cayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : cayleyInv (cayley z) = z := by
  have h := add_I_ne_zero hz
  unfold cayleyInv cayley
  have h2 : 1 - (z - I) / (z + I) = 2 * I / (z + I) := by field_simp; ring
  rw [h2]
  have hI : (2 * I : ℂ) ≠ 0 := by simp
  field_simp
  ring_nf

theorem cayley_cayleyInv {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : cayley (cayleyInv w) = w := by
  have hd := one_sub_ne_zero_of_mem_ball hw
  unfold cayleyInv cayley
  have h2 : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by field_simp; ring
  rw [h2]
  have hI : (2 * I : ℂ) ≠ 0 := by simp
  field_simp
  ring_nf

theorem differentiableOn_cayley : DifferentiableOn ℂ cayley {z | 0 < z.im} :=
  (differentiableOn_id.sub_const _).div (differentiableOn_id.add_const _)
    fun _ hz ↦ add_I_ne_zero hz

theorem differentiableOn_cayleyInv : DifferentiableOn ℂ cayleyInv (ball 0 1) :=
  ((differentiableOn_const _).mul ((differentiableOn_const _).add differentiableOn_id)).div
    ((differentiableOn_const _).sub differentiableOn_id) fun _ hw ↦ one_sub_ne_zero_of_mem_ball hw

theorem isOpen_upper : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im

end Uniformization
