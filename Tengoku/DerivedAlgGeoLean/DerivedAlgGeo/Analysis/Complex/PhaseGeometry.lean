/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Analysis.Complex.HalfPlane
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Arg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase geometry of the semi-closed upper half-plane

The argument of a sum of two nonzero vectors in the semi-closed upper
half-plane lies between their arguments. This is proved directly from the
oriented planar determinant `phaseCross`, and the resulting see-saw bounds are
the analytic input for Harder--Narasimhan arguments.

Nothing here is categorical, algebraic or stability-theoretic: every statement
quantifies over complex numbers.

## Placement

These declarations were the first half of what MO1.08 (#1319) has since
renamed `CategoryTheory/Abelian/Stability/PhaseGeometry.lean`, whose second
half -- the `StabilityFunction` see-saw for a short exact sequence
-- needs an abelian category and stayed there, importing this file. MO1.13
(#1324) made the split because the Euclidean core of the mass-subadditivity
proof rests on these bounds and is required to be importable with no category
theory and no stability.

Declaration names and the `CategoryTheory.Triangulated` namespace are
unchanged; see standing decision 1 of the cutover ledger, and the same note in
`Analysis/Complex/HalfPlane.lean`.
-/

noncomputable section

open Complex Real
open scoped BigOperators

namespace CategoryTheory.Triangulated

/--
@isnad1 id=le.1h1v.s4.441f97a6cb38 from=translated src=- shape=00219549 vocab=150e57ce
-/
theorem im_nonneg_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 ≤ z.im := by
  rcases hz with him | ⟨him, _⟩
  · exact him.le
  · exact him.symm ▸ le_rfl

/--
@isnad1 id=mem.2h2v.s5.4485d21440d7 from=translated src=- shape=92663731 vocab=21ff77cc
-/
theorem add_mem_semiClosedUpperHalfPlane {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    z + w ∈ semiClosedUpperHalfPlane := by
  have hz_im := im_nonneg_of_mem_semiClosedUpperHalfPlane hz
  have hw_im := im_nonneg_of_mem_semiClosedUpperHalfPlane hw
  by_cases hz_pos : 0 < z.im
  · exact Or.inl (by simpa using add_pos_of_pos_of_nonneg hz_pos hw_im)
  by_cases hw_pos : 0 < w.im
  · exact Or.inl (by simpa using add_pos_of_nonneg_of_pos hz_im hw_pos)
  right
  have hz_zero : z.im = 0 := le_antisymm (not_lt.mp hz_pos) hz_im
  have hw_zero : w.im = 0 := le_antisymm (not_lt.mp hw_pos) hw_im
  have hz_re : z.re < 0 := by
    rcases hz with h | ⟨_, h⟩
    · exact absurd hz_zero h.ne'
    · exact h
  have hw_re : w.re < 0 := by
    rcases hw with h | ⟨_, h⟩
    · exact absurd hw_zero h.ne'
    · exact h
  exact ⟨by simp [hz_zero, hw_zero], by simpa using add_neg hz_re hw_re⟩

/-- **The additive step of every boundary argument.** A nonempty finite family of
charges on the positive real axis has its negated sum on the negative real axis,
hence in the semi-closed upper half-plane. Nothing here asks how each `0 < Re`
was obtained.
@isnad1 id=mem.3h2v.s6.c80aaaabf464 from=translated src=- shape=907eb02a vocab=6e90e58d
-/
theorem neg_sum_mem_semiClosedUpperHalfPlane_of_im_eq_zero_of_re_pos
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (him : ∀ i, (z i).im = 0) (hre : ∀ i, 0 < (z i).re) :
    -(∑ i, z i) ∈ semiClosedUpperHalfPlane := by
  have him_sum : (∑ i, z i).im = ∑ i, (z i).im := by
    simpa only [show ∀ w : ℂ, Complex.imAddGroupHom w = w.im from fun _ ↦ rfl] using
      map_sum Complex.imAddGroupHom z Finset.univ
  have hre_sum : (∑ i, z i).re = ∑ i, (z i).re := by
    simpa only [show ∀ w : ℂ, Complex.reAddGroupHom w = w.re from fun _ ↦ rfl] using
      map_sum Complex.reAddGroupHom z Finset.univ
  refine Or.inr ⟨?_, ?_⟩
  · rw [Complex.neg_im, him_sum]
    simp [him]
  · rw [Complex.neg_re, hre_sum]
    exact neg_neg_of_pos
      (Finset.sum_pos (fun i _ ↦ hre i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩)

/-- The oriented determinant of two complex vectors.-/
def phaseCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

/--
@isnad1 id=eq.0h2v.s5.a4da360a7cf4 from=translated src=- shape=299b51c1 vocab=d70caeb2
-/
theorem phaseCross_eq_norm_mul_sin (z w : ℂ) :
    phaseCross z w = ‖z‖ * ‖w‖ * Real.sin (arg w - arg z) := by
  simp only [phaseCross]
  rw [← norm_mul_cos_arg z, ← norm_mul_sin_arg z,
    ← norm_mul_cos_arg w, ← norm_mul_sin_arg w, Real.sin_sub]
  ring

/--
@isnad1 id=le.4h2v.s5.de127041edf6 from=translated src=- shape=d809f841 vocab=a16c072d
-/
theorem phaseCross_nonneg_of_arg_le {z w : ℂ}
    (hz_im : 0 ≤ z.im) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : arg z ≤ arg w) : 0 ≤ phaseCross z w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnorm]
  exact Real.sin_nonneg_of_mem_Icc
    ⟨sub_nonneg.mpr harg,
      by linarith [arg_le_pi w, arg_nonneg_iff.mpr hz_im]⟩

/--
@isnad1 id=le.4h2v.s5.a08331167407 from=translated src=- shape=d23af55c vocab=1016a7d5
-/
theorem arg_le_of_phaseCross_nonneg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hw_arg : 0 < arg w)
    (hcross : 0 ≤ phaseCross z w) : arg z ≤ arg w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnorm] at hcross
  by_contra h
  have hneg : arg w - arg z < 0 := sub_neg.mpr (lt_of_not_ge h)
  have hneg_pi : -Real.pi < arg w - arg z := by
    linarith [arg_le_pi z]
  exact (not_lt_of_ge hcross)
    (Real.sin_neg_of_neg_of_neg_pi_lt hneg hneg_pi)

/--
@isnad1 id=lt.4h2v.s5.bcbfeb5e7820 from=translated src=- shape=e8d0de9a vocab=f37a8b6d
-/
theorem phaseCross_pos_of_arg_lt {z w : ℂ}
    (hz_arg : 0 < arg z) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : arg z < arg w) : 0 < phaseCross z w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin]
  exact mul_pos hnorm (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg)
    (by linarith [arg_le_pi w]))

/--
@isnad1 id=lt.4h2v.s5.aa9a424b42fe from=translated src=- shape=02975e2e vocab=f37a8b6d
-/
theorem arg_lt_of_phaseCross_pos {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hw_arg : 0 < arg w)
    (hcross : 0 < phaseCross z w) : arg z < arg w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin] at hcross
  have hsin : 0 < Real.sin (arg w - arg z) :=
    ((mul_pos_iff.mp hcross).elim id
      (fun h => absurd h.1 (not_lt.mpr hnorm.le))).2
  by_contra h
  have hwz : arg w ≤ arg z := le_of_not_gt h
  rcases hwz.eq_or_lt with heq | hlt
  · rw [heq, sub_self, Real.sin_zero] at hsin
    exact (lt_irrefl 0) hsin
  · have hneg : arg w - arg z < 0 := sub_neg.mpr hlt
    have hneg_pi : -Real.pi < arg w - arg z := by
      linarith [arg_le_pi z]
    exact (not_lt_of_ge (Real.sin_neg_of_neg_of_neg_pi_lt hneg hneg_pi).le) hsin

/--
@isnad1 id=le.2h2v.s5.9a517151ebfe from=translated src=- shape=f674e888 vocab=601f38d8
-/
theorem arg_add_le_max {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    arg (z + w) ≤ max (arg z) (arg w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases le_total (arg z) (arg w) with h | h
  · rw [max_eq_right h]
    apply arg_le_of_phaseCross_nonneg hsum0 hw0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [max_eq_left h]
    apply arg_le_of_phaseCross_nonneg hsum0 hz0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

/--
@isnad1 id=le.2h2v.s5.c0e307dcc32d from=translated src=- shape=b9bffdde vocab=476f744a
-/
theorem min_arg_le_arg_add {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    min (arg z) (arg w) ≤ arg (z + w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases le_total (arg z) (arg w) with h | h
  · rw [min_eq_left h]
    apply arg_le_of_phaseCross_nonneg hz0 hsum0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hsum)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [min_eq_right h]
    apply arg_le_of_phaseCross_nonneg hw0 hsum0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hsum)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

/--
@isnad1 id=lt.3h2v.s5.65eb3436cf48 from=translated src=- shape=18516df0 vocab=6bc403cb
-/
theorem arg_add_lt_max {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) (hne : arg z ≠ arg w) :
    arg (z + w) < max (arg z) (arg w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases hne.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply arg_lt_of_phaseCross_pos hsum0 hw0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw)
    have hcross := phaseCross_pos_of_arg_lt
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [max_eq_left h.le]
    apply arg_lt_of_phaseCross_pos hsum0 hz0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    have hcross := phaseCross_pos_of_arg_lt
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

end CategoryTheory.Triangulated
