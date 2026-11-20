/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapPeaks
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CircleChordBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chord bounds for actual canonical circular node gaps

Every actual node lies outside a selected open gap. Its midpoint is uniformly
separated from all nodes once the gap width has a positive lower bound. A point
in any other small gap is close to two distinct endpoints, including when the
right endpoint is the lifted copy at `2π`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

def gapWidth (angles : CyclicAngles n hn) (cut : Fin n) : ℝ :=
  gapRight angles cut - gapLeft angles cut

def gapMidpoint (angles : CyclicAngles n hn) (cut : Fin n) : ℝ :=
  (gapLeft angles cut + gapRight angles cut) / 2

/--
@isnad1 id=lt.1h3v.s5.8cd626f383de from=translated src=- shape=bdd8b0a5 vocab=8e850e4f
-/
lemma gapWidth_pos (angles : CyclicAngles n hn) (cut : Fin n) :
    0 < gapWidth angles cut := sub_pos.mpr (gapLeft_lt_gapRight angles cut)

/--
@isnad1 id=le.1h3v.s5.ad84855a2eb2 from=translated src=- shape=42735ef0 vocab=04781ba1
-/
lemma gapWidth_le_two_pi (angles : CyclicAngles n hn) (cut : Fin n) :
    gapWidth angles cut ≤ 2 * Real.pi := by
  have ha := gapLeft_nonneg angles cut
  have hb := gapRight_le_two_pi angles cut
  dsimp [gapWidth]
  linarith

/--
@isnad1 id=mem.1h3v.s5.47f7b29448b4 from=translated src=- shape=5f7d8dff vocab=9bd0660f
-/
lemma gapMidpoint_mem_gapInterval (angles : CyclicAngles n hn) (cut : Fin n) :
    gapMidpoint angles cut ∈ gapInterval angles cut := by
  have h := gapLeft_lt_gapRight angles cut
  change gapLeft angles cut < (gapLeft angles cut + gapRight angles cut) / 2 ∧
    (gapLeft angles cut + gapRight angles cut) / 2 < gapRight angles cut
  constructor <;> linarith

/--
@isnad1 id=or.1h4v.s5.84d3412c4980 from=translated src=- shape=518fff80 vocab=c57cda44
-/
lemma node_angle_outside_gap (angles : CyclicAngles n hn) (cut k : Fin n) :
    angles.angle k ≤ gapLeft angles cut ∨ gapRight angles cut ≤ angles.angle k := by
  by_cases hzero : cut.val = 0
  · left
    rw [gapLeft_of_zero angles cut hzero]
    exact angles.strictMono.monotone (Nat.le_sub_one_of_lt k.isLt)
  · have hc : 0 < cut.val := Nat.pos_of_ne_zero hzero
    by_cases hk : k < cut
    · left
      rw [gapLeft_of_pos angles cut hc]
      apply angles.strictMono.monotone
      change k.val ≤ cut.val - 1
      have h := (show k.val < cut.val from hk)
      omega
    · right
      rw [gapRight_of_pos angles cut hc]
      exact angles.strictMono.monotone (le_of_not_gt hk)

/-- The midpoint of the actual selected gap is separated from every actual node.
@isnad1 id=and.3h4v.s7.4f7b8440ad18 from=translated src=- shape=513a8d87 vocab=0972317c
-/
theorem gapMidpoint_uniform_chord_lower_bound (angles : CyclicAngles n hn)
    (cut : Fin n) (width : ℝ) (hw : 0 < width) (hwidth : width ≤ gapWidth angles cut) :
    0 < 2 * Real.sin (width / 4) ∧ ∀ k,
      2 * Real.sin (width / 4) ≤
        ‖(Circle.exp (gapMidpoint angles cut) : ℂ) - phaseNodes angles.angle k‖ := by
  have h (k : Fin n) := norm_phase_midpoint_sub_uniform_lower_bound width
    (gapLeft angles cut) (gapRight angles cut) (angles.angle k) hw hwidth
    (gapLeft_nonneg angles cut) (gapLeft_lt_gapRight angles cut)
    (gapRight_le_two_pi angles cut) (angles.nonneg k) (angles.lt_two_pi k).le
    (node_angle_outside_gap angles cut k)
  exact ⟨(h ⟨0, hn⟩).1, fun k => (h k).2⟩

def gapLeftNodeIndex (hn : 0 < n) (cut : Fin n) : Fin n :=
  if cut.val = 0 then lastNodeIndex hn else gapPredecessor cut

/--
@isnad1 id=eq.1h3v.s6.bd7cee27e7dd from=translated src=- shape=1ac98081 vocab=57f192d3
-/
lemma exp_gapLeft (angles : CyclicAngles n hn) (cut : Fin n) :
    Circle.exp (gapLeft angles cut) = Circle.exp (angles.angle (gapLeftNodeIndex hn cut)) := by
  by_cases hzero : cut.val = 0 <;> simp [gapLeft, gapLeftNodeIndex, hzero]

/--
@isnad1 id=eq.1h3v.s6.1d7641b0c4a0 from=translated src=- shape=7b4efbd3 vocab=808462a3
-/
lemma exp_gapRight (angles : CyclicAngles n hn) (cut : Fin n) :
    Circle.exp (gapRight angles cut) = Circle.exp (angles.angle cut) := by
  by_cases hzero : cut.val = 0
  · have heq : cut = ⟨0, hn⟩ := Fin.ext hzero
    rw [gapRight_of_zero angles cut hzero, heq, angles.first_eq_zero]
    simp
  · rw [gapRight_of_pos angles cut (Nat.pos_of_ne_zero hzero)]

/--
@isnad1 id=ne.2h2v.s5.1b62243f5f9d from=translated src=- shape=ccac1459 vocab=2580c678
-/
lemma gapLeftNodeIndex_ne_cut (hsize : 2 ≤ n) (cut : Fin n) :
    gapLeftNodeIndex hn cut ≠ cut := by
  intro heq
  have hv := congrArg Fin.val heq
  by_cases hzero : cut.val = 0
  · simp only [gapLeftNodeIndex, ite_eq_left hzero, lastNodeIndex, Fin.val_mk] at hv
    omega
  · simp only [gapLeftNodeIndex, ite_eq_right hzero, gapPredecessor, Fin.val_mk] at hv
    have hpos := Nat.pos_of_ne_zero hzero
    omega

/--
@isnad1 id=le.2h4v.s7.171efd1e8579 from=translated src=- shape=187d3b5b vocab=e9c9c497
-/
lemma norm_phase_sub_leftNode_le_gapWidth (angles : CyclicAngles n hn) (cut : Fin n)
    {t : ℝ} (ht : t ∈ gapInterval angles cut) :
    ‖(Circle.exp t : ℂ) - phaseNodes angles.angle (gapLeftNodeIndex hn cut)‖ ≤
      gapWidth angles cut := by
  change ‖(Circle.exp t : ℂ) - (Circle.exp (angles.angle (gapLeftNodeIndex hn cut)) : ℂ)‖ ≤ _
  rw [← exp_gapLeft]
  have h := norm_phase_sub_le_abs_sub t (gapLeft angles cut)
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)] at h
  exact h.trans (sub_le_sub_right ht.2.le _)

/--
@isnad1 id=le.2h4v.s7.e5adf8f6c01a from=translated src=- shape=aaa74aa1 vocab=1e951c52
-/
lemma norm_phase_sub_rightNode_le_gapWidth (angles : CyclicAngles n hn) (cut : Fin n)
    {t : ℝ} (ht : t ∈ gapInterval angles cut) :
    ‖(Circle.exp t : ℂ) - phaseNodes angles.angle cut‖ ≤ gapWidth angles cut := by
  change ‖(Circle.exp t : ℂ) - (Circle.exp (angles.angle cut) : ℂ)‖ ≤ _
  rw [← exp_gapRight]
  have h := norm_phase_sub_le_abs_sub t (gapRight angles cut)
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2.le), neg_sub] at h
  exact h.trans (sub_le_sub_left ht.1.le _)

/-- For every cardinal index, one of the two distinct gap endpoints is another
node within the literal gap width. Numerator zeros at an endpoint are allowed.
@isnad1 id=ex.3h5v.s7.2a44ce089a99 from=translated src=- shape=bf4a9d38 vocab=1e951c52
-/
theorem gapInterval_near_other_node (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (cut : Fin n) {t : ℝ} (ht : t ∈ gapInterval angles cut) (k : Fin n) :
    ∃ l, l ≠ k ∧ ‖(Circle.exp t : ℂ) - phaseNodes angles.angle l‖ ≤ gapWidth angles cut := by
  by_cases hk : k = gapLeftNodeIndex hn cut
  · subst k
    exact ⟨cut, (gapLeftNodeIndex_ne_cut hsize cut).symm,
      norm_phase_sub_rightNode_le_gapWidth angles cut ht⟩
  · exact ⟨gapLeftNodeIndex hn cut, (fun h => hk h.symm),
      norm_phase_sub_leftNode_le_gapWidth angles cut ht⟩

end

end UnitCircleInterpolation
