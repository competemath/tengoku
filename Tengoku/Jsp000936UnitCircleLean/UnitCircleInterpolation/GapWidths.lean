/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapChordBounds
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakOrder
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.AngularParameters
import Tengoku.Seed.Data.Finset.Max

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Widths of the actual circular node gaps

All actual positive widths add to one full turn, so one gap is at least the
average width. Their finite minimum is attained and positive. Literal gap
widths also extend continuously to the ambient normalized angular chart.
All statements include the single-node configuration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n} {d : ℕ}

/--
@isnad1 id=eq.1h2v.s5.954a693a34f8 from=translated src=- shape=4300fdaf vocab=14c2f7d4
-/
lemma sum_gapLeft (angles : CyclicAngles n hn) :
    (∑ cut, gapLeft angles cut) = ∑ k, angles.angle k := by
  have heq := (physicalGapEquiv hn).sum_comp (gapLeft angles)
  calc
    (∑ cut, gapLeft angles cut) =
        ∑ k, gapLeft angles (physicalGapCut hn k) := heq.symm
    _ = ∑ k, angles.angle k := by simp only [gapLeft_physicalGapCut]

/--
@isnad1 id=eq.1h2v.s6.decb296fe485 from=translated src=- shape=ceef4534 vocab=5d5e40c4
-/
lemma sum_gapRight (angles : CyclicAngles n hn) :
    (∑ cut, gapRight angles cut) = 2 * Real.pi + ∑ k, angles.angle k := by
  cases n with
  | zero => omega
  | succ d =>
    have hz : angles.angle 0 = 0 := angles.first_eq_zero
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hz]
    simp only [gapRight, Fin.val_zero, Fin.val_succ, Nat.succ_ne_zero,
      ite_true, ite_false, zero_add]

/-- The literal positive cyclic gap widths exhaust one full turn.
@isnad1 id=eq.1h2v.s5.2f0fb2dcd425 from=translated src=- shape=1544ef16 vocab=3e2a2e73
-/
theorem sum_gapWidth (angles : CyclicAngles n hn) :
    (∑ cut, gapWidth angles cut) = 2 * Real.pi := by
  simp only [gapWidth, Finset.sum_sub_distrib, sum_gapRight, sum_gapLeft, add_sub_cancel_right]

/-- Some actual gap is at least the mean width, also when there is only one gap.
@isnad1 id=ex.1h2v.s5.99e9f2c47164 from=translated src=- shape=5bfb2faf vocab=ed413c1e
-/
theorem exists_gapWidth_ge_average (angles : CyclicAngles n hn) :
    ∃ cut, 2 * Real.pi / (n : ℝ) ≤ gapWidth angles cut := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum : (∑ _cut : Fin n, 2 * Real.pi / (n : ℝ)) = 2 * Real.pi := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨cut, _, hcut⟩ := Finset.exists_le_of_sum_le huniv
    (show (∑ _cut : Fin n, 2 * Real.pi / (n : ℝ)) ≤ ∑ cut, gapWidth angles cut by
      rw [hsum, sum_gapWidth])
  exact ⟨cut, hcut⟩

/-- The literal finite set of all actual gap widths.-/
def gapWidthSet (angles : CyclicAngles n hn) : Finset ℝ :=
  Finset.univ.image (gapWidth angles)

/--
@isnad1 id=nonempty.1h2v.s4.52f80a4a61bb from=translated src=- shape=e47d5b57 vocab=114d80da
-/
lemma gapWidthSet_nonempty (angles : CyclicAngles n hn) : (gapWidthSet angles).Nonempty :=
  ⟨gapWidth angles ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

def minimumGapWidth (angles : CyclicAngles n hn) : ℝ :=
  (gapWidthSet angles).min' (gapWidthSet_nonempty angles)

/--
@isnad1 id=le.1h3v.s4.f571a69d8b6e from=translated src=- shape=c8f49739 vocab=cb484359
-/
lemma minimumGapWidth_le (angles : CyclicAngles n hn) (cut : Fin n) :
    minimumGapWidth angles ≤ gapWidth angles cut := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨cut, Finset.mem_univ cut, rfl⟩

/--
@isnad1 id=ex.1h2v.s5.733f9ebfb54d from=translated src=- shape=64fea889 vocab=0177d2cb
-/
lemma exists_gapWidth_eq_minimum (angles : CyclicAngles n hn) :
    ∃ cut, gapWidth angles cut = minimumGapWidth angles := by
  obtain ⟨cut, _, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem (gapWidthSet angles) (gapWidthSet_nonempty angles))
  exact ⟨cut, heq⟩

/--
@isnad1 id=lt.1h2v.s4.f5dc1cd45c3d from=translated src=- shape=1f032cf8 vocab=2ca2d316
-/
lemma minimumGapWidth_pos (angles : CyclicAngles n hn) : 0 < minimumGapWidth angles := by
  obtain ⟨cut, heq⟩ := exists_gapWidth_eq_minimum angles
  rw [← heq]
  exact gapWidth_pos angles cut

/--
@isnad1 id=le.1h2v.s5.c846a038ba62 from=translated src=- shape=b7f1a6f8 vocab=f21a7402
-/
lemma minimumGapWidth_le_average (angles : CyclicAngles n hn) :
    minimumGapWidth angles ≤ 2 * Real.pi / (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hnreal).mpr
  have hsum := Finset.sum_le_sum (fun cut (_ : cut ∈ (Finset.univ : Finset (Fin n))) =>
    minimumGapWidth_le angles cut)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_gapWidth, mul_comm] using hsum

/-- Literal gap width in the ambient normalized parameter chart.-/
def parameterGapWidth (cut : Fin (d + 1)) (u : Fin d → ℝ) : ℝ :=
  (if cut.val = 0 then 2 * Real.pi else angularParameterAngles u cut) -
    angularParameterAngles u (gapLeftNodeIndex (Nat.succ_pos d) cut)

/--
@isnad1 id=continuo.0h2v.s5.a5f02ce3f23e from=translated src=- shape=f83f0786 vocab=4f251f3c
-/
lemma continuous_parameterGapWidth (cut : Fin (d + 1)) : Continuous (parameterGapWidth cut) := by
  unfold parameterGapWidth
  split_ifs
  · exact continuous_const.sub (continuous_angularParameterAngle _)
  · exact (continuous_angularParameterAngle cut).sub (continuous_angularParameterAngle _)

/--
@isnad1 id=eq.1h3v.s6.199ee654b409 from=translated src=- shape=4f073610 vocab=ae9f739a
-/
lemma parameterGapWidth_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (cut : Fin (d + 1)) :
    parameterGapWidth cut u = gapWidth (cyclicAnglesOfParameters u hu) cut := by
  unfold parameterGapWidth gapWidth gapRight gapLeft gapLeftNodeIndex
  split_ifs <;> rfl

end

end UnitCircleInterpolation
