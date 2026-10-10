import Tengoku.OpenaiMath.OAI.Analysis.SegmentLenses.GateRecovery

namespace OAI

/-!
# Signed-product recovery and the finite midpoint tail bound
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section SignedRecovery
open scoped Classical
variable {V Ω : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]

end SignedRecovery

section JointLawBound
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end JointLawBound

section HeadSupport
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem dual_ext_coordinates {x y : FullDual V}
    (h : ∀ v, x (unitVector v) = y (unitVector v)) : x = y := by
  apply dual_ext_test
  intro u
  simp only [dual_apply_test, h]

theorem head_eq_iff (H : Finset V) (x : FullDual V) :
    head H x = x ↔ ∀ v ∉ H, x (unitVector v) = 0 := by
  constructor
  · intro hx v hv
    rw [← hx, head_unitVector, ite_eq_right hv]
  · intro hx
    apply dual_ext_coordinates
    intro v
    rw [head_unitVector]
    by_cases hv : v ∈ H
    · simp [hv]
    · simp [hv, hx v hv]

theorem head_eq_of_subset {H K : Finset V} (hHK : H ⊆ K)
    (x : FullDual V) (hx : head H x = x) : head K x = x := by
  apply (head_eq_iff K x).mpr
  intro v hv
  exact (head_eq_iff H x).mp hx v (fun hvH => hv (hHK hvH))

end HeadSupport

theorem norm_center_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (R : ℝ) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) : ‖x‖ ≤ R := by
  have he : x = (1 / 2 : ℝ) • ((x + y) + (x - y)) := by module
  calc
    ‖x‖ = ‖(1 / 2 : ℝ) • ((x + y) + (x - y))‖ := congrArg norm he
    _ = (1 / 2 : ℝ) * ‖(x + y) + (x - y)‖ := by rw [norm_smul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖x + y‖ + ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ R := by linarith

section FiniteMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end FiniteMain

end SegmentLenses

end

end OAI
