import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericReorientationMoment
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.TrialitySquares

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reorient_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_vGram` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_trialityA` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_trialityB` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_UC` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_US` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_exteriorQ` (it only prints; the queue checks the axioms of every declaration). -/

/-! The scalar contractions needed for literal-ledger reorientation.
These are identities in the existing nineteen-variable coefficient field. -/

noncomputable section
namespace AlbertLean.Generic.GenericMeasurementSymmetry

open Matrix
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericReorientationBase
open AlbertLean.Residual.TrialitySquares

universe u
variable (k : Type u) [Field k] [CharZero k]

theorem reorient_entry (i j : Fin 4) :
    reorient k (rationalM k i j) =
      (weight k i)⁻¹ * weight k j * rationalM k j i :=
  congrArg (fun M : Matrix (Fin 4) (Fin 4) (B k) => M i j) (rationalM_reorient k)

@[simp] theorem reorient_diagonal (i : Fin 4) :
    reorient k (rationalM k i i) = rationalM k i i := by
  rw [reorient_entry, inv_mul_cancel₀ (weight_ne_zero k i), one_mul]

@[simp] theorem reorient_bc :
    reorient k (ι k (b k) * ι k (c k)) = ι k (b k) * ι k (c k) := by
  rw [map_mul, reorient_b, reorient_c]
  field_simp [base_a_ne_zero k]

@[simp] theorem reorient_vGram :
    reorient k (ι k (c k) + ι k (a k) * ι k (b k)) =
      ι k (c k) + ι k (a k) * ι k (b k) := by
  rw [map_add, map_mul, reorient_c, reorient_a, reorient_b]
  field_simp [base_a_ne_zero k]
  ring

@[simp] theorem reorient_sGram :
    reorient k (rationalM k 0 1 + rationalM k 1 0) =
      rationalM k 0 1 + rationalM k 1 0 := by
  simp only [map_add, reorient_entry, weight]
  norm_num [Fin.lt_def]
  ring

@[simp] theorem reorient_cGram :
    reorient k (rationalM k 2 3 + rationalM k 3 2) =
      rationalM k 2 3 + rationalM k 3 2 := by
  simp only [map_add, reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

/-- Every A-weighted mixed triality is fixed.-/
theorem reorient_trialityA (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    reorient k (rationalM k i j + ι k (a k) * rationalM k j i) =
      rationalM k i j + ι k (a k) * rationalM k j i := by
  simp only [map_add, map_mul, reorient_a, reorient_entry,
    weight, ite_eq_left hi, ite_eq_right hj, inv_one, one_mul, mul_one]
  field_simp [base_a_ne_zero k]
  ring

/-- Every B-weighted mixed triality is fixed.-/
theorem reorient_trialityB (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    reorient k (ι k (b k) * rationalM k i j + ι k (c k) * rationalM k j i) =
      ι k (b k) * rationalM k i j + ι k (c k) * rationalM k j i := by
  simp only [map_add, map_mul, reorient_b, reorient_c, reorient_entry,
    weight, ite_eq_left hi, ite_eq_right hj, inv_one, one_mul, mul_one]
  field_simp [base_a_ne_zero k]
  ring

@[simp] theorem reorient_UC :
    reorient k (ι k (c k) * rationalM k 0 1 +
      ι k (a k) * ι k (b k) * rationalM k 1 0) =
    ι k (c k) * rationalM k 0 1 + ι k (a k) * ι k (b k) * rationalM k 1 0 := by
  simp only [map_add, map_mul, reorient_a, reorient_b, reorient_c,
    reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

@[simp] theorem reorient_US :
    reorient k (ι k (a k) * ι k (b k) * rationalM k 2 3 +
      ι k (c k) * rationalM k 3 2) =
    ι k (a k) * ι k (b k) * rationalM k 2 3 + ι k (c k) * rationalM k 3 2 := by
  simp only [map_add, map_mul, reorient_a, reorient_b, reorient_c,
    reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

theorem weightedTranspose_exteriorQ (M : Matrix (Fin 4) (Fin 4) (B k)) :
    exteriorQ (weightedTranspose k M) = exteriorQ M := by
  simp only [exteriorQ, weightedTranspose, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

@[simp] theorem reorient_exteriorQ :
    reorient k (exteriorQ (rationalM k)) = exteriorQ (rationalM k) := by
  calc
    _ = exteriorQ (weightedTranspose k (rationalM k)) := by
      simp only [exteriorQ, map_add, map_sub, map_mul, reorient_entry, weightedTranspose]
    _ = _ := weightedTranspose_exteriorQ k _

end AlbertLean.Generic.GenericMeasurementSymmetry
