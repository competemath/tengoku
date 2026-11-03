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

/--
@isnad1 id=eq.0h3v.s11.aa5d61d41848 from=translated src=- shape=a66849d4 vocab=16b7f552
-/
theorem reorient_entry (i j : Fin 4) :
    reorient k (rationalM k i j) =
      (weight k i)⁻¹ * weight k j * rationalM k j i :=
  congrArg (fun M : Matrix (Fin 4) (Fin 4) (B k) => M i j) (rationalM_reorient k)

/--
@isnad1 id=eq.0h2v.s10.da001906e333 from=translated src=- shape=5e92a6d4 vocab=fb222677
-/
@[simp] theorem reorient_diagonal (i : Fin 4) :
    reorient k (rationalM k i i) = rationalM k i i := by
  rw [reorient_entry, inv_mul_cancel₀ (weight_ne_zero k i), one_mul]

/--
@isnad1 id=eq.0h1v.s11.ca1752204e62 from=translated src=- shape=9740ec13 vocab=2130e76b
-/
@[simp] theorem reorient_bc :
    reorient k (ι k (b k) * ι k (c k)) = ι k (b k) * ι k (c k) := by
  rw [map_mul, reorient_b, reorient_c]
  field_simp [base_a_ne_zero k]

/--
@isnad1 id=eq.0h1v.s12.26bc907acd27 from=translated src=- shape=9736c51c vocab=5cd43054
-/
@[simp] theorem reorient_vGram :
    reorient k (ι k (c k) + ι k (a k) * ι k (b k)) =
      ι k (c k) + ι k (a k) * ι k (b k) := by
  rw [map_add, map_mul, reorient_c, reorient_a, reorient_b]
  field_simp [base_a_ne_zero k]
  ring

/--
@isnad1 id=eq.0h1v.s11.03fe50639716 from=translated src=- shape=9b1fcf0a vocab=7f727cb8
-/
@[simp] theorem reorient_sGram :
    reorient k (rationalM k 0 1 + rationalM k 1 0) =
      rationalM k 0 1 + rationalM k 1 0 := by
  simp only [map_add, reorient_entry, weight]
  norm_num [Fin.lt_def]
  ring

/--
@isnad1 id=eq.0h1v.s11.5196669aa307 from=translated src=- shape=9b1fcf0a vocab=7f727cb8
-/
@[simp] theorem reorient_cGram :
    reorient k (rationalM k 2 3 + rationalM k 3 2) =
      rationalM k 2 3 + rationalM k 3 2 := by
  simp only [map_add, reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

/-- Every A-weighted mixed triality is fixed.
@isnad1 id=eq.2h3v.s11.66501b84fa2b from=translated src=- shape=2a9241a7 vocab=55fd4983
-/
theorem reorient_trialityA (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    reorient k (rationalM k i j + ι k (a k) * rationalM k j i) =
      rationalM k i j + ι k (a k) * rationalM k j i := by
  simp only [map_add, map_mul, reorient_a, reorient_entry,
    weight, ite_eq_left hi, ite_eq_right hj, inv_one, one_mul, mul_one]
  field_simp [base_a_ne_zero k]
  ring

/-- Every B-weighted mixed triality is fixed.
@isnad1 id=eq.2h3v.s12.925c2ad4a2d2 from=translated src=- shape=08e859e2 vocab=f83a107d
-/
theorem reorient_trialityB (i j : Fin 4) (hi : i < 2) (hj : ¬ j < 2) :
    reorient k (ι k (b k) * rationalM k i j + ι k (c k) * rationalM k j i) =
      ι k (b k) * rationalM k i j + ι k (c k) * rationalM k j i := by
  simp only [map_add, map_mul, reorient_b, reorient_c, reorient_entry,
    weight, ite_eq_left hi, ite_eq_right hj, inv_one, one_mul, mul_one]
  field_simp [base_a_ne_zero k]
  ring

/--
@isnad1 id=eq.0h1v.s12.cfdd3b870c62 from=translated src=- shape=6a8819bf vocab=fca4e40e
-/
@[simp] theorem reorient_UC :
    reorient k (ι k (c k) * rationalM k 0 1 +
      ι k (a k) * ι k (b k) * rationalM k 1 0) =
    ι k (c k) * rationalM k 0 1 + ι k (a k) * ι k (b k) * rationalM k 1 0 := by
  simp only [map_add, map_mul, reorient_a, reorient_b, reorient_c,
    reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

/--
@isnad1 id=eq.0h1v.s12.8f12ff03e66f from=translated src=- shape=f0ebe1b7 vocab=fca4e40e
-/
@[simp] theorem reorient_US :
    reorient k (ι k (a k) * ι k (b k) * rationalM k 2 3 +
      ι k (c k) * rationalM k 3 2) =
    ι k (a k) * ι k (b k) * rationalM k 2 3 + ι k (c k) * rationalM k 3 2 := by
  simp only [map_add, map_mul, reorient_a, reorient_b, reorient_c,
    reorient_entry, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

/--
@isnad1 id=eq.0h2v.s6.ef2afc7706d1 from=translated src=- shape=a8a8a1ac vocab=47146c62
-/
theorem weightedTranspose_exteriorQ (M : Matrix (Fin 4) (Fin 4) (B k)) :
    exteriorQ (weightedTranspose k M) = exteriorQ M := by
  simp only [exteriorQ, weightedTranspose, weight]
  norm_num [Fin.lt_def]
  field_simp [base_a_ne_zero k]
  ring

/--
@isnad1 id=eq.0h1v.s10.ef28b6910537 from=translated src=- shape=a5644052 vocab=6b6f8583
-/
@[simp] theorem reorient_exteriorQ :
    reorient k (exteriorQ (rationalM k)) = exteriorQ (rationalM k) := by
  calc
    _ = exteriorQ (weightedTranspose k (rationalM k)) := by
      simp only [exteriorQ, map_add, map_sub, map_mul, reorient_entry, weightedTranspose]
    _ = _ := weightedTranspose_exteriorQ k _

end AlbertLean.Generic.GenericMeasurementSymmetry
