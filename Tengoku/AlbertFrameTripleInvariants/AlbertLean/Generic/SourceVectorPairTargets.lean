import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairReflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms target_pairing` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms targetSecond_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms targetRemainder_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms targetRemainder_norm` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Triality.SourceVectorPairDephase

open ExteriorSix CoordinateTensor

universe u
variable {K : Type u} [Field K] [CharZero K]

def planeVector (r z : K) : VCoord K := { r := r, z := z, omega := 0 }

def parityVector : VCoord K :=
  { r := 0, z := 0, omega := wBasis .i12 + wBasis .i34 }

@[simp] theorem nV_planeVector (r z : K) : nV (planeVector r z) = r * z := by
  simp [planeVector, nV, Pf, BW]

@[simp] theorem BV_planeVector (r z r' z' : K) :
    BV (planeVector r z) (planeVector r' z') = r * z' + z * r' := by
  simp [planeVector, BV, BW]

@[simp] theorem nV_parityVector : nV (parityVector : VCoord K) = 1 := by
  simp [parityVector, nV, pf_basis_i12_add_i34]

@[simp] theorem BV_parityVector_plane (r z : K) :
    BV (parityVector : VCoord K) (planeVector r z) = 0 := by
  simp [parityVector, planeVector, BV, BW]

def targetFirst (a : K) : VCoord K := planeVector 1 a
def targetB (a h s : K) : K := (h - s) / (2 * a)
def targetC (h s : K) : K := (h + s) / 2
def targetSecond (a h s : K) : VCoord K := planeVector (targetB a h s) (targetC h s)

theorem targetFirst_norm (a : K) : nV (targetFirst a) = a := by simp [targetFirst]

theorem target_pairing (a h s : K) (ha : a ≠ 0) :
    BV (targetFirst a) (targetSecond a h s) = h := by
  simp [targetFirst, targetSecond, targetB, targetC]
  field_simp [ha]
  ring

theorem targetSecond_norm (a h m s : K) (ha : a ≠ 0)
    (hs : s ^ 2 = h ^ 2 - 4 * a * m) :
    nV (targetSecond a h s) = m := by
  simp [targetSecond, targetB, targetC]
  field_simp [ha]
  linear_combination -hs

def targetRemainder (a h s : K) : VCoord K :=
  targetSecond a h s - (h / (2 * a)) • targetFirst a

theorem targetRemainder_eq (a h s : K) (ha : a ≠ 0) :
    targetRemainder a h s = planeVector (-s / (2 * a)) (s / 2) := by
  apply VCoord.ext <;> simp [targetRemainder, targetSecond, targetFirst,
    targetB, targetC, planeVector]
  · field_simp [ha]; ring
  · field_simp [ha]; ring

theorem targetRemainder_norm (a h s : K) (ha : a ≠ 0) :
    nV (targetRemainder a h s) = -(s ^ 2) / (4 * a) := by
  rw [targetRemainder_eq a h s ha]
  rw [nV_planeVector]
  field_simp [ha]
  ring

end AlbertLean.Triality.SourceVectorPairDephase
