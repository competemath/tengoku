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

/--
@isnad1 id=eq.0h3v.s5.ad988fcdeb35 from=translated src=- shape=d511e0d3 vocab=2911720b
-/
@[simp] theorem nV_planeVector (r z : K) : nV (planeVector r z) = r * z := by
  simp [planeVector, nV, Pf, BW]

/--
@isnad1 id=eq.0h5v.s6.cc3d4a9e03e8 from=translated src=- shape=fb544516 vocab=473fd44b
-/
@[simp] theorem BV_planeVector (r z r' z' : K) :
    BV (planeVector r z) (planeVector r' z') = r * z' + z * r' := by
  simp [planeVector, BV, BW]

/--
@isnad1 id=eq.0h1v.s5.fb1d0ddc76d8 from=translated src=- shape=e9245790 vocab=cde33bff
-/
@[simp] theorem nV_parityVector : nV (parityVector : VCoord K) = 1 := by
  simp [parityVector, nV, pf_basis_i12_add_i34]

/--
@isnad1 id=eq.0h3v.s5.5b76271b8038 from=translated src=- shape=cf3c58f9 vocab=755beae9
-/
@[simp] theorem BV_parityVector_plane (r z : K) :
    BV (parityVector : VCoord K) (planeVector r z) = 0 := by
  simp [parityVector, planeVector, BV, BW]

def targetFirst (a : K) : VCoord K := planeVector 1 a
def targetB (a h s : K) : K := (h - s) / (2 * a)
def targetC (h s : K) : K := (h + s) / 2
def targetSecond (a h s : K) : VCoord K := planeVector (targetB a h s) (targetC h s)

/--
@isnad1 id=eq.0h2v.s4.34eef3d0fa5c from=translated src=- shape=b6ef4f49 vocab=09c6c344
-/
theorem targetFirst_norm (a : K) : nV (targetFirst a) = a := by simp [targetFirst]

/--
@isnad1 id=eq.1h4v.s5.27685be87332 from=translated src=- shape=65d260ac vocab=518d374c
-/
theorem target_pairing (a h s : K) (ha : a ≠ 0) :
    BV (targetFirst a) (targetSecond a h s) = h := by
  simp [targetFirst, targetSecond, targetB, targetC]
  field_simp [ha]
  ring

/--
@isnad1 id=eq.2h5v.s7.315545b24584 from=translated src=- shape=9c73b707 vocab=94bbe6d9
-/
theorem targetSecond_norm (a h m s : K) (ha : a ≠ 0)
    (hs : s ^ 2 = h ^ 2 - 4 * a * m) :
    nV (targetSecond a h s) = m := by
  simp [targetSecond, targetB, targetC]
  field_simp [ha]
  linear_combination -hs

def targetRemainder (a h s : K) : VCoord K :=
  targetSecond a h s - (h / (2 * a)) • targetFirst a

/--
@isnad1 id=eq.1h4v.s7.e12efd73b0c3 from=translated src=- shape=42679fe1 vocab=50e8dfb2
-/
theorem targetRemainder_eq (a h s : K) (ha : a ≠ 0) :
    targetRemainder a h s = planeVector (-s / (2 * a)) (s / 2) := by
  apply VCoord.ext <;> simp [targetRemainder, targetSecond, targetFirst,
    targetB, targetC, planeVector]
  · field_simp [ha]; ring
  · field_simp [ha]; ring

/--
@isnad1 id=eq.1h4v.s7.dd0849973799 from=translated src=- shape=147a75bf vocab=8c1bf585
-/
theorem targetRemainder_norm (a h s : K) (ha : a ≠ 0) :
    nV (targetRemainder a h s) = -(s ^ 2) / (4 * a) := by
  rw [targetRemainder_eq a h s ha]
  rw [nV_planeVector]
  field_simp [ha]
  ring

end AlbertLean.Triality.SourceVectorPairDephase
