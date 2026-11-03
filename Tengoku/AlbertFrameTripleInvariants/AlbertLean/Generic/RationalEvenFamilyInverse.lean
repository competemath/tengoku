import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairReflection
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairTargets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms C_mul_reflectV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflectV_reflected_conjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverseOmega_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceEvenAut_reflected_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedParity_family_inverse` (it only prints; the queue checks the axioms of every declaration). -/

/-! Inverse closure of the normalized even source family at field-valued
points.  Ring-level substitution and coefficient naturality are outside this
module. -/

noncomputable section
namespace AlbertLean.Triality.RationalEvenFamilyInverse

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordLinear SourceCliffordIdentities SourceCliffordReflection
open SourceEvenReflections SourceEvenAutomorphism
open SourceVectorPairReflection
open SourceVectorPairDephase RationalEvenFamily

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- Polarization says that reflecting the second Clifford vector reverses
its product with the first, with the required minus sign.-/
theorem C_mul_reflectV (a b : VCoord K) (ha : nV a ≠ 0) :
    C a * C (reflectV a b) = -(C b * C a) := by
  rw [reflectV, map_sub, map_smul, mul_sub, mul_smul_comm, C_square,
    smul_smul]
  have hc : BV a b / nV a * nV a = BV a b := div_mul_cancel₀ _ ha
  rw [hc]
  have hp := C_polar a b
  rw [← hp]
  abel

/-- The S half of `C_mul_reflectV`; it is kept separate so later family
specialization never expands the eight spinor coordinates.-/
theorem muS_reflectV_reverse (a b : VCoord K) (ha : nV a ≠ 0)
    (s : SCoord K) :
    sourceMuS (sourceMuC (reflectV a b) s) a =
      -sourceMuS (sourceMuC a s) b := by
  have h := LinearMap.congr_fun (C_mul_reflectV a b ha) (s, 0)
  simpa [C_mul_C_apply] using congrArg Prod.fst h

/-- The C half of the same joint Clifford identity.-/
theorem muC_reflectV_reverse (a b : VCoord K) (ha : nV a ≠ 0)
    (c : CCoord K) :
    sourceMuC a (sourceMuS c (reflectV a b)) =
      -sourceMuC b (sourceMuS c a) := by
  have h := LinearMap.congr_fun (C_mul_reflectV a b ha) (0, c)
  simpa [C_mul_C_apply] using congrArg Prod.snd h

/-- Conjugating a reflection by the anisotropic reflection in `a` reflects
its center.  The proof uses only the full bilinear isometry law.-/
theorem reflectV_reflected_conjugate (a b v : VCoord K) (ha : nV a ≠ 0) :
    reflectV a (reflectV (reflectV a b) v) =
      reflectV b (reflectV a v) := by
  have habv : BV (reflectV a b) v = BV b (reflectV a v) := by
    have h := SourceVectorPairReflection.BV_reflectV a b (reflectV a v) ha
    rw [SourceEvenAutomorphism.reflectV_involutive a v ha] at h
    exact h
  change SourceEvenAutomorphism.reflectVLinear a
      (v - (BV (reflectV a b) v / nV (reflectV a b)) • reflectV a b) = _
  rw [map_sub, map_smul]
  change reflectV a v -
    (BV (reflectV a b) v / nV (reflectV a b)) • reflectV a (reflectV a b) = _
  rw [SourceEvenAutomorphism.reflectV_involutive a b ha]
  change reflectV a v - (BV (reflectV a b) v / nV (reflectV a b)) • b =
    reflectV a v - (BV b (reflectV a v) / nV b) • b
  rw [habv, nV_reflectV a b ha]

 theorem evenV_reflected_reverse (a b v : VCoord K) (ha : nV a ≠ 0) :
    evenV a (reflectV a b) v = evenV b a v := by
  exact reflectV_reflected_conjugate a b v ha

 theorem evenS_reflected_neg_reverse (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hrho0 : rho ≠ 0) (s : SCoord K) :
    evenS a (reflectV a b) (-rho) s = evenS b a rho s := by
  rw [evenS, evenS, muS_reflectV_reverse a b ha]
  simp only [inv_neg, smul_neg, neg_smul, neg_neg]

 theorem evenC_reflected_neg_reverse (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hrho0 : rho ≠ 0) (c : CCoord K) :
    evenC a (reflectV a b) (-rho) c = evenC b a rho c := by
  rw [evenC, evenC, muC_reflectV_reverse a b ha]
  simp only [inv_neg, smul_neg, neg_smul, neg_neg]

/-- The reflected center and negated square root give the genuine inverse on
all six source blocks, including both half-spin slots.-/
theorem sourceEvenAut_reflected_inverse
    (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    let hb' : nV (reflectV a b) ≠ 0 := by simpa [nV_reflectV a b ha] using hb
    let hrho' : (-rho) ^ 2 = nV a * nV (reflectV a b) := by
      simpa [nV_reflectV a b ha] using hrho
    (sourceEvenAut a (reflectV a b) (-rho) ha hb' hrho'
      (neg_ne_zero.mpr hrho0)).linear =
      (sourceEvenAut a b rho ha hb hrho hrho0).linear.symm := by
  intro hb' hrho'
  apply LinearEquiv.ext
  intro x
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · change evenV a (reflectV a b) x.v = evenV b a x.v
    exact evenV_reflected_reverse a b x.v ha
  · change evenS a (reflectV a b) (-rho) x.s = evenS b a rho x.s
    exact evenS_reflected_neg_reverse a b rho ha hrho0 x.s
  · change evenC a (reflectV a b) (-rho) x.c = evenC b a rho x.c
    exact evenC_reflected_neg_reverse a b rho ha hrho0 x.c

/-- Signed exterior-coordinate permutation induced by reflection in the
fixed parity vector.-/
def inverseOmega (w : ExteriorSix.W K) : ExteriorSix.W K
  | .i12 => -w .i34
  | .i13 => w .i13
  | .i14 => w .i14
  | .i23 => w .i23
  | .i24 => w .i24
  | .i34 => -w .i12

@[simp] theorem inverseOmega_involutive (w : ExteriorSix.W K) :
    inverseOmega (inverseOmega w) = w := by
  funext i
  cases i <;> simp [inverseOmega]

@[simp] theorem Pf_inverseOmega (w : ExteriorSix.W K) :
    Pf (inverseOmega w) = Pf w := by
  rw [pf_coordinate, pf_coordinate]
  simp [inverseOmega]
  ring

theorem parity_center_inverse (r : K) (w : ExteriorSix.W K) (rho : K) :
    center 1 r (inverseOmega w) (-rho) =
      reflectV (parityVector : VCoord K) (center 1 r w rho) := by
  rw [reflectV, nV_parityVector]
  apply VCoord.ext
  · simp [center, parityVector, BV, BW]
  · simp [center, parityVector, BV, BW, Pf_inverseOmega]
  · funext i
    fin_cases i <;>
      simp [center, parityVector, inverseOmega, BV, BW, wBasis] <;> ring

/-- The actual eight-parameter parity chart is closed under inverse by
`(r,w,rho) ↦ (r,inverseOmega w,-rho)`.-/
theorem fixedParity_family_inverse (r : K) (w : ExteriorSix.W K) (rho : K)
    (hr : r ≠ 0) (hp : rho ≠ 0) :
    (familyAut parityVector (by simp) r (inverseOmega w) (-rho)
      hr (neg_ne_zero.mpr hp)).linear =
      (familyAut parityVector (by simp) r w rho hr hp).linear.symm := by
  unfold familyAut
  have h := sourceEvenAut_reflected_inverse
    (parityVector : VCoord K) (center 1 r w rho) rho
    (by simp) (norm_center_ne_zero 1 r w rho (by norm_num) hr hp)
    (by simpa only [nV_parityVector] using
      center_root 1 r w rho (by norm_num) hr) hp
  simpa only [nV_parityVector, parity_center_inverse] using h

end AlbertLean.Triality.RationalEvenFamilyInverse
