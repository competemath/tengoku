import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephaseAut
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairTargets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms familyAut_linear_eq_fixed_center` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms two_familyAut_apply_eq_fixed_centers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms differenceB1_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms differenceB2_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms difference_centers_nonzero_r` (it only prints; the queue checks the axioms of every declaration). -/

/-! Exact matching of fixed difference-branch reflection centers with the
actual rational even family.  No branch-existence or dominance claim is made. -/

noncomputable section
namespace AlbertLean.Triality.RationalEvenFamilyFixedBranch

open ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenAutomorphism RationalEvenFamily
open SourceVectorPairDephase

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- A fixed legal even lift whose second center has nonzero `r` is literally
the corresponding member of `RationalEvenFamily.familyAut`, on the entire
source carrier.
@isnad1 id=eq.5h4v.s8.09f78c24dcaa from=translated src=- shape=887b3058 vocab=94975cec
-/
theorem familyAut_linear_eq_fixed_center
    (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0) (hBr : B.r ≠ 0)
    (hrho : rho ^ 2 = nV A * nV B) (hrho0 : rho ≠ 0) :
    (familyAut A hA B.r B.omega rho hBr hrho0).linear =
      (sourceEvenAut A B rho hA hB hrho hrho0).linear := by
  apply LinearEquiv.ext
  intro x
  unfold familyAut
  have hc : center (nV A) B.r B.omega rho = B :=
    center_eq (nV A) B rho hA hBr hrho
  change
    evenJEquiv A (center (nV A) B.r B.omega rho) rho hA _ _ hrho0 x =
      evenJEquiv A B rho hA hB hrho hrho0 x
  rw [evenJEquiv_apply, evenJEquiv_apply]
  rw [hc]

/-- Two fixed legal stages are represented by two actual rational-family
members before any coefficient specialization or numerator clearing.  The
statement is equality of the full V/S/C source action.
@isnad1 id=eq.10h8v.s11.ec49bbac7f01 from=translated src=- shape=c8119195 vocab=81d7283c
-/
theorem two_familyAut_apply_eq_fixed_centers
    (A1 B1 A2 B2 : VCoord K) (rho1 rho2 : K)
    (hA1 : nV A1 ≠ 0) (hB1 : nV B1 ≠ 0) (hB1r : B1.r ≠ 0)
    (hroot1 : rho1 ^ 2 = nV A1 * nV B1) (hrho1 : rho1 ≠ 0)
    (hA2 : nV A2 ≠ 0) (hB2 : nV B2 ≠ 0) (hB2r : B2.r ≠ 0)
    (hroot2 : rho2 ^ 2 = nV A2 * nV B2) (hrho2 : rho2 ≠ 0)
    (x : JCoord K) :
    (familyAut A2 hA2 B2.r B2.omega rho2 hB2r hrho2).linear
        ((familyAut A1 hA1 B1.r B1.omega rho1 hB1r hrho1).linear x) =
      (sourceEvenAut A2 B2 rho2 hA2 hB2 hroot2 hrho2).linear
        ((sourceEvenAut A1 B1 rho1 hA1 hB1 hroot1 hrho1).linear x) := by
  rw [familyAut_linear_eq_fixed_center A1 B1 rho1 hA1 hB1 hB1r hroot1 hrho1,
    familyAut_linear_eq_fixed_center A2 B2 rho2 hA2 hB2 hB2r hroot2 hrho2]

/-- The two second centers singled out by the fixed difference branch.-/
def differenceB1 (a : K) : VCoord K := (-2 : K) • targetFirst a

def differenceB2 (a h sigma : K) : VCoord K :=
  (-2 : K) • targetRemainder a h sigma

/--
@isnad1 id=eq.0h2v.s6.ec00e9072df0 from=translated src=- shape=cd4ba313 vocab=760c4ce5
-/
theorem differenceB1_r (a : K) : (differenceB1 a).r = -2 := by
  change (-2 : K) * (targetFirst a).r = -2
  simp [targetFirst, planeVector]

/--
@isnad1 id=eq.0h2v.s6.1a739be3711a from=translated src=- shape=560aa7df vocab=e99209cc
-/
theorem differenceB1_norm (a : K) : nV (differenceB1 a) = 4 * a := by
  rw [differenceB1, nV_smul, targetFirst_norm]
  ring

/--
@isnad1 id=eq.1h4v.s6.27d7bbe1f5dd from=translated src=- shape=2035a861 vocab=0c1dba24
-/
theorem differenceB2_r (a h sigma : K) (ha : a ≠ 0) :
    (differenceB2 a h sigma).r = sigma / a := by
  change (-2 : K) * (targetRemainder a h sigma).r = sigma / a
  rw [targetRemainder_eq a h sigma ha]
  change (-2 : K) * (-sigma / (2 * a)) = sigma / a
  field_simp [ha]

/--
@isnad1 id=eq.1h4v.s6.a092c5ae52bf from=translated src=- shape=c5deffc7 vocab=4091059f
-/
theorem differenceB2_norm (a h sigma : K) (ha : a ≠ 0) :
    nV (differenceB2 a h sigma) = -(sigma ^ 2) / a := by
  rw [differenceB2, nV_smul, targetRemainder_norm a h sigma ha]
  field_simp [ha]
  ring

/--
@isnad1 id=and.2h4v.s6.efaf9ad29b5d from=translated src=- shape=902fc89e vocab=47ee9056
-/
theorem difference_centers_nonzero_r (a h sigma : K)
    (ha : a ≠ 0) (hsigma : sigma ≠ 0) :
    (differenceB1 a).r ≠ 0 ∧ (differenceB2 a h sigma).r ≠ 0 := by
  constructor
  · rw [differenceB1_r]
    norm_num
  · rw [differenceB2_r a h sigma ha]
    exact div_ne_zero hsigma ha

end AlbertLean.Triality.RationalEvenFamilyFixedBranch
