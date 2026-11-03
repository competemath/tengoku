import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms evenV_middle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenS_middle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenC_middle` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceEvenAut_middle_apply` (it only prints; the queue checks the axioms of every declaration). -/

/-! The one-root middle identity in the arbitrary-even four-factor word. -/
noncomputable section
namespace AlbertLean.Triality.ParityEvenMiddleFactor

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordLinear SourceCliffordIdentities SourceCliffordReflection
open SourceEvenReflections SourceEvenAutomorphism
open SourceVectorPairDephase SourceVectorPairReflection
open RationalEvenFamilyInverse

universe u
variable {K : Type u} [Field K] [CharZero K]

set_option maxHeartbeats 600000 in
theorem evenS_middle (e A B : VCoord K) (alpha beta rho : K)
    (he : nV e = 1) (hab : alpha * beta = rho)
    (ha0 : alpha ≠ 0) (hb0 : beta ≠ 0) (s : SCoord K) :
    evenS e (reflectV e A) (-alpha)
      (evenS e B beta s) = evenS A B rho s := by
  rw [evenS_reflected_neg_reverse e A alpha (by simpa [he]) ha0]
  simp only [evenS]
  change alpha⁻¹ • muSLinear A
      (muCLinear e (beta⁻¹ • muSLinear e (muCLinear B s))) = _
  rw [(muCLinear e).map_smul]
  simp only [muSLinear_apply, muCLinear_apply]
  rw [sourceMuC_sourceMuS e]
  simp only [he, one_smul]
  change alpha⁻¹ • muSLinear A (beta⁻¹ • muCLinear B s) = _
  rw [(muSLinear A).map_smul]
  simp only [muSLinear_apply]
  simp only [smul_smul]
  have hi : alpha⁻¹ * beta⁻¹ = rho⁻¹ := by
    rw [← mul_inv, hab]
  rw [hi]
  rfl

set_option maxHeartbeats 600000 in
theorem evenC_middle (e A B : VCoord K) (alpha beta rho : K)
    (he : nV e = 1) (hab : alpha * beta = rho)
    (ha0 : alpha ≠ 0) (hb0 : beta ≠ 0) (c : CCoord K) :
    evenC e (reflectV e A) (-alpha)
      (evenC e B beta c) = evenC A B rho c := by
  rw [evenC_reflected_neg_reverse e A alpha (by simpa [he]) ha0]
  simp only [evenC]
  change alpha⁻¹ • muCLinear A
      (muSLinear e (beta⁻¹ • muCLinear e (muSLinear B c))) = _
  rw [(muSLinear e).map_smul]
  simp only [muSLinear_apply, muCLinear_apply]
  rw [sourceMuS_sourceMuC e]
  simp only [he, one_smul]
  change alpha⁻¹ • muCLinear A (beta⁻¹ • muSLinear B c) = _
  rw [(muCLinear A).map_smul]
  simp only [muCLinear_apply]
  simp only [smul_smul]
  have hi : alpha⁻¹ * beta⁻¹ = rho⁻¹ := by
    rw [← mul_inv, hab]
  rw [hi]
  rfl

theorem evenV_middle (e A B v : VCoord K) (he0 : nV e ≠ 0) :
    evenV e (reflectV e A) (evenV e B v) = evenV A B v := by
  rw [evenV_reflected_reverse e A _ he0]
  simp only [evenV]
  rw [reflectV_involutive e _ he0]

set_option maxHeartbeats 800000 in
/-- The two fixed-first-center factors equal the arbitrary even action on the
entire source carrier.-/
theorem sourceEvenAut_middle_apply
    (e A B : VCoord K) (alpha beta rho : K)
    (he : nV e = 1)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (ha : alpha ^ 2 = nV A) (hb : beta ^ 2 = nV B)
    (hab : alpha * beta = rho)
    (ha0 : alpha ≠ 0) (hb0 : beta ≠ 0) (hr0 : rho ≠ 0)
    (x : JCoord K) :
    let he0 : nV e ≠ 0 := by simpa [he]
    let hRA : nV (reflectV e A) ≠ 0 := by
      simpa [nV_reflectV e A he0] using hA
    let hneg : (-alpha) ^ 2 = nV e * nV (reflectV e A) := by
      rw [he, one_mul, nV_reflectV e A he0]
      simpa using ha
    let heB : beta ^ 2 = nV e * nV B := by simpa [he] using hb
    let hr : rho ^ 2 = nV A * nV B := by rw [← hab, mul_pow, ha, hb]
    (sourceEvenAut e (reflectV e A) (-alpha) he0 hRA hneg
      (neg_ne_zero.mpr ha0)).linear
        ((sourceEvenAut e B beta he0 hB heB hb0).linear x) =
      (sourceEvenAut A B rho hA hB hr hr0).linear x := by
  intro he0 hRA hneg heB hr
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · exact evenV_middle e A B x.v he0
  · exact evenS_middle e A B alpha beta rho he hab ha0 hb0 x.s
  · exact evenC_middle e A B alpha beta rho he hab ha0 hb0 x.c

end AlbertLean.Triality.ParityEvenMiddleFactor
