import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.FrameIdeal
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms plane_triality` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms plane_muC_pairing` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms plane_muS_pairing` (it only prints; the queue checks the axioms of every declaration). -/

/-!

Literal Appendix-A measurement identities derived from the already accepted
source tensor and adjoint coordinates. No paper formula becomes a premise.
-/

namespace AlbertLean.Generic.ResidualSourceMeasurements

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Residual.TrialitySquares

variable {K : Type*} [Field K] [CharZero K]

def planeVector (r z : K) : VCoord K := ⟨r, z, 0⟩

/--
@isnad1 id=eq.0h5v.s6.7c50d9df17f4 from=translated src=- shape=d8c240fa vocab=58bf1380
-/
theorem plane_triality (r z : K) (s : SCoord K) (c : CCoord K) :
    triality (planeVector r z) s c =
      r * evalU s.phi c.q + z * evalU c.psi s.p := by
  simp [triality, planeVector, BW, pairW]

/--
@isnad1 id=eq.0h7v.s7.431f6e881064 from=translated src=- shape=6fdbcf2e vocab=552c71a4
-/
theorem plane_muC_pairing (r1 z1 r2 z2 : K) (s1 s2 : SCoord K) :
    BC (sourceMuC (planeVector r1 z1) s1)
      (sourceMuC (planeVector r2 z2) s2) =
      r1 * z2 * evalU s1.phi s2.p +
        r2 * z1 * evalU s2.phi s1.p := by
  simp [BC, sourceMuC, planeVector, evalU]
  ring

/--
@isnad1 id=eq.0h7v.s7.fcf7934f93c0 from=translated src=- shape=998d116d vocab=847d0e60
-/
theorem plane_muS_pairing (r1 z1 r2 z2 : K) (c1 c2 : CCoord K) :
    BS (sourceMuS c1 (planeVector r1 z1))
      (sourceMuS c2 (planeVector r2 z2)) =
      r2 * z1 * evalU c1.psi c2.q +
        r1 * z2 * evalU c2.psi c1.q := by
  simp [BS, sourceMuS, planeVector, evalU]
  ring

/--
@isnad1 id=eq.0h5v.s7.9660c4830283 from=translated src=- shape=6928dce6 vocab=89b81ffc
-/
theorem within_gram_S (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    BS s1 s2 = momentMatrix s1 s2 c1 c2 0 1 +
      momentMatrix s1 s2 c1 c2 1 0 := rfl

/--
@isnad1 id=eq.0h5v.s7.420105bebf7b from=translated src=- shape=3426f5e3 vocab=996eddcc
-/
theorem within_gram_C (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    BC c1 c2 = momentMatrix s1 s2 c1 c2 2 3 +
      momentMatrix s1 s2 c1 c2 3 2 := rfl

end AlbertLean.Generic.ResidualSourceMeasurements
