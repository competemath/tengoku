import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredAdjoint
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceMuS_normalizedMuV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceMuC_normalizedMuV` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Cyclic contractions in the locked triality normalization

The proofs expand exactly the fixed four-coordinate vector/covector blocks.
No differently oriented Clifford identity is used.
-/

noncomputable section
namespace AlbertLean.Generic.CyclicContractions

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredAdjoint

variable {K : Type*} [Field K] [CharZero K]

/-- Contracting the `C` input against its normalized `V` composite returns
the `S` input scaled by its `C` norm.
@isnad1 id=eq.0h3v.s7.b3a7218264e0 from=translated src=- shape=46e08af1 vocab=c6a9d2a9
-/
theorem sourceMuS_normalizedMuV (u : SCoord K) (v : CCoord K) :
    sourceMuS v (normalizedMuV u v) = nC v • u := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, normalizedMuV, muV, nC, evalU, wedge2,
      hodgeStar, dualWedge2] <;> ring

/-- Contracting the `S` input against its normalized `V` composite returns
the `C` input scaled by its `S` norm.
@isnad1 id=eq.0h3v.s7.8cc6e8a82ce7 from=translated src=- shape=4c5a6b66 vocab=c25a37aa
-/
theorem sourceMuC_normalizedMuV (u : SCoord K) (v : CCoord K) :
    sourceMuC (normalizedMuV u v) u = nS u • v := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuC, normalizedMuV, muV, nS, evalU, wedge2,
      hodgeStar, dualWedge2] <;> ring

end AlbertLean.Generic.CyclicContractions
