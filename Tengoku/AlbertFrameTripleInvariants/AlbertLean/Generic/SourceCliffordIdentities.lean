import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredAdjoint
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceMuS_sourceMuC` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceMuC_sourceMuS` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceMuS_sourceMuC_polar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceMuC_sourceMuS_polar` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Source-only proof of the two Clifford-square identities in the accepted
`K × K × Λ²(K⁴)` normalization.  No group or reflection lift is constructed.
-/
noncomputable section
namespace AlbertLean.Triality.SourceCliffordIdentities

open ExteriorSix CoordinateTensor StructuredAdjoint

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The accepted signs give `+nV(v)`, with no factor of two.
@isnad1 id=eq.0h3v.s7.81cdbeb9fc15 from=translated src=- shape=4c5a6b66 vocab=344b69ef
-/
theorem sourceMuS_sourceMuC (v : VCoord K) (s : SCoord K) :
    sourceMuS (sourceMuC v s) v = nV v • s := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, sourceMuC, nV, pf_coordinate] <;> ring

/-- The companion square on the other half-spin coordinate has the same sign.
@isnad1 id=eq.0h3v.s7.394c8faf895f from=translated src=- shape=4cbe9d8b vocab=0875a967
-/
theorem sourceMuC_sourceMuS (v : VCoord K) (c : CCoord K) :
    sourceMuC v (sourceMuS c v) = nV v • c := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, sourceMuC, nV, pf_coordinate] <;> ring

/-- Polarization of `sourceMuS_sourceMuC`; this is the `S` block of the
Clifford anticommutator.
@isnad1 id=eq.0h4v.s7.fd90dc32cd02 from=translated src=- shape=6948175d vocab=946eaeb8
-/
theorem sourceMuS_sourceMuC_polar (v w : VCoord K) (s : SCoord K) :
    sourceMuS (sourceMuC v s) w + sourceMuS (sourceMuC w s) v = BV v w • s := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, sourceMuC, BV, BW] <;> ring

/-- The `C` block of the same polarized Clifford relation.
@isnad1 id=eq.0h4v.s7.63d570ac0f7d from=translated src=- shape=e8a66a81 vocab=39121f9f
-/
theorem sourceMuC_sourceMuS_polar (v w : VCoord K) (c : CCoord K) :
    sourceMuC v (sourceMuS c w) + sourceMuC w (sourceMuS c v) = BV v w • c := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, sourceMuC, BV, BW] <;> ring

end AlbertLean.Triality.SourceCliffordIdentities
