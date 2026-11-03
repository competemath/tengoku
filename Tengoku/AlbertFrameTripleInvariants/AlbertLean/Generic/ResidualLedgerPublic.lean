import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerPower
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredProductF0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceLedger_eq_public` (it only prints; the queue checks the axioms of every declaration). -/

/-! Exact rational public-ledger adapter. -/

noncomputable section
namespace AlbertLean.Generic.ResidualLedgerPublic

open AlbertLean
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Comparison.StructuredProductF0
open AlbertLean.Generic.ResidualLedgerPower

/--
@isnad1 id=eq.0h2v.s9.ee834d330f75 from=translated src=- shape=8e790da6 vocab=a885d9b6
-/
theorem map_sourceProduct (x y : JCoord ℚ) :
    structuredEquiv (sourceProduct x y) =
      structuredProduct (structuredEquiv x) (structuredEquiv y) :=
  StructuredSourceProductAgreesWithF0 x y

/--
@isnad1 id=eq.0h2v.s8.0344ebda7949 from=translated src=- shape=64963cd5 vocab=9667b4ef
-/
theorem map_spectralProjector (a : JCoord ℚ) (i : Fin 3) :
    structuredEquiv (spectralProjector a i) = projector (structuredEquiv a) i := by
  fin_cases i
  · change structuredEquiv ((2 : ℚ)⁻¹ • (sourceSquare a - a)) =
      (2 : ℚ)⁻¹ • (structuredProduct (structuredEquiv a) (structuredEquiv a) - structuredEquiv a)
    rw [map_smul, map_sub, sourceSquare, map_sourceProduct]
  · change structuredEquiv (sourceOne - sourceSquare a) =
      one - structuredProduct (structuredEquiv a) (structuredEquiv a)
    rw [map_sub, structuredEquiv_sourceOne, sourceSquare, map_sourceProduct]
  · change structuredEquiv ((2 : ℚ)⁻¹ • (sourceSquare a + a)) =
      (2 : ℚ)⁻¹ • (structuredProduct (structuredEquiv a) (structuredEquiv a) + structuredEquiv a)
    rw [map_smul, map_add, sourceSquare, map_sourceProduct]

/--
@isnad1 id=eq.0h1v.s8.eec2e62e3cef from=translated src=- shape=a00a6bc7 vocab=c0bffe7a
-/
theorem map_diagonalUnit (i : Fin 3) :
    structuredEquiv (diagonalUnit i : JCoord ℚ) =
      projector (structuredEquiv (diagonal (-1) 0 1)) i := by
  rw [← diagonal_projectors]
  exact map_spectralProjector _ i

def publicTriple (a b : JCoord ℚ) : WitnessTriple :=
  ⟨structuredEquiv (diagonal (-1) 0 1), structuredEquiv a, structuredEquiv b⟩

def copyLedger (L : Ledger) : SourceLedger ℚ := ⟨L.P, L.Q, L.R, L.C0⟩

/-- Equality with all 54 existing public cells, including ordered R slots
and the exact centering constants.
@isnad1 id=eq.0h2v.s4.3bbcdcd8093a from=translated src=- shape=05a42ed8 vocab=3ba27452
-/
theorem sourceLedger_eq_public (a b : JCoord ℚ) :
    sourceLedger a b = copyLedger (ledger (publicTriple a b)) := by
  apply SourceLedger.ext
  · funext i j
    change sourceTraceForm (diagonalUnit i) (spectralProjector a j) = _
    rw [sourceTraceForm_agrees_with_f0, map_diagonalUnit, map_spectralProjector]
    rfl
  · funext j l
    change sourceTraceForm (spectralProjector a j) (spectralProjector b l) = _
    rw [sourceTraceForm_agrees_with_f0, map_spectralProjector, map_spectralProjector]
    rfl
  · funext l i
    change sourceTraceForm (spectralProjector b l) (diagonalUnit i) = _
    rw [sourceTraceForm_agrees_with_f0, map_spectralProjector, map_diagonalUnit]
    rfl
  · funext i j l
    simp only [sourceLedger, copyLedger, ledger, publicTriple,
      sourceTraceForm_agrees_with_f0, map_sourceProduct,
      map_diagonalUnit, map_spectralProjector]

end AlbertLean.Generic.ResidualLedgerPublic
