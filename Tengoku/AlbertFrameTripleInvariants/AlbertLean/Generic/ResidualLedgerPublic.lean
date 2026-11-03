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

theorem map_sourceProduct (x y : JCoord ℚ) :
    structuredEquiv (sourceProduct x y) =
      structuredProduct (structuredEquiv x) (structuredEquiv y) :=
  StructuredSourceProductAgreesWithF0 x y

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

theorem map_diagonalUnit (i : Fin 3) :
    structuredEquiv (diagonalUnit i : JCoord ℚ) =
      projector (structuredEquiv (diagonal (-1) 0 1)) i := by
  rw [← diagonal_projectors]
  exact map_spectralProjector _ i

def publicTriple (a b : JCoord ℚ) : WitnessTriple :=
  ⟨structuredEquiv (diagonal (-1) 0 1), structuredEquiv a, structuredEquiv b⟩

def copyLedger (L : Ledger) : SourceLedger ℚ := ⟨L.P, L.Q, L.R, L.C0⟩

/-- Equality with all 54 existing public cells, including ordered R slots
and the exact centering constants.-/
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
