import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ChartBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualActionF0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The chart action in the accepted rational Albert coordinates

This module is the final acyclic join between the residual chart and the
actual `AlbertLean.JordanAut`.  The public coordinate values below are the
images of the two source encoders and the literal diagonal coordinates under
the audited structured-to-F0 equivalence.  The same residual matrix acts on
the chart and on all three kinds of values.
-/

noncomputable section

namespace AlbertLean.Generic.ResidualAction

open AlbertLean
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ChartBridge

/-- The first chart element as a value of the accepted public `Coord` type.-/
def f0EncoderA (x : ExplicitFrameChart ℚ) : Coord :=
  structuredEquiv (encoderA x)

/-- The second chart element as a value of the accepted public `Coord` type.-/
def f0EncoderB (x : ExplicitFrameChart ℚ) : Coord :=
  structuredEquiv (encoderB x)

/-- A literal source diagonal as a value of the accepted public `Coord` type.-/
def f0Diagonal (d1 d2 d3 : ℚ) : Coord :=
  structuredEquiv (diagonal d1 d2 d3)

/-- The actual F0 Albert automorphism transports the first chart encoder
exactly along the residual chart action.
@isnad1 id=eq.0h2v.s7.2eea150111dc from=translated src=- shape=42857b74 vocab=fdca1d3a
-/
theorem jordanAut_encoderA_actChart
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    jordanAut G (f0EncoderA x) = f0EncoderA (actChart G x) := by
  change f0LinearEquiv G (structuredEquiv (encoderA x)) =
    structuredEquiv (encoderA (actChart G x))
  rw [f0LinearEquiv_apply, LinearEquiv.symm_apply_apply,
    encoderA_actChart]

/-- The actual F0 Albert automorphism transports the second chart encoder
exactly along the residual chart action.
@isnad1 id=eq.0h2v.s7.e9aa6727daf6 from=translated src=- shape=42857b74 vocab=6d006de3
-/
theorem jordanAut_encoderB_actChart
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    jordanAut G (f0EncoderB x) = f0EncoderB (actChart G x) := by
  change f0LinearEquiv G (structuredEquiv (encoderB x)) =
    structuredEquiv (encoderB (actChart G x))
  rw [f0LinearEquiv_apply, LinearEquiv.symm_apply_apply,
    encoderB_actChart]

/-- Every literal diagonal public value is fixed by the same actual F0
Albert automorphism.
@isnad1 id=eq.0h4v.s7.d8f127ee929a from=translated src=- shape=709d21ea vocab=5cd88eec
-/
theorem jordanAut_f0Diagonal
    (G : DetOneMatrix ℚ) (d1 d2 d3 : ℚ) :
    jordanAut G (f0Diagonal d1 d2 d3) = f0Diagonal d1 d2 d3 := by
  change f0LinearEquiv G (structuredEquiv (diagonal d1 d2 d3)) =
    structuredEquiv (diagonal d1 d2 d3)
  rw [f0LinearEquiv_apply, LinearEquiv.symm_apply_apply]
  have h := sourceAut_diagonal G d1 d2 d3
  change act G (diagonal d1 d2 d3) = diagonal d1 d2 d3 at h
  rw [h]

/-- Load-bearing join: one actual rational unital Albert automorphism fixes
all diagonal values and carries both public chart values to the values of the
residually transformed chart.
@isnad1 id=and.0h2v.s9.ee5a55e8eb0b from=translated src=- shape=cc2e0a6f vocab=d6f9e451
-/
theorem jordanAut_actChart
    (G : DetOneMatrix ℚ) (x : ExplicitFrameChart ℚ) :
    (∀ d1 d2 d3 : ℚ,
      jordanAut G (f0Diagonal d1 d2 d3) = f0Diagonal d1 d2 d3) ∧
    jordanAut G (f0EncoderA x) = f0EncoderA (actChart G x) ∧
    jordanAut G (f0EncoderB x) = f0EncoderB (actChart G x) := by
  exact ⟨jordanAut_f0Diagonal G,
    jordanAut_encoderA_actChart G x, jordanAut_encoderB_actChart G x⟩

end AlbertLean.Generic.ResidualAction
