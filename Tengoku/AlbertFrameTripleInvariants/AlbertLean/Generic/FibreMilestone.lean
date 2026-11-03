import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FullOrbitFibre
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.WitnessChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A nonempty lawful fibre classified by one rational bit

The exact accepted witness pair establishes that the detector-separated
fixed-fibre theorem has an instance. All equivalences below use actual full
Albert automorphisms of ordered public triples. Their domain is the explicit
open residual fibre of `witnessChart1`, not the space of arbitrary frames.
-/

noncomputable section

namespace AlbertLean.Generic.FibreMilestone

open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.FullOrbitFibre
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction

/--
@isnad1 id=infibre.0h0v.s2.1df207b9eb0c from=translated src=- shape=deeaf44f vocab=6474662c
-/
theorem witnessM_inFibre : InFibre witnessChart1 (residualPairOfChart witnessChartM) :=
  ⟨witnessChartM_open, witnessCharts_sameResidualBase⟩

/--
@isnad1 id=eq.0h0v.s3.ff4d6891e854 from=translated src=- shape=9813dc7c vocab=1ab4d000
-/
theorem fibreTriple_witnessM :
    fibreTriple witnessChart1 (residualPairOfChart witnessChartM) =
      chartWitnessTriple witnessChartM := by
  unfold fibreTriple
  rw [← witnessChartM_eq_reinsert]

/-- The canonical swapped representative is separated without evaluating
its inverse matrix or recomputing either accepted detector value.
@isnad1 id=ne.0h0v.s3.47dfb3773090 from=translated src=- shape=8bb8ffd8 vocab=d1fc43a7
-/
theorem witness_rootSwap_detector_ne :
    traceCubeDetector (chartWitnessTriple witnessChart1) ≠
      traceCubeDetector (chartWitnessTriple
        (rootSwappedChart witnessChart1 witnessChart1_open)) := by
  apply representative_separation_of_witness witnessChart1 witnessChart1_open
    (residualPairOfChart witnessChartM) witnessM_inFibre
  rw [fibreTriple_witnessM]
  exact witnessCharts_detector_ne

/-- Every point of this exhibited open fibre is lawful. Its induced full
automorphism equivalence is exactly equality of trace-cube detector values.
@isnad1 id=and.2h2v.s5.06b755bef569 from=translated src=- shape=1b5e934e vocab=969b346c
-/
theorem witness_fibre_classification (Q R : ResidualPair ℚ)
    (hQ : InFibre witnessChart1 Q) (hR : InFibre witnessChart1 R) :
    LawfulFrameTriple (fibreTriple witnessChart1 Q) ∧
    LawfulFrameTriple (fibreTriple witnessChart1 R) ∧
    (FullRelated (fibreTriple witnessChart1 Q) (fibreTriple witnessChart1 R) ↔
      traceCubeDetector (fibreTriple witnessChart1 Q) =
        traceCubeDetector (fibreTriple witnessChart1 R)) :=
  ⟨lawful_of_inFibre _ witnessChart1_lawful Q hQ,
    lawful_of_inFibre _ witnessChart1_lawful R hR,
    fullRelated_iff_detector _ witnessChart1_open witness_rootSwap_detector_ne Q R hQ hR⟩

/-- Both detector values occur in this same lawful fibre and cannot be
identified by any full Albert automorphism.
@isnad1 id=ex.0h0v.s5.3385c4e616fd from=translated src=- shape=c13f18e3 vocab=e681e422
-/
theorem witness_fibre_has_two_classes :
    ∃ Q R : ResidualPair ℚ,
      InFibre witnessChart1 Q ∧ InFibre witnessChart1 R ∧
      LawfulFrameTriple (fibreTriple witnessChart1 Q) ∧
      LawfulFrameTriple (fibreTriple witnessChart1 R) ∧
      ¬ FullRelated (fibreTriple witnessChart1 Q) (fibreTriple witnessChart1 R) := by
  refine ⟨residualPairOfChart witnessChart1, residualPairOfChart witnessChartM,
    original_inFibre _ witnessChart1_open, witnessM_inFibre, ?_, ?_, ?_⟩
  · simpa [fibreTriple] using witnessChart1_lawful
  · rw [fibreTriple_witnessM]
    exact witnessChartM_lawful
  · apply not_fullRelated_of_traceCubeDetector_ne
    simpa [fibreTriple, ← witnessChartM_eq_reinsert] using witnessCharts_detector_ne

/-- Every point of the exhibited fibre has a normalized detector equal to
zero or one, and every rational-valued full invariant is affine in that bit.
@isnad1 id=other.2h2v.s6.1ad0ac184b8f from=translated src=- shape=0aab8f26 vocab=40ff7cc3
-/
theorem witness_fibre_invariant_affine (Q : ResidualPair ℚ)
    (hQ : InFibre witnessChart1 Q) (f : WitnessTriple → ℚ)
    (hf : ∀ {U V}, FullRelated U V → f U = f V) :
    let X₀ := chartWitnessTriple witnessChart1
    let X₁ := chartWitnessTriple (rootSwappedChart witnessChart1 witnessChart1_open)
    let Y := fibreTriple witnessChart1 Q
    (detectorBit X₀ X₁ Y = 0 ∨ detectorBit X₀ X₁ Y = 1) ∧
      f Y = f X₀ + (f X₁ - f X₀) * detectorBit X₀ X₁ Y := by
  exact ⟨detectorBit_zero_or_one witness_rootSwap_detector_ne
      (fullRelated_cover _ witnessChart1_open Q hQ),
    invariant_affine_in_detector witness_rootSwap_detector_ne
      (fullRelated_cover _ witnessChart1_open Q hQ) f hf⟩

end AlbertLean.Generic.FibreMilestone
