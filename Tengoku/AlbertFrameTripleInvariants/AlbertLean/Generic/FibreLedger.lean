import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FibreMilestone
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessLedger

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The public ledger on the exhibited residual fibre

The residual base is a coordinate statement: it fixes the residual moment and
the sum of the two determinant roots.  It is not identified here with the
public pair-and-centered ledger.  Instead, the accepted witness equality
`witnessSameLedger` supplies one same-ledger point on the other detector branch.
The full-automorphism cover then transports that equality to the canonical
root-swapped representative and from there to every point of the fibre.
-/

noncomputable section

namespace AlbertLean.Generic.FibreLedger

open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.FullOrbitFibre
open AlbertLean.Generic.FibreMilestone
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction

/-- A detector-separated member of a two-class cover must lie on the second
branch.
@isnad1 id=fullrela.2h3v.s4.c0c3e1c07289 from=translated src=- shape=3255fc0f vocab=504c94e9
-/
theorem right_of_cover_of_detector_ne {X₀ X₁ Y : WitnessTriple}
    (hdet : traceCubeDetector X₀ ≠ traceCubeDetector Y)
    (hcover : FullRelated X₀ Y ∨ FullRelated X₁ Y) :
    FullRelated X₁ Y := by
  rcases hcover with h | h
  · exact (hdet h.traceCubeDetector_eq).elim
  · exact h

/-- If the two representatives of a cover have the same public ledger, every
covered point has that ledger.  This is the general ledger transfer step.
@isnad1 id=eq.2h3v.s4.711272c1b50f from=translated src=- shape=1b19251a vocab=778acd6f
-/
theorem ledger_eq_of_cover {X₀ X₁ Y : WitnessTriple}
    (hroot : ledger X₁ = ledger X₀)
    (hcover : FullRelated X₀ Y ∨ FullRelated X₁ Y) :
    ledger Y = ledger X₀ := by
  rcases hcover with h | h
  · exact h.ledger_eq.symm
  · exact h.ledger_eq.symm.trans hroot

/-- A same-ledger witness separated from the first representative forces the
two representatives themselves to have the same public ledger.
@isnad1 id=eq.3h3v.s5.289a041b31cd from=translated src=- shape=afe99691 vocab=010f39a8
-/
theorem root_ledger_eq_of_separating_witness {X₀ X₁ Y : WitnessTriple}
    (hdet : traceCubeDetector X₀ ≠ traceCubeDetector Y)
    (hledger : ledger X₀ = ledger Y)
    (hcover : FullRelated X₀ Y ∨ FullRelated X₁ Y) :
    ledger X₁ = ledger X₀ := by
  exact (right_of_cover_of_detector_ne hdet hcover).ledger_eq.trans hledger.symm

/-- A fixed residual fibre has constant public ledger once one explicitly
same-ledger point is known to occupy the alternate detector branch.  The
same-residual-base hypotheses enter only through `fullRelated_cover`; public
ledger equality remains a separate premise.
@isnad1 id=eq.5h3v.s5.674a212bb1b7 from=translated src=- shape=5cfed005 vocab=d0a26d1c
-/
theorem fibre_ledger_eq_of_separating_witness (x : ExplicitFrameChart ℚ)
    (hx : ResidualOpen (residualPairOfChart x))
    (W : ResidualPair ℚ) (hW : InFibre x W)
    (hdet : traceCubeDetector (chartWitnessTriple x) ≠
      traceCubeDetector (fibreTriple x W))
    (hledger : ledger (chartWitnessTriple x) = ledger (fibreTriple x W))
    (Q : ResidualPair ℚ) (hQ : InFibre x Q) :
    ledger (fibreTriple x Q) = ledger (chartWitnessTriple x) := by
  apply ledger_eq_of_cover
  · exact root_ledger_eq_of_separating_witness hdet hledger
      (fullRelated_cover x hx W hW)
  · exact fullRelated_cover x hx Q hQ

/-- The chart readers identify the accepted coordinate pair with the two
public witness triples whose complete ledgers were proved equal.
@isnad1 id=eq.0h0v.s3.2347703134e4 from=translated src=- shape=51699e26 vocab=34ec1596
-/
theorem witnessCharts_ledger_eq :
    ledger (chartWitnessTriple witnessChart1) =
      ledger (chartWitnessTriple witnessChartM) := by
  rw [chartWitnessTriple_witnessChart1, chartWitnessTriple_witnessChartM]
  exact witnessSameLedger

/-- Detector separation rules out the original branch for the accepted second
witness, so the residual cover forces the canonical root-swapped branch.
@isnad1 id=fullrela.0h0v.s2.0167d2041db1 from=translated src=- shape=2bfd6d90 vocab=77faaae6
-/
theorem witness_rootSwap_fullRelated_witnessM :
    FullRelated
      (chartWitnessTriple (rootSwappedChart witnessChart1 witnessChart1_open))
      (chartWitnessTriple witnessChartM) := by
  apply right_of_cover_of_detector_ne witnessCharts_detector_ne
  simpa only [fibreTriple_witnessM] using
    (fullRelated_cover witnessChart1 witnessChart1_open
      (residualPairOfChart witnessChartM) witnessM_inFibre)

/-- The genuine normalized root exchange has the original public ledger in
the exhibited chart.  This conclusion uses the accepted public ledger theorem;
it is not inferred from equality of residual coordinate bases.
@isnad1 id=eq.0h0v.s3.fd7efe0b28f3 from=translated src=- shape=06cf59fb vocab=b49b5683
-/
theorem witness_rootSwap_ledger_eq :
    ledger
        (chartWitnessTriple
          (rootSwappedChart witnessChart1 witnessChart1_open)) =
      ledger (chartWitnessTriple witnessChart1) := by
  exact witness_rootSwap_fullRelated_witnessM.ledger_eq.trans
    witnessCharts_ledger_eq.symm

/-- Every point of the exhibited rational lawful residual fibre has exactly
the original public moment ledger.
@isnad1 id=eq.1h1v.s4.d27dfd1fae67 from=translated src=- shape=4e4712fa vocab=a395f99d
-/
theorem witness_fibre_ledger_eq_original (Q : ResidualPair ℚ)
    (hQ : InFibre witnessChart1 Q) :
    ledger (fibreTriple witnessChart1 Q) = ledger witnessTheta1 := by
  calc
    ledger (fibreTriple witnessChart1 Q) =
        ledger (chartWitnessTriple witnessChart1) :=
      ledger_eq_of_cover witness_rootSwap_ledger_eq
        (fullRelated_cover witnessChart1 witnessChart1_open Q hQ)
    _ = ledger witnessTheta1 := by rw [chartWitnessTriple_witnessChart1]

/-- The ledger conclusion and lawfulness are recorded together for the
exhibited fibre.
@isnad1 id=and.1h1v.s4.f6a339093dfe from=translated src=- shape=79eb0527 vocab=87a0eb1b
-/
theorem witness_fibre_lawful_same_original_ledger (Q : ResidualPair ℚ)
    (hQ : InFibre witnessChart1 Q) :
    LawfulFrameTriple (fibreTriple witnessChart1 Q) ∧
      ledger (fibreTriple witnessChart1 Q) = ledger witnessTheta1 :=
  ⟨lawful_of_inFibre witnessChart1 witnessChart1_lawful Q hQ,
    witness_fibre_ledger_eq_original Q hQ⟩

end AlbertLean.Generic.FibreLedger
