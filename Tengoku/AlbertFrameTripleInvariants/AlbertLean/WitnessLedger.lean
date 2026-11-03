import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessPairs
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessJoint00
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessJoint01
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessJoint02

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

/-- All 27 raw joint moments agree; diagonal slots are checked separately.
@isnad1 id=eq.0h3v.s5.559eba0e8c3d from=translated src=- shape=80427cb0 vocab=eadaff7c
-/
theorem witnessSameJoint (i j l : Fin 3) :
    traceForm (projector theta1E i)
      (structuredProduct (projector theta1F j) (projector theta1K l)) =
    traceForm (projector thetaME i)
      (structuredProduct (projector thetaMF j) (projector thetaMK l)) := by
  fin_cases i
  · exact witnessSameJoint00 j l
  · exact witnessSameJoint01 j l
  · exact witnessSameJoint02 j l

/-- The complete centered ledger follows from raw joint and pair moment equality.
@isnad1 id=eq.0h0v.s2.f59f3ea8a105 from=translated src=- shape=7bded134 vocab=fd94c261
-/
theorem witnessSameLedger : ledger witnessTheta1 = ledger witnessThetaM := by
  simp only [ledger]
  rw [Ledger.mk.injEq]
  refine ⟨witnessSameP, witnessSameQ, witnessSameR, ?_⟩
  funext i j l
  have hp := congrFun (congrFun witnessSameP i) j
  have hq := congrFun (congrFun witnessSameQ j) l
  have hr := congrFun (congrFun witnessSameR l) i
  change traceForm (projector theta1E i)
      (structuredProduct (projector theta1F j) (projector theta1K l)) -
      ((ledger witnessTheta1).P i j + (ledger witnessTheta1).Q j l +
        (ledger witnessTheta1).R l i) / 3 + 2 / 9 =
    traceForm (projector thetaME i)
      (structuredProduct (projector thetaMF j) (projector thetaMK l)) -
      ((ledger witnessThetaM).P i j + (ledger witnessThetaM).Q j l +
        (ledger witnessThetaM).R l i) / 3 + 2 / 9
  rw [witnessSameJoint i j l, hp, hq, hr]

end AlbertLean
