import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessLedger
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessFrames
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessDetector
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.AutomorphismLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

theorem noUnitalProductAutomorphismTransports :
    ¬ ∃ g : JordanAut, Transports g witnessTheta1 witnessThetaM := by
  rintro ⟨g, hg⟩
  exact witnessDetectorValues.2.2
    (traceCubeDetector_invariant g witnessTheta1 witnessThetaM hg).symm

theorem solution : CombinedTarget where
  productQBilinear := AlbertLean.productQBilinear
  productCommutative := AlbertLean.productCommutative
  unitLaw := AlbertLean.unitLaw
  traceFormSymmetricNondegenerate :=
    AlbertLean.traceFormSymmetricNondegenerate
  traceFormAssociative := AlbertLean.traceFormAssociative
  jordanIdentity := AlbertLean.jordanIdentity
  characteristicIdentity := AlbertLean.characteristicIdentity
  printedInvariantsAgree := AlbertLean.printedInvariantsAgree
  witnessTheta1Lawful := AlbertLean.witnessTheta1Lawful
  witnessThetaMLawful := AlbertLean.witnessThetaMLawful
  witnessSameLedger := AlbertLean.witnessSameLedger
  witnessDetectorValues := AlbertLean.witnessDetectorValues
  detectorFactorThree := AlbertLean.detectorFactorThree
  noUnitalProductAutomorphismTransports :=
    AlbertLean.noUnitalProductAutomorphismTransports

end AlbertLean
