import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessLedger
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessFrames
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessDetector
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.AutomorphismLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

/--
@isnad1 id=not.0h0v.s3.b7f0d103e66d from=translated src=- shape=94301928 vocab=94029dff
-/
theorem noUnitalProductAutomorphismTransports :
    ¬ ∃ g : JordanAut, Transports g witnessTheta1 witnessThetaM := by
  rintro ⟨g, hg⟩
  exact witnessDetectorValues.2.2
    (traceCubeDetector_invariant g witnessTheta1 witnessThetaM hg).symm

/--
@isnad1 id=combined.0h0v.s0.dc7e3c5dd717 from=translated src=- shape=45709ebd vocab=dc7e3c5d
-/
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
