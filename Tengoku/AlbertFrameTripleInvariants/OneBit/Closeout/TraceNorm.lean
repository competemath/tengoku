import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CommutatorGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The detector is three times a cubic norm

For every rational coordinate triple X, with W the word x∘(y∘z) − y∘(x∘z) of its
encoders, tr(W ∘ (W ∘ W)) = 3 · N(W), where N is the cubic norm of the coordinate model.
No frame or trace-zero hypothesis is needed. This is a supporting identity from
`AlbertLean.Generic.CommutatorGeometry`; it is audited but not one of the five selected
theorems. It explains why the detector values of the example, −2591357/62208 and
−1782559/62208, are three times the cubic norms −2591357/186624 and −1782559/186624.
-/

namespace OneBit

/-- Unconditional rational normalization identity for the displayed commutator
word. The cubic norm is the original independent coordinate polynomial.
@isnad1 id=eq.0h1v.s4.c41a93e64f49 from=translated src=- shape=9fc36aa0 vocab=14316a5d
-/
theorem traceCube_eq_three_cubicNorm (X : AlbertLean.WitnessTriple) :
    AlbertLean.traceCubeDetector X = 3 * AlbertLean.cubicNormDetector X :=
  AlbertLean.Generic.CommutatorGeometry.detectorFactorThree_unconditional X

end OneBit
