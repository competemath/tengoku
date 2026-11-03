import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms componentSolution_ratio` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeRelated_iff_trace_ratio_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms three_rawSystems_gaugeRelated_pair` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Reconstruction of raw systems up to determinant-one gauge

This composes ordinary matrix results and makes no
Albert-frame, genericity, or automorphism-classification claim.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowGaugeReconstruction

open AlbertLean.Generic.FourRowFrameReduction
open AlbertLean.Generic.FourRowAdjugateSystem
open AlbertLean.Generic.FourRowComponents
open AlbertLean.Generic.FourRowNormalization
open AlbertLean.Generic.FourRowUniqueness (reconstructionDenominator)
open AlbertLean.Generic.FourRowGauge

variable {K : Type*} [Field K]

/-- The explicit reconstruction-denominator open for a raw system.-/
def OnReconstructionOpen {a : Fin 3 → Mat3 K} (S : RawSystem a) : Prop :=
  (reconstructionDenominator (componentU (a 0) (a 1) (a 2))
    (componentV (a 0) (a 1)) ((a 1).det / (a 0).det)
    ((a 2).det / (a 0).det) (Matrix.trace (ratio S))).det ≠ 0

private theorem a_det_ne_zero {a : Fin 3 → Mat3 K} (S : RawSystem a)
    (i : Fin 3) : (a i).det ≠ 0 := by
  rw [← det_b_eq S i]
  exact S.b_ne i

/-- Every raw system on the displayed open supplies a component solution at
its gauge-invariant normalized ratio.-/
theorem componentSolution_ratio {a : Fin 3 → Mat3 K} (S : RawSystem a)
    (hopen : OnReconstructionOpen S) :
    ComponentSolution (a 0) (a 1) (a 2) (ratio S) := by
  have hnorm : normalizedX (a 0) (S.b 0) (S.b 1) = ratio S :=
    normalizedX_eq_ratio (a 0) (S.b 0) (S.b 1) (a_det_ne_zero S 0)
  rw [← hnorm]
  apply componentSolution_of_adjugate_equations a S.b S.c S.b_ne
    S.equations S.b_sum S.c_sum
  simpa only [OnReconstructionOpen, hnorm] using hopen

/-- On the reconstruction open, equality of the scalar traces is exactly
determinant-one gauge relatedness.-/
theorem gaugeRelated_iff_trace_ratio_eq {a : Fin 3 → Mat3 K}
    (S T : RawSystem a) (hS : OnReconstructionOpen S)
    (hT : OnReconstructionOpen T) :
    GaugeRelated S T ↔ Matrix.trace (ratio S) = Matrix.trace (ratio T) := by
  constructor
  · intro hg
    exact congrArg Matrix.trace ((gaugeRelated_iff_ratio_eq S T).mp hg)
  · intro htrace
    apply (gaugeRelated_iff_ratio_eq S T).mpr
    exact eq_of_components_of_trace_eq (a 0) (a 1) (a 2)
      (a_det_ne_zero S 0) (a_det_ne_zero S 1) (a_det_ne_zero S 2)
      (componentSolution_ratio S hS) (componentSolution_ratio T hT) htrace

/-- Any three raw systems over the same fixed first components and on the
reconstruction open contain a gauge-related pair.-/
theorem three_rawSystems_gaugeRelated_pair {a : Fin 3 → Mat3 K}
    (S T W : RawSystem a)
    (hS : OnReconstructionOpen S) (hT : OnReconstructionOpen T)
    (hW : OnReconstructionOpen W) :
    GaugeRelated S T ∨ GaugeRelated S W ∨ GaugeRelated T W := by
  rcases three_componentSolutions_pairwise_eq (a 0) (a 1) (a 2)
      (a_det_ne_zero S 0) (a_det_ne_zero S 1) (a_det_ne_zero S 2)
      (ratio S) (ratio T) (ratio W)
      (componentSolution_ratio S hS) (componentSolution_ratio T hT)
      (componentSolution_ratio W hW) with hST | hSW | hTW
  · exact Or.inl ((gaugeRelated_iff_ratio_eq S T).mpr hST)
  · exact Or.inr (Or.inl ((gaugeRelated_iff_ratio_eq S W).mpr hSW))
  · exact Or.inr (Or.inr ((gaugeRelated_iff_ratio_eq T W).mpr hTW))

end AlbertLean.Generic.FourRowGaugeReconstruction
