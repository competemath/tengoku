module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.ThreeBlockDensityIdentity

/-!
# Three-block conditional-density factorization

This module proves the three-block criterion used by the four-block intersection theorem: for a
measurable finite density on a product of standard Borel spaces, the first two blocks are
conditionally independent given the third exactly when the density satisfies the
marginal-density identity, equivalently when it factors through the conditioning block. The
density-theoretic equivalence of those two conditions lives in `ThreeBlockDensityIdentity`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection

universe uA uB uC

section ConditionalIndependence

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
variable [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
variable (muA : Measure A) (muB : Measure B) (muC : Measure C)
variable [SigmaFinite muA] [SigmaFinite muB] [SigmaFinite muC]
variable {d : ThreeBlock A B C → ℝ≥0∞}
variable [IsFiniteMeasure ((threeBlockReference muA muB muC).withDensity d)]

/-- Conditional independence of the first two coordinates given the third coordinate implies
the cross-multiplied identity for any measurable finite density relative to a product reference. -/
theorem threeBlockDensityIdentity_of_condIndepFun (hd : Measurable d)
    (hci : CondIndepFun
      (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
      measurable_thirdThreeCoord.comap_le
      (@firstThreeCoord A B C) (@secondThreeCoord A B C)
      ((threeBlockReference muA muB muC).withDensity d)) :
    ThreeBlockDensityIdentity muA muB muC d := by
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI := hA
      exact ae_of_all _ fun q ↦ isEmptyElim q.1
  | inr hA =>
      letI := hA
      cases isEmpty_or_nonempty B with
      | inl hB =>
          letI := hB
          exact ae_of_all _ fun q ↦ isEmptyElim q.2.1
      | inr hB =>
          letI := hB
          exact (threeBlockDensityIdentity_iff_ratio muA muB muC hd).2
            ((condIndepFun_threeBlock_iff_ratio muA muB muC hd).1 hci)

/-- The cross-multiplied identity for a measurable finite product density implies conditional
independence of the first two coordinates given the third coordinate. -/
theorem condIndepFun_threeBlock_of_densityIdentity (hd : Measurable d)
    (hid : ThreeBlockDensityIdentity muA muB muC d) :
    CondIndepFun
      (MeasurableSpace.comap (@thirdThreeCoord A B C) inferInstance)
      measurable_thirdThreeCoord.comap_le
      (@firstThreeCoord A B C) (@secondThreeCoord A B C)
      ((threeBlockReference muA muB muC).withDensity d) := by
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI := hA
      rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
        measurable_firstThreeCoord measurable_secondThreeCoord]
      intro s t hs ht
      exact ae_of_all _ fun q ↦ isEmptyElim q.1
  | inr hA =>
      letI := hA
      cases isEmpty_or_nonempty B with
      | inl hB =>
          letI := hB
          rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
            measurable_firstThreeCoord measurable_secondThreeCoord]
          intro s t hs ht
          exact ae_of_all _ fun q ↦ isEmptyElim q.2.1
      | inr hB =>
          letI := hB
          exact (condIndepFun_threeBlock_iff_ratio muA muB muC hd).2
            ((threeBlockDensityIdentity_iff_ratio muA muB muC hd).1 hid)

end ConditionalIndependence

end Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
