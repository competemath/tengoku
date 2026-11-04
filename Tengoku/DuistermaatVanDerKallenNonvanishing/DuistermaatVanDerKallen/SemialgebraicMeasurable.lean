import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ComplexSemialgebraic
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Measurability of the finite Boolean polynomial-sign definition and its
complex-coordinate counterpart. These facts have no projection or Hardt premise. -/

namespace DuistermaatVanDerKallen

theorem IsSemialgebraic.measurableSet {ι : Type*} [Countable ι]
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) : MeasurableSet S := by
  induction hS with
  | nonneg p => exact (isClosed_le continuous_const p.continuous_eval).measurableSet
  | inter _ _ hs ht => exact hs.inter ht
  | union _ _ hs ht => exact hs.union ht
  | compl _ hs => exact hs.compl

theorem IsComplexSemialgebraic.measurableSet {ι : Type*} [Countable ι]
    {S : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S) : MeasurableSet S := by
  have h := (IsSemialgebraic.measurableSet hS).preimage
    (complexCoordinatesHomeomorph ι).symm.continuous.measurable
  have he : (complexCoordinatesHomeomorph ι).symm ⁻¹' (complexCoordinates ⁻¹' S) = S := by
    ext z
    simp [complexCoordinatesHomeomorph]
  rwa [he] at h

end DuistermaatVanDerKallen
