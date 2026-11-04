import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ComplexSemialgebraic
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Measurability of the finite Boolean polynomial-sign definition and its
complex-coordinate counterpart. These facts have no projection or Hardt premise. -/

namespace DuistermaatVanDerKallen

/--
@isnad1 id=measurab.1h2v.s4.1812f634eff2 from=translated src=- shape=6d35c55d vocab=820262be
-/
theorem IsSemialgebraic.measurableSet {ι : Type*} [Countable ι]
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) : MeasurableSet S := by
  induction hS with
  | nonneg p => exact (isClosed_le continuous_const p.continuous_eval).measurableSet
  | inter _ _ hs ht => exact hs.inter ht
  | union _ _ hs ht => exact hs.union ht
  | compl _ hs => exact hs.compl

/--
@isnad1 id=measurab.1h2v.s4.240f84a62a00 from=translated src=- shape=6d35c55d vocab=0bb52116
-/
theorem IsComplexSemialgebraic.measurableSet {ι : Type*} [Countable ι]
    {S : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S) : MeasurableSet S := by
  have h := (IsSemialgebraic.measurableSet hS).preimage
    (complexCoordinatesHomeomorph ι).symm.continuous.measurable
  have he : (complexCoordinatesHomeomorph ι).symm ⁻¹' (complexCoordinates ⁻¹' S) = S := by
    ext z
    simp [complexCoordinatesHomeomorph]
  rwa [he] at h

end DuistermaatVanDerKallen
