import Tengoku.SingularityCompleteLean.Singularity.CompactBoundary
import Tengoku.Seed.MeasureTheory.MeasurableSpace.Embedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport from the geometric boundary in the sphere to the real projective line

The boundary inclusion is a measurable embedding. A measurable inverse on its
range transfers supported measures, group translates, stationarity, and measure
classes. Its values off the boundary are irrelevant to supported measures.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical MatrixGroups

namespace Singularity

/-- The compact real boundary inclusion is a closed embedding.
@isnad1 id=isclosed.0h0v.s4.577f1da1f58d from=translated src=- shape=324b2a5c vocab=69687a90
-/
theorem isClosedEmbedding_compactBoundaryEmbedding :
    Topology.IsClosedEmbedding compactBoundaryEmbedding :=
  continuous_compactBoundaryEmbedding.isClosedEmbedding compactBoundaryEmbedding_injective

/-- The boundary inclusion is also an embedding of measurable spaces.
@isnad1 id=measurab.0h0v.s4.9569436a6e93 from=translated src=- shape=324b2a5c vocab=ec55be0f
-/
theorem measurableEmbedding_compactBoundaryEmbedding :
    MeasurableEmbedding compactBoundaryEmbedding :=
  isClosedEmbedding_compactBoundaryEmbedding.measurableEmbedding

/-- A measurable inverse of the boundary inclusion, extended arbitrarily off the boundary.-/
def compactBoundaryRetraction : OnePoint ℂ → OnePoint ℝ :=
  measurableEmbedding_compactBoundaryEmbedding.invFun

/--
@isnad1 id=measurab.0h0v.s4.650c369d25be from=translated src=- shape=324b2a5c vocab=15611499
-/
theorem measurable_compactBoundaryRetraction : Measurable compactBoundaryRetraction :=
  measurableEmbedding_compactBoundaryEmbedding.measurable_invFun

/-- Retraction recovers every real projective point.
@isnad1 id=eq.0h1v.s3.9ac4d039eaf0 from=translated src=- shape=e9e6e124 vocab=5bf4df5b
-/
theorem compactBoundaryRetraction_embedding (p : OnePoint ℝ) :
    compactBoundaryRetraction (compactBoundaryEmbedding p) = p :=
  measurableEmbedding_compactBoundaryEmbedding.leftInverse_invFun p

/-- On the geometric boundary the inverse also reconstructs the original sphere point.
@isnad1 id=eq.1h1v.s4.baa517fb008a from=translated src=- shape=d8016c2d vocab=852cdb81
-/
theorem compactBoundaryEmbedding_retraction {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) :
    compactBoundaryEmbedding (compactBoundaryRetraction p) = p := by
  rw [← compactBoundaryEmbedding_range] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [compactBoundaryRetraction_embedding]

/-- Retraction is equivariant on the geometric boundary.
@isnad1 id=eq.1h2v.s8.8334b36c4643 from=translated src=- shape=621dea47 vocab=e6e2e8b5
-/
theorem compactBoundaryRetraction_smul (g : SL(2, ℝ)) {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) :
    compactBoundaryRetraction (g • p) = g • compactBoundaryRetraction p := by
  apply compactBoundaryEmbedding_injective
  rw [compactBoundaryEmbedding_retraction (compactHyperbolicBoundary_smul g hp),
    compactBoundaryEmbedding_smul, compactBoundaryEmbedding_retraction hp]

/-- Express a measure on the sphere boundary as a measure on the real projective line.-/
def realProjectiveMeasure (ν : Measure (OnePoint ℂ)) : Measure (OnePoint ℝ) :=
  Measure.map compactBoundaryRetraction ν

/-- The retraction preserves probability measures.
@isnad1 id=isprobab.0h1v.s5.630425dad8da from=translated src=- shape=0979ea19 vocab=37aeef2e
-/
theorem realProjectiveMeasure_probability (ν : Measure (OnePoint ℂ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (realProjectiveMeasure ν) := by
  exact (Measure.isProbabilityMeasure_map_iff measurable_compactBoundaryRetraction.aemeasurable).mpr
    inferInstance

/-- Supported measures can be reconstructed exactly from their real projective transport.
@isnad1 id=eq.1h1v.s7.a51bef92971c from=translated src=- shape=aa494b0e vocab=a739a9b2
-/
theorem realProjectiveMeasure_reconstruct (ν : Measure (OnePoint ℂ))
    (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary) :
    Measure.map compactBoundaryEmbedding (realProjectiveMeasure ν) = ν := by
  rw [realProjectiveMeasure, Measure.map_map continuous_compactBoundaryEmbedding.measurable
    measurable_compactBoundaryRetraction]
  calc
    _ = Measure.map id ν := Measure.map_congr (hsupp.mono (fun _ hp => compactBoundaryEmbedding_retraction hp))
    _ = ν := Measure.map_id

/-- Transport commutes with group pushforward for every boundary-supported measure.
@isnad1 id=eq.1h2v.s9.6cb7a93ddd55 from=translated src=- shape=acd9c1c2 vocab=6342442c
-/
theorem realProjectiveMeasure_map (ν : Measure (OnePoint ℂ))
    (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary) (g : SL(2, ℝ)) :
    realProjectiveMeasure (Measure.map (fun p : OnePoint ℂ => g • p) ν) =
      Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) := by
  rw [realProjectiveMeasure, Measure.map_map measurable_compactBoundaryRetraction
    (continuous_const_smul g).measurable, realProjectiveMeasure,
    Measure.map_map (continuous_const_smul g).measurable measurable_compactBoundaryRetraction]
  exact Measure.map_congr (hsupp.mono (fun _ hp => compactBoundaryRetraction_smul g hp))

/-- Equivalence with every translate is preserved by boundary transport.
@isnad1 id=and.2h3v.s13.7ab6bd362da6 from=translated src=- shape=5c022a26 vocab=0997ac79
-/
theorem realProjectiveMeasure_translate_equivalent (Γ : Subgroup SL(2, ℝ))
    (ν : Measure (OnePoint ℂ)) (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary)
    (hequiv : ∀ g : Γ, Measure.map (fun p : OnePoint ℂ => g • p) ν ≪ ν ∧
      ν ≪ Measure.map (fun p : OnePoint ℂ => g • p) ν) (g : Γ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) ≪ realProjectiveMeasure ν ∧
      realProjectiveMeasure ν ≪ Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) := by
  have h := hequiv g
  have he := realProjectiveMeasure_map ν hsupp (g : SL(2, ℝ))
  change realProjectiveMeasure (Measure.map (fun p : OnePoint ℂ => g • p) ν) =
    Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) at he
  rw [← he]
  exact ⟨h.1.map measurable_compactBoundaryRetraction, h.2.map measurable_compactBoundaryRetraction⟩

end Singularity
