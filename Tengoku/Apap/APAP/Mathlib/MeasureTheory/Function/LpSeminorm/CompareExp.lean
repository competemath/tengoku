module

public import Tengoku

public section

open ENNReal

namespace MeasureTheory
variable {𝕜 α : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]

/-- Hölder's inequality.
@isnad1 id=le.2h9v.s7.94ccb0f41d4e from=translated src=- shape=1a4dfd91 vocab=b1fcd0d5
-/
theorem eLpNorm_mul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f g : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) [HolderTriple p q r] :
    eLpNorm (f * g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  simpa using eLpNorm_smul_le_mul_eLpNorm hg hf

end MeasureTheory
