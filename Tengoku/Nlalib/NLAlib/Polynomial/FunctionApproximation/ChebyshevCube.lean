import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compactness and integration on the Chebyshev cube

These finite-dimensional support facts allow arbitrary laws on the closed
cube, including atoms on its boundary, to use continuous-observable estimates.
-/

noncomputable section

open Set MeasureTheory

namespace NLAlib

/-- The actual closed Chebyshev cube is compact in its Euclidean metric.
@isnad1 id=iscompac.0h1v.s5.4f1bdd2d0a7e from=translated src=- shape=f06fbadd vocab=456c77b3
-/
theorem isCompact_chebyshevCube {ι : Type*} [Fintype ι] :
    IsCompact (chebyshevCube ι) := by
  have hc : IsCompact (Set.univ.pi (fun _ : ι => Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  convert hc.image (PiLp.continuous_toLp 2 _) using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, fun i _ => hx i, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i (Set.mem_univ i)

/-- Every continuous-on-cube observable is integrable for any finite law
supported on the cube.
@isnad1 id=integrab.2h3v.s8.a982dd07bd12 from=translated src=- shape=e8a6ab7a vocab=4a6568ad
-/
theorem integrable_of_ae_mem_chebyshevCube_of_continuousOn
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube ι) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ContinuousOn f (chebyshevCube ι)) : Integrable f μ := by
  have hi := hf.integrableOn_compact (μ := μ) isCompact_chebyshevCube
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi

end NLAlib
