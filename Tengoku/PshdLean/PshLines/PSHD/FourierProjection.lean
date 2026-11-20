import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.Basic
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fourier transforms of projected measures

The normalization is the analyst's convention of `pshd-vibe`, Lemma 1.4.
The transform reuses mathlib's characteristic function at frequency `-2πξ`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Fourier transform of a measure with the article's `-2π` convention.-/
def measureFourier (μ : Measure E) (ξ : E) : ℂ :=
  charFun μ ((-2 * Real.pi) • ξ)

omit [BorelSpace E] in
/-- The normalized transform is the integral of the usual exponential character.
@isnad1 id=eq.0h3v.s6.dc557ff63ff1 from=translated src=- shape=3c20cf37 vocab=5770ac4b
-/
theorem measureFourier_eq_integral (μ : Measure E) (ξ : E) :
    measureFourier μ ξ =
      ∫ x, Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) ∂μ := by
  simp [measureFourier, charFun_apply, inner_smul_right, mul_comm]

/-- Orthogonal projection of a measure restricts its Fourier transform.
@isnad1 id=eq.0h4v.s10.509475664c85 from=translated src=- shape=768d2539 vocab=451546b0
-/
theorem measureFourier_map_orthogonalProjection (μ : Measure E)
    (H : Submodule ℝ E) [H.HasOrthogonalProjection] (ξ : H) :
    measureFourier (μ.map H.orthogonalProjectionOnto) ξ = measureFourier μ (ξ : E) := by
  simp only [measureFourier, charFun_apply]
  rw [integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  congr 2
  simp

omit [BorelSpace E] in
/-- The transform is bounded by the total mass.
@isnad1 id=le.0h3v.s5.77b6d43b1b4f from=translated src=- shape=5fccae1e vocab=64b6bf8f
-/
theorem norm_measureFourier_le (μ : Measure E) (ξ : E) :
    ‖measureFourier μ ξ‖ ≤ μ.real Set.univ := norm_charFun_le _

/-- The transform is Borel measurable.
@isnad1 id=measurab.0h2v.s5.22b202aaa4e0 from=translated src=- shape=a15f26b8 vocab=ddd60e97
-/
theorem measurable_measureFourier (μ : Measure E) [SFinite μ]
    [SecondCountableTopology E] : Measurable (measureFourier μ) := by
  unfold measureFourier
  exact measurable_charFun.comp (by fun_prop)

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [MeasurableSpace V] [BorelSpace V]

attribute [local instance] InnerProductSpace.complexToReal

omit [BorelSpace V] in
/-- The real inner product convention agrees with the article's Hermitian convention.
@isnad1 id=eq.0h3v.s6.ae92b7d24a8a from=translated src=- shape=4ba3cb6b vocab=1258f4b8
-/
theorem measureFourier_eq_integral_complex (μ : Measure V) (ξ : V) :
    measureFourier μ ξ =
      ∫ x, Complex.exp ((-2 * Real.pi * (inner ℂ x ξ).re : ℝ) * Complex.I) ∂μ := by
  exact measureFourier_eq_integral μ ξ

/-- Fourier restriction for complex subspaces, in particular complex hyperplanes.
@isnad1 id=eq.0h4v.s11.817819b103b6 from=translated src=- shape=a6af11a0 vocab=3bc33f57
-/
theorem measureFourier_map_complexProjection (μ : Measure V)
    (H : Submodule ℂ V) [H.HasOrthogonalProjection] (ξ : H) :
    measureFourier (μ.map H.orthogonalProjectionOnto) ξ = measureFourier μ (ξ : V) := by
  rw [measureFourier_eq_integral_complex, measureFourier_eq_integral_complex,
    integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

end Complex

end PshLines.PSHD
