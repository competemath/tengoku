import Tengoku.SingularityCompleteLean.Singularity.GreenSeries
import Tengoku.SingularityCompleteLean.Singularity.MarkovAdjoint
import Tengoku.SingularityCompleteLean.Singularity.WalkKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reflected walks, adjoints, and Green rows

The spectral gap is preserved by taking adjoints. The Green resolvent of the
reflected jump law is the adjoint resolvent, so its kernel is the transposed
original Green kernel. No symmetry of the law is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Gelfand's formula and equality of power norms give adjoint invariance of the radius.
@isnad1 id=eq.0h2v.s11.00a93c44bf9f from=translated src=- shape=dd341d98 vocab=e4b3391b
-/
theorem operator_spectralRadius_adjoint (P : E →L[ℂ] E) :
    spectralRadius ℂ P.adjoint = spectralRadius ℂ P := by
  have he (n : ℕ) : ‖P.adjoint ^ n‖₊ = ‖P ^ n‖₊ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← star_pow, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.nnnorm_map _
  have h := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius P.adjoint
  simp only [he] at h
  exact tendsto_nhds_unique h (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius P)

/-- Taking the adjoint commutes with the Green resolvent.
@isnad1 id=eq.0h2v.s12.c0ad2b37370e from=translated src=- shape=59d56092 vocab=d6cb6e81
-/
theorem green_adjoint (P : E →L[ℂ] E) : (green P).adjoint = green P.adjoint := by
  change star (Ring.inverse (1 - P)) = Ring.inverse (1 - P.adjoint)
  rw [← Ring.inverse_star, star_sub, star_one, ContinuousLinearMap.star_eq_adjoint]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- Reflection preserves the precise operator spectral-gap hypothesis.
@isnad1 id=lt.1h3v.s13.d00fe633a317 from=translated src=- shape=1f66d70c vocab=1fd161c5
-/
theorem reflectedMarkov_spectral_gap (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    spectralRadius ℂ (rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)) < 1 := by
  rw [← rightMarkov_adjoint_eq_reflected, operator_spectralRadius_adjoint]
  exact hgap

/-- The reflected Green operator is exactly the adjoint of the original one.
@isnad1 id=eq.0h3v.s16.efc69d41305e from=translated src=- shape=8524e025 vocab=eaf61b9d
-/
theorem reflected_green_operator (s : Finset Γ) (μ : Γ → ℝ) :
    green (rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)) =
      (green (rightMarkov s μ)).adjoint := by
  rw [← rightMarkov_adjoint_eq_reflected, ← green_adjoint]

variable [MeasurableSingletonClass Γ]

/-- The actual adjoint column has the coordinates of the original Green row.
@isnad1 id=eq.1h5v.s16.1fefdc79bf81 from=translated src=- shape=e8e925f9 vocab=114a9d63
-/
theorem green_adjoint_coefficient (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x a : Γ) :
    (green (rightMarkov s μ)).adjoint (countingDelta x) a = (walkGreen s μ x a : ℂ) := by
  rw [← countingDelta_inner a, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, countingDelta_inner, ← walkGreen_eq_coefficient s μ hgap, Complex.conj_ofReal]

/-- Reflection transposes the path-counting Green kernel.
@isnad1 id=eq.1h5v.s12.0341fa37248d from=translated src=- shape=b2023eaf vocab=be354716
-/
theorem reflected_walkGreen (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    walkGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) x y = walkGreen s μ y x := by
  apply Complex.ofReal_injective
  rw [walkGreen_eq_coefficient _ _ (reflectedMarkov_spectral_gap s μ hgap),
    reflected_green_operator, green_adjoint_coefficient s μ hgap]

end Singularity
