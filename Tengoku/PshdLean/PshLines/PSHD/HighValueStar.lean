import Tengoku.PshdLean.PshLines.PSHD.ChartStar
import Tengoku.PshdLean.PshLines.PSHD.ComponentSections
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The high-value star lemma

The uniform finite-energy conclusion of `pshd-vibe`, Lemma 1.3.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The radius--chart space has real dimension one below the ambient space.-/
theorem chartParameter_finrank {e : E} (he : ‖e‖ = 1) :
    Module.finrank ℝ (ℝ × (ℂ ∙ e)ᗮ) =
      2 * (Module.finrank ℂ E - 1) + 1 := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; exact one_ne_zero)
  have h := (ℂ ∙ e).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he0] at h
  rw [Module.finrank_prod, Module.finrank_self,
    ← Module.finrank_mul_finrank ℝ ℂ (ℂ ∙ e)ᗮ, Complex.finrank_real_complex]
  omega

/-- High values on all affine complex lines carry a probability measure with
uniform finite Riesz energy of order twice the complex dimension minus two.
The constant is independent of the function, domain and center.-/
theorem exists_uniform_highValue_star
    [MeasurableSpace E] [BorelSpace E]
    (hn : 2 ≤ Module.finrank ℂ E) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (u : E → ℝ), Measurable u →
      ∀ (D : Set E) (x : E), closedBall x R ⊆ D →
      (∀ v : E, v ≠ 0 → DiscPshOn (fun z => (u (x + z • v) : EReal))
        ((fun z : ℂ => x + z • v) ⁻¹' D)) →
      ∃ μ : Measure E, IsProbabilityMeasure μ ∧
        μ {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y} = 1 ∧
        rieszEnergy (2 * (Module.finrank ℂ E - 1) : ℕ) μ ≤ C := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have he := NormedSpace.norm_normalize hv
  refine exists_uniform_highValue_star_of_unit he ?_ ?_ hR
  · exact_mod_cast (show 0 < 2 * (Module.finrank ℂ E - 1) by omega)
  · rw [chartParameter_finrank he]
    exact_mod_cast Nat.lt_succ_self (2 * (Module.finrank ℂ E - 1))

/-- The high-value star with the article's connected-component convention
for affine complex-line sections.-/
theorem exists_uniform_highValue_star_of_components
    [MeasurableSpace E] [BorelSpace E]
    (hn : 2 ≤ Module.finrank ℂ E) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (u : E → ℝ), Measurable u →
      ∀ (D : Set E), IsOpen D → ∀ (x : E), closedBall x R ⊆ D →
      (∀ v : E, v ≠ 0 → ∀ z ∈ ((fun t : ℂ => x + t • v) ⁻¹' D),
        DiscPshOn (fun t => (u (x + t • v) : EReal))
          (connectedComponentIn ((fun t : ℂ => x + t • v) ⁻¹' D) z)) →
      ∃ μ : Measure E, IsProbabilityMeasure μ ∧
        μ {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y} = 1 ∧
        rieszEnergy (2 * (Module.finrank ℂ E - 1) : ℕ) μ ≤ C := by
  obtain ⟨C, hCt, hC⟩ := exists_uniform_highValue_star (E := E) hn hR
  refine ⟨C, hCt, ?_⟩
  intro u hum D hD x hball hu
  apply hC u hum D x hball
  intro v hv
  exact discPshOn_of_connectedComponentIn (hD.preimage (by fun_prop)) (hu v hv)

end PshLines.PSHD
