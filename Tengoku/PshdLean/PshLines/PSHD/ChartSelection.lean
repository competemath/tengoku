import Tengoku.PshdLean.PshLines.PSHD.NormalizedChart
import Tengoku.PshdLean.PshLines.PSHD.CirclePointSelection
import Tengoku.Seed.Analysis.InnerProductSpace.Orthogonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # High-value selection over an affine chart

Concrete Euclidean parameters for the high-value star of `pshd-vibe`, Lemma 1.3.
-/

open Set Metric MeasureTheory

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The normalized affine lift on a perpendicular hyperplane is continuous.-/
theorem continuous_normalized_affineLift {e : E} (he : ‖e‖ = 1) :
    Continuous (fun v : (ℂ ∙ e)ᗮ => NormedSpace.normalize (e + (v : E))) := by
  have hc : Continuous (fun v : (ℂ ∙ e)ᗮ => e + (v : E)) := by fun_prop
  have hi : Continuous (fun v : (ℂ ∙ e)ᗮ => ‖e + (v : E)‖⁻¹) :=
    hc.norm.inv₀ (fun v => norm_ne_zero_iff.mpr (affineLift_ne_zero he
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property)))
  exact hi.smul hc

/-- A Borel high-value point for every radius--chart parameter. Radii are
clamped to the fixed annulus, so the selector is defined on the entire
Euclidean parameter space.-/
theorem exists_highValue_chart_map
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hum : Measurable u) {D : Set E} (x : E)
    {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ D)
    (hu : ∀ v : E, v ≠ 0 → DiscPshOn (fun z => (u (x + z • v) : EReal))
      ((fun z : ℂ => x + z • v) ⁻¹' D))
    {e : E} (he : ‖e‖ = 1) :
    ∃ Ψ : ℝ × (ℂ ∙ e)ᗮ → E, Measurable Ψ ∧ ∀ p,
      u x ≤ u (Ψ p) ∧ ∃ z : ℂ,
        ‖z‖ = max (R / 2) (min R p.1) ∧
        Ψ p = x + z • NormedSpace.normalize (e + (p.2 : E)) := by
  let S := ℝ × (ℂ ∙ e)ᗮ
  let r : S → ℝ := fun p => max (R / 2) (min R p.1)
  let v : S → E := fun p => NormedSpace.normalize (e + (p.2 : E))
  have hr : ∀ p, 0 < r p := fun p =>
    (half_pos hR).trans_le (le_max_left _ _)
  have hrR : ∀ p, r p ≤ R := fun p =>
    max_le (by linarith) (min_le_left _ _)
  have hn : ∀ p, ‖v p‖ = 1 := fun p =>
    NormedSpace.norm_normalize (affineLift_ne_zero he
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property))
  have hvm : Measurable v :=
    (continuous_normalized_affineLift he).measurable.comp measurable_snd
  have hrm : Measurable r := by dsimp [r]; fun_prop
  apply exists_measurable_highValue_circlePoint hum x hvm hrm hr
    (fun p => hu _ (norm_ne_zero_iff.mp (by rw [hn p]; exact one_ne_zero)))
  rintro p y ⟨z, hz, rfl⟩
  apply hball
  have hz' : ‖z‖ ≤ r p := by simpa using hz
  simpa [mem_closedBall, dist_eq_norm, norm_smul, hn p] using hz'.trans (hrR p)

end PshLines.PSHD
