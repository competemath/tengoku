import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CurveVariation
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiniteExceptionFTC

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform metric rectifiability from coordinatewise semialgebraic
variation. Interior C¹ regularity and endpoint continuity suffice;
endpoint velocities need not be bounded. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory
open scoped ENNReal

/-- The metric variation is bounded by the actual integrated speed. Only
interior derivatives and continuity at the endpoints are required.-/
theorem eVariationOn_le_integral_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (γ v : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t)
    (hi : IntegrableOn v (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (∫ t in Icc a b, ‖v t‖) := by
  exact eVariationOn_le_integral_speed_off_finite γ v ∅ Set.finite_empty hab hc
    (fun t ht _ => hd t ht) hi

/-- A given bounded family of continuous semialgebraic curves, C¹ in the
interior, has a uniform rectifiable-length bound. The actual derivative is
used and may be unbounded near the endpoints.-/
theorem uniform_semialgebraic_rectifiable_curves
    {ι κ : Type*} [Fintype κ]
    (γ : (ι → ℝ) → ℝ → EuclideanSpace ℝ κ)
    (hgraph : ∀ i, IsSemialgebraic ((ι ⊕ Unit) ⊕ Unit) {q |
      q (.inr ()) ∈ Ioo (0 : ℝ) 1 ∧
      γ (fun j => q (.inl (.inl j))) (q (.inr ())) i = q (.inl (.inr ()))})
    (hc : ∀ a, ContinuousOn (γ a) (Icc (0 : ℝ) 1))
    (hγ : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ 1 (γ a) t)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ a, ∀ t ∈ Ioo (0 : ℝ) 1, ‖γ a t‖ ≤ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ a, BoundedVariationOn (γ a) (Icc (0 : ℝ) 1) ∧
      eVariationOn (γ a) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L := by
  obtain ⟨L, _, hL⟩ := uniform_semialgebraic_curve_finite_length
    (fun _ => Ioo (0 : ℝ) 1) (fun _ => measurableSet_Ioo) γ (fun a => deriv (γ a))
    hgraph hγ (fun a t ht => (hγ a t ht).differentiableAt_one.hasDerivAt) B hB hbound
  refine ⟨max 1 L, le_max_left _ _, fun a => ?_⟩
  have hi : IntegrableOn (deriv (γ a)) (Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (hL a).1
  have hb := eVariationOn_le_integral_speed (γ a) (deriv (γ a)) zero_le_one (hc a)
    (fun t ht => (hγ a t ht).differentiableAt_one.hasDerivAt) hi
  rw [integral_Icc_eq_integral_Ioo] at hb
  have hh := hb.trans (ENNReal.ofReal_le_ofReal ((hL a).2.trans (le_max_right 1 L)))
  exact ⟨(hh.trans_lt ENNReal.ofReal_lt_top).ne, hh⟩

end
end DuistermaatVanDerKallen
