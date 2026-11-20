import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatRegularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From Gaussian tails and quadratic growth to heat integrability

This criterion turns pointwise analytic estimates into all five required
integrability and local domination conditions. No integral inequality or
monotonicity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

theorem le_quadratic_of_sq_le {v K r : ℝ} (h : v^2 ≤ K*(1+r^2)) :
    v ≤ (1+K)*(1+r^2) := by
  have hv : v ≤ 1+v^2 := by nlinarith [sq_nonneg (v-1)]
  have hr : 1+K*(1+r^2) ≤ (1+K)*(1+r^2) := by nlinarith [sq_nonneg r]
  exact hv.trans ((add_le_add le_rfl h).trans hr)

theorem mul_le_polynomial_gaussian {q v A K b r : ℝ} (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hqa : q ≤ A*Real.exp (-b*r^2)) (hv : v ≤ K*(1+r^2)) :
    q*v ≤ (A*K)*(1+r^2)*Real.exp (-b*r^2) := by
  calc
    _ ≤ q*(K*(1+r^2)) := mul_le_mul_of_nonneg_left hv hq
    _ ≤ (A*Real.exp (-b*r^2))*(K*(1+r^2)) :=
      mul_le_mul_of_nonneg_right hqa (by positivity)
    _ = _ := by ring

namespace Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

theorem heatIntegrability_of_gaussian_bounds (A b K : ℝ → ℝ)
    (hb : ∀ t, 0 < t → 0 < b t) (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hAcont : ∀ t, 0 < t → ContinuousAt A t)
    (hbcont : ∀ t, 0 < t → ContinuousAt b t)
    (hKcont : ∀ t, 0 < t → ContinuousAt K t)
    (hH : ∀ t, 0 < t → ∀ i, Continuous ((U i).hessian t))
    (hQ : ∀ t, 0 < t → ∀ x, D.heatProduct U t x ≤ A t*Real.exp (-b t*‖x‖^2))
    (hS : ∀ t, 0 < t → ∀ x, ‖D.score U t x‖^2 ≤ K t*(1+‖x‖^2))
    (hDS : ∀ t, 0 < t → ∀ x, ‖D.scoreDerivative U t x‖ ≤ K t*(1+‖x‖^2))
    (hT : ∀ t, 0 < t → ∀ x, ‖D.timeRate U t x‖ ≤ K t*(1+‖x‖^2)) :
    D.HeatIntegrability U := by
  have htime (t : ℝ) (ht : 0 < t) (x : E) :
      ‖D.heatProduct U t x*D.timeRate U t x‖ ≤
        (A t*K t)*(1+‖x‖^2)*Real.exp (-b t*‖x‖^2) := by
    rw [norm_mul, Real.norm_eq_abs (D.heatProduct U t x), abs_of_pos (D.heatProduct_pos U t x)]
    exact mul_le_polynomial_gaussian (D.heatProduct_pos U t x).le (hK t ht) (hQ t ht x) (hT t ht x)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    apply ((integrable_gaussian (E := E) (hb t ht)).const_mul (A t)).mono'
      (D.heatProduct_continuous U ht).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (D.heatProduct_pos U t x)]
      exact hQ t ht x
  · intro t ht
    apply integrable_of_polynomial_gaussian_bound
      ((D.heatProduct_continuous U ht).mul (D.timeRate_continuous U ht (hH t ht))).aestronglyMeasurable
      0 2 (A t*K t) (hb t ht)
    simpa only [sub_zero, Pi.mul_apply] using htime t ht
  · intro t ht
    apply integrable_of_polynomial_gaussian_bound
      ((D.heatProduct_continuous U ht).smul (D.score_continuous U ht)).aestronglyMeasurable
      0 2 (A t*(1+K t)) (hb t ht)
    intro x
    change ‖D.heatProduct U t x • D.score U t x‖ ≤ _
    simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (D.heatProduct_pos U t x)]
    have hs := le_quadratic_of_sq_le (hS t ht x)
    have hk := hK t ht
    exact mul_le_polynomial_gaussian (D.heatProduct_pos U t x).le (by positivity) (hQ t ht x) hs
  · intro t ht
    apply integrable_of_polynomial_gaussian_bound
      (D.fluxDerivative_continuous U ht (hH t ht)).aestronglyMeasurable
      0 2 (A t*(2*K t)) (hb t ht)
    intro x
    simp only [sub_zero]
    apply (D.norm_fluxDerivative_le U t x).trans
    apply mul_le_polynomial_gaussian (D.heatProduct_pos U t x).le
      (mul_nonneg (by norm_num) (hK t ht)) (hQ t ht x)
    have hs := hS t ht x
    have hd := hDS t ht x
    linarith
  · intro t ht
    obtain ⟨V, hV, hVpos, g, hg, hbound⟩ := exists_local_quadratic_gaussian_bound
      (0 : E) ht (hb t ht) ((hAcont t ht).mul (hKcont t ht)) (hbcont t ht)
      (P := fun _ => 1) (R := fun _ => 1) continuousAt_const continuousAt_const
    refine ⟨V, hV, hVpos, g, hg, fun s hs x => ?_⟩
    apply (htime s (hVpos hs) x).trans
    have h := hbound s hs x
    simp only [sub_zero, one_mul, Pi.mul_apply] at h
    exact (le_abs_self _).trans h

end Datum
end GeometricBrascampLieb
