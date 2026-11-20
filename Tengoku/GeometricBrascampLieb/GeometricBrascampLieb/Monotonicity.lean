import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.LogHeat
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Divergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric heat-flow monotonicity

This module proves monotonicity from the logarithmic heat equation and explicit
integrability and domination conditions. These conditions still have to be
established for Gaussian regularizations of initial data.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

/-- Analytic bounds for a heat flow. Neither monotonicity nor a BL inequality
is a field of this structure.-/
structure HeatIntegrability : Prop where
  product_integrable : ∀ t, 0 < t → Integrable (D.heatProduct U t)
  time_integrable : ∀ t, 0 < t →
    Integrable (fun x => D.heatProduct U t x * D.timeRate U t x)
  flux_integrable : ∀ t, 0 < t → Integrable (D.flux U t)
  fluxDerivative_integrable : ∀ t, 0 < t → Integrable (D.fluxDerivative U t)
  local_time_bound : ∀ t, 0 < t → ∃ V ∈ 𝓝 t, V ⊆ Ioi 0 ∧ ∃ b : E → ℝ,
    Integrable b ∧ ∀ s ∈ V, ∀ x, ‖D.heatProduct U s x * D.timeRate U s x‖ ≤ b x

variable (H : D.HeatIntegrability U)
include H

/--
@isnad1 id=le.2h6v.s8.de30a091410c from=translated src=- shape=60faf300 vocab=07af2b4b
-/
theorem integral_time_derivative_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ x, D.heatProduct U t x * D.timeRate U t x := by
  let b := stdOrthonormalBasis ℝ E
  have hi : ∀ i, Integrable (fun x => inner ℝ (b i) (D.fluxDerivative U t x (b i))) := by
    intro i
    exact (innerSL ℝ (b i)).integrable_comp
      ((H.fluxDerivative_integrable t ht).apply_continuousLinearMap (b i))
  have hz := integral_trace_derivative_eq_zero b (H.flux_integrable t ht) hi
    (D.flux_hasFDerivAt U ht)
  have htr : Integrable (fun x => LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap) := by
    simp_rw [LinearMap.trace_eq_sum_inner _ b, ContinuousLinearMap.coe_coe]
    exact integrable_finsetSum _ (fun i _ => hi i)
  have hle := integral_mono htr (H.time_integrable t ht)
    (D.divergence_le_time_derivative U t)
  rwa [hz] at hle

/-- The geometric BL heat functional is nondecreasing on positive times.
@isnad1 id=monotone.1h5v.s8.b80b20f0ac5c from=translated src=- shape=679183f8 vocab=0630af88
-/
theorem heat_integral_monotoneOn :
    MonotoneOn (fun t => ∫ x, D.heatProduct U t x) (Ioi 0) := by
  apply monotoneOn_integral_of_local_derivative (convex_Ioi 0) isOpen_Ioi
    H.product_integrable
    (fun t ht => (H.time_integrable t ht).aestronglyMeasurable)
    (fun t ht => D.heatProduct_hasDerivAt U ht)
    H.local_time_bound
  exact fun t ht => D.integral_time_derivative_nonneg U H ht

end GeometricBrascampLieb.Datum
