import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Monotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Endpoint reduction

Monotonicity compares finite endpoint limits. This module does not prove that
Gaussian regularizations have the required endpoint limits.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

/--
@isnad1 id=le.3h3v.s6.005485e08bfb from=translated src=- shape=cb3282fc vocab=e0d3371d
-/
theorem le_of_positive_monotone_limits {g : ℝ → ℝ} {a b : ℝ}
    (hg : MonotoneOn g (Ioi 0))
    (hzero : Tendsto g (𝓝[>] 0) (𝓝 a))
    (hinfty : Tendsto g atTop (𝓝 b)) : a ≤ b := by
  have hb : ∀ t, 0 < t → g t ≤ b := by
    intro t ht
    apply ge_of_tendsto hinfty
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hg ht (lt_of_lt_of_le ht hs) hs
  apply le_of_tendsto hzero
  exact eventually_mem_nhdsWithin.mono fun t ht => hb t ht

namespace Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

/-- Once the analytic bounds and the endpoint limits are supplied, the
geometric heat calculation yields the corresponding integral inequality.
@isnad1 id=le.3h7v.s8.504dfcfe699a from=translated src=- shape=998d7cf2 vocab=77a6cfc1
-/
theorem le_of_heat_limits (H : D.HeatIntegrability U) {a b : ℝ}
    (hzero : Tendsto (fun t => ∫ x, D.heatProduct U t x) (𝓝[>] 0) (𝓝 a))
    (hinfty : Tendsto (fun t => ∫ x, D.heatProduct U t x) atTop (𝓝 b)) : a ≤ b :=
  le_of_positive_monotone_limits (D.heat_integral_monotoneOn U H) hzero hinfty

end Datum
end GeometricBrascampLieb
