import Tengoku.Piirrationalitymeasure.Formalization.CoefficientProbability
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual expectation and variance of the tilted law, equation (4.9). -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem pmf_nat_integrable_of_summable (p : PMF ℕ) (f : ℕ → ℝ)
    (hf : Summable (fun k => (p k).toReal * ‖f k‖)) : Integrable f p.toMeasure := by
  rw [← Measure.sum_smul_dirac p.toMeasure]
  apply integrable_sum_dirac
  · intro k
    exact measure_ne_top _ _
  · simpa only [PMF.toMeasure_apply_singleton p _ (MeasurableSet.singleton _)] using hf

theorem coefficientLaw_integrable_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (coefficientLaw x hx0 hx1 1).toMeasure := by
  apply pmf_nat_integrable_of_summable
  simpa only [coefficientLaw_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_comm t] using (coefficientProbability_exponential_sum hx0 1 t ht).summable

theorem coefficientLaw_mgf {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    mgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0 hx1 1).toMeasure t =
      SReal (x * Real.exp t) / SReal x := by
  rw [mgf, PMF.integral_eq_tsum _ _ (coefficientLaw_integrable_exp hx0 hx1 t ht)]
  simpa only [coefficientLaw_toReal, smul_eq_mul, mul_comm t, pow_one] using
    (coefficientProbability_exponential_sum hx0 1 t ht).tsum_eq

theorem coefficientLaw_interior_integrableExpSet {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {t : ℝ} (ht : x * Real.exp t < 1) :
    t ∈ interior (integrableExpSet (fun k : ℕ => (k : ℝ))
      (coefficientLaw x hx0 hx1 1).toMeasure) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hc : Continuous (fun s : ℝ => x * Real.exp s) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with s hs
  exact coefficientLaw_integrable_exp hx0 hx1 s hs

theorem SReal_differentiableAt {x : ℝ} (hx1 : x < 1) : DifferentiableAt ℝ SReal x := by
  have h : 1 - x ≠ 0 := by linarith
  unfold SReal PReal
  fun_prop (disch := positivity)

end PiIrrationality
