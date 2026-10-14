import Tengoku

open Real MeasureTheory

/--
@isnad1 id=interval.0h2v.s5.37ec639e220e from=translated src=- shape=8b80235b vocab=c1c5fc9e
-/
@[simp]
theorem intervalIntegral.intervalIntegrable_inv_sqrt_one_sub_sq {a b : ℝ} :
    IntervalIntegrable (fun x : ℝ => (√(1 - x ^ 2))⁻¹) volume a b := by
  simpa [deriv_arcsin] using (monotone_arcsin.monotoneOn _).intervalIntegrable_deriv
