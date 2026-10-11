import Tengoku

open Real MeasureTheory

@[simp]
theorem intervalIntegral.intervalIntegrable_inv_sqrt_one_sub_sq {a b : ℝ} :
    IntervalIntegrable (fun x : ℝ => (√(1 - x ^ 2))⁻¹) volume a b := by
  simpa [deriv_arcsin] using (monotone_arcsin.monotoneOn _).intervalIntegrable_deriv
