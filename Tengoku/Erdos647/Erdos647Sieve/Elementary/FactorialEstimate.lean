/-
The normalized factorial remainder needed by the endpoint argument.
The H+2 shift is handled by the exact factorial recurrence, not a second
asymptotic expansion. All divisions here are real divisions after casting.
-/
import Tengoku.Erdos647.Erdos647Sieve.Elementary.FactorialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped Topology
open Filter Real

noncomputable section
namespace Erdos647Sieve.Elementary

/-- The manuscript's factorial expression; division by two is over the reals.-/
def shiftedFactorialLog (H : ℕ) : ℝ :=
  Real.log ((Nat.factorial (H + 2) : ℝ) / 2)

/-- The exact shift identity also includes H=0.
@isnad1 id=eq.0h1v.s6.24db98c1332f from=translated src=- shape=0d029cb1 vocab=f9566cd7
-/
theorem shiftedFactorialLog_eq_expanded (H : ℕ) :
    shiftedFactorialLog H = Real.log (Nat.factorial H : ℝ) +
      Real.log ((H : ℝ) + 1) + Real.log ((H : ℝ) + 2) - Real.log 2 := by
  have hfac : (Nat.factorial (H + 2) : ℝ) =
      ((H : ℝ) + 2) * (((H : ℝ) + 1) * (Nat.factorial H : ℝ)) := by
    rw [show H + 2 = (H + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
    push_cast
    ring
  unfold shiftedFactorialLog
  rw [hfac, Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  ring

/-- The standard logarithm-over-identity limit, composed with natural casts.
@isnad1 id=tendsto.0h0v.s5.255b24d33c72 from=translated src=- shape=69636548 vocab=95411f06
-/
theorem log_nat_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num))
  exact h.comp tendsto_natCast_atTop_atTop

/-- A fixed real shift in the logarithm is harmless after division by n.
@isnad1 id=tendsto.0h1v.s5.2137fda6c7b1 from=translated src=- shape=aceb1b82 vocab=6153bcf2
-/
theorem log_nat_add_div_nat_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + c) / (n : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto
      (fun n : ℕ => Real.log ((n : ℝ) + c) - Real.log (n : ℝ))
      atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log c).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have h : Tendsto
      (fun n : ℕ => (Real.log ((n : ℝ) + c) - Real.log (n : ℝ)) *
        (1 / (n : ℝ)) + Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (hshift.mul hinv).add log_nat_div_nat_tendsto_zero
  exact h.congr (fun n => by ring)

/-- Stirling's upper and lower bounds imply the normalized remainder tends to zero.
@isnad1 id=tendsto.0h0v.s6.c1bcf7484b1b from=translated src=- shape=a5ccf57b vocab=34cb91fa
-/
theorem log_factorial_residual_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (Real.log (Nat.factorial n : ℝ) -
        ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupperlim : Tendsto
      (fun n : ℕ => (Real.log (n : ℝ) / 2 + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    have h : Tendsto
        (fun n : ℕ => (Real.log (n : ℝ) / (n : ℝ)) / 2 + 1 / (n : ℝ))
        atTop (𝓝 0) := by
      simpa using (log_nat_div_nat_tendsto_zero.div_const 2).add
        (tendsto_const_div_atTop_nhds_zero_nat 1)
    exact h.congr (fun n => by ring)
  refine squeeze_zero' ?_ ?_ hupperlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (sub_nonneg.mpr (log_factorial_lower n hn)) (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    linarith [log_factorial_upper n hn]

/-- The exact normalized residual requested in the endpoint handoff.
@isnad1 id=tendsto.0h0v.s6.06ddc773d831 from=translated src=- shape=f0c78fe7 vocab=8ee0e697
-/
theorem shiftedFactorialLog_residual_tendsto_zero :
    Tendsto (fun H : ℕ =>
      (shiftedFactorialLog H -
        ((H : ℝ) * Real.log (H : ℝ) - (H : ℝ))) / (H : ℝ))
      atTop (𝓝 0) := by
  have h : Tendsto (fun H : ℕ =>
      (Real.log (Nat.factorial H : ℝ) -
        ((H : ℝ) * Real.log (H : ℝ) - (H : ℝ))) / (H : ℝ) +
      Real.log ((H : ℝ) + 1) / (H : ℝ) +
      Real.log ((H : ℝ) + 2) / (H : ℝ) - Real.log 2 / (H : ℝ))
      atTop (𝓝 0) := by
    simpa using
      (((log_factorial_residual_tendsto_zero.add (log_nat_add_div_nat_tendsto_zero 1)).add
        (log_nat_add_div_nat_tendsto_zero 2)).sub
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)))
  refine h.congr (fun H => ?_)
  rw [shiftedFactorialLog_eq_expanded]
  ring

end Erdos647Sieve.Elementary
end
