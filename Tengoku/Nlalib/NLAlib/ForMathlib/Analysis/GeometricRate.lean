import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Solving a geometric error bound for an integer step count

An explicit logarithmic step condition bounds `D/(ρ^(2q-1)(ρ-1))` by a prescribed tolerance.
This is general real algebra used by the analytic stochastic Lanczos quadrature rate.
-/

noncomputable section

open Real

namespace NLAlib

/-- The explicit step condition `q ≥ (1+log(D/(η(ρ-1)))/logρ)/2` pays a geometric error
`D/(ρ^(2q-1)(ρ-1)) ≤ η`, for `D,η>0`, `ρ>1`, and integer `q≥1`.
Source: solving the geometric rate in Trefethen, ATAP, Theorem 8.2;
operator rederivations `rt:slq` (analytic SLQ step budget).
@isnad1 id=le.5h4v.s7.f5b9cfce5446 from=translated src=- shape=d9d9c020 vocab=253be381
-/
theorem div_pow_sub_one_le_of_log_steps {D η ρ : ℝ} (hD : 0 < D) (hη : 0 < η)
    (hρ : 1 < ρ) {q : ℕ} (hq : 0 < q)
    (hsteps : (1 + log (D / (η * (ρ - 1))) / log ρ) / 2 ≤ (q : ℝ)) :
    D / ρ ^ (2 * q - 1) / (ρ - 1) ≤ η := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hlogρ : 0 < log ρ := log_pos hρ
  have hqcast : ((2 * q - 1 : ℕ) : ℝ) = 2 * (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * q), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hratio : log (D / (η * (ρ - 1))) / log ρ ≤ 2 * (q : ℝ) - 1 := by linarith
  have hlog := (div_le_iff₀ hlogρ).mp hratio
  have hpow : D / (η * (ρ - 1)) ≤ ρ ^ (2 * q - 1) := by
    calc D / (η * (ρ - 1)) = exp (log (D / (η * (ρ - 1)))) :=
        (exp_log (by positivity)).symm
      _ ≤ exp (((2 * q - 1 : ℕ) : ℝ) * log ρ) := by
        apply exp_le_exp.mpr
        rw [hqcast]
        exact hlog
      _ = ρ ^ (2 * q - 1) := by rw [exp_nat_mul, exp_log hρ0]
  rw [div_le_iff₀ (sub_pos.mpr hρ), div_le_iff₀ (pow_pos hρ0 _)]
  rw [div_le_iff₀ (show 0 < η * (ρ - 1) by positivity)] at hpow
  nlinarith

end NLAlib
