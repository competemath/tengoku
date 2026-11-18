import Tengoku.WasowAsymptoticsLean.WasowPowerSeries
import Tengoku.Seed.RingTheory.PowerSeries.Trunc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms coeff_mul_congr_below` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_truncation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_shifted_derivative_truncation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms defect_coeff_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms defect_divisible` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms truncation_isUnit` (it only prints; the queue checks the axioms of every declaration). -/

/-! Finite polynomial truncations of a genuine formal matrix gauge.
The formal residual is proved divisible by the requested power, for every
truncation order. No convergence of the infinite gauge or transformed series
is assumed or concluded. Analytic realization requires a separate remainder
estimate for an actual analytic coefficient function. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowTruncation
open WasowPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication preserves agreement of all coefficients below a bound.
@isnad1 id=eq.3h7v.s9.b558b33c1923 from=translated src=- shape=d9616001 vocab=714314af
-/
theorem coeff_mul_congr_below {R : Type*} [Semiring R]
    {F G F' G' : PowerSeries R} {N k : ℕ} (hk : k < N)
    (hF : ∀ i < N, PowerSeries.coeff i F = PowerSeries.coeff i F')
    (hG : ∀ i < N, PowerSeries.coeff i G = PowerSeries.coeff i G') :
    PowerSeries.coeff k (F*G) = PowerSeries.coeff k (F'*G') := by
  rw [coeff_mul_range_left, coeff_mul_range_left]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  rw [hF i (hik.trans_lt hk), hG (k-i) ((Nat.sub_le _ _).trans_lt hk)]

/-- The actual polynomial truncation agrees with the prescribed formal data.
@isnad1 id=eq.1h4v.s8.7c71c97037e3 from=translated src=- shape=44eee381 vocab=c48e9f09
-/
theorem coeff_truncation {R : Type*} [Semiring R]
    (F : PowerSeries R) {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k ((PowerSeries.trunc N F : Polynomial R) : PowerSeries R) =
      PowerSeries.coeff k F := by
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hk]

/-- Positive-rank differentiation cannot bring an omitted coefficient below
the truncation order. This includes the zero coefficient at degree `q`.
@isnad1 id=eq.1h5v.s10.380d846676cb from=translated src=- shape=44b5f57f vocab=673f748b
-/
theorem coeff_shifted_derivative_truncation
    (P : PowerSeries (Matrix ι ι ℂ)) (q : ℕ) {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k (PowerSeries.X ^ (q+1) *
      derivative ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ))) =
      PowerSeries.coeff k (PowerSeries.X ^ (q+1) * derivative P) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with hq
  · rw [coeff_derivative, coeff_derivative, coeff_truncation P (by omega)]
  · rfl

def defect (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ) :
    PowerSeries (Matrix ι ι ℂ) :=
  let p : PowerSeries (Matrix ι ι ℂ) := PowerSeries.trunc N P
  let b : PowerSeries (Matrix ι ι ℂ) := PowerSeries.trunc N B
  A*p-p*b+PowerSeries.X^(q+1)*derivative p

/-- All coefficients of the finite-truncation residual below `N` vanish.
@isnad1 id=eq.2h7v.s9.af2991a9c8f7 from=translated src=- shape=a41a9e1b vocab=ce1ad976
-/
theorem defect_coeff_zero (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A*P-P*B = -(PowerSeries.X^(q+1)*derivative P)) :
    ∀ k < N, PowerSeries.coeff k (defect A P B q N) = 0 := by
  intro k hk
  have hp : ∀ i < N, PowerSeries.coeff i
      ((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ)) =
        PowerSeries.coeff i P := fun i hi => coeff_truncation P hi
  have hb : ∀ i < N, PowerSeries.coeff i
      ((PowerSeries.trunc N B : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ)) =
        PowerSeries.coeff i B := fun i hi => coeff_truncation B hi
  have hAP := coeff_mul_congr_below hk (fun _ _ => rfl (a := PowerSeries.coeff _ A)) hp
  have hPB := coeff_mul_congr_below hk hp hb
  have hh : A*P-P*B+PowerSeries.X^(q+1)*derivative P = 0 := by
    rw [heq, neg_add_cancel]
  have hfull := congrArg (PowerSeries.coeff k) hh
  simp only [map_add, map_sub, map_zero] at hfull
  simpa only [defect, map_add, map_sub, hAP, hPB,
    coeff_shifted_derivative_truncation P q hk] using hfull

/-- A genuine factorization of the residual by `X^N`, not just a notation
for an unspecified asymptotic error.
@isnad1 id=dvd.1h6v.s8.4694f682dc7f from=translated src=- shape=66abbda0 vocab=4a07059e
-/
theorem defect_divisible (A P B : PowerSeries (Matrix ι ι ℂ)) (q N : ℕ)
    (heq : A*P-P*B = -(PowerSeries.X^(q+1)*derivative P)) :
    (PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ N ∣ defect A P B q N :=
  PowerSeries.X_pow_dvd_iff.mpr (defect_coeff_zero A P B q N heq)

/-- The finite gauge itself remains formally invertible at every positive
truncation order because its constant matrix is the identity.
@isnad1 id=isunit.2h3v.s9.5833f031655c from=translated src=- shape=3dc542ca vocab=5c3b76b5
-/
theorem truncation_isUnit (P : PowerSeries (Matrix ι ι ℂ))
    (hP : PowerSeries.constantCoeff P = 1) {N : ℕ} (hN : 0 < N) :
    IsUnit (((PowerSeries.trunc N P : Polynomial (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ))) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncation P hN,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hP]
  exact isUnit_one

end WasowTruncation
