import Tengoku.Twinprime.TwinPrime.Analytic.VaughanMeanValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic small-conductor cutoffs at the exact BV endpoint

These are elementary comparisons, not prime-distribution estimates. They
bound the finite small-conductor budget once a centered character estimate
has been supplied independently.
-/

noncomputable section

namespace TwinPrime.Analytic

def bvSmallConductorCutoff (A : ℝ) (X : ℕ) : ℕ :=
  ⌈(Real.log X) ^ (A + 9)⌉₊

/--
@isnad1 id=and.2h2v.s7.cb7cee8dae02 from=translated src=- shape=c0b70d85 vocab=e5b8908e
-/
theorem bvSmallConductorCutoff_bounds (A : ℝ) (hA : 0 < A)
    (X : ℕ) (hlog : 2 ≤ Real.log (X : ℝ)) :
    1 ≤ bvSmallConductorCutoff A X ∧
      (Real.log X) ^ (A + 9) ≤ (bvSmallConductorCutoff A X : ℝ) ∧
      (bvSmallConductorCutoff A X : ℝ) ≤ 2 * (Real.log X) ^ (A + 9) := by
  have hp : 1 ≤ (Real.log X) ^ (A + 9) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hlo := Nat.le_ceil ((Real.log X) ^ (A + 9))
  have hhi := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) (A + 9))
  change (Real.log X) ^ (A + 9) ≤ (bvSmallConductorCutoff A X : ℝ) at hlo
  change (bvSmallConductorCutoff A X : ℝ) < (Real.log X) ^ (A + 9) + 1 at hhi
  refine ⟨?_, hlo, by linarith⟩
  exact_mod_cast hp.trans hlo

/--
@isnad1 id=le.3h2v.s6.6922b5d86afa from=translated src=- shape=c694c437 vocab=e5b8908e
-/
theorem bvSmallConductorCutoff_le_log_endpoint (A : ℝ) (hA : 0 < A)
    (X : ℕ) (hX : 2 ≤ X) (hlog : 2 ≤ Real.log (X : ℝ)) :
    (bvSmallConductorCutoff A X : ℝ) ≤ (Real.log (2 * X + 2)) ^ (A + 10) := by
  have hl : 0 < Real.log (X : ℝ) := by linarith
  have hlt : Real.log (X : ℝ) ≤ Real.log (2 * X + 2 : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
      (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  calc
    _ ≤ 2 * (Real.log X) ^ (A + 9) := (bvSmallConductorCutoff_bounds A hA X hlog).2.2
    _ ≤ (Real.log X) ^ (A + 9) * Real.log X := by
      nlinarith [mul_nonneg (Real.rpow_nonneg hl.le (A + 9)) (sub_nonneg.mpr hlog)]
    _ = (Real.log X) ^ (A + 10) := by
      rw [show A + 10 = (A + 9) + 1 by ring,
        Real.rpow_add hl (A + 9) 1, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow hl.le hlt (by linarith)

/-- The admissible BV range is inside both the original scale and the
square-root range required by the proved finite mean.
@isnad1 id=and.4h3v.s7.40950c95e866 from=translated src=- shape=9e7def37 vocab=3fc8b303
-/
theorem bv_admissible_modulus_bounds (A : ℝ) (hA : 0 < A)
    (X Q : ℕ) (hX : 2 ≤ X) (hlog : 1 ≤ Real.log (X : ℝ))
    (hQ : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 9)) :
    Q ≤ X ∧ (Q : ℝ) ≤ Real.sqrt ((2 * X + 2 : ℕ) : ℝ) := by
  have hpow : 1 ≤ (Real.log X) ^ (A + 9) := Real.one_le_rpow hlog (by linarith)
  have hq : (Q : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply hQ.trans
    rw [← Real.sqrt_eq_rpow]
    exact div_le_self (Real.sqrt_nonneg _) hpow
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  refine ⟨?_, hq.trans (Real.sqrt_le_sqrt ?_)⟩
  · exact_mod_cast hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx))
  · push_cast
    have := Nat.cast_nonneg (α := ℝ) X
    linarith

/-- Increasing the logarithmic modulus loss also meets the already proved
primitive-replacement error range.
@isnad1 id=le.3h3v.s7.ffd701505e2c from=translated src=- shape=2c32988b vocab=ea7ec0a7
-/
theorem bv_admissible_modulus_le_exception_range (A : ℝ) (_hA : 0 < A)
    (X Q : ℕ) (hlog : 1 ≤ Real.log (X : ℝ))
    (hQ : (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 9)) :
    (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2) := by
  apply hQ.trans
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg X) _) (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hlog (by linarith)

/-- A uniform centered bound with exponent `2A+12` absorbs the count of
small conductors and the outer reciprocal-totient logarithm.
@isnad1 id=le.5h4v.s8.65516bfe29cf from=translated src=- shape=aceb69d3 vocab=5a02ed70
-/
theorem bv_small_conductor_budget_le (A : ℝ) (hA : 0 < A)
    (C : ℝ) (hC : 0 ≤ C) (X Q : ℕ) (hX : 2 ≤ X)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hQ : Q ≤ X) :
    totientReciprocalConstant * (1 + Real.log Q) *
      ((bvSmallConductorCutoff A X : ℝ) *
        (C * (2 * X + 2 : ℕ) / (Real.log (2 * X + 2 : ℕ)) ^ (2 * A + 12))) ≤
      (12 * totientReciprocalConstant * C) * X / (Real.log X) ^ A := by
  have hx : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hl : 0 < Real.log (X : ℝ) := by linarith
  have hlt : Real.log (X : ℝ) ≤ Real.log ((2 * X + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have ht : ((2 * X + 2 : ℕ) : ℝ) ≤ 3 * X := by push_cast; linarith
  have hlq : Real.log (Q : ℝ) ≤ Real.log X := by
    rcases Q.eq_zero_or_pos with rfl | hq
    · simpa only [Nat.cast_zero, Real.log_zero] using hl.le
    · exact Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hQ)
  have hcφ := totientReciprocalConstant_nonneg
  have he : C * (2 * X + 2 : ℕ) / (Real.log (2 * X + 2 : ℕ)) ^ (2 * A + 12) ≤
      3 * C * X / (Real.log X) ^ (2 * A + 12) := by
    calc
      _ ≤ C * (3 * X) / (Real.log X) ^ (2 * A + 12) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ht hC) (by positivity)
        exact Real.rpow_le_rpow hl.le hlt (by linarith)
      _ = _ := by ring
  have hbase : totientReciprocalConstant * (1 + Real.log Q) *
      ((bvSmallConductorCutoff A X : ℝ) *
        (C * (2 * X + 2 : ℕ) / (Real.log (2 * X + 2 : ℕ)) ^ (2 * A + 12))) ≤
      totientReciprocalConstant * (2 * Real.log X) *
        ((2 * (Real.log X) ^ (A + 9)) * (3 * C * X / (Real.log X) ^ (2 * A + 12))) := by
    gcongr
    · linarith
    · exact (bvSmallConductorCutoff_bounds A hA X hlog).2.2
  have hp : (Real.log X) ^ (2 * A + 12) =
      (Real.log X) ^ (A + 9) * Real.log X * (Real.log X) ^ (A + 2) := by
    rw [← Real.rpow_add_one hl.ne', ← Real.rpow_add hl]
    congr 1
    ring
  have heq : totientReciprocalConstant * (2 * Real.log X) *
        ((2 * (Real.log X) ^ (A + 9)) * (3 * C * X / (Real.log X) ^ (2 * A + 12))) =
      (12 * totientReciprocalConstant * C) * X / (Real.log X) ^ (A + 2) := by
    rw [hp]
    field_simp
    ring
  apply (hbase.trans_eq heq).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end TwinPrime.Analytic
