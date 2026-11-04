import Tengoku.DeletionCodesLean.DeletionCode.UniqueWordParameters
import Tengoku.DeletionCodesLean.DeletionCode.HeaderRecovery
import Tengoku.Seed.Analysis.Asymptotics.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms tendsto_L_atTop` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eventually_ready` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms le_two_pow_of_L_lt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms L_isBigO_logb` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms logb_L_isBigO_logb_logb` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Growth bounds for the manuscript's actual parameters, with no asymptotic
hypotheses supplied by the caller. The explicit estimates also discharge
the finite thresholds used in the counting and probability arguments.
-/
namespace DeletionCode.PaperParameters

open Filter Asymptotics
open scoped Topology

def k (n : ℕ) : ℕ := UniqueWordParameters.uniquenessLength n

def L (n : ℕ) : ℕ := HeaderRecovery.windowLength (k n)

/--
@isnad1 id=eq.0h1v.s5.95dc1def757e from=translated src=- shape=b05fb6e7 vocab=d4dff3ad
-/
theorem L_eq (n : ℕ) : L n = 6 * Nat.clog 2 n + 9 := by
  unfold L k HeaderRecovery.windowLength UniqueWordParameters.uniquenessLength
  omega

/--
@isnad1 id=le.0h1v.s3.12cd5c4c63f8 from=translated src=- shape=8a62b088 vocab=e5670694
-/
theorem nine_le_L (n : ℕ) : 9 ≤ L n := by rw [L_eq]; omega

/-- A concrete, albeit deliberately generous, threshold for every fixed M.
@isnad1 id=le.1h2v.s5.976a342fee43 from=translated src=- shape=44a97ff6 vocab=eab9a0cc
-/
theorem threshold (M n : ℕ) (hn : 2 ^ M + 1 ≤ n) : M ≤ L n := by
  have hc : M < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  rw [L_eq]
  omega

/--
@isnad1 id=eventual.0h1v.s3.13d4fd2887bd from=translated src=- shape=e66203b3 vocab=f151a336
-/
theorem eventually_threshold (M : ℕ) : ∀ᶠ n : ℕ in atTop, M ≤ L n := by
  filter_upwards [eventually_ge_atTop (2 ^ M + 1)] with n hn
  exact threshold M n hn

/--
@isnad1 id=tendsto.0h0v.s3.b8fb6e3e248f from=translated src=- shape=41b74a9e vocab=a734bf7e
-/
theorem tendsto_L_atTop : Tendsto L atTop atTop :=
  tendsto_atTop.2 eventually_threshold

private theorem affine_le_pow (q : ℕ) : 6 * (q + 6) + 15 ≤ 2 ^ (q + 6) := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    have he : (q + 1) + 6 = (q + 6) + 1 := by omega
    change 6 * ((q + 1) + 6) + 15 ≤ 2 ^ ((q + 1) + 6)
    rw [he, pow_succ]
    omega

/-- The required window fits in the word from the explicit threshold 65.
@isnad1 id=le.1h1v.s4.d9c1518a3903 from=translated src=- shape=71fa8a4a vocab=e5670694
-/
theorem L_le_n (n : ℕ) (hn : 65 ≤ n) : L n ≤ n := by
  let c := Nat.clog 2 n
  have hc : 6 < c := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    norm_num
    omega
  have hpow := affine_le_pow (c - 7)
  have he : (c - 7) + 6 = c - 1 := by omega
  rw [he] at hpow
  have hnpow : 2 ^ (c - 1) < n := Nat.pow_lt_of_lt_clog (by omega : c - 1 < c)
  rw [L_eq]
  change 6 * c + 9 ≤ n
  omega

/--
@isnad1 id=eventual.0h0v.s3.16e04ec35c25 from=translated src=- shape=4d699f29 vocab=f151a336
-/
theorem eventually_L_le_n : ∀ᶠ n : ℕ in atTop, L n ≤ n := by
  filter_upwards [eventually_ge_atTop 65] with n hn
  exact L_le_n n hn

/--
@isnad1 id=eventual.0h0v.s4.94d1320b7cf9 from=translated src=- shape=183cbfe9 vocab=7f354f7a
-/
theorem eventually_three_le_n : ∀ᶠ n : ℕ in atTop, 3 ≤ n := eventually_ge_atTop 3

/-- All concrete fixed thresholds can be imposed together for large n.
@isnad1 id=eventual.0h1v.s5.ed97aeafda5d from=translated src=- shape=807bed09 vocab=f151a336
-/
theorem eventually_ready (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ L n ≤ n ∧ M ≤ L n := by
  filter_upwards [eventually_three_le_n, eventually_L_le_n, eventually_threshold M]
    with n hn hfit hM
  exact ⟨hn, hfit, hM⟩

/-- This discharges the extra-component arithmetic premise in WitnessCounting.
@isnad1 id=le.1h2v.s5.abbbd6861cc7 from=translated src=- shape=520b13f4 vocab=3bd5e925
-/
theorem le_two_pow_of_L_lt (n R : ℕ) (hR : L n < R) : n ≤ 2 ^ R := by
  have hc : Nat.clog 2 n ≤ R := by rw [L_eq] at hR; omega
  exact (Nat.le_pow_clog (by decide : 1 < 2) n).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hc)

/--
@isnad1 id=le.1h1v.s5.18c14ab42d45 from=translated src=- shape=2c468144 vocab=5b61d28c
-/
theorem one_le_logb (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/--
@isnad1 id=le.1h1v.s5.cba3719b73b2 from=translated src=- shape=2c468144 vocab=5b61d28c
-/
theorem two_le_logb (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2 ^ (2 : ℕ))
    (show (2 : ℝ) ^ (2 : ℕ) ≤ n by norm_num; exact_mod_cast hn)
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] using h

/-- A pointwise logarithmic bound for the actual ceiling parameter.
@isnad1 id=le.1h1v.s5.11c6d227668c from=translated src=- shape=7010f426 vocab=653b0f27
-/
theorem L_le_twenty_one_logb (n : ℕ) (hn : 2 ≤ n) :
    (L n : ℝ) ≤ 21 * Real.logb 2 (n : ℝ) := by
  have hlog := one_le_logb n hn
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
    have he : Nat.clog 2 n = ⌈Real.logb 2 (n : ℝ)⌉₊ := by
      symm
      simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
    rw [he]
    exact Nat.ceil_lt_add_one (by linarith)
  have hL : (L n : ℝ) = 6 * (Nat.clog 2 n : ℝ) + 9 := by
    exact_mod_cast L_eq n
  linarith

/--
@isnad1 id=isbigo.0h0v.s4.077ce6b3e845 from=translated src=- shape=b546c60c vocab=50e01ee2
-/
theorem L_isBigO_logb :
    (fun n : ℕ => (L n : ℝ)) =O[atTop] (fun n => Real.logb 2 (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 21
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := by have := one_le_logb n hn; linarith
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (L n) : (0 : ℝ) ≤ (L n : ℝ)),
    abs_of_nonneg hlog] using L_le_twenty_one_logb n hn

/--
@isnad1 id=le.1h1v.s5.34da328e43fa from=translated src=- shape=935ff288 vocab=5b61d28c
-/
theorem one_le_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (two_le_logb n hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- The logarithm of the window length is bounded by six times log-log.
@isnad1 id=le.1h1v.s6.ba29c54053dc from=translated src=- shape=6e08b987 vocab=653b0f27
-/
theorem logb_L_le_six_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    Real.logb 2 (L n : ℝ) ≤ 6 * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have hlog : 0 < Real.logb 2 (n : ℝ) := by have := two_le_logb n hn; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 9) (nine_le_L n))
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hL (L_le_twenty_one_logb n (by omega))
  rw [Real.logb_mul (by norm_num : (21 : ℝ) ≠ 0) (ne_of_gt hlog)] at hmono
  have h21 : Real.logb 2 (21 : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 21) (by norm_num : (21 : ℝ) ≤ 2 ^ (5 : ℕ))
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_ofNat, mul_one] using h
  have hll := one_le_logb_logb n hn
  linarith

/--
@isnad1 id=isbigo.0h0v.s5.ff7436aa98fc from=translated src=- shape=5b75fe06 vocab=50e01ee2
-/
theorem logb_L_isBigO_logb_logb :
    (fun n : ℕ => Real.logb 2 (L n : ℝ)) =O[atTop]
      (fun n => Real.logb 2 (Real.logb 2 (n : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hL : 0 ≤ Real.logb 2 (L n : ℝ) := Real.logb_nonneg
    (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (show 1 ≤ L n by have := nine_le_L n; omega))
  have hll : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    have := one_le_logb_logb n hn
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hll] using
    logb_L_le_six_logb_logb n hn

end DeletionCode.PaperParameters
