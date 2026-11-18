import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Packing
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Theta
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Decimal
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp finite-group interval bound

This file joins the exact rational packing theorem to the analytic theta
estimate.  The group-theoretic core stays in `Packing`; the lemmas here
certify the change from the exact finite sum to the logarithmic notation of
the manuscript.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The real logarithm to the natural base `q`, specialized to natural
arguments.-/
def indexLog (q n : ℕ) : ℝ :=
  Real.log (n : ℝ) / Real.log (q : ℝ)

/-- The exponential normal form of `n ^ ((log_q n) / 4)`.-/
def sharpScale (q n : ℕ) : ℝ :=
  Real.exp (Real.log (q : ℝ) * indexLog q n ^ 2 / 4)

/-- The natural floor of the real logarithm is Mathlib's exact natural
logarithm.
@isnad1 id=eq.0h2v.s4.ca8d57315175 from=translated src=- shape=8c042ac6 vocab=0fcc20bd
-/
@[simp]
theorem natFloor_indexLog (q n : ℕ) :
    Nat.floor (indexLog q n) = Nat.log q n := by
  rw [indexLog, Real.log_div_log, Real.natFloor_logb_natCast]

/-- The logarithmic parameter is nonnegative in the range used below.
@isnad1 id=le.2h2v.s5.018468a378f1 from=translated src=- shape=603a042a vocab=aa964f31
-/
theorem indexLog_nonneg {q n : ℕ} (hq : 1 < q) (hn : 0 < n) :
    0 ≤ indexLog q n := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  exact div_nonneg (Real.log_nonneg hnR) (Real.log_pos hqR).le

/-- The exact rational Euler factor used by packing casts to the real Euler
factor used by the theta estimate.
@isnad1 id=eq.1h2v.s4.25c8d4163865 from=translated src=- shape=4bb7ff45 vocab=96cad8a4
-/
theorem ratCast_gammaQ_eq_gammaR (q r : ℕ) (hq : 0 < q) :
    ((gammaQ q r : ℚ) : ℝ) = gammaR (q : ℝ) r := by
  induction r with
  | zero => simp [gammaR]
  | succ r ih =>
      rw [gammaQ_succ q r hq]
      rw [gammaR, Finset.prod_range_succ]
      rw [gammaR] at ih
      push_cast
      rw [ih]
      congr 2
      norm_num [div_eq_mul_inv]

/-- One summand of the exact rational finite sum has precisely the
exponential form used in `finiteThetaSum`.
@isnad1 id=eq.2h3v.s6.6a747296b893 from=translated src=- shape=5071ef47 vocab=9604a2df
-/
theorem exp_log_band_term {q n r : ℕ} (hq : 1 < q) (hn : 0 < n) :
    Real.exp
        (Real.log (q : ℝ) * (r : ℝ) * (indexLog q n - (r : ℝ))) =
      (n : ℝ) ^ r / (q : ℝ) ^ (r * r) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexponent :
      Real.log (q : ℝ) * (r : ℝ) * (indexLog q n - (r : ℝ)) =
        (r : ℝ) * Real.log (n : ℝ) -
          ((r * r : ℕ) : ℝ) * Real.log (q : ℝ) := by
    unfold indexLog
    field_simp
    push_cast
    ring
  rw [hexponent, Real.exp_sub]
  rw [Real.exp_nat_mul, Real.exp_nat_mul]
  rw [Real.exp_log hnR, Real.exp_log (by positivity : (0 : ℝ) < q)]

/-- Casting the exact finite packing sum to `ℝ` gives the analytic finite
theta sum, term by term.
@isnad1 id=eq.2h2v.s5.038cc1ff6b9c from=translated src=- shape=9acbe73a vocab=eae22e74
-/
theorem ratCast_finiteUQ_eq_finiteThetaSum {q n : ℕ} (hq : 1 < q)
    (hn : 0 < n) :
    ((finiteUQ n q : ℚ) : ℝ) =
      finiteThetaSum (q : ℝ) (indexLog q n) := by
  rw [finiteUQ, finiteThetaSum, natFloor_indexLog]
  push_cast
  let f : ℕ → ℝ := fun r ↦
    (n : ℝ) ^ r /
      (((gammaQ q r : ℚ) : ℝ) * (q : ℝ) ^ (r * r))
  change (∑ r : Fin (Nat.log q n + 1), f r.1) = _
  rw [Fin.sum_univ_eq_sum_range f]
  unfold f
  apply Finset.sum_congr rfl
  intro r hr
  rw [exp_log_band_term hq hn, ← ratCast_gammaQ_eq_gammaR q r (by omega)]
  have hgamma : gammaQ q r ≠ 0 := (gammaQ_pos hq).ne'
  norm_num [div_eq_mul_inv, hgamma]
  ring

/-- Rational packing followed by the exact real change of variables.
@isnad1 id=le.3h3v.s6.6cfe830dba66 from=translated src=- shape=6a5d22be vocab=00e352cb
-/
theorem interval_card_le_finiteThetaSum {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℝ) ≤
      finiteThetaSum (q : ℝ) (indexLog q H.index) := by
  have hQ := finiteU_bound hn hq hqp
  have hR :
      (((Nat.card (interval H) : ℚ) : ℝ)) ≤
        ((finiteUQ H.index q : ℚ) : ℝ) := by
    exact_mod_cast hQ
  rw [ratCast_finiteUQ_eq_finiteThetaSum hq (by omega)] at hR
  exact_mod_cast hR

/-- General base form of the sharp analytic interval bound.  It applies to
every integer growth base not exceeding the least prime divisor of the
ambient index.
@isnad1 id=lt.3h3v.s6.cbf0644e44d9 from=translated src=- shape=6515ac44 vocab=9952fb4c
-/
theorem interval_card_lt_sharpConstant {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (q : ℝ) * sharpScale q H.index := by
  exact (interval_card_le_finiteThetaSum hn hq hqp).trans_lt
    (finiteThetaSum_lt (by exact_mod_cast (show 2 ≤ q by omega))
      (indexLog_nonneg hq (by omega)))

/-- The exponential scale agrees exactly with the conventional real-power
notation in the manuscript.
@isnad1 id=eq.2h2v.s5.400f3a022ec5 from=translated src=- shape=400d6e50 vocab=d8244674
-/
theorem sharpScale_eq_rpow {q n : ℕ} (hq : 1 < q) (hn : 0 < n) :
    sharpScale q n = (n : ℝ) ^ (indexLog q n / 4) := by
  rw [sharpScale, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  unfold indexLog
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  congr 1
  field_simp

/-- The least-prime-divisor form of the manuscript's main finite-group
theorem.
@isnad1 id=lt.1h2v.s5.7bfb48e234a0 from=translated src=- shape=417ba7bc vocab=0578fc5b
-/
theorem interval_card_lt_leastPrime {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (H.index.minFac : ℝ) *
        sharpScale H.index.minFac H.index := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact interval_card_lt_sharpConstant hn hp.one_lt le_rfl

/-- Least-prime bound in the literal real-power notation of Theorem 1.1.
@isnad1 id=lt.1h2v.s6.b9940ea21d00 from=translated src=- shape=594db42e vocab=473b93b0
-/
theorem interval_card_lt_leastPrime_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (H.index.minFac : ℝ) *
        (H.index : ℝ) ^
          (indexLog H.index.minFac H.index / 4) := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  rw [← sharpScale_eq_rpow hp.one_lt (by omega)]
  exact interval_card_lt_leastPrime hn

/-- The two inequalities in the finite main theorem, packaged together:
first the exact rational finite sum and then its strict theta simplification.
@isnad1 id=and.1h2v.s6.473bc96718f1 from=translated src=- shape=90542125 vocab=dc3b66b4
-/
theorem finiteU_and_sharp_leastPrime {H : Subgroup G} (hn : 1 < H.index) :
    ((Nat.card (interval H) : ℚ) ≤
        finiteUQ H.index H.index.minFac) ∧
      (Nat.card (interval H) : ℝ) <
        sharpConstant (H.index.minFac : ℝ) *
          (H.index : ℝ) ^
            (indexLog H.index.minFac H.index / 4) := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact ⟨finiteU_bound hn hp.one_lt le_rfl,
    interval_card_lt_leastPrime_rpow hn⟩

/-- Universal sharp bound, obtained by taking the uniform growth base `2`.
@isnad1 id=lt.1h2v.s5.fabf6fe092fd from=translated src=- shape=99cd259f vocab=db3aa7c3
-/
theorem interval_card_lt_universal {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant 2 * sharpScale 2 H.index := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact interval_card_lt_sharpConstant hn (by norm_num) hp.two_le

/-- Universal bound in the literal `n ^ ((log_2 n)/4)` notation.
@isnad1 id=lt.1h2v.s6.bb37eb69d1a0 from=translated src=- shape=1c9f7893 vocab=6cf1ecc5
-/
theorem interval_card_lt_universal_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant 2 * (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by
  rw [← sharpScale_eq_rpow (q := 2) (n := H.index) (by norm_num) (by omega)]
  exact interval_card_lt_universal hn

/-- A fully rational decimal coefficient above the universal sharp constant.
@isnad1 id=lt.1h2v.s6.e945e70ff9c3 from=translated src=- shape=c70b7ccd vocab=d9fdd93a
-/
theorem interval_card_lt_universal_decimal {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      ((3685984401 : ℝ) / 500000000) *
        (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by
  have hscale : 0 < (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by positivity
  exact (interval_card_lt_universal_rpow hn).trans
    (mul_lt_mul_of_pos_right sharpConstant_two_lt_decimal hscale)

/-- The elementary generating-set estimate from the introduction, in its
literal real-power form.
@isnad1 id=le.1h2v.s5.b779ee99cfe7 from=translated src=- shape=7bec3243 vocab=6ea4d988
-/
theorem elementary_interval_bound_rpow {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) ≤
      (H.index : ℝ) ^ indexLog 2 H.index := by
  have hnat := elementary_interval_bound hn
  have hcast :
      (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := by
    exact_mod_cast hnat
  calc
    (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := hcast
    _ = (H.index : ℝ) ^ (Nat.log 2 H.index : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (H.index : ℝ) ^ indexLog 2 H.index := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ H.index by omega))
      rw [indexLog, Real.log_div_log]
      exact Real.natLog_le_logb H.index 2

/-- All-index form of the elementary generating-set estimate in real-power
notation, including the singleton interval of index one.
@isnad1 id=le.0h2v.s5.5bca2e5d2b80 from=translated src=- shape=9e3258af vocab=c2c2e623
-/
theorem elementary_interval_bound_rpow_all (H : Subgroup G) :
    (Nat.card (interval H) : ℝ) ≤
      (H.index : ℝ) ^ indexLog 2 H.index := by
  have hnat := elementary_interval_bound_all H
  have hcast :
      (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := by
    exact_mod_cast hnat
  have hindex : 1 ≤ H.index :=
    Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  calc
    (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := hcast
    _ = (H.index : ℝ) ^ (Nat.log 2 H.index : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (H.index : ℝ) ^ indexLog 2 H.index := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hindex)
      rw [indexLog, Real.log_div_log]
      exact Real.natLog_le_logb H.index 2

end

end SharpIntermediateSubgroupBounds
