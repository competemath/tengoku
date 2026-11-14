import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusTotient
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Analysis.Normed.Group.Tannery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Consequences of the finite Möbius/totient recurrence

The results in this file propagate an explicitly supplied bound or convergence
statement for `F` to `F_p`. They do not prove the analytic cancellation of `F`.
The constants are uniform over odd primes for the bound, while convergence of
`F_p` is asserted separately for each fixed odd prime.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

private theorem odd_prime_two_lt (p : ℕ) (hp : p.Prime) (hpodd : Odd p) : 2 < p := by
  have hp2 := hp.two_le
  obtain ⟨k, hk⟩ := hpodd
  omega

/-- A global bound for `F` gives a bound for all `F_p`, with the explicit
geometric factor `1/(p-2)`. The bound does not assume cancellation.
@isnad1 id=le.3h3v.s6.b4be7138b517 from=translated src=- shape=0e2b5c4e vocab=51042a24
-/
theorem oddMoebiusTotientSumDivisible_abs_le {M : ℝ}
    (hF : ∀ U : ℕ, |oddMoebiusTotientSum U| ≤ M) (U p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    |oddMoebiusTotientSumDivisible U p| ≤ M / ((p : ℝ) - 2) := by
  have hp2 : (2 : ℝ) < p := by exact_mod_cast odd_prime_two_lt p hp hpodd
  have hq : (0 : ℝ) < p - 1 := by linarith
  have ht : (0 : ℝ) < p - 2 := by linarith
  have hM : 0 ≤ M := (abs_nonneg (oddMoebiusTotientSum 0)).trans (hF 0)
  induction U using Nat.strong_induction_on with
  | h U ih =>
    by_cases hU : U = 0
    · subst U
      simpa [oddMoebiusTotientSumDivisible, oddCutoff] using div_nonneg hM ht.le
    · rw [oddMoebiusTotientSumDivisible_recurrence U p hp hpodd,
        abs_div, abs_neg, abs_of_pos hq]
      calc
        _ ≤ (|oddMoebiusTotientSum (U / p)| +
            |oddMoebiusTotientSumDivisible (U / p) p|) / ((p : ℝ) - 1) :=
          div_le_div_of_nonneg_right (abs_sub _ _) hq.le
        _ ≤ (M + M / ((p : ℝ) - 2)) / ((p : ℝ) - 1) := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact add_le_add (hF _) (ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hU) hp.one_lt))
        _ = M / ((p : ℝ) - 2) := by
          field_simp
          ring

/-- Iterating the exact recurrence `J` times, with the complete remaining term.
The powers in the natural quotient are exact integer cutoffs.
@isnad1 id=eq.2h3v.s7.eb9a61d727d4 from=translated src=- shape=f486740a vocab=2a17e169
-/
theorem oddMoebiusTotientSumDivisible_expansion (U p J : ℕ) (hp : p.Prime)
    (hpodd : Odd p) :
    oddMoebiusTotientSumDivisible U p =
      -(∑ j ∈ range J,
        oddMoebiusTotientSum (U / p ^ (j + 1)) / ((p : ℝ) - 1) ^ (j + 1)) +
      oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J := by
  have hq : (p : ℝ) - 1 ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = -(∑ j ∈ range J,
          oddMoebiusTotientSum (U / p ^ (j + 1)) / ((p : ℝ) - 1) ^ (j + 1)) +
          oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J := ih
      _ = _ := by
        rw [oddMoebiusTotientSumDivisible_recurrence (U / p ^ J) p hp hpodd,
          Nat.div_div_eq_div_mul, ← pow_succ, sum_range_succ]
        simp only [pow_succ]
        field_simp
        ring

/-- If the odd Möbius/totient sum tends to zero, then its portion divisible
by any fixed odd prime also tends to zero. The prime is fixed before the limit;
this theorem does not claim an error rate uniform in a growing prime.
@isnad1 id=tendsto.3h1v.s5.d26a974d5ca0 from=translated src=- shape=264cb0f0 vocab=9cd01958
-/
theorem tendsto_oddMoebiusTotientSumDivisible
    (hF : Tendsto oddMoebiusTotientSum atTop (nhds 0)) (p : ℕ)
    (hp : p.Prime) (hpodd : Odd p) :
    Tendsto (fun U : ℕ => oddMoebiusTotientSumDivisible U p) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_range_of_tendsto oddMoebiusTotientSum hF).exists_norm_le
  have hFM : ∀ U : ℕ, |oddMoebiusTotientSum U| ≤ M := by
    intro U
    simpa only [Real.norm_eq_abs] using hM _ ⟨U, rfl⟩
  have hp2 : (2 : ℝ) < p := by exact_mod_cast odd_prime_two_lt p hp hpodd
  have hq1 : (1 : ℝ) < p - 1 := by linarith
  have hq0 : (0 : ℝ) < p - 1 := by linarith
  have htail : Tendsto
      (fun J : ℕ => (M / ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ J)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq1)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htailSmall : ∀ᶠ J : ℕ in atTop,
      (M / ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ J < ε / 2 :=
    htail.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨J, hJ⟩ := htailSmall.exists
  let S : ℕ → ℝ := fun U => ∑ j ∈ range J,
    oddMoebiusTotientSum (U / p ^ (j + 1)) / ((p : ℝ) - 1) ^ (j + 1)
  have hS : Tendsto S atTop (nhds 0) := by
    have h := tendsto_finsetSum (range J) (fun j _ =>
      (hF.comp (Nat.tendsto_div_const_atTop (pow_ne_zero (j + 1) hp.ne_zero))).div_const
        (((p : ℝ) - 1) ^ (j + 1)))
    simpa [S] using h
  have hSabs : Tendsto (fun U => |S U|) atTop (nhds 0) := by simpa using hS.abs
  have hSSmall : ∀ᶠ U : ℕ in atTop, |S U| < ε / 2 :=
    hSabs.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hSSmall
  refine ⟨U₀, fun U hU => ?_⟩
  have hrem :
      |oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J| ≤
        (M / ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ J := by
    rw [abs_div, abs_of_pos (pow_pos hq0 _)]
    exact div_le_div_of_nonneg_right
      (oddMoebiusTotientSumDivisible_abs_le hFM _ p hp hpodd) (pow_pos hq0 _).le
  rw [Real.dist_eq, sub_zero, oddMoebiusTotientSumDivisible_expansion U p J hp hpodd]
  change |-S U + oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J| < ε
  calc
    _ ≤ |S U| +
        |oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J| := by
      simpa only [abs_neg] using abs_add_le (-S U)
        (oddMoebiusTotientSumDivisible (U / p ^ J) p / ((p : ℝ) - 1) ^ J)
    _ ≤ |S U| + (M / ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ J := add_le_add le_rfl hrem
    _ < ε := by linarith [hU₀ U hU]

/-- A summable majorant for the prime-power coefficient after the uniform
`F_p` bound. The estimate uses only `log p≤p`, not prime distribution.
@isnad1 id=le.3h2v.s7.75adbba02dc8 from=translated src=- shape=aab328e6 vocab=db62aad7
-/
theorem primePowerTotientWeight_le (p k : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hk : 0 < k) :
    (Real.log p / ((p : ℝ) * Nat.totient (p ^ k))) / ((p : ℝ) - 2) ≤
      (12 / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ k := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast odd_prime_two_lt p hp hpodd
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hp2 : (0 : ℝ) < p - 2 := by linarith
  have hpD : (p : ℝ) ^ 2 ≤ 6 * ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
    nlinarith [sq_nonneg ((p : ℝ) - 3)]
  have hlog : Real.log p ≤ (p : ℝ) :=
    (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  cases k with
  | zero => omega
  | succ k =>
    have hpow : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by linarith) _
    have hdenom : (p : ℝ) ^ 2 * (2 : ℝ) ^ k ≤
        6 * ((p : ℝ) ^ k * (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
      calc
        _ ≤ (6 * ((p : ℝ) - 1) * ((p : ℝ) - 2)) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hpD (by positivity)
        _ ≤ (6 * ((p : ℝ) - 1) * ((p : ℝ) - 2)) * (p : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = _ := by ring
    rw [Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    calc
      _ = Real.log p / ((p : ℝ) ^ (k + 1) * (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
        field_simp
        ring
      _ ≤ (p : ℝ) / ((p : ℝ) ^ (k + 1) * (((p : ℝ) - 1) * ((p : ℝ) - 2))) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      _ = 1 / ((p : ℝ) ^ k * (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
        field_simp
        ring
      _ ≤ 6 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ k) :=
        (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hdenom)
      _ = _ := by
        rw [pow_succ]
        simp only [div_pow]
        field_simp
        ring

/-- The exact shared-prime correction subtracted from the product main term.-/
def sharedPrimeCorrection (U V : ℕ) : ℝ :=
  ∑ pk ∈ oddPrimePowerPairs V,
    (Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))) *
      oddMoebiusTotientSumDivisible U pk.1

/--
@isnad1 id=eq.0h2v.s5.5b1a8ccc50a6 from=translated src=- shape=b715d413 vocab=fe9c0cb2
-/
theorem totientTypeIMain_eq_main_sub_sharedPrimeCorrection (U V : ℕ) :
    totientTypeIMain U V =
      oddMoebiusTotientSum U *
        (∑ b ∈ oddCutoff V, ArithmeticFunction.vonMangoldt b / Nat.totient b) -
      sharedPrimeCorrection U V :=
  totientTypeIMain_eq_primePowerCorrection U V

private def primePowerCorrectionSummand (U V : ℕ) (pk : ℕ × ℕ) : ℝ :=
  if pk ∈ oddPrimePowerPairs V then
    (Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))) *
      oddMoebiusTotientSumDivisible U pk.1 else 0

private theorem sharedPrimeCorrection_eq_tsum (U V : ℕ) :
    sharedPrimeCorrection U V = ∑' pk, primePowerCorrectionSummand U V pk := by
  symm
  calc
    _ = ∑ pk ∈ oddPrimePowerPairs V, primePowerCorrectionSummand U V pk :=
      tsum_eq_sum (fun pk hpk => by simp [primePowerCorrectionSummand, hpk])
    _ = sharedPrimeCorrection U V := by
      unfold sharedPrimeCorrection
      apply sum_congr rfl
      intro pk hpk
      simp [primePowerCorrectionSummand, hpk]

private theorem abs_primePowerCorrectionSummand_le {M : ℝ}
    (hF : ∀ U : ℕ, |oddMoebiusTotientSum U| ≤ M) (U V : ℕ) (pk : ℕ × ℕ) :
    |primePowerCorrectionSummand U V pk| ≤
      (12 * M / (pk.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pk.2 := by
  have hM : 0 ≤ M := (abs_nonneg (oddMoebiusTotientSum 0)).trans (hF 0)
  unfold primePowerCorrectionSummand
  split_ifs with hpk
  · simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc] at hpk
    have hp := hpk.1.1.2.1
    have hpodd := hpk.1.1.2.2
    have hk : 0 < pk.2 := hpk.1.2.1
    have hc : 0 ≤ Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2)) := by
      have hlog : 0 ≤ Real.log pk.1 := Real.log_nonneg (by exact_mod_cast hp.one_le)
      positivity
    rw [abs_mul, abs_of_nonneg hc]
    calc
      _ ≤ (Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))) *
          (M / ((pk.1 : ℝ) - 2)) := mul_le_mul_of_nonneg_left
        (oddMoebiusTotientSumDivisible_abs_le hF U pk.1 hp hpodd) hc
      _ = M * ((Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))) /
          ((pk.1 : ℝ) - 2)) := by ring
      _ ≤ M * ((12 / (pk.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pk.2) :=
        mul_le_mul_of_nonneg_left (primePowerTotientWeight_le pk.1 pk.2 hp hpodd hk) hM
      _ = _ := by ring
  · simpa only [abs_zero] using
      (show 0 ≤ (12 * M / (pk.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pk.2 by positivity)

private theorem tendsto_primePowerCorrectionSummand
    (hF : Tendsto oddMoebiusTotientSum atTop (nhds 0))
    (U V : ℕ → ℕ) (hU : Tendsto U atTop atTop) (pk : ℕ × ℕ) :
    Tendsto (fun X => primePowerCorrectionSummand (U X) (V X) pk) atTop (nhds 0) := by
  by_cases hvalid : pk.1.Prime ∧ Odd pk.1 ∧ 0 < pk.2
  · let c : ℝ := Real.log pk.1 / ((pk.1 : ℝ) * Nat.totient (pk.1 ^ pk.2))
    let a : ℕ → ℝ := fun X => if pk ∈ oddPrimePowerPairs (V X) then c else 0
    have ha : ∀ᶠ X : ℕ in atTop, |a X| ≤ |c| := by
      filter_upwards with X
      dsimp only [a]
      split_ifs <;> simp
    have hmul := bdd_le_mul_tendsto_zero' |c| ha
      ((tendsto_oddMoebiusTotientSumDivisible hF pk.1 hvalid.1 hvalid.2.1).comp hU)
    simpa only [a, c, primePowerCorrectionSummand, ite_mul, zero_mul, Function.comp_apply] using hmul
  · have heq : (fun X => primePowerCorrectionSummand (U X) (V X) pk) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext X
      unfold primePowerCorrectionSummand
      rw [ite_eq_right]
      intro hpk
      simp only [oddPrimePowerPairs, mem_filter, mem_product, mem_Icc] at hpk
      exact hvalid ⟨hpk.1.1.2.1, hpk.1.1.2.2, hpk.1.2.1⟩
    rw [heq]
    exact tendsto_const_nhds

/-- The full shared-prime correction tends to zero, using domination over the
actual `(prime, exponent)` pairs. Only the cancellation `F→0` is assumed.
`V` may be arbitrary; only the first cutoff must tend to infinity.
@isnad1 id=tendsto.2h2v.s6.0714afb343a9 from=translated src=- shape=af11f4a8 vocab=be63b951
-/
theorem tendsto_sharedPrimeCorrection
    (hF : Tendsto oddMoebiusTotientSum atTop (nhds 0))
    (U V : ℕ → ℕ) (hU : Tendsto U atTop atTop) :
    Tendsto (fun X => sharedPrimeCorrection (U X) (V X)) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_range_of_tendsto oddMoebiusTotientSum hF).exists_norm_le
  have hFM : ∀ U : ℕ, |oddMoebiusTotientSum U| ≤ M := by
    intro U
    simpa only [Real.norm_eq_abs] using hM _ ⟨U, rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg (oddMoebiusTotientSum 0)).trans (hFM 0)
  have hP : Summable (fun p : ℕ => 12 * M / (p : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (show 1 < (2 : ℕ) by omega)).mul_left (12 * M)
  have hsum : Summable (fun pk : ℕ × ℕ =>
      (12 * M / (pk.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ pk.2) :=
    hP.mul_of_nonneg summable_geometric_two (fun _ => by positivity) (fun _ => by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun pk => tendsto_primePowerCorrectionSummand hF U V hU pk)
    (Eventually.of_forall (fun X pk => by
      simpa only [Real.norm_eq_abs] using abs_primePowerCorrectionSummand_le hFM (U X) (V X) pk))
  simpa only [tsum_zero, ← sharedPrimeCorrection_eq_tsum] using h

end TwinPrime.Analytic
