import Tengoku.Twinprime.TwinPrime.Analytic.LogPowerDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.ClassicalDistribution
import Tengoku.Twinprime.TwinPrime.Sieve.ErrorSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Squarefree divisor weights on progression errors

Elementary progression counting and divisor moments turn the actual unweighted
Bombieri--Vinogradov estimate into a bound with 3^omega weights. Squarefree
support remains explicit throughout.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace TwinPrime.Analytic

/-- Dividing by the modulus injects any one residue class through t into
the quotient interval. The extra one covers its first incomplete block.
@isnad1 id=le.0h3v.s5.f890bb96cd97 from=translated src=- shape=ec58a473 vocab=c97496c4
-/
theorem card_progression_le_div_add_one (t q a : ℕ) :
    ((Ioc 0 t).filter (fun n => Nat.ModEq q n a)).card ≤ t / q + 1 := by
  have hcard := card_le_card_of_injOn (s := (Ioc 0 t).filter (fun n => Nat.ModEq q n a))
    (t := range (t / q + 1)) (fun n => n / q) (fun n hn => by
      exact mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (mem_Ioc.mp (mem_filter.mp hn).1).2))) (by
      intro n hn m hm hnm
      have hmod : n % q = m % q :=
        (mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm
      have hn' := Nat.mod_add_div n q
      have hm' := Nat.mod_add_div m q
      dsimp only at hnm
      rw [hnm, hmod] at hn'
      exact hn'.symm.trans hm')
  simpa only [card_range] using hcard

/-- A trivial but uniform progression estimate, with the modulus retained
in the denominator. It applies to every residue, including nonreduced ones.
@isnad1 id=le.3h4v.s6.e900408ef5df from=translated src=- shape=da784aaa vocab=ffcd4ce2
-/
theorem progressionPsi_le_two_mul_div_mul_log (t Y q a : ℕ)
    (ht : t ≤ Y) (hq : 1 ≤ q) (hqY : q ≤ Y) :
    progressionPsi t q a ≤ 2 * (Y : ℝ) / q * Real.log Y := by
  have hY : 1 ≤ Y := hq.trans hqY
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY)
  have hcard : (((Ioc 0 t).filter (fun n => Nat.ModEq q n a)).card : ℝ) ≤
      2 * (Y : ℝ) / q := by
    calc
      _ ≤ ((t / q + 1 : ℕ) : ℝ) := by exact_mod_cast card_progression_le_div_add_one t q a
      _ ≤ (t : ℝ) / q + 1 := by
        push_cast
        exact add_le_add (Nat.cast_div_le (m := t) (n := q) (α := ℝ)) le_rfl
      _ ≤ (Y : ℝ) / q + 1 := by gcongr
      _ ≤ 2 * (Y : ℝ) / q := by
        have h1 : (1 : ℝ) ≤ (Y : ℝ) / q :=
          (le_div_iff₀ hq0).mpr (by simpa using (show (q : ℝ) ≤ Y by exact_mod_cast hqY))
        rw [mul_div_assoc]
        linarith
  calc
    _ ≤ ∑ _n ∈ (Ioc 0 t).filter (fun n => Nat.ModEq q n a), Real.log Y := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := (mem_Ioc.mp (mem_filter.mp hn).1).1
      exact (vonMangoldt_le_log (n := n)).trans (Real.log_le_log
        (by exact_mod_cast hn0) (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2.trans ht))
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hcard hlog

/-- Pointwise domination used only in the second weighted moment. The
first moment will retain the proved cancellation in Bombieri--Vinogradov.
@isnad1 id=le.2h2v.s6.5442daadcf26 from=translated src=- shape=294201de vocab=4b9a5110
-/
theorem progressionMaxError_le_totient_trivial (Y q : ℕ)
    (hq : 1 ≤ q) (hqY : q ≤ Y) :
    progressionMaxError Y q ≤ 3 * (Y : ℝ) * (1 + Real.log Y) / Nat.totient q := by
  have hY : 1 ≤ Y := hq.trans hqY
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY)
  unfold progressionMaxError
  apply sup'_le
  intro ta hta
  have ht : ta.1 ≤ Y := by have := mem_range.mp (mem_product.mp hta).1; omega
  split_ifs
  · have hψ := progressionPsi_le_two_mul_div_mul_log ta.1 Y q ta.2 ht hq hqY
    have hψ0 : 0 ≤ progressionPsi ta.1 q ta.2 :=
      sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    have ht0 : (0 : ℝ) ≤ ta.1 := Nat.cast_nonneg _
    have htY : (ta.1 : ℝ) ≤ Y := by exact_mod_cast ht
    calc
      _ ≤ progressionPsi ta.1 q ta.2 + (ta.1 : ℝ) / Nat.totient q := by
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hψ0, abs_of_nonneg (by positivity)])
      _ ≤ 2 * (Y : ℝ) / Nat.totient q * Real.log Y + (Y : ℝ) / Nat.totient q := by
        gcongr
        exact hψ.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
          (by positivity) hφ hφq) hlog)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div, ← add_div]
        apply (div_le_div_iff_of_pos_right hφ).mpr
        nlinarith
  · positivity

/-- A uniform elementary comparison of the totient with the number of
distinct prime factors. This comparison itself does not require squarefreeness.
@isnad1 id=le.1h1v.s6.44f1c006ebb2 from=translated src=- shape=bf382fd9 vocab=ce24d00f
-/
theorem div_totient_le_two_pow_omega (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / Nat.totient m ≤ (2 : ℝ) ^ ω m := by
  have hprod : (∏ p ∈ m.primeFactors, p) ≤
      2 ^ m.primeFactors.card * ∏ p ∈ m.primeFactors, (p - 1) := by
    calc
      _ ≤ ∏ p ∈ m.primeFactors, 2 * (p - 1) := by
        apply prod_le_prod'
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      _ = _ := by rw [prod_mul_distrib, prod_const]
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    apply prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmul := Nat.mul_le_mul_left (Nat.totient m) hprod
  rw [Nat.totient_mul_prod_primeFactors] at hmul
  have hnat : m ≤ 2 ^ m.primeFactors.card * Nat.totient m := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hw : ω m = m.primeFactors.card := by
    rw [← Nat.toFinset_factors, List.card_toFinset]
    rfl
  rw [hw, div_le_iff₀ (show (0 : ℝ) < Nat.totient m from
    by exact_mod_cast Nat.totient_pos.mpr hm)]
  exact_mod_cast hnat

/--
@isnad1 id=le.1h1v.s6.3c9be584d76d from=translated src=- shape=fa5e28f3 vocab=ce24d00f
-/
theorem one_div_totient_le_two_pow_omega_div (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / Nat.totient m ≤ (2 : ℝ) ^ ω m / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hm0]
  simpa only [one_div_mul_eq_div] using div_totient_le_two_pow_omega m hm

/-- The second moment needed by weighted Cauchy--Schwarz has only a fixed
logarithmic cost. Its proof uses squarefreeness in the divisor moment.
@isnad1 id=le.3h3v.s7.75e814085496 from=translated src=- shape=346f15b3 vocab=b07d7f0c
-/
theorem squarefree_nine_pow_omega_mul_error_le (P Q Y : ℕ)
    (hP : Squarefree P) (hY : 1 ≤ Y) (hQY : Q ≤ Y) :
    (∑ d ∈ P.divisors.filter (· ≤ Q),
      (9 : ℝ) ^ ω d * progressionMaxError Y d) ≤
      3 * (Y : ℝ) * (1 + Real.log Y) ^ 19 := by
  have hL : 0 ≤ 1 + Real.log Y := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)
    linarith
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (· ≤ Q),
        (3 * (Y : ℝ) * (1 + Real.log Y)) * ((18 : ℝ) ^ ω d / d) := by
      apply sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
      have hdY : d ≤ Y := (mem_filter.mp hd).2.trans hQY
      calc
        _ ≤ (9 : ℝ) ^ ω d * (3 * Y * (1 + Real.log Y) / Nat.totient d) :=
          mul_le_mul_of_nonneg_left (progressionMaxError_le_totient_trivial Y d hd0 hdY)
            (by positivity)
        _ = (3 * Y * (1 + Real.log Y)) *
            ((9 : ℝ) ^ ω d * (1 / Nat.totient d)) := by ring
        _ ≤ (3 * Y * (1 + Real.log Y)) * ((9 : ℝ) ^ ω d * ((2 : ℝ) ^ ω d / d)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (one_div_totient_le_two_pow_omega_div d hd0) (by positivity)) (by positivity)
        _ = _ := by rw [← mul_div_assoc, ← mul_pow]; norm_num
    _ = (3 * (Y : ℝ) * (1 + Real.log Y)) *
        ∑ d ∈ P.divisors.filter (· ≤ Q), (18 : ℝ) ^ ω d / d := by rw [mul_sum]
    _ ≤ (3 * (Y : ℝ) * (1 + Real.log Y)) * (1 + Real.log Y) ^ 18 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply le_trans (sum_le_sum_of_subset_of_nonneg (show
        P.divisors.filter (· ≤ Q) ⊆ P.divisors.filter (fun d => (d : ℝ) ≤ Y) from
        fun d hd => mem_filter.mpr ⟨(mem_filter.mp hd).1,
          by exact_mod_cast (mem_filter.mp hd).2.trans hQY⟩) (fun d _ _ => by positivity))
      rw [sum_filter]
      exact TwinPrime.Sieve.sum_pow_cardDistinctFactors_div_self_le_log_pow
        (k := 18) (Y : ℝ) (by exact_mod_cast hY) hP
    _ = _ := by ring

/-- The actual squarefree-supported weighted progression-error sum.-/
def squarefreeWeightedProgressionError (P Q Y : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.filter (· ≤ Q), (3 : ℝ) ^ ω d * progressionMaxError Y d

/--
@isnad1 id=le.0h3v.s4.2b335e45dc16 from=translated src=- shape=1995cd38 vocab=abb862e6
-/
theorem squarefreeWeightedProgressionError_nonneg (P Q Y : ℕ) :
    0 ≤ squarefreeWeightedProgressionError P Q Y :=
  sum_nonneg (fun d _ => mul_nonneg (by positivity) (progressionMaxError_nonneg Y d))

/-- Finite weighted Cauchy--Schwarz retains the actual unweighted
progression-error sum. No weighted distribution hypothesis is supplied.
@isnad1 id=le.3h3v.s7.19b3960097c2 from=translated src=- shape=0b041c4e vocab=4366493e
-/
theorem squarefree_weighted_progressionMaxError_sq_le (P Q Y : ℕ)
    (hP : Squarefree P) (hY : 1 ≤ Y) (hQY : Q ≤ Y) :
    squarefreeWeightedProgressionError P Q Y ^ 2 ≤
      3 * (Y : ℝ) * (1 + Real.log Y) ^ 19 *
        ∑ q ∈ Icc 1 Q, progressionMaxError Y q := by
  let s := P.divisors.filter (· ≤ Q)
  have hCS := sum_mul_sq_le_sq_mul_sq s
    (fun d => (3 : ℝ) ^ ω d * Real.sqrt (progressionMaxError Y d))
    (fun d => Real.sqrt (progressionMaxError Y d))
  have hleft : (∑ d ∈ s, ((3 : ℝ) ^ ω d * Real.sqrt (progressionMaxError Y d)) *
      Real.sqrt (progressionMaxError Y d)) = squarefreeWeightedProgressionError P Q Y := by
    apply sum_congr rfl
    intro d _
    rw [mul_assoc, ← sq, Real.sq_sqrt (progressionMaxError_nonneg Y d)]
  have hfirst : (∑ d ∈ s, ((3 : ℝ) ^ ω d * Real.sqrt (progressionMaxError Y d)) ^ 2) =
      ∑ d ∈ s, (9 : ℝ) ^ ω d * progressionMaxError Y d := by
    apply sum_congr rfl
    intro d _
    rw [mul_pow, Real.sq_sqrt (progressionMaxError_nonneg Y d), ← pow_mul, mul_comm (ω d) 2,
      pow_mul]
    norm_num
  have hsecond : (∑ d ∈ s, Real.sqrt (progressionMaxError Y d) ^ 2) =
      ∑ d ∈ s, progressionMaxError Y d := by
    apply sum_congr rfl
    intro d _
    exact Real.sq_sqrt (progressionMaxError_nonneg Y d)
  rw [hleft, hfirst, hsecond] at hCS
  apply hCS.trans
  apply mul_le_mul (squarefree_nine_pow_omega_mul_error_le P Q Y hP hY hQY)
    (sum_le_sum_of_subset_of_nonneg (show s ⊆ Icc 1 Q from fun d hd =>
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1, (mem_filter.mp hd).2⟩)
      (fun d _ _ => progressionMaxError_nonneg Y d))
    (sum_nonneg fun d _ => progressionMaxError_nonneg Y d)
  have : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY)
  positivity

end TwinPrime.Analytic
