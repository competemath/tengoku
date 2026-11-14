import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusTotientAsymptotics
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decay of the finite Type I main term

The von Mangoldt/totient coefficient sum has an elementary logarithmic bound.
Combining it with the proved shared-prime correction limit reduces decay of
`Q(U,V)` to explicit cancellation hypotheses for the odd Möbius/totient sum.
No prime-distribution or twin-prime estimate is assumed implicitly.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

/-- The nonnegative coefficient multiplying `F(U)` in the Type I main term.-/
def oddMangoldtTotientSum (V : ℕ) : ℝ :=
  ∑ b ∈ oddCutoff V, vonMangoldt b / Nat.totient b

theorem oddMangoldtTotientSum_nonneg (V : ℕ) : 0 ≤ oddMangoldtTotientSum V := by
  unfold oddMangoldtTotientSum
  apply sum_nonneg
  intro b _
  exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- On prime powers, Euler's totient is at least half the argument.-/
theorem primePower_le_two_totient {b : ℕ} (hb : IsPrimePow b) : b ≤ 2 * Nat.totient b := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff b).mp hb
  cases k with
  | zero => omega
  | succ k =>
    have h : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
    calc
      p ^ (k + 1) = p ^ k * p := pow_succ _ _
      _ ≤ p ^ k * (2 * (p - 1)) := Nat.mul_le_mul_left _ h
      _ = 2 * Nat.totient (p ^ (k + 1)) := by
        rw [Nat.totient_prime_pow_succ hp]
        ring

theorem mangoldt_div_totient_le (b : ℕ) :
    vonMangoldt b / Nat.totient b ≤ 2 * vonMangoldt b / (b : ℝ) := by
  by_cases hb : IsPrimePow b
  · have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb.ne_zero
    have hφ : (0 : ℝ) < Nat.totient b := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb.ne_zero)
    have hbφ : (b : ℝ) ≤ 2 * Nat.totient b := by exact_mod_cast primePower_le_two_totient hb
    apply (div_le_div_iff₀ hφ hb0).mpr
    calc
      _ ≤ vonMangoldt b * (2 * Nat.totient b) :=
        mul_le_mul_of_nonneg_left hbφ vonMangoldt_nonneg
      _ = _ := by ring
  · simp [vonMangoldt_eq_zero_iff.mpr hb]

/-- A sufficient elementary coefficient bound. It costs two logarithms and
uses only the harmonic-sum bound and prime-power support of `Λ`.-/
theorem oddMangoldtTotientSum_le_log_sq (V : ℕ) :
    oddMangoldtTotientSum V ≤ 6 * (Real.log ((V : ℝ) + 1)) ^ 2 := by
  by_cases hV : V = 0
  · simp [hV, oddMangoldtTotientSum, oddCutoff]
  have hVpos : 0 < V := Nat.pos_of_ne_zero hV
  let L : ℝ := Real.log ((V : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) V; linarith)
  have hlogV : Real.log V ≤ L :=
    Real.log_le_log (by exact_mod_cast hVpos) (by linarith)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    linarith
  have hLhalf : (1 : ℝ) / 2 ≤ L := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ V + 1 by omega)))
  have hH : (harmonic V : ℝ) ≤ 3 * L := (harmonic_le_one_add_log V).trans (by linarith)
  have hHsum : (∑ b ∈ Icc 1 V, (b : ℝ)⁻¹) = (harmonic V : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    oddMangoldtTotientSum V ≤ ∑ b ∈ oddCutoff V, 2 * L / (b : ℝ) := by
      unfold oddMangoldtTotientSum
      apply sum_le_sum
      intro b hb
      have hbI := mem_Icc.mp (mem_filter.mp hb).1
      have hb0 : (0 : ℝ) < b := by exact_mod_cast hbI.1
      have hbV : (b : ℝ) ≤ (V : ℝ) + 1 := by exact_mod_cast (show b ≤ V + 1 by omega)
      have hΛ : vonMangoldt b ≤ L := vonMangoldt_le_log.trans (Real.log_le_log hb0 hbV)
      exact (mangoldt_div_totient_le b).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ (by norm_num)) hb0.le)
    _ ≤ ∑ b ∈ Icc 1 V, 2 * L / (b : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro b _ _
      positivity
    _ = 2 * L * harmonic V := by
      simp only [div_eq_mul_inv, ← mul_sum]
      rw [hHsum]
    _ ≤ 2 * L * (3 * L) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = 6 * (Real.log ((V : ℝ) + 1)) ^ 2 := by dsimp [L]; ring

theorem abs_moebius_mul_oddMangoldtTotientSum_le (U V : ℕ) :
    |oddMoebiusTotientSum U * oddMangoldtTotientSum V| ≤
      6 * |oddMoebiusTotientSum U * (Real.log ((V : ℝ) + 1)) ^ 2| := by
  rw [abs_mul, abs_of_nonneg (oddMangoldtTotientSum_nonneg V)]
  calc
    _ ≤ |oddMoebiusTotientSum U| * (6 * (Real.log ((V : ℝ) + 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left (oddMangoldtTotientSum_le_log_sq V) (abs_nonneg _)
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((V : ℝ) + 1)))]
      ring

/-- The elementary coefficient bound converts logarithmically weighted
cancellation of `F` into decay of the product part of `Q`.-/
theorem tendsto_moebius_mul_oddMangoldtTotientSum
    (U V : ℕ → ℕ)
    (hweighted : Tendsto (fun X =>
      oddMoebiusTotientSum (U X) * (Real.log ((V X : ℝ) + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun X => oddMoebiusTotientSum (U X) * oddMangoldtTotientSum (V X))
      atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hupper : Tendsto (fun X =>
      6 * |oddMoebiusTotientSum (U X) * (Real.log ((V X : ℝ) + 1)) ^ 2|)
      atTop (nhds 0) := by simpa using hweighted.abs.const_mul 6
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · exact Eventually.of_forall (fun X => abs_moebius_mul_oddMangoldtTotientSum_le (U X) (V X))

/-- Decay of the complete Type I main term, including its shared-prime
correction. Both analytic cancellation inputs are displayed explicitly.-/
theorem tendsto_totientTypeIMain
    (hF : Tendsto oddMoebiusTotientSum atTop (nhds 0))
    (U V : ℕ → ℕ) (hU : Tendsto U atTop atTop)
    (hweighted : Tendsto (fun X =>
      oddMoebiusTotientSum (U X) * (Real.log ((V X : ℝ) + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun X => totientTypeIMain (U X) (V X)) atTop (nhds 0) := by
  have h := (tendsto_moebius_mul_oddMangoldtTotientSum U V hweighted).sub
    (tendsto_sharedPrimeCorrection hF U V hU)
  simpa only [sub_zero, oddMangoldtTotientSum,
    ← totientTypeIMain_eq_main_sub_sharedPrimeCorrection] using h

/-- Logarithmically weighted cancellation already implies unweighted
cancellation. This avoids a redundant hypothesis when the cutoffs coincide.-/
theorem tendsto_oddMoebiusTotientSum_of_log_sq
    (hweighted : Tendsto (fun U : ℕ =>
      oddMoebiusTotientSum U * (Real.log ((U : ℝ) + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto oddMoebiusTotientSum atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hupper : Tendsto (fun U : ℕ =>
      4 * |oddMoebiusTotientSum U * (Real.log ((U : ℝ) + 1)) ^ 2|)
      atTop (nhds 0) := by simpa using hweighted.abs.const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with U hU
    change |oddMoebiusTotientSum U| ≤ _
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h
      linarith
    have hLhalf : (1 : ℝ) / 2 ≤ Real.log ((U : ℝ) + 1) := hlog2.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ U + 1 by omega)))
    have hLsq : (1 : ℝ) ≤ 4 * (Real.log ((U : ℝ) + 1)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log ((U : ℝ) + 1) - (1 / 2 : ℝ))]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((U : ℝ) + 1)))]
    nlinarith [mul_le_mul_of_nonneg_left hLsq (abs_nonneg (oddMoebiusTotientSum U))]

/-- With the same growing cutoff in both positions, the sole remaining input
for `Q→0` is the classical cancellation `F(t) log²(t+1)→0`.-/
theorem tendsto_totientTypeIMain_same_cutoff
    (hweighted : Tendsto (fun t : ℕ =>
      oddMoebiusTotientSum t * (Real.log ((t : ℝ) + 1)) ^ 2) atTop (nhds 0))
    (U : ℕ → ℕ) (hU : Tendsto U atTop atTop) :
    Tendsto (fun X => totientTypeIMain (U X) (U X)) atTop (nhds 0) := by
  exact tendsto_totientTypeIMain (tendsto_oddMoebiusTotientSum_of_log_sq hweighted)
    U U hU (hweighted.comp hU)

end TwinPrime.Analytic
