import Tengoku.Seed.NumberTheory.ArithmeticFunction.VonMangoldt
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.SplitIfs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Vaughan decomposition with explicit cutoffs

This file proves the algebraic identity in PLAN.md, Section 6.1. Multiplication
of arithmetic functions is Dirichlet convolution; `ζ` is the function equal to
one on positive integers. Every identity is finite and unconditional. No
distribution estimate or estimate for a shifted prime correlation is used.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- The restriction of an arithmetic function to inputs at most `U`.-/
def cutoffLow (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The restriction of an arithmetic function to inputs strictly above `U`.-/
def cutoffHigh (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] theorem cutoffLow_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    cutoffLow f U n = if n ≤ U then f n else 0 := rfl

@[simp] theorem cutoffHigh_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    cutoffHigh f U n = if U < n then f n else 0 := rfl

theorem cutoffLow_add_cutoffHigh (f : ArithmeticFunction ℝ) (U : ℕ) :
    cutoffLow f U + cutoffHigh f U = f := by
  ext n
  by_cases h : n ≤ U
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

def moebiusLow (U : ℕ) : ArithmeticFunction ℝ := cutoffLow μ U
def moebiusHigh (U : ℕ) : ArithmeticFunction ℝ := cutoffHigh μ U
def mangoldtLow (V : ℕ) : ArithmeticFunction ℝ := cutoffLow vonMangoldt V
def mangoldtHigh (V : ℕ) : ArithmeticFunction ℝ := cutoffHigh vonMangoldt V

/-- Vaughan's identity, including its low von Mangoldt term. It holds at all
natural inputs, including zero, for every pair of natural cutoffs.-/
theorem vaughanIdentity (U V : ℕ) :
    vonMangoldt =
      moebiusLow U * ArithmeticFunction.log -
      moebiusLow U * mangoldtLow V * ζ + mangoldtLow V +
      moebiusHigh U * mangoldtHigh V * ζ := by
  have hm : moebiusLow U + moebiusHigh U = (μ : ArithmeticFunction ℝ) :=
    cutoffLow_add_cutoffHigh _ _
  have hl : mangoldtLow V + mangoldtHigh V = vonMangoldt :=
    cutoffLow_add_cutoffHigh _ _
  have hz : (moebiusLow U + moebiusHigh U) * (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [hm, coe_moebius_mul_coe_zeta]
  have hlow :
      moebiusLow U * mangoldtLow V * ζ +
        moebiusHigh U * mangoldtLow V * ζ = mangoldtLow V := by
    calc
      _ = mangoldtLow V * ((moebiusLow U + moebiusHigh U) * ζ) := by ring
      _ = mangoldtLow V := by rw [hz, mul_one]
  have hhighlow : moebiusHigh U * mangoldtLow V * ζ =
      mangoldtLow V - moebiusLow U * mangoldtLow V * ζ := by
    exact eq_sub_of_add_eq (by simpa [add_comm] using hlow)
  calc
    vonMangoldt = (moebiusLow U + moebiusHigh U) * ArithmeticFunction.log := by
      rw [hm, moebius_mul_log_eq_vonMangoldt]
    _ = moebiusLow U * ArithmeticFunction.log +
        moebiusHigh U * ((mangoldtLow V + mangoldtHigh V) * ζ) := by
      rw [hl, vonMangoldt_mul_zeta, add_mul]
    _ = moebiusLow U * ArithmeticFunction.log +
        moebiusHigh U * mangoldtLow V * ζ +
        moebiusHigh U * mangoldtHigh V * ζ := by ring
    _ = _ := by rw [hhighlow]; ring

/-- The Type I coefficient `c_{U,V}`.-/
def vaughanCoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  moebiusLow U * mangoldtLow V

/-- The nonnegative divisor weight `β_V(r) = ∑ b ∣ r, b > V, Λ(b)`.-/
def vaughanBeta (V : ℕ) : ArithmeticFunction ℝ := mangoldtHigh V * ζ

theorem vaughanCoefficient_apply (U V n : ℕ) :
    vaughanCoefficient U V n =
      ∑ db ∈ n.divisorsAntidiagonal,
        if db.1 ≤ U ∧ db.2 ≤ V then (μ db.1 : ℝ) * vonMangoldt db.2 else 0 := by
  simp only [vaughanCoefficient, mul_apply, moebiusLow, mangoldtLow, cutoffLow_apply]
  apply sum_congr rfl
  intro db hdb
  split_ifs <;> simp_all

theorem vaughanBeta_apply (V n : ℕ) :
    vaughanBeta V n = ∑ b ∈ n.divisors, if V < b then vonMangoldt b else 0 := by
  simp only [vaughanBeta, coe_mul_zeta_apply, mangoldtHigh, cutoffHigh_apply]

theorem vaughanBeta_eq_log_sub (V n : ℕ) :
    vaughanBeta V n = Real.log n -
      ∑ b ∈ n.divisors, if b ≤ V then vonMangoldt b else 0 := by
  have h :
      (mangoldtLow V * (ζ : ArithmeticFunction ℝ)) n + vaughanBeta V n =
        Real.log n := by
    rw [← ArithmeticFunction.add_apply, vaughanBeta, ← add_mul]
    change ((cutoffLow vonMangoldt V + cutoffHigh vonMangoldt V) * ζ) n = _
    rw [cutoffLow_add_cutoffHigh, vonMangoldt_mul_zeta, log_apply]
  rw [coe_mul_zeta_apply] at h
  simpa only [mangoldtLow, cutoffLow_apply] using (eq_sub_iff_add_eq.mpr (by linarith :
    vaughanBeta V n + (∑ b ∈ n.divisors, mangoldtLow V b) = Real.log n))

theorem vaughanBeta_nonneg (V n : ℕ) : 0 ≤ vaughanBeta V n := by
  rw [vaughanBeta_apply]
  exact sum_nonneg fun b _ => by split_ifs <;> positivity

theorem vaughanBeta_le_log (V n : ℕ) : vaughanBeta V n ≤ Real.log n := by
  rw [vaughanBeta_eq_log_sub]
  have h : 0 ≤ ∑ b ∈ n.divisors, if b ≤ V then vonMangoldt b else 0 :=
    sum_nonneg fun b _ => by split_ifs <;> positivity
  linarith

theorem vaughanBeta_eq_zero_of_le (V n : ℕ) (hn : n ≤ V) :
    vaughanBeta V n = 0 := by
  rw [vaughanBeta_apply]
  apply sum_eq_zero
  intro b hb
  have hbn : b ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hb)) (Nat.dvd_of_mem_divisors hb)
  simp [Nat.not_lt.mpr (hbn.trans hn)]

theorem vaughanCoefficient_eq_zero_of_lt (U V n : ℕ) (hn : U * V < n) :
    vaughanCoefficient U V n = 0 := by
  rw [vaughanCoefficient_apply]
  apply sum_eq_zero
  intro db hdb
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hdb).1
  split_ifs with h
  · have hle := Nat.mul_le_mul h.1 h.2
    omega
  · rfl

theorem abs_vaughanCoefficient_le_log (U V n : ℕ) :
    |vaughanCoefficient U V n| ≤ Real.log n := by
  rw [vaughanCoefficient_apply]
  calc
    _ ≤ ∑ db ∈ n.divisorsAntidiagonal,
        |if db.1 ≤ U ∧ db.2 ≤ V then (μ db.1 : ℝ) * vonMangoldt db.2 else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ db ∈ n.divisorsAntidiagonal, vonMangoldt db.2 := by
      apply sum_le_sum
      intro db _
      split_ifs
      · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        have hm : |(μ db.1 : ℝ)| ≤ 1 := by exact_mod_cast
          (ArithmeticFunction.abs_moebius_le_one (n := db.1))
        simpa using mul_le_mul_of_nonneg_right hm (vonMangoldt_nonneg (n := db.2))
      · simp
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => vonMangoldt b), vonMangoldt_sum]

/-- The remaining convolution is bilinear, with both factors strictly above
their respective cutoffs. The factorization is over positive divisors.-/
theorem vaughanBilinear_apply (U V n : ℕ) :
    (moebiusHigh U * vaughanBeta V) n =
      ∑ dr ∈ n.divisorsAntidiagonal,
        if U < dr.1 ∧ V < dr.2 then (μ dr.1 : ℝ) * vaughanBeta V dr.2 else 0 := by
  rw [mul_apply]
  apply sum_congr rfl
  intro dr _
  simp only [moebiusHigh, cutoffHigh_apply]
  by_cases hd : U < dr.1
  · by_cases hr : V < dr.2
    · simp [hd, hr]
    · simp [hd, hr, vaughanBeta_eq_zero_of_le V dr.2 (Nat.le_of_not_gt hr)]
  · simp [hd]

/-- On inputs above `V`, the low von Mangoldt term disappears.-/
theorem vaughanIdentity_apply_of_lt (U V n : ℕ) (hn : V < n) :
    vonMangoldt n = (moebiusLow U * ArithmeticFunction.log) n -
      (vaughanCoefficient U V * ζ) n + (moebiusHigh U * vaughanBeta V) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughanIdentity U V)
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    mangoldtLow, cutoffLow_apply, ite_eq_right (Nat.not_le.mpr hn),
    add_zero, vaughanCoefficient, vaughanBeta, mul_assoc] using h

/-- The finite weighted identity, ready to specialize to the weight `Λ(n+2)`
on a dyadic interval. All hypotheses concern support, not prime distribution.-/
theorem vaughanIdentity_sum (U V : ℕ) (s : Finset ℕ) (w : ℕ → ℝ)
    (hs : ∀ n ∈ s, V < n) :
    (∑ n ∈ s, vonMangoldt n * w n) =
      (∑ n ∈ s, (moebiusLow U * ArithmeticFunction.log) n * w n) -
      (∑ n ∈ s, (vaughanCoefficient U V * ζ) n * w n) +
      ∑ n ∈ s, (moebiusHigh U * vaughanBeta V) n * w n := by
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [vaughanIdentity_apply_of_lt U V n (hs n hn)]
  ring

end TwinPrime.Analytic
