import Tengoku.Pi2Lean.Row12.Convergence
import Tengoku.Seed.RingTheory.Polynomial.Pochhammer
import Tengoku.Seed.Algebra.BigOperators.Intervals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.coefficient_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.successorProduct_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.factorial_six_step` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient_succ_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.risingProduct_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.risingProduct_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient_eq_risingProduct` (it only prints; the queue checks the axioms of every declaration). -/

namespace Row12

noncomputable def successorProduct (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, ((n : ℝ) + (j : ℝ) / 6)

noncomputable def risingProduct (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, (ascPochhammer ℝ n).eval ((j : ℝ) / 6)

/--
@isnad1 id=eq.0h0v.s3.75ef1957fe4c from=translated src=- shape=1ac31801 vocab=edf8a514
-/
theorem coefficient_zero : coefficient 0 = 1 := by
  norm_num [coefficient]

/--
@isnad1 id=eq.0h1v.s7.dc712cac6bdd from=translated src=- shape=2f2e8481 vocab=f0d6b58d
-/
theorem successorProduct_eq (n : ℕ) :
    successorProduct n =
      ((n : ℝ) + 1 / 6) * ((n : ℝ) + 2 / 6) * ((n : ℝ) + 3 / 6) *
        ((n : ℝ) + 4 / 6) * ((n : ℝ) + 5 / 6) := by
  unfold successorProduct
  norm_num [Finset.prod_Icc_succ_top]

/--
@isnad1 id=eq.0h1v.s8.584a800f51c1 from=translated src=- shape=cfeead11 vocab=3c69b864
-/
theorem factorial_six_step (n : ℕ) :
    (Nat.factorial (6 * (n + 1)) : ℝ) =
      (Nat.factorial (6 * n) : ℝ) * (6 * (n : ℝ) + 1) * (6 * (n : ℝ) + 2) *
        (6 * (n : ℝ) + 3) * (6 * (n : ℝ) + 4) * (6 * (n : ℝ) + 5) *
        (6 * (n : ℝ) + 6) := by
  have hnat : Nat.factorial (6 * (n + 1)) =
      Nat.factorial (6 * n) * (6 * n + 1).ascFactorial 6 := by
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
  have hcast : (Nat.factorial (6 * (n + 1)) : ℝ) =
      (Nat.factorial (6 * n) : ℝ) * ((6 * n + 1).ascFactorial 6 : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  norm_num [Nat.ascFactorial]
  ring

/--
@isnad1 id=eq.0h1v.s6.763a97f19407 from=translated src=- shape=ab71693f vocab=a77d9bee
-/
theorem coefficient_succ_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ 5 * coefficient (n + 1) =
      rho * successorProduct n * coefficient n := by
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold coefficient
  rw [factorial_six_step, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show 6 * (n + 1) = 6 * n + 6 by omega, pow_add, successorProduct_eq]
  unfold rho
  field_simp [hf, hn]
  ring

/--
@isnad1 id=eq.0h1v.s6.c9e3b0650f31 from=translated src=- shape=4b9b1e0b vocab=4737c936
-/
theorem coefficient_succ (n : ℕ) :
    coefficient (n + 1) =
      rho * successorProduct n / ((n : ℝ) + 1) ^ 5 * coefficient n := by
  have hn : ((n : ℝ) + 1) ^ 5 ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  rw [coefficient_succ_mul]
  field_simp

/--
@isnad1 id=eq.0h0v.s3.39cd5684492d from=translated src=- shape=1ac31801 vocab=d1c5ccfc
-/
theorem risingProduct_zero : risingProduct 0 = 1 := by
  simp [risingProduct]

/--
@isnad1 id=eq.0h1v.s4.7d83e6582920 from=translated src=- shape=61b74864 vocab=3e34bb44
-/
theorem risingProduct_succ (n : ℕ) :
    risingProduct (n + 1) = risingProduct n * successorProduct n := by
  unfold risingProduct successorProduct
  simp only [ascPochhammer_succ_eval]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  ring

/--
@isnad1 id=eq.0h1v.s5.4947c6feb317 from=translated src=- shape=07bcad43 vocab=01eb7665
-/
theorem coefficient_eq_risingProduct (n : ℕ) :
    coefficient n = rho ^ n * risingProduct n / (Nat.factorial n : ℝ) ^ 5 := by
  induction n with
  | zero => simp [coefficient_zero, risingProduct_zero]
  | succ n ih =>
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [coefficient_succ, ih, risingProduct_succ, Nat.factorial_succ, pow_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hf, hn]
    ring

end Row12

