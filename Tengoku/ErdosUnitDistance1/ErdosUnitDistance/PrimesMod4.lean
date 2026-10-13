/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Tengoku

/-!
# Primes in the progressions 1, 3 mod 4

The `j`-th primes `≡ 1, 3 (mod 4)`, their polynomial growth (from
PrimeNumberTheoremAnd's `chebyshev_asymptotic_pnt`), and the product
`m t` of the first `t` primes `≡ 1 (mod 4)`.
-/

open scoped Classical
open Filter

namespace Erdos

/-- If eventually `count p x ≥ x / (4 log x)`, then eventually
`nth p j ≤ (j+2)²`.  (Key step: at `x = (j+2)²` the hypothesis gives
`count p x ≥ (j+2)²/(8 log (j+2)) > j` for large `j`, using
`log y ≤ 2√y`; conclude with `Nat.nth_lt_of_lt_count`.)
@isnad1 id=eventual.1h1v.s6.95892f66a85c from=translated src=- shape=9718fa64 vocab=92e8fe2c
-/
theorem nth_le_sq_of_count_ge (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ᶠ x : ℕ in atTop, (x : ℝ) / (4 * Real.log x) ≤ Nat.count p x) :
    ∀ᶠ j : ℕ in atTop, (Nat.nth p j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by
  have hx : Tendsto (fun j : ℕ => (j + 2) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id_eq]; nlinarith) tendsto_id
  filter_upwards [hx.eventually h, eventually_ge_atTop 255] with j hcount hj
  set y : ℝ := (j : ℝ) + 2 with hy
  have hy257 : (257 : ℝ) ≤ y := by
    have : (255 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    simp only [hy]; linarith
  have hyx : (((j + 2) ^ 2 : ℕ) : ℝ) = y ^ 2 := by push_cast; ring
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hs16 : (16 : ℝ) ≤ Real.sqrt y := by
    have : (16 : ℝ) = Real.sqrt 256 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogy : Real.log y ≤ 2 * Real.sqrt y := by
    have hsq : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (by nlinarith)
    have hls : Real.log (Real.sqrt y) = Real.log y / 2 :=
      Real.log_sqrt (by linarith)
    linarith [hls ▸ hsq]
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  -- the hypothesis at x = (j+2)²
  have hcount' : y ^ 2 / (8 * Real.log y) ≤ (Nat.count p ((j + 2) ^ 2) : ℝ) := by
    have hlog : Real.log (((j + 2) ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
      rw [hyx, show y ^ 2 = y * y by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [hlog, hyx] at hcount
    calc y ^ 2 / (8 * Real.log y) = y ^ 2 / (4 * (2 * Real.log y)) := by ring_nf
    _ ≤ _ := hcount
  -- conclude j < count
  have h8 : 8 * Real.log y ≤ y := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.sqrt y - 16 by linarith) hs0]
  have hjy : (j : ℝ) < y ^ 2 / (8 * Real.log y) := by
    rw [lt_div_iff₀ (by positivity)]
    have hjlt : (j : ℝ) < y := by rw [hy]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
      mul_lt_mul_of_pos_right hjlt (show (0 : ℝ) < y by linarith)]
  have hjc : j < Nat.count p ((j + 2) ^ 2) := by
    have : (j : ℝ) < (Nat.count p ((j + 2) ^ 2) : ℝ) := lt_of_lt_of_le hjy hcount'
    exact_mod_cast this
  have hnth : Nat.nth p j < (j + 2) ^ 2 := Nat.nth_lt_of_lt_count hjc
  calc (Nat.nth p j : ℝ) ≤ (((j + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnth.le
  _ = y ^ 2 := hyx

/-- The `j`-th prime congruent to `3` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j

/-- The `i`-th prime congruent to `1` modulo `4` (must match
`Framework.lean` verbatim). -/
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i

/-! ## Primes in the progressions `1, 3 mod 4` -/

/-- The product `m t = p1 0 * p1 1 * ⋯ * p1 (t-1)` of the first `t` primes
congruent to `1 mod 4`; the repeated unit distance will be (a rescaling of)
a norm-one element above `m t`. -/
noncomputable def m (t : ℕ) : ℕ := ∏ i ∈ Finset.range t, p1 i

/-- [easy] There are infinitely many primes `≡ 3 mod 4`.  Sketch: in
Mathlib as a special case of Dirichlet
(`Nat.forall_exists_prime_gt_and_modEq`), or by the classical elementary
argument.
@isnad1 id=infinite.0h0v.s4.4aa3a4978fe2 from=translated src=- shape=93fec4b9 vocab=97d12efe
-/
theorem infinite_setOf_q3 : {n | n.Prime ∧ n % 4 = 3}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]}.Infinite :=
    Nat.infinite_setOfPred_prime_and_modEq (by norm_num) (by decide)
  convert! h using 2 with n

/-- [easy] There are infinitely many primes `≡ 1 mod 4`.
(Proved by Aristotle, 2026-06-11.)
@isnad1 id=infinite.0h0v.s4.b76f25b047ec from=translated src=- shape=93fec4b9 vocab=97d12efe
-/
theorem infinite_setOf_p1 : {n | n.Prime ∧ n % 4 = 1}.Infinite :=
  Nat.infinite_setOfPred_prime_modEq_one <| by decide

/-- [easy given infinitude] `q3 j` is prime and `≡ 3 mod 4`
(`Nat.nth_mem_of_infinite`).
@isnad1 id=and.0h1v.s4.fc4bbf288e56 from=translated src=- shape=3e5397b1 vocab=c2ca94ea
-/
theorem q3_spec (j : ℕ) : (q3 j).Prime ∧ q3 j % 4 = 3 :=
  Nat.nth_mem_of_infinite infinite_setOf_q3 j

/-- [easy given infinitude] `p1 i` is prime and `≡ 1 mod 4`.
@isnad1 id=and.0h1v.s4.345bc3d071a9 from=translated src=- shape=3e5397b1 vocab=12a22f61
-/
theorem p1_spec (i : ℕ) : (p1 i).Prime ∧ p1 i % 4 = 1 :=
  Nat.nth_mem_of_infinite infinite_setOf_p1 i

/--
@isnad1 id=strictmo.0h0v.s2.ca28e557ac05 from=translated src=- shape=e3d48bcb vocab=d9886fa4
-/
theorem q3_strictMono : StrictMono q3 :=
  Nat.nth_strictMono infinite_setOf_q3

/--
@isnad1 id=strictmo.0h0v.s2.699ecec59fa1 from=translated src=- shape=e3d48bcb vocab=f3232891
-/
theorem p1_strictMono : StrictMono p1 :=
  Nat.nth_strictMono infinite_setOf_p1

/-- [easy] `m t ≥ 2^t` (each prime factor is `≥ 5`).
@isnad1 id=le.0h1v.s4.d3feec7d4e15 from=translated src=- shape=82643d74 vocab=df0fd678
-/
theorem m_ge (t : ℕ) : 2 ^ t ≤ m t := by
  calc 2 ^ t = ∏ _i ∈ Finset.range t, 2 := by simp
  _ ≤ m t := Finset.prod_le_prod' fun i _ => (p1_spec i).1.two_le

end Erdos
