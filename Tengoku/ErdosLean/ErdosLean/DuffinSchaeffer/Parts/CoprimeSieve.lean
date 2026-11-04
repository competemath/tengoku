import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.Mertens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Duffin–Schaeffer — Part 7: an upper-bound sieve for integers coprime to `m`

`∑_{1 ≤ h ≤ H, (h,m)=1} gcd(h,g)/φ(gcd(h,g)) ≪ H ∏_{p | m, p ≤ H} (1 - 1/p)`.

Instead of Selberg's Λ² sieve we use the elementary "Chebyshev–Hall–Tenenbaum" argument:
with `F(n) = 1_{(n,m)=1} n/φ(n)` (which dominates the weight since `gcd(h,g) ∣ h`),
* `F(n) log n = ∑_{d ∣ n} Λ(d) F(n) ≤ 2 ∑_{d ∣ n} Λ(d) F(n/d)` (sub-multiplicativity of `n/φ(n)`
  and `d/φ(d) ≤ 2` for prime powers), so by Chebyshev `ψ(x) ≪ x`,
  `∑_{n ≤ N} F(n) log n ≪ N ∑_{n ≤ N} F(n)/n`;
* `log(N/n) ≤ N/n`, hence `(∑_{n≤N} F(n)) log N ≪ N ∑_{n ≤ N, (n,m)=1} 1/φ(n)`;
* the Euler product bounds `∑_{n ≤ N, (n,m)=1} 1/φ(n) ≤ e⁴ ∏_{p ≤ N, p ∤ m} (1 - 1/p)⁻¹`,
  and Mertens' third theorem (upper bound, Part 5) turns this into `≪ log N ∏_{p ∣ m, p ≤ N}(1-1/p)`.
-/

open Finset

namespace DuffinSchaeffer

namespace CoprimeSieveAux

/--
@isnad1 id=eq.0h1v.s5.cfc404a95fb3 from=translated src=- shape=ed341a56 vocab=868f914c
-/
lemma totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at h
  simpa [one_div] using h

/--
@isnad1 id=and.1h1v.s7.9e64bd131fb7 from=translated src=- shape=5431aa29 vocab=edc32717
-/
lemma prime_factor_bounds {p : ℕ} (hp : p.Prime) :
    0 < 1 - (1 : ℝ) / p ∧ 1 - (1 : ℝ) / p ≤ 1 ∧ 1 / 2 ≤ 1 - (1 : ℝ) / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (1 : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h4 : 0 ≤ (1 : ℝ) / p := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

/--
@isnad1 id=le.1h1v.s5.0f4131fd294b from=translated src=- shape=68ef3600 vocab=ee6aa6f8
-/
lemma one_le_factor {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - (1 : ℝ) / p)⁻¹ := by
  obtain ⟨h1, h2, -⟩ := prime_factor_bounds hp
  exact (one_le_inv₀ h1).mpr h2

/-- `R n = n / φ(n)`.-/
noncomputable def R (n : ℕ) : ℝ := (n : ℝ) / Nat.totient n

/--
@isnad1 id=le.0h1v.s3.71ecdbfd5316 from=translated src=- shape=b9369acb vocab=20c80ffd
-/
lemma R_nonneg (n : ℕ) : 0 ≤ R n := by unfold R; positivity

/--
@isnad1 id=eq.1h1v.s5.59841d7543bc from=translated src=- shape=87195f25 vocab=8a80d568
-/
lemma R_eq {n : ℕ} (hn : n ≠ 0) : R n = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
  rw [R, totient_real, prod_inv_distrib]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [div_mul_eq_div_div, div_self this, one_div]

/--
@isnad1 id=le.1h1v.s4.29ba615d1c9c from=translated src=- shape=a558fa7c vocab=b8749d43
-/
lemma R_primePow {d : ℕ} (hd : IsPrimePow d) : R d ≤ 2 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  rw [R_eq (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk.ne' hp, prod_singleton]
  obtain ⟨h1, -, h3⟩ := prime_factor_bounds hp
  rw [inv_le_comm₀ h1 (by norm_num)]
  have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  linarith

/--
@isnad1 id=le.2h2v.s5.71bbf906f0c3 from=translated src=- shape=a9e7a3e5 vocab=da60323b
-/
lemma R_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : R (a * b) ≤ R a * R b := by
  unfold R
  have hta : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)
  have htb : (0 : ℝ) < Nat.totient b := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hsup : (Nat.totient a : ℝ) * Nat.totient b ≤ Nat.totient (a * b) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  rw [div_mul_div_comm, Nat.cast_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsup

/-- `F m n = 1_{(n,m)=1} · n/φ(n)`.-/
noncomputable def F (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime m then R n else 0, by simp [R]⟩

/--
@isnad1 id=eq.0h2v.s5.7096498cd673 from=translated src=- shape=d9581454 vocab=f46c67b3
-/
lemma F_apply (m n : ℕ) : F m n = if n.Coprime m then R n else 0 := rfl

/--
@isnad1 id=le.0h2v.s4.57641ffb79bb from=translated src=- shape=f54b5217 vocab=bff17e63
-/
lemma F_nonneg (m n : ℕ) : 0 ≤ F m n := by
  rw [F_apply]; split_ifs
  · exact R_nonneg n
  · exact le_refl 0

/--
@isnad1 id=le.0h2v.s6.8649581623af from=translated src=- shape=f62eb855 vocab=6bb3b8ea
-/
lemma F_mul_log_le (m n : ℕ) :
    F m n * Real.log n ≤ 2 * (ArithmeticFunction.vonMangoldt * F m) n := by
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum, ArithmeticFunction.mul_apply]
  have hd := Nat.sum_divisorsAntidiagonal
    (fun a b => ArithmeticFunction.vonMangoldt a * F m b) (n := n)
  rw [hd, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hid : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hi).2
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt i := ArithmeticFunction.vonMangoldt_nonneg
  by_cases h0 : ArithmeticFunction.vonMangoldt i = 0
  · rw [h0]; simp
  have hpp : IsPrimePow i := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
  have hk0 : n / i ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hi) (Nat.pos_of_ne_zero hi0)).ne'
  have key : F m n ≤ 2 * F m (n / i) := by
    rw [F_apply, F_apply]
    by_cases h1 : n.Coprime m
    · have h2 : (n / i).Coprime m := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hid) h1
      rw [ite_eq_left h1, ite_eq_left h2]
      calc R n = R (i * (n / i)) := by rw [Nat.mul_div_cancel' hid]
        _ ≤ R i * R (n / i) := R_mul_le hi0 hk0
        _ ≤ 2 * R (n / i) := mul_le_mul_of_nonneg_right (R_primePow hpp) (R_nonneg _)
    · rw [ite_eq_right h1]
      split_ifs
      · linarith [R_nonneg (n / i)]
      · norm_num
  calc F m n * ArithmeticFunction.vonMangoldt i
      = ArithmeticFunction.vonMangoldt i * F m n := mul_comm _ _
    _ ≤ ArithmeticFunction.vonMangoldt i * (2 * F m (n / i)) := mul_le_mul_of_nonneg_left key hΛ
    _ = 2 * (ArithmeticFunction.vonMangoldt i * F m (n / i)) := by ring

/--
@isnad1 id=le.0h2v.s7.e603fe386d7c from=translated src=- shape=3555230a vocab=0de8b38a
-/
lemma sum_F_log_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n * Real.log n ≤
      2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  calc ∑ n ∈ Ioc 0 N, F m n * Real.log n
      ≤ ∑ n ∈ Ioc 0 N, 2 * (ArithmeticFunction.vonMangoldt * F m) n :=
        sum_le_sum fun n _ => F_mul_log_le m n
    _ = 2 * ∑ n ∈ Ioc 0 N, (F m * ArithmeticFunction.vonMangoldt) n := by
        rw [← mul_sum, mul_comm ArithmeticFunction.vonMangoldt (F m)]
    _ = 2 * ∑ k ∈ Ioc 0 N, F m k * ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j := by
        rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    _ ≤ 2 * ∑ k ∈ Ioc 0 N, F m k * ((Real.log 4 + 4) * ((N : ℝ) / k)) := by
        gcongr with k hk
        · exact F_nonneg m k
        · have h1 : ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j =
              Chebyshev.psi ((N / k : ℕ) : ℝ) := by
            simp [Chebyshev.psi]
          rw [h1]
          calc Chebyshev.psi ((N / k : ℕ) : ℝ) ≤ (Real.log 4 + 4) * ((N / k : ℕ) : ℝ) :=
                Chebyshev.psi_le_const_mul_self (by positivity)
            _ ≤ (Real.log 4 + 4) * ((N : ℝ) / k) := by
                gcongr
                exact Nat.cast_div_le
    _ = 2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => by ring

/--
@isnad1 id=le.0h2v.s7.92f0804f6283 from=translated src=- shape=9907bca5 vocab=0de8b38a
-/
lemma sum_F_logN_le (m N : ℕ) :
    (∑ n ∈ Ioc 0 N, F m n) * Real.log N ≤
      (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  have h : ∀ n ∈ Ioc 0 N, F m n * Real.log N ≤ F m n * Real.log n + N * (F m n / n) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn.1 hn.2)
    have hlog : Real.log N ≤ Real.log n + N / n := by
      have e : Real.log N = Real.log n + Real.log ((N : ℝ) / n) := by
        rw [Real.log_div hN0.ne' hn0.ne']; ring
      have h2 : Real.log ((N : ℝ) / n) ≤ N / n :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      linarith
    have := F_nonneg m n
    calc F m n * Real.log N ≤ F m n * (Real.log n + N / n) := mul_le_mul_of_nonneg_left hlog this
      _ = _ := by ring
  have hA := sum_F_log_le m N
  have e2 : (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n =
      2 * (Real.log 4 + 4) * N * (∑ n ∈ Ioc 0 N, F m n / n) +
        N * ∑ n ∈ Ioc 0 N, F m n / n := by ring
  calc (∑ n ∈ Ioc 0 N, F m n) * Real.log N = ∑ n ∈ Ioc 0 N, F m n * Real.log N := sum_mul _ _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (F m n * Real.log n + N * (F m n / n)) := sum_le_sum h
    _ = ∑ n ∈ Ioc 0 N, F m n * Real.log n + N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by rw [e2]; linarith

/-- `f n = 1/φ(n)`.-/
noncomputable def f (n : ℕ) : ℝ := 1 / (Nat.totient n : ℝ)

/--
@isnad1 id=le.0h1v.s3.7871dd6f55a4 from=translated src=- shape=b9369acb vocab=9f49a1bc
-/
lemma f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity

/--
@isnad1 id=eq.0h0v.s3.94f837b305c8 from=translated src=- shape=1ac31801 vocab=a3a7c397
-/
lemma f_one : f 1 = 1 := by simp [f]

/--
@isnad1 id=eq.1h2v.s4.c056debb50ff from=translated src=- shape=544cf949 vocab=7b77df54
-/
lemma f_mul {a b : ℕ} (h : Nat.Coprime a b) : f (a * b) = f a * f b := by
  simp [f, Nat.totient_mul h, mul_comm]

/--
@isnad1 id=eq.1h2v.s6.3801cb22aad7 from=translated src=- shape=55f24f7f vocab=7e9830ee
-/
lemma f_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ (k + 1)) = (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
  rw [f, Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le,
    Nat.cast_one, one_div_pow, div_mul_div_comm, one_mul, mul_comm]

/--
@isnad1 id=hassum.1h1v.s6.10807ebc6003 from=translated src=- shape=8cc40a9a vocab=9cb3016e
-/
lemma hasSum_f_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => f (p ^ k)) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / ((p : ℝ) - 1))
  have hg' : HasSum (fun k => f (p ^ (k + 1))) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹) := by
    have : (fun k => f (p ^ (k + 1))) = fun k => (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
      funext k; exact f_pow_succ hp k
    rw [this]; exact hg
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [sum_range_one, pow_zero, f_one, add_sub_cancel_right]
  exact hg'

/--
@isnad1 id=le.1h1v.s7.6ab60e27071e from=translated src=- shape=a9169db9 vocab=ec4afb93
-/
lemma euler_factor_le {p : ℕ} (hp : p.Prime) :
    1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1 ≤
      (1 - 1 / (p : ℝ))⁻¹ * (1 + 2 * ((p : ℝ) ^ 2)⁻¹) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set q : ℝ := (p : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have e1 : (1 - 1 / q)⁻¹ = q / (q - 1) := by rw [one_sub_div hq0, inv_div]
  rw [e1]
  have key : q / (q - 1) * (1 + 2 * (q ^ 2)⁻¹) - (1 / (q - 1) * (q / (q - 1)) + 1) =
      (q - 2) / (q * (q - 1) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (q - 2) / (q * (q - 1) ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/--
@isnad1 id=le.0h2v.s7.af664dc19d14 from=translated src=- shape=bdef6f0f vocab=f4e089a3
-/
lemma sum_F_div_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n / n ≤
      ∏ p ∈ ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m),
        (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  classical
  set s := ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m) with hs
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simpa [Real.norm_eq_abs] using (hasSum_f_pow hp).summable.abs
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := f) f_one (fun h => f_mul h) hsum s
  have hsP : ∀ p ∈ s, p.Prime := fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2
  have hfilt : s.filter Nat.Prime = s := filter_true_of_mem hsP
  have hle : ∑ n ∈ Ioc 0 N, F m n / n = ∑ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), f n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := (mem_Ioc.mp hn).1
      exact_mod_cast this.ne'
    rw [F_apply]
    split_ifs
    · unfold R f
      have ht : (Nat.totient n : ℝ) ≠ 0 := by
        have : 0 < n := (mem_Ioc.mp hn).1
        exact_mod_cast (Nat.totient_pos.mpr this).ne'
      field_simp
    · simp
  rw [hle]
  have hmem : ∀ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), n ∈ Nat.factoredNumbers s := by
    intro n hn
    obtain ⟨hnI, hcop⟩ := mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hnI
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    refine ⟨hn1.ne', fun p hp => ?_⟩
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    simp only [hs, mem_filter, mem_Iic]
    refine ⟨⟨(Nat.le_of_dvd hn1 hpn).trans hn2, hpp⟩, fun hpm => ?_⟩
    have := Nat.dvd_gcd hpn hpm
    rw [hcop.gcd_eq_one] at this
    exact hpp.not_dvd_one this
  rw [← sum_subtype_of_mem f hmem]
  calc ∑ x ∈ ((Ioc 0 N).filter (fun n => n.Coprime m)).subtype (· ∈ Nat.factoredNumbers s), f x
      ≤ ∑' x : Nat.factoredNumbers s, f x :=
        hhas.summable.sum_le_tsum _ (fun x _ => f_nonneg x)
    _ = ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, f (p ^ k) := hhas.tsum_eq
    _ = _ := by
        rw [hfilt]
        exact prod_congr rfl fun p hp => (hasSum_f_pow (hsP p hp)).tsum_eq

end CoprimeSieveAux

end DuffinSchaeffer
