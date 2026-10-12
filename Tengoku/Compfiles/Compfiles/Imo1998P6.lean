/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1998, Problem 6

Determine the least possible value of `f(1998)`, where `f : ℕ+ → ℕ+` satisfies
`f(n^2 * f(m)) = m * f(n)^2` for all `m, n ∈ ℕ+`.
-/

namespace Imo1998P6

section AlgebraicLemmas

variable (f : ℕ+ → ℕ+) (hf : ∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2)
include hf

/--
@isnad1 id=eq.1h2v.s6.e3a91c12b53f from=translated src=- shape=cea04bfe vocab=a740cf7c
-/
lemma f_f_eq (n : ℕ+) : f (f n) = n * (f 1) ^ 2 := by
  have h := hf n 1
  simpa using h

/--
@isnad1 id=injectiv.1h1v.s6.0db063411f70 from=translated src=- shape=9d246e8f vocab=085d2a0e
-/
lemma f_injective : Function.Injective f := by
  intro a b hab
  have ha := f_f_eq f hf a
  have hb := f_f_eq f hf b
  rw [hab] at ha
  have : (a : ℕ) * ((f 1 : ℕ+) : ℕ) ^ 2 = (b : ℕ) * ((f 1 : ℕ+) : ℕ) ^ 2 := by
    exact_mod_cast ha.symm.trans hb
  rwa [Nat.mul_left_inj (by positivity), PNat.coe_inj] at this

/--
@isnad1 id=eq.1h2v.s7.bf3f65d46e4e from=translated src=- shape=8e13bc65 vocab=a740cf7c
-/
lemma f_sq_d (n : ℕ+) : f (n ^ 2 * f 1) = (f n) ^ 2 := by
  simpa using hf 1 n

/--
@isnad1 id=eq.1h3v.s6.b5bcd0b6486a from=translated src=- shape=4c32aec6 vocab=a740cf7c
-/
lemma f_prod_eq (a b : ℕ+) : f a * f b = f (f 1 * a * b) := by
  have h_eq : f a ^ 2 * f b ^ 2 = f ((a * b * f 1) ^ 2 * f 1) := by
    convert hf ( f ( a ^ 2 * f 1 ) ) b |> Eq.symm using 1
    · simp +decide [ hf ]
    · simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, f_f_eq ]
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
  rw [ ← PNat.coe_inj ] at * ; simp_all +decide [ ← mul_pow ]

/--
@isnad1 id=eq.1h2v.s6.ce5163614603 from=translated src=- shape=468c396e vocab=a740cf7c
-/
lemma f_d_mul (n : ℕ+) : f 1 * f n = f (f 1 * n) := by
  have h := f_prod_eq f hf 1 n
  simpa using h

/--
@isnad1 id=eq.1h3v.s6.f3e600697dc5 from=translated src=- shape=60e2c44e vocab=a740cf7c
-/
lemma f_mul_rel (a b : ℕ+) : f a * f b = f 1 * f (a * b) := by
  rw [f_prod_eq f hf a b, f_d_mul f hf (a * b), mul_assoc]

/--
@isnad1 id=dvd.1h2v.s6.7f29ba7d502c from=translated src=- shape=1d1e2f12 vocab=9ac8c41c
-/
lemma f1_dvd (n : ℕ+) : (f 1 : ℕ) ∣ (f n : ℕ) := by
  have h_pow : ∀ k : ℕ, k > 0 → f (n ^ k) * (f 1) ^ (k - 1) = f n ^ k := by
    intro k hk_positive
    induction hk_positive <;> simp_all +decide [pow_succ, mul_comm, mul_left_comm]
    rename_i k hk ih
    rw [ ← ih ]
    rw [ ← mul_assoc, mul_comm ]
    rw [ f_mul_rel ]
    · rw [ show f 1 ^ k = f 1 * f 1 ^ ( k - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel hk ] ]
      ring
    · exact fun m n => by simpa only [ sq, mul_assoc ] using hf m n
  by_contra h_not_div
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ (Nat.factorization (f 1)) p > (Nat.factorization (f n)) p := by
    contrapose! h_not_div
    exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k > 0 ∧ (k - 1) * Nat.factorization (f 1) p > k * Nat.factorization (f n) p := by
    exact ⟨ ( f 1 |> PNat.val |> Nat.factorization ) p + 1, Nat.succ_pos _, by norm_num; nlinarith ⟩
  replace h_pow := congr_arg ( fun x : ℕ+ => x.val.factorization p ) ( h_pow k hk.1 )
  simp_all +decide [ Nat.factorization_mul ]
  lia

end AlgebraicLemmas

section LowerBound

variable (f : ℕ+ → ℕ+) (hf : ∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2)
include hf

noncomputable def gf (n : ℕ+) : ℕ := (f n : ℕ) / (f 1 : ℕ)

/--
@isnad1 id=eq.1h2v.s6.d9e550eefc5e from=translated src=- shape=7e3afbb8 vocab=6068a9cd
-/
lemma gf_spec (n : ℕ+) : (f n : ℕ) = (f 1 : ℕ) * gf f n := by
  rw [gf, Nat.mul_div_cancel' (f1_dvd f hf n)]

/--
@isnad1 id=lt.1h2v.s6.c5cf48e5bab9 from=translated src=- shape=87d85299 vocab=a0c43252
-/
lemma gf_pos (n : ℕ+) : 0 < gf f n := by
  rw [gf]
  exact Nat.div_pos (Nat.le_of_dvd (by positivity) (f1_dvd f hf n)) (by positivity)

omit hf in
/--
@isnad1 id=eq.0h1v.s4.29de519f8715 from=translated src=- shape=ab70bd0f vocab=50cd4091
-/
lemma gf_one : gf f 1 = 1 := by
  rw [gf, Nat.div_self (by positivity)]

/--
@isnad1 id=eq.1h3v.s6.4d248e9d1963 from=translated src=- shape=7cd57726 vocab=d054dcd1
-/
lemma gf_mul (a b : ℕ+) : gf f (a * b) = gf f a * gf f b := by
  unfold gf
  rw [ Nat.div_mul_div_comm ]
  · rw [ ← PNat.mul_coe, f_mul_rel f hf a b ]
    norm_num [ Nat.mul_div_mul_left ]
  · exact f1_dvd f hf a
  · exact f1_dvd f hf b

/--
@isnad1 id=eq.1h2v.s6.32659dbf9c03 from=translated src=- shape=de3516f1 vocab=916fcf43
-/
lemma gf_invol (n : ℕ+) : gf f ⟨gf f n, gf_pos f hf n⟩ = n := by
  have h_fg : f ⟨gf f n, gf_pos f hf n⟩ = n * f 1 := by
    have h_fg : f (f 1 * ⟨gf f n, gf_pos f hf n⟩) = n * f 1 * f 1 := by
      convert hf n 1 using 1
      · simp +decide [mul_comm]
        congr! 1
        exact PNat.eq (gf_spec f hf n).symm
      · ring
    have := f_d_mul f hf ⟨gf f n, gf_pos f hf n⟩
    ( rw [ ← PNat.coe_inj ] at *; simp_all +decide [mul_comm, mul_left_comm] )
    nlinarith [ PNat.pos ( f 1 ) ]
  exact Nat.div_eq_of_eq_mul_left ( PNat.pos _ ) ( by erw [ h_fg ] ; norm_cast )

/--
@isnad1 id=prime.2h2v.s6.57fe99814095 from=translated src=- shape=c69477ee vocab=89da346d
-/
lemma gf_prime (p : ℕ+) (hp : Nat.Prime (p : ℕ)) : Nat.Prime (gf f p) := by
  refine Nat.prime_def_lt'.mpr ?_
  refine' ⟨ _, fun m hm₁ hm₂ h => _ ⟩
  · by_contra h_contra
    interval_cases _ : gf f p <;> have := gf_invol f hf p <;> simp_all +decide
    · exact absurd ‹gf f p = 0› ( ne_of_gt ( gf_pos f hf p ) )
    · exact absurd this ( by erw [ gf_one f ] ; exact ne_of_lt hp.one_lt )
  · have h_gmn : gf f ⟨m, by linarith⟩ * gf f ⟨gf f p / m, by
      exact Nat.div_pos ( Nat.le_of_dvd ( pos_of_gt hm₂ ) h ) ( pos_of_gt hm₁ )⟩ = p := by
      all_goals generalize_proofs at *
      convert gf_invol f hf p using 1
      convert gf_mul f hf ⟨ m, by linarith ⟩ ⟨ gf f p / m, by linarith ⟩ |> Eq.symm using 1
      exact congr_arg _ ( PNat.eq ( Eq.symm ( Nat.mul_div_cancel' h ) ) )
    generalize_proofs at *
    have h_g_one : gf f ⟨m, by linarith⟩ = 1 ∨ gf f ⟨gf f p / m, by positivity⟩ = 1 := by
      have := hp.isUnit_or_isUnit h_gmn.symm
      aesop
    generalize_proofs at *
    cases h_g_one <;> have := gf_invol f hf ⟨ m, by linarith ⟩ <;> simp_all +decide
    · linarith [ show gf f 1 = 1 from gf_one f ]
    · linarith!

/--
@isnad1 id=eq.1h1v.s7.42f8f043821b from=translated src=- shape=d80f0509 vocab=6068a9cd
-/
lemma f_1998_eq : (f 1998 : ℕ) = (f 1 : ℕ) * gf f 2 * gf f 3 ^ 3 * gf f 37 := by
  rw [gf_spec f hf 1998]
  have h1998 : (1998 : ℕ+) = 2 * 3 * 3 * 3 * 37 := by rfl
  rw [h1998]
  simp [gf_mul f hf]
  ring

/--
@isnad1 id=le.1h1v.s6.81a486f955b1 from=translated src=- shape=acdd7c70 vocab=81f2c353
-/
theorem f_1998_ge : (120 : ℕ) ≤ (f 1998 : ℕ) := by
  have h_min : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p ≠ q ∧ q ≠ r ∧ p ≠ r → p * q^3 * r ≥ 120 := by
    intros p q r hp hq hr h_distinct
    by_cases hq2 : q = 2
    · rcases p with ( _ | _ | _ | _ | _ | p ) <;> rcases r with ( _ | _ | _ | _ | _ | r ) <;> simp_all +arith +decide
      grind
    · by_cases hq3 : q = 3
      · rcases p with ( _ | _ | _ | _ | p ) <;> rcases r with ( _ | _ | _ | _ | r ) <;> simp_all +arith +decide
        nlinarith
      · have hq_ge_5 : 5 ≤ q := le_of_not_gt fun h => by interval_cases q <;> trivial
        have hq3_ge_125 : 125 ≤ q^3 := Nat.pow_le_pow_left hq_ge_5 3
        nlinarith [ hp.two_le, hr.two_le, mul_pos hp.pos hr.pos ]
  have h_final : (gf f 2 : ℕ) * (gf f 3 : ℕ) ^ 3 * (gf f 37 : ℕ) ≥ 120 := by
    apply h_min
    · exact gf_prime f hf 2 (by decide)
    · exact gf_prime f hf 3 (by decide)
    · exact gf_prime f hf 37 (by decide)
    · refine' ⟨ _, _, _ ⟩ <;> intro h <;> have := gf_invol f hf 2 <;> have := gf_invol f hf 3 <;> have := gf_invol f hf 37 <;> simp_all +decide
  exact le_trans h_final ( by nlinarith [ f_1998_eq f hf, PNat.pos ( f 1 ) ] )

end LowerBound

section Construction

def primeSwap : ℕ → ℕ
  | 2 => 3 | 3 => 2 | 5 => 37 | 37 => 5 | n => n

def g (n : ℕ) : ℕ := (n.primeFactorsList.map primeSwap).prod

/--
@isnad1 id=eq.0h1v.s3.054db7fdf1a5 from=translated src=- shape=47dcad53 vocab=b5dfaf78
-/
lemma primeSwap_invol (n : ℕ) : primeSwap (primeSwap n) = n := by
  by_cases h2 : n = 2 <;> by_cases h3 : n = 3 <;> by_cases h5 : n = 5 <;> by_cases h37 : n = 37
  all_goals (try subst_vars; try rfl)
  all_goals simp only [primeSwap, *]

/--
@isnad1 id=prime.1h1v.s3.f296245d18df from=translated src=- shape=2c86d966 vocab=74ae7a24
-/
lemma primeSwap_prime {p : ℕ} (hp : Nat.Prime p) : Nat.Prime (primeSwap p) := by
  by_cases! h2 : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 37
  · rcases h2 with h | h | h | h <;> (subst h; decide)
  · simp [primeSwap, h2, hp]

/--
@isnad1 id=eq.2h2v.s5.5c856c83a043 from=translated src=- shape=eff8b0f5 vocab=4011fb8b
-/
lemma g_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : g (a * b) = g a * g b := by
  simp only [g]
  have h := (Nat.perm_primeFactorsList_mul ha hb).map primeSwap
  rw [List.map_append] at h
  rw [h.prod_eq, List.prod_append]

/--
@isnad1 id=eq.1h1v.s3.cce7abd933a9 from=translated src=- shape=981d6891 vocab=340fb842
-/
lemma g_prime {p : ℕ} (hp : Nat.Prime p) : g p = primeSwap p := by
  simp [g, Nat.primeFactorsList_prime hp]

/--
@isnad1 id=ne.0h1v.s3.17528f818031 from=translated src=- shape=b14ee516 vocab=60b1e567
-/
lemma g_ne_zero (n : ℕ) : g n ≠ 0 := by
  simp only [g]
  apply List.prod_ne_zero; rw [List.mem_map]; push Not
  intro p hp; exact (primeSwap_prime (Nat.prime_of_mem_primeFactorsList hp)).ne_zero

/--
@isnad1 id=lt.0h1v.s3.29278b2d62f2 from=translated src=- shape=8a62b088 vocab=a5928ad6
-/
lemma g_pos (n : ℕ) : 0 < g n := Nat.pos_of_ne_zero (g_ne_zero n)

/--
@isnad1 id=eq.1h1v.s4.ee9f870f1cc0 from=translated src=- shape=18e0457f vocab=60b1e567
-/
lemma g_invol {n : ℕ} (hn : n ≠ 0) : g (g n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      simp [g]
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm : m ≠ 0 := right_ne_zero_of_mul hn
    rw [g_mul hp.ne_zero hm,
        g_mul (g_ne_zero p) (g_ne_zero m),
        g_prime hp, g_prime (primeSwap_prime hp), primeSwap_invol]
    congr 1
    exact ih m (by nlinarith [hp.one_lt, Nat.pos_of_ne_zero hm]) hm

/--
@isnad1 id=eq.2h2v.s6.ef47b133bf10 from=translated src=- shape=a0ad9269 vocab=fb4cea19
-/
lemma g_func_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : g (n ^ 2 * g m) = m * g n ^ 2 := by
  rw [g_mul (pow_ne_zero 2 hn) (g_ne_zero m), sq, g_mul hn hn, sq, g_invol hm, mul_comm]

/--
@isnad1 id=eq.0h0v.s3.c2c9e0f2700f from=translated src=- shape=3c26ae4f vocab=60b1e567
-/
lemma g_1998 : g 1998 = 120 := by decide +kernel

def gPNat (n : ℕ+) : ℕ+ := ⟨g n.val, g_pos n.val⟩

/--
@isnad1 id=eq.0h2v.s6.f52a2395c28a from=translated src=- shape=f62d426d vocab=7ad7a1cf
-/
lemma gPNat_func_eq (m n : ℕ+) : gPNat (n ^ 2 * gPNat m) = m * gPNat n ^ 2 := by
  apply PNat.eq
  show g ((n ^ 2 * gPNat m).val) = (m * gPNat n ^ 2).val
  rw [PNat.mul_coe, PNat.pow_coe, PNat.mul_coe, PNat.pow_coe]
  show g (n.val ^ 2 * (gPNat m).val) = m.val * (gPNat n).val ^ 2
  simp only [gPNat]
  exact g_func_eq m.ne_zero n.ne_zero

/--
@isnad1 id=eq.0h0v.s3.17c103393941 from=translated src=- shape=3c26ae4f vocab=d8ab6555
-/
lemma gPNat_1998 : gPNat 1998 = 120 := by
  apply PNat.eq
  simp [gPNat, g_1998]

end Construction

/--
@isnad1 id=mem.0h0v.s6.2229d5ae3c70 from=translated src=- shape=e46b9566 vocab=dd70e792
-/
theorem imo1998_p6_mem :
    (120 : ℕ+) ∈ {k : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2) ∧ f 1998 = k} :=
  ⟨gPNat, gPNat_func_eq, gPNat_1998⟩

/--
@isnad1 id=le.1h1v.s6.c58aa060617b from=translated src=- shape=5132e737 vocab=f9dd5079
-/
theorem imo1998_p6_lb :
    ∀ k ∈ {k : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2) ∧ f 1998 = k}, (120 : ℕ+) ≤ k := by
  intro k ⟨f, hf_eq, hf_1998⟩
  rw [← hf_1998]
  show (120 : ℕ) ≤ (f 1998 : ℕ)
  exact f_1998_ge f hf_eq

abbrev answer : ℕ+ := 120

end Imo1998P6
