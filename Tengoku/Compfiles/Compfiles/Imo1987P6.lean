/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jia-Jun Ma
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1987, Problem 6

Let $n$ be an integer greater than or equal to 2. Prove that
if $k^2 + k + n$ is prime for all integers $k$ such that
$0 <= k <= \sqrt{n/3}$, then $k^2 + k + n$ is prime for all
integers $k$ such that $0 <= k <= n - 2$.
-/

namespace Imo1987P6
open Nat

/--
@isnad1 id=le.2h1v.s5.11b4c94db344 from=translated src=- shape=e652210e vocab=5b8b4e48
-/
lemma minFac_le_sq {n : ℕ} (hnezero : n ≠ 0) (hn : minFac n ≠ n) : (minFac n)^2 ≤ n := by
  match n with
  | 0 => contradiction
  | 1 => simp
  | n+2 =>
    obtain ⟨r,hr⟩ := Nat.minFac_dvd (n+2)
    match r with
    | 0 => lia
    | 1 => nth_rw 2 [hr] at hn; simp at hn
    | r+2 =>
      have hh : (r+2) ∣ (n+2) := ⟨minFac (n+2), (by nth_rw 1 [hr,mul_comm])⟩
      have hr' : minFac (n+2) ≤ (r+2) := Nat.minFac_le_of_dvd (by lia) hh
      calc
      _ =  (minFac (n+2)) * minFac (n+2) := by ring_nf
      _ ≤ minFac (n+2) * (r+2) := Nat.mul_le_mul_left _ hr'
      _ = _ := hr.symm

/--
@isnad1 id=prime.2h1v.s5.4cd7b239f416 from=translated src=- shape=4421e074 vocab=02aeb0e8
-/
lemma prime_of_coprime' (n : ℕ) (h1 : 1 < n)
    (h2 : ∀ m:ℕ, m^2  ≤  n → m ≠ 0 → n.Coprime m) : Nat.Prime n := by
  rw [Nat.prime_def_minFac]
  by_contra H; push Not at H
  replace H := H (by lia)
  let m := minFac n
  have nneone : n ≠ 1 := by lia
  have mpos := Nat.minFac_pos n
  replace h2 := h2 (m) (minFac_le_sq (by lia) H) (by lia)
  apply Nat.Prime.not_coprime_iff_dvd.2 ?_ h2
  use (minFac n)
  simp [Nat.minFac_prime nneone,Nat.minFac_dvd,m]

/--
@isnad1 id=ex.2h2v.s6.b27d1bcf872e from=translated src=- shape=9654e6e4 vocab=2a3f5b88
-/
lemma dyadic {k b : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ b) : ∃ i, b < 2^i * k ∧ 2^i *k ≤ 2* b := by
  have hbk :  b/k ≠ 0 := by
    apply (Nat.div_ne_zero_iff (a:=b) (b:=k)).2
    lia
  use Nat.log2 (b/k) + 1
  constructor
  · have h2bk: (b/k).log2 < (b/k).log2 + 1 := Nat.lt_succ_self _
    replace h2bk := (Nat.log2_lt hbk).1 h2bk
    replace h2bk := succ_le_of_lt h2bk
    calc
    _ < b/k * k + k := lt_div_mul_add (by lia)
    _ = (b/k+1) *k := by ring
    _ ≤  2 ^((b/k).log2 +1) * k := Nat.mul_le_mul_right k h2bk
  · have h2 : 2 ^((b/k).log2 +1)  = 2 * 2^( (b/k).log2 ):=
      by rw [pow_succ _ _,mul_comm]
    rw [h2]
    have h3 : 2^((b/k).log2) ≤ b/k := Nat.log2_self_le hbk
    rw [mul_assoc]
    apply Nat.mul_le_mul_left 2
    exact (Nat.le_div_iff_mul_le h1).mp h3

/--
@isnad1 id=coprime.3h3v.s6.65bce8110a79 from=translated src=- shape=fccf507d vocab=a271807a
-/
lemma key_lemma {m b: ℕ}
    (h: ∀ k, b < k → k ≤ 2*b → Coprime m k) :
     ∀ k, 1 < k →  k ≤ 2 * b → Coprime m k := by
   intro k hk1 hk2
   by_cases hk0 : b < k
   · exact h k hk0 hk2
   · push Not at hk0
     obtain ⟨i, hi1, hi2⟩  :=  dyadic (le_of_lt hk1) hk0
     exact Coprime.coprime_mul_left_right (h (2 ^ i * k) hi1 hi2)

/--
@isnad1 id=prime.3h2v.s6.589cebc125dd from=translated src=- shape=edcb8846 vocab=aefad5a1
-/
lemma key_lemma'  {m b: ℕ } (h1 : 1 < m)
    (h: ∀ k,  b < k → k ≤ 2*b → Coprime m k) (h2 : m < (2*b+1)^2) :
     Nat.Prime m := by
  replace h := key_lemma h
  apply prime_of_coprime' m h1
  intro k hk1 hk2
  by_cases hk0 : k=1
  · simp [hk0]
  push Not at hk0
  refine h k ?_ ?_
  · lia
  · replace h2 := lt_of_le_of_lt hk1 h2
    rw [pow_two,pow_two] at h2
    replace h2 := Nat.mul_self_lt_mul_self_iff.1 h2
    lia

/--
@isnad1 id=eq.4h3v.s5.55183f62dd43 from=translated src=- shape=8e9dc091 vocab=3a19dee0
-/
lemma dvd_lemma (a b c : ℕ ) (h : c ≠ 0) : a ≤ b → b ∣ c → c < 2 * a → b = c := by
  intro h1 ⟨k, hk⟩ h3
  match k with
  | 0 => simp at hk; exfalso; exact h hk
  | 1 => simp [hk]
  | k + 2 => lia

/--
@isnad1 id=eq.2h2v.s5.aaf6aff106ba from=translated src=- shape=61659543 vocab=cf369417
-/
lemma zero_of_le_sub_pos {a b : ℕ} : b ≠ 0 → a ≤ a - b → a = 0 := by lia

/--
@isnad1 id=lt.2h2v.s5.dc3277d0d28f from=translated src=- shape=04fb3ac7 vocab=6e13db02
-/
lemma sub_le_lemma {a b : ℕ} : b ≤ a → b ≠ 0 → a - b < a := by lia

end Imo1987P6
