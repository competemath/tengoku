/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2017 N1 (P1)

For each $n ∈ ℕ$, define $f(n)$ by $\sqrt{n}$ if $n$ is a square and $n + 3$ otherwise.
Find all $N ∈ ℕ$ such that $\{n : f^n(N) = a\}$ is infinite for some $a ∈ ℕ$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2017N1

/-! ### Extra lemmas -/

/--
@isnad1 id=ex.2h3v.s5.8cc25a153438 from=translated src=- shape=0bb6b6d6 vocab=2e257d4c
-/
theorem exists_eq_add_mul_of_le_of_mod_eq (h : m ≤ n) (h0 : m % p = n % p) :
    ∃ r : ℕ, n = m + p * r := by
  obtain ⟨q, rfl⟩ : ∃ q, n = m + q := Nat.exists_eq_add_of_le h
  replace h0 : (m + q - m) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h0.symm
  rw [← Nat.dvd_iff_mod_eq_zero, Nat.add_sub_cancel_left] at h0
  rcases h0 with ⟨r, rfl⟩; exact ⟨r, rfl⟩

/--
@isnad1 id=ex.2h2v.s6.a8016a413a32 from=translated src=- shape=da82fe4a vocab=86d7078a
-/
theorem exists_restricted_sq_mod_eq (h : 0 < p) (h0 : ∃ x, x ^ 2 % p = k % p) :
    ∃ j > 0, j ≤ p ∧ (k.sqrt + j) ^ 2 % p = k % p := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  clear h; rcases h0 with ⟨x, h⟩
  let y : ℕ := (x + p * (k.sqrt + 1)) % (p + 1) + 1
  refine ⟨y, Nat.succ_pos _, Nat.succ_le_of_lt (Nat.mod_lt _ p.succ_pos), ?_⟩
  rw [Nat.add_left_comm, Nat.pow_mod, Nat.mod_add_mod, Nat.add_assoc,
    ← Nat.succ_mul, Nat.add_mul_mod_self_left, ← Nat.pow_mod, h]

/--
@isnad1 id=ex.2h2v.s6.cb5138f0fa83 from=translated src=- shape=497e0267 vocab=a1802dbf
-/
theorem exists_add_mul_eq_sqrt_add_sq_of_sq_mod (hp : 0 < p) (hk : ∃ x, x ^ 2 % p = k % p) :
    ∃ j > 0, j ≤ p ∧ ∃ m, (k.sqrt + j) ^ 2 = k + p * m := by
  rcases exists_restricted_sq_mod_eq hp hk with ⟨j, hj, hj0, h⟩
  refine ⟨j, hj, hj0, exists_eq_add_mul_of_le_of_mod_eq (Nat.le_of_lt ?_) h.symm⟩
  rwa [← Nat.sqrt_lt', Nat.lt_add_right_iff_pos]

/--
@isnad1 id=lt.2h2v.s5.623e9d6ed272 from=translated src=- shape=97f882f5 vocab=bc204005
-/
theorem sqrt_add_lt_of_two_mul_lt (h : 0 < p) (h0 : 2 * p < k) : k.sqrt + p < k := by
  revert h0; revert k; apply Nat.le_induction
  ---- Base case: `k = 2p + 1`
  · rw [Nat.two_mul, ← Nat.succ_add, Nat.add_lt_add_iff_right, Nat.sqrt_lt, Nat.mul_succ,
      Nat.add_comm, Nat.add_lt_add_iff_right, Nat.succ_mul, Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos h h
  ---- Induction step
  · rintro k - hk0; refine Nat.lt_of_le_of_lt ?_ (Nat.succ_lt_succ hk0)
    rw [← Nat.succ_add, Nat.add_le_add_iff_right]
    exact k.sqrt_succ_le_succ_sqrt

/--
@isnad1 id=ex.3h2v.s6.1b688db1ea81 from=translated src=- shape=aa86aa29 vocab=daab4b83
-/
theorem exists_add_mul_eq_small_sq_of_sq_mod
    (hp : 0 < p) (hk : 2 * p < k) (hk0 : ∃ x, x ^ 2 % p = k % p) :
    ∃ x < k, ∃ m, x ^ 2 = k + p * m := by
  obtain ⟨j, -, hj, h⟩ := exists_add_mul_eq_sqrt_add_sq_of_sq_mod hp hk0
  refine ⟨k.sqrt + j, ?_, h⟩
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hj _) (sqrt_add_lt_of_two_mul_lt hp hk)

/--
@isnad1 id=eq.1h3v.s6.3fce259753fd from=translated src=- shape=462ba73b vocab=059f5c5c
-/
theorem sq_mod_eq_of_dvd_add {p a b : ℕ} (h : p ∣ a + b) : a ^ 2 % p = b ^ 2 % p := by
  rcases h with ⟨n, h⟩
  obtain h0 | h0 : a ^ 2 ≤ b ^ 2 ∨ b ^ 2 ≤ a ^ 2 := le_total (a ^ 2) (b ^ 2)
  · obtain ⟨m, h1⟩ : p ∣ b ^ 2 - a ^ 2 := by
      rw [Nat.sq_sub_sq, Nat.add_comm, h, p.mul_assoc]
      exact Nat.dvd_mul_right p _
    rw [← Nat.add_sub_cancel' h0, h1, Nat.add_mul_mod_self_left]
  · obtain ⟨m, h1⟩ : p ∣ a ^ 2 - b ^ 2 := by
      rw [Nat.sq_sub_sq, h, p.mul_assoc]
      exact Nat.dvd_mul_right p _
    rw [← Nat.add_sub_cancel' h0, h1, Nat.add_mul_mod_self_left]

/--
@isnad1 id=lt.2h2v.s5.302c9ca25a1b from=translated src=- shape=5e74b5bf vocab=c28ef0a7
-/
theorem lt_sub_self_of_sq_lt (hp : 2 < p) (h : x ^ 2 < p) : x < p - x := by
  refine Nat.lt_sub_of_add_lt (x.two_mul ▸ Nat.lt_of_not_le λ h0 ↦ Nat.not_le_of_lt h ?_)
  replace h : 2 ≤ x := Nat.lt_of_mul_lt_mul_left (a := 2) (Nat.lt_of_lt_of_le hp h0)
  rw [Nat.pow_two]; exact Nat.le_trans h0 (Nat.mul_le_mul_right x h)

/--
@isnad1 id=ex.3h2v.s6.baadcebc71e5 from=translated src=- shape=c0f3f458 vocab=33eeb603
-/
theorem exists_add_mul_eq_sq_of_small_sq_mod
    (hp : 2 < p) (hk : k ≤ 2 * p) (h : ∃ x, x ^ 2 % p = k % p) :
    ∃ x ≤ p, ∃ m, x ^ 2 = k + p * m := by
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  obtain ⟨x, hx, hx0⟩ : ∃ x < p, x ^ 2 % p = k % p := by
    rcases h with ⟨x, hx⟩
    exact ⟨x % p, Nat.mod_lt x hp0, (Nat.pow_mod _ _ _).symm.trans hx⟩
  clear h; obtain h | ⟨m, rfl⟩ : k < p ∨ ∃ m, k = p + m :=
    (lt_or_ge k p).imp_right Nat.exists_eq_add_of_le
  ---- First resolve the case `k < p`
  · refine ⟨x, Nat.le_of_lt hx, exists_eq_add_mul_of_le_of_mod_eq ?_ hx0.symm⟩
    rw [← Nat.mod_eq_of_lt h, ← hx0]; exact Nat.mod_le _ _
  ---- Now assume `p ≤ k`, rewrite `k` as `p + m`, and resolve the case `m = p`
  rw [Nat.two_mul, Nat.add_le_add_iff_left, Nat.le_iff_lt_or_eq, or_comm] at hk
  rcases hk with rfl | hm
  · refine ⟨m, m.le_refl, m - 2, ?_⟩
    rw [Nat.add_comm, ← Nat.mul_two, ← m.mul_add,
      Nat.sub_add_cancel (Nat.le_of_lt hp), Nat.pow_two]
  ---- Finally, resolve the case `k = p + m` with `m < p`
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm] at hx0
  clear hm; subst hx0
  obtain ⟨d, h⟩ : ∃ d, x ^ 2 = x ^ 2 % p + p * d := ⟨x ^ 2 / p, (Nat.mod_add_div _ _).symm⟩
  obtain ⟨d, rfl⟩ | rfl : (∃ d', d = d' + 1) ∨ d = 0 :=
    (ne_or_eq d 0).imp_left Nat.exists_eq_succ_of_ne_zero
  · refine ⟨x, Nat.le_of_lt hx, d, ?_⟩
    rw [p.add_comm, Nat.add_assoc, p.add_comm, ← p.mul_succ, ← h]
  · refine ⟨p - x, p.sub_le x, ?_⟩
    rw [p.mul_zero, Nat.add_zero, eq_comm, Nat.mod_eq_iff_lt (Nat.ne_of_gt hp0)] at h
    replace hx : (p - x) ^ 2 % p = x ^ 2 % p :=
      sq_mod_eq_of_dvd_add ⟨1, by rw [p.mul_one, Nat.sub_add_cancel (Nat.le_of_lt hx)]⟩
    obtain ⟨d, h0⟩ : ∃ d, (p - x) ^ 2 = (p - x) ^ 2 % p + p * d :=
      ⟨(p - x) ^ 2 / p, (Nat.mod_add_div _ _).symm⟩
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero λ hd ↦ ?_
      subst d; rw [hx, Nat.mod_eq_of_lt h, p.mul_zero, Nat.add_zero] at h0
      have h1 := Nat.pow_lt_pow_left (lt_sub_self_of_sq_lt hp h) (Nat.succ_ne_zero 1)
      exact Nat.ne_of_gt h1 h0
    refine ⟨d, ?_⟩; rw [h0, hx, p.mul_succ, p.add_comm, Nat.add_assoc, p.add_comm]

/-! ### General theory of the function `f` -/

def f (p k : ℕ) : ℕ := if k.sqrt ^ 2 = k then k.sqrt else k + p

/--
@isnad1 id=eq.0h2v.s4.f80a7571d10c from=translated src=- shape=26c6251a vocab=e3afc725
-/
theorem f_sq (p x) : f p (x ^ 2) = x := by
  rw [f, Nat.sqrt_eq', ite_eq_left rfl]

/--
@isnad1 id=eq.0h2v.s4.3a1e061c5aef from=translated src=- shape=d6c2590e vocab=e1423eca
-/
theorem f_iterate_zero (p) : ∀ m, (f p)^[m] 0 = 0 :=
  Nat.rec rfl λ k hk ↦ by rw [(f p).iterate_succ_apply', hk]; rfl

/--
@isnad1 id=iff.0h2v.s4.e73708c22636 from=translated src=- shape=57d47f00 vocab=5d5cf605
-/
theorem f_eq_zero_iff {p k} : f p k = 0 ↔ k = 0 := by
  refine ⟨λ hk ↦ ?_, λ hk ↦ hk.symm ▸ rfl⟩
  unfold f at hk; split_ifs at hk with h
  · rwa [hk, Nat.pow_two, Nat.zero_mul, eq_comm] at h
  · exact Nat.eq_zero_of_add_eq_zero_right hk

/--
@isnad1 id=iff.0h3v.s4.ce754ade3f65 from=translated src=- shape=0f1c7a32 vocab=e1423eca
-/
theorem f_iterate_eq_zero_iff : (f p)^[m] k = 0 ↔ k = 0 := by
  refine Nat.rec Iff.rfl (λ n hn ↦ ?_) m
  rw [(f p).iterate_succ_apply', f_eq_zero_iff, hn]

/--
@isnad1 id=eq.0h2v.s4.0461e035938b from=translated src=- shape=d6c2590e vocab=e1423eca
-/
theorem f_iterate_one (p) : ∀ m, (f p)^[m] 1 = 1 :=
  Nat.rec rfl λ k hk ↦ by rw [(f p).iterate_succ_apply', hk]; rfl

/--
@isnad1 id=iff.0h2v.s4.7e7157db35d7 from=translated src=- shape=57d47f00 vocab=5d5cf605
-/
theorem f_eq_one_iff {p k} : f p k = 1 ↔ k = 1 := by
  refine ⟨λ hk ↦ ?_, λ hk ↦ hk.symm ▸ rfl⟩
  unfold f at hk; split_ifs at hk with h
  · rwa [hk, Nat.one_pow, eq_comm] at h
  · rw [Nat.add_eq_one_iff] at hk
    rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [absurd rfl h, rfl]

/--
@isnad1 id=iff.0h3v.s4.3668c5efdcc6 from=translated src=- shape=0f1c7a32 vocab=e1423eca
-/
theorem f_iterate_eq_one_iff : (f p)^[m] k = 1 ↔ k = 1 := by
  refine Nat.rec Iff.rfl (λ n hn ↦ ?_) m
  rw [(f p).iterate_succ_apply', f_eq_one_iff, hn]

/--
@isnad1 id=eq.1h3v.s6.1bcab4276e01 from=translated src=- shape=ce378bc3 vocab=5b2051c0
-/
theorem f_iterate_of_not_sq_mod (h : ∀ x, x ^ 2 % p ≠ k % p) :
    ∀ m, (f p)^[m] k = k + p * m := by
  refine Nat.rec rfl λ m hm ↦ ?_
  rw [(f p).iterate_succ_apply', hm, Nat.mul_succ, ← Nat.add_assoc]
  refine ite_eq_right λ h0 ↦ h (k + p * m).sqrt ?_
  rw [h0, Nat.add_mul_mod_self_left]

/--
@isnad1 id=or.0h3v.s6.b0951309c04a from=translated src=- shape=cc66f0aa vocab=471edf1f
-/
theorem f_iterate_eq_or_exists_le_sqrt (p k) :
    ∀ m, (∃ n ≤ m, (f p)^[n] k ≤ (k + p * m).sqrt) ∨ (f p)^[m] k = k + p * m := by
  ---- Induction on `m`; base case `m = 0` immediate
  refine Nat.rec (Or.inr rfl) λ m hm ↦ ?_
  have X : (k + p * m).sqrt ≤ (k + p * m.succ).sqrt := by
    rw [Nat.mul_succ, ← k.add_assoc]; exact Nat.sqrt_le_sqrt (Nat.le_add_right _ _)
  ---- If `f_p^n(k) ≤ √(k + pm)` for some `n ≤ m`, we are done
  rcases hm with ⟨n, hn, hn0⟩ | hm
  · left; exact ⟨n, Nat.le_succ_of_le hn, Nat.le_trans hn0 X⟩
  ---- Now resolve the case `f_p^m(k) = k + pm`
  refine (dec_em ((k + p * m).sqrt ^ 2 = k + p * m)).imp (λ h ↦ ?_) (λ h ↦ ?_)
  · refine ⟨m.succ, m.succ.le_refl, ?_⟩
    rwa [(f p).iterate_succ_apply', hm, f, ite_eq_left h]
  · rw [(f p).iterate_succ_apply', hm, f, ite_eq_right h, p.mul_succ, k.add_assoc]

/--
@isnad1 id=ex.3h2v.s6.7ebfe090a41e from=translated src=- shape=78179945 vocab=76867d75
-/
theorem exists_f_iterate_lt_self_of_big
    (hp : 0 < p) (hk : 2 * p < k) (h : ∃ x, x ^ 2 % p = k % p) :
    ∃ n, (f p)^[n] k < k := by
  obtain ⟨x, hx, m, h0⟩ := exists_add_mul_eq_small_sq_of_sq_mod hp hk h
  obtain ⟨n, -, h1⟩ | h1 := f_iterate_eq_or_exists_le_sqrt p k m
  ---- Case 1: `f_p^n(k) ≤ x` for some `n ≤ m`
  · rw [← h0, Nat.sqrt_eq'] at h1
    exact ⟨n, Nat.lt_of_le_of_lt h1 hx⟩
  ---- Case 2: `f_p^m(k) = k + pm`
  · refine ⟨m.succ, ?_⟩
    rwa [(f p).iterate_succ_apply', h1, ← h0, f_sq]

/--
@isnad1 id=ex.3h2v.s6.3860b475c6bf from=translated src=- shape=70318b1d vocab=988c15b7
-/
theorem exists_f_iterate_le_p_of_small
    (hp : 2 < p) (hk : k ≤ 2 * p) (h : ∃ x, x ^ 2 % p = k % p) :
    ∃ n, (f p)^[n] k ≤ p := by
  obtain ⟨x, hx, m, h0⟩ := exists_add_mul_eq_sq_of_small_sq_mod hp hk h
  obtain ⟨n, -, h1⟩ | h1 := f_iterate_eq_or_exists_le_sqrt p k m
  ---- Case 1: `f_p^n(k) ≤ x` for some `n ≤ m`
  · rw [← h0, Nat.sqrt_eq'] at h1
    exact ⟨n, Nat.le_trans h1 hx⟩
  ---- Case 2: `f_p^m(k) = k + pm`
  · refine ⟨m.succ, ?_⟩
    rwa [(f p).iterate_succ_apply', h1, ← h0, f_sq]

/--
@isnad1 id=dvd.1h2v.s4.dcb2d8116867 from=translated src=- shape=beee0e23 vocab=fce120a8
-/
theorem dvd_of_dvd_f (h : p ∣ f p N) : p ∣ N := by
  unfold f at h; split_ifs at h with h0
  · rcases h with ⟨m, h⟩
    rw [← h0, Nat.pow_two, h, p.mul_assoc]
    exact Nat.dvd_mul_right p _
  · exact Nat.dvd_add_self_right.mp h

/--
@isnad1 id=dvd.1h3v.s4.d17aa60299fb from=translated src=- shape=b0b31737 vocab=f02e87f3
-/
theorem dvd_of_dvd_f_iterate (h : p ∣ (f p)^[k] N) : p ∣ N := by
  revert h; refine Nat.rec id (λ k hk h ↦ hk ?_) k
  rw [(f p).iterate_succ_apply'] at h; exact dvd_of_dvd_f h

/-! ##### `f_p` for `p = 0` and `p = 1` -/

/--
@isnad1 id=eq.0h1v.s5.7eec8c1767dc from=translated src=- shape=6511e91e vocab=84dc9112
-/
theorem f_zero_left (k) : f 0 k = if k.sqrt ^ 2 = k then k.sqrt else k := rfl

/--
@isnad1 id=le.0h1v.s3.7fb80338597f from=translated src=- shape=a60e91e3 vocab=3f9890fe
-/
theorem f_zero_left_le_self (k) : f 0 k ≤ k := by
  rw [f_zero_left]; split_ifs with h
  exacts [Nat.sqrt_le_self k, k.le_refl]

/--
@isnad1 id=ex.0h1v.s4.2376caccfce1 from=translated src=- shape=7bd422d6 vocab=7fb56f4a
-/
theorem exists_f_one_iterate_le_two (k) : ∃ n, (f 1)^[n] k ≤ 2 := by
  ---- Strong induction on `k`, clearing the base case `k ≤ 2` immediately
  induction k using Nat.strongRecOn with | ind k k_ih => ?_
  obtain h | h : k ≤ 2 ∨ 2 < k := le_or_gt k 2
  · exact ⟨0, h⟩
  ---- For `k > 2`, first find `m` such that `f^m(k) < k`
  obtain ⟨m, hm⟩ : ∃ m, (f 1)^[m] k < k := by
    refine exists_f_iterate_lt_self_of_big Nat.one_pos h ⟨0, ?_⟩
    rw [Nat.mod_one, Nat.mod_one]
  ---- Now apply IH on `f^m(k)` to find some `m'` and use `m + m'`
  obtain ⟨m', h0⟩ : ∃ m', (f 1)^[m'] ((f 1)^[m] k) ≤ 2 := k_ih _ hm
  refine ⟨m' + m, ?_⟩; rwa [(f 1).iterate_add_apply]

/-! ### Good numbers -/

def good (p N : ℕ) := ∃ a, ∀ m, ∃ n ≥ m, (f p)^[n] N = a

/--
@isnad1 id=good.0h1v.s3.b2b6eb2803b6 from=translated src=- shape=3d52821e vocab=6d09ebfb
-/
lemma good_zero_right (p) : good p 0 := ⟨0, λ m ↦ ⟨m, m.le_refl, f_iterate_zero p m⟩⟩

/--
@isnad1 id=good.0h1v.s3.3de26f038e89 from=translated src=- shape=3d52821e vocab=6d09ebfb
-/
lemma good_one_right (p) : good p 1 := ⟨1, λ m ↦ ⟨m, m.le_refl, f_iterate_one p m⟩⟩

/--
@isnad1 id=iff.0h2v.s3.b67110c3697c from=translated src=- shape=43dd6e5e vocab=f372e5fb
-/
lemma good_f_iff : good p (f p N) ↔ good p N := by
  refine exists_congr λ a ↦ ⟨?_, ?_⟩
  · intro h m; obtain ⟨n, hn, h0⟩ := h m
    exact ⟨n.succ, Nat.le_succ_of_le hn, h0⟩
  · intro h m; obtain ⟨n, hn, h0⟩ := h m.succ
    match n with
    | 0 => exact absurd hn m.not_succ_le_zero
    | n + 1 => exact ⟨n, Nat.le_of_succ_le_succ hn, h0⟩

/--
@isnad1 id=iff.0h3v.s4.0478dbd7bf37 from=translated src=- shape=d178c6b4 vocab=20f34ad3
-/
lemma good_f_iterate_iff : good p ((f p)^[k] N) ↔ good p N := by
  induction k with | zero => exact Iff.rfl | succ k h => ?_
  rw [(f p).iterate_succ_apply', good_f_iff, h]

/--
@isnad1 id=not.2h2v.s5.c57936b95fd8 from=translated src=- shape=d743843a vocab=0e51f84b
-/
theorem not_good_of_not_sq_mod (hp : 0 < p) (h : ∀ x, x ^ 2 % p ≠ k % p) : ¬good p k := by
  rintro ⟨a, ha⟩
  have h0 := f_iterate_of_not_sq_mod h
  obtain ⟨n, -, rfl⟩ := ha 0
  obtain ⟨n', hn', h1⟩ := ha (n + 1)
  rw [h0, h0, Nat.add_left_cancel_iff, Nat.mul_right_inj (Nat.ne_of_gt hp)] at h1
  subst n'; exact Nat.not_lt_of_le hn' n.lt_succ_self

/-- A version of `not_good_of_not_sq_mod` that allows testing non-good numbers by `decide`
@isnad1 id=not.2h2v.s5.428bf755b05e from=translated src=- shape=bf406ad6 vocab=ee670cc2
-/
theorem not_good_of_not_sq_mod_fin (hp : 0 < p) (h : ∀ x : Fin p, x ^ 2 % p ≠ k % p) :
    ¬good p k := by
  have : NeZero p := ⟨Nat.ne_zero_of_lt hp⟩
  refine not_good_of_not_sq_mod hp λ x hx ↦ h (Fin.ofNat p x) ?_
  rw [Fin.val_ofNat, ← Nat.pow_mod, hx]

/--
@isnad1 id=ex.2h2v.s5.2ae8d1fd15f6 from=translated src=- shape=63637a13 vocab=0e51f84b
-/
theorem good.exists_mod_eq_sq (hp : 0 < p) (h : good p k) : ∃ x, x ^ 2 % p = k % p := by
  by_contra h0; exact not_good_of_not_sq_mod hp (not_exists.mp h0) h

/--
@isnad1 id=ex.2h2v.s5.85660b30317e from=translated src=- shape=6468a4a9 vocab=1a40a1c0
-/
theorem good.exists_iterate_le_two_mul (hp : 0 < p) (h : good p N) :
    ∃ k, (f p)^[k] N ≤ 2 * p := by
  ---- Strong induction on `N`, with base case `N ≤ 2p`
  induction N using Nat.strongRecOn with | ind N N_ih => ?_
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hN0 : ∃ x, x ^ 2 % p = N % p := h.exists_mod_eq_sq hp0
  obtain hN | hN : N ≤ 2 * p ∨ 2 * p < N := le_or_gt N (2 * p)
  · exact ⟨0, hN⟩
  ---- Now focus on the induction step
  obtain ⟨m, h0⟩ := exists_f_iterate_lt_self_of_big hp0 hN hN0
  obtain ⟨k, h1⟩ := N_ih _ h0 (good_f_iterate_iff.mpr h)
  refine ⟨k + m, ?_⟩; rwa [(f p).iterate_add_apply]

/--
@isnad1 id=ex.2h2v.s5.2165eae2a015 from=translated src=- shape=de2263ec vocab=3329f2e4
-/
theorem good.exists_iterate_le_p (hp : 2 < p) (h : good p N) :
    ∃ k, (f p)^[k] N ≤ p := by
  ---- Strong induction on `N`, with base case `N ≤ 2p`
  induction N using Nat.strongRecOn with | ind N N_ih => ?_
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  have hN0 : ∃ x, x ^ 2 % p = N % p := h.exists_mod_eq_sq hp0
  obtain hN | hN : N ≤ 2 * p ∨ 2 * p < N := le_or_gt N (2 * p)
  · exact exists_f_iterate_le_p_of_small hp hN hN0
  ---- Now focus on the induction step
  obtain ⟨m, h0⟩ := exists_f_iterate_lt_self_of_big hp0 hN hN0
  obtain ⟨k, h1⟩ := N_ih _ h0 (good_f_iterate_iff.mpr h)
  refine ⟨k + m, ?_⟩; rwa [(f p).iterate_add_apply]

/-! ##### Every number is good for `p = 0` and `p = 1` -/

/--
@isnad1 id=good.0h1v.s3.b9b7fffbbade from=translated src=- shape=56f853c1 vocab=6d09ebfb
-/
theorem good_zero_left (k) : good 0 k := by
  induction k using Nat.strongRecOn with | ind k k_ih => ?_
  obtain h | h : f 0 k < k ∨ f 0 k = k := Nat.lt_or_eq_of_le (f_zero_left_le_self k)
  exacts [good_f_iff.mp (k_ih (f 0 k) h), ⟨k, λ m ↦ ⟨m, m.le_refl, (f 0).iterate_fixed h m⟩⟩]

/--
@isnad1 id=good.0h1v.s3.25bd144a495d from=translated src=- shape=56f853c1 vocab=6d09ebfb
-/
theorem good_one_left (k) : good 1 k := by
  ---- Strong induction on `k`
  induction k using Nat.strongRecOn with | ind k h0 => ?_
  obtain h | h : 2 < k ∨ k ≤ 2 := lt_or_ge 2 k
  ---- First clear the induction step
  · obtain ⟨m, h1⟩ : ∃ m, (f 1)^[m] k ≤ 2 := exists_f_one_iterate_le_two k
    exact good_f_iterate_iff.mp (h0 _ (Nat.lt_of_le_of_lt h1 h))
  ---- Now bash all the three base cases
  rw [Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at h
  rcases h with (rfl | rfl) | rfl
  · exact good_zero_right 1
  · exact good_one_right 1
  · replace h0 : (f 1)^[3] 2 = 2 := by unfold f; norm_num
    refine ⟨2, λ m ↦ ⟨3 * m, Nat.le_mul_of_pos_left m (Nat.succ_pos 2), ?_⟩⟩
    rw [(f 1).iterate_mul, Function.iterate_fixed h0]

/-! ### The squarefree case -/

/-- Although this exists on mathlib under `Mathlib.Algebra.Squarefree.Basic`, we don't
  want too many extra imports, and the only instance we need is that `3` is squarefree. -/
def squarefree (n : ℕ) := ∀ x, x ^ 2 ∣ n → x = 1

/--
@isnad1 id=squarefr.2h2v.s3.a4e59e2eb87d from=translated src=- shape=43a197de vocab=071b7ca8
-/
lemma squarefree.of_dvd (hn : squarefree n) (hk : k ∣ n) : squarefree k :=
  λ x hx ↦ hn x (Nat.dvd_trans hx hk)

/--
@isnad1 id=squarefr.0h0v.s2.d4b202120475 from=translated src=- shape=e590c3e1 vocab=27620731
-/
lemma three_is_squarefree : squarefree 3 := λ x hx ↦ by
  have X : 0 < 3 := Nat.succ_pos 2
  have h : x = 0 ∨ x = 1 := by
    have h : Nat.sqrt 3 = 1 := by norm_num
    rw [← Nat.le_one_iff_eq_zero_or_eq_one, ← h, Nat.le_sqrt']
    exact Nat.le_of_dvd X hx
  exact h.resolve_left (Nat.ne_of_gt (Nat.pos_of_mul_pos_left (Nat.pos_of_dvd_of_pos hx X)))

/--
@isnad1 id=not.0h0v.s2.85baf0b231c8 from=translated src=- shape=8d7dbbf6 vocab=27620731
-/
lemma zero_is_not_squarefree : ¬squarefree 0 :=
  λ h ↦ Nat.zero_ne_one (h 0 (Nat.dvd_zero 0))

section

variable (hp : squarefree p)
include hp

/--
@isnad1 id=ne.1h1v.s3.fdea865d2d3c from=translated src=- shape=4f29f389 vocab=27620731
-/
lemma squarefree.ne_zero : p ≠ 0 :=
  λ h ↦ zero_is_not_squarefree (h ▸ hp)

/--
@isnad1 id=lt.1h1v.s3.6edfeffba458 from=translated src=- shape=7d122e43 vocab=0405ca2d
-/
lemma squarefree.pos : 0 < p :=
  Nat.pos_of_ne_zero hp.ne_zero

/--
@isnad1 id=dvd.2h2v.s5.a6dd3ce9a8dc from=translated src=- shape=acb4be25 vocab=47f09600
-/
lemma squarefree.dvd_sq_imp (hk : p ∣ k ^ 2) : p ∣ k := by
  obtain rfl | h : p = 0 ∨ 0 < p := p.eq_zero_or_pos
  · rw [Nat.zero_dvd, Nat.pow_eq_zero] at hk
    exact Nat.zero_dvd.mpr hk.1
  · obtain ⟨a, ha⟩ : p.gcd k ∣ p := p.gcd_dvd_left k
    obtain ⟨b, hb⟩ : p.gcd k ∣ k := p.gcd_dvd_right k
    suffices a = 1 from ⟨b, by rwa [ha, this, Nat.mul_one]⟩
    suffices a ∣ p.gcd k by
      refine hp a ?_
      rw [Nat.pow_two, ha]
      exact Nat.mul_dvd_mul_right this a
    replace hn : 0 < p.gcd k := Nat.gcd_pos_of_pos_left k h
    replace h : a.Coprime b := by
      rw [Nat.Coprime, ← Nat.mul_right_inj (Nat.ne_of_gt hn),
        ← Nat.gcd_mul_left, ← ha, ← hb, Nat.mul_one]
    generalize p.gcd k = d at ha hb hn ⊢; subst p k
    rw [Nat.mul_pow, d.pow_two, d.mul_assoc, Nat.mul_dvd_mul_iff_left hn] at hk
    exact Nat.Coprime.dvd_of_dvd_mul_right (h.pow_right 2) hk

/--
@isnad1 id=dvd.2h3v.s5.b20af0d0a033 from=translated src=- shape=2ca8c561 vocab=80980d4f
-/
lemma squarefree.dvd_of_mul_eq_sq (hk : p * k = x ^ 2) : p ∣ k := by
  obtain ⟨m, rfl⟩ : p ∣ x := hp.dvd_sq_imp ⟨k, hk.symm⟩
  rw [Nat.mul_pow, p.pow_two, p.mul_assoc, Nat.mul_right_inj hp.ne_zero] at hk
  exact ⟨m ^ 2, hk⟩

/--
@isnad1 id=eq.2h1v.s5.32c08fc48320 from=translated src=- shape=65a000c8 vocab=cc682adc
-/
lemma squarefree.f_self (h : p ≠ 1) : f p p = 2 * p := by
  refine p.two_mul ▸ ite_eq_right λ h0 ↦ absurd (hp p.sqrt ⟨1, ?_⟩) (λ h1 ↦ h ?_)
  · rw [h0, p.mul_one]
  · rwa [h1, Nat.one_pow, eq_comm] at h0

/--
@isnad1 id=eq.2h2v.s5.ebd4b4287050 from=translated src=- shape=6b9af0e9 vocab=607eaac6
-/
lemma squarefree.f_iterate_self (h : k < p) : (f p)^[k] p = p * (k + 1) := by
  induction k with | zero => exact p.mul_one.symm | succ k hk => ?_
  rw [(f p).iterate_succ_apply', hk (Nat.lt_of_succ_lt h), p.mul_succ (k + 1)]
  exact ite_eq_right λ h0 ↦ Nat.not_dvd_of_pos_of_lt k.succ_pos h (hp.dvd_of_mul_eq_sq h0.symm)

/--
@isnad1 id=eq.1h1v.s3.fd3ee3bf2a95 from=translated src=- shape=1464b291 vocab=0cee6b76
-/
lemma squarefree.f_iterate_self_self : (f p)^[p] p = p := by
  have h := congrArg (f p) (hp.f_iterate_self (Nat.pred_lt hp.ne_zero))
  rw [← (f p).iterate_succ_apply', ← Nat.succ_eq_add_one, Nat.succ_pred hp.ne_zero] at h
  rw [h, ← Nat.pow_two, f, Nat.sqrt_eq', ite_eq_left rfl]

/--
@isnad1 id=good.1h1v.s3.4b268a9fc961 from=translated src=- shape=4a2427db vocab=871caed0
-/
lemma squarefree.good_self : good p p := by
  refine ⟨p, λ m ↦ ⟨p * m, Nat.le_mul_of_pos_left m hp.pos, ?_⟩⟩
  rw [(f p).iterate_mul, Function.iterate_fixed hp.f_iterate_self_self m]

/--
@isnad1 id=good.1h1v.s4.7c4fa4c27d52 from=translated src=- shape=35a60626 vocab=1e821d34
-/
lemma squarefree.good_two_mul : good p (2 * p) := by
  obtain rfl | h : p = 1 ∨ p ≠ 1 := dec_em (p = 1)
  · exact good_one_left 2
  · rw [← hp.f_self h, good_f_iff]; exact hp.good_self

/--
@isnad1 id=dvd.2h2v.s4.89652980bcb7 from=translated src=- shape=a6742926 vocab=2ab3dd23
-/
lemma squarefree.dvd_f_of_dvd (h : p ∣ N) : p ∣ f p N := by
  unfold f; split_ifs with h0
  exacts [hp.dvd_sq_imp (h0.symm ▸ h), Nat.dvd_add_self_right.mpr h]

/--
@isnad1 id=dvd.2h3v.s4.b21479bee154 from=translated src=- shape=7b4b8c84 vocab=eaa2ffc9
-/
lemma squarefree.dvd_f_iterate_of_dvd (h : p ∣ N) : ∀ k, p ∣ (f p)^[k] N := by
  refine Nat.rec h λ n ↦ ?_
  rw [(f p).iterate_succ_apply']; exact hp.dvd_f_of_dvd

/--
@isnad1 id=good.2h2v.s4.db35f4da93f7 from=translated src=- shape=38619297 vocab=a779d53e
-/
theorem squarefree.good_of_dvd (hN : p ∣ N) : good p N := by
  ---- We will instead induct to show that `pN` is good for all `N`
  rcases hN with ⟨N, rfl⟩
  induction N using Nat.strongRecOn with | ind N N_ih => ?_
  obtain h | h : 2 < N ∨ N ≤ 2 := lt_or_ge 2 N
  ---- First clear the induction step
  · obtain ⟨m, h0⟩ : ∃ m, (f p)^[m] (p * N) < p * N := by
      refine exists_f_iterate_lt_self_of_big hp.pos ?_ ⟨0, ?_⟩
      · rwa [Nat.mul_comm, Nat.mul_lt_mul_left hp.pos]
      · rw [Nat.pow_two, Nat.zero_mul, Nat.zero_mod, Nat.mul_mod_right]
    obtain ⟨N', h1⟩ : p ∣ (f p)^[m] (p * N) := hp.dvd_f_iterate_of_dvd ⟨N, rfl⟩ m
    rw [h1, Nat.mul_lt_mul_left hp.pos] at h0
    rw [← good_f_iterate_iff (k := m), h1]
    exact N_ih N' h0
  ---- Now bash all the three base cases
  rw [Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at h
  rcases h with (rfl | rfl) | rfl
  · rw [p.mul_zero]; exact good_zero_right p
  · rw [p.mul_one]; exact hp.good_self
  · rw [p.mul_comm]; exact hp.good_two_mul

end

/-! ### Final solution -/

/-- Final solution
@isnad1 id=iff.0h1v.s4.2247d67ad227 from=translated src=- shape=d6e2fd88 vocab=ba079ff3
-/
theorem final_solution : good 3 N ↔ N = 1 ∨ 3 ∣ N := by
  refine ⟨λ hN ↦ ?_, λ hN ↦ ?_⟩
  ---- `→` direction
  · obtain ⟨k, h⟩ : ∃ k, (f 3)^[k] N ≤ 3 := hN.exists_iterate_le_p (Nat.lt_succ_self 2)
    rw [Nat.le_succ_iff, Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at h
    rcases h with ((h | h) | h) | h
    · right; exact ⟨0, f_iterate_eq_zero_iff.mp h⟩
    · left; exact f_iterate_eq_one_iff.mp h
    · rw [← good_f_iterate_iff (k := k), h] at hN
      refine absurd hN (not_good_of_not_sq_mod_fin (Nat.succ_pos 2) ?_)
      decide
    · right; exact dvd_of_dvd_f_iterate ⟨1, h⟩
  ---- `←` direction
  · rcases hN with rfl | hN
    exacts [good_one_right 3, three_is_squarefree.good_of_dvd hN]
