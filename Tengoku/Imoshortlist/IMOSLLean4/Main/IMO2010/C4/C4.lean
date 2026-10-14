/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module

/-!
# IMO 2010 C4 (P5)

In the board, $N = 6$ stacks of coins are given with stack $k < N$ containing one coin each.
At any time, one of the following operations are done:
* Remove a coin from a stack $k + 1 < N$ and add two coins to stack $k$.
* Remove a coin from a stack $k + 2 < N$ and swap the content of the stacks $k$ and $k + 1$.
Is it possible that, after some operations, we are left with stack $0$
  containing $A = 2010^{2010^{2010}}$ coins and all other stacks empty?
-/

@[expose] public section

namespace IMOSL
namespace IMO2010C4

/-! ### Iteration of two-power -/

/-- Iteration of two-power -/
def P (seed : Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => P (2 ^ seed) n

/--
@isnad1 id=eq.0h1v.s3.04bbaa47ec3f from=translated src=- shape=1fa26838 vocab=eb31a339
-/
theorem P_zero (seed) : P seed 0 = seed := rfl

/--
@isnad1 id=eq.0h2v.s4.9b97df5fb4e5 from=translated src=- shape=ac2ad1e2 vocab=7a221724
-/
theorem P_succ (seed n) : P seed n.succ = P (2 ^ seed) n := rfl

/--
@isnad1 id=eq.0h2v.s4.3c4a192e85de from=translated src=- shape=b400595a vocab=7a221724
-/
theorem P_succ' (seed) : ∀ n, P seed n.succ = 2 ^ P seed n
  | 0 => rfl
  | n + 1 => by rw [P_succ, P_succ', P_succ]

/--
@isnad1 id=lt.1h2v.s4.622841dd7969 from=translated src=- shape=d58f95ac vocab=e7c1d021
-/
theorem P_pos_of_seed (h : 0 < seed) : ∀ n, 0 < P seed n
  | 0 => h
  | n + 1 => P_pos_of_seed (Nat.pow_pos Nat.two_pos) n

/--
@isnad1 id=lt.1h3v.s4.87f6b7fe7312 from=translated src=- shape=79c5e0af vocab=e7c1d021
-/
theorem P_lt_of_seed (h : seed₁ < seed₂) : ∀ n, P seed₁ n < P seed₂ n
  | 0 => h
  | n + 1 => P_lt_of_seed (Nat.pow_lt_pow_of_lt (Nat.lt_succ_self 1) h) n

/-- A copy of `Nat.lt_two_pow`
@isnad1 id=lt.0h1v.s4.a48c2652c57b from=translated src=- shape=e17d9afa vocab=7ddce274
-/
theorem Nat_lt_two_pow : ∀ n, n < 2 ^ n := by
  refine Nat.rec Nat.one_pos λ n h ↦ ?_
  rw [Nat.pow_succ, Nat.mul_two]; exact Nat.add_lt_add_of_lt_of_le h Nat.one_le_two_pow

/--
@isnad1 id=lt.0h1v.s3.39c15115905f from=translated src=- shape=591c59b6 vocab=e7c1d021
-/
theorem seed_lt_P_one (seed) : seed < P seed 1 :=
  Nat_lt_two_pow seed

/--
@isnad1 id=lt.0h2v.s4.968f2af589e3 from=translated src=- shape=e692bb03 vocab=eace6beb
-/
theorem P_lt_succ_iter (seed n) : P seed n < P seed (n + 1) :=
  P_lt_of_seed (seed_lt_P_one seed) n

/--
@isnad1 id=le.0h3v.s4.c419fcf88e34 from=translated src=- shape=5ed860cf vocab=d367d4d8
-/
theorem P_le_add_iter (seed n) : ∀ k, P seed n ≤ P seed (n + k)
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (P_le_add_iter seed n k) (Nat.le_of_lt (P_lt_succ_iter seed _))

/--
@isnad1 id=le.1h3v.s4.a3541f33cbb4 from=translated src=- shape=dc7ae3e3 vocab=29262f6a
-/
theorem P_monotone_iter (seed) (h : n ≤ m) : P seed n ≤ P seed m :=
  Nat.add_sub_cancel' h ▸ P_le_add_iter seed n (m - n)

/--
@isnad1 id=lt.1h3v.s4.d21ed37d3636 from=translated src=- shape=dc7ae3e3 vocab=e7c1d021
-/
theorem P_strict_mono_iter (seed) (h : n < m) : P seed n < P seed m :=
  Nat.lt_of_lt_of_le (P_lt_succ_iter seed n) (P_monotone_iter seed h)

/--
@isnad1 id=le.1h3v.s4.53815cc90a8a from=translated src=- shape=c887747c vocab=29262f6a
-/
theorem le_of_P_le_iter (h : P seed n ≤ P seed m) : n ≤ m :=
  Nat.le_of_not_lt λ h0 ↦ Nat.not_lt_of_le h (P_strict_mono_iter seed h0)

/--
@isnad1 id=iff.0h3v.s4.26c474fa79ee from=translated src=- shape=518d04df vocab=29262f6a
-/
theorem P_iter_le_iff : P seed n ≤ P seed m ↔ n ≤ m :=
  ⟨le_of_P_le_iter, P_monotone_iter seed⟩

/-! ### More lemmas on `log2` -/

/--
@isnad1 id=iff.1h2v.s5.feec7a3ffd7c from=translated src=- shape=e4a7ee4e vocab=14cf6afb
-/
theorem log2_lt_iff₂ {n} (hk : 0 < k) : n.log2 < k ↔ n < 2 ^ k :=
  match n with
  | 0 => ⟨λ _ ↦ k.two_pow_pos, λ _ ↦ by rwa [Nat.log2_zero]⟩
  | n + 1 => Nat.log2_lt n.succ_ne_zero

/--
@isnad1 id=le.1h2v.s4.3ba11604abcb from=translated src=- shape=6bee9d27 vocab=21935081
-/
theorem log2_monotone {m n : Nat} (h : m ≤ n) : m.log2 ≤ n.log2 :=
  match m with
  | 0 => by rw [Nat.log2_zero]; exact n.log2.zero_le
  | m + 1 => (Nat.le_log2 (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt h))).mpr
      (Nat.le_trans (Nat.log2_self_le m.succ_ne_zero) h)

/--
@isnad1 id=eq.0h1v.s4.f174a4ddddf5 from=translated src=- shape=20e71180 vocab=fcdf0226
-/
theorem log2_two_pow : ∀ n : Nat, (2 ^ n).log2 = n
  | 0 => by simp [Nat.pow_zero, Nat.log2_def]
  | n + 1 => by rw [Nat.pow_succ, Nat.log2_def, Nat.mul_div_left _ Nat.two_pos,
      log2_two_pow, ite_eq_left (Nat.le_mul_of_pos_left 2 n.two_pow_pos)]

/-! ### Iteration of `log2` -/

def log2_iter (seed : Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => log2_iter seed.log2 n

/--
@isnad1 id=eq.0h1v.s3.97e803f92e8f from=translated src=- shape=1fa26838 vocab=a6b3b399
-/
theorem log2_iter_zero (seed) : log2_iter seed 0 = seed := rfl

/--
@isnad1 id=eq.0h2v.s4.9e6c0cc2c7cd from=translated src=- shape=f03ca6bd vocab=6c541b82
-/
theorem log2_iter_succ (seed n) : log2_iter seed (n + 1) = log2_iter seed.log2 n := rfl

/--
@isnad1 id=eq.0h3v.s4.c128c73f1788 from=translated src=- shape=99b7d63c vocab=9999f055
-/
theorem log2_iter_add (seed n) :
    ∀ k, log2_iter seed (n + k) = log2_iter (log2_iter seed k) n
  | 0 => rfl
  | k + 1 => by rw [← n.add_assoc, log2_iter_succ, log2_iter_succ, log2_iter_add]

/--
@isnad1 id=iff.1h3v.s4.b4acbbf44b3d from=translated src=- shape=6adb3d9b vocab=ac461fa4
-/
theorem log2_iter_lt_iff {seed} (hk : 0 < k) : ∀ {n}, log2_iter seed n < k ↔ seed < P k n
  | 0 => Iff.rfl
  | n + 1 => by rw [P_succ', log2_iter, log2_iter_lt_iff hk,
      log2_lt_iff₂ (P_pos_of_seed hk n)]

/--
@isnad1 id=iff.0h2v.s4.832b601fc685 from=translated src=- shape=d9d337f9 vocab=ac461fa4
-/
theorem log2_iter_eq_zero_iff : log2_iter seed n = 0 ↔ seed < P 1 n := by
  rw [← log2_iter_lt_iff Nat.one_pos, Nat.lt_succ_iff, Nat.le_zero]

/--
@isnad1 id=le.1h3v.s4.4b1ee2c87b92 from=translated src=- shape=79c5e0af vocab=44bde512
-/
theorem log2_iter_monotone_seed (h : seed₁ ≤ seed₂) :
    ∀ n, log2_iter seed₁ n ≤ log2_iter seed₂ n
  | 0 => h
  | n + 1 => log2_iter_monotone_seed (log2_monotone h) n

/--
@isnad1 id=le.0h2v.s3.e557c1906de9 from=translated src=- shape=03d1ed50 vocab=44bde512
-/
theorem log2_iter_le_self (seed) : ∀ n, log2_iter seed n ≤ seed
  | 0 => seed.le_refl
  | n + 1 => Nat.le_trans (log2_iter_le_self seed.log2 n) (Nat.log2_le_self seed)

/--
@isnad1 id=le.1h3v.s4.b55447f82f41 from=translated src=- shape=3e3801c9 vocab=44bde512
-/
theorem log2_antitone_iter (seed) (h : m ≤ n) : log2_iter seed n ≤ log2_iter seed m := by
  rw [← Nat.sub_add_cancel h, log2_iter_add]; exact log2_iter_le_self _ _

/- ### The game -/

open List

inductive isReachable : List Nat → List Nat → Prop
  | type1_move (k m) : isReachable [k + 1, m] [k, m + 2]
  | type2_move (k m n) : isReachable [k + 1, m, n] [k, n, m]
  | refl (l) : isReachable l l
  | trans (h : isReachable l₁ l₂) (h : isReachable l₂ l₃) : isReachable l₁ l₃
  | append_right (h : isReachable l₁ l₂) (l) : isReachable (l₁ ++ l) (l₂ ++ l)
  | cons_left (h : isReachable l₁ l₂) (k) : isReachable (k :: l₁) (k :: l₂)

namespace isReachable

/-! ### General observation -/

/--
@isnad1 id=isreacha.1h3v.s5.11687aa36d8b from=translated src=- shape=521f7267 vocab=0b34331f
-/
theorem append_left (h : isReachable l₁ l₂) : ∀ l, isReachable (l ++ l₁) (l ++ l₂)
  | [] => h
  | k :: l => cons_left (append_left h l) k

/--
@isnad1 id=isreacha.1h4v.s6.715bf23a0d43 from=translated src=- shape=6a25f5d6 vocab=0b34331f
-/
theorem append_left_right (h : isReachable l₁ l₂) (l l') :
    isReachable (l ++ l₁ ++ l') (l ++ l₂ ++ l') :=
  append_right (append_left h l) l'

/--
@isnad1 id=isreacha.0h3v.s5.7f5fb8505c67 from=translated src=- shape=53ac03c6 vocab=09904ef3
-/
theorem type1_repeat (k m) : ∀ n, isReachable [k + n, m] [k, m + 2 * n]
  | 0 => refl [k, m]
  | n + 1 => by
      rw [Nat.mul_succ, ← m.add_assoc, Nat.add_right_comm]
      exact (type1_move _ _).trans (type1_repeat _ _ n)

/--
@isnad1 id=isreacha.0h1v.s5.b460b5b1dae8 from=translated src=- shape=b1c77d35 vocab=2a38600f
-/
theorem type1_repeat_zero (n) : isReachable [n, 0] [0, 2 * n] := by
  have h := type1_repeat 0 0 n; rwa [n.zero_add, Nat.zero_add] at h

/--
@isnad1 id=isreacha.0h4v.s6.8076e05d524d from=translated src=- shape=da059d1d vocab=7250995d
-/
theorem two_pow₁ (k n m) : ∀ c, isReachable [k + c, n + m, n] [k, n + 2 ^ c * m, n]
  | 0 => by rw [Nat.pow_zero, Nat.one_mul]; exact refl _
  | c + 1 => by
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact (cons_left (type1_repeat _ _ _) _).trans
        ((type2_move _ _ _).trans (two_pow₁ _ _ _ _))

/--
@isnad1 id=isreacha.0h3v.s6.84268697bb60 from=translated src=- shape=ea083c2f vocab=2cbea148
-/
theorem two_pow₂ (k n c) : isReachable [k + (c + 1), n, n] [k, n + 2 ^ (c + 1), n] :=
  (append_right (type1_move _ _) [n]).trans (two_pow₁ _ _ _ _)

/--
@isnad1 id=isreacha.1h3v.s6.37cef0d13c44 from=translated src=- shape=88ae7156 vocab=3f9d3355
-/
theorem two_pow₃ (k n) (hc : 0 < c) : isReachable [k + c, n, n] [k, n + 2 ^ c, n] :=
  Nat.succ_pred_eq_of_pos hc ▸ two_pow₂ k n c.pred

/--
@isnad1 id=isreacha.1h4v.s6.4ef246b2aa13 from=translated src=- shape=2b941e61 vocab=9be47487
-/
theorem two_pow_iter₁ (k n) (hm : 0 < m) :
    ∀ c, isReachable [k + c, n + m, n, n] [k, n + P m c, n, n]
  | 0 => refl _
  | Nat.succ c => (cons_left (two_pow₃ _ _ hm) _).trans <|
      (append_right (type2_move _ _ _) [n]).trans (two_pow_iter₁ k n m.two_pow_pos c)

/--
@isnad1 id=isreacha.0h3v.s6.5e7f3149ac40 from=translated src=- shape=981cc92f vocab=8de8f4e8
-/
theorem two_pow_iter₂ (k n c) :
    isReachable [k + (c + 1), n, n, n] [k, n + P 1 (c + 1), n, n] :=
  (append_right (type1_move _ _) _).trans (two_pow_iter₁ k n Nat.two_pos _)

/--
@isnad1 id=isreacha.1h3v.s6.e588a3f457bb from=translated src=- shape=63702682 vocab=9be47487
-/
theorem two_pow_iter₃ (k n) (hc : 0 < c) :
    isReachable [k + c, n, n, n] [k, n + P 1 c, n, n] :=
  Nat.succ_pred_eq_of_pos hc ▸ two_pow_iter₂ k n c.pred

/--
@isnad1 id=isreacha.1h2v.s5.369ff6d02332 from=translated src=- shape=5059f882 vocab=9be47487
-/
theorem two_pow_iter₄ (n) (hc : 0 < c) : isReachable [c, n, n, n] [0, n + P 1 c, n, n] := by
  have h := two_pow_iter₃ 0 n hc; rwa [c.zero_add] at h

/--
@isnad1 id=isreacha.0h3v.s5.775c57e25d9a from=translated src=- shape=4469a14b vocab=b69c7642
-/
theorem type2_repeat_drain₀ (k n) : ∀ c, isReachable [k + c, n, n] [k, n, n]
  | 0 => refl _
  | c + 1 => (type2_move (k + c) n n).trans (type2_repeat_drain₀ k n c)

/--
@isnad1 id=isreacha.1h3v.s5.7fa6d47463a8 from=translated src=- shape=cab605c4 vocab=59191361
-/
theorem type2_repeat_drain (n) (h : k ≤ m) : isReachable [m, n, n] [k, n, n] :=
  Nat.add_sub_of_le h ▸ type2_repeat_drain₀ k n (m - k)

/-! ### Reachability of specific states -/

/--
@isnad1 id=isreacha.0h1v.s5.67140bcefbfd from=translated src=- shape=7bff08d8 vocab=d12358ac
-/
theorem replicate_ones_to_3₀ :
    ∀ n, isReachable (replicate (n + 2) 1) (0 :: 3 :: replicate n 0)
  | 0 => type1_move 0 1
  | n + 1 => (cons_left (replicate_ones_to_3₀ n) _).trans
      (append_right (type2_move 0 0 3) (replicate n 0))

/--
@isnad1 id=isreacha.0h1v.s5.5e3dc438e51d from=translated src=- shape=7bff08d8 vocab=d12358ac
-/
theorem replicate_ones_to_3₁ (n) :
    isReachable (replicate (n + 2) 1) (0 :: 3 :: replicate n 1) :=
  append_right (type1_move 0 1) (replicate n 1)

/--
@isnad1 id=isreacha.1h2v.s6.d54cfa8a7b2a from=translated src=- shape=5e53a40c vocab=9be47487
-/
theorem cons_replicate4_to_P₀ (n) (hN : 0 < N) :
    isReachable [N, n, n, n, n] [0, 0, n + P 1 (n + P 1 N), n, n] :=
  (append_right (two_pow_iter₄ n hN) [n]).trans
    (cons_left (two_pow_iter₄ n (Nat.add_pos_right _ (P_pos_of_seed Nat.one_pos N))) 0)

/--
@isnad1 id=isreacha.1h2v.s6.430356810e81 from=translated src=- shape=1be34b32 vocab=9a4d3e0a
-/
theorem cons_replicate4_to_P (n) (hN : 0 < N) :
    isReachable [N, n, n, n, n] [0, 0, P 1 (P 1 N), n, n] :=
  suffices P 1 (P 1 N) ≤ n + P 1 (n + P 1 N) from
    (cons_replicate4_to_P₀ n hN).trans (append_left (type2_repeat_drain n this) [0, 0])
  Nat.le_trans (P_monotone_iter 1 ((P 1 N).le_add_left n)) (Nat.le_add_left _ n)

/--
@isnad1 id=isreacha.0h4v.s5.b85931042c88 from=translated src=- shape=1b41e400 vocab=09904ef3
-/
theorem type1_double_repeat (a b c N) : isReachable [a + N, b, c] [a, b, c + 4 * N] :=
  Nat.mul_assoc 2 2 N ▸ (append_right (type1_repeat a b N) [c]).trans
    (cons_left (type1_repeat b c (2 * N)) a)

/--
@isnad1 id=isreacha.0h3v.s5.3827f75b4549 from=translated src=- shape=0214e3cc vocab=09904ef3
-/
theorem type1_double_repeat_a_eq_zero (b c N) : isReachable [N, b, c] [0, b, c + 4 * N] := by
  simpa only [Nat.zero_add] using type1_double_repeat 0 b c N

/-- `[2, 0, 0] → [1, 2, 0] → [1, 1, 2] → [0, 2, 1] → [0, 0, 5]`
@isnad1 id=isreacha.0h1v.s6.63b5a95d0539 from=translated src=- shape=9c60d55c vocab=09904ef3
-/
theorem Nadd2_zero_zero_to_4Nadd5 (N) : isReachable [N + 2, 0, 0] [0, 0, 4 * N + 5] := by
  apply (append_right (type1_move (N + 1) 0) [0]).trans
  apply (cons_left (type1_move 1 0) (N + 1)).trans
  apply (type2_move N 1 2).trans
  apply (type1_double_repeat_a_eq_zero 2 1 N).trans
  exact (4 * N).add_comm 1 ▸ cons_left (type1_repeat 0 (4 * N + 1) 2) 0

/-- `[2, 0, 0] → [1, 2, 0] → [0, 0, 2]`
@isnad1 id=isreacha.0h1v.s6.3ddd4679bf18 from=translated src=- shape=9c60d55c vocab=09904ef3
-/
theorem Nadd2_zero_zero_to_4Nadd2 (N) : isReachable [N + 2, 0, 0] [0, 0, 4 * N + 2] := by
  apply (append_right (type1_move (N + 1) 0) [0]).trans
  apply (type2_move N 2 0).trans
  exact (4 * N).add_comm 2 ▸ type1_double_repeat_a_eq_zero 0 2 N

/-- `[5, 0, 0] → [1, 16, 0] → [1, 14, 4] → [0, 4, 14] → [0, 0, 22]`
@isnad1 id=isreacha.0h1v.s6.b37c0e0e91e7 from=translated src=- shape=9c60d55c vocab=09904ef3
-/
theorem Nadd5_zero_zero_to_4Nadd22 (N) : isReachable [N + 5, 0, 0] [0, 0, 4 * N + 22] := by
  apply (two_pow₃ (N + 1) 0 (Nat.succ_pos 3)).trans
  apply (cons_left (type1_repeat 14 0 2) (N + 1)).trans
  apply (type2_move N 14 4).trans
  apply (cons_left (type1_repeat 0 14 4) N).trans
  exact (4 * N).add_comm 22 ▸ type1_double_repeat_a_eq_zero 0 22 N

/--
@isnad1 id=isreacha.0h1v.s6.08377588f9a2 from=translated src=- shape=03163ded vocab=09904ef3
-/
theorem N_one_one_to_4Nadd3 (N) : isReachable [N, 1, 1] [0, 0, 4 * N + 3] :=
  (cons_left (type1_move 0 1) N).trans <|
    (4 * N).add_comm 3 ▸ type1_double_repeat_a_eq_zero 0 3 N

/--
@isnad1 id=isreacha.2h2v.s6.bf667f7a3fed from=translated src=- shape=becd4c8e vocab=379ee548
-/
theorem three_stack_0mod4 (N) (hA : A % 4 = 0) (h : A < 4 * N) :
    isReachable [N, 0, 0] [0, 0, A] := by
  rw [← A.div_add_mod 4, Nat.add_comm, hA]
  exact (type2_repeat_drain 0 (Nat.div_le_of_le_mul (Nat.le_of_lt h))).trans
    (type1_double_repeat_a_eq_zero 0 0 (A / 4))

/--
@isnad1 id=isreacha.4h2v.s6.b4e790856bf6 from=translated src=- shape=75aabfc4 vocab=e1228769
-/
theorem three_stack_1mod4 (hN : 2 ≤ N) (hA : A % 4 = 1) (hA0 : A ≠ 1) (h : A < 4 * N) :
    isReachable [N, 0, 0] [0, 0, A] := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 2 := Nat.exists_eq_add_of_le' hN
  obtain ⟨A', h0, rfl⟩ : ∃ A', A' ≤ N' ∧ A = 4 * A' + 5 := by
    refine ⟨A / 4 - 1, ?_, ?_⟩
    · rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 3), Nat.lt_succ_iff] at h
      exact Nat.sub_le_of_le_add h
    · rw [← A.div_add_mod 4, hA, Ne, Nat.add_right_cancel_iff] at hA0
      replace hA0 := (Nat.mul_ne_zero_iff.mp hA0).2
      change A = 4 * (A / 4 - 1 + 1) + 1
      rw [Nat.sub_add_cancel (Nat.ne_zero_iff_zero_lt.mp hA0), ← hA, A.div_add_mod]
  exact (type2_repeat_drain 0 (Nat.add_le_add_right h0 2)).trans
    (Nadd2_zero_zero_to_4Nadd5 A')

/--
@isnad1 id=isreacha.3h2v.s6.bbbaa6f9bae1 from=translated src=- shape=26dd4f5a vocab=e1228769
-/
theorem three_stack_2mod4 (hN : 6 ≤ N) (hA : A % 4 = 2) (h : A < 4 * N) :
    isReachable [N, 0, 0] [0, 0, A] := by
  rw [← A.div_add_mod 4, hA]
  obtain ⟨N, rfl⟩ : ∃ N', N'.succ = N :=
    ⟨N.pred, Nat.sub_one_add_one_eq_of_pos (Nat.zero_lt_of_lt hN)⟩
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 3), Nat.lt_succ_iff_lt_or_eq] at h
  rcases h with h | h
  ---- Case 1: `A/4 < N`
  · refine (type2_repeat_drain 0 ?_).trans (Nadd2_zero_zero_to_4Nadd2 (A / 4))
    rwa [Nat.succ_le_succ_iff, Nat.succ_le_iff]
  ---- Case 2: `A/4 = N`
  · rw [h]; clear A hA h
    rcases Nat.exists_eq_add_of_le' (Nat.succ_le_succ_iff.mp hN) with ⟨K, rfl⟩
    rw [Nat.mul_add, Nat.add_assoc]
    exact (type2_move (K + 5) 0 0).trans (Nadd5_zero_zero_to_4Nadd22 K)

/--
@isnad1 id=isreacha.2h2v.s6.655e68a55634 from=translated src=- shape=becd4c8e vocab=379ee548
-/
theorem three_stack_3mod4 (N) (hA : A % 4 = 3) (h : A < 4 * N) :
    isReachable [N, 1, 1] [0, 0, A] := by
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 3)] at h
  rw [← A.div_add_mod 4, hA]
  exact (type2_repeat_drain 1 (Nat.le_of_succ_le h)).trans (N_one_one_to_4Nadd3 _)

/--
@isnad1 id=isreacha.5h3v.s7.ff9c1f2ba335 from=translated src=- shape=242dcb29 vocab=638cdea0
-/
theorem three_stack_of_bdd (hN : 6 ≤ N) (hL₀ : isReachable L [0, 0, 0, N, 0, 0])
    (hL₁ : isReachable L [0, 0, 0, N, 1, 1]) (h : A ≠ 1) (h0 : A < 4 * N) :
    isReachable L (replicate 5 0 ++ [A]) := by
  have h1 : A % 4 < 4 := A.mod_lt (Nat.succ_pos 3)
  iterate 3 rw [Nat.lt_succ_iff_lt_or_eq] at h1
  ---- Cases on `A % 4`: `0, 1, 2, 3` resp.
  rcases h1 with ((h1 | h1) | h1) | h1
  · rw [Nat.lt_one_iff] at h1
    exact hL₀.trans (append_left (three_stack_0mod4 N h1 h0) [0, 0, 0])
  · replace hN : 2 ≤ N := Nat.le_trans (Nat.le_add_left 2 4) hN
    exact hL₀.trans (append_left (three_stack_1mod4 hN h1 h h0) [0, 0, 0])
  · exact hL₀.trans (append_left (three_stack_2mod4 hN h1 h0) [0, 0, 0])
  · exact hL₁.trans (append_left (three_stack_3mod4 N h1 h0) [0, 0, 0])

/--
@isnad1 id=isreacha.4h3v.s7.38c7be30536b from=translated src=- shape=c621d877 vocab=572becbb
-/
theorem six_stack_of_bdd (hN : 2 ≤ N) (hL₀ : isReachable L (0 :: N :: replicate 4 0))
    (hL₁ : isReachable L (0 :: N :: replicate 4 1)) (hA : A < 4 * P 1 (P 1 N)) :
    isReachable L (replicate 5 0 ++ [A]) := by
  obtain h0 | rfl : A ≠ 1 ∨ A = 1 := (Decidable.em _).symm
  ---- Case 1: `A ≠ 1`
  · have X (n) := cons_left (cons_replicate4_to_P n (Nat.zero_lt_of_lt hN)) 0
    refine three_stack_of_bdd ?_ (hL₀.trans (X 0)) (hL₁.trans (X 1)) h0 hA
    exact Nat.le_trans (Nat.le_add_left 6 65530) (P_monotone_iter 1 (P_monotone_iter 1 hN))
  ---- Case 2: `A = 1`
  · refine hL₁.trans (append_left_right (?_ : isReachable [N, 1, 1, 1] _) [0] [1])
    apply (cons_left (replicate_ones_to_3₀ 1) N).trans
    rw [← Nat.sub_add_cancel hN]
    apply (append_right (type2_move _ 0 3) [0]).trans
    apply (cons_left (type2_repeat_drain₀ 0 0 3) _).trans
    exact append_right (type2_repeat_drain 0 (Nat.zero_le _)) [0]

/--
@isnad1 id=isreacha.4h3v.s6.b1e065eb07ce from=translated src=- shape=bd5a86a8 vocab=48b74766
-/
theorem six_stack_of_bdd_log (hN : 2 ≤ N) (hL₀ : isReachable L (0 :: N :: replicate 4 0))
    (hL₁ : isReachable L (0 :: N :: replicate 4 1)) (hA : log2_iter (A / 4) (P 1 N) = 0) :
    isReachable L (replicate 5 0 ++ [A]) :=
  six_stack_of_bdd hN hL₀ hL₁ <| by
    rwa [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 3), ← log2_iter_eq_zero_iff]

/--
@isnad1 id=isreacha.1h1v.s6.ae9a9f0e83b6 from=translated src=- shape=a153412a vocab=bf7f0a33
-/
theorem replicate6_ones_to_A (hA : log2_iter (A / 4) 16 = 0) :
    isReachable (replicate 6 1) (replicate 5 0 ++ [A]) :=
  six_stack_of_bdd_log (Nat.le_succ 2) (replicate_ones_to_3₀ 4) (replicate_ones_to_3₁ 4) hA

end isReachable

/-! ### Final solution -/

/-- Final solution
@isnad1 id=isreacha.0h0v.s6.e716534983b9 from=translated src=- shape=eed8f6b5 vocab=bd01a99a
-/
theorem final_solution :
    isReachable (replicate 6 1) (replicate 5 0 ++ [2010 ^ 2010 ^ 2010]) := by
  refine isReachable.replicate6_ones_to_A (Nat.eq_zero_of_le_zero ?_)
  generalize hM : 2010 = M -- Avoid computations of overly big numbers
  replace hM : M ≤ 2 ^ 11 := hM ▸ Nat.le_add_right 2010 38
  calc
    _ ≤ log2_iter (2 ^ (11 * M ^ M)) 16 := by
      refine log2_iter_monotone_seed (Nat.le_trans (Nat.div_le_self _ _) ?_) 16
      rw [Nat.pow_mul]; exact Nat.pow_le_pow_left hM (M ^ M)
    _ = log2_iter (11 * M ^ M) 15 := by rw [log2_iter_succ, log2_two_pow]
    _ ≤ log2_iter (2 ^ (4 + 11 * M)) 15 := by
      refine log2_iter_monotone_seed ?_ 15
      rw [Nat.pow_add, Nat.pow_mul]
      exact Nat.mul_le_mul (Nat.le_add_right 11 5) (Nat.pow_le_pow_left hM M)
    _ = log2_iter (4 + 11 * M) 14 := by rw [log2_iter_succ, log2_two_pow]
    _ ≤ log2_iter (2 ^ 15) 14 :=
      log2_iter_monotone_seed (Nat.add_le_add_left (Nat.mul_le_mul_left 11 hM) 4) 14
    _ = 0 := rfl
