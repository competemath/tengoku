/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4.2: the degree-bound recursion for the quantitative Nullstellensatz

The proof of the Quantitative Hilbert's Nullstellensatz (Theorem 4.83) tracks the degree of the
coefficients through the resultant induction of Proposition 4.77. BPR introduces the bound
function `g(d, 1) = d`, `g(d, k) = g(2 d², k - 1)` and observes that `g(d, k) ≤ (2d)^{2^k}`.

We index by the number of *recursion steps* (one per eliminated variable): `gBound d 0 = d`
(the one-variable base) and `gBound d (k+1) = gBound (2 d²) k`. So `gBound d (k-1)` is BPR's
`g(d, k)` for `k` variables, and the key inequality is `gBound d k ≤ (2d)^{2^{k+1}}`.
-/

namespace Azurite.BPR.Chapter4

/-- BPR's degree-bound recursion `g(d, 1) = d`, `g(d, k) = g(2 d², k - 1)`, indexed by the number
of recursion steps: `gBound d k` is the bound after eliminating `k` variables from a degree-`d`
system (so it is BPR's `g(d, k+1)`).-/
def gBound (d : ℕ) : ℕ → ℕ
  | 0 => d
  | (k + 1) => gBound (2 * d ^ 2) k

/--
@isnad1 id=eq.0h1v.s3.4a4674fb40ae from=translated src=- shape=1fa26838 vocab=8a4771a8
-/
@[simp] theorem gBound_zero (d : ℕ) : gBound d 0 = d := rfl

/--
@isnad1 id=eq.0h2v.s5.80721a93ab64 from=translated src=- shape=a72f6041 vocab=bf173ed4
-/
@[simp] theorem gBound_succ (d k : ℕ) : gBound d (k + 1) = gBound (2 * d ^ 2) k := rfl

/-- **BPR's bound `g(d, k) ≤ (2d)^{2^k}`** (here `gBound d k ≤ (2d)^{2^{k+1}}` after the indexing
shift).
@isnad1 id=le.0h2v.s6.df2df998bc24 from=translated src=- shape=00278585 vocab=4c10bbec
-/
theorem gBound_le (d k : ℕ) : gBound d k ≤ (2 * d) ^ (2 ^ (k + 1)) := by
  induction k generalizing d with
  | zero =>
    rw [gBound_zero]
    calc d ≤ (2 * d) ^ 2 := by nlinarith [Nat.zero_le d]
      _ = (2 * d) ^ (2 ^ (0 + 1)) := by norm_num
  | succ k ih =>
    rw [gBound_succ]
    calc gBound (2 * d ^ 2) k ≤ (2 * (2 * d ^ 2)) ^ (2 ^ (k + 1)) := ih (2 * d ^ 2)
      _ = (2 * d) ^ (2 ^ (k + 1 + 1)) := by
          rw [show 2 * (2 * d ^ 2) = (2 * d) ^ 2 by ring, ← pow_mul]
          congr 1
          rw [pow_succ]
          ring

/-- The weak-Nullstellensatz degree bound, indexed by the number of variables, *including* the
per-step resultant-cofactor overhead. The lift's cofactors carry an `X₀`-degree `< d` (from the
Bézout) on top of the coefficient degree `≤ 2 d²`, so the overhead is `≤ 3 d²`: `wBound d 0 = 0`
(the constant case) and `wBound d (m+1) = wBound (2 d²) m + 3 d²`. This is the degree bound on the
coefficients `A_i` in `∑ A_i P_i = 1` for an `m`-variable system of degree `≤ d` with no common
zero.-/
def wBound (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | (m + 1) => wBound (2 * d ^ 2) m + 3 * d ^ 2

/--
@isnad1 id=eq.0h1v.s4.de3019dfbb56 from=translated src=- shape=1d838610 vocab=82138cb8
-/
@[simp] theorem wBound_zero (d : ℕ) : wBound d 0 = 0 := rfl

/--
@isnad1 id=eq.0h2v.s6.2ad8ca4c006c from=translated src=- shape=bcf3dd15 vocab=8accee4a
-/
@[simp] theorem wBound_succ (d m : ℕ) : wBound d (m + 1) = wBound (2 * d ^ 2) m + 3 * d ^ 2 := rfl

/-- The margin invariant: `wBound d (m+1) + d² ≤ (2d)^{2^{m+1}}`. The extra `+ d²` is the slack
that absorbs the per-step overhead through the induction (`3d² + d² = (2d)²` at the base).-/
private theorem wBound_succ_add_le (d m : ℕ) :
    wBound d (m + 1) + d ^ 2 ≤ (2 * d) ^ (2 ^ (m + 1)) := by
  induction m generalizing d with
  | zero =>
    rw [wBound_succ, wBound_zero]
    calc 0 + 3 * d ^ 2 + d ^ 2 ≤ (2 * d) ^ 2 := by nlinarith [Nat.zero_le d]
      _ = (2 * d) ^ (2 ^ (0 + 1)) := by norm_num
  | succ m ih =>
    rw [wBound_succ]
    have hpow : (2 * (2 * d ^ 2)) ^ (2 ^ (m + 1)) = (2 * d) ^ (2 ^ (m + 1 + 1)) := by
      rw [show 2 * (2 * d ^ 2) = (2 * d) ^ 2 by ring, ← pow_mul]
      congr 1
      rw [pow_succ]; ring
    calc wBound (2 * d ^ 2) (m + 1) + 3 * d ^ 2 + d ^ 2
        ≤ wBound (2 * d ^ 2) (m + 1) + (2 * d ^ 2) ^ 2 := by
          have h4 : (4 : ℕ) * d ^ 2 ≤ (2 * d ^ 2) ^ 2 := by
            rcases Nat.eq_zero_or_pos d with hd | hd
            · simp [hd]
            · nlinarith [Nat.one_le_pow 2 d hd]
          omega
      _ ≤ (2 * (2 * d ^ 2)) ^ (2 ^ (m + 1)) := ih (2 * d ^ 2)
      _ = (2 * d) ^ (2 ^ (m + 1 + 1)) := hpow

/-- **The weak-Nullstellensatz bound matches BPR's `(2d)^{2^m}`** even with the per-step cofactor
overhead: `wBound d m ≤ (2d)^{2^m}`.
@isnad1 id=le.0h2v.s5.101b9c3ae0c3 from=translated src=- shape=810d273a vocab=d704c860
-/
theorem wBound_le (d m : ℕ) : wBound d m ≤ (2 * d) ^ (2 ^ m) := by
  cases m with
  | zero => simp
  | succ m => exact le_trans (Nat.le_add_right _ _) (wBound_succ_add_le d m)

end Azurite.BPR.Chapter4
