/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
module

public import Tengoku.Seed.NumberTheory.Bernoulli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fast computable Bernoulli numbers

This module defines `bernoulliCompute : ℕ → ℚ`, using an incremental binomial
sum and an iterative list recurrence for efficient concrete evaluation.
-/

@[expose] public section

namespace KummerCriterion.BernoulliFast

open Finset

/-- Inner loop for `binomSum`.

`binomSum.loop m bs k c acc` computes
 `acc + ∑_{j=0}^{|bs|−1} C(m, k+j) · bs[j]`
where `c = ↑C(m, k)` is the running binomial coefficient maintained
incrementally in `ℚ`.-/
def binomSum.loop (m : ℕ) (bs : List ℚ) : ℕ → ℚ → ℚ → ℚ :=
  List.rec
    (fun _ _ acc => acc)
    (fun b _ loop k c acc =>
      loop (k + 1)
        (c * ((m : ℚ) - k) / ((k : ℚ) + 1))
        (acc + c * b))
    bs

theorem binomSum_loop_nil (m k : ℕ) (c acc : ℚ) :
    binomSum.loop m [] k c acc = acc := rfl

theorem binomSum_loop_cons (m k : ℕ) (b : ℚ) (rest : List ℚ) (c acc : ℚ) :
    binomSum.loop m (b :: rest) k c acc =
      binomSum.loop m rest (k + 1)
        (c * ((m : ℚ) - k) / ((k : ℚ) + 1))
        (acc + c * b) := rfl

/-- `binomSum bs m = ∑_{k<|bs|} C(m,k) · bs[k]`.

Computed in O(|bs|) rational operations without calling `Nat.choose`.
The binomial coefficient `C(m, k)` is tracked as a running `ℚ` value
updated via `C(m, k+1) = C(m,k) · (m−k)/(k+1)`.-/
def binomSum (bs : List ℚ) (m : ℕ) : ℚ :=
  binomSum.loop m bs 0 1 0

/-- `bernoulliList n` returns the list `[B₀, B₁, …, Bₙ]`.

Uses the recurrence derived from `sum_bernoulli`:
 `(n+2) · B_{n+1} + ∑_{k≤n} C(n+2, k) · Bₖ = 0`
so that
 `B_{n+1} = − (∑_{k≤n} C(n+2,k) · Bₖ) / (n+2)`.-/
def bernoulliList (n : ℕ) : List ℚ :=
  Nat.rec [(1 : ℚ)]
    (fun n prev =>
      let s := binomSum prev (n + 2)
      prev ++ [-s / ((n : ℚ) + 2)])
    n

theorem bernoulliList_zero : bernoulliList 0 = [(1 : ℚ)] := rfl

theorem bernoulliList_succ (n : ℕ) :
    bernoulliList (n + 1) =
      bernoulliList n ++
        [-binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2)] := rfl

/-- Fast computable Bernoulli number `Bₙ`.

Extracts the last element of `bernoulliList n = [B₀, …, Bₙ]`.-/
def bernoulliCompute (n : ℕ) : ℚ :=
  (bernoulliList n).getLast!

end KummerCriterion.BernoulliFast

/-!
# Correctness of `bernoulliCompute`

This module proves `bernoulliCompute n = bernoulli n`, connecting the fast
computable definition to Mathlib's noncomputable `bernoulli`.
-/

@[expose] public section

namespace KummerCriterion.BernoulliFast

open Finset Nat

/-- The multiplicative recurrence for binomial coefficients, cast to `ℚ`:
`↑C(m, k+1) = ↑C(m, k) · (↑m − ↑k) / (↑k + 1)`.

Follows from `(k+1) · C(m, k+1) = (m − k) · C(m, k)` for `k < m`.-/
theorem cast_choose_mul_eq (m k : ℕ) (hk : k < m) :
    (↑(m.choose (k + 1)) : ℚ) =
      ↑(m.choose k) * ((m : ℚ) - k) / ((k : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq m k
  have hq :
      ((m.choose (k + 1) * (k + 1) : ℕ) : ℚ) =
        ((m.choose k * (m - k) : ℕ) : ℚ) := by
    exact_mod_cast h
  have hkq : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hkq]
  simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk.le,
    add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hq

/-- When `k ≥ m`, `C(m, k+1) = 0` and the incremental formula also gives 0.-/
theorem cast_choose_mul_eq_of_le (m k : ℕ) (hk : m ≤ k) :
    (↑(m.choose (k + 1)) : ℚ) = 0 := by
  norm_num [Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hk)]

/-- Loop invariant: `binomSum.loop m bs k c acc` equals
`acc + ∑_{j<|bs|} ↑C(m, k+j) · bs.getD j 0` provided `c = ↑C(m, k)`.-/
theorem binomSum_loop_eq (m : ℕ) (bs : List ℚ) (k : ℕ) (c acc : ℚ)
    (hc : c = ↑(m.choose k)) :
    binomSum.loop m bs k c acc =
      acc + ∑ j ∈ range bs.length, ↑(m.choose (k + j)) * bs.getD j 0 := by
  induction bs generalizing k c acc with
  | nil =>
      simp [binomSum_loop_nil]
  | cons b rest ih =>
      rw [binomSum_loop_cons]
      simp only [List.length_cons]
      have hc' :
          c * ((m : ℚ) - k) / ((k : ℚ) + 1) = ↑(m.choose (k + 1)) := by
        rw [hc]
        by_cases hkm_lt : k < m
        · rw [cast_choose_mul_eq m k hkm_lt]
        · have hkm : m ≤ k := Nat.le_of_not_gt hkm_lt
          rw [cast_choose_mul_eq_of_le m k hkm]
          rw [div_eq_zero_iff]
          left
          by_cases hEq : m = k
          · subst hEq
            norm_num
          · have hchoose0 : (↑(m.choose k) : ℚ) = 0 := by
              norm_num [Nat.choose_eq_zero_of_lt (lt_of_le_of_ne hkm hEq)]
            rw [hchoose0]
            simp
      rw [ih (k := k + 1) (c := c * ((m : ℚ) - k) / ((k : ℚ) + 1))
        (acc := acc + c * b) hc']
      rw [sum_range_succ']
      rw [hc]
      simp [add_assoc, add_left_comm, add_comm, mul_comm]

/-- `binomSum bs m = ∑_{k<|bs|} C(m,k) · bs.getD k 0`.-/
theorem binomSum_eq (bs : List ℚ) (m : ℕ) :
    binomSum bs m =
      ∑ k ∈ range bs.length, ↑(m.choose k) * bs.getD k 0 := by
  unfold binomSum
  rw [binomSum_loop_eq m bs 0 1 0 (by simp)]
  simp

theorem bernoulliList_length (n : ℕ) : (bernoulliList n).length = n + 1 := by
  induction n with
  | zero =>
      simp [bernoulliList_zero]
  | succ n ih =>
      rw [bernoulliList_succ]
      simp [ih]

theorem bernoulliList_getD_lt (n k : ℕ) (hk : k ≤ n) :
    (bernoulliList (n + 1)).getD k 0 = (bernoulliList n).getD k 0 := by
  simpa [bernoulliList_succ] using
    (List.getD_append (bernoulliList n)
      [- binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2)] 0 k
      (by simpa [bernoulliList_length] using Nat.lt_succ_of_le hk))

theorem bernoulliList_getD_eq :
    ∀ n k : ℕ, k ≤ n → (bernoulliList n).getD k 0 = bernoulli k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [bernoulliList_zero]
  | succ n ih =>
      intro k hk
      cases Nat.eq_or_lt_of_le hk with
      | inr hlt =>
          rw [bernoulliList_getD_lt n k (Nat.lt_succ_iff.mp hlt)]
          exact ih k (Nat.lt_succ_iff.mp hlt)
      | inl hEq =>
          subst hEq
          have hlast :
              (bernoulliList (n + 1)).getD (n + 1) 0 =
                - binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2) := by
            rw [bernoulliList_succ]
            rw [List.getD_append_right _ _ _ _]
            · rw [bernoulliList_length]
              simp
            · rw [bernoulliList_length]
          rw [hlast]
          have hsum :
              binomSum (bernoulliList n) (n + 2) =
                ∑ x ∈ range (n + 1), ↑((n + 2).choose x) * bernoulli x := by
            rw [binomSum_eq, bernoulliList_length]
            apply sum_congr rfl
            intro x hx
            rw [ih x (Nat.lt_succ_iff.mp (mem_range.mp hx))]
          rw [hsum]
          have hb :
              (∑ x ∈ range (n + 2), ↑((n + 2).choose x) * bernoulli x) = 0 := by
            simpa only [Nat.succ_succ_ne_one, ite_false] using sum_bernoulli (n + 2)
          rw [sum_range_succ] at hb
          have hchooseNat : (n + 2).choose (n + 1) = n + 2 := by
            simp
          have hchoose : (↑((n + 2).choose (n + 1)) : ℚ) = (n + 2 : ℚ) := by
            exact_mod_cast hchooseNat
          rw [hchoose] at hb
          have hden : (n + 2 : ℚ) ≠ 0 := by positivity
          have hmul :
              bernoulli (n + 1) * (n + 2 : ℚ) =
                -∑ x ∈ range (n + 1), ↑((n + 2).choose x) * bernoulli x := by
            linarith
          exact ((eq_div_iff hden).2 hmul).symm

/-- `bernoulliCompute n = bernoulli n`.-/
theorem bernoulliCompute_eq (n : ℕ) : bernoulliCompute n = bernoulli n := by
  unfold bernoulliCompute
  rw [List.getLast!_eq_getElem!, List.getElem!_eq_getElem?_getD,
    ← List.getD_eq_getElem?_getD]
  simpa [bernoulliList_length] using bernoulliList_getD_eq n n le_rfl

end KummerCriterion.BernoulliFast
