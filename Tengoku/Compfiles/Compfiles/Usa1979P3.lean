/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1979, Problem 3

$a_1, a_2, \dots, a_n$ is an arbitrary sequence of positive integers. A member of the
sequence is picked at random. Its value is $a$. Another member is picked at random,
independently of the first. Its value is $b$. Then a third, value $c$. Show that the
probability that $a + b + c$ is divisible by $3$ is at least $1 / 4$.
-/

namespace Usa1979P3

open Finset

/-- The residue of `a i` modulo `3`. -/
def res {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : ZMod 3 := (a i : ZMod 3)

/-- The number of entries of `a` having residue `x` modulo `3`. -/
def cnt {n : ℕ} (a : Fin n → ℕ) (x : ZMod 3) : ℕ :=
  (univ.filter fun i ↦ res a i = x).card

/-- The "good" residue patterns: triples of residues that sum to `0`. -/
def patterns : Finset (Fin 3 → ZMod 3) := univ.filter fun u ↦ u 0 + u 1 + u 2 = 0

/-- Divisibility by `3` in terms of residues in `ZMod 3`.
@isnad1 id=iff.0h3v.s8.85c406f2690c from=translated src=- shape=9fb43d86 vocab=effcc033
-/
lemma dvd_iff_res {x y z : ℕ} :
    3 ∣ x + y + z ↔ (x : ZMod 3) + (y : ZMod 3) + (z : ZMod 3) = 0 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_add]

/-- Summing over `ZMod 3` gives three terms.
@isnad1 id=eq.0h1v.s7.db65bba2c80e from=translated src=- shape=cea20870 vocab=e3c55c56
-/
lemma sum_univ_zmod3 (f : ZMod 3 → ℕ) : ∑ x : ZMod 3, f x = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- The residues split `Fin n` into the three fibers of `res a`.
@isnad1 id=eq.0h2v.s7.5defd4485464 from=translated src=- shape=5d2b5c2f vocab=2e80886b
-/
lemma cnt_sum {n : ℕ} (a : Fin n → ℕ) :
    cnt a 0 + cnt a 1 + cnt a 2 = n := by
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (ZMod 3))) (f := res a) (fun i _ ↦ mem_univ _)
  rw [sum_univ_zmod3] at h
  rw [card_univ, Fintype.card_fin] at h
  exact h.symm

/-- The fiber of triples with prescribed residues is a product of fibers.
@isnad1 id=eq.0h3v.s7.b0f4f7c86d67 from=translated src=- shape=29ac4982 vocab=8d34b053
-/
lemma fiber_card {n : ℕ} (a : Fin n → ℕ) (u : Fin 3 → ZMod 3) :
    (univ.filter fun t : Fin 3 → Fin n ↦ ∀ j, res a (t j) = u j).card
      = ∏ j, cnt a (u j) := by
  have h : (univ.filter fun t : Fin 3 → Fin n ↦ ∀ j, res a (t j) = u j)
      = Fintype.piFinset fun j ↦ univ.filter fun i ↦ res a i = u j := by
    ext t
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  rfl

/-- The number of good triples, grouped by their residue pattern.
@isnad1 id=eq.0h2v.s8.5a095adfb680 from=translated src=- shape=7405b818 vocab=c9a690b0
-/
lemma good_card {n : ℕ} (a : Fin n → ℕ) :
    Fintype.card {t : Fin 3 → Fin n // 3 ∣ a (t 0) + a (t 1) + a (t 2)}
      = ∑ u ∈ patterns, ∏ j, cnt a (u j) := by
  have hmem : ∀ t ∈ univ.filter (fun t : Fin 3 → Fin n ↦ 3 ∣ a (t 0) + a (t 1) + a (t 2)),
      (fun j ↦ res a (t j)) ∈ patterns := by
    intro t ht
    have h0 : res a (t 0) + res a (t 1) + res a (t 2) = 0 := by
      show (a (t 0) : ZMod 3) + (a (t 1) : ZMod 3) + (a (t 2) : ZMod 3) = 0
      rw [← dvd_iff_res]
      simpa using ht
    simp [patterns, h0]
  rw [Fintype.card_subtype, card_eq_sum_card_fiberwise (t := patterns) hmem]
  apply sum_congr rfl
  intro u hu
  have hf : (univ.filter fun t : Fin 3 → Fin n ↦
        3 ∣ a (t 0) + a (t 1) + a (t 2)).filter (fun t ↦ (fun j ↦ res a (t j)) = u)
      = univ.filter fun t : Fin 3 → Fin n ↦ ∀ j, res a (t j) = u j := by
    ext t
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, heq⟩ j
      exact congrFun heq j
    · intro hall
      have hu0 : u 0 + u 1 + u 2 = 0 := by
        have := (mem_filter.mp hu).2
        simpa using this
      have hall' : ∀ j, (a (t j) : ZMod 3) = u j := hall
      refine ⟨?_, funext hall⟩
      rw [dvd_iff_res, hall' 0, hall' 1, hall' 2]
      exact hu0
  rw [hf, fiber_card]

/-- Summing over the good patterns by reindexing with the first two entries.
@isnad1 id=eq.0h1v.s8.9bc62ee0be05 from=translated src=- shape=68df9403 vocab=5cb5cc50
-/
lemma sum_over_patterns (F : (Fin 3 → ZMod 3) → ℕ) :
    ∑ u ∈ patterns, F u
      = ∑ p : ZMod 3 × ZMod 3, F ![p.1, p.2, -(p.1 + p.2)] := by
  apply sum_bij (fun u _ ↦ (u 0, u 1))
  · intro u _
    exact mem_univ _
  · intro u₁ h₁ u₂ h₂ heq
    funext j
    have e₁ : u₁ 0 + u₁ 1 + u₁ 2 = 0 := by
      have := (mem_filter.mp h₁).2
      simpa using this
    have e₂ : u₂ 0 + u₂ 1 + u₂ 2 = 0 := by
      have := (mem_filter.mp h₂).2
      simpa using this
    have f₁ : u₁ 0 = u₂ 0 := congrArg Prod.fst heq
    have f₂ : u₁ 1 = u₂ 1 := congrArg Prod.snd heq
    fin_cases j
    · exact f₁
    · exact f₂
    · have hsum : u₁ 0 + u₁ 1 + u₁ 2 = u₂ 0 + u₂ 1 + u₂ 2 := by rw [e₁, e₂]
      rw [f₁, f₂] at hsum
      exact add_left_cancel_iff.mp hsum
  · intro p _
    exact ⟨![p.1, p.2, -(p.1 + p.2)], by simp [patterns], by simp⟩
  · intro u hu
    have e : u 0 + u 1 + u 2 = 0 := by
      have := (mem_filter.mp hu).2
      simpa using this
    have hu' : u = ![u 0, u 1, -(u 0 + u 1)] := by
      funext j
      fin_cases j
      · rfl
      · rfl
      · show u (2 : Fin 3) = ![u 0, u 1, -(u 0 + u 1)] (2 : Fin 3)
        simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        linear_combination e
    exact congrArg F hu'

/-- The good triple count in terms of the residue counts.
@isnad1 id=eq.0h1v.s9.d26dba7dfc8c from=translated src=- shape=f69eb5f0 vocab=b5f85d98
-/
lemma pattern_sum (c : ZMod 3 → ℕ) :
    ∑ u ∈ patterns, ∏ j, c (u j)
      = c 0 ^ 3 + c 1 ^ 3 + c 2 ^ 3 + 6 * (c 0 * c 1 * c 2) := by
  rw [sum_over_patterns, Fintype.sum_prod_type]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [sum_univ_zmod3]
  simp only [sum_univ_zmod3]
  have h00 : (-((0 : ZMod 3) + 0)) = 0 := by decide
  have h01 : (-((0 : ZMod 3) + 1)) = 2 := by decide
  have h02 : (-((0 : ZMod 3) + 2)) = 1 := by decide
  have h10 : (-((1 : ZMod 3) + 0)) = 2 := by decide
  have h11 : (-((1 : ZMod 3) + 1)) = 1 := by decide
  have h12 : (-((1 : ZMod 3) + 2)) = 0 := by decide
  have h20 : (-((2 : ZMod 3) + 0)) = 1 := by decide
  have h21 : (-((2 : ZMod 3) + 1)) = 0 := by decide
  have h22 : (-((2 : ZMod 3) + 2)) = 2 := by decide
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  ring

/-- The key inequality in the case where `x` is a maximum of `x, y, z`.
@isnad1 id=le.5h3v.s7.6edba24f620d from=translated src=- shape=aa7f468b vocab=cef4cf1d
-/
lemma ineq_max {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyx : y ≤ x) (hzx : z ≤ x) :
    (x + y + z) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3 + z ^ 3 + 6 * (x * y * z)) := by
  have hs : 0 ≤ x + y + z := by positivity
  have h3 : (0 : ℝ) ≤ 3 * x - (x + y + z) := by linarith
  nlinarith [mul_nonneg hs (sq_nonneg (x - (x + y + z) / 2)),
    mul_nonneg (mul_nonneg hy hz) h3]

/-- The key inequality: `4 * (p³ + q³ + r³ + 6pqr) ≥ (p + q + r)³` for `p q r ≥ 0`.
@isnad1 id=le.3h3v.s7.d68d1b667886 from=translated src=- shape=b97f268c vocab=cef4cf1d
-/
lemma ineq3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3 + z ^ 3 + 6 * (x * y * z)) := by
  rcases le_total y x with hyx | hxy
  · rcases le_total z x with hzx | hxz
    · exact ineq_max hx hy hz hyx hzx
    · have h := ineq_max hz hy hx (by linarith) (by linarith)
      convert h using 1 <;> ring
  · rcases le_total z y with hzy | hyz
    · have h := ineq_max hy hx hz hxy hzy
      convert h using 1 <;> ring
    · have h := ineq_max hz hx hy (by linarith) (by linarith)
      convert h using 1 <;> ring

end Usa1979P3
