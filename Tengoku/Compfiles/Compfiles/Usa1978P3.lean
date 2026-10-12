/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1978, Problem 3

You are told that all integers from 33 to 73 inclusive can be expressed as a sum
of positive integers whose reciprocals sum to 1. Show that the same is true for
all integers greater than 73.
-/

namespace Usa1978P3

/-- A natural number `n` is *expressible* if it can be written as a sum of
positive integers whose reciprocals sum to `1`. -/
def Expressible (n : ℕ) : Prop :=
  ∃ l : List ℕ, (∀ a ∈ l, 0 < a) ∧ l.sum = n ∧ (l.map fun a : ℕ => (a : ℚ)⁻¹).sum = 1

/--
@isnad1 id=eq.0h1v.s5.ddf97256cf46 from=translated src=- shape=ebc6a0b8 vocab=3a8da64c
-/
lemma sum_map_two_mul (l : List ℕ) : (l.map (2 * ·)).sum = 2 * l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/--
@isnad1 id=eq.0h1v.s6.c44051ab73bd from=translated src=- shape=2d420fe2 vocab=be9b8bc2
-/
lemma recip_sum_map_two_mul (l : List ℕ) :
    ((l.map (2 * ·)).map fun a : ℕ => (a : ℚ)⁻¹).sum
      = (2 : ℚ)⁻¹ * (l.map fun a : ℕ => (a : ℚ)⁻¹).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev]
    ring

/-- The key construction: given a representation of `n`, doubling every summand
halves the sum of the reciprocals, so adjoining two more positive summands
`c, d` whose reciprocals sum to `1 / 2` yields a representation of
`2 * n + (c + d)`.
@isnad1 id=expressi.4h3v.s6.46903399fc6a from=translated src=- shape=beeade34 vocab=a82d31db
-/
lemma expressible_two_mul_add {n : ℕ} (h : Expressible n) {c d : ℕ}
    (hc : 0 < c) (hd : 0 < d) (hcd : (c : ℚ)⁻¹ + (d : ℚ)⁻¹ = 1 / 2) :
    Expressible (2 * n + (c + d)) := by
  obtain ⟨l, hpos, hsum, hrec⟩ := h
  refine ⟨l.map (2 * ·) ++ [c, d], ?_, ?_, ?_⟩
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · rw [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hbpos : 0 < b := hpos b hb
      positivity
    · simp at ha
      rcases ha with rfl | rfl
      · exact hc
      · exact hd
  · rw [List.sum_append, sum_map_two_mul, hsum]
    simp only [List.sum_cons, List.sum_nil, add_zero]
  · rw [List.map_append, List.sum_append, recip_sum_map_two_mul, hrec]
    have hcd' : ([c, d].map fun a : ℕ => (a : ℚ)⁻¹).sum = (c : ℚ)⁻¹ + (d : ℚ)⁻¹ := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hcd', hcd]
    norm_num

/-- Adjoining two `4`s: if `n` is expressible, so is `2 * n + 8`.
@isnad1 id=expressi.1h1v.s4.0a334ac9b634 from=translated src=- shape=c2e0b24d vocab=96ff2f22
-/
lemma expressible_two_mul_add_eight {n : ℕ} (h : Expressible n) :
    Expressible (2 * n + 8) :=
  expressible_two_mul_add (c := 4) (d := 4) h (by norm_num) (by norm_num) (by norm_num)

/-- Adjoining `3` and `6`: if `n` is expressible, so is `2 * n + 9`.
@isnad1 id=expressi.1h1v.s4.8212989c2503 from=translated src=- shape=c2e0b24d vocab=96ff2f22
-/
lemma expressible_two_mul_add_nine {n : ℕ} (h : Expressible n) :
    Expressible (2 * n + 9) :=
  expressible_two_mul_add (c := 3) (d := 6) h (by norm_num) (by norm_num) (by norm_num)

end Usa1978P3
