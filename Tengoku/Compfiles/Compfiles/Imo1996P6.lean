/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1996, Problem 6

Let p, q, n be three positive integers with p + q < n. Let (x₀, x₁, . . . , xₙ)
be an (n + 1)-tuple of integers satisfying the following conditions:
(a) x₀ = xₙ = 0.
(b) For each i with 1 ≤ i ≤ n, either xᵢ − xᵢ₋₁ = p or xᵢ − xᵢ₋₁ = −q.
Show that there exist indices i < j with (i, j) ≠ (0, n), such that xᵢ = xⱼ.

-/

namespace Imo1996P6

/--
@isnad1 id=lt.2h2v.s4.b4016418ead6 from=translated src=- shape=66342627 vocab=a5150267
-/
lemma one_lt_gcd_of_not_coprime {p q : ℕ} (h₁ : 0 < p) (h₂ : ¬Nat.Coprime p q) : 1 < p.gcd q :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(Nat.gcd_pos_of_pos_left q h₁).ne', by simp_all⟩

/--
@isnad1 id=lt.3h2v.s5.8d75583816ef from=translated src=- shape=bd33a14c vocab=19f4df30
-/
lemma dist_gt_one_of_ne_sign {p q : ℤ} (h₁ : p.sign ≠ q.sign) (h₂ : p ≠ 0) (h₃ : q ≠ 0) : 1 < |p - q| := by
  grind

/--
@isnad1 id=and.1h2v.s5.f8586fb3cd65 from=translated src=- shape=f2b004a2 vocab=0f374885
-/
lemma diff_ne_pm_one_of_dist_gt_one {p q : ℤ} (h : 1 < |p - q|) : p - q ≠ 1 ∧ p - q ≠ -1 := by
  grind

/--
@isnad1 id=and.2h3v.s5.168c5c596085 from=translated src=- shape=5418afeb vocab=ea85cceb
-/
lemma ne_zero_of_eq_mul {a b c : ℤ} (h₁ : a ≠ 0) (h₂ : a = b * c) : b ≠ 0 ∧ c ≠ 0 := by
  grind

/--
@isnad1 id=ex.1h4v.s6.fdb5ded6da80 from=translated src=- shape=7e5c92db vocab=eb663e7b
-/
lemma sum_bivalued {p q : ℤ} (s : Finset (ℕ)) (f : ℕ → ℤ) (h : ∀ i ∈ s, f i = p ∨ f i = q) :
  ∃ r : ℕ, ∑ i ∈ s, f i = r * p + (s.card - r) * q ∧ r ≤ s.card := by
  let s₂ := s.filter (fun i ↦ f i = p)
  let r := s₂.card
  use r
  have h_sum_split : ∑ i ∈ s, f i = ∑ i ∈ s₂, f i + ∑ i ∈ (s \ s₂), f i := by
    rw [← Finset.sum_disjUnion (Finset.disjoint_sdiff)]
    have : s₂.disjUnion (s \ s₂) (Finset.disjoint_sdiff) = s := by grind
    rw [this]
  have h_s₂ : ∀ i ∈ s₂, f i = p := by grind
  have h_s_s₂ : ∀ i ∈ (s \ s₂), f i = q := by grind
  rw [Finset.sum_congr rfl h_s₂, Finset.sum_congr rfl h_s_s₂, Finset.sum_const, Finset.sum_const] at h_sum_split
  grind

end Imo1996P6
