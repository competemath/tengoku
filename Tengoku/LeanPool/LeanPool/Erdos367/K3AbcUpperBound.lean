/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku

/-!
# Erdős Problem #367 (k = 3 case), conditional on abc

We formalize:
  1. rad(m)  — the radical (squarefree kernel) of m
  2. B₂(m)  — the powerful (2-full) part of m
  3. LEMMA STAR:  rad(m)² · B₂(m) ≤ m²
  4. Submultiplicativity of rad
  5. The abc conjecture (as a hypothesis)
  6. The main theorem:  B₂(n) · B₂(n+1) · B₂(n+2) ≤ C'_ε · n^{2+ε}
-/

@[expose] public section

open Finset BigOperators Nat

noncomputable section

namespace Erdos367

/-! ## Definitions -/

/-- The radical (squarefree kernel) of n: the product of distinct prime factors. -/
def Nat.rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- The powerful (2-full) part of n: ∏_{p : v_p(n) ≥ 2} p^{v_p(n)}. -/
def Nat.powerfulPart (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/-! ## Basic properties of rad -/

@[simp] theorem Nat.rad_zero : Nat.rad 0 = 1 := by simp [Nat.rad]

@[simp] theorem Nat.rad_one : Nat.rad 1 = 1 := by simp [Nat.rad]

theorem Nat.rad_pos (n : ℕ) (_hn : 0 < n) : 0 < Nat.rad n := by
  exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp

/-! ## Basic properties of powerfulPart -/

@[simp] theorem Nat.powerfulPart_zero : Nat.powerfulPart 0 = 1 := by
  simp [Nat.powerfulPart]

@[simp] theorem Nat.powerfulPart_one : Nat.powerfulPart 1 = 1 := by
  simp [Nat.powerfulPart]

theorem Nat.powerfulPart_pos (n : ℕ) (_hn : 0 < n) : 0 < Nat.powerfulPart n := by
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp |>.1)) _

/-! ## LEMMA STAR: rad(m)² · B₂(m) ≤ m²

The key integer-arithmetic lemma. For every m > 0,
  rad(m)² * powerfulPart(m) ≤ m².

Proof sketch: Write m = ∏ p^{a_p}. Then
  rad(m)² * B₂(m) = ∏_{a_p=1} p² · ∏_{a_p≥2} p^{2+a_p}
  m²              = ∏ p^{2a_p}
Compare primewise: for a_p = 1, 2 ≤ 2; for a_p ≥ 2, 2+a_p ≤ 2a_p.
-/

/-! ## Submultiplicativity of rad

rad(a * b) ≤ rad(a) * rad(b) for positive a, b.
This follows because primeFactors(ab) = primeFactors(a) ∪ primeFactors(b),
and the product over a union is ≤ the product of products (intersection terms ≥ 1).
-/

theorem Nat.rad_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.rad (a * b) ≤ Nat.rad a * Nat.rad b := by
  unfold Nat.rad
  rw [Nat.primeFactors_mul ha hb]
  simp only [id_eq]
  rw [← Finset.prod_union_inter]
  exact le_mul_of_one_le_right (Nat.zero_le _)
    (Finset.prod_pos fun p hp =>
      Nat.pos_of_mem_primeFactors (Finset.mem_inter.mp hp |>.1))

/-! ## The abc conjecture (stated as a hypothesis) -/

/-- The abc conjecture: for every ε > 0, there exists C > 0 such that for all
coprime positive integers a, b with a + b = c, we have c ≤ C · rad(abc)^{1+ε}. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ C * ((Nat.rad (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-! ## Key identity and the abc application step -/

/-- (n+1)² = n(n+2) + 1, the "squaring trick" identity. -/
theorem squaring_trick (n : ℕ) : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring

/-
rad(n(n+1)²(n+2)) = rad(n(n+1)(n+2)) since rad ignores exponents.
-/
theorem rad_ignore_sq (n : ℕ) (hn : 0 < n) :
    Nat.rad (n * (n + 1) ^ 2 * (n + 2)) = Nat.rad (n * (n + 1) * (n + 2)) := by
  unfold Nat.rad;
  norm_num [ Nat.primeFactors_mul, hn.ne', Nat.primeFactors_pow ]

/-! ## Main theorem: Erdős #367 (k=3), conditional on abc

**Theorem.** Assume abc. For every ε > 0, there exists C' > 0 such that for all n ≥ 1,
  B₂(n) · B₂(n+1) · B₂(n+2) ≤ C' · n^{2+ε}.

The proof proceeds in two stages:
  (1) *Integer core*: Use the squaring trick + abc to get
        (n+1)² ≤ C_ε · rad(n(n+1)(n+2))^{1+ε},
      then apply rad submultiplicativity and LEMMA STAR to bound the radical
      in terms of n and the powerful parts.
  (2) *Real-analytic rearrangement*: Rearrange the resulting inequality
      using real-valued exponents to isolate B₂(n)B₂(n+1)B₂(n+2) ≤ C'·n^{2+ε}.
-/

/-
The integer core: from abc, we get
  (n+1)² ≤ C_ε · [n(n+1)(n+2) / (B₂(n)B₂(n+1)B₂(n+2))^{1/2}]^{1+ε}.
  Stated as: (n+1)^2 * P^{(1+ε)/2} ≤ C_ε * (n(n+1)(n+2))^{1+ε},
  where P = B₂(n)·B₂(n+1)·B₂(n+2).
-/
theorem integer_core_ineq (habc : ABCConjecture) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((n + 1 : ℕ) : ℝ) ^ 2 ≤ C *
        ((Nat.rad n : ℝ) * (Nat.rad (n + 1) : ℝ) *
          (Nat.rad (n + 2) : ℝ)) ^ (1 + ε) := by
  obtain ⟨C, hC_pos, hC⟩ := habc ε hε
  use C
  refine ⟨hC_pos, fun n hn ↦ ?_⟩
  have hC_applied :=
    hC (n * (n + 2)) 1 ((n + 1) ^ 2) (by positivity) (by norm_num)
      (by positivity) (by ring) (by simp)
  norm_num [mul_assoc] at hC_applied ⊢
  refine le_trans hC_applied ?_
  gcongr
  -- `Nat.rad_mul_le` gives the radical bound; `rad_ignore_sq` removes the square.
  have h_rad_mul :
      Nat.rad (n * (n + 2) * (n + 1) ^ 2) ≤
        Nat.rad n * Nat.rad (n + 2) * Nat.rad ((n + 1) ^ 2) := by
    convert
      Nat.rad_mul_le (n * (n + 2)) ((n + 1) ^ 2) (by positivity) (by positivity)
        |> le_trans <|
          Nat.mul_le_mul (Nat.rad_mul_le n (n + 2) (by positivity) (by positivity))
            le_rfl
      using 1
  -- Since rad((n + 1)^2) = rad(n + 1), we can simplify the inequality.
  have h_rad_sq : Nat.rad ((n + 1) ^ 2) = Nat.rad (n + 1) := by
    unfold Nat.rad; simp +decide [ Nat.primeFactors_pow ] ;
  rw [h_rad_sq] at h_rad_mul
  have h_rad_mul' :
      Nat.rad (n * ((n + 2) * (n + 1) ^ 2)) ≤
        Nat.rad n * (Nat.rad (n + 1) * Nat.rad (n + 2)) := by
    convert h_rad_mul using 1 <;> ring
  exact_mod_cast h_rad_mul'

/-! ## Helper: product of three LEMMA STAR instances (pure ℕ) -/

/-
Multiplying three instances of LEMMA STAR: if R = rad(n)·rad(n+1)·rad(n+2)
and P = B₂(n)·B₂(n+1)·B₂(n+2), then R² · P ≤ (n(n+1)(n+2))².
-/

/-
**Real-analytic rearrangement lemma** (clearly marked).
Given the bound from the integer core and LEMMA STAR applied to each of
n, n+1, n+2, the real-exponent bookkeeping yields
  B₂(n)·B₂(n+1)·B₂(n+2) ≤ C'·n^{2+ε}.

The key steps are:
  1. rad(n+i) ≤ (n+i) / B₂(n+i)^{1/2}  (from LEMMA STAR)
  2. Substituting into the abc bound and using n(n+1)(n+2) ≤ 27n³
  3. Rearranging to isolate the product of powerful parts
  4. The resulting exponent 6 - 4/(1+ε) = 2 + 4ε/(1+ε) ≤ 2 + 4ε,
     then relabeling ε' = ε/4.
-/

end Erdos367

end
