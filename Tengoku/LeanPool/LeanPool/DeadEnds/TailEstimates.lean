/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.DeadEnds.Basic
import Tengoku.LeanPool.LeanPool.DeadEnds.Counting
import Tengoku.LeanPool.LeanPool.DeadEnds.PrimeTail
import Tengoku.LeanPool.LeanPool.DeadEnds.RelevantPrimes
public import Tengoku

/-!
Asymptotic tail estimates that turn finite-prime counts into density bounds.
-/

@[expose] public section

namespace LeanPool.DeadEnds

lemma sqrt_bXb_div_X_small (b : ℕ) (_hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (2 * (b : ℝ) / ε ^ 2)
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  have h₅ : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hX
  have h₆ : (X₀ : ℝ) ≤ (X : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hX
  have hX₀' : (X₀ : ℝ) > 2 * (b : ℝ) / ε ^ 2 := hX₀
  have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
  have h₈ : ε ^ 2 * (X : ℝ) > 2 * (b : ℝ) := by rw [gt_iff_lt, ← div_lt_iff₀' hεsq]; linarith
  have h₁₀ : (b : ℝ) * X + b < ε ^ 2 * (X : ℝ) ^ 2 := by nlinarith [sq_nonneg ((X : ℝ) - 1)]
  have hsq : ((Nat.sqrt (b * X + b) : ℝ)) * (Nat.sqrt (b * X + b) : ℝ) ≤ (b : ℝ) * X + b := by
    exact_mod_cast Nat.sqrt_le (b * X + b)
  have h₁₁ : (Nat.sqrt (b * X + b) : ℝ) < ε * X := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt (b * X + b)),
      mul_pos hε (lt_of_lt_of_le one_pos h₅)]
  calc (Nat.sqrt (b * X + b) : ℝ) / X < (ε * X) / X := by gcongr
    _ = ε := by field_simp

lemma combine_violation_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b)
    (X : ℕ) (hX : 0 < X)
    (ε : ℝ) (_hε : 0 < ε)
    (htail : (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2)
    (hsqrt : (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2) :
    (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
          d)).card : ℝ) / X < ε := by
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  have hbound := violation_count_bound b hb T hT S y hy hyb X
  calc (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) / X
      ≤ ((T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
         (T.card + 1 : ℝ) * (Nat.sqrt (b * X + b) : ℝ)) / X := by
        apply div_le_div_of_nonneg_right hbound (le_of_lt hX_pos)
    _ = (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
        (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) := by
        have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX_pos
        field_simp [hXne]
    _ < ε / 2 + ε / 2 := add_lt_add htail hsqrt
    _ = ε := add_halves ε

lemma tail_sum_antitone (y y' : ℕ) (h : y ≤ y') :
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y'}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 ≤
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 := by
  let e : {q : Nat.Primes // (q : ℕ) > y'} → {q : Nat.Primes // (q : ℕ) > y} :=
    fun ⟨q, hq⟩ => ⟨q, lt_of_le_of_lt h hq⟩
  apply Summable.tsum_le_tsum_of_inj e
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have : a = b := by
      have := congrArg Subtype.val hab
      exact this
    exact Subtype.ext this
  · intro c _
    positivity
  · intro i
    rfl
  · exact primes_summable_one_div_sq.subtype _
  · exact primes_summable_one_div_sq.subtype _

/-- Choose y large enough that the tail sum is small enough, and y ≥ b.
    Uses prime_tail_sum_small with ε/(2*(|T|+1)). -/
lemma choose_y_for_tail (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, y ≥ b ∧
      (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2 := by
  have hK : (0 : ℝ) < T.card + 1 := by positivity
  have hε' : 0 < ε / (2 * (T.card + 1)) := by positivity
  obtain ⟨y₁, hy₁⟩ := prime_tail_sum_small (ε / (2 * (T.card + 1))) hε'
  use max b y₁
  constructor
  · exact le_max_left b y₁
  · calc (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > max b y₁}), 1 / (
      ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      ≤ (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y₁}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · exact tail_sum_antitone y₁ (max b y₁) (le_max_right b y₁)
          · linarith
    _ < (T.card + 1 : ℝ) * (ε / (2 * (T.card + 1))) := by apply mul_lt_mul_of_pos_left hy₁ hK
    _ = ε / 2 := by field_simp

/-- Choose X₀ large enough that the √(bX+b)/X term is small and X₀ > 0. -/
lemma choose_X_for_sqrt (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 0 < X₀ ∧ ∀ X ≥ X₀,
      (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2 := by
  have hc : (0 : ℝ) < T.card + 1 := by positivity
  set ε' := ε / (2 * (T.card + 1)) with hε'_def
  have hε' : 0 < ε' := by positivity
  obtain ⟨X₀', hX₀'⟩ := sqrt_bXb_div_X_small b hb ε' hε'
  use max X₀' 1
  constructor
  · omega
  · intro X hX
    have hXge : X ≥ X₀' := le_trans (le_max_left _ _) hX
    have hbound := hX₀' X hXge
    calc (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X)
        < (T.card + 1) * ε' := by nlinarith [hbound]
      _ = (T.card + 1) * (ε / (2 * (T.card + 1))) := by rfl
      _ = ε / 2 := by field_simp

/-- The "violation count" (N failing for primes outside S) divided by X vanishes
    as S grows and X gets large. -/
lemma error_term_vanishes (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∃ X₁ : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      ∀ X ≥ X₁,
        (((Finset.Icc 1 X).filter fun N =>
          ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
              d)).card : ℝ) / X < ε := by
  obtain ⟨y, hyb, htail⟩ := choose_y_for_tail b hb T ε hε
  obtain ⟨X₀, hX₀_pos, hsqrt⟩ := choose_X_for_sqrt b hb T ε hε
  use y, X₀
  intro S hS X hX
  have hX_pos : 0 < X := Nat.lt_of_lt_of_le hX₀_pos hX
  exact combine_violation_bounds b hb T _hT S y hS hyb X hX_pos ε hε htail (hsqrt X hX)

lemma exists_large_for_ratio (M : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (M : ℝ) / X < δ := by
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (max ((M : ℝ) / δ) 1)
  refine ⟨X₀, fun X hX => ?_⟩
  have h₃ : (X₀ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hmax := lt_of_le_of_lt (le_max_left _ _) hX₀
  have hone := lt_of_le_of_lt (le_max_right _ _) hX₀
  have h₅ : 0 < (X : ℝ) := by linarith
  rw [div_lt_iff₀ h₅]
  have : (M : ℝ) < X₀ * δ := by rw [div_lt_iff₀ hδ] at hmax; linarith
  nlinarith

lemma finite_prod_lt_density_add (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (ε : ℝ) (_hε : 0 < ε)
    (h : |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε) :
    ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε := by
  linarith [(abs_lt.mp h).2]

lemma combine_upper_bounds (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (ε : ℝ) (_hε : 0 < ε) (hX : 0 < X)
    (M : ℕ) (_hM : M = ∏ p ∈ S, (p : ℕ) ^ 2)
    (hcount : (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M)
    (hprod : ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε / 2)
    (hratio : (M : ℝ) / X < ε / 2) :
    (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
  have h₁ : 0 < (X : ℝ) := by exact_mod_cast hX
  have heq : ((X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M) / X =
      (∏ p ∈ S, localDensityFactor (p : ℕ) b T) + (M : ℝ) / X := by field_simp [h₁.ne']
  have h_div : (countJointSquarefree b T X : ℝ) / X ≤
      (∏ p ∈ S, localDensityFactor (p : ℕ) b T) + (M : ℝ) / X := by
    rw [← heq]; gcongr
  linarith

lemma exists_finite_prime_set (y : ℕ) :
    ∃ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) := by
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ y}.Finite :=
    Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) (Set.finite_Iic y)
  refine ⟨hfin.toFinset, fun p hp => ?_⟩
  rwa [Set.Finite.mem_toFinset]

end LeanPool.DeadEnds
