/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.DeadEnds.CRT
import Tengoku.LeanPool.LeanPool.DeadEnds.CountingBlocks
public import Tengoku

/-!
Finite-prime counting bounds and comparison with the Euler product density.
-/

@[expose] public section

namespace LeanPool.DeadEnds

lemma count_upper_bound (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    count ≤ (X / M + 1) * A.card := by
  intro M A count
  have hdecomp := count_eq_sum_blocks b T S X
  simp only at hdecomp
  rw [show count = _ from hdecomp]
  have hblock : ∀ k, ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card :=
    fun k => completeBlock_valid_count b T S k
  have hsum : ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card =
      (X / M) * A.card := by
    simp_all
  rw [hsum]
  linarith [partialBlock_valid_count_le b T S X]

lemma count_bounds (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (X / M) * A.card ≤ count ∧ count ≤ (X / M + 1) * A.card := by
  constructor
  · exact count_lower_bound b T S X
  · exact count_upper_bound b T S X

/-- Helper: localDensityProduct is non-negative (product of non-negative factors). -/
lemma localDensityProduct_nonneg (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    0 ≤ localDensityProduct b T S := by
  rw [localDensityProduct]
  exact Finset.prod_nonneg fun p _ => localDensityFactor_nonneg _ b T

lemma interval_bound {a b lo hi d : ℝ}
    (ha_lo : lo ≤ a) (ha_hi : a ≤ hi) (hb_lo : lo ≤ b) (hb_hi : b ≤ hi)
    (hd : hi - lo ≤ d) : |a - b| ≤ d := by
  rw [abs_le]
  constructor <;> linarith

lemma floor_div_bounds (X M : ℕ) (hM : 0 < M) :
    (X / M) * M ≤ X ∧ X < (X / M + 1) * M :=
  ⟨Nat.div_mul_le_self X M, by
    have h1 : X % M < M := Nat.mod_lt X hM
    have h2 : M * (X / M) + X % M = X := Nat.div_add_mod X M
    nlinarith⟩

/-- Helper: From count_bounds + validResidues_card_eq_mul, get the real-valued bounds. -/
lemma count_real_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let q := X / M
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (q : ℝ) * M * L ≤ count ∧ (count : ℝ) ≤ (q + 1) * M * L := by
  intro M L q count
  have hbounds := count_bounds b T S X
  simp only at hbounds
  have hA := validResidues_card_eq_mul b hb T hT S
  have hA' : (M : ℝ) * L = (validResiduesMod b T S).card := by
    simp only [hA]
    ring
  constructor
  · calc (q : ℝ) * M * L = q * (M * L) := by ring
      _ = q * (validResiduesMod b T S).card := by rw [← hA']
      _ ≤ count := by exact_mod_cast hbounds.1
  · calc (count : ℝ) ≤ (q + 1) * (validResiduesMod b T S).card := by exact_mod_cast hbounds.2
      _ = (q + 1) * M * L := by
        rw [← hA']
        ring

lemma xL_real_bounds (X M : ℕ) (L : ℝ) (hL : 0 ≤ L) (hM : 0 < M) :
    let q := X / M
    (q : ℝ) * M * L ≤ (X : ℝ) * L ∧ (X : ℝ) * L ≤ (q + 1) * M * L := by
  intro q
  have hfloor := floor_div_bounds X M hM
  have hqM_real : (q : ℝ) * M ≤ (X : ℝ) := by exact_mod_cast (by simpa [q] using hfloor.1)
  have hXle_real : (X : ℝ) ≤ (q + 1 : ℝ) * M := by
    exact_mod_cast (by simpa [q] using Nat.le_of_lt hfloor.2)
  exact ⟨by nlinarith, by nlinarith⟩

lemma final_error_bound {count X M : ℕ} {L : ℝ} {q : ℕ}
    (hcount_lo : (q : ℝ) * M * L ≤ count)
    (hcount_hi : (count : ℝ) ≤ (q + 1) * M * L)
    (hxL_lo : (q : ℝ) * M * L ≤ (X : ℝ) * L)
    (hxL_hi : (X : ℝ) * L ≤ (q + 1) * M * L)
    (_hL_nonneg : 0 ≤ L)
    (hL_le_one : L ≤ 1) :
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) :=
  abs_le.mpr ⟨by nlinarith, by nlinarith⟩

lemma error_bound_empty_case (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (hM : primeSquareProduct S = 0) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  exact (Nat.ne_of_gt (primeSquareProduct_pos S) hM).elim

/-- Finite-prime counts differ from the expected local-density main term by at most the modulus. -/
lemma error_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  intro M L count
  have hcount := count_real_bounds b hb T hT S X
  have hL_nonneg := localDensityProduct_nonneg b T S
  have hL_le_one := localDensityProduct_le_one b T S
  by_cases hM : M = 0
  · exact error_bound_empty_case b hb T hT S X hM
  · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have hxL := xL_real_bounds X M L hL_nonneg hM_pos
    exact final_error_bound hcount.1 hcount.2 hxL.1 hxL.2 hL_nonneg hL_le_one

lemma count_finite_prime_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    |(((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) -
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T| ≤
      (∏ p ∈ S, (p : ℕ) ^ 2 : ℝ) := by
  have h := error_bound b hb T hT S X
  simp only [primeSquareProduct, localDensityProduct] at h
  simp_all

lemma hasProd_implies_finite_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset Nat.Primes, ∀ S : Finset Nat.Primes, A ⊆ S →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  have h_multi := jointSquarefreeDensity_multipliable b hb T hT
  have h_hasProd := Multipliable.hasProd h_multi
  rw [HasProd.eq_1] at h_hasProd
  simp only [SummationFilter.unconditional_filter] at h_hasProd
  rw [Metric.tendsto_nhds] at h_hasProd
  specialize h_hasProd ε hε
  rw [Filter.eventually_atTop] at h_hasProd
  obtain ⟨A, hA⟩ := h_hasProd
  use A
  intro S hAS
  specialize hA S hAS
  rwa [Real.dist_eq] at hA

/-- For any ε > 0, the tail contribution from primes p > y to the joint density
    (measuring how much the finite product differs from the infinite product)
    can be made arbitrarily small by choosing y large enough.
    Uses jointSquarefreeDensity_multipliable to ensure convergence. -/
lemma finite_product_converges_to_density (b : ℕ) (hb : 2 ≤ b)
    (T : Finset ℕ) (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  obtain ⟨A, hA⟩ := hasProd_implies_finite_approx b hb T hT ε hε
  use A.image (fun p : Nat.Primes => (p : ℕ)) |>.sup id
  intro S hS
  apply hA S
  intro p hp
  apply hS p
  calc (p : ℕ) = id (p : ℕ) := rfl
    _ ≤ (A.image (fun q : Nat.Primes => (q : ℕ))).sup id :=
        Finset.le_sup (Finset.mem_image_of_mem _ hp)

/-- Upper bound: For any S, C(X) ≤ #{N ≤ X : N satisfies S-conditions} since C(X)
    imposes more constraints. Combined with count_finite_prime_approx, this gives
    limsup C(X)/X ≤ D(b,T). -/
lemma count_upper_bound_via_finite (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≤
      ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card := by
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  obtain ⟨hNIcc, hSqN, hSqAll⟩ := hN
  refine ⟨hNIcc, fun p _ => ?_⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hSqN
  exact ⟨by rw [sq]; exact hSqN p p.prop,
    fun d hd => by simp only [Nat.squarefree_iff_prime_squarefree] at hSqAll
                   rw [sq]; exact (hSqAll d hd) p p.prop⟩

/-- The number of `N ∈ [1, X]` such that for every `p ∈ S` we have `p² ∤ N` and `p² ∤ b * N + d`
for all `d ∈ T` (i.e. the square-free conditions checked only at the primes in `S`). -/
noncomputable def countFinitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun N =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card

/-- The primes `p ≤ n`, packaged as a `Finset Nat.Primes`. -/
def primesUpTo (n : ℕ) : Finset Nat.Primes :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).subtype Nat.Prime |>.image (fun ⟨p, hp⟩ => ⟨p,
      hp⟩)

lemma mem_primesUpTo (n : ℕ) (p : Nat.Primes) :
    (p : ℕ) ≤ n → p ∈ primesUpTo n := by
  intro hpn
  rw [primesUpTo, Finset.mem_image]
  refine ⟨⟨(p : ℕ), p.prop⟩, ?_, rfl⟩
  rw [Finset.mem_subtype, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hpn, p.prop⟩

lemma jointSquarefree_subset_finitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) := by
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  obtain ⟨hNIcc, hSqN, hSqAll⟩ := hN
  refine ⟨hNIcc, fun p _ => ?_⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hSqN
  exact ⟨by rw [sq]; exact hSqN p p.prop,
    fun d hd => by simp only [Nat.squarefree_iff_prime_squarefree] at hSqAll
                   rw [sq]; exact (hSqAll d hd) p p.prop⟩

lemma not_squarefree_has_prime_sq_divisor (n : ℕ) (h : ¬Squarefree n) :
    ∃ p : Nat.Primes, (p : ℕ) ^ 2 ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hp'⟩ := h
  exact ⟨⟨p, hp⟩, by simpa [pow_two] using hp'⟩

lemma sdiff_subset_violations (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) \
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
        q : ℕ) ^ 2 ∣ b * N + d)) := by
  intro N hN
  rw [Finset.mem_sdiff] at hN
  rw [Finset.mem_filter] at hN ⊢
  obtain ⟨⟨hNIcc, hNS⟩, hNotG⟩ := hN
  refine ⟨hNIcc, ?_⟩
  simp only [Finset.mem_filter, not_and] at hNotG
  specialize hNotG hNIcc
  by_cases hSqN : Squarefree N
  · have hNotAll := hNotG hSqN
    push Not at hNotAll
    obtain ⟨d, hd_mem, hd_not_sq⟩ := hNotAll
    obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor (b * N + d) hd_not_sq
    refine ⟨q, ?_, Or.inr ⟨d, hd_mem, hq_dvd⟩⟩
    intro hqS
    simp_all
  · obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor N hSqN
    refine ⟨q, ?_, Or.inl hq_dvd⟩
    intro hqS
    simp_all

lemma count_ge_finite_minus_violations (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ)
    (_hT : T ⊆ Finset.range b) (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≥ (countFinitePrime b T S X : ℝ) -
      ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card := by
  let A := (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d))
  let B := (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣
      b * N + d))
  let V := (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
      q : ℕ) ^ 2 ∣ b * N + d))
  change (A.card : ℝ) ≥ (B.card : ℝ) - (V.card : ℝ)
  have hAB : A ⊆ B := jointSquarefree_subset_finitePrime b T S X
  have hDiffCard : (B \ A).card ≤ V.card := Finset.card_le_card (sdiff_subset_violations b T S X)
  have hCard : (B \ A).card + A.card = B.card := Finset.card_sdiff_add_card_eq_card hAB
  have h2 : (A.card : ℤ) ≥ (B.card : ℤ) - (V.card : ℤ) := by omega
  exact_mod_cast h2

end LeanPool.DeadEnds
