/-
Copyright (c) 2026 Bhavik Mehta, Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk
-/
module

public import Tengoku

import Tengoku.LeanPool.LeanPool.ABCExceptions.ForMathlib.RingTheory.Radical

/-!
# LeanPool.ABCExceptions.Section2
-/

@[expose] public section

open Finset UniqueFactorizationMonoid

section

/--
The set (as a `Finset`) of exceptions to the abc conjecture at `ε` inside [1, X] ^ 3, in particular
the set of triples `(a, b, c)` which are
* pairwise coprime,
* contained in `[1, X] ^ 3`,
* satisfy `a + b = c`,
* have `radical (a * b * c) < c ^ (1 - ε)`

Note this has a slight difference from the usual formulation, which has
`radical (a * b * c) ^ (1 + ε) < c` instead.
-/
noncomputable def Finset.abcExceptionsBelow (ε : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (1, 1, 1) (X, X, X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ (1 - ε) : ℝ)

@[simp]
theorem Finset.mem_abcExceptionsBelow (ε : ℝ) (X : ℕ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ abcExceptionsBelow ε X ↔
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) < (c ^ (1 - ε) : ℝ) ∧
      (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) := by
  simp [abcExceptionsBelow]
  tauto

@[gcongr]
lemma Finset.abcExceptionsBelow_mono_right {ε : ℝ} {X Y : ℕ} (hXY : X ≤ Y) :
    abcExceptionsBelow ε X ⊆ abcExceptionsBelow ε Y := by
  exact Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc le_rfl ⟨hXY, hXY, hXY⟩)

@[gcongr]
lemma Finset.abcExceptionsBelow_mono_left {ε₁ ε₂ : ℝ} {X : ℕ} (hε : ε₁ ≤ ε₂) :
    abcExceptionsBelow ε₂ X ⊆ abcExceptionsBelow ε₁ X := by
  rintro ⟨a, b, c⟩
  simp +contextual only [mem_abcExceptionsBelow, Nat.Coprime, Set.mem_Icc, Prod.mk_le_mk, and_self,
    and_true, true_and, and_imp]
  rintro - - - - h - - hc - - -
  refine h.trans_le ?_
  gcongr
  simpa

@[gcongr]
lemma Finset.abcExceptionsBelow_mono {ε₁ ε₂ : ℝ} {X Y : ℕ} (hε : ε₁ ≤ ε₂) (hXY : X ≤ Y) :
    abcExceptionsBelow ε₂ X ⊆ abcExceptionsBelow ε₁ Y :=
  (abcExceptionsBelow_mono_right hXY).trans (abcExceptionsBelow_mono_left hε)

/--
The number of exceptions to the abc conjecture for a given `ε` which are bounded by `X`.
-/
noncomputable def countTriples (ε : ℝ) (X : ℕ) : ℕ := #(abcExceptionsBelow ε X)

@[gcongr]
lemma countTriples_mono {ε₁ ε₂ : ℝ} {X Y : ℕ} (hε : ε₁ ≤ ε₂) (hXY : X ≤ Y) :
    countTriples ε₂ X ≤ countTriples ε₁ Y := by
  simp only [countTriples]; gcongr

@[gcongr]
lemma countTriples_mono_left {ε : ℝ} {X Y : ℕ} (hXY : X ≤ Y) :
    countTriples ε X ≤ countTriples ε Y := by
  simp only [countTriples]; gcongr

@[gcongr]
lemma countTriples_mono_right {ε₁ ε₂ : ℝ} {X : ℕ} (hε : ε₁ ≤ ε₂) :
    countTriples ε₂ X ≤ countTriples ε₁ X := by
  simp only [countTriples]; gcongr

/--
The set of exceptions to the abc conjecture for `ε`, in particular
the set of triples `(a, b, c)` which are
* pairwise coprime,
* positive,
* satisfy `a + b = c`,
* have `radical (a * b * c) ^ (1 + ε) < c`
-/
def abcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) : ℕ × ℕ × ℕ |
    0 < a ∧ 0 < b ∧ 0 < c ∧
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) ^ (1 + ε) < (c : ℝ) }

@[simp]
theorem mem_abcExceptions (ε : ℝ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ abcExceptions ε ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) ^ (1 + ε) < (c : ℝ) := Iff.rfl

@[gcongr]
lemma abcExceptions_mono {ε₁ ε₂ : ℝ} (hε : ε₂ ≤ ε₁) :
    abcExceptions ε₁ ⊆ abcExceptions ε₂ := by
  rintro ⟨a, b, c⟩
  simp +contextual only [mem_abcExceptions, and_imp, true_and, Nat.Coprime]
  rintro ha hb hc - - - - habc
  refine habc.trans_le' ?_
  gcongr
  simp [Nat.one_le_cast, Nat.add_one_le_iff, Nat.radical_pos]

lemma abcExceptions_subset_Ici_one (ε : ℝ) : abcExceptions ε ⊆ Set.Ici 1 := by
  rintro ⟨a, b, c⟩
  simp only [mem_abcExceptions, Set.mem_Ici, and_imp, ← Prod.mk_one_one, Prod.mk_le_mk]
  omega

/-- The abc conjecture: the set of exceptional triples is finite. -/
def abcConjecture : Prop := ∀ ε > 0, (abcExceptions ε).Finite

open Topology in
lemma abcConjecture_iff_eventually :
    abcConjecture ↔ ∀ᶠ ε in 𝓝[>] 0, (abcExceptions ε).Finite := by
  constructor
  · intro (h : ∀ _, _)
    simp +contextual [eventually_nhdsWithin_iff, h]
  · intro h ε hε
    suffices ∀ᶠ (δ : ℝ) in 𝓝[>] 0, (abcExceptions ε).Finite by simpa
    filter_upwards [h, eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hε)]
      with δ hδ hδε using hδ.subset (abcExceptions_mono hδε.le)

lemma abcExceptionsBelow_eq_abcExceptions_inter (ε : ℝ) (X : ℕ) (hε : ε < 1) :
    abcExceptionsBelow ε X =
      abcExceptions ((1 - ε)⁻¹ - 1) ∩ Set.Icc (1, 1, 1) (X, X, X) := by
  ext ⟨a, b, c⟩
  suffices radical (a * b * c) ^ (1 - ε)⁻¹ < (c : ℝ) ↔ radical (a * b * c) < (c : ℝ) ^ (1 - ε) by
    simp [Nat.add_one_le_iff]
    tauto
  rw [Real.rpow_inv_lt_iff_of_pos (by simp) (by simp) (by simpa)]

lemma abcExceptionsBelow_eq_abcExceptions_inter' (ε : ℝ) (X : ℕ) (hε : 0 < ε) :
    abcExceptionsBelow (1 - (1 + ε)⁻¹) X =
      abcExceptions ε ∩ Set.Icc (1, 1, 1) (X, X, X) := by
  rw [abcExceptionsBelow_eq_abcExceptions_inter _ _]
  · simp
  · simp [add_pos zero_lt_one hε]

open Asymptotics Filter

lemma forall_increasing' {α : Type*} (f : ℕ → Set α) (hf : Monotone f)
    (hf' : ∀ n, (f n).Finite)
    {C : ℕ} (hC : ∀ n, (f n).ncard ≤ C) : (⋃ n, f n).Finite := by
  by_contra!
  obtain ⟨t, ht, ht', ht''⟩ := Set.Infinite.exists_subset_ncard_eq this (C + 1)
  lift t to Finset α using ht'
  obtain ⟨i, hi⟩ := hf.directed_le.exists_mem_subset_of_finset_subset_biUnion ht
  replace hC : (f i).ncard ≤ C := hC i
  have := Set.ncard_le_ncard hi (hf' _)
  omega

lemma forall_increasing {α : Type*} (f : ℕ → Set α) (hf : Monotone f)
    {s : Set α} (hf' : ∀ n, (s ∩ f n).Finite)
    {C : ℕ} (hC : ∀ n, (s ∩ f n).ncard ≤ C) : (s ∩ ⋃ n, f n).Finite := by
  rw [Set.inter_iUnion]
  refine forall_increasing' _ ?_ hf' hC
  intro a b hab
  exact Set.inter_subset_inter_right _ (hf hab)

lemma abcConjecture_iff_countTriples :
    abcConjecture ↔ ∀ ε > 0, ε < 1 → (countTriples ε · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_one_nat_atTop_iff]
  constructor
  · intro h ε hε₀ hε₁
    have habc := h ((1 - ε)⁻¹ - 1) (by simp [sub_pos, one_lt_inv₀, *])
    use (abcExceptions ((1 - ε)⁻¹ - 1)).ncard
    intro n
    rw [Real.norm_natCast, Nat.cast_le, countTriples,
      ← Set.ncard_coe_finset, abcExceptionsBelow_eq_abcExceptions_inter _ _ hε₁]
    exact Set.ncard_le_ncard Set.inter_subset_left habc
  · intro h ε hε
    obtain ⟨C, hC⟩ := h (1 - (1 + ε)⁻¹)
      (by simp [inv_lt_one_of_one_lt₀, hε]) (by simp [add_pos, hε])
    have hC₀ : 0 ≤ C := (hC 0).trans' (by simp)
    simp_rw [Real.norm_natCast, countTriples, ← Nat.le_floor_iff hC₀,
      ← Set.ncard_coe_finset, abcExceptionsBelow_eq_abcExceptions_inter' ε _ hε] at hC
    have : ⋃ n, Set.Icc (1, 1, 1) (n, n, n) = Set.Ici 1 := by
      ext ⟨i, j, k⟩
      simp only [Set.mem_iUnion, Set.mem_Icc, Prod.mk_le_mk, exists_and_left, ← Prod.mk_one_one,
        Set.mem_Ici, and_iff_left_iff_imp, and_imp]
      rintro - - -
      exact ⟨max i (max j k), by simp⟩
    rw [← Set.inter_eq_left.2 (abcExceptions_subset_Ici_one ε), ← this]
    refine forall_increasing _ ?_ ?_ hC
    · intro n m hnm
      dsimp
      gcongr
    · intro n
      exact (Set.finite_Icc (1, 1, 1) (n, n, n)).inter_of_right _

open Topology in
lemma abcConjecture_iff_eventually_countTriples :
    abcConjecture ↔ ∀ᶠ ε in 𝓝[>] 0, (countTriples ε · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  rw [abcConjecture_iff_countTriples]
  constructor
  · intro h
    simp only [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds zero_lt_one] with ε hε₁ hε₀ using h _ hε₀ hε₁
  intro h ε hε₀ hε₁
  suffices ∀ᶠ (δ : ℝ) in 𝓝[>] 0, (countTriples ε · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) by simpa
  filter_upwards [h, eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hε₀)]
    with δ hδ hδε
  apply IsBigO.trans (IsBigO.of_norm_le _) hδ
  simp only [Real.norm_natCast, Nat.cast_le]
  intro x
  gcongr

lemma radical_dvd_div_mul_radical_of_dvd (a b : ℕ) (h : a ∣ b) :
    radical b ∣ (b / a) * radical a := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain ⟨c, rfl⟩ := h
  simp only [ne_eq, ha₀, not_false_eq_true, mul_div_cancel_left₀]
  calc
    radical (a * c) ∣ radical a * radical c := radical_mul_dvd
    _ = radical c * radical a := by rw [mul_comm]
    _ ∣ c * radical a := Nat.mul_dvd_mul_right radical_dvd_self _

/-- A concrete construction of a triple which has rad(abc) < c. -/
def tripleAt (n : ℕ) : ℕ × ℕ × ℕ := (1, 2 ^ (6 * n) - 1, 2 ^ (6 * n))

lemma tripleAt_mem_abcExceptions (n : ℕ) (hn : 0 < n) : tripleAt n ∈ abcExceptions 0 := by
  have h₂ : 1 < 2 ^ (6 * n) := one_lt_pow₀ one_lt_two (by positivity)
  suffices radical ((2 ^ (6 * n) - 1) * 2 ^ (6 * n)) < 2 ^ (6 * n) by
    simpa [hn.ne', h₂.le, abcExceptions, tripleAt]
  have h₃ : 9 ∣ 2 ^ (6 * n) - 1 := by
    rw [← Nat.modEq_iff_dvd' h₂.le, Nat.ModEq.comm]
    calc
      2 ^ (6 * n) ≡ (2 ^ 6) ^ n [MOD 9] := by rw [pow_mul]
      _ ≡ 64 ^ n [MOD 9] := by simp [Nat.ModEq.refl]
      _ ≡ 1 ^ n [MOD 9] := .pow _ (by decide)
      _ ≡ 1 [MOD 9] := by simp [Nat.ModEq.refl]
  have h₄ : radical (2 ^ (6 * n) - 1) * 2 < 2 ^ (6 * n) := by
    obtain ⟨k, hk⟩ := h₃
    have h₉ : radical 9 = 3 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.radical_eq_prod_primeFactors,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      simp
    calc
    radical (2 ^ (6 * n) - 1) * 2 = radical (9 * k) * 2 := by rw [hk]
    _ ≤ (radical 9 * radical k) * 2 :=
      Nat.mul_le_mul_right 2 (Nat.le_of_dvd (by positivity) radical_mul_dvd)
    _ = 2 * radical 9 * radical k := by ring
    _ = 6 * radical k := by rw [h₉]
    _ ≤ 9 * k := by
      gcongr
      · norm_num1
      · exact Nat.radical_le_self_iff.2 (by omega)
    _ < 2 ^ (6 * n) := by omega
  calc
    radical ((2 ^ (6 * n) - 1) * 2 ^ (6 * n))
    _ = radical (2 ^ (6 * n) - 1) * radical (2 ^ (6 * n)) := by
      simp [radical_mul, h₂.le, ← Nat.coprime_iff_isRelPrime]
    _ = radical (2 ^ (6 * n) - 1) * 2 := by
      rw [radical_pow_of_prime Nat.prime_two.prime (by positivity), normalize_eq]
    _ < 2 ^ (6 * n) := h₄

lemma tripleAt_strictMono : StrictMono tripleAt := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [tripleAt, Prod.mk_lt_mk, lt_self_iff_false, Prod.mk_le_mk, tsub_le_iff_right,
    false_and, le_refl, true_and, false_or]
  right
  constructor
  · rw [mul_add_one, pow_add]
    omega
  · gcongr
    · simp
    · simp

lemma abcExceptions_zero_infinite : (abcExceptions 0).Infinite :=
  ((Set.Ioi_infinite 0).image tripleAt_strictMono.injective.injOn).mono
    (by simpa [Set.subset_def] using tripleAt_mem_abcExceptions)

end

/-- We define reals `x` and `X` to be similar if `x ∈ [X, 2X]`. -/
def similar (x X : ℝ) : Prop := x ∈ Set.Icc X (2 * X)

local infixr:36 " ~ " => similar

theorem similar_pow_natLog (x : ℕ) (hx : x ≠ 0) : x ~ 2 ^ Nat.log 2 x := by
  simp only [similar, Set.mem_Icc]
  norm_cast
  constructor
  · refine Nat.pow_log_le_self 2 hx
  · rw [← Nat.pow_succ']
    exact (Nat.lt_pow_succ_log_self (by omega) _).le

open Classical in
/-- The finite set of exceptions `(a, b, c)` to the abc conjecture for which `X/2 ≤ c ≤ X` and
  `rad a ~ X^α`, `rad b ~ X^β`, `rad c ~ X^γ`. `S*` counts the size of this set. -/
noncomputable def dyadicPoints (α β γ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (1, 1, 1) (2*X, 2*X, 2*X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    (radical a : ℕ) ~ (X ^ α : ℝ) ∧
    (radical b : ℕ) ~ (X ^ β : ℝ) ∧
    (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
    X ≤ 2 * c ∧ c ≤ X

@[simp]
theorem mem_dyadicPoints (α β γ : ℝ) (X : ℕ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ dyadicPoints α β γ X ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧
      (radical b : ℕ) ~ (X ^ β : ℝ) ∧
      (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      X ≤ 2 * c ∧ c ≤ X := by
  simp only [dyadicPoints, Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk, Nat.add_one_le_iff,
    similar, Set.mem_Icc, ← and_assoc, and_congr_left_iff]
  intro ha hb hc hc_le_X hX_le_c hrc hrb hra habc hbc hac
  omega

/--
This is $$S^*_{α,β,γ}(X)$$ in the paper and blueprint.
-/
noncomputable def refinedCountTriplesStar (α β γ : ℝ) (X : ℕ) : ℕ := #(dyadicPoints α β γ X)

/-- The set over which we take the supremum in lemma 2.2. -/
noncomputable def indexSet (ε : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 0 (Nat.log 2 X)) ×ˢ
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 1 (Nat.log 2 X+1)) |>.filter fun ⟨i, j, k, n⟩ ↦
    i + j + k ≤ (1 - ε) * n

private theorem card_indexSet_le (ε : ℝ) (X : ℕ) :
    (indexSet ε X).card ≤ (Nat.log 2 X + 1) ^ 4 := by
  apply (Finset.card_filter_le ..).trans
  simp only [card_product, Nat.card_Icc, tsub_zero, add_tsub_cancel_right]
  linear_combination

@[simp]
private theorem mem_indexSet (ε : ℝ) (X : ℕ) (i j k n : ℕ) :
    ⟨i, j, k, n⟩ ∈ indexSet ε X ↔
      i ≤ Nat.log 2 X ∧ j ≤ Nat.log 2 X ∧ k ≤ Nat.log 2 X ∧
      1 ≤ n ∧ n ≤ Nat.log 2 X + 1 ∧ i + j + k ≤ (1 - ε) * n := by
  simp [indexSet]
  norm_cast
  aesop

theorem Nat.Coprime.isRelPrime (a b : ℕ) (h : a.Coprime b) : IsRelPrime a b := by
  rwa [← Nat.coprime_iff_isRelPrime]

theorem sum_le_card_mul_sup {ι : Type*} (f : ι → ℕ) (s : Finset ι) :
    ∑ i ∈ s, f i ≤ s.card * s.sup f := calc
  ∑ i ∈ s, f i ≤ ∑ i ∈ s, s.sup f := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.le_sup hi
  _ = s.card * s.sup f := by
    simp

theorem card_union_dyadicPoints_le_log_pow_mul_sup (ε : ℝ) (X : ℕ) :
    ((indexSet ε X).biUnion fun ⟨i, j, k, n⟩ ↦
      dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)).card ≤
  (Nat.log 2 X+1)^4 * (indexSet ε X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  apply (Finset.card_biUnion_le ..).trans
  simp only
  apply (sum_le_card_mul_sup _ _).trans
  gcongr
  · apply card_indexSet_le
  · rfl

/-- The supremum that appears in lemma 2.2, taken over a finite subset of α, β, γ > 0 such that
  α + β + γ ≤ 1 - ε -/
noncomputable def dyadicSupBound (ε : ℝ) (X : ℕ) : ℕ :=
  (indexSet ε X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)

open Asymptotics Filter

theorem Real.natLog_isBigO_logb (b : ℕ) :
    (fun x : ℕ ↦ (Nat.log b x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.logb b x) := by
  apply IsBigO.of_bound'
  filter_upwards with x
  rw [Real.norm_natCast, Real.norm_eq_abs]
  exact (Real.natLog_le_logb _ _).trans (le_abs_self _)

theorem Real.logb_isBigO_log (b : ℝ) :
    logb b =O[atTop] log :=
  .of_bound |Real.log b|⁻¹ <| by filter_upwards using by simp [Real.logb, div_eq_inv_mul]

theorem Real.log_isBigO_logb (b : ℝ) (hb : 1 < b) :
    log =O[atTop] logb b :=
  .of_bound |Real.log b| <| by
    filter_upwards using by simp [Real.logb, mul_div_cancel₀, (log_pos hb).ne']

theorem Nat.log_isBigO_log (b : ℕ) :
    (fun x : ℕ ↦ (Nat.log b x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.log x) :=
  (Real.natLog_isBigO_logb _).trans
    ((Real.logb_isBigO_log _).comp_tendsto tendsto_natCast_atTop_atTop)

/-- The finite set of `d`-tuples `a i` such that `a i ~ X i` for all `i`. -/
def dyadicTuples {d : ℕ} (X : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i ↦ Finset.Icc (X i) (2 * X i))

@[simp]
theorem mem_dyadicTuples {d : ℕ} (X x : Fin d → ℕ) :
    x ∈ dyadicTuples X ↔ ∀ i, x i ~ X i := by
  simp [dyadicTuples, similar]
  norm_cast

open Classical in
/-- The finite set counted by `B_d(C, X, Y, X)`. We choose to add `C` as an entry in these tuples,
  as this allows us to write down a surjective map from a union of these sets back to triples
  `(a, b, c)` in `dyadicTriples α β γ`. -/
noncomputable def BFinset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  ((dyadicTuples X) ×ˢ (dyadicTuples Y) ×ˢ (dyadicTuples Z) ×ˢ {C}).filter fun ⟨x, y, z, c⟩ ↦
    c 0 * ∏ i, x i ^ (i.val + 1) + c 1 * ∏ i, y i ^ (i.val + 1) = c 2 * ∏ i, z i ^ (i.val + 1) ∧
    Nat.gcd (c 0 * ∏ i, x i) (c 1 * ∏ i, y i) = 1 ∧ -- TODO: write these as Coprime?
    Nat.gcd (c 0 * ∏ i, x i) (c 2 * ∏ i, z i) = 1 ∧
    Nat.gcd (c 1 * ∏ i, y i) (c 2 * ∏ i, z i) = 1

theorem mem_B_finset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ)
    (x y z : Fin d → ℕ) (c : Fin 3 → ℕ) :
    (x, y, z, c) ∈ BFinset d C X Y Z ↔
      C = c ∧
      (∀ i, x i ~ X i) ∧ (∀ i, y i ~ Y i) ∧ (∀ i, z i ~ Z i) ∧
      c 0 * ∏ i, (x i)^(i.val + 1) + c 1 * ∏ i, (y i)^(i.val + 1) = c 2 * ∏ i, (z i)^(i.val + 1) ∧
      Nat.gcd (c 0 * ∏ i, (x i)) (c 1 * ∏ i, (y i)) = 1 ∧
      Nat.gcd (c 0 * ∏ i, (x i)) (c 2 * ∏ i, (z i)) = 1 ∧
      Nat.gcd (c 1 * ∏ i, (y i)) (c 2 * ∏ i, (z i)) = 1 := by
  simp only [BFinset, Fin.isValue, Finset.mem_singleton, Finset.mem_filter, Finset.mem_product,
    mem_dyadicTuples]
  tauto

/-- Definition 2.4 -/
noncomputable def B (d : ℕ) (c : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) : ℕ := (BFinset d c X Y Z).card

theorem Nat.factorization_le_right (p n : ℕ) (hp : p.Prime) : n.factorization p ≤ n := by
  refine factorization_le_of_le_pow ?_
  induction n with
  | zero => simp
  | succ n ih =>
    have : 1 ≤ p ^ n := by
      apply Nat.one_le_pow
      apply hp.pos
    have : 2 ≤ p := hp.two_le
    rw [pow_succ]
    calc _ ≤ p^n + p^n := by gcongr
      _ = p^n * 2 := by ring
      _ ≤ p^n * p := by gcongr

theorem Nat.ceil_lt_floor (a b : ℝ) (ha : 0 ≤ a) (hab : a + 2 ≤ b) : ⌈a⌉₊ < ⌊b⌋₊ := by
  exact_mod_cast calc
    ⌈a⌉₊ < a + 1 := by
      exact ceil_lt_add_one ha
    _ ≤ b - 1 := by
      linarith
    _ < ⌊b⌋₊ := by
      exact sub_one_lt_floor b

namespace NiceFactorization

/-- The data and assumptions of lemma 2.5. We treat `d` as a free variable constrained by `hd` here
  because `d` appears in a type and this gives the user some leeway to rewrite the value of `d`. -/
class ProofData where
  /-- The value of epsilon in Lemma 2.5 -/
  ε : ℝ
  hε_pos : 0 < ε
  hε : ε < 1 / 2
  /-- `d` in Lemma 2.5 -/
  d : ℕ
  hd : d = ⌊5 / 2 * ε⁻¹ ^ 2⌋₊
  /-- `n` in Lemma 2.5 -/
  n : ℕ
  /-- `X` in Lemma 2.5 -/
  X : ℕ
  h1n : 1 ≤ n
  hnX : n ≤ X

open ProofData NiceFactorization
variable [data : ProofData]

/-- `y j` is the product of primes dividing `n` with multiplicity `j`. -/
def y (j : ℕ) : ℕ := ∏ p ∈ n.primeFactors with n.factorization p = j, p

@[simp]
private theorem y_zero : y 0 = 1 := by
  simp +contextual [y, Nat.factorization_eq_zero_iff]

private theorem hy_pos (j : ℕ) : 0 < y j := by
  apply Finset.prod_pos
  simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, and_imp]
  intro p hp _ _ _
  exact hp.pos

private theorem prod_y_pow_eq_n_subset {s : Finset ℕ}
    (hs : ∀ p, p.Prime → p ∣ n → n.factorization p ∈ s) :
    ∏ m ∈ s, y m ^ m = n := by
  have := h1n
  simp_rw [y]
  conv =>
    rhs
    rw [← Nat.prod_factorization_pow_eq_self (show n ≠ 0 by omega)]
  simp_rw [← Finset.prod_pow]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  convert Finset.prod_fiberwise_of_maps_to  (f := fun p ↦ p ^ n.factorization p)
    (g := n.factorization) (s := n.primeFactors) (t := s) ?_ using 1
  · apply Finset.prod_congr rfl
    intro k hk
    apply Finset.prod_congr rfl
    simp_all
  · simp_all

private theorem prod_y_pow_eq_n : ∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m ^ m = n := by
  apply prod_y_pow_eq_n_subset
  intro p hp hpn
  simp only [Finset.mem_union, Finset.mem_Icc]
  have : n.factorization p ≤ n := Nat.factorization_le_right p n hp
  have : n.factorization p ≤ d ∨ d < n.factorization p := le_or_gt (n.factorization p) d
  simp only [Finset.mem_Ioc]
  have : 1 ≤ n.factorization p := by
    rw [← hp.dvd_iff_one_le_factorization]
    · exact hpn
    · have := h1n
      omega
  tauto

open Function in
omit data in
theorem _root_.Nat.prod_squarefree {ι : Type*} (f : ι → ℕ) {s : Finset ι}
    (hf : ∀ i ∈ s, Squarefree (f i))
    (h : Set.Pairwise (s : Set ι) (Nat.Coprime on f)) :
    Squarefree (∏ i ∈ s, f i) := by
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun i hi j hj hij ↦ (Nat.coprime_iff_isRelPrime.mp (h hi hj hij))) hf

omit data in
theorem _root_.Associated.nat_eq {a b : ℕ} (h : Associated a b) : a = b := by
  rwa [associated_iff_eq] at h

theorem y_squarefree {i : ℕ} : Squarefree (y i) := by
  rw [y]
  apply Nat.prod_squarefree
  · simp +contextual [Finset.mem_filter, Nat.mem_primeFactors, Nat.Prime.prime, Prime.squarefree]
  · simp +contextual [Nat.coprime_primes, Function.onFun, Set.Pairwise]

/-- `K` in the proof of lemma 2.5 -/
noncomputable def K := ⌈ε⁻¹⌉₊

private theorem two_lt_eps_inv : 2 < ε⁻¹ := by
  have := hε_pos
  rw [← inv_inv 2]
  gcongr
  linarith only [hε]

private theorem hK_pos : 0 < K := by
  rw [K, Nat.ceil_pos]
  simp [hε_pos]

private theorem K_inv_le_eps : (K : ℝ)⁻¹ ≤ ε := by
  rw [inv_le_iff_one_le_mul₀]
  · calc
    1 = ε * ε⁻¹ := by
      field_simp [hε_pos.ne.symm]
    _ ≤ ε * K := by
      have := hε_pos
      gcongr
      rw [K]
      apply Nat.le_ceil
  · simp [hK_pos]

private theorem hd_pos : 0 < d := by
  rw [hd, Nat.floor_pos]
  nlinarith only [two_lt_eps_inv]

instance hd_ne_zero : NeZero d := by
  simp_rw [neZero_iff]
  apply ne_of_gt hd_pos

private theorem hKd : K < d := by
  have := two_lt_eps_inv
  simp_rw [K, hd]
  rw [Nat.lt_iff_add_one_le]
  apply Nat.ceil_lt_floor
  · positivity
  nlinarith

/-- `x` in the proof of lemma 2.5 -/
noncomputable def x (j : Fin d) : ℕ :=
  y (j.val+1) * if j.val + 1 = K then (∏ m ∈ Finset.Ioc d n, y m ^ (m / K)) else 1

theorem x_pos (j : Fin d) : 0 < x j := by
  rw [x]
  split_ifs with h
  · apply mul_pos
    · apply hy_pos
    · apply Finset.prod_pos
      intros
      apply pow_pos (hy_pos _)
  · simp [hy_pos]

/-- `c` in the proof of lemma 2.5 -/
noncomputable def c : ℕ := ∏ m ∈ Finset.Ioc d n, y m ^ (m % K)

omit data in
theorem nat_eq_fin_iff {n a : ℕ} {b : Fin n} [NeZero n] (ha : a < n) :
    Fin.ofNat n a = b ↔ a = b.val := by
  rw [← Fin.val_inj]
  simp [Fin.ofNat, Nat.mod_eq_of_lt ha]

omit data in
theorem fin_eq_nat_iff {n a : ℕ} {b : Fin n} [NeZero n] (ha : a < n) :
    b = Fin.ofNat n a ↔ b.val = a := by
  rw [← Fin.val_inj]
  simp [Fin.ofNat, Nat.mod_eq_of_lt ha]

/-- The distinguished index `K - 1`, viewed in `Fin d`. -/
noncomputable def KIndex : Fin d := Fin.ofNat d (K - 1)

@[simp]
private theorem KIndex_val_add_one : KIndex.val + 1 = K := by
  have hlt : K - 1 < d := by
    have := hKd
    omega
  simp [KIndex, Fin.ofNat, Nat.mod_eq_of_lt hlt]
  have := hK_pos
  omega

theorem x_K_le_X_pow : x KIndex ≤ (X : ℝ) ^ ε := by
  have h1n := h1n
  have hnX := hnX
  rw [x, ite_eq_left ?side]
  case side =>
    simp
  have := hKd
  simp only [KIndex_val_add_one, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, ge_iff_le]
  exact_mod_cast calc
    (y K * ∏ m ∈ Finset.Ioc d n, y m ^ (m / K) : ℝ) ≤
      (y K ^ K)^(K⁻¹:ℝ) * (∏ m ∈ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
        gcongr
        · rw [← Real.rpow_natCast_mul, mul_inv_cancel₀]
          · simp
          · simp only [ne_eq, Nat.cast_eq_zero]
            apply hK_pos.ne.symm
          · exact_mod_cast (hy_pos _).le
        · push_cast
          rw [← Real.finsetProd_rpow _ _ (by simp)]
          gcongr with i hi
          rw [← Real.rpow_natCast_mul, ← Real.rpow_natCast]
          · gcongr
            · simp only [Nat.one_le_cast]
              apply Nat.add_one_le_of_lt
              apply hy_pos
            · rw [← Nat.floor_div_eq_div (K := ℝ), div_eq_mul_inv]
              apply Nat.floor_le
              positivity
          · simp
    _ = (∏ m ∈ {K} ∪ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
        rw [Finset.prod_union]
        · simp only [Nat.cast_prod, Nat.cast_pow, Finset.prod_singleton, Nat.cast_mul]
          rw [Real.mul_rpow]
          · simp
          · positivity
        · simp only [disjoint_singleton_left, mem_Ioc, not_and, not_le]
          intro
          linarith
    _ ≤ (∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
      gcongr
      · intros
        apply Nat.add_one_le_of_lt
        simp [hy_pos]
      · intro i
        simp +contextual [hKd.le, Nat.add_one_le_iff.eq ▸ hK_pos]
    _ = (n : ℝ) ^ (K⁻¹ : ℝ) := by
      congr
      rw [prod_y_pow_eq_n]
    _ ≤ (X : ℝ) ^ (K⁻¹ : ℝ) := by
      gcongr
    _ ≤ (X : ℝ)^ε := by
      gcongr
      · norm_cast
        omega
      apply K_inv_le_eps

end NiceFactorization

/-- A surjective map ⋃_{c, X, Y ,Z} B (c, X, Y, Z) → S*_α β γ (X) -/
def BToTriple {d : ℕ} : (Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ) → ℕ × ℕ × ℕ :=
  fun ⟨X, Y, Z, c⟩ ↦
    ⟨c 0 * ∏ i, X i ^ (i.val + 1), c 1 * ∏ i, Y i ^ (i.val + 1), c 2 * ∏ i, Z i ^ (i.val + 1)⟩

open Classical in
/-- The finite set over which we will take a supremum in proposition 2.6 -/
noncomputable def indexSet' (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  ((Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x)) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Ioc 0 ⌊(x:ℝ)^(ε/4)⌋₊) : Finset (Fin 3 → ℕ))
  ) |>.filter fun ⟨r, s, t, c⟩ ↦
    (x:ℝ) ^ (α - ε) ≤ 2^d * ∏ i, 2 ^ r i ∧ ∏ i, 2 ^ r i ≤ 2 * (x:ℝ) ^ (α + ε) ∧
    (x:ℝ) ^ (β - ε) ≤ 2^d * ∏ i, 2 ^ s i ∧ ∏ i, 2 ^ s i ≤ 2 * (x:ℝ) ^ (β + ε) ∧
    (x:ℝ) ^ (γ - ε) ≤ 2^d * ∏ i, 2 ^ t i ∧ ∏ i, 2 ^ t i ≤ 2 * (x:ℝ) ^ (γ + ε) ∧
    ∏ i, (2 ^ r i)^(i.val + 1) ≤ x ∧
    ∏ i, (2 ^ s i)^(i.val + 1) ≤ x ∧
    ∏ i, (2 ^ t i)^(i.val + 1) ≤ x ∧
    (x : ℝ)^(1-ε^2) ≤ 2^(Nat.choose (d+1) 2 + 1) * ∏ i, (2 ^ t i)^(i.val + 1) ∧
    (Nat.Coprime (c 0) (c 1)) ∧ (Nat.Coprime (c 1) (c 2)) ∧ (Nat.Coprime (c 0) (c 2)))

theorem card_indexSet'_le (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ) :
    (indexSet' α β γ d x ε).card ≤ (Nat.log 2 x + 1)^(3*d) * (⌊(x:ℝ) ^ (ε/4)⌋₊)^3 := by
  rw [indexSet']
  apply Finset.card_filter_le .. |>.trans
  simp only [card_product, Fintype.card_piFinset, Nat.card_Icc, tsub_zero, prod_const, card_univ,
    Fintype.card_fin, Nat.card_Ioc]
  apply le_of_eq
  ring

/-- The union of `B`-sets used in the proof of proposition 2.6. -/
noncomputable def BUnion (α β γ : ℝ) {d : ℕ} (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  (indexSet' α β γ d x ε).sup fun ⟨r, s, t, c⟩ ↦
    BFinset d c (fun i ↦ 2^r i) (fun i ↦ 2^s i) (fun i ↦ 2^t i)

theorem similar_pow_log {x : ℕ} (hx : 0 < x) : x ~ 2 ^ Nat.log 2 x := by
  simp only [similar, Set.mem_Icc]
  norm_cast
  constructor
  · refine Nat.pow_log_le_self 2 hx.ne.symm
  · rw [mul_comm, ← Nat.pow_succ]
    apply le_of_lt
    refine Nat.lt_pow_succ_log_self ?_ x
    norm_num

theorem coprime_mul_prod_aux {ι : Type*} {s : Finset ι} {f g u v : ι → ℕ} {a b : ℕ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hcop : Nat.Coprime (a * ∏ i ∈ s, (f i) ^ (u i)) (b * ∏ i ∈ s, g i ^ (v i))) :
    Nat.Coprime (a * ∏ i ∈ s, f i) (b * ∏ i ∈ s, g i) := by
  simpa only [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_left, Nat.coprime_prod_left_iff,
    Nat.coprime_prod_right_iff, hu, Nat.coprime_pow_left_iff, hv, Nat.coprime_pow_right_iff] using
    hcop

open Finset in
theorem Nat.sum_Ico_choose (n k : ℕ) : ∑ m ∈ Ico k n, m.choose k = n.choose (k + 1) := by
  rcases le_or_gt n k with h | h
  · rw [choose_eq_zero_of_lt (by omega), Ico_eq_empty_of_le h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← insert_Ico_right_eq_Ico_add_one (by omega), sum_insert (by simp), ih,
        choose_succ_succ' n]

open Finset in
lemma Nat.sum_range_add_choose' (n k : ℕ) :
    ∑ i ∈ Finset.range n, (i + k).choose k = (n + k).choose (k + 1) := by
  rw [← sum_Ico_choose, range_eq_Ico]
  rw [show Ico k (n + k) = (Ico 0 n).map (addRightEmbedding k) by
    rw [Finset.map_add_right_Ico, zero_add], sum_map]
  rfl

theorem sum_range_id_add_one {d : ℕ} : ∑ i ∈ Finset.range d, (i + 1) = (d + 1).choose 2 := by
  simpa using Nat.sum_range_add_choose' d 1

section Asymptotics
/- TODO: The results in this section should probably be cleaned up - in the end we also lose a
  factor of (log x)^4 going from N to S, perhaps this should also be rolled into this bound. -/

theorem log_le_const_mul_pow {ε : ℝ} (hε : 0 < ε) (d : ℕ) (hd : 0 < d) :
    ∃ c ≥ 0, ∀ x : ℕ, (Real.log x)^d ≤ c * (x : ℝ)^ε := by
  have := (isLittleO_log_rpow_rpow_atTop d hε).isBigO.natCast_atTop
  have := this.nat_of_atTop (l := ⊤) ?_
  · simp only [Real.rpow_natCast, Asymptotics.isBigO_iff', norm_pow, Real.norm_eq_abs] at this
    simp only [gt_iff_lt, eventually_top] at this
    obtain ⟨c, hc_pos, hc⟩ := this
    refine ⟨c, hc_pos.le, ?_⟩
    intro x
    calc
      _ ≤ _ := by
        gcongr
        exact le_abs_self (Real.log ↑x)
      _ ≤ _ := hc x
      _ ≤ _ := by
        rw [abs_of_nonneg]
        positivity
  · simp [Real.rpow_natCast, hε.ne', hd.ne']

theorem tmp {ε : ℝ} (hε : 0 < ε) (d : ℕ) (hd : 0 < d) :
    ∃ c, ∀ x : ℕ, 2 ≤ x → (Nat.log 2 x + 1) ^ (3 * d) ≤ c * (x : ℝ)^(ε/4) := by
  obtain ⟨c, hc_nonneg, hc⟩ := log_le_const_mul_pow (show 0 < ε/4 by linarith) (3*d) (by omega)
  use (Real.log 2)⁻¹ ^ (3*d) * c * 2^(ε/4)
  intro x hx
  specialize hc (2*x)
  have log_add : Nat.log 2 x + 1 = Nat.log 2 (2 * x) := by
    rw [mul_comm, Nat.log_mul_base]
    · norm_num
    omega
  have : (Nat.log 2 (2 * x))^(3*d) ≤ (Real.log 2)⁻¹ ^ (3*d) * Real.log (2 * x) ^ (3*d) := by
    trans (Real.logb 2 (2 * x))^(3*d)
    · gcongr
      rw [← Real.natFloor_logb_natCast]
      push_cast
      apply Nat.floor_le
      apply Real.logb_nonneg <;> norm_cast
      omega
    · apply le_of_eq
      rw [← Real.log_div_log]
      ring
  calc
    _ ≤ ((Nat.log 2 (2 * x)) ^ (3 * d) : ℝ) :=  by
      rw_mod_cast [log_add]
    _ ≤ ((Real.log 2)⁻¹ ^ (3*d) * c * 2^(ε/4) * (x : ℝ)^(ε/4): ℝ) :=  by
      apply this.trans
      simp_rw [mul_assoc]
      gcongr
      push_cast at hc
      apply hc.trans
      gcongr
      rw [Real.mul_rpow] <;> norm_num

/-- The implicit coefficient in the conclusion of proposition 2.6 -/
noncomputable def const (ε : ℝ) : ℝ :=
  if h : 0 < ε then
    if h' : ε < 1 / 2 then
      let d := ⌊10 * ε⁻¹ ^ 4⌋₊
      have : 2 < ε⁻¹ := by
        rw [← show (2:ℝ)⁻¹⁻¹ = 2 by norm_num]
        gcongr
        linarith
      have : 2 ^ 4 < ε⁻¹ ^ 4 := by gcongr
      have hd : 0 < d := by rw [Nat.floor_pos]; linarith
      Classical.choose (tmp h d hd)
    else 0
  else 0

theorem const_spec {ε : ℝ} (hε_pos : 0 < ε) (hε : ε < 1 / 2) :
    let d := ⌊10 * ε⁻¹ ^ 4⌋₊
    ∀ x : ℕ, 2 ≤ x → (Nat.log 2 x + 1) ^ (3 * d) ≤ const ε * (x : ℝ)^(ε/4) := by
  rw [const, dite_eq_left hε_pos, dite_eq_left hε]
  extract_lets d _ _ _ hd
  apply Classical.choose_spec (tmp hε_pos d hd)

theorem const_nonneg {ε : ℝ} : 0 ≤ const ε := by
  by_cases hε_pos : 0 < ε
  · by_cases hε : ε < 1 / 2
    · have := const_spec hε_pos hε 2 le_rfl
      simp only [inv_pow, Nat.cast_ofNat] at this
      have := calc
        0 ≤ _ := mod_cast Nat.zero_le _
        _ ≤ _ := this
      -- surely there's a better lemma that doesn't require strict positivity
      apply nonneg_of_mul_nonneg_left this
      apply Real.rpow_pos_of_pos
      norm_num
    · rw [const, dite_eq_left hε_pos, dite_eq_right hε]
  · rw [const, dite_eq_right hε_pos]

end Asymptotics

theorem card_indexSet'_le_pow (ε α β γ : ℝ) (d x : ℕ) (hd : d = ⌊10 * ε⁻¹ ^ 4⌋₊) (hx : 2 ≤ x)
    (hε_pos : 0 < ε) (hε : ε < 1 / 2) :
    (indexSet' α β γ d x ε).card ≤ const ε * (x:ℝ)^ε := by
  have := const_spec hε_pos hε x hx
  rw [← hd] at this
  calc
    _ ≤ ((Nat.log 2 x + 1) ^ (3 * d) * ⌊(x : ℝ) ^ (ε / 4)⌋₊ ^ 3 : ℝ) :=
      mod_cast card_indexSet'_le α β γ d x ε
    _ ≤ (const ε * (x : ℝ) ^ (ε/4) * (x : ℝ) ^ (3/4 * ε) : ℝ) :=  by
      gcongr
      · have := const_nonneg (ε := ε)
        positivity
      · trans (x ^ (ε / 4)) ^ 3
        · gcongr
          apply Nat.floor_le
          positivity
        apply le_of_eq
        rw [← Real.rpow_mul_natCast (by positivity)]
        ring_nf
    _ = const ε * (x : ℝ) ^ ε  :=  by
      rw [mul_assoc, ← Real.rpow_add]
      · ring_nf
      · positivity

/-- The value of `d` chosen in proposition 2.6 -/
noncomputable def d (ε : ℝ) : ℕ := ⌊10 * ε⁻¹ ^ 4⌋₊

/- Proposition 2.7. Reformulated slightly in terms of the existence of a `Finset` whose elements
  have certain properties. As it stands the statement in the blueprint implicitly assumes that
  this `Finset` is nonempty. That might be true, but is rather annoying to prove and unnecessary
  if we just need an upper bound on S*. -/
