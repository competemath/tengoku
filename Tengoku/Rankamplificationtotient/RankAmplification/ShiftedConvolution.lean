import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Data.Nat.Cast.Order.Field
import Tengoku.Rankamplificationtotient.RankAmplification.ShiftedCoprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Shifted divisor convolution This module formalizes the finite-support form of Lemma 2.4. -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-- A nonnegative divisor weight with finite, positive support.-/
structure FiniteDivisorWeight where
  /-- Finite set on which the weight may be nonzero.-/
  support : Finset ℕ
  /-- Real weight assigned to each divisor.-/
  weight : ℕ → ℝ
  weight_nonneg : ∀ d ∈ support, 0 ≤ weight d
  support_pos : ∀ d ∈ support, 0 < d

namespace FiniteDivisorWeight

variable (W : FiniteDivisorWeight)

/-- The divisor convolution `F(N) = ∑_{d∣N} w(d)`.-/
def eval (N : ℕ) : ℝ :=
  ∑ d ∈ W.support, if d ∣ N then W.weight d else 0

/-- The reciprocal mass `Λ = ∑ w(d)/d`.-/
def mass : ℝ :=
  ∑ d ∈ W.support, W.weight d / d

/-- The strict reciprocal tail `Λ_{>H}`.-/
def tailMass (H : ℕ) : ℝ :=
  ∑ d ∈ W.support with H < d, W.weight d / d

/-- The literal finite maximum `max_{1≤N≤B} F(N)`, with value zero for an empty interval.-/
def supNorm (B : ℕ) : ℝ :=
  if h : (Finset.Icc 1 B).Nonempty then
    ((Finset.Icc 1 B).image W.eval).max' (h.image W.eval)
  else 0

/-- Restrict a weight to divisors strictly above `H`.-/
def restrictAbove (H : ℕ) : FiniteDivisorWeight where
  support := W.support.filter (H < ·)
  weight := W.weight
  weight_nonneg := fun d hd ↦ W.weight_nonneg d (Finset.mem_filter.mp hd).1
  support_pos := fun d hd ↦ W.support_pos d (Finset.mem_filter.mp hd).1

/-- The pair contribution with `d₁d₂ ≤ x`.-/
def smallPairSum (x h : ℕ) : ℝ :=
  ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with d₁ * d₂ ≤ x,
    W.weight d₁ * W.weight d₂ * (shiftedDivisibilitySet x h d₁ d₂).card

/-- The complementary pair contribution with `x < d₁d₂`.-/
def largePairSum (x h : ℕ) : ℝ :=
  ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with x < d₁ * d₂,
    W.weight d₁ * W.weight d₂ * (shiftedDivisibilitySet x h d₁ d₂).card

/-- Pair contribution for which the unshifted divisor exceeds `H`.-/
def leftTailPairSum (x h H : ℕ) : ℝ :=
  ∑ d₁ ∈ W.support with H < d₁, ∑ d₂ ∈ W.support,
    W.weight d₁ * W.weight d₂ * (shiftedDivisibilitySet x h d₁ d₂).card

/-- Pair contribution for which the shifted divisor exceeds `H`.-/
def rightTailPairSum (x h H : ℕ) : ℝ :=
  ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with H < d₂,
    W.weight d₁ * W.weight d₂ * (shiftedDivisibilitySet x h d₁ d₂).card

theorem weight_nonneg_of_mem {d : ℕ} (hd : d ∈ W.support) : 0 ≤ W.weight d :=
  W.weight_nonneg d hd

theorem support_ne_zero {d : ℕ} (hd : d ∈ W.support) : d ≠ 0 :=
  (W.support_pos d hd).ne'

theorem eval_nonneg (N : ℕ) : 0 ≤ W.eval N := by
  unfold eval
  exact Finset.sum_nonneg fun d hd ↦ by
    by_cases hdiv : d ∣ N
    · simpa [hdiv] using W.weight_nonneg d hd
    · simp [hdiv]

theorem mass_nonneg : 0 ≤ W.mass := by
  unfold mass
  exact Finset.sum_nonneg fun d hd ↦
    div_nonneg (W.weight_nonneg d hd) (Nat.cast_nonneg d)

theorem tailMass_nonneg (H : ℕ) : 0 ≤ W.tailMass H := by
  unfold tailMass
  exact Finset.sum_nonneg fun d hd ↦
    div_nonneg (W.weight_nonneg d (Finset.mem_filter.mp hd).1) (Nat.cast_nonneg d)

theorem eval_le_supNorm {B N : ℕ} (hN : N ∈ Finset.Icc 1 B) :
    W.eval N ≤ W.supNorm B := by
  classical
  have hnonempty : (Finset.Icc 1 B).Nonempty := ⟨N, hN⟩
  unfold supNorm
  rw [dite_eq_left hnonempty]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨N, hN, rfl⟩)

theorem supNorm_nonneg {B : ℕ} (hB : 1 ≤ B) : 0 ≤ W.supNorm B := by
  have hmem : 1 ∈ Finset.Icc 1 B := Finset.mem_Icc.mpr ⟨le_rfl, hB⟩
  exact (W.eval_nonneg 1).trans (W.eval_le_supNorm hmem)

@[simp]
theorem restrictAbove_support (H : ℕ) :
    (W.restrictAbove H).support = W.support.filter (H < ·) := rfl

@[simp]
theorem restrictAbove_weight (H d : ℕ) : (W.restrictAbove H).weight d = W.weight d := rfl

theorem restrictAbove_mass (H : ℕ) : (W.restrictAbove H).mass = W.tailMass H := rfl

theorem eval_eq_sum_filter (N : ℕ) :
    W.eval N = ∑ d ∈ W.support.filter (· ∣ N), W.weight d := by
  simp [eval, Finset.sum_filter]

/-- Bilinear expansion for two different finite divisor weights.-/
theorem sum_eval_mul_eval_eq_pair_sum_two (W₁ W₂ : FiniteDivisorWeight) (x h : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, W₁.eval n * W₂.eval (n + h) =
      ∑ d₂ ∈ W₂.support, ∑ d₁ ∈ W₁.support,
        W₁.weight d₁ * W₂.weight d₂ *
          (shiftedDivisibilitySet x h d₁ d₂).card := by
  classical
  simp only [eval, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  change (∑ n ∈ Finset.Icc 1 x,
      (if d₁ ∣ n then W₁.weight d₁ else 0) *
        (if d₂ ∣ n + h then W₂.weight d₂ else 0)) = _
  calc
    _ = ∑ n ∈ Finset.Icc 1 x,
        if d₁ ∣ n ∧ d₂ ∣ n + h then W₁.weight d₁ * W₂.weight d₂ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h₁ : d₁ ∣ n <;> by_cases h₂ : d₂ ∣ n + h <;> simp [h₁, h₂]
    _ = ∑ n ∈ shiftedDivisibilitySet x h d₁ d₂, W₁.weight d₁ * W₂.weight d₂ := by
      unfold shiftedDivisibilitySet
      exact (Finset.sum_filter (s := Finset.Icc 1 x)
        (fun n ↦ d₁ ∣ n ∧ d₂ ∣ n + h)
        (fun _ ↦ W₁.weight d₁ * W₂.weight d₂)).symm
    _ = W₁.weight d₁ * W₂.weight d₂ *
        (shiftedDivisibilitySet x h d₁ d₂).card := by
      simp [mul_comm]

/-- Expanding both divisor sums turns the shifted convolution into a weighted sum of the exact compatibility counts `N_h(d₁,d₂)`.-/
theorem sum_eval_mul_eval_eq_pair_sum_swapped (x h : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h) =
      ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support,
        W.weight d₂ * W.weight d₁ *
          (shiftedDivisibilitySet x h d₂ d₁).card := by
  classical
  simp only [eval, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  change (∑ n ∈ Finset.Icc 1 x,
      (if d₂ ∣ n then W.weight d₂ else 0) *
        (if d₁ ∣ n + h then W.weight d₁ else 0)) = _
  calc
    _ = ∑ n ∈ Finset.Icc 1 x,
        if d₂ ∣ n ∧ d₁ ∣ n + h then W.weight d₂ * W.weight d₁ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h₂ : d₂ ∣ n <;> by_cases h₁ : d₁ ∣ n + h <;> simp [h₁, h₂]
    _ = ∑ n ∈ shiftedDivisibilitySet x h d₂ d₁, W.weight d₂ * W.weight d₁ := by
      unfold shiftedDivisibilitySet
      exact (Finset.sum_filter (s := Finset.Icc 1 x)
        (fun n ↦ d₂ ∣ n ∧ d₁ ∣ n + h)
        (fun _ ↦ W.weight d₂ * W.weight d₁)).symm
    _ = W.weight d₂ * W.weight d₁ *
        (shiftedDivisibilitySet x h d₂ d₁).card := by
      simp [mul_comm]

/-- The same expansion with the unshifted divisor in the first coordinate.-/
theorem sum_eval_mul_eval_eq_pair_sum (x h : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h) =
      ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support,
        W.weight d₁ * W.weight d₂ *
          (shiftedDivisibilitySet x h d₁ d₂).card := by
  rw [W.sum_eval_mul_eval_eq_pair_sum_swapped x h, Finset.sum_comm]

/-- In the small-product range, the exact compatibility count has the paper's `2x/(d₁d₂)` real-valued upper bound.-/
theorem shiftedDivisibilitySet_card_cast_le_two_mul_div {x h d₁ d₂ : ℕ}
    (hh : 0 < h) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ d₁ → h < p) (hprod : d₁ * d₂ ≤ x) :
    ((shiftedDivisibilitySet x h d₁ d₂).card : ℝ) ≤
      2 * x / (d₁ * d₂) := by
  have hcard := shiftedDivisibilitySet_card_le (x := x) hh hd₁ hd₂ hlarge
  have hcardCast : ((shiftedDivisibilitySet x h d₁ d₂).card : ℝ) ≤
      ((x / (d₁ * d₂) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hdiv : ((x / (d₁ * d₂) : ℕ) : ℝ) ≤ (x : ℝ) / (d₁ * d₂) :=
    by simpa only [Nat.cast_mul] using
      (Nat.cast_div_le (α := ℝ) (m := x) (n := d₁ * d₂))
  have hden : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by positivity
  have hone : (1 : ℝ) ≤ (x : ℝ) / (d₁ * d₂) := by
    rw [le_div_iff₀ hden]
    norm_num
    exact_mod_cast hprod
  calc
    ((shiftedDivisibilitySet x h d₁ d₂).card : ℝ) ≤
        ((x / (d₁ * d₂) + 1 : ℕ) : ℝ) := hcardCast
    _ = ((x / (d₁ * d₂) : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ (x : ℝ) / (d₁ * d₂) + 1 := by linarith
    _ ≤ 2 * x / (d₁ * d₂) := by
      rw [mul_div_assoc]
      nlinarith

theorem sqrt_lt_left_or_right_of_lt_mul {x d₁ d₂ : ℕ} (hprod : x < d₁ * d₂) :
    x.sqrt < d₁ ∨ x.sqrt < d₂ := by
  by_contra h
  push Not at h
  have hmul : d₁ * d₂ ≤ x.sqrt * x.sqrt := Nat.mul_le_mul h.1 h.2
  exact (Nat.not_lt_of_ge (hmul.trans (Nat.sqrt_le x))) hprod

/-- Every large-product pair is charged to at least one strict square-root tail.-/
theorem largePairSum_le_tailPairSums (x h : ℕ) :
    W.largePairSum x h ≤
      W.leftTailPairSum x h x.sqrt + W.rightTailPairSum x h x.sqrt := by
  classical
  let term : ℕ → ℕ → ℝ := fun d₁ d₂ ↦
    W.weight d₁ * W.weight d₂ * (shiftedDivisibilitySet x h d₁ d₂).card
  have hterm : ∀ d₁ ∈ W.support, ∀ d₂ ∈ W.support, 0 ≤ term d₁ d₂ := by
    intro d₁ hd₁ d₂ hd₂
    exact mul_nonneg
      (mul_nonneg (W.weight_nonneg d₁ hd₁) (W.weight_nonneg d₂ hd₂)) (by positivity)
  unfold largePairSum leftTailPairSum rightTailPairSum
  change (∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with x < d₁ * d₂, term d₁ d₂) ≤ _
  calc
    (∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with x < d₁ * d₂, term d₁ d₂) ≤
        ∑ d₁ ∈ W.support, (
          (if x.sqrt < d₁ then ∑ d₂ ∈ W.support, term d₁ d₂ else 0) +
            ∑ d₂ ∈ W.support with x.sqrt < d₂, term d₁ d₂) := by
      apply Finset.sum_le_sum
      intro d₁ hd₁
      by_cases htail : x.sqrt < d₁
      · rw [ite_eq_left htail]
        have hleft : (∑ d₂ ∈ W.support with x < d₁ * d₂, term d₁ d₂) ≤
            ∑ d₂ ∈ W.support, term d₁ d₂ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun d₂ hd₂ _ ↦ hterm d₁ hd₁ d₂ hd₂)
        have hright : 0 ≤ ∑ d₂ ∈ W.support with x.sqrt < d₂, term d₁ d₂ :=
          Finset.sum_nonneg fun d₂ hd₂ ↦
            hterm d₁ hd₁ d₂ (Finset.mem_filter.mp hd₂).1
        linarith
      · rw [ite_eq_right htail, zero_add]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d₂ hd₂
          have hd₂mem := (Finset.mem_filter.mp hd₂).1
          have hprod := (Finset.mem_filter.mp hd₂).2
          exact Finset.mem_filter.mpr ⟨hd₂mem,
            (sqrt_lt_left_or_right_of_lt_mul hprod).resolve_left htail⟩
        · intro d₂ hd₂ _
          exact hterm d₁ hd₁ d₂ (Finset.mem_filter.mp hd₂).1
    _ = (∑ d₁ ∈ W.support with x.sqrt < d₁, ∑ d₂ ∈ W.support, term d₁ d₂) +
          ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with x.sqrt < d₂, term d₁ d₂ := by
      rw [Finset.sum_add_distrib, Finset.sum_filter]

theorem Icc_filter_dvd_card_eq_div (x d : ℕ) :
    ((Finset.Icc 1 x).filter (d ∣ ·)).card = x / d := by
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp
    omega
  rw [hinterval]
  exact Nat.Ioc_filter_dvd_card_eq_div x d

theorem sum_dvd_indicator_eq (x d : ℕ) (a : ℝ) :
    (∑ n ∈ Finset.Icc 1 x, if d ∣ n then a else 0) = a * (x / d : ℕ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 x, if d ∣ n then a else 0) =
        ∑ n ∈ (Finset.Icc 1 x).filter (d ∣ ·), a := by
      exact (Finset.sum_filter (s := Finset.Icc 1 x) (d ∣ ·) (fun _ ↦ a)).symm
    _ = a * ((Finset.Icc 1 x).filter (d ∣ ·)).card := by simp [mul_comm]
    _ = a * (x / d : ℕ) := by rw [Icc_filter_dvd_card_eq_div]

/-- The elementary reciprocal-mass estimate for one divisor sum.-/
theorem sum_eval_le_mul_mass (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, W.eval n) ≤ x * W.mass := by
  classical
  unfold eval mass
  rw [Finset.sum_comm]
  calc
    (∑ d ∈ W.support, ∑ n ∈ Finset.Icc 1 x,
        if d ∣ n then W.weight d else 0) =
        ∑ d ∈ W.support, W.weight d * (x / d : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_dvd_indicator_eq x d (W.weight d)
    _ ≤ ∑ d ∈ W.support, x * (W.weight d / d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hcast : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := by
        simpa using (Nat.cast_div_le (α := ℝ) (m := x) (n := d))
      calc
        W.weight d * (x / d : ℕ) ≤ W.weight d * ((x : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hcast (W.weight_nonneg d hd)
        _ = x * (W.weight d / d) := by
          field_simp [W.support_ne_zero hd]
    _ = x * ∑ d ∈ W.support, W.weight d / d := by rw [Finset.mul_sum]

theorem leftTailPairSum_eq_sum (x h H : ℕ) :
    W.leftTailPairSum x h H =
      ∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval n * W.eval (n + h) := by
  symm
  rw [sum_eval_mul_eval_eq_pair_sum_two, Finset.sum_comm]
  rfl

theorem rightTailPairSum_eq_sum (x h H : ℕ) :
    W.rightTailPairSum x h H =
      ∑ n ∈ Finset.Icc 1 x, W.eval n * (W.restrictAbove H).eval (n + h) := by
  symm
  rw [sum_eval_mul_eval_eq_pair_sum_two, Finset.sum_comm]
  rfl

/-- Translating `[1,x]` by `h ≤ x` embeds it in `[1,2x]`, so a shifted divisor sum is controlled by the ordinary reciprocal-mass estimate at `2x`.-/
theorem sum_restrictAbove_eval_shift_le {x h H : ℕ} (hhx : h ≤ x) :
    (∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval (n + h)) ≤
      2 * x * W.tailMass H := by
  classical
  let e : ℕ ↪ ℕ := addRightEmbedding h
  have hsubset : (Finset.Icc 1 x).map e ⊆ Finset.Icc 1 (2 * x) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hm
    have hnIcc := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    change 1 ≤ n + h ∧ n + h ≤ 2 * x
    omega
  calc
    (∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval (n + h)) =
        ∑ m ∈ (Finset.Icc 1 x).map e, (W.restrictAbove H).eval m := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ m ∈ Finset.Icc 1 (2 * x), (W.restrictAbove H).eval m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun m hm _ ↦ (W.restrictAbove H).eval_nonneg m)
    _ ≤ 2 * x * (W.restrictAbove H).mass := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (W.restrictAbove H).sum_eval_le_mul_mass (2 * x)
    _ = 2 * x * W.tailMass H := by rw [W.restrictAbove_mass]

theorem leftTailPairSum_le {x h H : ℕ} {M : ℝ} (hhx : h ≤ x) (hMnonneg : 0 ≤ M)
    (hM : ∀ N : ℕ, 1 ≤ N → N ≤ 2 * x → W.eval N ≤ M) :
    W.leftTailPairSum x h H ≤ x * M * W.tailMass H := by
  rw [W.leftTailPairSum_eq_sum]
  calc
    (∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval n * W.eval (n + h)) ≤
        ∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval n * M := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc := Finset.mem_Icc.mp hn
      exact mul_le_mul_of_nonneg_left
        (hM (n + h) (by omega) (by omega)) ((W.restrictAbove H).eval_nonneg n)
    _ = (∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval n) * M := by
      rw [Finset.sum_mul]
    _ ≤ (x * (W.restrictAbove H).mass) * M :=
      mul_le_mul_of_nonneg_right ((W.restrictAbove H).sum_eval_le_mul_mass x) hMnonneg
    _ = x * M * W.tailMass H := by
      rw [W.restrictAbove_mass]
      ring

theorem rightTailPairSum_le {x h H : ℕ} {M : ℝ} (hhx : h ≤ x) (hMnonneg : 0 ≤ M)
    (hM : ∀ N : ℕ, 1 ≤ N → N ≤ 2 * x → W.eval N ≤ M) :
    W.rightTailPairSum x h H ≤ 2 * x * M * W.tailMass H := by
  rw [W.rightTailPairSum_eq_sum]
  calc
    (∑ n ∈ Finset.Icc 1 x, W.eval n * (W.restrictAbove H).eval (n + h)) ≤
        ∑ n ∈ Finset.Icc 1 x, M * (W.restrictAbove H).eval (n + h) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc := Finset.mem_Icc.mp hn
      exact mul_le_mul_of_nonneg_right
        (hM n hnIcc.1 (by omega)) ((W.restrictAbove H).eval_nonneg (n + h))
    _ = M * (∑ n ∈ Finset.Icc 1 x, (W.restrictAbove H).eval (n + h)) := by
      rw [Finset.mul_sum]
    _ ≤ M * (2 * x * W.tailMass H) :=
      mul_le_mul_of_nonneg_left (W.sum_restrictAbove_eval_shift_le hhx) hMnonneg
    _ = 2 * x * M * W.tailMass H := by ring

theorem sum_eval_mul_eval_eq_small_add_large (x h : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h)) =
      W.smallPairSum x h + W.largePairSum x h := by
  classical
  rw [W.sum_eval_mul_eval_eq_pair_sum]
  unfold smallPairSum largePairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  symm
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not W.support (fun d₂ ↦ d₁ * d₂ ≤ x)
      (fun d₂ ↦ W.weight d₁ * W.weight d₂ *
        (shiftedDivisibilitySet x h d₁ d₂).card))

/-- The `d₁d₂ ≤ x` part of Lemma 2.4 contributes at most `2xΛ²`.-/
theorem smallPairSum_le_two_mul_mass_sq {x h : ℕ} (hh : 0 < h)
    (hlarge : ∀ d ∈ W.support, 0 < W.weight d →
      ∀ p : ℕ, p.Prime → p ∣ d → h < p) :
    W.smallPairSum x h ≤ 2 * x * W.mass ^ 2 := by
  classical
  unfold smallPairSum
  calc
    (∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with d₁ * d₂ ≤ x,
        W.weight d₁ * W.weight d₂ *
          (shiftedDivisibilitySet x h d₁ d₂).card) ≤
        ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support with d₁ * d₂ ≤ x,
          2 * x * (W.weight d₁ / d₁) * (W.weight d₂ / d₂) := by
      apply Finset.sum_le_sum
      intro d₁ hd₁
      apply Finset.sum_le_sum
      intro d₂ hd₂
      have hd₂mem := (Finset.mem_filter.mp hd₂).1
      have hprod := (Finset.mem_filter.mp hd₂).2
      by_cases hw₁ : W.weight d₁ = 0
      · simp [hw₁]
      by_cases hw₂ : W.weight d₂ = 0
      · simp [hw₂]
      have hw₁pos : 0 < W.weight d₁ :=
        lt_of_le_of_ne (W.weight_nonneg d₁ hd₁) (Ne.symm hw₁)
      have hw₂pos : 0 < W.weight d₂ :=
        lt_of_le_of_ne (W.weight_nonneg d₂ hd₂mem) (Ne.symm hw₂)
      have hcount := shiftedDivisibilitySet_card_cast_le_two_mul_div
        hh (W.support_pos d₁ hd₁) (W.support_pos d₂ hd₂mem)
        (hlarge d₁ hd₁ hw₁pos) hprod
      calc
        W.weight d₁ * W.weight d₂ *
            (shiftedDivisibilitySet x h d₁ d₂).card ≤
            W.weight d₁ * W.weight d₂ * (2 * x / (d₁ * d₂)) :=
          mul_le_mul_of_nonneg_left hcount (mul_nonneg hw₁pos.le hw₂pos.le)
        _ = 2 * x * (W.weight d₁ / d₁) * (W.weight d₂ / d₂) := by
          field_simp [W.support_ne_zero hd₁, W.support_ne_zero hd₂mem]
    _ ≤ ∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support,
          2 * x * (W.weight d₁ / d₁) * (W.weight d₂ / d₂) := by
      apply Finset.sum_le_sum
      intro d₁ hd₁
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d₂ hd₂ _ ↦
          mul_nonneg
            (mul_nonneg (by positivity)
              (div_nonneg (W.weight_nonneg d₁ hd₁) (Nat.cast_nonneg d₁)))
            (div_nonneg (W.weight_nonneg d₂ hd₂) (Nat.cast_nonneg d₂)))
    _ = 2 * x * W.mass ^ 2 := by
      unfold mass
      calc
        (∑ d₁ ∈ W.support, ∑ d₂ ∈ W.support,
            2 * x * (W.weight d₁ / d₁) * (W.weight d₂ / d₂)) =
            ∑ d₁ ∈ W.support,
              (2 * x * (W.weight d₁ / d₁)) *
                (∑ d₂ ∈ W.support, W.weight d₂ / d₂) := by
          apply Finset.sum_congr rfl
          intro d₁ hd₁
          rw [Finset.mul_sum]
        _ = (2 * x) * (∑ d₁ ∈ W.support, W.weight d₁ / d₁) *
              (∑ d₂ ∈ W.support, W.weight d₂ / d₂) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = 2 * x * (∑ d ∈ W.support, W.weight d / d) ^ 2 := by ring

/-- Lemma 2.4, in the exact finite-support form used by the supplier weights.-/
theorem shifted_divisor_convolution {x h : ℕ} {M : ℝ} (hh : 0 < h) (hhx : h ≤ x)
    (hMnonneg : 0 ≤ M)
    (hM : ∀ N : ℕ, 1 ≤ N → N ≤ 2 * x → W.eval N ≤ M)
    (hlarge : ∀ d ∈ W.support, 0 < W.weight d →
      ∀ p : ℕ, p.Prime → p ∣ d → h < p) :
    (∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h)) ≤
      2 * x * W.mass ^ 2 + 4 * x * M * W.tailMass x.sqrt := by
  rw [W.sum_eval_mul_eval_eq_small_add_large]
  have hsmall := W.smallPairSum_le_two_mul_mass_sq (x := x) hh hlarge
  have hlargePairs := W.largePairSum_le_tailPairSums x h
  have hleft := W.leftTailPairSum_le hhx hMnonneg hM (H := x.sqrt)
  have hright := W.rightTailPairSum_le hhx hMnonneg hM (H := x.sqrt)
  have htailNonneg : 0 ≤ (x : ℝ) * M * W.tailMass x.sqrt := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg x) hMnonneg) (W.tailMass_nonneg x.sqrt)
  calc
    W.smallPairSum x h + W.largePairSum x h ≤
        2 * x * W.mass ^ 2 +
          (W.leftTailPairSum x h x.sqrt + W.rightTailPairSum x h x.sqrt) :=
      add_le_add hsmall hlargePairs
    _ ≤ 2 * x * W.mass ^ 2 +
          (x * M * W.tailMass x.sqrt + 2 * x * M * W.tailMass x.sqrt) :=
      add_le_add (le_refl _) (add_le_add hleft hright)
    _ ≤ 2 * x * W.mass ^ 2 + 4 * x * M * W.tailMass x.sqrt := by
      nlinarith

/-- Lemma 2.4 with `M` instantiated by the paper's literal maximum norm.-/
theorem shifted_divisor_convolution_supNorm {x h : ℕ} (hh : 0 < h) (hhx : h ≤ x)
    (hlarge : ∀ d ∈ W.support, 0 < W.weight d →
      ∀ p : ℕ, p.Prime → p ∣ d → h < p) :
    (∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h)) ≤
      2 * x * W.mass ^ 2 +
        4 * x * W.supNorm (2 * x) * W.tailMass x.sqrt := by
  have hx : 1 ≤ x := by omega
  apply W.shifted_divisor_convolution hh hhx (W.supNorm_nonneg (by omega))
  · intro N hN1 hN2
    exact W.eval_le_supNorm (Finset.mem_Icc.mpr ⟨hN1, hN2⟩)
  · exact hlarge

end FiniteDivisorWeight

end

end RankAmplification
