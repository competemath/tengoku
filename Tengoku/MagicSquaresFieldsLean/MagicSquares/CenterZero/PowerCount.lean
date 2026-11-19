import Tengoku.MagicSquaresFieldsLean.MagicSquares.Characters.SplitPowerCount
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.Distinct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact Section 12 character-sum error constant.-/
def centerZeroC0 (d : ℕ) : ℝ := ((d : ℝ) - 1) ^ 2 * (2 * (d : ℝ) + 1)

/-- Unnormalized weight for three consecutive powers.-/
noncomputable def centerZeroPowerWeight (n d : ℕ) (x : F) : ℝ :=
  powerIndicatorNumerator n d (x - 1) * powerIndicatorNumerator n d x *
    powerIndicatorNumerator n d (x + 1)

omit [Fintype F] in
/--
@isnad1 id=le.0h4v.s4.34f86685d2c0 from=translated src=- shape=b9165939 vocab=64033b25
-/
theorem centerZeroPowerWeight_nonneg (n d : ℕ) (x : F) :
    0 ≤ centerZeroPowerWeight n d x :=
  mul_nonneg (mul_nonneg (powerIndicatorNumerator_nonneg _ _ _)
    (powerIndicatorNumerator_nonneg _ _ _)) (powerIndicatorNumerator_nonneg _ _ _)

omit [Fintype F] in
/--
@isnad1 id=le.1h4v.s5.d5aed5f331ab from=translated src=- shape=d8815f34 vocab=00f3fa9d
-/
theorem centerZeroPowerWeight_le {n d : ℕ} (hd : 0 < d) (x : F) :
    centerZeroPowerWeight n d x ≤ (d : ℝ) ^ 3 := by
  have hpair := mul_le_mul (powerIndicatorNumerator_le (n := n) hd (x - 1))
    (powerIndicatorNumerator_le (n := n) hd x)
    (powerIndicatorNumerator_nonneg n d x) (show (0 : ℝ) ≤ d by positivity)
  have h := mul_le_mul hpair (powerIndicatorNumerator_le (n := n) hd (x + 1))
    (powerIndicatorNumerator_nonneg n d (x + 1))
    (show (0 : ℝ) ≤ (d : ℝ) * d by positivity)
  simpa only [centerZeroPowerWeight, pow_succ, pow_zero, one_mul] using h

omit [Fintype F] in
/-- Each of the three zero locations contributes at most `d^2`, rather
than the general bound `d^3`.
@isnad1 id=le.2h4v.s7.6fdf9e2e9adc from=translated src=- shape=46fcf4ae vocab=3fa811d5
-/
theorem centerZeroPowerWeight_le_at_zero {n d : ℕ} (hd : 0 < d) {x : F}
    (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    centerZeroPowerWeight n d x ≤ (d : ℝ) ^ 2 := by
  have hz : powerIndicatorNumerator (F := F) n d 0 = 1 := by
    simp [powerIndicatorNumerator]
  have hp (a b : F) : powerIndicatorNumerator n d a *
      powerIndicatorNumerator n d b ≤ (d : ℝ) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul (powerIndicatorNumerator_le (n := n) hd a)
        (powerIndicatorNumerator_le (n := n) hd b)
        (powerIndicatorNumerator_nonneg n d b) (show (0 : ℝ) ≤ d by positivity)
  rcases hx with rfl | rfl | rfl
  · simpa only [centerZeroPowerWeight, neg_add_cancel, hz, mul_one] using hp (-1 - 1) (-1)
  · simpa only [centerZeroPowerWeight, zero_sub, zero_add, hz, mul_one] using hp (-1) 1
  · simpa only [centerZeroPowerWeight, sub_self, hz, one_mul] using hp 1 (1 + 1)

omit [Fintype F] in
/--
@isnad1 id=and.2h4v.s7.735b8339f528 from=translated src=- shape=79ff20b0 vocab=988432a9
-/
theorem centerZeroPowerWeight_ne_zero_forces_powers {n d : ℕ} (hn : 0 < n)
    {x : F} (hw : centerZeroPowerWeight n d x ≠ 0) :
    IsNthPower n (x - 1) ∧ IsNthPower n x ∧ IsNthPower n (x + 1) := by
  have hh : (powerIndicatorNumerator n d (x - 1) * powerIndicatorNumerator n d x) *
      powerIndicatorNumerator n d (x + 1) ≠ 0 := hw
  obtain ⟨hmx, hp⟩ := mul_ne_zero_iff.mp hh
  obtain ⟨hm, hx⟩ := mul_ne_zero_iff.mp hmx
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hm (powerIndicatorNumerator_eq_zero_of_not_power hn h)
  · by_contra h
    exact hx (powerIndicatorNumerator_eq_zero_of_not_power hn h)
  · by_contra h
    exact hp (powerIndicatorNumerator_eq_zero_of_not_power hn h)

omit [Fintype F] in
/-- The seven excluded parameters cost at most `4*d^3+3*d^2` in total.
Overlaps in small characteristic can only decrease this bound.
@isnad1 id=le.1h3v.s6.1309e6d07050 from=translated src=- shape=e258fbbd vocab=428e87e0
-/
theorem centerZeroPowerWeight_bad_sum_le {n d : ℕ} (hd : 0 < d) :
    (∑ x ∈ (centerZeroBadValues : Finset F), centerZeroPowerWeight n d x) ≤
      4 * (d : ℝ) ^ 3 + 3 * (d : ℝ) ^ 2 := by
  let z : Finset F := {(-1 : F), 0, 1}
  let b : Finset F := {(-2 : F), (-1 : F) / 2, (1 : F) / 2, 2}
  have hcover : (centerZeroBadValues : Finset F) ⊆ z ∪ b := by
    intro x hx
    simp only [mem_centerZeroBadValues] at hx
    simp only [z, b, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsum : (∑ x ∈ (centerZeroBadValues : Finset F), centerZeroPowerWeight n d x) ≤
      (∑ x ∈ z, centerZeroPowerWeight n d x) + ∑ x ∈ b, centerZeroPowerWeight n d x := by
    calc
      _ ≤ ∑ x ∈ z ∪ b, centerZeroPowerWeight n d x :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun x _ _ => centerZeroPowerWeight_nonneg _ _ _)
      _ ≤ _ := by
        have heq := Finset.sum_union_inter (s₁ := z) (s₂ := b) (f := centerZeroPowerWeight n d)
        have hnonneg : 0 ≤ ∑ x ∈ z ∩ b, centerZeroPowerWeight n d x :=
          Finset.sum_nonneg (fun x _ => centerZeroPowerWeight_nonneg _ _ _)
        linarith
  have hz : (∑ x ∈ z, centerZeroPowerWeight n d x) ≤ z.card * (d : ℝ) ^ 2 := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul z (centerZeroPowerWeight n d) ((d : ℝ) ^ 2) (by
        intro x hx
        apply centerZeroPowerWeight_le_at_zero hd
        simpa only [z, Finset.mem_insert, Finset.mem_singleton] using hx))
  have hb : (∑ x ∈ b, centerZeroPowerWeight n d x) ≤ b.card * (d : ℝ) ^ 3 := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul b (centerZeroPowerWeight n d) ((d : ℝ) ^ 3)
        (fun x _ => centerZeroPowerWeight_le hd x))
  have hzc : z.card ≤ 3 := by
    dsimp [z]
    exact Finset.card_le_three
  have hbc : b.card ≤ 4 := by
    dsimp [b]
    exact Finset.card_le_four
  have hzR : (z.card : ℝ) ≤ 3 := by exact_mod_cast hzc
  have hbR : (b.card : ℝ) ≤ 4 := by exact_mod_cast hbc
  have hz' := mul_le_mul_of_nonneg_right hzR (show (0 : ℝ) ≤ (d : ℝ) ^ 2 by positivity)
  have hb' := mul_le_mul_of_nonneg_right hbR (show (0 : ℝ) ≤ (d : ℝ) ^ 3 by positivity)
  linarith

end MagicSquares
