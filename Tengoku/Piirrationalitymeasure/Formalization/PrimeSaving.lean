import Tengoku.Piirrationalitymeasure.Formalization.PiIrrationality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000

/-!
Discrete certificates for the five index families in Section 3.1.
-/

namespace PiIrrationality

def familyI : Finset ℕ :=
  (Finset.Icc 1 371).filter (fun j => j % 2 = 1)

def familyII : Finset ℕ :=
  (Finset.Icc 2 1114).filter (fun j => j % 2 = 0)

def familyIII : Finset ℕ :=
  (Finset.Icc 373 1855).filter (fun j => j % 2 = 1)

def familyIV : Finset ℕ :=
  (Finset.Icc 1116 1856).filter (fun j => j % 2 = 0)

def familyV : Finset ℕ :=
  (Finset.Icc 1859 3713).filter (fun j => j % 2 = 1)

def indexSum (s : Finset ℕ) : ℕ := s.sum id

theorem cast_indexSum (s : Finset ℕ) :
    (indexSum s : ℚ) = s.sum (fun j => (j : ℚ)) := by
  unfold indexSum
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, Nat.cast_add]

def familyILength : ℚ :=
  (2 * (indexSum familyI : ℚ) + (familyI.card : ℚ) * 3714) / (2 * 5570 * 3714)

def familyIILength : ℚ :=
  (indexSum familyII : ℚ) / (5570 * 3714)

def familyIIILength : ℚ :=
  ((familyIII.card : ℚ) * 3714 - 2 * (indexSum familyIII : ℚ)) / (2 * 3715 * 3714)

def familyIVLength : ℚ :=
  ((familyIV.card : ℚ) * 3714 - 2 * (indexSum familyIV : ℚ)) / (2 * 3715 * 3714)

def familyVLength : ℚ :=
  (2 * (indexSum familyV : ℚ) - (familyV.card : ℚ) * 3714) / (2 * 5570 * 3714)

def firstLeftEndpoint : ℚ := 1 / 3714

def periodicSummand (ell r q : ℚ) : ℚ :=
  (r - ell) / ((q + ell) * (q + r))

theorem periodicSummand_eq_sub_inv {ell r q : ℚ}
    (hℓ : q + ell ≠ 0) (hr : q + r ≠ 0) :
    periodicSummand ell r q = 1 / (q + ell) - 1 / (q + r) := by
  unfold periodicSummand
  field_simp [hℓ, hr]
  ring

theorem periodicSummand_pos {ell r q : ℚ}
    (hℓ : 0 < q + ell) (hr : 0 < q + r) (hord : ell < r) :
    0 < periodicSummand ell r q := by
  unfold periodicSummand
  have hden : 0 < (q + ell) * (q + r) := mul_pos hℓ hr
  apply div_pos
  · linarith
  · exact hden

theorem periodicSummand_le_inv_sq {ell r q : ℚ}
    (hℓ : 0 < ell) (hord : ell < r) (hr : r ≤ 1) (hq : 1 ≤ q) :
    periodicSummand ell r q ≤ 1 / q ^ 2 := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hden : 0 < (q + ell) * (q + r) := by
    exact mul_pos (by linarith) (by linarith)
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hqpos
  apply (div_le_div_iff₀ hden hq2).2
  have hnum : r - ell ≤ 1 := by linarith
  have hprod : q ^ 2 ≤ (q + ell) * (q + r) := by
    nlinarith [mul_pos hℓ (by linarith : 0 < r)]
  calc
    (r - ell) * q ^ 2 ≤ 1 * q ^ 2 := by
      exact mul_le_mul_of_nonneg_right hnum (sq_nonneg q)
    _ ≤ 1 * ((q + ell) * (q + r)) := by
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)

theorem interval_endpoint_equiv
    {n p q ell r u : ℝ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 ≤ q) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (heq : n / p = q + u) (hell : 0 < ell) (hord : ell < r) :
    (ell ≤ u ∧ u < r) ↔
      (n / (q + r) < p ∧ p ≤ n / (q + ell)) := by
  have hqell : 0 < q + ell := by linarith
  have hqr : 0 < q + r := by linarith
  constructor
  · rintro ⟨hℓu, hur⟩
    have hleft : q + ell ≤ n / p := by linarith [heq]
    have hright : n / p < q + r := by linarith [heq]
    constructor
    · apply (div_lt_iff₀ hqr).2
      simpa [mul_comm] using (div_lt_iff₀ hp).mp hright
    · apply (le_div_iff₀ hqell).2
      simpa [mul_comm] using (le_div_iff₀ hp).mp hleft
  · rintro ⟨hleft, hright⟩
    have hright' : n / p < q + r := by
      apply (div_lt_iff₀ hp).2
      simpa [mul_comm] using (div_lt_iff₀ hqr).mp hleft
    have hleft' : q + ell ≤ n / p := by
      apply (le_div_iff₀ hp).2
      simpa [mul_comm] using (le_div_iff₀ hqell).mp hright
    constructor <;> linarith [heq]

theorem familyI_card : familyI.card = 186 := by
  decide

theorem familyII_card : familyII.card = 557 := by
  decide

theorem familyIII_card : familyIII.card = 742 := by
  decide

theorem familyIV_card : familyIV.card = 371 := by
  decide

theorem familyV_card : familyV.card = 928 := by
  decide

theorem familyI_sum : indexSum familyI = 34596 := by
  decide

theorem familyII_sum : indexSum familyII = 310806 := by
  decide

theorem familyIII_sum : indexSum familyIII = 826588 := by
  decide

theorem familyIV_sum : indexSum familyIV = 551306 := by
  decide

theorem familyV_sum : indexSum familyV = 2585408 := by
  decide

theorem familyILength_value : familyILength = 63333 / 3447830 := by
  norm_num [familyILength, familyI_sum, familyI_card]

theorem familyIILength_value : familyIILength = 93 / 6190 := by
  norm_num [familyIILength, familyII_sum]

theorem familyIIILength_value : familyIIILength = 371 / 9285 := by
  norm_num [familyIIILength, familyIII_sum, familyIII_card]

theorem familyIVLength_value : familyIVLength = 137641 / 13797510 := by
  norm_num [familyIVLength, familyIV_sum, familyIV_card]

theorem familyVLength_value : familyVLength = 215528 / 5171745 := by
  norm_num [familyVLength, familyV_sum, familyV_card]

theorem all_family_lengths_value :
    familyILength + familyIILength + familyIIILength + familyIVLength + familyVLength =
      1724689 / 13797510 := by
  rw [familyILength_value, familyIILength_value, familyIIILength_value,
    familyIVLength_value, familyVLength_value]
  norm_num

theorem firstLeftEndpoint_gt_inv_d0 : firstLeftEndpoint > (1 : ℚ) / d0 := by
  rw [d0_eq]
  norm_num [firstLeftEndpoint]

theorem family_lengths_pos :
    0 < familyILength ∧ 0 < familyIILength ∧ 0 < familyIIILength ∧
      0 < familyIVLength ∧ 0 < familyVLength := by
  rw [familyILength_value, familyIILength_value, familyIIILength_value,
    familyIVLength_value, familyVLength_value]
  norm_num

theorem all_family_lengths_pos : 0 <
    familyILength + familyIILength + familyIIILength + familyIVLength + familyVLength := by
  rw [all_family_lengths_value]
  norm_num

theorem five_family_component_count :
    familyI.card + familyII.card + familyIII.card + familyIV.card + familyV.card = 2784 := by
  norm_num [familyI_card, familyII_card, familyIII_card, familyIV_card, familyV_card]

theorem familyI_first : familyI.min' (by decide) = 1 := by
  decide

end PiIrrationality
