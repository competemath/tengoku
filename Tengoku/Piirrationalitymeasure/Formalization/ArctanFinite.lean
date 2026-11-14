import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Signed strict alternating remainders and the finite Machin certificate from Appendix A.5. -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def arctanTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)

noncomputable def arctanPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1) ^ j * arctanTerm x j

theorem arctanTerm_strictAnti {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    StrictAnti (arctanTerm x) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  unfold arctanTerm
  have hn : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hn' : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  calc
    _ ≤ x ^ (2 * n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hn'.le
      exact pow_le_pow_of_le_one hx.le hx1.le (by omega)
    _ < _ := div_lt_div_of_pos_left (pow_pos hx _) hn (by push_cast; linarith)

theorem arctanPartial_tendsto {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (arctanPartial x) atTop (𝓝 (Real.arctan x)) := by
  have h := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs, abs_of_pos hx])
  convert! h.tendsto_sum_nat using 1
  funext N
  apply Finset.sum_congr rfl
  intro j hj
  simp only [arctanTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_div_assoc]

theorem arctanPartial_succ (x : ℝ) (N : ℕ) :
    arctanPartial x (N + 1) = arctanPartial x N + (-1) ^ N * arctanTerm x N := by
  exact Finset.sum_range_succ _ _

theorem arctanPartial_even_odd {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (k : ℕ) :
    arctanPartial x (2 * k) < Real.arctan x ∧
      Real.arctan x < arctanPartial x (2 * k + 1) := by
  have hanti := arctanTerm_strictAnti hx hx1
  have hlim := arctanPartial_tendsto hx hx1
  have hL := hanti.antitone.alternating_series_le_tendsto hlim (k + 1)
  have hU := hanti.antitone.tendsto_le_alternating_series hlim (k + 1)
  change arctanPartial x (2 * (k + 1)) ≤ _ at hL
  change _ ≤ arctanPartial x (2 * (k + 1) + 1) at hU
  have hstep : arctanPartial x (2 * (k + 1)) = arctanPartial x (2 * k) +
      arctanTerm x (2 * k) - arctanTerm x (2 * k + 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      arctanPartial_succ, arctanPartial_succ]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
      mul_neg_one, neg_one_mul]
    ring
  have hstep' : arctanPartial x (2 * (k + 1) + 1) = arctanPartial x (2 * k + 1) -
      arctanTerm x (2 * k + 1) + arctanTerm x (2 * k + 2) := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega,
      arctanPartial_succ, arctanPartial_succ]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
      mul_neg_one, neg_one_mul]
    ring
  rw [hstep] at hL
  rw [hstep'] at hU
  constructor
  · linarith [hanti (show 2 * k < 2 * k + 1 by omega)]
  · linarith [hanti (show 2 * k + 1 < 2 * k + 2 by omega)]

theorem arctanPartial_signed_remainder {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    0 < (-1) ^ N * (Real.arctan x - arctanPartial x N) ∧
      (-1) ^ N * (Real.arctan x - arctanPartial x N) <
        x ^ (2 * N + 1) / (2 * (N : ℝ) + 1) := by
  change 0 < (-1) ^ N * (Real.arctan x - arctanPartial x N) ∧
    (-1) ^ N * (Real.arctan x - arctanPartial x N) < arctanTerm x N
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hN
    obtain ⟨hL, hU⟩ := arctanPartial_even_odd hx hx1 k
    rw [arctanPartial_succ] at hU
    simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul] at hU ⊢
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hN
    have hU := (arctanPartial_even_odd hx hx1 k).2
    have hL := (arctanPartial_even_odd hx hx1 (k + 1)).1
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, arctanPartial_succ] at hL
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, neg_one_mul] at hL ⊢
    constructor <;> linarith

theorem machin_identity :
    Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  simp only [← one_div] at h
  linarith

def arctanPartialRat (x : ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, (-1) ^ j * x ^ (2 * j + 1) / (2 * (j : ℚ) + 1)

theorem arctanPartialRat_cast (x : ℚ) (N : ℕ) :
    (arctanPartialRat x N : ℝ) = arctanPartial x N := by
  unfold arctanPartialRat arctanPartial arctanTerm
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem machin40_rational_bounds :
    (314159265358979323846 : ℚ) / 10 ^ 20 <
      16 * arctanPartialRat (1 / 5) 40 - 4 * arctanPartialRat (1 / 239) 40 -
        4 * (1 / 239) ^ 81 / 81 ∧
    16 * arctanPartialRat (1 / 5) 40 - 4 * arctanPartialRat (1 / 239) 40 +
      16 * (1 / 5) ^ 81 / 81 < (314159265358979323847 : ℚ) / 10 ^ 20 := by
  decide +kernel

theorem machin40_pi_bounds :
    (314159265358979323846 : ℝ) / 10 ^ 20 < Real.pi ∧
      Real.pi < (314159265358979323847 : ℝ) / 10 ^ 20 := by
  have h5 := arctanPartial_signed_remainder (x := 1 / 5) (by norm_num) (by norm_num) 40
  have h239 := arctanPartial_signed_remainder (x := 1 / 239) (by norm_num) (by norm_num) 40
  norm_num at h5 h239
  have hnum : (314159265358979323846 : ℝ) / 10 ^ 20 <
      16 * arctanPartial (1 / 5) 40 - 4 * arctanPartial (1 / 239) 40 -
        4 * (1 / 239) ^ 81 / 81 ∧
      16 * arctanPartial (1 / 5) 40 - 4 * arctanPartial (1 / 239) 40 +
        16 * (1 / 5) ^ 81 / 81 < (314159265358979323847 : ℝ) / 10 ^ 20 := by
    have h := machin40_rational_bounds
    have h' := (Rat.cast_lt (K := ℝ)).mpr h.1
    have h'' := (Rat.cast_lt (K := ℝ)).mpr h.2
    push_cast at h' h''
    norm_num only [arctanPartialRat_cast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h' h''
    constructor
    · convert! h' using 1 <;> norm_num
    · convert! h'' using 1 <;> norm_num
  rw [machin_identity]
  constructor <;> linarith [hnum.1, hnum.2]

theorem sqrt_three_paper_bounds :
    (17320508075688772935 : ℝ) / 10 ^ 19 < Real.sqrt 3 ∧
      Real.sqrt 3 < (17320508075688772936 : ℝ) / 10 ^ 19 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  · apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num

end PiIrrationality
