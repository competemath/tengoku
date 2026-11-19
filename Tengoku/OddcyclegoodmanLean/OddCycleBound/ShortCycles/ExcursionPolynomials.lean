import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.SymmetricPoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Excursion polynomials of the short odd cycles (Proposition 4.1)

Closed forms of the excursion polynomials `P_{m,r}(q; λ₁, …, λ_r) = multiKernel m r q [λ₁, …, λ_r]`
for `m ∈ {3, 5, 7}`, the completed squares of the paper (for `P_{7,1}` with the denominator `D(q)`
cleared), and their pointwise nonnegativity for `q ≤ 1/2` and all real `λᵢ`.
-/

open scoped BigOperators

namespace OddCycleBound

open DenseRegion

lemma hsym_zero_right : ∀ L : List ℝ, hsym L 0 = 1
  | [] => rfl
  | x :: L => by rw [hsym_cons]; simp [hsym_zero_right L]

lemma hsym_one_right : ∀ L : List ℝ, hsym L 1 = L.sum
  | [] => rfl
  | x :: L => by
      rw [hsym_cons, Finset.sum_range_succ, Finset.sum_range_one]
      simp [hsym_zero_right, hsym_one_right L, add_comm]

lemma multiKernel_three_one (q ℓ : ℝ) : multiKernel 3 1 q [ℓ] = 2 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

lemma multiKernel_five_one (q ℓ : ℝ) :
    multiKernel 5 1 q [ℓ] = 4 * ℓ ^ 2 + (8 * q - 5) * ℓ + 12 * q ^ 2 - 15 * q + 5 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

lemma multiKernel_five_one_sq (q ℓ : ℝ) :
    multiKernel 5 1 q [ℓ] = 4 * (ℓ + q - 5 / 8) ^ 2 + 8 * (q - 5 / 8) ^ 2 + 5 / 16 := by
  rw [multiKernel_five_one]
  ring

lemma multiKernel_five_two (q ℓ₁ ℓ₂ : ℝ) : multiKernel 5 2 q [ℓ₁, ℓ₂] = 4 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

lemma multiKernel_seven_one (q ℓ : ℝ) :
    multiKernel 7 1 q [ℓ] =
      6 * ℓ ^ 4 + (12 * q - 7) * ℓ ^ 3 + (18 * q ^ 2 - 21 * q + 7) * ℓ ^ 2
        + (24 * q ^ 3 - 42 * q ^ 2 + 28 * q - 7) * ℓ
        + (30 * q ^ 4 - 70 * q ^ 3 + 70 * q ^ 2 - 35 * q + 7) := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

/-- The polynomial `D(q)` of Proposition 4.1.-/
noncomputable def shortD (q : ℝ) : ℝ := 288 * q ^ 2 - 336 * q + 119

/-- The polynomial `C(q)` of Proposition 4.1.-/
noncomputable def shortC (q : ℝ) : ℝ := 24 * q ^ 3 - 42 * q ^ 2 + 28 * q - 7

/-- The polynomial `N(q)` of Proposition 4.1.-/
noncomputable def shortN (q : ℝ) : ℝ :=
  5184 * q ^ 6 - 18144 * q ^ 5 + 28602 * q ^ 4 - 25802 * q ^ 3 + 13874 * q ^ 2 - 4165 * q + 539

/-- The completed square for `P_{7,1}`, with the denominator `D(q)` cleared.-/
lemma multiKernel_seven_one_sq (q ℓ : ℝ) :
    24 * shortD q * multiKernel 7 1 q [ℓ] =
      shortD q * (12 * ℓ ^ 2 + (12 * q - 7) * ℓ) ^ 2 + (shortD q * ℓ + 12 * shortC q) ^ 2
        + 24 * shortN q := by
  rw [multiKernel_seven_one]
  unfold shortD shortC shortN
  ring

lemma shortD_eq (q : ℝ) : shortD q = 2 * (12 * q - 7) ^ 2 + 21 := by
  unfold shortD; ring

lemma shortD_pos (q : ℝ) : 0 < shortD q := by
  rw [shortD_eq]; positivity

lemma shortN_eq (q : ℝ) :
    8 * shortN q =
      41472 * (1 / 2 - q) ^ 6 + 20736 * (1 / 2 - q) ^ 5 + 21456 * (1 / 2 - q) ^ 4
        + 7984 * (1 / 2 - q) ^ 3 + 2032 * (1 / 2 - q) ^ 2 + 316 * (1 / 2 - q) + 11 := by
  unfold shortN; ring

lemma shortN_pos {q : ℝ} (hq : q ≤ 1 / 2) : 0 < shortN q := by
  have hy : 0 ≤ 1 / 2 - q := by linarith
  have h8 := shortN_eq q
  have : 0 < 8 * shortN q := by rw [h8]; positivity
  linarith

lemma multiKernel_seven_two (q ℓ₁ ℓ₂ : ℝ) :
    multiKernel 7 2 q [ℓ₁, ℓ₂] =
      3 / 2 * (ℓ₁ - ℓ₂) ^ 2 + 9 / 2 * (ℓ₁ + ℓ₂ + 2 * q - 7 / 6) ^ 2
        + 18 * (q - 7 / 12) ^ 2 + 7 / 4 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

lemma multiKernel_seven_three (q ℓ₁ ℓ₂ ℓ₃ : ℝ) : multiKernel 7 3 q [ℓ₁, ℓ₂, ℓ₃] = 6 := by
  unfold multiKernel
  norm_num [hsym_zero_right, hsym_one_right, List.replicate]
  ring

lemma multiKernel_seven_one_pos {q : ℝ} (hq : q ≤ 1 / 2) (ℓ : ℝ) :
    0 < multiKernel 7 1 q [ℓ] := by
  have hD := shortD_pos q
  have hN := shortN_pos hq
  have hsq := multiKernel_seven_one_sq q ℓ
  have h24 : 0 < 24 * shortD q * multiKernel 7 1 q [ℓ] := by
    rw [hsq]; positivity
  have h24D : 0 < 24 * shortD q := by positivity
  exact pos_of_mul_pos_right h24 h24D.le

/-- **Proposition 4.1.** For `m ∈ {3, 5, 7}` and `1 ≤ r ≤ (m - 1)/2`, the excursion polynomial
`P_{m,r}(q; λ₁, …, λ_r)` is nonnegative for every `q ≤ 1/2` and all real `λᵢ`. The hypothesis
`0 ≤ q` of the paper is not needed.-/
theorem multiKernel_nonneg_short {m r : ℕ} (hm : m = 3 ∨ m = 5 ∨ m = 7) (hr : 1 ≤ r)
    (h2r : 2 * r < m) {q : ℝ} (_hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (L : List ℝ)
    (hlen : L.length = r) : 0 ≤ multiKernel m r q L := by
  rcases hm with rfl | rfl | rfl
  · obtain rfl : r = 1 := by omega
    obtain ⟨ℓ, rfl⟩ := List.length_eq_one_iff.mp hlen
    rw [multiKernel_three_one]; norm_num
  · obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · obtain ⟨ℓ, rfl⟩ := List.length_eq_one_iff.mp hlen
      rw [multiKernel_five_one_sq]; positivity
    · obtain ⟨ℓ₁, ℓ₂, rfl⟩ := List.length_eq_two.mp hlen
      rw [multiKernel_five_two]; norm_num
  · obtain rfl | rfl | rfl : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    · obtain ⟨ℓ, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact (multiKernel_seven_one_pos hq ℓ).le
    · obtain ⟨ℓ₁, ℓ₂, rfl⟩ := List.length_eq_two.mp hlen
      rw [multiKernel_seven_two]; positivity
    · obtain ⟨ℓ₁, ℓ₂, ℓ₃, rfl⟩ := List.length_eq_three.mp hlen
      rw [multiKernel_seven_three]; norm_num

end OddCycleBound
