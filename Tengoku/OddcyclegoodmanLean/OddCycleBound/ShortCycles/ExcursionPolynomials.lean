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

/--
@isnad1 id=eq.0h1v.s4.9f39f53f45c9 from=translated src=- shape=18650b26 vocab=f5a5f4a4
-/
lemma hsym_zero_right : ∀ L : List ℝ, hsym L 0 = 1
  | [] => rfl
  | x :: L => by rw [hsym_cons]; simp [hsym_zero_right L]

/--
@isnad1 id=eq.0h1v.s4.829969073a0e from=translated src=- shape=a910d2dd vocab=7fd9af0f
-/
lemma hsym_one_right : ∀ L : List ℝ, hsym L 1 = L.sum
  | [] => rfl
  | x :: L => by
      rw [hsym_cons, Finset.sum_range_succ, Finset.sum_range_one]
      simp [hsym_zero_right, hsym_one_right L, add_comm]

/--
@isnad1 id=eq.0h2v.s4.e55fd317fd40 from=translated src=- shape=6998616c vocab=e069ebb6
-/
lemma multiKernel_three_one (q ℓ : ℝ) : multiKernel 3 1 q [ℓ] = 2 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

/--
@isnad1 id=eq.0h2v.s7.d4d8c3e84323 from=translated src=- shape=a9900c27 vocab=e7a9866a
-/
lemma multiKernel_five_one (q ℓ : ℝ) :
    multiKernel 5 1 q [ℓ] = 4 * ℓ ^ 2 + (8 * q - 5) * ℓ + 12 * q ^ 2 - 15 * q + 5 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

/--
@isnad1 id=eq.0h2v.s7.ed8c1362974f from=translated src=- shape=4148ab2a vocab=5c6e91dd
-/
lemma multiKernel_five_one_sq (q ℓ : ℝ) :
    multiKernel 5 1 q [ℓ] = 4 * (ℓ + q - 5 / 8) ^ 2 + 8 * (q - 5 / 8) ^ 2 + 5 / 16 := by
  rw [multiKernel_five_one]
  ring

/--
@isnad1 id=eq.0h3v.s5.b2ecc46046e7 from=translated src=- shape=ded1d8cc vocab=e069ebb6
-/
lemma multiKernel_five_two (q ℓ₁ ℓ₂ : ℝ) : multiKernel 5 2 q [ℓ₁, ℓ₂] = 4 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

/--
@isnad1 id=eq.0h2v.s8.76fbfbdcc86e from=translated src=- shape=cf6e511e vocab=e7a9866a
-/
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

/-- The completed square for `P_{7,1}`, with the denominator `D(q)` cleared.
@isnad1 id=eq.0h2v.s7.4125b8207d48 from=translated src=- shape=d2623f72 vocab=1f63df2c
-/
lemma multiKernel_seven_one_sq (q ℓ : ℝ) :
    24 * shortD q * multiKernel 7 1 q [ℓ] =
      shortD q * (12 * ℓ ^ 2 + (12 * q - 7) * ℓ) ^ 2 + (shortD q * ℓ + 12 * shortC q) ^ 2
        + 24 * shortN q := by
  rw [multiKernel_seven_one]
  unfold shortD shortC shortN
  ring

/--
@isnad1 id=eq.0h1v.s6.320394f57992 from=translated src=- shape=94e20779 vocab=c3230993
-/
lemma shortD_eq (q : ℝ) : shortD q = 2 * (12 * q - 7) ^ 2 + 21 := by
  unfold shortD; ring

/--
@isnad1 id=lt.0h1v.s3.3574041edc7a from=translated src=- shape=8a62b088 vocab=eecf54c0
-/
lemma shortD_pos (q : ℝ) : 0 < shortD q := by
  rw [shortD_eq]; positivity

/--
@isnad1 id=eq.0h1v.s8.957c34c6a635 from=translated src=- shape=00b87566 vocab=80bff85d
-/
lemma shortN_eq (q : ℝ) :
    8 * shortN q =
      41472 * (1 / 2 - q) ^ 6 + 20736 * (1 / 2 - q) ^ 5 + 21456 * (1 / 2 - q) ^ 4
        + 7984 * (1 / 2 - q) ^ 3 + 2032 * (1 / 2 - q) ^ 2 + 316 * (1 / 2 - q) + 11 := by
  unfold shortN; ring

/--
@isnad1 id=lt.1h1v.s5.348201dffff5 from=translated src=- shape=75fcbd95 vocab=5684611f
-/
lemma shortN_pos {q : ℝ} (hq : q ≤ 1 / 2) : 0 < shortN q := by
  have hy : 0 ≤ 1 / 2 - q := by linarith
  have h8 := shortN_eq q
  have : 0 < 8 * shortN q := by rw [h8]; positivity
  linarith

/--
@isnad1 id=eq.0h3v.s8.39ba4805edb3 from=translated src=- shape=080e8857 vocab=5c6e91dd
-/
lemma multiKernel_seven_two (q ℓ₁ ℓ₂ : ℝ) :
    multiKernel 7 2 q [ℓ₁, ℓ₂] =
      3 / 2 * (ℓ₁ - ℓ₂) ^ 2 + 9 / 2 * (ℓ₁ + ℓ₂ + 2 * q - 7 / 6) ^ 2
        + 18 * (q - 7 / 12) ^ 2 + 7 / 4 := by
  norm_num [multiKernel, hsym_cons, Finset.sum_range_succ, List.replicate]
  ring

/--
@isnad1 id=eq.0h4v.s5.9b8f474b4449 from=translated src=- shape=318f0e07 vocab=e069ebb6
-/
lemma multiKernel_seven_three (q ℓ₁ ℓ₂ ℓ₃ : ℝ) : multiKernel 7 3 q [ℓ₁, ℓ₂, ℓ₃] = 6 := by
  unfold multiKernel
  norm_num [hsym_zero_right, hsym_one_right, List.replicate]
  ring

/--
@isnad1 id=lt.1h2v.s5.eefceb0e2c80 from=translated src=- shape=84a424b7 vocab=0fa1c326
-/
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
`0 ≤ q` of the paper is not needed.
@isnad1 id=le.6h4v.s6.8fd3f2dda16c from=translated src=- shape=8591c1a3 vocab=ec22de65
-/
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
