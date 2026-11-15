import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist

namespace TateCurve

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

private theorem norm_add_le_max' (a b : K) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  exact_mod_cast nnnorm_add_le_max a b

private theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using norm_add_le_max' a (-b)

noncomputable def xDivTerm (u : K) (d : ℕ) : K := (d : K) * (u ^ d + u⁻¹ ^ d - 2)

noncomputable def yDivTerm (u : K) (d : ℕ) : K :=
  ((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d) - (d : K) * u⁻¹ ^ d + (d : K)

noncomputable def xCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, xDivTerm u d

noncomputable def yCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, yDivTerm u d

noncomputable def growthBound (u : K) : ℝ := max (max ‖u‖ ‖u⁻¹‖) 1

/--
@isnad1 id=le.0h2v.s5.7bd0e3a3da32 from=translated src=- shape=c83d11cb vocab=a99e7ebc
-/
theorem one_le_growthBound (u : K) : 1 ≤ growthBound u := le_max_right _ _

/--
@isnad1 id=le.0h2v.s5.89b105a79cb4 from=translated src=- shape=c83d11cb vocab=a99e7ebc
-/
theorem growthBound_nonneg (u : K) : 0 ≤ growthBound u :=
  zero_le_one.trans (one_le_growthBound u)

/--
@isnad1 id=le.0h3v.s6.46af01827b35 from=translated src=- shape=c1207b09 vocab=4050b20a
-/
theorem norm_pow_le_growthBound (u : K) (d : ℕ) : ‖u ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg u) ((le_max_left _ _).trans (le_max_left _ _)) d

/--
@isnad1 id=le.0h3v.s6.158b432835bc from=translated src=- shape=5eb16a5d vocab=3ca25ebb
-/
theorem norm_inv_pow_le_growthBound (u : K) (d : ℕ) : ‖u⁻¹ ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((le_max_right _ _).trans (le_max_left _ _)) d

/--
@isnad1 id=le.0h3v.s5.ba4a1d9777dd from=translated src=- shape=15b0968e vocab=920dcc63
-/
theorem one_le_growthBound_pow (u : K) (d : ℕ) : (1 : ℝ) ≤ growthBound u ^ d :=
  one_le_pow₀ (one_le_growthBound u)

/--
@isnad1 id=le.0h4v.s6.883b4f3710b1 from=translated src=- shape=5417af2b vocab=049bc140
-/
theorem norm_natCast_le_growthBound_pow (u : K) (k d : ℕ) :
    ‖(k : K)‖ ≤ growthBound u ^ d :=
  (IsUltrametricDist.norm_natCast_le_one K k).trans (one_le_growthBound_pow u d)

/--
@isnad1 id=le.0h3v.s5.47b5f6c0f4dd from=translated src=- shape=487c9952 vocab=2bef738a
-/
theorem norm_xDivTerm_le (u : K) (d : ℕ) : ‖xDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [xDivTerm]
  calc ‖(d : K) * (u ^ d + u⁻¹ ^ d - 2)‖
      = ‖(d : K)‖ * ‖u ^ d + u⁻¹ ^ d - 2‖ := norm_mul _ _
    _ ≤ 1 * ‖u ^ d + u⁻¹ ^ d - 2‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K d)
          (norm_nonneg _)
    _ = ‖u ^ d + (u⁻¹ ^ d - 2)‖ := by rw [one_mul, add_sub_assoc]
    _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d - 2‖ := norm_add_le_max' _ _
    _ ≤ growthBound u ^ d := by
        refine max_le (norm_pow_le_growthBound u d) ?_
        refine (norm_sub_le_max' _ _).trans
          (max_le (norm_inv_pow_le_growthBound u d) ?_)
        calc ‖(2 : K)‖ = ‖((2 : ℕ) : K)‖ := by norm_num
          _ ≤ growthBound u ^ d := norm_natCast_le_growthBound_pow u 2 d

/--
@isnad1 id=le.0h3v.s5.690adfd27dba from=translated src=- shape=487c9952 vocab=af33128b
-/
theorem norm_yDivTerm_le (u : K) (d : ℕ) : ‖yDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [yDivTerm]
  refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
  · refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · calc ‖((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d)‖
          = ‖((d.choose 2 : ℕ) : K)‖ * ‖u ^ d - u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * ‖u ^ d - u⁻¹ ^ d‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
              (norm_nonneg _)
        _ = ‖u ^ d - u⁻¹ ^ d‖ := one_mul _
        _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d‖ := norm_sub_le_max' _ _
        _ ≤ growthBound u ^ d := max_le (norm_pow_le_growthBound u d)
            (norm_inv_pow_le_growthBound u d)
    · calc ‖(d : K) * u⁻¹ ^ d‖ = ‖(d : K)‖ * ‖u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * (growthBound u ^ d) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one K d)
              (norm_inv_pow_le_growthBound u d) (norm_nonneg _) zero_le_one
        _ = growthBound u ^ d := one_mul _
  · exact norm_natCast_le_growthBound_pow u d d

end Coefficients

end TateCurve
