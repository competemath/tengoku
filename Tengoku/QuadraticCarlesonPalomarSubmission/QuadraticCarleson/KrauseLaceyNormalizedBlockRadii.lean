import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveDyadicKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized radii for the paper's finite dyadic blocks

The scale index places the normalized spatial scale in `[1, 2)`. Consequently
each endpoint of the finite block is within a factor of two of the desired
fixed normalized radius. The integer exponents below retain the paper's
exact indexing.
-/

namespace QuadraticCarleson
namespace KrauseLaceyNormalizedBlockRadii

set_option autoImplicit false

/-- A single positive dilation controls every shifted dyadic radius.
@isnad1 id=and.3h3v.s8.4347dadcd7f3 from=translated src=- shape=a987a229 vocab=ff7b73ec
-/
theorem normalizedRadius_bracket (a : ℝ) (ha : 0 < a) (j k : ℤ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j + k) ≤ (2 : ℝ) ^ (k + 1) / a ∧
      (2 : ℝ) ^ (k + 1) / a ≤ 2 * (2 : ℝ) ^ (j + k) := by
  have hk : 0 ≤ (2 : ℝ) ^ k := (zpow_pos (by norm_num : (0 : ℝ) < 2) k).le
  constructor
  · apply (le_div_iff₀ ha).2
    simp only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hhigh hk]
  · apply (div_le_iff₀ ha).2
    simp only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hlow hk]

/-- The starting radius corresponds to the fixed normalized radius `1/4`.
@isnad1 id=and.3h2v.s7.996a48a9ba16 from=translated src=- shape=fabfcd0a vocab=3b688350
-/
theorem lowerRadius_bracket (a : ℝ) (ha : 0 < a) (j : ℤ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j - 3) ≤ (1 / 4 : ℝ) / a ∧
      (1 / 4 : ℝ) / a ≤ 2 * (2 : ℝ) ^ (j - 3) := by
  have h := normalizedRadius_bracket a ha j (-3) hlow hhigh
  norm_num [← sub_eq_add_neg] at h ⊢
  exact h

/-- The ending radius retains the exact integer index `B - 1` after scaling.
@isnad1 id=and.3h3v.s8.ef9db0c491e1 from=translated src=- shape=dbca68bc vocab=a34e8832
-/
theorem upperRadius_bracket (a : ℝ) (ha : 0 < a) (j : ℤ) (B : ℕ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j + (B : ℤ) - 2) ≤ (2 : ℝ) ^ ((B : ℤ) - 1) / a ∧
      (2 : ℝ) ^ ((B : ℤ) - 1) / a ≤
        2 * (2 : ℝ) ^ (j + (B : ℤ) - 2) := by
  have h := normalizedRadius_bracket a ha j ((B : ℤ) - 2) hlow hhigh
  simpa only [show j + ((B : ℤ) - 2) = j + (B : ℤ) - 2 by omega,
    show (B : ℤ) - 2 + 1 = (B : ℤ) - 1 by omega] using h

/-- Positive modulation turns the selected scale specification into the
normalization inequality required by the radius comparisons.
@isnad1 id=and.1h1v.s6.7578f771ec25 from=translated src=- shape=08815a94 vocab=34d9f71b
-/
theorem positiveModulation_scale_bracket (lam : ℝ) (hlam : 0 < lam) :
    1 ≤ Real.sqrt lam * (2 : ℝ) ^ oscillatoryScaleIndex lam 0 hlam.ne' ∧
      Real.sqrt lam * (2 : ℝ) ^ oscillatoryScaleIndex lam 0 hlam.ne' < 2 := by
  simpa only [OscillatoryScaleSpec, abs_of_pos hlam, pow_zero, zero_add,
    pow_one, mul_comm] using oscillatoryScaleIndex_spec lam 0 hlam.ne'

/--
@isnad1 id=and.1h1v.s7.dd3a3737f8e3 from=translated src=- shape=ce2166f6 vocab=5e09a6fb
-/
theorem paperBlockLowerRadius_bracket (lam : ℝ) (hlam : 0 < lam) :
    (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' - 3) ≤
      (1 / 4 : ℝ) / Real.sqrt lam ∧
    (1 / 4 : ℝ) / Real.sqrt lam ≤
      2 * (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' - 3) := by
  have h := positiveModulation_scale_bracket lam hlam
  exact lowerRadius_bracket (Real.sqrt lam) (Real.sqrt_pos.mpr hlam)
    (oscillatoryScaleIndex lam 0 hlam.ne') h.1 h.2.le

/--
@isnad1 id=and.1h2v.s7.f48ef9974f06 from=translated src=- shape=b0a2cb32 vocab=54fbffde
-/
theorem paperBlockUpperRadius_bracket (lam : ℝ) (hlam : 0 < lam) (B : ℕ) :
    (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' + (B : ℤ) - 2) ≤
      (2 : ℝ) ^ ((B : ℤ) - 1) / Real.sqrt lam ∧
    (2 : ℝ) ^ ((B : ℤ) - 1) / Real.sqrt lam ≤
      2 * (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' + (B : ℤ) - 2) := by
  have h := positiveModulation_scale_bracket lam hlam
  exact upperRadius_bracket (Real.sqrt lam) (Real.sqrt_pos.mpr hlam)
    (oscillatoryScaleIndex lam 0 hlam.ne') B h.1 h.2.le

end KrauseLaceyNormalizedBlockRadii
end QuadraticCarleson
