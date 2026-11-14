import Tengoku.Piirrationalitymeasure.Formalization.EndpointArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Endpoint denominator clearing from an arbitrary principal coefficient factor. -/

namespace PiIrrationality

theorem endpoint_scaled_coefficient_of_factor (H F j k : ℕ) (hH : 0 < H)
    (z : ℚ) (w : ℤ)
    (hz : z = (2 : ℚ) ^ (H - 1 + (3 * j + 1) / 2) * 5 ^ (F + j) * (w : ℚ)) :
    ∃ w : ℤ, (5 : ℂ) ^ (k + 1) * 2 ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
      (z : ℂ) * (10 : ℂ) ^ (-((j + k + 1 : ℕ) : ℤ)) =
        2 ^ endpointResidualTwoExponent j k * 5 ^ (F) * (w : ℂ) := by
  have hw := hz
  refine ⟨w, ?_⟩
  have h2 : (2 : ℂ) ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
      2 ^ (H - 1 + (3 * j + 1) / 2) =
        2 ^ (j + k + 1) * 2 ^ endpointResidualTwoExponent j k := by
    rw [← zpow_natCast (2 : ℂ), ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      show (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) +
        ((H - 1 + (3 * j + 1) / 2 : ℕ) : ℤ) =
        ((j + k + 1 + endpointResidualTwoExponent j k : ℕ) : ℤ) by
          unfold endpointResidualTwoExponent
          omega, zpow_natCast, pow_add]
  have h5 : (5 : ℂ) ^ (k + 1) * 5 ^ (F + j) =
      5 ^ (j + k + 1) * 5 ^ (F) := by
    simp only [← pow_add]
    congr 1
    omega
  rw [hw]
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast]
  rw [zpow_neg, zpow_natCast]
  calc
    _ = ((2 : ℂ) ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
          2 ^ (H - 1 + (3 * j + 1) / 2)) *
        (5 ^ (k + 1) * 5 ^ (F + j)) * (w : ℂ) / 10 ^ (j + k + 1) := by ring
    _ = _ := by
      rw [h2, h5, show (10 : ℂ) = 2 * 5 by norm_num, mul_pow]
      field_simp

theorem endpoint_bracket_integral_of_factor (H F j k : ℕ) (hH : 0 < H)
    (z : ℚ) (w : ℤ)
    (hz : z = (2 : ℚ) ^ (H - 1 + (3 * j + 1) / 2) * 5 ^ (F + j) * (w : ℚ)) :
    ∃ G : GI, (5 : ℂ) ^ (k + 1) * 2 ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
      (z : ℂ) *
        ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j + k + 1) +
          1 / (6 + 2 * Complex.I) ^ (j + k + 1)) = (G : ℂ) := by
  obtain ⟨w, hw⟩ := endpoint_scaled_coefficient_of_factor H F j k hH z w hz
  let l := j + k + 1
  let u := endpointResidualTwoExponent j k
  let A : GI := (-1) ^ k * 2 ^ u * 5 ^ (F) * w * giTwoAddI ^ l
  let B : GI := (-giI) ^ u * giOneAddI ^ (2 * u - l) * 5 ^ (F) * w * giTwoAddI ^ l
  refine ⟨A + B, ?_⟩
  obtain ⟨hleft, hright⟩ := endpoint_inverse_powers l
  have hexpr :
      (5 : ℂ) ^ (k + 1) * 2 ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
        (z : ℂ) *
          ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ l + 1 / (6 + 2 * Complex.I) ^ l) =
      (-1 : ℂ) ^ k * (2 ^ u * 5 ^ (F) * (w : ℂ)) * (2 + Complex.I) ^ l +
        (2 ^ u * 5 ^ (F) * (w : ℂ)) * ((2 + Complex.I) / (1 + Complex.I)) ^ l := by
    rw [show (-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ l =
      (-1 : ℂ) ^ k * (1 / (4 - 2 * Complex.I) ^ l) by ring, hleft, hright]
    calc
      _ = (-1 : ℂ) ^ k *
          (5 ^ (k + 1) * 2 ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
            (z : ℂ) * 10 ^ (-(l : ℤ))) * (2 + Complex.I) ^ l +
          (5 ^ (k + 1) * 2 ^ (-(H : ℤ) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3) *
            (z : ℂ) * 10 ^ (-(l : ℤ))) *
              ((2 + Complex.I) / (1 + Complex.I)) ^ l := by ring
      _ = _ := by rw [hw]
  have hA : (A : ℂ) = (-1 : ℂ) ^ k * (2 ^ u * 5 ^ (F) * (w : ℂ)) *
      (2 + Complex.I) ^ l := by
    simp only [A, map_mul, map_pow, map_neg, map_one, map_ofNat,
      map_intCast, giTwoAddI_toComplex]
    ring
  have hB : (B : ℂ) = (2 ^ u * 5 ^ (F) * (w : ℂ)) *
      ((2 + Complex.I) / (1 + Complex.I)) ^ l := by
    simp only [B, map_mul, map_pow, map_neg, map_ofNat, map_intCast,
      giI_toComplex, giOneAddI_toComplex, giTwoAddI_toComplex]
    rw [← two_pow_div_one_add_I_pow l u (endpointResidualTwoExponent_bound j k), div_pow]
    ring
  rw [map_add, hA, hB]
  exact hexpr

end PiIrrationality
