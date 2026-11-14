import Tengoku.Piirrationalitymeasure.Formalization.PoleIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Clearing the two Gaussian endpoint denominators using the stronger
principal Laurent coefficient estimate.
-/

namespace PiIrrationality

def endpointTwoExponent (n k : ℕ) : ℤ :=
  -(4645 * (n : ℤ)) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3

def endpointResidualTwoExponent (j k : ℕ) : ℕ :=
  (3 * j + 1) / 2 + (3 * k + 1) / 2 + 1 - j - k

/--
@isnad1 id=le.0h2v.s5.51b25d9202e2 from=translated src=- shape=15040a65 vocab=c39088b5
-/
theorem endpointResidualTwoExponent_bound (j k : ℕ) :
    j + k + 1 ≤ 2 * endpointResidualTwoExponent j k := by
  unfold endpointResidualTwoExponent
  omega

/--
@isnad1 id=eq.1h3v.s7.93f4ad9e90a2 from=translated src=- shape=558fcd51 vocab=9d53594a
-/
theorem endpoint_two_exponent_balance (n : ℕ) (hn : 1 ≤ n) (j k : ℕ) :
    endpointTwoExponent n k + ((4645 * n - 1 + (3 * j + 1) / 2 : ℕ) : ℤ) =
      ((j + k + 1 + endpointResidualTwoExponent j k : ℕ) : ℤ) := by
  unfold endpointTwoExponent endpointResidualTwoExponent
  omega

/--
@isnad1 id=ex.2h3v.s7.603aecb5ecc0 from=translated src=- shape=28baa050 vocab=ddb6dabc
-/
theorem endpoint_scaled_coefficient
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ 5570 * n) (k : ℕ) :
    ∃ w : ℤ, (5 : ℂ) ^ (k + 1) * 2 ^ endpointTwoExponent n k *
      (laurentCoeffRat n (j : ℤ) : ℂ) * (10 : ℂ) ^ (-((j + k + 1 : ℕ) : ℤ)) =
        2 ^ endpointResidualTwoExponent j k * 5 ^ (2 * n) * (w : ℂ) := by
  obtain ⟨w, hw⟩ := principal_laurentCoeffRat_integer_factors n hn j hj
  refine ⟨w, ?_⟩
  have h2 : (2 : ℂ) ^ endpointTwoExponent n k *
      2 ^ (4645 * n - 1 + (3 * j + 1) / 2) =
        2 ^ (j + k + 1) * 2 ^ endpointResidualTwoExponent j k := by
    rw [← zpow_natCast (2 : ℂ), ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      endpoint_two_exponent_balance n hn, zpow_natCast, pow_add]
  have h5 : (5 : ℂ) ^ (k + 1) * 5 ^ (2 * n + j) =
      5 ^ (j + k + 1) * 5 ^ (2 * n) := by
    simp only [← pow_add]
    congr 1
    omega
  rw [hw]
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast]
  rw [zpow_neg, zpow_natCast]
  calc
    _ = ((2 : ℂ) ^ endpointTwoExponent n k *
          2 ^ (4645 * n - 1 + (3 * j + 1) / 2)) *
        (5 ^ (k + 1) * 5 ^ (2 * n + j)) * (w : ℂ) / 10 ^ (j + k + 1) := by ring
    _ = _ := by
      rw [h2, h5, show (10 : ℂ) = 2 * 5 by norm_num, mul_pow]
      field_simp

/--
@isnad1 id=and.0h1v.s8.b9fb9984956c from=translated src=- shape=b5e34618 vocab=ec06b0ab
-/
theorem endpoint_inverse_powers (l : ℕ) :
    (1 / (4 - 2 * Complex.I) ^ l =
      (10 : ℂ) ^ (-((l : ℕ) : ℤ)) * (2 + Complex.I) ^ l) ∧
    (1 / (6 + 2 * Complex.I) ^ l =
      (10 : ℂ) ^ (-((l : ℕ) : ℤ)) * ((2 + Complex.I) / (1 + Complex.I)) ^ l) := by
  obtain ⟨h1, _, h3, _⟩ := pole_endpoints_ten_div
  constructor
  · rw [← h1, div_pow, zpow_neg, zpow_natCast]
    field_simp
  · rw [← h3, div_pow, zpow_neg, zpow_natCast]
    field_simp

/--
@isnad1 id=ex.2h3v.s8.f1007f740257 from=translated src=- shape=43ba472a vocab=5c155d46
-/
theorem endpoint_scaled_bracket_is_gaussian_integer
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ 5570 * n) (k : ℕ) :
    ∃ z : GI, (5 : ℂ) ^ (k + 1) * 2 ^ endpointTwoExponent n k *
      (laurentCoeffRat n (j : ℤ) : ℂ) *
        ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j + k + 1) +
          1 / (6 + 2 * Complex.I) ^ (j + k + 1)) = (z : ℂ) := by
  obtain ⟨w, hw⟩ := endpoint_scaled_coefficient n hn j hj k
  let l := j + k + 1
  let u := endpointResidualTwoExponent j k
  let A : GI := (-1) ^ k * 2 ^ u * 5 ^ (2 * n) * w * giTwoAddI ^ l
  let B : GI := (-giI) ^ u * giOneAddI ^ (2 * u - l) * 5 ^ (2 * n) * w * giTwoAddI ^ l
  refine ⟨A + B, ?_⟩
  obtain ⟨hleft, hright⟩ := endpoint_inverse_powers l
  have hexpr :
      (5 : ℂ) ^ (k + 1) * 2 ^ endpointTwoExponent n k *
        (laurentCoeffRat n (j : ℤ) : ℂ) *
          ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ l + 1 / (6 + 2 * Complex.I) ^ l) =
      (-1 : ℂ) ^ k * (2 ^ u * 5 ^ (2 * n) * (w : ℂ)) * (2 + Complex.I) ^ l +
        (2 ^ u * 5 ^ (2 * n) * (w : ℂ)) * ((2 + Complex.I) / (1 + Complex.I)) ^ l := by
    rw [show (-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ l =
      (-1 : ℂ) ^ k * (1 / (4 - 2 * Complex.I) ^ l) by ring, hleft, hright]
    calc
      _ = (-1 : ℂ) ^ k *
          (5 ^ (k + 1) * 2 ^ endpointTwoExponent n k *
            (laurentCoeffRat n (j : ℤ) : ℂ) * 10 ^ (-(l : ℤ))) * (2 + Complex.I) ^ l +
          (5 ^ (k + 1) * 2 ^ endpointTwoExponent n k *
            (laurentCoeffRat n (j : ℤ) : ℂ) * 10 ^ (-(l : ℤ))) *
              ((2 + Complex.I) / (1 + Complex.I)) ^ l := by ring
      _ = _ := by rw [hw]
  have hA : (A : ℂ) = (-1 : ℂ) ^ k * (2 ^ u * 5 ^ (2 * n) * (w : ℂ)) *
      (2 + Complex.I) ^ l := by
    simp only [A, map_mul, map_pow, map_neg, map_one, map_ofNat,
      map_intCast, giTwoAddI_toComplex]
    ring
  have hB : (B : ℂ) = (2 ^ u * 5 ^ (2 * n) * (w : ℂ)) *
      ((2 + Complex.I) / (1 + Complex.I)) ^ l := by
    simp only [B, map_mul, map_pow, map_neg, map_ofNat, map_intCast,
      giI_toComplex, giOneAddI_toComplex, giTwoAddI_toComplex]
    rw [← two_pow_div_one_add_I_pow l u (endpointResidualTwoExponent_bound j k), div_pow]
    ring
  rw [map_add, hA, hB]
  exact hexpr

/--
@isnad1 id=ex.3h3v.s7.12c997257d4f from=translated src=- shape=d82e6be6 vocab=23f3720e
-/
theorem gaussian_integer_of_coprime_multipliers
    (x : ℂ) (a b : ℕ) (hab : Nat.Coprime a b)
    (ha : ∃ u : GI, (a : ℂ) * x = (u : ℂ))
    (hb : ∃ v : GI, (b : ℂ) * x = (v : ℂ)) :
    ∃ z : GI, x = (z : ℂ) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain ⟨s, t, hst⟩ := hab.isCoprime
  have hstC : (s : ℂ) * (a : ℂ) + (t : ℂ) * (b : ℂ) = 1 := by
    exact_mod_cast hst
  refine ⟨(s : GI) * u + (t : GI) * v, ?_⟩
  calc
    x = ((s : ℂ) * (a : ℂ) + (t : ℂ) * (b : ℂ)) * x := by rw [hstC, one_mul]
    _ = (s : ℂ) * ((a : ℂ) * x) + (t : ℂ) * ((b : ℂ) * x) := by ring
    _ = _ := by rw [hu, hv]; simp only [map_add, map_mul, map_intCast]

end PiIrrationality
