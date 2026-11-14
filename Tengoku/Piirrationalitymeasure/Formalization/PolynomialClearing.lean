import Tengoku.Piirrationalitymeasure.Formalization.EndpointDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The first denominator clearing in Lemma 2.5, equation (2.28).
The original LCM clears `k+1`; Lemma 2.4 clears the remaining power of two.
-/

namespace PiIrrationality

open Polynomial

noncomputable def originalNormalizedPolynomialIntegral (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * (lcmRange (7430 * n) : ℂ) *
    (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (polynomialPart n)))

noncomputable def originalNormalizedEndpointTerm (n k : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * (lcmRange (7430 * n) : ℂ) *
    Complex.I * (endpointCoeff n k : ℂ) * (4 * Complex.I) ^ (k + 1) / (k + 1 : ℂ)

theorem polynomial_integral_two_power_balance (n k : ℕ) :
    (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * 4 ^ (k + 1) =
      2 ^ (2 * k - (3 * k + 1) / 2) * 2 ^ endpointTwoExponent n k := by
  rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul,
    ← zpow_natCast (2 : ℂ) (2 * (k + 1)),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    ← zpow_natCast (2 : ℂ) (2 * k - (3 * k + 1) / 2),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  unfold endpointTwoExponent
  omega

theorem originalNormalizedEndpointTerm_is_gaussian_integer
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k < 7430 * n - 1) :
    ∃ z : GI, originalNormalizedEndpointTerm n k = (z : ℂ) := by
  obtain ⟨q, hq⟩ := dvd_lcmRange (7430 * n) (k + 1) (by omega) (by omega)
  obtain ⟨G, hG⟩ := normalizedEndpointCoeff_is_gaussian_integer n hn k
  have hqC : (lcmRange (7430 * n) : ℂ) = (k + 1 : ℂ) * (q : ℂ) := by
    exact_mod_cast hq
  have hkC : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  refine ⟨(2 : GI) ^ (2 * k - (3 * k + 1) / 2) * G * giI ^ (k + 2) * q, ?_⟩
  unfold originalNormalizedEndpointTerm
  rw [hqC, mul_pow]
  calc
    _ = ((2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * 4 ^ (k + 1)) *
        (endpointCoeff n k : ℂ) * Complex.I ^ (k + 2) * (q : ℂ) := by
      field_simp
      simp only [pow_succ]
      ring
    _ = (2 : ℂ) ^ (2 * k - (3 * k + 1) / 2) *
        normalizedEndpointCoeff n k * Complex.I ^ (k + 2) * (q : ℂ) := by
      rw [polynomial_integral_two_power_balance]
      unfold normalizedEndpointCoeff
      ring
    _ = _ := by
      rw [hG]
      simp only [map_mul, map_pow, map_ofNat, map_natCast, giI_toComplex]

theorem originalNormalizedPolynomialIntegral_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    originalNormalizedPolynomialIntegral n =
      ∑ k ∈ Finset.range (7430 * n - 1), originalNormalizedEndpointTerm n k := by
  unfold originalNormalizedPolynomialIntegral
  rw [polynomialPart_endpoint_integral n hn, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold originalNormalizedEndpointTerm
  ring

theorem originalNormalizedPolynomialIntegral_is_gaussian_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : GI, originalNormalizedPolynomialIntegral n = (z : ℂ) := by
  classical
  let z (k : ℕ) : GI := if hk : k < 7430 * n - 1 then
    (originalNormalizedEndpointTerm_is_gaussian_integer n hn k hk).choose else 0
  refine ⟨∑ k ∈ Finset.range (7430 * n - 1), z k, ?_⟩
  rw [originalNormalizedPolynomialIntegral_eq_sum n hn, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  dsimp only [z]
  rw [dite_eq_left hk']
  exact (originalNormalizedEndpointTerm_is_gaussian_integer n hn k hk').choose_spec

theorem originalNormalizedPolynomialIntegral_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, originalNormalizedPolynomialIntegral n = (z : ℂ) := by
  obtain ⟨G, hG⟩ := originalNormalizedPolynomialIntegral_is_gaussian_integer n hn
  have hrat : originalNormalizedPolynomialIntegral n =
      ((2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * (lcmRange (7430 * n) : ℚ) *
        verticalPolynomialIntegralRat (polynomialPart n) : ℚ) := by
    rw [originalNormalizedPolynomialIntegral, verticalPolynomial_integral_rat]
    push_cast
    rfl
  have him : G.im = 0 := by
    have h := congrArg Complex.im (hG.symm.trans hrat)
    have hzero : (G : ℂ).im = 0 := by simpa only [Complex.ratCast_im] using h
    have hInt : ((G.im : ℤ) : ℝ) = 0 := by
      rw [GaussianInt.intCast_im]
      exact hzero
    exact_mod_cast hInt
  refine ⟨G.re, ?_⟩
  rw [hG, GaussianInt.toComplex_def, him]
  simp

noncomputable def normalizedPolynomialIntegral (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * (reducedLcm n : ℂ) *
    (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (polynomialPart n)))

theorem normalizedPolynomialIntegral_mul_Phi (n : ℕ) :
    (Phi n : ℂ) * normalizedPolynomialIntegral n = originalNormalizedPolynomialIntegral n := by
  have h := congrArg (fun x : ℚ => (x : ℂ)) (reducedLcm_mul_Phi n)
  push_cast at h
  unfold normalizedPolynomialIntegral originalNormalizedPolynomialIntegral
  calc
    _ = (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * ((reducedLcm n : ℂ) * (Phi n : ℂ)) *
      (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (polynomialPart n))) := by ring
    _ = _ := by rw [h]

theorem normalizedPolynomialIntegral_Phi_multiple_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (Phi n : ℂ) * normalizedPolynomialIntegral n = (z : ℂ) := by
  rw [normalizedPolynomialIntegral_mul_Phi]
  exact originalNormalizedPolynomialIntegral_is_integer n hn

end PiIrrationality
