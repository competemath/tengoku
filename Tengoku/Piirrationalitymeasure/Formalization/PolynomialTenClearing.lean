import Tengoku.Piirrationalitymeasure.Formalization.PolynomialReducedCoefficients
import Tengoku.Piirrationalitymeasure.Formalization.PolynomialClearing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The second denominator clearing (2.31), followed by the coprime
intersection (2.32). This completes Lemma 2.5 for the actual integral.
-/

namespace PiIrrationality

open Polynomial

def poleIntegralEndpointFactor (q : ℕ) : GI :=
  giI * ((upperEndpointGI + 5) ^ (q + 1) - (lowerEndpointGI + 5) ^ (q + 1))

theorem poleMonomial_integral (q : ℕ) :
    -(∫ s : ℝ in (-2)..2, (verticalSegment s + 5) ^ q) =
      (poleIntegralEndpointFactor q : ℂ) / (q + 1 : ℂ) := by
  have hd (s : ℝ) : HasDerivAt
      (fun s : ℝ => -Complex.I / (q + 1 : ℂ) * (verticalSegment s + 5) ^ (q + 1))
      ((verticalSegment s + 5) ^ q) s := by
    have h := (((((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (-1)).add_const 5).pow
      (q + 1)).const_mul (-Complex.I / (q + 1 : ℂ))
    convert h.comp_ofReal using 1
    · rfl
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul]
      have hq : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
      field_simp
      ring_nf
      simp [Complex.I_sq, verticalSegment, mul_comm, add_comm]
      congr 1
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((verticalSegment_continuous.add continuous_const).pow q).intervalIntegrable _ _)]
  have hu : verticalSegment 2 + 5 = ((upperEndpointGI + 5 : GI) : ℂ) := by
    simp [verticalSegment, map_add, map_ofNat, upperEndpointGI_cast]
  have hl : verticalSegment (-2) + 5 = ((lowerEndpointGI + 5 : GI) : ℂ) := by
    simp [verticalSegment, map_add, map_ofNat, lowerEndpointGI_cast]
    ring
  rw [hu, hl]
  simp only [poleIntegralEndpointFactor, map_mul, map_sub, map_pow, giI_toComplex]
  ring

theorem reduced_polynomial_monomial_scaled_is_gaussian_integer
    (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q < 7430 * n - 1) :
    ∃ G : GI, (10 : ℂ) ^ (7430 * n - 1) * (reducedLcm n : ℂ) *
      (poleShiftCoeff n q : ℂ) * (-(∫ s : ℝ in (-2)..2, (verticalSegment s + 5) ^ q)) =
        (G : ℂ) := by
  obtain ⟨z, hz⟩ := poleAntiderivativeScaledCoeff_is_integer n hn q hq
  have hzC := congrArg (fun x : ℚ => (x : ℂ)) hz
  unfold poleAntiderivativeScaledCoeff at hzC
  push_cast at hzC
  have hqC : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hpow : (10 : ℂ) ^ (7430 * n - 1) =
      10 ^ (7430 * n - 1 - (q + 1)) * 10 ^ (q + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  refine ⟨(10 : GI) ^ (7430 * n - 1 - (q + 1)) * (z : GI) * poleIntegralEndpointFactor q, ?_⟩
  rw [poleMonomial_integral, hpow]
  calc
    _ = (10 : ℂ) ^ (7430 * n - 1 - (q + 1)) *
        (10 ^ (q + 1) * (reducedLcm n : ℂ) * (poleShiftCoeff n q : ℂ) / (q + 1)) *
          (poleIntegralEndpointFactor q : ℂ) := by ring
    _ = _ := by rw [hzC]; simp only [map_mul, map_pow, map_ofNat, map_intCast]

theorem ten_power_reducedPolynomialIntegral_is_gaussian_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : GI, (10 : ℂ) ^ (7430 * n - 1) * (reducedLcm n : ℂ) *
      (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (polynomialPart n))) = (G : ℂ) := by
  classical
  let G (q : ℕ) : GI := if hq : q < 7430 * n - 1 then
    (reduced_polynomial_monomial_scaled_is_gaussian_integer n hn q hq).choose else 0
  refine ⟨∑ q ∈ Finset.range (7430 * n - 1), G q, ?_⟩
  simp_rw [polynomialPart_pole_expansion n hn]
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul]
    have hq' := Finset.mem_range.mp hq
    have h := (reduced_polynomial_monomial_scaled_is_gaussian_integer n hn q hq').choose_spec
    dsimp only [G]
    rw [dite_eq_left hq']
    rw [← h]
    ring
  · intro q _
    exact (continuous_const.mul
      ((verticalSegment_continuous.add continuous_const).pow q)).intervalIntegrable _ _

theorem rational_gaussian_integer_is_integer (x : ℚ)
    (h : ∃ G : GI, (x : ℂ) = (G : ℂ)) : ∃ z : ℤ, x = (z : ℚ) := by
  obtain ⟨G, hG⟩ := h
  have him : G.im = 0 := by
    have h := congrArg Complex.im hG.symm
    have hzero : (G : ℂ).im = 0 := by simpa only [Complex.ratCast_im] using h
    have hInt : ((G.im : ℤ) : ℝ) = 0 := by
      rw [GaussianInt.intCast_im]
      exact hzero
    exact_mod_cast hInt
  refine ⟨G.re, ?_⟩
  apply Rat.cast_injective (α := ℂ)
  rw [hG, GaussianInt.toComplex_def, him]
  push_cast
  ring

theorem ten_power_reducedPolynomialIntegralRat_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (10 : ℚ) ^ (7430 * n - 1) * reducedLcm n *
      verticalPolynomialIntegralRat (polynomialPart n) = (z : ℚ) := by
  apply rational_gaussian_integer_is_integer
  obtain ⟨G, hG⟩ := ten_power_reducedPolynomialIntegral_is_gaussian_integer n hn
  refine ⟨G, ?_⟩
  rw [verticalPolynomial_integral_rat] at hG
  push_cast
  exact hG

theorem normalizedPolynomialIntegral_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, normalizedPolynomialIntegral n = (z : ℂ) := by
  let x : ℚ := (2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * reducedLcm n *
    verticalPolynomialIntegralRat (polynomialPart n)
  have hx : normalizedPolynomialIntegral n = (x : ℂ) := by
    rw [normalizedPolynomialIntegral, verticalPolynomial_integral_rat]
    dsimp only [x]
    push_cast
    rfl
  have hPhi : ∃ z : ℤ, (Phi n : ℚ) * x = (z : ℚ) := by
    obtain ⟨z, hz⟩ := normalizedPolynomialIntegral_Phi_multiple_is_integer n hn
    refine ⟨z, ?_⟩
    apply Rat.cast_injective (α := ℂ)
    push_cast
    rw [← hx]
    exact hz
  have hten : ∃ K : ℕ, ∃ z : ℤ, (10 : ℚ) ^ K * x = (z : ℚ) := by
    obtain ⟨z, hz⟩ := ten_power_reducedPolynomialIntegralRat_is_integer n hn
    have h2 : (10 : ℚ) ^ (4645 * n) * 2 ^ (1 - 4645 * (n : ℤ)) =
        2 * 5 ^ (4645 * n) := by
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      calc
        _ = ((2 : ℚ) ^ (4645 * n) * 2 ^ (1 - 4645 * (n : ℤ))) * 5 ^ (4645 * n) := by ring
        _ = _ := by
          rw [← zpow_natCast (2 : ℚ) (4645 * n),
            ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
          rw [show ((4645 * n : ℕ) : ℤ) + (1 - 4645 * (n : ℤ)) = 1 by omega, zpow_one]
    refine ⟨4645 * n + (7430 * n - 1), 2 * (5 : ℤ) ^ (4645 * n) * z, ?_⟩
    dsimp only [x]
    rw [pow_add]
    calc
      _ = ((10 : ℚ) ^ (4645 * n) * 2 ^ (1 - 4645 * (n : ℤ))) *
          (10 ^ (7430 * n - 1) * reducedLcm n *
            verticalPolynomialIntegralRat (polynomialPart n)) := by ring
      _ = _ := by rw [h2, hz]; push_cast; rfl
  obtain ⟨z, hz⟩ := integer_of_Phi_and_ten_power n x hPhi hten
  refine ⟨z, ?_⟩
  rw [hx, hz]
  push_cast
  rfl

end PiIrrationality
