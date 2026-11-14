import Tengoku.Piirrationalitymeasure.Formalization.NormalizedCoefficient
import Tengoku.Piirrationalitymeasure.Formalization.GaussianIntegrality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The arithmetic of the nonlogarithmic endpoint expression (2.34).
-/

namespace PiIrrationality

noncomputable def poleClearedCoeff (n j : ℕ) : ℚ :=
  reducedLcm n * ((10 : ℚ) ^ (-(j : ℤ)) * laurentCoeffRat n (j : ℤ)) / j

/--
@isnad1 id=ex.3h2v.s7.ab95d3ea9902 from=translated src=- shape=c042cd01 vocab=c5c34c57
-/
theorem poleClearedCoeff_two_factor
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, poleClearedCoeff n j =
      (2 : ℚ) ^ (4645 * n - 1 + (j + 1) / 2) * (z : ℚ) := by
  obtain ⟨q, hq⟩ := (reducedLcm_actual_laurent_integrality n hn).2.1
    (j : ℤ) (by omega) (by exact_mod_cast hj) (by exact_mod_cast hj0.ne')
  change poleClearedCoeff n j = (q : ℚ) at hq
  obtain ⟨w, hw⟩ := principal_scaled_laurentCoeffRat_integer_factors n hn j hj
  obtain ⟨L, hL⟩ := dvd_lcmRange (7430 * n) j hj0 (by omega)
  have hLQ : (lcmRange (7430 * n) : ℚ) = (j : ℚ) * (L : ℚ) := by
    exact_mod_cast hL
  let k := 4645 * n - 1 + (j + 1) / 2
  let x := poleClearedCoeff n j / (2 : ℚ) ^ k
  have hp : (Phi n : ℚ) ≠ 0 := by exact_mod_cast (Phi_pos n).ne'
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have ht : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨z, hz⟩ := integer_of_Phi_and_ten_power n x
    (by
      refine ⟨(L : ℤ) * (5 : ℤ) ^ (2 * n) * w, ?_⟩
      dsimp [x, poleClearedCoeff, reducedLcm]
      rw [hw, hLQ]
      change (Phi n : ℚ) * ((j * L / Phi n *
        (2 ^ k * 5 ^ (2 * n) * (w : ℚ)) / j) / 2 ^ k) = _
      push_cast
      field_simp)
    (by
      refine ⟨k, (5 : ℤ) ^ k * q, ?_⟩
      dsimp [x]
      rw [hq, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      push_cast
      field_simp)
  refine ⟨z, ?_⟩
  exact (div_eq_iff ht).mp hz |>.trans (mul_comm _ _)

/--
@isnad1 id=ex.3h2v.s7.1daf4d93dd99 from=translated src=- shape=f6b3f9e0 vocab=93408f44
-/
theorem normalized_poleClearedCoeff_two_factor
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, (2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * poleClearedCoeff n j =
      (2 : ℚ) ^ ((j + 1) / 2) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := poleClearedCoeff_two_factor n hn j hj0 hj
  refine ⟨z, ?_⟩
  rw [hz, ← mul_assoc, ← zpow_natCast (2 : ℚ),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  rw [show 1 - 4645 * (n : ℤ) + (4645 * n - 1 + (j + 1) / 2 : ℕ) =
    (((j + 1) / 2 : ℕ) : ℤ) by omega, zpow_natCast]

def giI : GaussianInt := ⟨0, 1⟩

/--
@isnad1 id=eq.0h0v.s5.b94e6f26c60c from=translated src=- shape=501f93a1 vocab=7e1b68b9
-/
theorem giI_toComplex : (giI : ℂ) = Complex.I := by
  simp [giI, GaussianInt.toComplex_def']

/--
@isnad1 id=eq.1h2v.s7.9c0debf0acdb from=translated src=- shape=f19f0ae3 vocab=750ed724
-/
theorem two_pow_div_one_add_I_pow (j m : ℕ) (hm : j ≤ 2 * m) :
    (2 : ℂ) ^ m / (1 + Complex.I) ^ j =
      (-Complex.I) ^ m * (1 + Complex.I) ^ (2 * m - j) := by
  have hne : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have htwo : (2 : ℂ) = (-Complex.I) * (1 + Complex.I) ^ 2 := by
    calc
      _ = -Complex.I * (2 * Complex.I) := by linear_combination 2 * Complex.I_sq
      _ = _ := by congr 1; linear_combination -Complex.I_sq
  rw [div_eq_iff (pow_ne_zero j hne), htwo, mul_pow, ← pow_mul]
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

/--
@isnad1 id=ex.0h1v.s8.ce8fecda3f8c from=translated src=- shape=a43def3e vocab=2301961c
-/
theorem pole_endpoint_bracket_is_integer (j : ℕ) :
    ∃ z : ℤ, Complex.I * (2 : ℂ) ^ ((j + 1) / 2) *
      ((2 + Complex.I) ^ j - (2 - Complex.I) ^ j -
        ((2 + Complex.I) / (1 + Complex.I)) ^ j +
        ((2 - Complex.I) / (1 - Complex.I)) ^ j) = (z : ℂ) := by
  let m := (j + 1) / 2
  let A : GaussianInt := 2 ^ m * giTwoAddI ^ j
  let B : GaussianInt := (-giI) ^ m * giOneAddI ^ (2 * m - j) * giTwoAddI ^ j
  have hA : (A : ℂ) = (2 : ℂ) ^ m * (2 + Complex.I) ^ j := by
    have htwo : GaussianInt.toComplex (2 : GaussianInt) = (2 : ℂ) :=
      map_natCast GaussianInt.toComplex 2
    simp only [A, map_mul, map_pow, htwo, giTwoAddI_toComplex]
  have hB : (B : ℂ) = (2 : ℂ) ^ m * ((2 + Complex.I) / (1 + Complex.I)) ^ j := by
    simp only [B, map_mul, map_pow, map_neg, giI_toComplex,
      giOneAddI_toComplex, giTwoAddI_toComplex]
    rw [← two_pow_div_one_add_I_pow j m (by dsimp [m]; omega), div_pow]
    ring
  have hAc : (star A : ℂ) = (2 : ℂ) ^ m * (2 - Complex.I) ^ j := by
    rw [hA]
    simp [sub_eq_add_neg]
  have hBc : (star B : ℂ) = (2 : ℂ) ^ m * ((2 - Complex.I) / (1 - Complex.I)) ^ j := by
    rw [hB]
    simp [sub_eq_add_neg]
  refine ⟨-2 * (A.im - B.im), ?_⟩
  calc
    _ = Complex.I * ((A : ℂ) - (star A : ℂ) - (B : ℂ) + (star B : ℂ)) := by
      rw [hAc, hBc, hA, hB]
      dsimp [m]
      ring
    _ = _ := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      ring

noncomputable def normalizedPoleEndpointTerm (n j : ℕ) : ℂ :=
  ((2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * poleClearedCoeff n j : ℚ) * Complex.I *
    ((2 + Complex.I) ^ j - (2 - Complex.I) ^ j -
      ((2 + Complex.I) / (1 + Complex.I)) ^ j +
      ((2 - Complex.I) / (1 - Complex.I)) ^ j)

/--
@isnad1 id=ex.3h2v.s5.e1b250701ea0 from=translated src=- shape=640afb8a vocab=014fb202
-/
theorem normalizedPoleEndpointTerm_is_integer
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, normalizedPoleEndpointTerm n j = (z : ℂ) := by
  obtain ⟨q, hq⟩ := normalized_poleClearedCoeff_two_factor n hn j hj0 hj
  obtain ⟨w, hw⟩ := pole_endpoint_bracket_is_integer j
  refine ⟨q * w, ?_⟩
  unfold normalizedPoleEndpointTerm
  rw [hq]
  push_cast
  rw [show (2 : ℂ) ^ ((j + 1) / 2) * q * Complex.I =
    q * (Complex.I * 2 ^ ((j + 1) / 2)) by ring, mul_assoc, hw]

end PiIrrationality
