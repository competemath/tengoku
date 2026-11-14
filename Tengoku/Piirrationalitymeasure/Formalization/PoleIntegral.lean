import Tengoku.Piirrationalitymeasure.Formalization.PoleArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Evaluation and integrality of the nonlogarithmic pole integral, Lemma 2.6.
The vertical segment is parametrized by `t = -1 + s*I`, `-2 <= s <= 2`;
the outer factor `I` in the definition of `J_n` makes its integral `-integral`.
-/

namespace PiIrrationality

noncomputable def polePair (j : ℕ) (s : ℝ) : ℂ :=
  (4 + (s : ℂ) * Complex.I) ^ (-(j : ℤ) - 1) +
    (6 - (s : ℂ) * Complex.I) ^ (-(j : ℤ) - 1)

/--
@isnad1 id=ne.0h1v.s5.8a468a53ad54 from=translated src=- shape=d5403407 vocab=c83afcd8
-/
theorem pole_left_ne_zero (s : ℝ) : (4 + (s : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/--
@isnad1 id=ne.0h1v.s5.2a457c39f26a from=translated src=- shape=d5403407 vocab=65d3ac2a
-/
theorem pole_right_ne_zero (s : ℝ) : (6 - (s : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/--
@isnad1 id=continuo.0h1v.s4.ddbc58c1142e from=translated src=- shape=7000f90d vocab=08278fed
-/
theorem polePair_continuous (j : ℕ) : Continuous (polePair j) := by
  apply Continuous.add
  · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).zpow₀
      (-(j : ℤ) - 1) (fun s => Or.inl (pole_left_ne_zero s))
  · exact (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).zpow₀
      (-(j : ℤ) - 1) (fun s => Or.inl (pole_right_ne_zero s))

/--
@isnad1 id=hasderiv.1h2v.s7.5088d8c1a010 from=translated src=- shape=93cb5712 vocab=881a048f
-/
theorem polePair_has_primitive (j : ℕ) (hj : 0 < j) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.I / (j : ℂ) *
      ((4 + (s : ℂ) * Complex.I) ^ (-(j : ℤ)) -
        (6 - (s : ℂ) * Complex.I) ^ (-(j : ℤ)))) (polePair j s) s := by
  have hleft := (hasDerivAt_zpow (-(j : ℤ))
    (4 + (s : ℂ) * Complex.I) (Or.inl (pole_left_ne_zero s))).comp (s : ℂ)
      (((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add 4)
  have hright := (hasDerivAt_zpow (-(j : ℤ))
    (6 - (s : ℂ) * Complex.I) (Or.inl (pole_right_ne_zero s))).comp (s : ℂ)
      (((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_sub 6)
  have hd := ((hleft.sub hright).const_mul (Complex.I / (j : ℂ))).comp_ofReal
  convert hd using 1
  · rfl
  · simp only [polePair, Int.cast_neg, Int.cast_natCast, one_mul, neg_mul]
    have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
    field_simp
    ring_nf
    simp [Complex.I_sq]

/--
@isnad1 id=eq.1h1v.s8.45cfe87e5c3a from=translated src=- shape=dbcdb058 vocab=211e27a6
-/
theorem polePair_integral (j : ℕ) (hj : 0 < j) :
    -(∫ s : ℝ in (-2)..2, polePair j s) = Complex.I / (j : ℂ) *
      ((4 - 2 * Complex.I) ^ (-(j : ℤ)) - (4 + 2 * Complex.I) ^ (-(j : ℤ)) -
        (6 + 2 * Complex.I) ^ (-(j : ℤ)) + (6 - 2 * Complex.I) ^ (-(j : ℤ))) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => polePair_has_primitive j hj s) ((polePair_continuous j).intervalIntegrable _ _)]
  push_cast
  simp only [neg_mul, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/--
@isnad1 id=and.0h0v.s8.a204934d7c48 from=translated src=- shape=d9dd9733 vocab=177de603
-/
theorem pole_endpoints_ten_div :
    (10 : ℂ) / (4 - 2 * Complex.I) = 2 + Complex.I ∧
    (10 : ℂ) / (4 + 2 * Complex.I) = 2 - Complex.I ∧
    (10 : ℂ) / (6 + 2 * Complex.I) = (2 + Complex.I) / (1 + Complex.I) ∧
    (10 : ℂ) / (6 - 2 * Complex.I) = (2 - Complex.I) / (1 - Complex.I) := by
  constructor
  · apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq]
  constructor
  · apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq]
  constructor <;> apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq]

/--
@isnad1 id=eq.1h1v.s8.98e2a259c8fd from=translated src=- shape=70374b5c vocab=211e27a6
-/
theorem polePair_integral_scaled (j : ℕ) (hj : 0 < j) :
    -(∫ s : ℝ in (-2)..2, polePair j s) =
      Complex.I / (j : ℂ) * (10 : ℂ) ^ (-(j : ℤ)) *
        ((2 + Complex.I) ^ j - (2 - Complex.I) ^ j -
          ((2 + Complex.I) / (1 + Complex.I)) ^ j +
          ((2 - Complex.I) / (1 - Complex.I)) ^ j) := by
  rw [polePair_integral j hj]
  obtain ⟨h1, h2, h3, h4⟩ := pole_endpoints_ten_div
  rw [← h3, ← h4, ← h1, ← h2]
  simp only [div_pow, zpow_neg, zpow_natCast]
  field_simp

noncomputable def normalizedPoleIntegral (n j : ℕ) : ℂ :=
  -((2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * reducedLcm n : ℚ) *
    (∫ s : ℝ in (-2)..2, (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s)

/--
@isnad1 id=eq.1h2v.s4.977c982f4bf5 from=translated src=- shape=a252a28b vocab=faa70f8e
-/
theorem normalizedPoleIntegral_eq_endpointTerm (n j : ℕ) (hj : 0 < j) :
    normalizedPoleIntegral n j = normalizedPoleEndpointTerm n j := by
  unfold normalizedPoleIntegral normalizedPoleEndpointTerm poleClearedCoeff
  rw [intervalIntegral.integral_const_mul]
  have hi := polePair_integral_scaled j hj
  push_cast
  rw [show -((2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * (reducedLcm n : ℂ)) *
      ((laurentCoeffRat n (j : ℤ) : ℂ) * (∫ s : ℝ in (-2)..2, polePair j s)) =
    (2 : ℂ) ^ (1 - 4645 * (n : ℤ)) * (reducedLcm n : ℂ) *
      (laurentCoeffRat n (j : ℤ) : ℂ) * (-(∫ s : ℝ in (-2)..2, polePair j s)) by ring,
    hi]
  ring

/--
@isnad1 id=ex.3h2v.s5.53fb7d4ba736 from=translated src=- shape=640afb8a vocab=83c68a36
-/
theorem normalizedPoleIntegral_is_integer
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, normalizedPoleIntegral n j = (z : ℂ) := by
  rw [normalizedPoleIntegral_eq_endpointTerm n j hj0]
  exact normalizedPoleEndpointTerm_is_integer n hn j hj0 hj

noncomputable def normalizedNonlogPoleIntegral (n : ℕ) : ℂ :=
  -((2 : ℚ) ^ (1 - 4645 * (n : ℤ)) * reducedLcm n : ℚ) *
    (∫ s : ℝ in (-2)..2,
      ∑ j ∈ Finset.Icc 1 (5570 * n), (laurentCoeffRat n (j : ℤ) : ℂ) * polePair j s)

/--
@isnad1 id=eq.0h1v.s5.0250a4a91907 from=translated src=- shape=b0eef33c vocab=5270d8e5
-/
theorem normalizedNonlogPoleIntegral_eq_sum (n : ℕ) :
    normalizedNonlogPoleIntegral n =
      ∑ j ∈ Finset.Icc 1 (5570 * n), normalizedPoleIntegral n j := by
  unfold normalizedNonlogPoleIntegral normalizedPoleIntegral
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro j _
    exact (continuous_const.mul (polePair_continuous j)).intervalIntegrable _ _

/--
@isnad1 id=ex.1h1v.s4.106baaed8de4 from=translated src=- shape=f3832220 vocab=fb65baff
-/
theorem normalizedNonlogPoleIntegral_is_integer (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, normalizedNonlogPoleIntegral n = (z : ℂ) := by
  classical
  rw [normalizedNonlogPoleIntegral_eq_sum]
  have hsum (S : Finset ℕ) (hS : ∀ j ∈ S, 0 < j ∧ j ≤ 5570 * n) :
      ∃ z : ℤ, ∑ j ∈ S, normalizedPoleIntegral n j = (z : ℂ) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert j S hj ih =>
      obtain ⟨z, hz⟩ := ih (fun k hk => hS k (Finset.mem_insert_of_mem hk))
      have hjbounds := hS j (Finset.mem_insert_self _ _)
      obtain ⟨w, hw⟩ := normalizedPoleIntegral_is_integer n hn j hjbounds.1 hjbounds.2
      exact ⟨w + z, by rw [Finset.sum_insert hj, hw, hz]; push_cast; rfl⟩
  exact hsum _ (fun j hj => Finset.mem_Icc.mp hj)

end PiIrrationality
