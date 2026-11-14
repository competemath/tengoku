import Tengoku.Piirrationalitymeasure.Formalization.LaurentRationality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The integer polynomial part of (2.2). Division in the variable `y=t^2`
makes evenness explicit. The denominator in `y` is monic; its odd power
accounts for the minus sign in the numerator.
-/

namespace PiIrrationality

open Polynomial

noncomputable def infinityNumeratorY (n : ℕ) : Polynomial ℤ :=
  C (-5) * (X ^ (1857 * n) * (X ^ 2 + C 6 * X + C 25) ^ (3714 * n))

noncomputable def infinityDenominatorY (n : ℕ) : Polynomial ℤ :=
  (X - C 25) ^ (5570 * n + 1)

noncomputable def polynomialPartY (n : ℕ) : Polynomial ℤ :=
  infinityNumeratorY n /ₘ infinityDenominatorY n

noncomputable def polynomialRemainderY (n : ℕ) : Polynomial ℤ :=
  infinityNumeratorY n %ₘ infinityDenominatorY n

noncomputable def polynomialPart (n : ℕ) : Polynomial ℤ :=
  (polynomialPartY n).comp (X ^ 2)

noncomputable def polynomialRemainder (n : ℕ) : Polynomial ℤ :=
  (polynomialRemainderY n).comp (X ^ 2)

/--
@isnad1 id=monic.0h1v.s2.486af1211f10 from=translated src=- shape=1a6c1393 vocab=17252b1a
-/
theorem infinityDenominatorY_monic (n : ℕ) : (infinityDenominatorY n).Monic :=
  (monic_X_sub_C 25).pow _

/--
@isnad1 id=eq.0h1v.s5.0566a14655a4 from=translated src=- shape=3487779f vocab=1c0983da
-/
theorem infinityDenominatorY_natDegree (n : ℕ) :
    (infinityDenominatorY n).natDegree = 5570 * n + 1 := by
  rw [infinityDenominatorY, natDegree_pow, natDegree_X_sub_C, mul_one]

/--
@isnad1 id=eq.0h1v.s4.35e082be846e from=translated src=- shape=e96f2693 vocab=946eb1ef
-/
theorem infinityNumeratorY_natDegree (n : ℕ) :
    (infinityNumeratorY n).natDegree = 9285 * n := by
  have hquad : (X ^ 2 + C (6 : ℤ) * X + C 25).natDegree = 2 := by
    compute_degree <;> norm_num
  have hquad0 : (X ^ 2 + C (6 : ℤ) * X + C 25) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hquad
    omega
  rw [infinityNumeratorY, natDegree_C_mul (by norm_num : (-5 : ℤ) ≠ 0),
    natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hquad0),
    natDegree_X_pow, natDegree_pow, hquad]
  omega

/--
@isnad1 id=eq.0h1v.s5.236530e73dfc from=translated src=- shape=3487779f vocab=140455ce
-/
theorem polynomialPartY_natDegree (n : ℕ) :
    (polynomialPartY n).natDegree = 3715 * n - 1 := by
  rw [polynomialPartY, natDegree_divByMonic _ (infinityDenominatorY_monic n),
    infinityNumeratorY_natDegree, infinityDenominatorY_natDegree]
  omega

/--
@isnad1 id=eq.0h1v.s5.53842489c723 from=translated src=- shape=3487779f vocab=f79fd5c9
-/
theorem polynomialPart_natDegree (n : ℕ) :
    (polynomialPart n).natDegree = 7430 * n - 2 := by
  rw [polynomialPart, natDegree_comp, polynomialPartY_natDegree, natDegree_X_pow]
  omega

/--
@isnad1 id=eq.0h3v.s7.323c7391334f from=translated src=- shape=76d2d0c8 vocab=8246dd3f
-/
theorem polynomialPart_aeval_even {K : Type*} [CommRing K] [Algebra ℤ K]
    (n : ℕ) (t : K) : aeval (-t) (polynomialPart n) = aeval t (polynomialPart n) := by
  simp [polynomialPart, aeval_comp]

/--
@isnad1 id=lt.0h1v.s4.9555d20ac83c from=translated src=- shape=2d31147b vocab=31b5073b
-/
theorem polynomialRemainderY_degree_lt (n : ℕ) :
    (polynomialRemainderY n).degree < (infinityDenominatorY n).degree :=
  degree_modByMonic_lt _ (infinityDenominatorY_monic n)

/--
@isnad1 id=le.0h1v.s4.e291c270d934 from=translated src=- shape=e96f2693 vocab=7a222d29
-/
theorem polynomialRemainder_natDegree_le (n : ℕ) :
    (polynomialRemainder n).natDegree ≤ 11140 * n := by
  have h := polynomialRemainderY_degree_lt n
  have hdeg := infinityDenominatorY_natDegree n
  rw [degree_eq_natDegree (infinityDenominatorY_monic n).ne_zero, hdeg] at h
  have hY : (polynomialRemainderY n).natDegree ≤ 5570 * n := by
    by_cases hzero : polynomialRemainderY n = 0
    · simp [hzero]
    rw [degree_eq_natDegree hzero, Nat.cast_lt] at h
    omega
  rw [polynomialRemainder, natDegree_comp, natDegree_X_pow]
  omega

/--
@isnad1 id=eq.0h1v.s7.58d69f322add from=translated src=- shape=11c3ebcf vocab=58707d19
-/
theorem polynomialPart_division (n : ℕ) :
    (infinityNumeratorY n).comp (X ^ 2) =
      (X ^ 2 - C 25) ^ (5570 * n + 1) * polynomialPart n + polynomialRemainder n := by
  have h := congrArg (fun P : Polynomial ℤ => P.comp (X ^ 2))
    (modByMonic_add_div (infinityNumeratorY n) (infinityDenominatorY n))
  simpa [polynomialPart, polynomialRemainder, polynomialPartY,
    polynomialRemainderY, infinityDenominatorY, add_comm] using h.symm

/--
@isnad1 id=monic.0h1v.s7.9bc2af57d4ee from=translated src=- shape=6048f06b vocab=358dbc2c
-/
theorem infinityDenominator_monic (n : ℕ) :
    ((X ^ 2 - C 25 : Polynomial ℤ) ^ (5570 * n + 1)).Monic :=
  (monic_X_pow_sub_C 25 (by decide)).pow _

/--
@isnad1 id=eq.0h1v.s8.48da4ad44e2c from=translated src=- shape=78e382b2 vocab=48386ec2
-/
theorem polynomialPart_eq_divByMonic (n : ℕ) :
    ((infinityNumeratorY n).comp (X ^ 2)) /ₘ
      (X ^ 2 - C 25) ^ (5570 * n + 1) = polynomialPart n := by
  apply (div_modByMonic_unique (polynomialPart n) (polynomialRemainder n)
    (infinityDenominator_monic n) ?_).1
  refine ⟨by rw [add_comm, ← polynomialPart_division], ?_⟩
  calc
    (polynomialRemainder n).degree ≤ (11140 * n : ℕ) :=
      degree_le_of_natDegree_le (polynomialRemainder_natDegree_le n)
    _ < ((X ^ 2 - C 25 : Polynomial ℤ) ^ (5570 * n + 1)).degree := by
      rw [degree_eq_natDegree (infinityDenominator_monic n).ne_zero,
        natDegree_pow, natDegree_X_pow_sub_C, Nat.cast_lt]
      omega

/--
@isnad1 id=eq.0h1v.s8.3d39dbf82366 from=translated src=- shape=acc94666 vocab=8d4e53aa
-/
theorem polynomialPart_map_eq_divByMonic (n : ℕ) :
    ((infinityNumeratorY n).comp (X ^ 2)).map (Int.castRingHom ℚ) /ₘ
      (X ^ 2 - C 25) ^ (5570 * n + 1) =
      (polynomialPart n).map (Int.castRingHom ℚ) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (polynomialPart_eq_divByMonic n)
  rw [map_divByMonic _ (infinityDenominator_monic n)] at h
  simpa only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    show (Int.castRingHom ℚ) (25 : ℤ) = 25 by norm_num] using h

/--
@isnad1 id=eq.1h2v.s8.f4981ebd9a2b from=translated src=- shape=f49c71f0 vocab=a88f0b8d
-/
theorem rationalFunction_eq_polynomialPart_add_remainder
    (n : ℕ) (t : ℚ) (ht : t ^ 2 ≠ 25) :
    rationalFunction n t = aeval t (polynomialPart n) +
      aeval t (polynomialRemainder n) / (t ^ 2 - 25) ^ (5570 * n + 1) := by
  have hD : (t ^ 2 - 25) ^ (5570 * n + 1) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr ht)
  have hodd : Odd (5570 * n + 1) := ⟨2785 * n, by omega⟩
  have hden : (25 - t ^ 2) ^ (5570 * n + 1) =
      -((t ^ 2 - 25) ^ (5570 * n + 1)) := by
    rw [← neg_sub (t ^ 2) 25, hodd.neg_pow]
  have h := congrArg (aeval t) (polynomialPart_division n)
  simp only [infinityNumeratorY, aeval_comp, map_mul, map_add, map_sub, map_pow,
    aeval_X, map_neg, map_ofNat, ← pow_mul] at h
  have he : 2 * (1857 * n) = 2 * 1857 * n := by omega
  rw [he] at h
  norm_num only [Nat.reduceMul] at h
  unfold rationalFunction
  rw [hden, div_neg, ← neg_div, div_eq_iff hD]
  rw [add_mul, div_mul_cancel₀ _ hD]
  norm_num only [Nat.reduceMul]
  linear_combination h

end PiIrrationality
