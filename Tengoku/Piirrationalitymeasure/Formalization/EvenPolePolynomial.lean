import Tengoku.Piirrationalitymeasure.Formalization.PartialFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Integer polynomial quotients for an arbitrary even numerator and two symmetric poles. -/

namespace PiIrrationality.EvenPole

open Polynomial

noncomputable def numerator (F : Polynomial ℤ) : Polynomial ℚ :=
  (F.comp (X ^ 2)).map (Int.castRingHom ℚ)

noncomputable def signedNumeratorY (F : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  C ((-1 : ℤ) ^ m) * F

noncomputable def denominatorY (m : ℕ) : Polynomial ℤ := (X - C 25) ^ m

noncomputable def partY (F : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  signedNumeratorY F m /ₘ denominatorY m

noncomputable def remainderY (F : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  signedNumeratorY F m %ₘ denominatorY m

noncomputable def part (F : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (partY F m).comp (X ^ 2)

noncomputable def remainder (F : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (remainderY F m).comp (X ^ 2)

theorem denominatorY_monic (m : ℕ) : (denominatorY m).Monic :=
  (monic_X_sub_C 25).pow _

theorem part_aeval_even {K : Type*} [CommRing K] [Algebra ℤ K]
    (F : Polynomial ℤ) (m : ℕ) (t : K) : aeval (-t) (part F m) = aeval t (part F m) := by
  simp [part, aeval_comp]

theorem remainder_natDegree_le (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    (remainder F m).natDegree ≤ 2 * m - 2 := by
  have h := degree_modByMonic_lt (signedNumeratorY F m) (denominatorY_monic m)
  change (remainderY F m).degree < (denominatorY m).degree at h
  rw [degree_eq_natDegree (denominatorY_monic m).ne_zero,
    denominatorY, natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have hY : (remainderY F m).natDegree ≤ m - 1 := by
    by_cases hzero : remainderY F m = 0
    · simp [hzero]
    rw [degree_eq_natDegree hzero, Nat.cast_lt] at h
    omega
  rw [remainder, natDegree_comp, natDegree_X_pow]
  omega

theorem division (F : Polynomial ℤ) (m : ℕ) :
    (signedNumeratorY F m).comp (X ^ 2) =
      (X ^ 2 - C 25) ^ m * part F m + remainder F m := by
  have h := congrArg (fun P : Polynomial ℤ => P.comp (X ^ 2))
    (modByMonic_add_div (signedNumeratorY F m) (denominatorY m))
  simpa [part, remainder, partY, remainderY, denominatorY, add_comm] using h.symm

theorem part_eq_divByMonic (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    (signedNumeratorY F m).comp (X ^ 2) /ₘ (X ^ 2 - C 25) ^ m = part F m := by
  have hmonic : ((X ^ 2 - C 25 : Polynomial ℤ) ^ m).Monic :=
    (monic_X_pow_sub_C 25 (by decide)).pow _
  apply (div_modByMonic_unique (part F m) (remainder F m) hmonic ?_).1
  refine ⟨by rw [add_comm, ← division], ?_⟩
  calc
    (remainder F m).degree ≤ (2 * m - 2 : ℕ) :=
      degree_le_of_natDegree_le (remainder_natDegree_le F hm)
    _ < ((X ^ 2 - C 25 : Polynomial ℤ) ^ m).degree := by
      rw [degree_eq_natDegree hmonic.ne_zero, natDegree_pow, natDegree_X_pow_sub_C,
        Nat.cast_lt]
      omega

theorem part_map_eq_divByMonic (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    numerator (signedNumeratorY F m) /ₘ (X ^ 2 - C 25) ^ m =
      (part F m).map (Int.castRingHom ℚ) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (part_eq_divByMonic F hm)
  rw [map_divByMonic _ ((monic_X_pow_sub_C (25 : ℤ) (by decide)).pow m)] at h
  simpa only [numerator, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, show (Int.castRingHom ℚ) (25 : ℤ) = 25 by norm_num] using h

def Decomposition (F : Polynomial ℤ) (m : ℕ) (a b : Fin m → ℚ) : Prop :=
  numerator (signedNumeratorY F m) =
    (part F m).map (Int.castRingHom ℚ) * ((X + C 5) ^ m * (X - C 5) ^ m) +
      (∑ i : Fin m, C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ m) +
      (∑ i : Fin m, C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ m)

theorem exists_decomposition (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    ∃ a b : Fin m → ℚ, Decomposition F m a b := by
  obtain ⟨Q, a, b, h⟩ := two_pole_polynomial_decomposition
    (numerator (signedNumeratorY F m)) m
  have hQ := two_pole_quotient_eq_divByMonic _ Q m hm a b h
  rw [part_map_eq_divByMonic F hm] at hQ
  refine ⟨a, b, ?_⟩
  unfold Decomposition
  exact hQ ▸ h

theorem Decomposition.reflect {F : Polynomial ℤ} {m : ℕ} {a b : Fin m → ℚ}
    (hF : Decomposition F m a b) :
    Decomposition F m (fun i => (-1 : ℚ) ^ (i.val + m) * b i)
      (fun i => (-1 : ℚ) ^ (i.val + m) * a i) := by
  unfold Decomposition at hF ⊢
  have h := congrArg (fun P : Polynomial ℚ => P.comp (-X)) hF
  rw [show (numerator (signedNumeratorY F m)).comp (-X) =
      numerator (signedNumeratorY F m) from int_square_comp_reflect _,
    add_comp, add_comp, mul_comp,
    show ((part F m).map (Int.castRingHom ℚ)).comp (-X) =
      (part F m).map (Int.castRingHom ℚ) from int_square_comp_reflect _] at h
  simp only [mul_comp, pow_comp, sum_comp, C_comp, X_comp, add_comp, sub_comp] at h
  rw [show (-X + C 5 : Polynomial ℚ) = -(X - C 5) by ring,
    show (-X - C 5 : Polynomial ℚ) = -(X + C 5) by ring] at h
  have hden : (-(X - C 5) : Polynomial ℚ) ^ m * (-(X + C 5)) ^ m =
      (X + C 5) ^ m * (X - C 5) ^ m := by
    rw [← mul_pow, neg_mul_neg, mul_comm, mul_pow]
  rw [hden] at h
  have hterm (u v : Polynomial ℚ) (z : ℚ) (i m : ℕ) :
      C z * (-u) ^ i * (-v) ^ m = C ((-1 : ℚ) ^ (i + m) * z) * u ^ i * v ^ m := by
    rw [neg_pow u i, neg_pow v m]
    simp only [pow_add, map_mul, map_pow, map_neg, map_one]
    ring
  simp_rw [hterm] at h
  linear_combination h

end PiIrrationality.EvenPole
