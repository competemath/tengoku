import Tengoku.Piirrationalitymeasure.Formalization.PartialFractions
import Tengoku.Piirrationalitymeasure.Formalization.ScaledLaurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Identification of the partial-fraction coefficients with the normalized
derivatives defining `laurentCoeffRat`.
-/

namespace PiIrrationality

open Polynomial

theorem normalizedDeriv_shift_power (k m : ℕ) :
    normalizedDeriv k (fun t : ℝ => (t + 5) ^ m) (-5) = if m = k then 1 else 0 := by
  unfold normalizedDeriv
  rw [iteratedDeriv_comp_add_const (f := fun t : ℝ => t ^ m) (s := 5) (n := k)]
  norm_num only [neg_add_cancel]
  change normalizedPowerDeriv m k 0 = _
  rw [normalizedPowerDeriv_eq_choose_or_zero]
  by_cases h : m = k
  · subst m
    simp
  by_cases hk : k ≤ m
  · have hmk : m - k ≠ 0 := by omega
    simp [h, hk, zero_pow hmk]
  · simp [h, hk]

theorem normalizedDeriv_shift_power_mul_zero
    (k m : ℕ) (hkm : k < m) (f : ℝ → ℝ) (hf : ContDiffAt ℝ k f (-5)) :
    normalizedDeriv k (fun t : ℝ => (t + 5) ^ m * f t) (-5) = 0 := by
  rw [normalizedDeriv_mul (by fun_prop) hf]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [normalizedDeriv_shift_power, ite_eq_right (by omega), zero_mul]

theorem normalizedDeriv_shift_polynomial (m : ℕ) (a : Fin m → ℚ) (k : Fin m) :
    normalizedDeriv k.val (fun t : ℝ => ∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) (-5) =
      (a k : ℝ) := by
  unfold normalizedDeriv
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop), Finset.sum_div]
  change (∑ i : Fin m, normalizedDeriv k.val
    (fun t : ℝ => (a i : ℝ) * (t + 5) ^ i.val) (-5)) = _
  simp_rw [normalizedDeriv_const_mul, normalizedDeriv_shift_power]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
    simp [hval]
  · simp

theorem regularized_eq_of_twoPoleDecomposition
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b)
    (t : ℝ) (ht : t ≠ 5) :
    regularized n t = (∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) +
      (t + 5) ^ (5570 * n + 1) *
        (aeval t (polynomialPart n) +
          (∑ i : Fin (5570 * n + 1), (b i : ℝ) * (t - 5) ^ i.val) /
            (t - 5) ^ (5570 * n + 1)) := by
  have hD : (t - 5) ^ (5570 * n + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht)
  have hodd : Odd (5570 * n + 1) := ⟨2785 * n, by omega⟩
  have hden : (5 - t) ^ (5570 * n + 1) = -((t - 5) ^ (5570 * n + 1)) := by
    rw [← neg_sub t 5, hodd.neg_pow]
  have h := congrArg (aeval t) hF
  simp only [show Int.castRingHom ℚ = algebraMap ℤ ℚ from Subsingleton.elim _ _,
    map_add, map_mul, map_sum, aeval_map_algebraMap ℚ] at h
  simp only [infinityNumeratorY, aeval_comp, map_mul, map_add, map_sub,
    map_pow, aeval_X, aeval_C, map_neg, map_ofNat, ← pow_mul] at h
  have hmap (q : ℚ) : (algebraMap ℚ ℝ) q = (q : ℝ) := map_ratCast _ q
  simp_rw [hmap] at h
  norm_num only [Nat.reduceMul] at h
  rw [← Finset.sum_mul, ← Finset.sum_mul] at h
  unfold regularized
  rw [hden, div_neg, ← neg_div, div_eq_iff hD]
  norm_num only [Nat.reduceMul]
  field_simp at *
  linear_combination h

theorem normalizedDeriv_regularized_of_twoPoleDecomposition
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b)
    (k : Fin (5570 * n + 1)) :
    normalizedDeriv k.val (regularized n) (-5) = (a k : ℝ) := by
  let f : ℝ → ℝ := fun t => aeval t (polynomialPart n) +
    (∑ i : Fin (5570 * n + 1), (b i : ℝ) * (t - 5) ^ i.val) /
      (t - 5) ^ (5570 * n + 1)
  have hf : ContDiffAt ℝ k.val f (-5) := by
    dsimp [f]
    apply ((polynomialPart n).contDiff_aeval k.val).contDiffAt.add
    fun_prop (disch := norm_num)
  have hpoly : ContDiffAt ℝ k.val
      (fun t : ℝ => ∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) (-5) := by
    fun_prop
  have hroot : ContDiffAt ℝ k.val (fun t : ℝ => (t + 5) ^ (5570 * n + 1) * f t) (-5) :=
    ((contDiffAt_id.add contDiffAt_const).pow _).mul hf
  have heq : regularized n =ᶠ[nhds (-5 : ℝ)]
      (fun t : ℝ => (∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) +
        (t + 5) ^ (5570 * n + 1) * f t) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-5 : ℝ) ≠ 5)] with t ht
    exact regularized_eq_of_twoPoleDecomposition n a b hF t ht
  have hnorm := congrArg (fun x : ℝ => x / (k.val.factorial : ℝ))
    (heq.iteratedDeriv_eq k.val)
  change normalizedDeriv k.val (regularized n) (-5) =
    normalizedDeriv k.val
      (fun t : ℝ => (∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) +
        (t + 5) ^ (5570 * n + 1) * f t) (-5) at hnorm
  rw [hnorm]
  have hsplit : normalizedDeriv k.val
      (fun t : ℝ => (∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) +
        (t + 5) ^ (5570 * n + 1) * f t) (-5) =
      normalizedDeriv k.val
        (fun t : ℝ => ∑ i : Fin (5570 * n + 1), (a i : ℝ) * (t + 5) ^ i.val) (-5) +
      normalizedDeriv k.val (fun t : ℝ => (t + 5) ^ (5570 * n + 1) * f t) (-5) := by
    unfold normalizedDeriv
    rw [iteratedDeriv_fun_add hpoly hroot, add_div]
  rw [hsplit, normalizedDeriv_shift_polynomial,
    normalizedDeriv_shift_power_mul_zero k.val _ k.isLt f hf, add_zero]

theorem leftPartialCoeff_eq_laurentCoeffRat
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b)
    (k : Fin (5570 * n + 1)) :
    a k = laurentCoeffRat n (5570 * (n : ℤ) - k.val) := by
  apply Rat.cast_injective (α := ℝ)
  rw [laurentCoeffRat_cast, laurentCoeff_eq_normalizedDeriv n _ (by omega)]
  rw [show (5570 * (n : ℤ) - (5570 * (n : ℤ) - k.val)).toNat = k.val by omega]
  exact (normalizedDeriv_regularized_of_twoPoleDecomposition n a b hF k).symm

theorem rightPartialCoeff_eq_laurentCoeffRat
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b)
    (k : Fin (5570 * n + 1)) :
    b k = (-1 : ℚ) ^ (k.val + (5570 * n + 1)) *
      laurentCoeffRat n (5570 * (n : ℤ) - k.val) := by
  have h := leftPartialCoeff_eq_laurentCoeffRat n _ _ (hF.reflect n a b) k
  change (-1 : ℚ) ^ (k.val + (5570 * n + 1)) * b k = _ at h
  rw [← h, ← mul_assoc, ← mul_pow]
  norm_num

theorem actual_twoPoleDecomposition (n : ℕ) :
    TwoPoleDecomposition n
      (fun i => laurentCoeffRat n (5570 * (n : ℤ) - i.val))
      (fun i => (-1 : ℚ) ^ (i.val + (5570 * n + 1)) *
        laurentCoeffRat n (5570 * (n : ℤ) - i.val)) := by
  obtain ⟨a, b, hF⟩ := polynomialPart_two_pole_decomposition n
  have ha : a = fun i => laurentCoeffRat n (5570 * (n : ℤ) - i.val) :=
    funext (leftPartialCoeff_eq_laurentCoeffRat n a b hF)
  have hb : b = fun i => (-1 : ℚ) ^ (i.val + (5570 * n + 1)) *
      laurentCoeffRat n (5570 * (n : ℤ) - i.val) :=
    funext (rightPartialCoeff_eq_laurentCoeffRat n a b hF)
  rwa [ha, hb] at hF

end PiIrrationality
