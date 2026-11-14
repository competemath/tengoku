import Tengoku.Piirrationalitymeasure.Formalization.PartialFractionIdentity
import Tengoku.Piirrationalitymeasure.Formalization.ComplexDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The second polynomial representation (2.29), including the negative
Laurent indices needed to clear the reduced denominator.
-/

namespace PiIrrationality

open Polynomial

noncomputable def poleShiftPolynomial (n : ℕ) : Polynomial ℤ :=
  taylor (-5) (polynomialPart n)

noncomputable def poleShiftCoeff (n k : ℕ) : ℤ := (poleShiftPolynomial n).coeff k

/--
@isnad1 id=eq.1h3v.s7.3a3dcbd22eae from=translated src=- shape=d03a7ff2 vocab=7cc2cf07
-/
theorem normalizedDeriv_shift_power_mul (m q : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ (m + q) f (-5)) :
    normalizedDeriv (m + q) (fun t : ℝ => (t + 5) ^ m * f t) (-5) =
      normalizedDeriv q f (-5) := by
  rw [normalizedDeriv_mul (by fun_prop) hf]
  simp_rw [normalizedDeriv_shift_power]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ him
    simp [Ne.symm him]
  · intro hm
    exact (hm (Finset.mem_range.mpr (by omega))).elim

/--
@isnad1 id=eq.0h2v.s7.068b7dd27eef from=translated src=- shape=66635e5a vocab=92119cee
-/
theorem normalizedDeriv_inv_linear_choose (j k : ℕ) :
    normalizedDeriv k (fun t : ℝ => 1 / (5 - t) ^ (j + 1)) (-5) =
      ((j + k).choose k : ℝ) / 10 ^ (j + k + 1) := by
  have hprod : (∏ i ∈ Finset.range k, (-(j + 1 : ℝ) - i)) =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((j + k).choose k : ℝ) := by
    exact_mod_cast negative_ascending_product j k
  have hfun : (fun t : ℝ => 1 / (5 - t) ^ (j + 1)) =
      (fun t : ℝ => (5 - t) ^ (-((j + 1 : ℕ) : ℤ))) := by
    simp only [one_div, zpow_neg, zpow_natCast]
  rw [hfun, normalized_inv_linear_deriv]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hprod]
  have he : -((j : ℤ) + 1) - k = -((j + k + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  norm_num only [sub_neg_eq_add, Nat.reduceAdd]
  rw [show (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * ((j + k).choose k : ℝ)) =
      (k.factorial : ℝ) * ((j + k).choose k : ℝ) by
    rw [← mul_assoc, ← mul_assoc, ← mul_pow]; norm_num]
  field_simp

/--
@isnad1 id=eq.1h2v.s9.1bc4e76bdf17 from=translated src=- shape=326ee4eb vocab=7472024e
-/
theorem otherPole_lowIndex_eq_sum (n : ℕ) (t : ℝ) (ht : t ≠ 5) :
    (∑ i : Fin (5570 * n + 1),
      (((-1 : ℚ) ^ (i.val + (5570 * n + 1)) *
          laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℚ) : ℝ) * (t - 5) ^ i.val) /
        (t - 5) ^ (5570 * n + 1) =
      ∑ j : Fin (5570 * n + 1), (laurentCoeffRat n (j.val : ℤ) : ℝ) *
        (1 / (5 - t) ^ (j.val + 1)) := by
  rw [Finset.sum_div]
  have hterm (i : Fin (5570 * n + 1)) :
      ((((-1 : ℚ) ^ (i.val + (5570 * n + 1)) *
          laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℚ) : ℝ) * (t - 5) ^ i.val) /
        (t - 5) ^ (5570 * n + 1) =
      (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℝ) /
        (5 - t) ^ (5570 * n + 1 - i.val) := by
    have hsign : (-1 : ℝ) ^ (i.val + (5570 * n + 1)) =
        (-1 : ℝ) ^ (5570 * n + 1 - i.val) := by
      rw [show i.val + (5570 * n + 1) = (5570 * n + 1 - i.val) + 2 * i.val by
        have := i.isLt; omega, pow_add, pow_mul]
      norm_num
    push_cast
    rw [show 5 - t = -(t - 5) by ring, div_neg_power, ← hsign]
    have hpow : (t - 5) ^ (5570 * n + 1) =
        (t - 5) ^ (5570 * n + 1 - i.val) * (t - 5) ^ i.val := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
    rw [hpow]
    have hne := sub_ne_zero.mpr ht
    field_simp
  simp_rw [hterm]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  have hindex : 5570 * (n : ℤ) - (j.rev.val : ℤ) = (j.val : ℤ) := by
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  have hpower : 5570 * n + 1 - j.rev.val = j.val + 1 := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  rw [hindex, hpower]
  ring

/--
@isnad1 id=eq.1h2v.s9.a3bf77f96858 from=translated src=- shape=727d2b80 vocab=7605939a
-/
theorem regularized_polynomial_remainder_identity (n : ℕ) (t : ℝ) (ht : t ≠ 5) :
    regularized n t =
      (∑ i : Fin (5570 * n + 1),
        (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℝ) * (t + 5) ^ i.val) +
      (t + 5) ^ (5570 * n + 1) *
        (aeval t (polynomialPart n) +
          ∑ j : Fin (5570 * n + 1), (laurentCoeffRat n (j.val : ℤ) : ℝ) *
            (1 / (5 - t) ^ (j.val + 1))) := by
  rw [regularized_eq_of_twoPoleDecomposition n _ _ (actual_twoPoleDecomposition n) t ht,
    otherPole_lowIndex_eq_sum n t ht]

/--
@isnad1 id=eq.0h2v.s6.a05fbf5b10dd from=translated src=- shape=e0251df1 vocab=0e18b818
-/
theorem poleShiftCoeff_eq_normalizedDeriv (n q : ℕ) :
    normalizedDeriv q (fun t : ℝ => aeval t (polynomialPart n)) (-5) =
      (poleShiftCoeff n q : ℝ) := by
  rw [poleShiftCoeff, poleShiftPolynomial, taylor_coeff]
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    normalizedDeriv_int_polynomial q (polynomialPart n) (-5)

/--
@isnad1 id=eq.0h2v.s8.fd2f917b8469 from=translated src=- shape=2a2d97fa vocab=a802e656
-/
theorem poleShiftCoeff_laurent_formula (n q : ℕ) :
    (poleShiftCoeff n q : ℚ) = laurentCoeffRat n (-((q + 1 : ℕ) : ℤ)) -
      ∑ j : Fin (5570 * n + 1), ((j.val + q).choose q : ℚ) *
        laurentCoeffRat n (j.val : ℤ) / 10 ^ (j.val + q + 1) := by
  let m := 5570 * n + 1
  let A (t : ℝ) := ∑ i : Fin m,
    (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℝ) * (t + 5) ^ i.val
  let S (t : ℝ) := ∑ j : Fin m, (laurentCoeffRat n (j.val : ℤ) : ℝ) *
    (1 / (5 - t) ^ (j.val + 1))
  let f (t : ℝ) := aeval t (polynomialPart n) + S t
  have hP : ContDiffAt ℝ (m + q) (fun t : ℝ => aeval t (polynomialPart n)) (-5) :=
    ((polynomialPart n).contDiff_aeval (m + q)).contDiffAt
  have hS : ContDiffAt ℝ (m + q) S (-5) := by
    dsimp [S]
    fun_prop (disch := norm_num)
  have hf : ContDiffAt ℝ (m + q) f (-5) := hP.add hS
  have hA : ContDiffAt ℝ (m + q) A (-5) := by dsimp [A]; fun_prop
  have hg : ContDiffAt ℝ (m + q) (fun t : ℝ => (t + 5) ^ m * f t) (-5) :=
    (by fun_prop : ContDiffAt ℝ (m + q) (fun t : ℝ => (t + 5) ^ m) (-5)).mul hf
  have heq : regularized n =ᶠ[nhds (-5 : ℝ)]
      (fun t => A t + (t + 5) ^ m * f t) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-5 : ℝ) ≠ 5)] with t ht
    exact regularized_polynomial_remainder_identity n t ht
  have hd := congrArg (fun x : ℝ => x / ((m + q).factorial : ℝ))
    (heq.iteratedDeriv_eq (m + q))
  change normalizedDeriv (m + q) (regularized n) (-5) =
    normalizedDeriv (m + q) (fun t => A t + (t + 5) ^ m * f t) (-5) at hd
  have hsplit : normalizedDeriv (m + q) (fun t => A t + (t + 5) ^ m * f t) (-5) =
      normalizedDeriv (m + q) A (-5) + normalizedDeriv q f (-5) := by
    unfold normalizedDeriv
    rw [iteratedDeriv_fun_add hA hg, add_div]
    exact congrArg (fun z : ℝ => iteratedDeriv (m + q) A (-5) / (m + q).factorial + z)
      (normalizedDeriv_shift_power_mul m q f hf)
  have hAzero : normalizedDeriv (m + q) A (-5) = 0 := by
    unfold normalizedDeriv
    dsimp only [A]
    rw [iteratedDeriv_fun_sum (by intros; fun_prop), Finset.sum_div]
    change (∑ i : Fin m, normalizedDeriv (m + q)
      (fun t : ℝ => (laurentCoeffRat n (5570 * (n : ℤ) - i.val) : ℝ) *
        (t + 5) ^ i.val) (-5)) = 0
    simp_rw [normalizedDeriv_const_mul, normalizedDeriv_shift_power]
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt
    simp [show i.val ≠ m + q by omega]
  have hD : normalizedDeriv q f (-5) = (poleShiftCoeff n q : ℝ) +
      ∑ j : Fin m, ((j.val + q).choose q : ℝ) *
        (laurentCoeffRat n (j.val : ℤ) : ℝ) / 10 ^ (j.val + q + 1) := by
    have hPq : ContDiffAt ℝ q (fun t : ℝ => aeval t (polynomialPart n)) (-5) :=
      hP.of_le (by exact_mod_cast (show q ≤ m + q by omega))
    have hSq : ContDiffAt ℝ q S (-5) :=
      hS.of_le (by exact_mod_cast (show q ≤ m + q by omega))
    have hsplit' : normalizedDeriv q f (-5) =
        normalizedDeriv q (fun t : ℝ => aeval t (polynomialPart n)) (-5) +
          normalizedDeriv q S (-5) := by
      unfold normalizedDeriv
      dsimp only [f]
      rw [iteratedDeriv_fun_add hPq hSq, add_div]
    rw [hsplit', poleShiftCoeff_eq_normalizedDeriv]
    congr 1
    unfold normalizedDeriv
    dsimp only [S]
    rw [iteratedDeriv_fun_sum (by intros; fun_prop (disch := norm_num)), Finset.sum_div]
    change (∑ j : Fin m, normalizedDeriv q
      (fun t : ℝ => (laurentCoeffRat n (j.val : ℤ) : ℝ) *
        (1 / (5 - t) ^ (j.val + 1))) (-5)) = _
    simp_rw [normalizedDeriv_const_mul, normalizedDeriv_inv_linear_choose]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, hAzero, zero_add, hD] at hd
  have hc := laurentCoeff_neg_eq_normalizedDeriv n (q + 1)
  have hm : 5570 * n + (q + 1) = m + q := by dsimp [m]; omega
  rw [hm] at hc
  simp only [Nat.cast_add, Nat.cast_one] at hc
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [laurentCoeffRat_cast, hc]
  dsimp only [m] at hd
  linear_combination -hd

/--
@isnad1 id=eq.0h1v.s5.7211fd6bfb1a from=translated src=- shape=3487779f vocab=e4d7d93b
-/
theorem poleShiftPolynomial_natDegree (n : ℕ) :
    (poleShiftPolynomial n).natDegree = 7430 * n - 2 := by
  rw [poleShiftPolynomial, natDegree_taylor, polynomialPart_natDegree]

/--
@isnad1 id=eq.0h2v.s7.4dad4c718eab from=translated src=- shape=c509404d vocab=fe26aec1
-/
theorem poleShiftPolynomial_aeval (n : ℕ) (t : ℂ) :
    aeval (t + 5) (poleShiftPolynomial n) = aeval t (polynomialPart n) := by
  simp [poleShiftPolynomial, taylor_apply, aeval_comp, map_ofNat]

/--
@isnad1 id=eq.1h2v.s7.6bcec027141e from=translated src=- shape=594f5fe4 vocab=a069c580
-/
theorem polynomialPart_pole_expansion (n : ℕ) (hn : 1 ≤ n) (t : ℂ) :
    aeval t (polynomialPart n) = ∑ q ∈ Finset.range (7430 * n - 1),
      (poleShiftCoeff n q : ℂ) * (t + 5) ^ q := by
  rw [← poleShiftPolynomial_aeval, aeval_def, eval₂_eq_sum_range,
    poleShiftPolynomial_natDegree]
  rw [show 7430 * n - 2 + 1 = 7430 * n - 1 by omega]
  rfl

/--
@isnad1 id=eq.1h2v.s8.e13424023257 from=translated src=- shape=23ace5e6 vocab=eb928496
-/
theorem polynomialPart_pole_laurent_expansion (n : ℕ) (hn : 1 ≤ n) (t : ℂ) :
    aeval t (polynomialPart n) = ∑ q ∈ Finset.range (7430 * n - 1),
      ((laurentCoeffRat n (-((q + 1 : ℕ) : ℤ)) -
        ∑ j : Fin (5570 * n + 1), ((j.val + q).choose q : ℚ) *
          laurentCoeffRat n (j.val : ℤ) / 10 ^ (j.val + q + 1) : ℚ) : ℂ) * (t + 5) ^ q := by
  rw [polynomialPart_pole_expansion n hn]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact_mod_cast poleShiftCoeff_laurent_formula n q

end PiIrrationality
