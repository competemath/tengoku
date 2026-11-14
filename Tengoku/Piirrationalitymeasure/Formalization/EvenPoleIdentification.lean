import Tengoku.Piirrationalitymeasure.Formalization.EvenPoleLaurent
import Tengoku.Piirrationalitymeasure.Formalization.PartialFractionIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual Laurent derivatives identify both sides of the general partial fractions. -/

namespace PiIrrationality.EvenPole

open Polynomial

theorem numerator_signed (F : Polynomial ℤ) (m : ℕ) :
    numerator (signedNumeratorY F m) = C ((-1 : ℚ) ^ m) * numerator F := by
  simp [numerator, signedNumeratorY, mul_comp]

theorem numerator_aeval {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : Polynomial ℤ) (t : K) : aeval t (numerator F) = aeval (t ^ 2) F := by
  rw [numerator, show Int.castRingHom ℚ = algebraMap ℤ ℚ from Subsingleton.elim _ _,
    aeval_map_algebraMap ℚ, aeval_comp]
  simp

theorem Decomposition.eval {K : Type*} [Field K] [Algebra ℚ K]
    {F : Polynomial ℤ} {m : ℕ} {a b : Fin m → ℚ} (hF : Decomposition F m a b) (t : K) :
    (-1 : K) ^ m * aeval t (numerator F) =
      aeval t (part F m) * ((t + 5) ^ m * (t - 5) ^ m) +
        (∑ i : Fin m, (a i : K) * (t + 5) ^ i.val * (t - 5) ^ m) +
        (∑ i : Fin m, (b i : K) * (t - 5) ^ i.val * (t + 5) ^ m) := by
  unfold Decomposition at hF
  rw [numerator_signed] at hF
  have h := congrArg (aeval t) hF
  simp only [show Int.castRingHom ℚ = algebraMap ℤ ℚ from Subsingleton.elim _ _,
    map_add, map_sub, map_mul, map_sum, map_pow, aeval_map_algebraMap ℚ,
    aeval_C, aeval_X, map_ofNat] at h
  have hmap (q : ℚ) : (algebraMap ℚ K) q = (q : K) := map_ratCast _ q
  simpa only [hmap, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using h

theorem regularized_eq_of_decomposition {F : Polynomial ℤ} {m : ℕ}
    {a b : Fin m → ℚ} (hF : Decomposition F m a b) (t : ℝ) (ht : t ≠ 5) :
    regularized F m t = (∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) +
      (t + 5) ^ m * (aeval t (part F m) +
        (∑ i : Fin m, (b i : ℝ) * (t - 5) ^ i.val) / (t - 5) ^ m) := by
  have hD : (t - 5) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht)
  have h := hF.eval t
  rw [← Finset.sum_mul, ← Finset.sum_mul] at h
  rw [regularized, show 5 - t = -(t - 5) by ring, div_neg_power, div_eq_iff hD]
  field_simp at *
  linear_combination h

theorem normalizedDeriv_regularized_of_decomposition {F : Polynomial ℤ} {m : ℕ}
    {a b : Fin m → ℚ} (hF : Decomposition F m a b) (k : Fin m) :
    normalizedDeriv k.val (regularized F m) (-5) = (a k : ℝ) := by
  let f : ℝ → ℝ := fun t => aeval t (part F m) +
    (∑ i : Fin m, (b i : ℝ) * (t - 5) ^ i.val) / (t - 5) ^ m
  have hf : ContDiffAt ℝ k.val f (-5) := by
    dsimp [f]
    apply ((part F m).contDiff_aeval k.val).contDiffAt.add
    fun_prop (disch := norm_num)
  have hpoly : ContDiffAt ℝ k.val
      (fun t : ℝ => ∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) (-5) := by fun_prop
  have hroot : ContDiffAt ℝ k.val (fun t : ℝ => (t + 5) ^ m * f t) (-5) :=
    ((contDiffAt_id.add contDiffAt_const).pow _).mul hf
  have heq : regularized F m =ᶠ[nhds (-5 : ℝ)]
      (fun t : ℝ => (∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) + (t + 5) ^ m * f t) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-5 : ℝ) ≠ 5)] with t ht
    exact regularized_eq_of_decomposition hF t ht
  have hnorm := congrArg (fun x : ℝ => x / (k.val.factorial : ℝ))
    (heq.iteratedDeriv_eq k.val)
  change normalizedDeriv k.val (regularized F m) (-5) =
    normalizedDeriv k.val (fun t : ℝ =>
      (∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) + (t + 5) ^ m * f t) (-5) at hnorm
  rw [hnorm]
  have hsplit : normalizedDeriv k.val (fun t : ℝ =>
      (∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) + (t + 5) ^ m * f t) (-5) =
      normalizedDeriv k.val (fun t : ℝ => ∑ i : Fin m, (a i : ℝ) * (t + 5) ^ i.val) (-5) +
      normalizedDeriv k.val (fun t : ℝ => (t + 5) ^ m * f t) (-5) := by
    unfold normalizedDeriv
    rw [iteratedDeriv_fun_add hpoly hroot, add_div]
  rw [hsplit, normalizedDeriv_shift_polynomial,
    normalizedDeriv_shift_power_mul_zero k.val m k.isLt f hf, add_zero]

theorem Decomposition.left_eq {F : Polynomial ℤ} {m : ℕ} {a b : Fin m → ℚ}
    (hF : Decomposition F m a b) (k : Fin m) : a k = localCoeff F m k.val := by
  apply Rat.cast_injective (α := ℝ)
  rw [localCoeff_cast]
  exact (normalizedDeriv_regularized_of_decomposition hF k).symm

theorem Decomposition.right_eq {F : Polynomial ℤ} {m : ℕ} {a b : Fin m → ℚ}
    (hF : Decomposition F m a b) (k : Fin m) :
    b k = (-1 : ℚ) ^ (k.val + m) * localCoeff F m k.val := by
  have h := hF.reflect.left_eq k
  change (-1 : ℚ) ^ (k.val + m) * b k = _ at h
  rw [← h, ← mul_assoc, ← mul_pow]
  norm_num

theorem actual_decomposition (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    Decomposition F m (fun i => localCoeff F m i.val)
      (fun i => (-1 : ℚ) ^ (i.val + m) * localCoeff F m i.val) := by
  obtain ⟨a, b, hF⟩ := exists_decomposition F hm
  have ha : a = fun i => localCoeff F m i.val := funext hF.left_eq
  have hb : b = fun i => (-1 : ℚ) ^ (i.val + m) * localCoeff F m i.val :=
    funext hF.right_eq
  rwa [ha, hb] at hF

end PiIrrationality.EvenPole
