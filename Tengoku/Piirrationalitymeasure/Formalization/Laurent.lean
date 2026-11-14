import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Laurent-coefficient interface for the pole at `t = -5`.

The regularized function is holomorphic at the pole; its normalized
derivatives are the Laurent coefficients used in Section 2.2.  The valuation
inequalities are proved in later files, after the finite binomial expansion is
introduced.
-/

namespace PiIrrationality

noncomputable def regularizedRat (n : ℕ) (t : ℚ) : ℚ :=
  5 * t ^ (2 * 1857 * n) * (t^4 + 6 * t^2 + 25) ^ (3714 * n) /
    (5 - t) ^ (5570 * n + 1)

theorem regularizedRat_eq_mul (n : ℕ) (t : ℚ)
    (ht : t ≠ 5) (ht' : t ≠ -5) :
    regularizedRat n t = (t + 5) ^ (5570 * n + 1) * rationalFunction n t := by
  unfold regularizedRat rationalFunction
  have hfactor : 25 - t^2 = (t + 5) * (5 - t) := by ring
  rw [hfactor, mul_pow]
  have h₁ : t + 5 ≠ 0 := by
    intro h
    apply ht'
    linarith
  have h₂ : 5 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  field_simp [h₁, h₂]

noncomputable def regularized (n : ℕ) (t : ℝ) : ℝ :=
  5 * t ^ (2 * 1857 * n) * (t^4 + 6 * t^2 + 25) ^ (3714 * n) /
    (5 - t) ^ (5570 * n + 1)

noncomputable def regularizedZpowCore (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * 1857 * n) * (((t + 1)^2 + 4) ^ (3714 * n)) *
    (((t - 1)^2 + 4) ^ (3714 * n)) *
    (5 - t) ^ (-(5570 * n + 1) : ℤ)

theorem regularizedZpowCore_at_pole_eq (n : ℕ) :
    5 * regularizedZpowCore n (-5) = regularized n (-5) := by
  unfold regularizedZpowCore regularized
  rw [zpow_neg]
  norm_num [zpow_natCast]
  field_simp
  have hexp : (5570 * (↑n : ℤ) + 1 : ℤ) = ((n * 5570 + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast, pow_add]
  rw [← mul_pow]
  rw [pow_add]
  ring

theorem regularized_eventuallyEq_ZpowCore (n : ℕ) :
    (regularized n) =ᶠ[nhds (-5 : ℝ)]
      (fun t => 5 * regularizedZpowCore n t) := by
  filter_upwards [eventually_ne_nhds (show (-5 : ℝ) ≠ 5 by norm_num)] with t ht
  unfold regularized regularizedZpowCore
  rw [zpow_neg]
  have hexp : (5570 * (n : ℤ) + 1 : ℤ) = ((5570 * n + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast]
  have hquartic : t^4 + 6 * t^2 + 25 =
      (((t + 1)^2 + 4) * ((t - 1)^2 + 4)) := by ring
  rw [hquartic]
  have hden : 5 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  field_simp [hden]
  rw [mul_pow]
  ring

theorem regularized_quartic_factorization (n : ℕ) (t : ℝ) :
    regularized n t =
      5 * t ^ (2 * 1857 * n) *
        (((t + 1)^2 + 4) * ((t - 1)^2 + 4)) ^ (3714 * n) /
        (5 - t) ^ (5570 * n + 1) := by
  unfold regularized
  congr 2
  ring

theorem regularized_six_factor_shape (n : ℕ) (t : ℝ) :
    regularized n t =
      5 * t ^ (2 * 1857 * n) *
        ((t + 1)^2 + 4) ^ (3714 * n) *
        ((t - 1)^2 + 4) ^ (3714 * n) /
        (5 - t) ^ (5570 * n + 1) := by
  rw [regularized_quartic_factorization, mul_pow]
  ring

noncomputable def normalizedDeriv (k : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  iteratedDeriv k f x / k.factorial

theorem normalizedDeriv_regularized_eq_ZpowCore (n k : ℕ) :
    normalizedDeriv k (regularized n) (-5) =
      5 * normalizedDeriv k (regularizedZpowCore n) (-5) := by
  unfold normalizedDeriv
  have hder := (regularized_eventuallyEq_ZpowCore n).iteratedDeriv_eq k
  rw [hder]
  rw [iteratedDeriv_const_mul_field]
  ring

theorem normalized_inv_linear_deriv (M k : ℕ) (x : ℝ) :
    normalizedDeriv k (fun t : ℝ => (5 - t) ^ (-M : ℤ)) x =
      ((-1 : ℝ) ^ k *
        (∏ i ∈ Finset.range k, ((-(M : ℝ)) - i)) *
        (5 - x) ^ (-(M : ℤ) - k)) / (k.factorial : ℝ) := by
  unfold normalizedDeriv
  have hcomp := iteratedDeriv_comp_const_sub k
    (fun z : ℝ => z ^ (-M : ℤ)) 5
  rw [congrFun hcomp x]
  simp only [smul_eq_mul]
  have hz : iteratedDeriv k (fun z : ℝ => z ^ (-M : ℤ)) (5 - x) =
      (∏ i ∈ Finset.range k, ((-(M : ℝ)) - i)) *
        (5 - x) ^ (-(M : ℤ) - k) := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
    norm_num
  rw [hz]
  ring

noncomputable def laurentCoeff (n : ℕ) (j : ℤ) : ℝ :=
  if j ≤ 5570 * n then
    normalizedDeriv (5570 * (n : ℤ) - j).toNat (regularized n) (-5)
  else 0

theorem regularized_denominator_at_pole (n : ℕ) :
    (5 - (-5 : ℝ)) ^ (5570 * n + 1) ≠ 0 := by
  norm_num

theorem regularized_contDiffAt (n : ℕ) :
    ContDiffAt ℝ ⊤ (regularized n) (-5) := by
  unfold regularized
  have hden : (5 - (-5 : ℝ)) ^ (5570 * n + 1) ≠ 0 := by
    norm_num
  fun_prop (disch := aesop)

theorem laurentCoeff_is_real (n : ℕ) (j : ℤ) :
    ∃ x : ℝ, laurentCoeff n j = x := by
  exact ⟨laurentCoeff n j, rfl⟩

theorem laurentCoeff_eq_iteratedDeriv (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ 5570 * n) :
    laurentCoeff n j =
      iteratedDeriv (5570 * n - j.toNat) (regularized n) (-5) /
        (5570 * n - j.toNat).factorial := by
  have horder : (5570 * (n : ℤ) - j).toNat = 5570 * n - j.toNat := by omega
  simp only [laurentCoeff, ite_eq_left hj.2, normalizedDeriv, horder]

theorem laurentCoeff_eq_normalizedDeriv (n : ℕ) (j : ℤ)
    (hj : j ≤ 5570 * (n : ℤ)) :
    laurentCoeff n j =
      normalizedDeriv (5570 * (n : ℤ) - j).toNat (regularized n) (-5) := by
  simp only [laurentCoeff, ite_eq_left hj]

theorem laurentCoeff_neg_eq_normalizedDeriv (n k : ℕ) :
    laurentCoeff n (-(k : ℤ)) =
      normalizedDeriv (5570 * n + k) (regularized n) (-5) := by
  have hj : -(k : ℤ) ≤ 5570 * (n : ℤ) := by omega
  have horder : (5570 * (n : ℤ) - -(k : ℤ)).toNat = 5570 * n + k := by omega
  rw [laurentCoeff_eq_normalizedDeriv n _ hj, horder]

theorem laurentCoeff_eq_normalizedZpowCore (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ 5570 * n) :
    laurentCoeff n j =
      5 * normalizedDeriv (5570 * n - j.toNat)
        (regularizedZpowCore n) (-5) := by
  rw [laurentCoeff_eq_iteratedDeriv n j hj]
  change normalizedDeriv (5570 * n - j.toNat) (regularized n) (-5) = _
  rw [normalizedDeriv_regularized_eq_ZpowCore]

theorem laurentCoeff_zero_of_outside (n : ℕ) (j : ℤ)
    (h : 5570 * (n : ℤ) < j) : laurentCoeff n j = 0 := by
  simp only [laurentCoeff, ite_eq_right (not_le.mpr h)]

theorem laurentCoeff_zero_zero : laurentCoeff 0 0 = (1 : ℝ) / 2 := by
  simp [laurentCoeff, normalizedDeriv, regularized]
  norm_num

theorem laurentCoeff_zero_neg_one : laurentCoeff 0 (-1) = (1 : ℝ) / 20 := by
  have hreg : regularized 0 = (fun t : ℝ => 5 / (5 - t)) := by
    funext t
    simp [regularized]
  have hd : HasDerivAt (fun t : ℝ => 5 / (5 - t)) ((1 : ℝ) / 20) (-5) := by
    convert! (hasDerivAt_const (-5 : ℝ) (5 : ℝ)).div
      ((hasDerivAt_const (-5 : ℝ) (5 : ℝ)).sub (hasDerivAt_id (-5)))
      (by norm_num) using 1 <;> norm_num [Pi.div_apply, Pi.sub_apply, id_eq]
  change laurentCoeff 0 (-(1 : ℕ) : ℤ) = _
  rw [laurentCoeff_neg_eq_normalizedDeriv, hreg]
  norm_num [normalizedDeriv, iteratedDeriv_one, hd.deriv]

theorem laurentCoeff_top (n : ℕ) :
    laurentCoeff n (5570 * n : ℤ) = regularized n (-5) := by
  simp [laurentCoeff, normalizedDeriv]

theorem regularized_at_pole_eq (n : ℕ) :
    regularized n (-5) =
      5 * (5 : ℝ) ^ (2 * 1857 * n) * (800 : ℝ) ^ (3714 * n) /
        (10 : ℝ) ^ (5570 * n + 1) := by
  unfold regularized
  norm_num

theorem regularized_at_pole_pos (n : ℕ) : 0 < regularized n (-5) := by
  rw [regularized_at_pole_eq]
  have hfive : 0 < (5 : ℝ) ^ (2 * 1857 * n) := by positivity
  have height : 0 < (800 : ℝ) ^ (3714 * n) := by positivity
  have hten : 0 < (10 : ℝ) ^ (5570 * n + 1) := by positivity
  positivity

theorem laurentCoeff_top_pos (n : ℕ) :
    0 < laurentCoeff n (5570 * n : ℤ) := by
  rw [laurentCoeff_top]
  exact regularized_at_pole_pos n

end PiIrrationality
