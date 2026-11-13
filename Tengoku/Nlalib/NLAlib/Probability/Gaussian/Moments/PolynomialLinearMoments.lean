import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Calculus.ProductIntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial products of Gaussian linear forms

Every product is genuinely integrable. Coordinate Stein proves the covariance
recursion for arbitrary products, including repeated factors.
Source: Stein 1981; Janson 1997, *Gaussian Hilbert Spaces*, Thm 1.28.
Supports atlas `isserlis`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

/-- A finite linear form has an explicit polynomial-growth bound.
Source: finite coordinate norm comparison; supports `isserlis`.
@isnad1 id=le.0h3v.s6.66b2660af3c2 from=translated src=- shape=4ddb69c6 vocab=3f81d429
-/
theorem abs_dotProduct_le_sum_abs_mul_one_add_norm {n : ℕ} (a x : Fin n → ℝ) :
    |a ⬝ᵥ x| ≤ (∑ i, |a i|) * (1 + ‖x‖) := by
  rw [dotProduct, Finset.sum_mul]
  calc _ ≤ ∑ i, |a i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      gcongr
      have hh := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at hh
      linarith

/-- A finite product of linear forms is explicitly bounded by a polynomial
in the ambient coordinate norm. Source: Stein 1981 (Gaussian integration by parts).
@isnad1 id=le.0h5v.s7.a7a9144eed8f from=translated src=- shape=d53cf2af vocab=a47a8c6e
-/
theorem abs_prod_dotProduct_le_polynomial
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    |∏ j ∈ s, a j ⬝ᵥ x| ≤ (∏ j ∈ s, ∑ i, |a j i|) * (1 + ‖x‖) ^ s.card := by
  rw [Finset.abs_prod]
  calc
    _ ≤ (∏ j ∈ s, (∑ i, |a j i|) * (1 + ‖x‖)) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j _
      exact abs_dotProduct_le_sum_abs_mul_one_add_norm (a j) x
    _ = _ := (Finset.prod_mul_pow_card).symm

/-- Every finite product of Gaussian linear forms has finite absolute first
moment. Source: Stein 1981 (Gaussian integration by parts); supports `isserlis`.
@isnad1 id=integrab.0h4v.s6.bc1635d28541 from=translated src=- shape=16ab6e05 vocab=b5a3dc95
-/
theorem integrable_prod_dotProduct_gaussianVector
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => ∏ j ∈ s, a j ⬝ᵥ x)
      (gaussianVector _) := by
  apply integrable_gaussianVector_of_polynomial_growth
    (Measurable.aemeasurable (by simp only [dotProduct]; fun_prop)) _ s.card
  exact abs_prod_dotProduct_le_polynomial s a

/-- Multiplying such a product by any one linear form remains integrable.
Source: Stein 1981 (Gaussian integration by parts); supports `isserlis`.
@isnad1 id=integrab.0h5v.s6.1fdcfc98f9b5 from=translated src=- shape=1d8fc03b vocab=1381e0f7
-/
theorem integrable_dotProduct_mul_prod_gaussianVector
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) (b : Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x)
      (gaussianVector _) := by
  apply integrable_gaussianVector_of_polynomial_growth
    (Measurable.aemeasurable (by simp only [dotProduct]; fun_prop))
    ((∑ i, |b i|) * ∏ j ∈ s, ∑ i, |a j i|) (s.card + 1)
  intro x
  rw [abs_mul, pow_succ]
  calc _ ≤ ((∑ i, |b i|) * (1 + ‖x‖)) *
      ((∏ j ∈ s, ∑ i, |a j i|) * (1 + ‖x‖) ^ s.card) :=
        mul_le_mul (abs_dotProduct_le_sum_abs_mul_one_add_norm b x)
          (abs_prod_dotProduct_le_polynomial s a x) (abs_nonneg _)
          (by positivity)
    _ = _ := by ring

/-- Updating one Gaussian coordinate differentiates a linear form by its
coefficient in that coordinate. Source: Stein 1981 (Gaussian integration by parts).
@isnad1 id=hasderiv.0h5v.s6.eb6085a461d9 from=translated src=- shape=90935e8f vocab=a07d6235
-/
theorem hasDerivAt_dotProduct_update {n : ℕ} (a x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun y => a ⬝ᵥ Function.update x i y) (a i) t := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ j, (a j) • ContinuousLinearMap.proj j
  have hh := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
  have hf : (fun y => a ⬝ᵥ Function.update x i y) = L ∘ Function.update x i := by
    funext y
    simp [L, dotProduct]
  rw [hf]
  exact hh.congr_deriv (by simp [L, Pi.single_apply])

/-- Coordinate Stein for an arbitrary product of linear forms. All derivatives
and Gaussian products are proved integrable; repeated factors are counted by
their separate positions. Source: Stein 1981 (Gaussian integration by parts).
@isnad1 id=eq.0h5v.s7.a6c1677708fd from=translated src=- shape=eaaa0648 vocab=d5e6db1e
-/
theorem integral_coordinate_mul_prod_dotProduct_gaussianVector
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    (a : ι → Fin n → ℝ) (i : Fin n) :
    ∫ x : Fin n → ℝ, x i * ∏ j ∈ s, a j ⬝ᵥ x
        ∂(gaussianVector _) =
      ∑ j ∈ s, a j i * ∫ x : Fin n → ℝ, ∏ k ∈ s.erase j, a k ⬝ᵥ x
        ∂(gaussianVector _) := by
  let f : (Fin n → ℝ) → ℝ := fun x => ∏ j ∈ s, a j ⬝ᵥ x
  let df : (Fin n → ℝ) → ℝ := fun x =>
    ∑ j ∈ s, a j i * ∏ k ∈ s.erase j, a k ⬝ᵥ x
  have hupdate : ∀ x t, HasDerivAt (fun y => f (Function.update x i y))
      (df (Function.update x i t)) t := by
    intro x t
    have hh := HasDerivAt.fun_finsetProd (u := s)
      (fun j (_ : j ∈ s) => hasDerivAt_dotProduct_update (a j) x i t)
    exact hh.congr_deriv (by
      dsimp only [df]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_eq_mul, mul_comm])
  have hfi := integrable_prod_dotProduct_gaussianVector s a
  have hxfi : Integrable (fun x : Fin n → ℝ => x i * f x)
      (gaussianVector _) := by
    have hh := integrable_dotProduct_mul_prod_gaussianVector s a (Pi.single i 1)
    simpa only [single_dotProduct, one_mul, f] using hh
  have hdfi : Integrable df (gaussianVector _) :=
    integrable_finsetSum s (fun j _ =>
      (integrable_prod_dotProduct_gaussianVector (s.erase j) a).const_mul (a j i))
  have hh := integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update f df i
    hupdate hfi hxfi hdfi
  rw [hh]
  dsimp only [df]
  rw [integral_finsetSum s (fun j _ =>
    (integrable_prod_dotProduct_gaussianVector (s.erase j) a).const_mul (a j i))]
  simp only [integral_const_mul]

/-- Covariance Stein recursion for products of arbitrary standard-Gaussian
linear forms. It includes repeated coefficient vectors and every finite
product length. Source: Janson 1997, Thm 1.28 (the Wick recursion); supports `isserlis`.
@isnad1 id=eq.0h5v.s7.b02f5fa83366 from=translated src=- shape=7b7e86e3 vocab=d5e6db1e
-/
theorem integral_dotProduct_mul_prod_gaussianVector
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    (a : ι → Fin n → ℝ) (b : Fin n → ℝ) :
    ∫ x : Fin n → ℝ, (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x
        ∂(gaussianVector _) =
      ∑ j ∈ s, (b ⬝ᵥ a j) * ∫ x : Fin n → ℝ, ∏ k ∈ s.erase j, a k ⬝ᵥ x
        ∂(gaussianVector _) := by
  have hcoord : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => x i * ∏ j ∈ s, a j ⬝ᵥ x)
      (gaussianVector _) := by
    intro i
    have hh := integrable_dotProduct_mul_prod_gaussianVector s a (Pi.single i 1)
    simpa only [single_dotProduct, one_mul] using hh
  have hexpand : ∀ x : Fin n → ℝ, (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x =
      ∑ i, b i * (x i * ∏ j ∈ s, a j ⬝ᵥ x) := by
    intro x
    simp only [dotProduct, Finset.sum_mul, mul_assoc]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => (hcoord i).const_mul (b i))]
  simp_rw [integral_const_mul, integral_coordinate_mul_prod_dotProduct_gaussianVector]
  simp only [Finset.mul_sum, dotProduct, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end NLAlib
