import Tengoku.TdaLib.TDA.Persistence.GaussianGram

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian kernel functions and their distance bound

Two unit vectors whose inner product is `exp (-r² / (2s²))` are at distance at most
`|r| / |s|`. This is the abstract content of Kusano–Fukumizu–Hiraoka, JMLR 18(189), 2018,
Appendix C, Lemma 16, eq. (25): it uses only `1 - e^{-t} ≤ t`. Both the birth–death
feature bound and the second-level bound for the Gaussian kernel on an RKHS are instances.

The Gaussian kernel of an arbitrary real inner product space `E` generates mathlib's RKHS
`RKHS.OfKernel`. Its kernel functions have unit norm and Gaussian inner products. With
Lean's division the bandwidth needs no sign hypothesis; at bandwidth zero all kernel
functions coincide and every bound reads `0 ≤ 0`.
-/

namespace TDA.Persistence.WeightedKernel

open Matrix
open scoped InnerProductSpace

/-! ## The scalar inequality and the unit-vector lemma -/

/-- `2 - 2 exp (-r² / (2s²)) ≤ r² / s²`, from `1 - t ≤ exp (-t)`. Both sides vanish at
`s = 0`.
@isnad1 id=le.0h2v.s7.2595a8871ac9 from=translated src=- shape=38daebe4 vocab=4684e443
-/
theorem two_sub_two_mul_exp_le (r s : ℝ) :
    2 - 2 * Real.exp (-r ^ 2 / (2 * s ^ 2)) ≤ r ^ 2 / s ^ 2 := by
  rcases eq_or_ne s 0 with rfl | _
  · norm_num
  · have h := Real.add_one_le_exp (-(r ^ 2 / s ^ 2) / 2)
    have he : -r ^ 2 / (2 * s ^ 2) = -(r ^ 2 / s ^ 2) / 2 := by ring
    rw [he]
    linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The squared distance of two unit vectors with a Gaussian inner product.
@isnad1 id=eq.3h5v.s8.66c058b487ae from=translated src=- shape=171fe5a4 vocab=8e186398
-/
theorem norm_sub_sq_eq_of_inner_eq_gaussian {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r s : ℝ} (huv : ⟪u, v⟫_ℝ = Real.exp (-r ^ 2 / (2 * s ^ 2))) :
    ‖u - v‖ ^ 2 = 2 - 2 * Real.exp (-r ^ 2 / (2 * s ^ 2)) := by
  rw [norm_sub_sq_real, hu, hv, huv]
  ring

/-- Gaussian unit-vector lemma, KFH18 Lemma 16, eq. (25), in an arbitrary real inner
product space.
@isnad1 id=le.3h5v.s7.477ebcf78660 from=translated src=- shape=eaaa8c6a vocab=128c7dd7
-/
theorem norm_sub_le_of_inner_eq_gaussian {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r s : ℝ} (huv : ⟪u, v⟫_ℝ = Real.exp (-r ^ 2 / (2 * s ^ 2))) :
    ‖u - v‖ ≤ |r| / |s| := by
  have hsq : (|r| / |s|) ^ 2 = r ^ 2 / s ^ 2 := by rw [div_pow, sq_abs, sq_abs]
  have hle : ‖u - v‖ ^ 2 ≤ (|r| / |s|) ^ 2 := by
    rw [norm_sub_sq_eq_of_inner_eq_gaussian hu hv huv, hsq]
    exact two_sub_two_mul_exp_le r s
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (abs_nonneg _) (abs_nonneg _))).mp hle

/-! ## Scalar kernels as operator-valued kernels -/

/-! ## The Gaussian RKHS of a real inner product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian kernel `exp (-‖a - b‖² / (2τ²))` on all of `E`, operator-valued.-/
noncomputable def gaussianKernelOp (τ : ℝ) : Matrix E E (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun a b => gaussianGram τ (id : E → E) a b • ContinuousLinearMap.id ℝ ℝ

omit [InnerProductSpace ℝ E] in
/--
@isnad1 id=eq.0h5v.s7.1038170c4c7d from=translated src=- shape=78f24d4e vocab=48e53712
-/
theorem gaussianKernelOp_apply (τ : ℝ) (a b : E) (t : ℝ) :
    gaussianKernelOp τ a b t = Real.exp (-‖a - b‖ ^ 2 / (2 * τ ^ 2)) * t := rfl

end TDA.Persistence.WeightedKernel
