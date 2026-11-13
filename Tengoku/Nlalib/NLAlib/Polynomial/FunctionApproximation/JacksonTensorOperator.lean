import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.JacksonTensorCoordinate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The positive contracting tensor Jackson operator

The kernel integral is a positive contraction on arbitrary bounded observables
on the cube. For continuous observables it is exactly the coefficient-controlled
finite tensor polynomial already defined.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Section 2.2.
Atlas: `tensor-chebyshev-kernel-measure` (partial).
-/

noncomputable section

open Real MeasureTheory Set Finset Polynomial.Chebyshev

namespace NLAlib

/-- The actual positive tensor Jackson integral operator.-/
def tensorChebyshevJacksonOperator {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (M : ℕ) (r : EuclideanSpace ℝ ι) : ℝ :=
  ∫ x, tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * f (WithLp.toLp 2 x)
    ∂Measure.pi (fun _ => measureT)

/-- Only the observable's values on the closed cube affect its kernel integral.
@isnad1 id=eq.1h5v.s5.d830a44ad421 from=translated src=- shape=e8a83f31 vocab=09d69d53
-/
theorem tensorChebyshevJacksonOperator_congr {ι : Type*} [Fintype ι]
    {f g : EuclideanSpace ℝ ι → ℝ} (hfg : EqOn f g (chebyshevCube ι))
    (M : ℕ) (r : EuclideanSpace ℝ ι) :
    tensorChebyshevJacksonOperator f M r = tensorChebyshevJacksonOperator g M r := by
  apply integral_congr_ae
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  rw [hfg hx]

/-- Positivity of the actual tensor kernel operator on the whole closed cube.
Source: Musco--Musco--Shah--Urschel--West, Section 2.2.
atlas: tensor-chebyshev-kernel-measure (partial)
@isnad1 id=le.2h4v.s6.6979644cea6e from=translated src=- shape=901af5cc vocab=b4999377
-/
theorem tensorChebyshevJacksonOperator_nonneg {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ∀ x ∈ chebyshevCube ι, 0 ≤ f x)
    (M : ℕ) {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    0 ≤ tensorChebyshevJacksonOperator f M r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  exact mul_nonneg (tensorChebyshevJacksonKernel_nonneg M hx hr) (hf _ hx)

/-- The actual tensor Jackson operator contracts every uniform bound.
Source: Musco--Musco--Shah--Urschel--West, Section 2.2.
atlas: tensor-chebyshev-kernel-measure (partial)
@isnad1 id=le.2h5v.s6.992d37664d02 from=translated src=- shape=6a7f87ef vocab=c95534c4
-/
theorem abs_tensorChebyshevJacksonOperator_le {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {B : ℝ}
    (hB : ∀ x ∈ chebyshevCube ι, |f x| ≤ B) (M : ℕ)
    {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonOperator f M r| ≤ B := by
  rw [tensorChebyshevJacksonOperator, ← Real.norm_eq_abs]
  have hI : Integrable (fun x : ι → ℝ => B * tensorChebyshevJacksonKernel M x (WithLp.ofLp r))
      (Measure.pi (fun _ => measureT)) := integrable_pi_measureT_of_continuous (by fun_prop)
  refine (norm_integral_le_of_norm_le hI ?_).trans_eq ?_
  · filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
    have hp := tensorChebyshevJacksonKernel_nonneg M hx hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left (hB _ hx) hp).trans_eq (mul_comm _ _)
  · rw [integral_const_mul, integral_tensorChebyshevJacksonKernel, mul_one]

/-- The positive operator fixes every constant, so its norm is exactly one.
Source: Musco--Musco--Shah--Urschel--West, Section 2.2.
atlas: tensor-chebyshev-kernel-measure (partial)
@isnad1 id=eq.0h4v.s4.389abccadbd7 from=translated src=- shape=448de0b9 vocab=3e9b2b3f
-/
theorem tensorChebyshevJacksonOperator_const {ι : Type*} [Fintype ι]
    (c : ℝ) (M : ℕ) (r : EuclideanSpace ℝ ι) :
    tensorChebyshevJacksonOperator (fun _ => c) M r = c := by
  rw [tensorChebyshevJacksonOperator, integral_mul_const, integral_tensorChebyshevJacksonKernel,
    one_mul]

/-- For continuous inputs, the actual integral operator is exactly the finite
polynomial with damped normalized tensor coefficients.
@isnad1 id=eq.1h4v.s6.487065a7049a from=translated src=- shape=b900255c vocab=ddf55c90
-/
theorem tensorChebyshevJacksonOperator_eq_approx {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) (M : ℕ) (r : EuclideanSpace ℝ ι) :
    tensorChebyshevJacksonOperator f M r = tensorChebyshevJacksonApprox f M r :=
  (tensorChebyshevJacksonApprox_eq_integral hf M r).symm

/-- The same exact coefficient formula applies when continuity is obtained
only by extending a cube-Lipschitz observable.
@isnad1 id=eq.1h5v.s6.1fa41e694d13 from=translated src=- shape=4c09fe67 vocab=6751b87b
-/
theorem tensorChebyshevJacksonOperator_eq_approx_of_lipschitzOnWith
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (chebyshevCube ι)) (M : ℕ) (r : EuclideanSpace ℝ ι) :
    tensorChebyshevJacksonOperator f M r = tensorChebyshevJacksonApprox f M r := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  rw [tensorChebyshevJacksonOperator_congr hfg, tensorChebyshevJacksonApprox_congr hfg]
  exact tensorChebyshevJacksonOperator_eq_approx hg.continuous M r

/-- The actual positive kernel operator obeys the coordinate Lipschitz error
bound on the closed cube with the exact source constant.
Source: Musco--Musco--Shah--Urschel--West, Theorem 2.5.
atlas: tensor-chebyshev-kernel-measure (partial)
@isnad1 id=le.3h5v.s8.dab5d5aaf109 from=translated src=- shape=10092844 vocab=6ec66816
-/
theorem abs_tensorChebyshevJacksonOperator_sub_le_of_coordinate_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ} (L : ι → NNReal)
    (hf : ∀ i, ∀ x ∈ chebyshevCube ι, ∀ y ∈ chebyshevCube ι,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (L i : ℝ) * |x i - y i|)
    {M : ℕ} (hM : 1 ≤ M) {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonOperator f M r - f r| ≤ (6 / M) * ∑ i, (L i : ℝ) := by
  rw [tensorChebyshevJacksonOperator_eq_approx_of_lipschitzOnWith
    (lipschitzOnWith_sum_of_coordinate_chebyshevCube L hf)]
  exact abs_tensorChebyshevJacksonApprox_sub_le_of_coordinate_lipschitz L hf hM hr

end NLAlib
