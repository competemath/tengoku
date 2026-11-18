import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowRegularSingular.norm_exp_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.norm_rayLog_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.exp_ray_norm_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.rayPowerInverse_mul_rayPower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.rayPower_mul_rayPowerInverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.rayPower_mulVec_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.rayPowerInverse_mulVec_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRegularSingular.exists_polynomial_bounds` (it only prints; the queue checks the axioms of every declaration). -/
/-! Polynomial bounds for the regular-singular matrix power and its inverse.
The matrix exponential is represented through its continuous linear operator,
whose norm is submultiplicative.  This isolates the bound for arbitrary repeated
eigenvalues and nilpotent blocks; it does not assert a general rational-system
normal form or an analytic realization theorem. -/
set_option autoImplicit false
noncomputable section
namespace WasowRegularSingular
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]
/--
@isnad1 id=le.0h2v.s6.c20b79c18dfb from=translated src=- shape=2093cc7e vocab=803f3f53
-/
theorem norm_exp_le (x : A) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hreal : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * ‖x‖ ^ n)
      (Real.exp ‖x‖) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).norm_le_of_bounded hreal
  intro n
  simp only [norm_smul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (inv_nonneg.mpr (Nat.cast_nonneg _))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Nontrivial E]

/-- A fixed branch of the logarithm along the ray.-/
def rayLog (θ r : ℝ) : ℂ := (Real.log r : ℂ) + (θ : ℂ) * Complex.I

/--
@isnad1 id=le.1h2v.s5.14e72319ffa9 from=translated src=- shape=db965e52 vocab=8ab93684
-/
theorem norm_rayLog_le (θ : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖rayLog θ r‖ ≤ Real.log r + |θ| := by
  calc
    ‖rayLog θ r‖ ≤ ‖(Real.log r : ℂ)‖ + ‖(θ : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = Real.log r + |θ| := by simp [abs_of_nonneg (Real.log_nonneg hr)]

/--
@isnad1 id=le.1h4v.s9.5114f175c82a from=translated src=- shape=33cc198d vocab=73b6574a
-/
theorem exp_ray_norm_bound (G : E →L[ℂ] E) (θ : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖NormedSpace.exp (rayLog θ r • G)‖ ≤
      Real.exp (|θ| * ‖G‖) * r ^ ‖G‖ := by
  calc
    ‖NormedSpace.exp (rayLog θ r • G)‖ ≤ Real.exp ‖rayLog θ r • G‖ := norm_exp_le _
    _ ≤ Real.exp ((Real.log r + |θ|) * ‖G‖) := by
      apply Real.exp_le_exp.mpr
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_rayLog_le θ hr) (norm_nonneg _)
    _ = Real.exp (|θ| * ‖G‖) * r ^ ‖G‖ := by
      rw [add_mul, Real.exp_add, Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hr)]
      ring

end WasowRegularSingular
namespace WasowRegularSingular
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The actual matrix action, equipped with its operator norm.-/
def matrixOperator (G : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  G.mulVecLin.toContinuousLinearMap

/-- The matrix of `exp ((log r + i θ) G)` in standard coordinates.-/
def rayPower (G : Matrix ι ι ℂ) (θ r : ℝ) : Matrix ι ι ℂ :=
  LinearMap.toMatrix' (NormedSpace.exp (rayLog θ r • matrixOperator G)).toLinearMap

/-- The matrix of the negative exponential, giving a two-sided inverse.-/
def rayPowerInverse (G : Matrix ι ι ℂ) (θ r : ℝ) : Matrix ι ι ℂ :=
  LinearMap.toMatrix' (NormedSpace.exp (-(rayLog θ r • matrixOperator G))).toLinearMap

omit [Nonempty ι] in
/--
@isnad1 id=eq.0h4v.s6.bd79e040652f from=translated src=- shape=c2d363fd vocab=c4e78fbe
-/
theorem rayPowerInverse_mul_rayPower (G : Matrix ι ι ℂ) (θ r : ℝ) :
    rayPowerInverse G θ r * rayPower G θ r = 1 := by
  let : NormedAlgebra ℚ ((ι → ℂ) →L[ℂ] (ι → ℂ)) :=
    .restrictScalars ℚ ℂ _
  unfold rayPowerInverse rayPower
  rw [← LinearMap.toMatrix'_mul, ← ContinuousLinearMap.toLinearMap_mul]
  have hh : NormedSpace.exp (-(rayLog θ r • matrixOperator G)) *
      NormedSpace.exp (rayLog θ r • matrixOperator G) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (rayLog θ r • matrixOperator G)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  rw [hh, ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix'_one]

omit [Nonempty ι] in
/--
@isnad1 id=eq.0h4v.s6.09df1e2aa113 from=translated src=- shape=c2d363fd vocab=c4e78fbe
-/
theorem rayPower_mul_rayPowerInverse (G : Matrix ι ι ℂ) (θ r : ℝ) :
    rayPower G θ r * rayPowerInverse G θ r = 1 := by
  let : NormedAlgebra ℚ ((ι → ℂ) →L[ℂ] (ι → ℂ)) :=
    .restrictScalars ℚ ℂ _
  unfold rayPowerInverse rayPower
  rw [← LinearMap.toMatrix'_mul, ← ContinuousLinearMap.toLinearMap_mul]
  have hh : NormedSpace.exp (rayLog θ r • matrixOperator G) *
      NormedSpace.exp (-(rayLog θ r • matrixOperator G)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (rayLog θ r • matrixOperator G)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  rw [hh, ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix'_one]

/--
@isnad1 id=le.1h5v.s9.3de3784d5b4e from=translated src=- shape=dbb33cb2 vocab=932138d8
-/
theorem rayPower_mulVec_bound (G : Matrix ι ι ℂ) (θ : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (x : ι → ℂ) :
    ‖(rayPower G θ r).mulVec x‖ ≤
      Real.exp (|θ| * ‖matrixOperator G‖) * r ^ ‖matrixOperator G‖ * ‖x‖ := by
  unfold rayPower
  rw [LinearMap.toMatrix'_mulVec]
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (exp_ray_norm_bound _ θ hr) (norm_nonneg x))

/--
@isnad1 id=le.1h5v.s9.545ee986d385 from=translated src=- shape=dbb33cb2 vocab=0d5d1103
-/
theorem rayPowerInverse_mulVec_bound (G : Matrix ι ι ℂ) (θ : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (x : ι → ℂ) :
    ‖(rayPowerInverse G θ r).mulVec x‖ ≤
      Real.exp (|θ| * ‖matrixOperator G‖) * r ^ ‖matrixOperator G‖ * ‖x‖ := by
  unfold rayPowerInverse
  rw [LinearMap.toMatrix'_mulVec]
  apply (ContinuousLinearMap.le_opNorm _ x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  simpa only [smul_neg, norm_neg] using exp_ray_norm_bound (-matrixOperator G) θ hr

/-- Both matrix factors have polynomial operator growth on the ray.  The
exponent is the norm of the fixed matrix acting on the finite-dimensional
sup-norm space; no diagonalizability or Jordan normal form is required.
@isnad1 id=ex.0h3v.s7.463d50cb03d8 from=translated src=- shape=09e5c60e vocab=57aa58d3
-/
theorem exists_polynomial_bounds (G : Matrix ι ι ℂ) (θ : ℝ) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : ι → ℂ,
      ‖(rayPower G θ r).mulVec x‖ ≤ C * r ^ K * ‖x‖ ∧
      ‖(rayPowerInverse G θ r).mulVec x‖ ≤ C * r ^ K * ‖x‖ := by
  refine ⟨Real.exp (|θ| * ‖matrixOperator G‖), ‖matrixOperator G‖,
    Real.exp_pos _, norm_nonneg _, ?_⟩
  intro r hr x
  exact ⟨rayPower_mulVec_bound G θ hr x, rayPowerInverse_mulVec_bound G θ hr x⟩

end WasowRegularSingular

