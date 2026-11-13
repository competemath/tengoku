import Tengoku.Nlalib.NLAlib.RandomMatrix.Gaussian.Wishart.SoftMin.InversePowerConcavity
import Tengoku.Nlalib.NLAlib.RandomMatrix.Gaussian.Wishart.SoftMin.GramTrace
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.QuadraticProbe

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regularized Gram resolvent derivatives

The resolvent approximation to the smallest eigenvalue of `GGᵀ + εI`
has coordinate second derivatives whose sum is at most twice the column
dimension. This supplies the global Laplacian bound for the operator
integration-by-parts argument.

Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A Gram matrix regularized by a scalar multiple of the identity.
Source: resolvent operator proof; atlas `wishart-lambda-min-tail` (helper).
atlas: inverse-power-gram-def-/
def regularizedGram (ε : ℝ) (G : Matrix ι κ ℝ) : Matrix ι ι ℝ := G * Gᵀ + ε • 1

omit [DecidableEq κ] in
/-- Positive regularization makes every real Gram matrix positive definite.
Source: Gram positivity; atlas `wishart-lambda-min-tail` (helper).-/
theorem regularizedGram_posDef {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    (regularizedGram ε G).PosDef := by
  have hG : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  exact Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)

omit [Fintype ι] [DecidableEq κ] in
/-- The exact quadratic expansion of the Gram curve in one matrix direction.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper).-/
theorem regularizedGram_add_smul (ε t : ℝ) (G E : Matrix ι κ ℝ) :
    regularizedGram ε (G + t • E) = regularizedGram ε G +
      t • (E * Gᵀ + G * Eᵀ) + t ^ 2 • (E * Eᵀ) := by
  simp only [regularizedGram, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, pow_two]
  module

omit [DecidableEq κ] in
/-- The first derivative of the regularized Gram curve.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper).-/
theorem hasDerivAt_regularizedGram_add_smul (ε : ℝ) (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => regularizedGram ε (G + x • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) t := by
  have hlin := ((hasDerivAt_id t).smul_const (E * Gᵀ + G * Eᵀ)).const_add
    (regularizedGram ε G)
  have hquad := ((hasDerivAt_id t).pow 2).smul_const (E * Eᵀ)
  have h := hlin.add hquad
  simpa only [regularizedGram_add_smul, id_eq, Pi.add_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, mul_one, one_smul, Nat.cast_ofNat] using! h

omit [DecidableEq κ] in
/-- The first Gram derivative has constant derivative `2EEᵀ`.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper).-/
theorem hasDerivAt_regularizedGram_first (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => E * Gᵀ + G * Eᵀ + (2 * x) • (E * Eᵀ))
      ((2 : ℝ) • (E * Eᵀ)) t := by
  simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul 2).smul_const (E * Eᵀ)
    |>.const_add (E * Gᵀ + G * Eᵀ)

/-- The explicit second derivative along one Gram direction after
composition with the resolvent approximation. Source: Gram chain rule;
atlas `wishart-lambda-min-tail` (helper).
atlas: inverse-power-gram-def-/
def gramSoftMinSecond (n : ℕ) (ε : ℝ) (G E : Matrix ι κ ℝ) : ℝ :=
  inversePowerSoftMinSecond n (regularizedGram ε G) (E * Gᵀ + G * Eᵀ) +
    inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ))

/-- The coordinate gradient of the resolvent regularized Gram functional.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper).
atlas: inverse-power-gram-def-/
def gramSoftMinGradient (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  (2 : ℝ) • (inversePowerSoftMinWeight n (regularizedGram ε G) * G)

omit [DecidableEq κ] in
/-- The Euler gradient contraction is a trace pairing with the Gram
matrix. Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper).-/
theorem frobInner_gramSoftMinGradient_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) :
    frobInner G (gramSoftMinGradient n ε G) =
      2 * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) * (G * Gᵀ)) := by
  rw [gramSoftMinGradient, frobInner_smul_right, frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  congr 1
  calc _ = Matrix.trace ((Gᵀ * inversePowerSoftMinWeight n (regularizedGram ε G)) * G) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (G * (Gᵀ * inversePowerSoftMinWeight n (regularizedGram ε G))) := by
          simpa only [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle Gᵀ (inversePowerSoftMinWeight n (regularizedGram ε G)) G)
    _ = Matrix.trace ((G * Gᵀ) * inversePowerSoftMinWeight n (regularizedGram ε G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

omit [DecidableEq κ] in
/-- The squared gradient is four times the quadratic gradient-weight
Gram trace. Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper).-/
theorem frobSq_gramSoftMinGradient_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    frobSq (gramSoftMinGradient n ε G) = 4 *
      Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) ^ 2 * (G * Gᵀ)) := by
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε G))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram ε G) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n hpd.posSemidef).isHermitian).eq
  rw [gramSoftMinGradient, frobSq_smul]
  norm_num only
  congr 1
  rw [frobSq, frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hP, pow_two]
  calc _ = Matrix.trace (Gᵀ * (inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G) * Gᵀ) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

/-- The first Gram chain coefficient along a coordinate line equals the
corresponding actual gradient entry at every point. Source: operator tail
proof; atlas `wishart-lambda-min-tail` (helper).-/
theorem inversePowerSoftMinFirst_gram_single_eq_gradient (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = gramSoftMinGradient n ε (G + t • E) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ) =
      E * (G + t • E)ᵀ + (G + t • E) * Eᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε (G + t • E)))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram ε (G + t • E)) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n
      (regularizedGram_posDef hε (G + t • E)).posSemidef).isHermitian).eq
  change inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = _
  rw [hD, inversePowerSoftMinFirst_eq_trace_weight_mul, trace_mul_gram_direction _ hP]
  rfl

/-- The coordinate Laplacian represented by the explicit Gram Hessian.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper).
atlas: inverse-power-gram-def-/
def gramSoftMinLaplacian (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, gramSoftMinSecond n ε G (Matrix.single i j 1)

/-- Contracting the inverse-power Hessian over all Gram coordinates gives
an exact finite sum of trace products. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper).-/
theorem sum_inversePowerHessianKernel_gram_direction_eq
    (R : Matrix ι ι ℝ) (hR : R.PosSemidef) (G : Matrix ι κ ℝ) (n : ℕ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerHessianKernel R (E * Gᵀ + G * Eᵀ) n) =
      ∑ a ∈ Finset.range (n + 1),
        (2 * Matrix.trace (R ^ (n + 2) * (G * Gᵀ)) +
          Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) +
          Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᵀ))) := by
  unfold inversePowerHessianKernel
  dsimp only
  calc _ = (∑ i, ∑ a ∈ Finset.range (n + 1), ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᵀ + G * Eᵀ) * R ^ (a + 1) *
          (E * Gᵀ + G * Eᵀ))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = (∑ a ∈ Finset.range (n + 1), ∑ i, ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᵀ + G * Eᵀ) * R ^ (a + 1) *
          (E * Gᵀ + G * Eᵀ))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have hX : (R ^ (n - a + 1))ᵀ = R ^ (n - a + 1) :=
        (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
      have hY : (R ^ (a + 1))ᵀ = R ^ (a + 1) :=
        (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
      rw [sum_trace_mul_gram_direction_mul_gram_direction _ _ hX hY G, ← pow_add]
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [show n - a + 1 + (a + 1) = n + 2 by omega]

/-- The exact finite resolvent Gram Laplacian in trace-power form. This
identity exposes the cancellations needed for the sharper limiting
Laplacian bound. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (helper).-/
theorem gramSoftMinLaplacian_eq (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let R := (regularizedGram ε G)⁻¹
    let T := Matrix.trace (R ^ n)
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) +
      4 * ((n : ℝ) + 1) * T ^ (-(n : ℝ)⁻¹ - 2) * Matrix.trace (R ^ (2 * n + 2) * (G * Gᵀ)) -
      T ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1),
          (2 * Matrix.trace (R ^ (n + 2) * (G * Gᵀ)) +
            Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) +
            Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᵀ))) := by
  dsimp only
  let R := (regularizedGram ε G)⁻¹
  have hR : R.PosSemidef := hpd.inv.posSemidef
  have hX : (R ^ (n + 1))ᵀ = R ^ (n + 1) :=
    (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
  have hsq := sum_trace_mul_gram_direction_sq (R ^ (n + 1)) hX G
  rw [← pow_mul, show (n + 1) * 2 = 2 * n + 2 by omega] at hsq
  have hk := sum_inversePowerHessianKernel_gram_direction_eq R hR G n
  dsimp only [R] at hsq hk
  have hfirst : (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ))) =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) := by
    simp only [inversePowerSoftMinFirst_eq_trace_weight_mul, Matrix.transpose_single,
      Matrix.single_mul_single_same, one_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_mul_single, op_smul_eq_smul, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.trace, Matrix.diag]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  unfold gramSoftMinLaplacian gramSoftMinSecond
  simp only [Finset.sum_add_distrib]
  rw [hfirst]
  unfold inversePowerSoftMinSecond
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsq, hk]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end NLAlib
