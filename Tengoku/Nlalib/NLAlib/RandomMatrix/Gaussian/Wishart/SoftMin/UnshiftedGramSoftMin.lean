import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds
import Tengoku.Nlalib.NLAlib.RandomMatrix.Gaussian.Wishart.SoftMin.InversePowerLimit
import Tengoku.Nlalib.NLAlib.RandomMatrix.Gaussian.Wishart.SoftMin.GramSoftMinSpectral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite unshifted inverse-power Gram bounds

The inverse-power approximation to the minimum of a positive definite Gram
matrix satisfies the sharp hard-edge Laplacian inequality at every finite
positive power. Positive trace-product defects supply the dimension correction,
without an identity shift or any eigenvalue-separation condition.

Source: the user's finite inverse-power operator refinement.
Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq κ] in
/-- Zero regularization is the original Gram matrix. Source: the Gram
definition; atlas `wishart-lambda-min-tail` (helper).-/
@[simp] theorem regularizedGram_zero (G : Matrix ι κ ℝ) : regularizedGram 0 G = G * Gᵀ := by
  simp only [regularizedGram, zero_smul, add_zero]

omit [Fintype κ] [DecidableEq κ] in
/-- Products of positive semidefinite trace powers dominate the trace
power of their product. Source: nonnegative eigenvalue cross terms;
atlas `wishart-lambda-min-tail` (finite defect helper).
atlas: inverse-power-gram-laplacian-/
theorem trace_pow_le_trace_pow_mul_trace_pow {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (a b : ℕ) :
    Matrix.trace (R ^ (a + b)) ≤ Matrix.trace (R ^ a) * Matrix.trace (R ^ b) := by
  rw [trace_pow_eq_sum_eigenvalues hR.isHermitian,
    trace_pow_eq_sum_eigenvalues hR.isHermitian,
    trace_pow_eq_sum_eigenvalues hR.isHermitian, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => pow_nonneg (hR.eigenvalues_nonneg j) b)
      (Finset.mem_univ i)) (pow_nonneg (hR.eigenvalues_nonneg i) a)

omit [DecidableEq κ] in
/-- At an invertible Gram matrix, its inverse trace power contracts with
the Gram matrix by lowering the exponent by one. Source: inverse identity;
atlas `wishart-lambda-min-tail` (finite calculus helper).-/
theorem trace_inv_gram_pow_succ_mul_gram (G : Matrix ι κ ℝ)
    (hpd : (G * Gᵀ).PosDef) (a : ℕ) :
    Matrix.trace ((G * Gᵀ)⁻¹ ^ (a + 1) * (G * Gᵀ)) =
      Matrix.trace ((G * Gᵀ)⁻¹ ^ a) := by
  rw [pow_succ, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit), Matrix.mul_one]

omit [DecidableEq κ] in
/-- The unshifted Gram gradient energy has an exact inverse trace-power
formula. Source: the user's finite operator refinement; atlas
`wishart-lambda-min-tail` (helper).
atlas: inverse-power-gram-gradient-energy-/
theorem frobSq_gramSoftMinGradient_unshifted_eq (n : ℕ)
    (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) :
    let R := (G * Gᵀ)⁻¹
    let c := Matrix.trace (R ^ n) ^ (-(n : ℝ)⁻¹ - 1)
    frobSq (gramSoftMinGradient n 0 G) = 4 * c ^ 2 * Matrix.trace (R ^ (2 * n + 1)) := by
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := frobSq_gramSoftMinGradient_eq_trace n 0 G hreg
  simp only [regularizedGram_zero] at h
  rw [inversePowerSoftMinWeight, pow_two, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← pow_add,
    show n + 1 + (n + 1) = (2 * n + 1) + 1 by omega,
    trace_inv_gram_pow_succ_mul_gram G hpd] at h
  simpa only [pow_two, mul_assoc] using h

omit [Fintype κ] [DecidableEq κ] in
/-- The inverse-power minimum is below the reciprocal of every inverse
eigenvalue. Source: one summand of the positive trace power;
atlas `wishart-lambda-min-tail` (cutoff helper).-/
theorem inversePowerSoftMin_le_inv_inverse_eigenvalue [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι) :
    inversePowerSoftMin n A ≤ (hA.inv.isHermitian.eigenvalues i)⁻¹ := by
  have hb := hA.inv.eigenvalues_pos i
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsingle : hA.inv.isHermitian.eigenvalues i ^ n ≤ Matrix.trace (A⁻¹ ^ n) := by
    rw [trace_pow_eq_sum_eigenvalues hA.inv.isHermitian]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (hA.inv.eigenvalues_pos j).le n)
      (Finset.mem_univ i)
  have h := Real.rpow_le_rpow_of_nonpos (pow_pos hb n) hsingle
    (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))
  rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hb.le, mul_neg,
    mul_inv_cancel₀ hn0, Real.rpow_neg_one] at h
  exact h

omit [DecidableEq κ] in
/-- A Gram matrix outside the positive definite domain has zero total
inverse. Source: Gram positivity and the singular inverse convention;
atlas `wishart-lambda-min-tail` (cutoff helper).-/
theorem inv_gram_eq_zero_of_not_posDef (G : Matrix ι κ ℝ)
    (hnot : ¬(G * Gᵀ).PosDef) : (G * Gᵀ)⁻¹ = 0 := by
  have hPSD : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  have hnotunit : ¬IsUnit (G * Gᵀ) := fun hunit => hnot ((hPSD.posDef_iff_isUnit).2 hunit)
  have hnotdet : ¬IsUnit (G * Gᵀ).det := fun hdet =>
    hnotunit ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
  exact Matrix.nonsing_inv_apply_not_isUnit _ hnotdet

omit [DecidableEq κ] in
/-- The unshifted inverse-power minimum is zero outside the positive
definite Gram domain, using the total inverse convention. Source: singular
Gram inverse; atlas `wishart-lambda-min-tail` (cutoff helper).-/
theorem inversePowerSoftMin_gram_eq_zero_of_not_posDef (n : ℕ) (hn : 0 < n)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᵀ).PosDef) :
    inversePowerSoftMin n (G * Gᵀ) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inversePowerSoftMin, inv_gram_eq_zero_of_not_posDef G hnot,
    zero_pow hn.ne', Matrix.trace_zero, Real.zero_rpow (neg_ne_zero.mpr (inv_ne_zero hn0))]

omit [DecidableEq κ] in
/-- The unshifted Gram gradient is zero outside the positive definite
Gram domain. Source: the total singular inverse convention; atlas
`wishart-lambda-min-tail` (cutoff helper).-/
theorem gramSoftMinGradient_unshifted_eq_zero_of_not_posDef (n : ℕ)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᵀ).PosDef) : gramSoftMinGradient n 0 G = 0 := by
  rw [gramSoftMinGradient, regularizedGram_zero, inversePowerSoftMinWeight,
    inv_gram_eq_zero_of_not_posDef G hnot, zero_pow (Nat.succ_ne_zero n),
    smul_zero, Matrix.zero_mul, smul_zero]

/-- The unshifted first Gram chain coefficient equals the corresponding
gradient entry along every coordinate line, including singular points.
Source: trace pairing and Gram positivity; atlas `wishart-lambda-min-tail` (helper).-/
theorem inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient (n : ℕ)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = gramSoftMinGradient n 0 (G + t • E) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ) =
      E * (G + t • E)ᵀ + (G + t • E) * Eᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hPSD : (regularizedGram 0 (G + t • E)).PosSemidef := by
    rw [regularizedGram_zero]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (G + t • E)
  have hP : (inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n hPSD).isHermitian).eq
  change inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = _
  rw [hD, inversePowerSoftMinFirst_eq_trace_weight_mul, trace_mul_gram_direction _ hP]
  rfl

omit [DecidableEq κ] in
/-- The total unshifted inverse-power minimum is nonnegative everywhere.
Source: Gram inverse positivity; atlas `wishart-lambda-min-tail` (helper).-/
theorem inversePowerSoftMin_gram_nonneg (n : ℕ) (G : Matrix ι κ ℝ) :
    0 ≤ inversePowerSoftMin n (G * Gᵀ) := by
  have hPSD : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  exact Real.rpow_nonneg (hPSD.inv.pow n).trace_nonneg _

end NLAlib
