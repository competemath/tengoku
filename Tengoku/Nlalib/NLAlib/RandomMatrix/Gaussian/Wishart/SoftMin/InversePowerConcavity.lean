import Tengoku.Nlalib.NLAlib.Matrix.Functions.InverseCalculus
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.TraceEigenvalues
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.Seed.Analysis.InnerProductSpace.StarOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted spectral inequalities for inverse trace powers

The Hessian kernel of an inverse trace power dominates its diagonal part.
A weighted Cauchy--Schwarz inequality controls the square of its first
derivative. Together these are the algebraic basis for the concavity of
the resolvent approximation to the smallest eigenvalue.

Source: operator re-derivation of the smallest Wishart eigenvalue bound.
Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic kernel arising as the second derivative of an inverse
trace power. Source: finite noncommutative power rule; atlas
`wishart-lambda-min-tail` (operator calculus helper).
atlas: inverse-power-gram-def-/
def inversePowerHessianKernel (R B : Matrix ι ι ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Matrix.trace (R ^ (n - i + 1) * B * R ^ (i + 1) * B)

/-- Resolvent approximation to the smallest eigenvalue: the negative
`n`th root of the inverse-power trace. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper).
atlas: inverse-power-gram-def-/
def inversePowerSoftMin (n : ℕ) (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹)

/-- First directional derivative of the resolvent approximation. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper).
atlas: inverse-power-gram-def-/
def inversePowerSoftMinFirst (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) * Matrix.trace (A⁻¹ ^ (n + 1) * B)

/-- Positive semidefinite gradient weight for the resolvent approximation.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (operator
calculus helper).
atlas: inverse-power-gram-def-/
def inversePowerSoftMinWeight (n : ℕ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) • A⁻¹ ^ (n + 1)

/-- The first directional derivative is the trace pairing with the
resolvent gradient weight. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper).-/
theorem inversePowerSoftMinFirst_eq_trace_weight_mul (n : ℕ)
    (A B : Matrix ι ι ℝ) :
    inversePowerSoftMinFirst n A B = Matrix.trace (inversePowerSoftMinWeight n A * B) := by
  simp only [inversePowerSoftMinFirst, inversePowerSoftMinWeight, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul]

/-- The resolvent gradient weight is positive semidefinite at a positive
semidefinite matrix. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper).-/
theorem inversePowerSoftMinWeight_posSemidef (n : ℕ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (inversePowerSoftMinWeight n A).PosSemidef := by
  exact (hA.inv.pow (n + 1)).smul (Real.rpow_nonneg
    (hA.inv.pow n).trace_nonneg _)

/-- Second directional derivative of the resolvent approximation. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper).
atlas: inverse-power-gram-def-/
def inversePowerSoftMinSecond (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  ((n : ℝ) + 1) * Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
      Matrix.trace (A⁻¹ ^ (n + 1) * B) ^ 2 -
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) * inversePowerHessianKernel A⁻¹ B n

/-- The resolvent approximation has its explicit first derivative along
any differentiable invertible matrix curve with positive inverse-power trace. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper).-/
theorem hasDerivAt_inversePowerSoftMin_curve (n : ℕ) (hn : 0 < n)
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t))
    (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMin n (A x))
      (inversePowerSoftMinFirst n (A t) A') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹) (Or.inl hT.ne')
  convert! h using 1
  · unfold inversePowerSoftMinFirst
    field_simp

/-- The resolvent approximation has its explicit first derivative along
an affine matrix line. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper).-/
theorem hasDerivAt_inversePowerSoftMin (n : ℕ) (hn : 0 < n)
    (A B : Matrix ι ι ℝ) (t : ℝ) (hunit : IsUnit (A + t • B))
    (hT : 0 < Matrix.trace ((A + t • B)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMin n (A + x • B))
      (inversePowerSoftMinFirst n (A + t • B) B) t := by
  have hline : HasDerivAt (fun x : ℝ => A + x • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add A
  exact hasDerivAt_inversePowerSoftMin_curve n hn hline hunit hT

/-- Along a twice differentiable matrix curve, the derivative of the
resolvent first derivative is its directional Hessian plus the trace
pairing with the second curve derivative. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (operator calculus helper).-/
theorem hasDerivAt_inversePowerSoftMinFirst_curve (n : ℕ) (hn : 0 < n)
    {A D : ℝ → Matrix ι ι ℝ} {D' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (D t) t) (hD : HasDerivAt D D' t)
    (hunit : IsUnit (A t)) (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMinFirst n (A x) (D x))
      (inversePowerSoftMinSecond n (A t) (D t) +
        inversePowerSoftMinFirst n (A t) D') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpower := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹ - 1) (Or.inl hT.ne')
  have hmul := hpower.mul (hasDerivAt_matrix_trace_inv_pow_mul hA hD hunit n)
  convert! hmul using 1
  · unfold inversePowerSoftMinSecond inversePowerSoftMinFirst inversePowerHessianKernel
    have he : -(n : ℝ)⁻¹ - 1 - 1 = -(n : ℝ)⁻¹ - 2 := by ring
    rw [he]
    field_simp
    ring

/-- The derivative of the resolvent approximation's first directional
derivative is its explicit Hessian. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper).-/
theorem hasDerivAt_inversePowerSoftMinFirst (n : ℕ) (hn : 0 < n)
    (A B : Matrix ι ι ℝ) (t : ℝ) (hunit : IsUnit (A + t • B))
    (hT : 0 < Matrix.trace ((A + t • B)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMinFirst n (A + x • B) B)
      (inversePowerSoftMinSecond n (A + t • B) B) t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hline : HasDerivAt (fun x : ℝ => A + x • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add A
  have hpower := (hasDerivAt_matrix_trace_inv_pow hline hunit n).rpow_const
    (p := -(n : ℝ)⁻¹ - 1) (Or.inl hT.ne')
  have hmul := hpower.mul (hasDerivAt_matrix_trace_inv_pow_mul_const A B n t hunit)
  convert! hmul using 1
  · unfold inversePowerSoftMinSecond inversePowerHessianKernel
    have he : -(n : ℝ)⁻¹ - 1 - 1 = -(n : ℝ)⁻¹ - 2 := by ring
    rw [he]
    field_simp
    ring

end NLAlib
