module
public import Tengoku.Causalean.Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Recovery

/-!
# Quantitative local inverse for symmetric tensor pencils

This module assembles contraction, lifted conditioning, pencil perturbation, spectral-projector
matching, trace-coordinate recovery, and normalization into a permutation-aligned local inverse
for finite symmetric rank-one tensor decompositions.
-/

@[expose] public section

namespace Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil

open scoped Matrix.Norms.L2Operator

/-- The contracted denominator singular-value margin assembled from coefficient, probe, and
lifted-factor margins. With [its explicit inputs](hyp:q,sigma,kappa), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def contractedMargin (q : ℕ) (sigma kappa : ℝ) : ℝ :=
  kappa * sigma ^ (q + 2)

/-- The condition-number envelope for a lifted matrix with `n` unit columns and least singular
value at least `sigma`, namely the square root of `n` divided by `sigma`. The formula is unguarded:
it is a condition-number envelope only for positive `sigma`, and a zero margin gives zero by the
division-by-zero convention. With [its explicit inputs](hyp:n,sigma), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def liftedConditionEnvelope (n : ℕ) (sigma : ℝ) : ℝ :=
  Real.sqrt n / sigma

/-- The admissible tensor perturbation radius for the quantitative tensor-pencil inverse. The
formula is unguarded: it is an admissible radius only in the positive-margin regime assumed by the
inverse theorem, and degenerate margins give zero by the division-by-zero convention. With [its explicit inputs](hyp:n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def localInverseRadius (n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  let eta := contractedMargin q sigma kappa
  let chi := liftedConditionEnvelope n sigma
  let h := pencilPerturbationConstant n eta Lambda
  min (eta / 2) (sigma / (6 * chi * h))

/-- The coordinatewise trace-recovery Lipschitz factor for the quantitative tensor-pencil inverse. The
formula is unguarded: it is a valid Lipschitz factor only in the positive-margin regime assumed by the
recovery theorems, and degenerate margins give zero by the division-by-zero convention. With [its explicit inputs](hyp:n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def traceRecoveryConstant (n q : ℕ)
    (sigma kappa Lambda : ℝ) : ℝ :=
  let eta := contractedMargin q sigma kappa
  let chi := liftedConditionEnvelope n sigma
  let h := pencilPerturbationConstant n eta Lambda
  n * h * (2 * chi + 6 * n * Lambda * chi ^ 2 / (eta * sigma))

/-- The final factor-matrix Frobenius Lipschitz factor for the quantitative tensor-pencil
inverse. It is a fixed multiple of the trace-recovery factor and inherits its unguarded conventions:
it is a valid Lipschitz factor only in the positive-margin regime of the recovery theorems. With
[its explicit inputs](hyp:p,n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def factorRecoveryConstant (p n q : ℕ)
    (sigma kappa Lambda : ℝ) : ℝ :=
  2 * Real.sqrt (n * p) * traceRecoveryConstant n q sigma kappa Lambda

/-- For positive dimensions and admissible positive margins, the contracted margin, lifted
condition envelope, pencil constant, local radius, trace constant, and factor constant are all
strictly positive. Under [the listed assumptions](hyp:hp,hn,hq,hsigma,hkappa,hkappaLambda), [the stated conclusion follows](goal). -/
-- Proof route: unfold the six constants in dependency order.  `Real.sqrt_pos.2` handles the
-- two dimension square roots; `pow_pos`, division positivity, and `min_pos` handle the remaining
-- arithmetic.  Derive `0 < Lambda` from `hkappa` and `hkappaLambda` before proving positivity of
-- `pencilPerturbationConstant`.
theorem localInverse_constants_pos {p n q : ℕ}
    (hp : 0 < p) (hn : 0 < n) (hq : 0 < q)
    {sigma kappa Lambda : ℝ} (hsigma : 0 < sigma)
    (hkappa : 0 < kappa) (hkappaLambda : kappa ≤ Lambda) :
    0 < contractedMargin q sigma kappa ∧
    0 < liftedConditionEnvelope n sigma ∧
    0 < pencilPerturbationConstant n (contractedMargin q sigma kappa) Lambda ∧
    0 < localInverseRadius n q sigma kappa Lambda ∧
    0 < traceRecoveryConstant n q sigma kappa Lambda ∧
    0 < factorRecoveryConstant p n q sigma kappa Lambda := by
  have hLambda : 0 < Lambda := lt_of_lt_of_le hkappa hkappaLambda
  have heta : 0 < contractedMargin q sigma kappa := by
    unfold contractedMargin
    exact mul_pos hkappa (pow_pos hsigma _)
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hchi : 0 < liftedConditionEnvelope n sigma := by
    unfold liftedConditionEnvelope
    exact div_pos hsqrtn hsigma
  have hh : 0 < pencilPerturbationConstant n
      (contractedMargin q sigma kappa) Lambda := by
    unfold pencilPerturbationConstant
    positivity
  have hradius : 0 < localInverseRadius n q sigma kappa Lambda := by
    unfold localInverseRadius
    exact lt_min (div_pos heta (by norm_num))
      (div_pos hsigma (mul_pos (mul_pos (by norm_num) hchi) hh))
  have htrace : 0 < traceRecoveryConstant n q sigma kappa Lambda := by
    unfold traceRecoveryConstant
    positivity
  have hfactor : 0 < factorRecoveryConstant p n q sigma kappa Lambda := by
    unfold factorRecoveryConstant
    have hsqrtnp : 0 < Real.sqrt (n * p) :=
      Real.sqrt_pos.2 (mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 hp))
    positivity
  exact ⟨heta, hchi, hh, hradius, htrace, hfactor⟩

end Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil
