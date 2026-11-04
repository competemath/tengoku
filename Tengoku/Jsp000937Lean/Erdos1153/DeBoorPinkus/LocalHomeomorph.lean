import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Jacobian
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Statement
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.GlobalHomeomorph
import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Tengoku.Seed.Topology.OpenPartialHomeomorph.Constructions
import Tengoku.Seed.Topology.IsLocalHomeomorph
import Tengoku.Seed.LinearAlgebra.Determinant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local homeomorphism of consecutive gap-height differences

This file passes from the checked coordinate derivative of each individual
gap height to the source map

`Γ_i = h_{i+1} - h_i`.

Continuity is unconditional.  The sole algebraic input to the inverse
function theorem is isolated as nonvanishing of the determinant of the
explicit consecutive-row-difference matrix.  No inhabitant of that
proposition is asserted here; it is the output expected from the coherent
maximal-minor sign argument.
-/

namespace Erdos1153.DeBoorPinkus

open Filter Function Topology

noncomputable section

/-! ## The explicit Jacobian model -/

/-- Consecutive row differences of the checked gap-height Jacobian.-/
def gapDifferenceJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => gapHeightJacobianModel nodes i.succ j -
    gapHeightJacobianModel nodes i.castSucc j

/-- The exact algebraic residue of the local-homeomorphism argument.
It is deliberately a proposition, not an assumed theorem.-/
def GapDifferenceJacobianDeterminantCondition (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : EndpointArray d A B,
    Matrix.det (gapDifferenceJacobianModel nodes) ≠ 0

/-! ## `C¹` regularity of the local critical-value extension -/

private lemma contDiffAt_finset_sum_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

private lemma contDiffAt_finset_prod_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (1 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

/-- The rational coordinate gap-value map is `C¹` at every simplex point
and every evaluation point.
@isnad1 id=contdiff.1h6v.s7.dd3e9a22b09d from=translated src=- shape=bc42a987 vocab=6f5c9e43
-/
lemma contDiffAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    ContDiffAt ℝ 1 (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul (by
    simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
    let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
      fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
    have hfac : ∀ i ∈ Finset.univ.erase k,
        ContDiffAt ℝ 1 (fac i) (u.1, x) := by
      intro i hi
      exact contDiffAt_coordinateLagrangeFactorValue hAB u
        (Finset.mem_erase.mp hi).1.symm x 1
    exact contDiffAt_finset_prod_scalar 1 (Finset.univ.erase k) fac
      (u.1, x) hfac)

/-! ## Continuity of genuine gap heights -/

/-! ## The ambient derivative of consecutive differences -/

/-- Its checked differential, formed before choosing any matrix
coordinates.-/
def gapDifferenceDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ) -
      (concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

/-! ## Restriction to the open simplex and inverse function theorem -/

/-- The genuine source map in the open-simplex chart.-/
def coordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => gapDifference (endpointArrayOfInterior hAB v)

/-! ## Endpoint arrays, including dimension zero -/

/-- In dimension zero the displayed determinant condition holds
automatically: both matrix index types are empty.
@isnad1 id=gapdiffe.0h2v.s3.0725c88cfa9b from=translated src=- shape=e7e63813 vocab=a7b22350
-/
theorem gapDifferenceJacobianDeterminantCondition_zero (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition 0 A B := by
  intro nodes
  simp

end

end Erdos1153.DeBoorPinkus
