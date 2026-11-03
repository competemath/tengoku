import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowFrameReduction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowFrameDeterminants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponents.determinant_ratios` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponents.goodSolution_of_components` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponents.eq_of_components_of_trace_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowComponents.three_componentSolutions_pairwise_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# At most two solutions of the normalized matrix-component system

Fix three invertible matrices `a0,a1,a2`.  A candidate `X` specifies the
normalized second components `a0`, `X*a0`, and `-(1+X)*a0`.  Their determinant
and inverse-adjugate sum equations imply the right quadratic and all shared
endpoint identities used by the trace reconstruction theorem.

These are ordinary matrix equations.  No Albert model, lawful-frame predicate,
ledger identification, normalization coverage or automorphism classification
is asserted here.  In particular, the reconstruction open is explicit.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowComponents

open FourRowFrameReduction
open FourRowUniqueness (GoodSolution reconstructionDenominator
  eq_of_goodSolution_of_trace_eq three_goodSolutions_pairwise_eq)

variable {K : Type*} [Field K]

/-- Parameters determined by the three fixed first components.-/
def componentU (a0 a1 a2 : Mat3 K) : Mat3 K :=
  frameU a0.adjugate a1.adjugate a2.adjugate

def componentV (a0 a1 : Mat3 K) : Mat3 K :=
  frameV a0.adjugate a1.adjugate

/-- Raw normalized matrix-component constraints, without a quadratic premise.-/
structure ComponentSolution (a0 a1 a2 X : Mat3 K) : Prop where
  det_b1 : (X * a0).det = a1.det
  det_b2 : (-(1 + X) * a0).det = a2.det
  inverse_adjugate_sum :
    cslotSum a0 (X * a0) (-(1 + X) * a0)
      a0.adjugate a1.adjugate a2.adjugate = 0
  denominator_det_ne_zero :
    (reconstructionDenominator (componentU a0 a1 a2) (componentV a0 a1)
      (a1.det / a0.det) (a2.det / a0.det) (Matrix.trace X)).det ≠ 0

/-- Normalization derives both determinant ratios with the dimension-three sign.
@isnad1 id=and.2h5v.s8.d9294ecb7230 from=translated src=- shape=f7dd093c vocab=c453c2ec
-/
theorem determinant_ratios (a0 a1 a2 X : Mat3 K) (ha0 : a0.det ≠ 0)
    (hX : ComponentSolution a0 a1 a2 X) :
    X.det = a1.det / a0.det ∧ (1 + X).det = -(a2.det / a0.det) := by
  constructor
  · apply (eq_div_iff ha0).2
    simpa only [Matrix.det_mul] using hX.det_b1
  · have hn : -(1 + X).det = a2.det / a0.det := by
      apply (eq_div_iff ha0).2
      have hb := hX.det_b2
      rw [Matrix.det_mul, Matrix.det_neg] at hb
      norm_num at hb
      simpa only [neg_mul] using hb
    exact neg_eq_iff_eq_neg.mp hn

/-- The component equations supply every `GoodSolution` requirement.
@isnad1 id=goodsolu.4h5v.s8.2c95ed6ec69b from=translated src=- shape=9f60ecfa vocab=7723f91c
-/
theorem goodSolution_of_components
    (a0 a1 a2 X : Mat3 K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    (hX : ComponentSolution a0 a1 a2 X) :
    GoodSolution (componentU a0 a1 a2) (componentV a0 a1)
      (a1.det / a0.det) (a2.det / a0.det) X := by
  obtain ⟨hdetX, hdetOne⟩ := determinant_ratios a0 a1 a2 X ha0 hX
  have hnX : X.det ≠ 0 := by rw [hdetX]; exact div_ne_zero ha1 ha0
  have hnOne : (1 + X).det ≠ 0 := by
    rw [hdetOne]; exact neg_ne_zero.mpr (div_ne_zero ha2 ha0)
  have hnA0 : a0.adjugate.det ≠ 0 := by
    have h : a0.adjugate.det = a0.det ^ 2 := by simpa using Matrix.det_adjugate a0
    rw [h]
    exact pow_ne_zero 2 ha0
  refine ⟨?_, hdetX, hdetOne, hX.denominator_det_ne_zero⟩
  exact right_quadratic_of_normalized_cslots
    a0 a0 (X * a0) (-(1 + X) * a0) X a0.adjugate a1.adjugate a2.adjugate
    rfl rfl rfl ha0 (by rw [hX.det_b1]; exact ha1)
    (by rw [hX.det_b2]; exact ha2) hnX hnOne hnA0 hX.inverse_adjugate_sum

/-- The recovered trace determines a normalized component solution uniquely.-/
theorem eq_of_components_of_trace_eq
    (a0 a1 a2 : Mat3 K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    {X Y : Mat3 K} (hX : ComponentSolution a0 a1 a2 X)
    (hY : ComponentSolution a0 a1 a2 Y)
    (ht : Matrix.trace X = Matrix.trace Y) : X = Y := by
  exact eq_of_goodSolution_of_trace_eq _ _ _ _
    (goodSolution_of_components a0 a1 a2 X ha0 ha1 ha2 hX)
    (goodSolution_of_components a0 a1 a2 Y ha0 ha1 ha2 hY) ht

/-- Any three normalized component solutions on this open contain an equal pair.
The quadratic and shared determinant constraints are derived inside the proof.
@isnad1 id=or.6h7v.s7.3eaa7003ce7d from=translated src=- shape=76210b0a vocab=a6208ed4
-/
theorem three_componentSolutions_pairwise_eq
    (a0 a1 a2 : Mat3 K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    (X Y Z : Mat3 K)
    (hX : ComponentSolution a0 a1 a2 X)
    (hY : ComponentSolution a0 a1 a2 Y)
    (hZ : ComponentSolution a0 a1 a2 Z) :
    X = Y ∨ X = Z ∨ Y = Z := by
  have hparams := FourRowFrameDeterminants.adjugate_normalized_endpoint_determinants
    a0 a1 a2 ha0
  exact three_goodSolutions_pairwise_eq
    (componentU a0 a1 a2) (componentV a0 a1) (a1.det / a0.det) (a2.det / a0.det)
    (div_ne_zero ha1 ha0) (div_ne_zero ha2 ha0) hparams.1 hparams.2 X Y Z
    (goodSolution_of_components a0 a1 a2 X ha0 ha1 ha2 hX)
    (goodSolution_of_components a0 a1 a2 Y ha0 ha1 ha2 hY)
    (goodSolution_of_components a0 a1 a2 Z ha0 ha1 ha2 hZ)

end AlbertLean.Generic.FourRowComponents
