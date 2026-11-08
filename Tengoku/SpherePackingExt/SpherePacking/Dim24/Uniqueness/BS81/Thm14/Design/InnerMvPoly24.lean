module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inner-product monomials as homogeneous polynomials

We encode `x ↦ ⟪u,x⟫` as a degree-1 multivariate polynomial, and hence encode products of powers
`(⟪u,x⟫)^i * (⟪v,x⟫)^j` as homogeneous polynomials of degree `i+j`.

This is shared by:
- the derivation of BS81 equation (11) from moment identities, and
- the "44 common neighbors" computation (BS81 Lemma 18(ii)).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The `MvPolynomial` representing the linear form `x ↦ ⟪u,x⟫` on `ℝ²⁴`.-/
@[expose] public def innerMvPoly24 (u : ℝ²⁴) : MvPolynomial (Fin 24) ℝ :=
  (Finset.univ : Finset (Fin 24)).sum fun i => MvPolynomial.C (u i) * MvPolynomial.X i

/-- Evaluating `innerMvPoly24 u` at `x` gives the inner product `⟪u,x⟫`.-/
public lemma mvPolyEval24_innerMvPoly24 (u x : ℝ²⁴) :
    mvPolyEval24 (innerMvPoly24 u) x = (⟪u, x⟫ : ℝ) := by
  simp [mvPolyEval24, innerMvPoly24, PiLp.inner_apply, mul_comm]

attribute [grind =] mvPolyEval24_innerMvPoly24

/-- Evaluating `(innerMvPoly24 u)^m` at `x` gives `(⟪u,x⟫)^m`.-/
public lemma mvPolyEval24_innerMvPoly24_pow (u x : ℝ²⁴) (m : ℕ) :
    mvPolyEval24 ((innerMvPoly24 u) ^ m) x = (⟪u, x⟫ : ℝ) ^ m := by
  have h :
      (MvPolynomial.eval x.ofLp) (innerMvPoly24 u) = (⟪u, x⟫ : ℝ) := by
    simpa [mvPolyEval24] using (mvPolyEval24_innerMvPoly24 (u := u) (x := x))
  simp [mvPolyEval24, h]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
