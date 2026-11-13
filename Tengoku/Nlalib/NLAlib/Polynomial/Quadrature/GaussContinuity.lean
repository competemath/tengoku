import Tengoku.Nlalib.NLAlib.Polynomial.Quadrature.MomentGauss
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.JacobiContinuity
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Calculus.LagrangeContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuity of Gauss nodes and cardinal weights

Smooth monomial moments give continuous actual nodes and weights at a positive
finite Hankel system. Node differences are nonzero at the limit; early singular
systems need no special conventions beyond the total definitions.
Source: Gautschi (2004), §2.1; AQ22–AQ23 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : E → (ℝ[X] →ₗ[ℝ] ℝ)} {x : E} {n : ℕ}

/-- The actual cardinal weight is continuous in the moments whenever the
limiting finite moment system is nonsingular with positive included norms.
Source: AQ23, equivalently the cardinal form of the Vandermonde solve.
atlas: recurrence-coefficient-continuity (partial)
@isnad1 id=continuo.3h5v.s8.e81b77fe6652 from=translated src=- shape=2cd74829 vocab=b26526c4
-/
theorem continuousAt_momentGaussWeights
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : ∀ k ≤ n, hankelMomentDet (L x) k ≠ 0)
    (hh : ∀ k < n, 0 < orthogonalPolynomialNorm (L x) k) (i : Fin n) :
    ContinuousAt (fun y => momentGaussWeights (L y) n i) x := by
  unfold momentGaussWeights
  apply continuousAt_functional_polynomial_of_degree_lt (d := n)
  · intro y
    apply (Lagrange.degree_basis_le_of_mem _ (mem_univ i)).trans_lt
    simp only [card_univ, Fintype.card_fin]
    exact_mod_cast (show n - 1 < n by have := i.isLt; omega)
  · intro k
    apply Lagrange.continuousAt_coeff_basis
    · exact continuousAt_eigenvalues_orthogonalPolynomialJacobiMatrix hL
        (fun k hk => hn k hk.le) hh
    · exact mem_univ i
    · exact (eigenvalues_orthogonalPolynomialJacobiMatrix_injective (L x) hn hh).injOn
  · exact fun k => (hL k.val).continuousAt

end NLAlib
