import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Symplectic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical Poisson calculus

Mixed partials commute; the canonical bracket satisfies Jacobi, and its
Hamiltonian derivations respect the commutator bracket.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace Calculus
noncomputable section

variable {K σ : Type*} [CommRing K] [DecidableEq σ]

/-- Formal mixed partial derivatives commute.
@isnad1 id=eq.0h5v.s10.8e2fa70b520d from=translated src=- shape=55b98e4f vocab=5274be99
-/
theorem pderiv_comm (i j : σ) (f : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  have h : ⁅MvPolynomial.pderiv (R:=K) i, MvPolynomial.pderiv (R:=K) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, hi, hj]
  have hf := congrArg (fun D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) => D f) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using hf

section Field
variable (K : Type*) [Field K]

/-- Hamiltonian vector field as an actual polynomial derivation.-/
def hamiltonian (f : MvPolynomial Var K) :
    Derivation K (MvPolynomial Var K) (MvPolynomial Var K) :=
    (MvPolynomial.pderiv 2 f) • MvPolynomial.pderiv 0 -
    (MvPolynomial.pderiv 0 f) • MvPolynomial.pderiv 2 +
    (MvPolynomial.pderiv 3 f) • MvPolynomial.pderiv 1 -
    (MvPolynomial.pderiv 1 f) • MvPolynomial.pderiv 3

end Field
end
end Calculus
end RankTwoPoisson
