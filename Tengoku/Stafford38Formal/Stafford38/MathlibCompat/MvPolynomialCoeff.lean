module
public import Tengoku.Seed.Algebra.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Compatibility spelling for sources using `MvPolynomial.coeff m p`.
The canonical operation is the polynomial's coefficient at `m`. -/
namespace MvPolynomial

/--
@isnad1 id=eq.0h3v.s6.a01f2d65db9b from=translated src=- shape=ef5b60c2 vocab=7608171b
-/
@[simp] theorem coeff_zero_compat {σ : Type*} {R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) : MvPolynomial.coeff m (0 : MvPolynomial σ R) = 0 := by
  simp [MvPolynomial.coeff]

end MvPolynomial
