import Tengoku.AbelFormalization.AbelFormalization.IdealHeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Height under elimination of the auxiliary polynomial variables

The outer literal polynomial variable represents the inverse-minor symbol.
Contracting it and then a finite tuple of auxiliary variables has exactly
the height cost used by the analytic elimination lemma.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Contraction eliminates the outer inverse symbol and the chosen finite
tuple of auxiliary polynomial symbols, retaining the entire base ring.-/
def polynomialEliminationContraction (a : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R))) : Ideal R :=
  (Q.comap Polynomial.C).comap MvPolynomial.C

omit [IsNoetherianRing R] in
/--
@isnad1 id=iff.0h4v.s9.5d44557c119c from=translated src=- shape=104fde3d vocab=26e8fa0b
-/
@[simp]
theorem polynomialEliminationContraction_mem_iff (a : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R))) (r : R) :
    r ∈ polynomialEliminationContraction a Q ↔
      Polynomial.C (MvPolynomial.C r) ∈ Q := Iff.rfl

end AbelFormalization
