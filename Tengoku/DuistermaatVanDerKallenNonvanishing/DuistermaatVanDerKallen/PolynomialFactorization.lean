import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Targets
import Tengoku.Seed.Algebra.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A coordinatewise minimum exponent gives a monomial times a polynomial,
with the minimum coefficient as the polynomial's nonzero constant coefficient. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Nonnegative polynomial exponents included in the Laurent exponent lattice.-/
def natExponent {d : ℕ} : (Fin d →₀ ℕ) →+ (Fin d → ℤ) where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

/--
@isnad1 id=injectiv.0h1v.s6.ba6e4bb9502e from=translated src=- shape=82ed8014 vocab=4902ebd4
-/
theorem natExponent_injective {d : ℕ} : Function.Injective (natExponent (d := d)) := by
  intro a b h
  ext i
  have hi := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at hi
  exact_mod_cast hi

/-- The canonical inclusion of ordinary polynomials into Laurent polynomials.-/
def polynomialLaurentHom {d : ℕ} : MvPolynomial (Fin d) ℂ →+* MultiLaurent d :=
  AddMonoidAlgebra.mapDomainRingHom ℂ natExponent

/--
@isnad1 id=injectiv.0h1v.s6.0aade24654dd from=translated src=- shape=2ed2924a vocab=62198fd4
-/
theorem polynomialLaurentHom_injective {d : ℕ} :
    Function.Injective (polynomialLaurentHom (d := d)) :=
  AddMonoidAlgebra.mapDomain_injective natExponent_injective

/-- Nonnegative Laurent support is exactly what is needed to come from a polynomial.
@isnad1 id=ex.1h2v.s7.c4664b27c121 from=translated src=- shape=96f86126 vocab=631bcf69
-/
theorem exists_polynomial_of_nonnegative_support {d : ℕ} (f : MultiLaurent d)
    (hf : ∀ a ∈ f.coeff.support, ∀ i, 0 ≤ a i) :
    ∃ u : MvPolynomial (Fin d) ℂ, polynomialLaurentHom u = f := by
  classical
  refine ⟨AddMonoidAlgebra.comapDomain natExponent natExponent_injective f, ?_⟩
  apply AddMonoidAlgebra.mapDomain_comapDomain
  intro a ha
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).toNat), ?_⟩
  ext i
  change ((Finsupp.equivFunOnFinite.symm (fun i => (a i).toNat)) i : ℤ) = a i
  simpa using Int.toNat_of_nonneg (hf a ha i)

end
end DuistermaatVanDerKallen
