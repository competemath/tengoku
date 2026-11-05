import Tengoku.NsP23.P23.Presentation.PolynomialBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The final finite three-variable polynomial presentation

This file combines the frozen single-tie presentation with the exact border
kernel calculation.  It proves that the direct finite model is the quotient
by the displayed tie polynomial and the lifted exact border.  No minimality
claim for this generating family is made here.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie P23.Artin

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The quotient by the displayed single tie and exact polynomial border
lifts.-/
abbrev FinitePolynomialQuotient (k : Type*) [Field k]
    (S : Finset (Normal a b c)) :=
  HasQuotient.Quotient (ThreePoly k) (finitePresentationIdeal (k := k) S)

/-- The final polynomial quotient is exactly the direct finite monomial
Artin model.-/
noncomputable def finitePolynomialQuotientEquiv
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    FinitePolynomialQuotient k S ≃ₐ[k] MonomialArtin k S :=
  (Ideal.quotientEquivAlgOfEq k
      (polyToDirectAlg_ker (k := k) S hS hdom).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (polyToDirectAlg_surjective (k := k) S))

@[simp]
theorem finitePolynomialQuotientEquiv_mk
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (f : ThreePoly k) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk (finitePresentationIdeal (k := k) S) f) =
      polyToDirectAlg (k := k) S f := by
  rfl

@[simp]
theorem finitePolynomialQuotientEquiv_polyX
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ polyX) =
      truncatedMonomial (k := k) S (Normal.xGenerator : Normal a b c) := by
  simp

@[simp]
theorem finitePolynomialQuotientEquiv_polyY
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ polyY) =
      truncatedMonomial (k := k) S (Normal.yGenerator : Normal a b c) := by
  simp

@[simp]
theorem finitePolynomialQuotientEquiv_polyZ
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ polyZ) =
      truncatedMonomial (k := k) S (Normal.zGenerator : Normal a b c) := by
  simp

@[simp]
theorem finitePolynomialQuotientEquiv_monomial
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (d : Fin 3 →₀ ℕ) (r : k) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ (MvPolynomial.monomial d r)) =
      r • truncatedMonomial (k := k) S (normalizeExponent a b c d) := by
  simp

@[simp]
theorem finitePolynomialQuotientEquiv_polynomialLift_of_mem
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (p : Normal a b c)
    (hp : p ∈ standardFinset S) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ (polynomialLift (k := k) p)) =
      X (k := k) S p hp := by
  simp [polynomialLift, hp]

@[simp]
theorem finitePolynomialQuotientEquiv_polynomialLift_of_border
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (g : Normal a b c)
    (hg : g ∈ borderFinset S) :
    finitePolynomialQuotientEquiv (k := k) S hS hdom
        (Ideal.Quotient.mk _ (polynomialLift (k := k) g)) = 0 := by
  have hgnot : g ∉ standardFinset S := by
    intro hgstd
    exact ((mem_borderFinset_iff hS g).1 hg).1
      ((mem_standardFinset_iff_standardSet S g).1 hgstd)
  simp [polynomialLift, hgnot]

/-- A concrete finite displayed generating family.  Run 15 proves that it
spans the presentation ideal, but deliberately makes no minimality claim.-/
def presentationGeneratorFinset (S : Finset (Normal a b c)) :
    Finset (ThreePoly k) := by
  classical
  exact insert (tiePolynomial (k := k) a b c)
    ((borderFinset S).image (polynomialLift (k := k)))

/-- The concrete finite family spans exactly the final presentation ideal.-/
theorem span_presentationGeneratorFinset (S : Finset (Normal a b c)) :
    Ideal.span (↑(presentationGeneratorFinset (k := k) S) : Set (ThreePoly k)) =
      finitePresentationIdeal (k := k) S := by
  classical
  have himage :
      ↑((borderFinset S).image (polynomialLift (k := k))) =
        polynomialBorderSet (k := k) S := by
    ext f
    simp only [Finset.mem_coe, Finset.mem_image, polynomialBorderSet,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [presentationGeneratorFinset, Finset.coe_insert, Ideal.span_insert]
  rw [himage]
  rfl

/-- Scope-explicit Run 15 package.  It records the canonical polynomial map,
its exact kernel and the induced quotient equivalence; it contains no
minimal-generator assertion.-/
structure DirectModelAsPolynomialQuotient (k : Type*) [Field k]
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) : Prop where
  map_surjective : Function.Surjective (polyToDirectAlg (k := k) S)
  kernel_eq : RingHom.ker (polyToDirectAlg (k := k) S).toRingHom =
    finitePresentationIdeal (k := k) S
  quotient_equiv : Nonempty
    (FinitePolynomialQuotient k S ≃ₐ[k] MonomialArtin k S)
  quotient_equiv_mk : ∀ f : ThreePoly k,
    finitePolynomialQuotientEquiv (k := k) S
        hS hdom
        (Ideal.Quotient.mk (finitePresentationIdeal (k := k) S) f) =
      polyToDirectAlg (k := k) S f

/-- Run 15 summary theorem.  This is a presentation theorem only; it does not
assert minimality or compute the number of minimal kernel generators.-/
theorem directModel_as_polynomialQuotient
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    DirectModelAsPolynomialQuotient k S hS hdom where
  map_surjective := polyToDirectAlg_surjective (k := k) S
  kernel_eq := polyToDirectAlg_ker (k := k) S hS hdom
  quotient_equiv := ⟨finitePolynomialQuotientEquiv (k := k) S hS hdom⟩
  quotient_equiv_mk := finitePolynomialQuotientEquiv_mk (k := k) S hS hdom

end

end P23.Presentation
