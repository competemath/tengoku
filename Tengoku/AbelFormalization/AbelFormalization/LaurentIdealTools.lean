import Tengoku.AbelFormalization.AbelFormalization.IdealHeight
import Tengoku.Seed.Algebra.Polynomial.Laurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Coefficient ideals and full Laurent contractions

A Laurent series here is a finite Laurent polynomial. Coefficient extension
is characterized by membership of every coefficient, and contraction to the
ordinary polynomial subring recovers the coefficient-extended ideal. This
connects the manuscript's literal Laurent deformation to the checked height
invariance under localization and polynomial extension.
-/

noncomputable section

namespace AbelFormalization

open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- Extending a coefficient ideal to Laurent polynomials is exactly requiring
every Laurent coefficient to belong to the original ideal.
@isnad1 id=iff.0h3v.s8.bdfac64b6fa9 from=translated src=- shape=000521e9 vocab=dd0b4916
-/
theorem laurentPolynomial_mem_map_C_iff (I : Ideal R) (f : LaurentPolynomial R) :
    f ∈ I.map LaurentPolynomial.C ↔ ∀ n : ℤ, f.coeff n ∈ I := by
  classical
  let L : LaurentPolynomial R →+* LaurentPolynomial (R ⧸ I) :=
    AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk I)
  have hker : I.map LaurentPolynomial.C ≤ RingHom.ker L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change L (LaurentPolynomial.C a) = 0
    change AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk I)
      (AddMonoidAlgebra.single 0 a) = 0
    rw [AddMonoidAlgebra.mapRingHom_single, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    simp
  constructor
  · intro hf n
    have hzero : L f = 0 := hker hf
    have he := congrArg (fun g : LaurentPolynomial (R ⧸ I) => g.coeff n) hzero
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [L, AddMonoidAlgebra.coeff_mapRingHom,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
  · intro hf
    rw [← AddMonoidAlgebra.sum_coeff_single f]
    change (∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n)) ∈
      I.map LaurentPolynomial.C
    apply Ideal.sum_mem
    intro n hn
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact (I.map LaurentPolynomial.C).mul_mem_right _ (Ideal.mem_map_of_mem _ (hf n))

/-- An ordinary polynomial has no negative Laurent coefficient.
@isnad1 id=eq.1h3v.s7.3af35c5d153b from=translated src=- shape=ca82f215 vocab=eabcb8f5
-/
theorem polynomial_toLaurent_coeff_neg (f : R[X]) (n : ℤ) (hn : n < 0) :
    (Polynomial.toLaurent f).coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, rfl⟩
  exact (not_le_of_gt hn) (Int.natCast_nonneg k)

/-- Every Laurent contraction is saturated with respect to the ordinary
polynomial variable.
@isnad1 id=mem.1h3v.s9.99376983a592 from=translated src=- shape=362ae523 vocab=ae04e277
-/
theorem laurentPolynomial_comap_cancel_X (J : Ideal (LaurentPolynomial R))
    (f : R[X]) (hf : Polynomial.X * f ∈ J.comap Polynomial.toLaurent) :
    f ∈ J.comap Polynomial.toLaurent := by
  change Polynomial.toLaurent (Polynomial.X * f) ∈ J at hf
  rw [map_mul, Polynomial.toLaurent_X] at hf
  exact (J.unit_mul_mem_iff_mem (LaurentPolynomial.isUnit_T 1)).mp hf

section Height

variable [IsNoetherianRing R]

/-- The arbitrary-ideal polynomial extension height theorem in the literal
univariate polynomial convention.
@isnad1 id=eq.0h2v.s7.458357ab3972 from=translated src=- shape=6e64bc19 vocab=b62e51e7
-/
theorem polynomialIdeal_height_map_C (I : Ideal R) :
    (I.map Polynomial.C).height = I.height := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  have he : e.toRingEquiv.toRingHom.comp MvPolynomial.C = Polynomial.C := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  calc
    (I.map Polynomial.C).height =
        ((I.map (MvPolynomial.C (σ := Unit))).map e.toRingEquiv.toRingHom).height := by
      rw [Ideal.map_map, he]
    _ = (I.map (MvPolynomial.C (σ := Unit))).height := e.toRingEquiv.height_map _
    _ = I.height := mvPolynomial_height_map_C I

end Height

end AbelFormalization
