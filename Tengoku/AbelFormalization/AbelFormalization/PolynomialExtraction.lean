import Tengoku.AbelFormalization.AbelFormalization.IdealHeight
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Noetherian
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.Algebra.Polynomial.Monic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polynomial extraction at maximum height

Polynomial ideals of maximum height over a finite-dimensional augmented
Noetherian local coefficient ring contain monic scalar polynomials in each
chosen variable. The proof derives maximality and coefficient contraction
from height, then combines the finitely many minimal-prime relations.
-/

noncomputable section

namespace AbelFormalization

open scoped Polynomial

section FieldPolynomial

variable {k : Type*} [Field k] {m : ℕ}

/-- A maximal ideal in a polynomial algebra over a field contains a monic
univariate polynomial in every chosen coordinate.
@isnad1 id=ex.0h4v.s9.ad766d135f38 from=translated src=- shape=fc17629e vocab=b054c386
-/
theorem maximal_mvPolynomial_contains_monic_univariate
    (P : Ideal (MvPolynomial (Fin m) k)) [P.IsMaximal] (i : Fin m) :
    ∃ f : k[X], f.Monic ∧ f.toMvPolynomial i ∈ P := by
  have hint := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing P
  obtain ⟨f, hmonic, hroot⟩ := hint (Ideal.Quotient.mk P (MvPolynomial.X i))
  refine ⟨f, hmonic, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ k P) (Polynomial.aeval (MvPolynomial.X i) f) = 0
  rw [← Polynomial.aeval_algHom_apply]
  exact hroot

end FieldPolynomial

section CoefficientEmbedding

variable (k B : Type*) [Field k] [CommRing B] [Algebra k B] {m : ℕ}

/-- The literal copy of `k[X]` in the selected coordinate of `B[t]`.-/
def scalarUnivariateEmbedding (i : Fin m) : k[X] →+* MvPolynomial (Fin m) B :=
  (MvPolynomial.map (algebraMap k B)).comp
    (Polynomial.toMvPolynomial i).toRingHom

variable {k B}

/--
@isnad1 id=surjecti.0h3v.s6.191f552e5c35 from=translated src=- shape=9c304c75 vocab=8d1871c9
-/
theorem augmentation_surjective (ε : B →ₐ[k] k) : Function.Surjective ε := by
  intro c
  refine ⟨algebraMap k B c, ?_⟩
  simp

/-- Coefficient specialization retracts the embedded scalar polynomial.
@isnad1 id=eq.0h6v.s9.61b9bfe4c39e from=translated src=- shape=165b988d vocab=f8bf5063
-/
theorem map_scalarUnivariateEmbedding (ε : B →ₐ[k] k) (i : Fin m) (f : k[X]) :
    MvPolynomial.map ε.toRingHom (scalarUnivariateEmbedding k B i f) =
      f.toMvPolynomial i := by
  have he : ε.toRingHom.comp (algebraMap k B) = RingHom.id k := by
    apply RingHom.ext
    intro c
    simp
  rw [scalarUnivariateEmbedding, RingHom.comp_apply, MvPolynomial.map_map,
    he, MvPolynomial.map_id]
  rfl

/--
@isnad1 id=injectiv.0h5v.s7.686f8449343c from=translated src=- shape=48fe1486 vocab=ac797004
-/
theorem scalarUnivariateEmbedding_injective (ε : B →ₐ[k] k) (i : Fin m) :
    Function.Injective (scalarUnivariateEmbedding k B i) := by
  intro f g h
  apply Polynomial.toMvPolynomial_injective i
  have he := congrArg (MvPolynomial.map ε.toRingHom) h
  simpa only [map_scalarUnivariateEmbedding] using he

end CoefficientEmbedding

section LocalHeight

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] [IsLocalRing B]

omit [IsNoetherianRing B] in
/-- An actual field augmentation identifies the unique maximal ideal.
@isnad1 id=eq.0h3v.s7.9f47901d2517 from=translated src=- shape=3f70a6c3 vocab=727c8a73
-/
theorem augmentation_ker_eq_maximalIdeal (ε : B →ₐ[k] k) :
    RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal B :=
  IsLocalRing.ker_eq_maximalIdeal ε.toRingHom (augmentation_surjective ε)

end LocalHeight

section FiniteMinimalPrimes

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] {m : ℕ}

/-- Monic coordinate relations in every minimal prime combine into a monic
coordinate relation in the ideal itself. This includes the empty-prime-family
case of the unit ideal.
@isnad1 id=ex.1h5v.s9.f064728a92f8 from=translated src=- shape=03d82370 vocab=015ab48d
-/
theorem mvPolynomial_contains_monic_univariate_of_minimalPrimes
    (I : Ideal (MvPolynomial (Fin m) B)) (i : Fin m)
    (h : ∀ P ∈ I.minimalPrimes,
      ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ P) :
    ∃ f : k[X], f.Monic ∧ scalarUnivariateEmbedding k B i f ∈ I := by
  classical
  let : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) B)).fintype
  choose f hmonic hmem using fun P : I.minimalPrimes => h P.val P.property
  let g : k[X] := ∏ P : I.minimalPrimes, f P
  have hg : g.Monic := Polynomial.monic_prod_of_monic Finset.univ f (fun P _ => hmonic P)
  have hrad : scalarUnivariateEmbedding k B i g ∈ I.radical := by
    rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    dsimp only [g]
    rw [map_prod]
    exact Ideal.prod_mem P (Finset.mem_univ (⟨P, hP⟩ : I.minimalPrimes))
      (hmem ⟨P, hP⟩)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨g ^ n, hg.pow n, ?_⟩
  simpa only [map_pow] using hn

end FiniteMinimalPrimes

section Extraction

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  [IsNoetherianRing B] [IsLocalRing B]

end Extraction

end AbelFormalization
