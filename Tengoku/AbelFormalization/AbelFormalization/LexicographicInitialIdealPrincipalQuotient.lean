import Tengoku.AbelFormalization.AbelFormalization.LexicographicInitialIdealLocalization
import Tengoku.Seed.Algebra.MvPolynomial.CommRing
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.MvPolynomial.Localization
import Tengoku.Seed.RingTheory.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Lexicographic initial ideals and saturated principal quotients

For an arbitrary coefficient map, mapping an initial ideal into the initial
ideal of the image is formal.  The reverse inclusion can fail because lower
weight components of a lift may be killed by the coefficient map.

This file gives the exact condition that repairs the reverse inclusion.  Let
`N ≤ K`, assume that `K` is homogeneous for the lexicographic weight, and
assume

`K ∩ ker (MvPolynomial.map f) ≤ N`.

Then every killed lower component of a lift belongs to `N` and can be
subtracted.  This is the unbounded polynomial version of the finite-product
prefix-subtraction argument.

For the quotient `B → B/(b)`, the kernel condition follows from the
sandwich `C(b)K ≤ N ≤ K` when `K` is saturated by `C(b)`.
-/

noncomputable section

namespace AbelFormalization

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section LowerComponents

variable {R ι : Type*} [CommRing R] {h : ℕ}

/-- Every component strictly below the actual lexicographic minimum is
zero.
@isnad1 id=eq.1h6v.s8.4fe8b81bd937 from=translated src=- shape=6a3c4277 vocab=9e325ee0
-/
theorem weightedHomogeneousComponent_eq_zero_of_lt_lexicographicMinimum
    (weight : ι → Fin h → ℤ) (p : MvPolynomial ι R)
    {degree : Lex (Fin h → ℤ)}
    (hdegree : degree < lexicographicMinimumWeight weight p) :
    MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (weight i)) degree p = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · by_contra hcoeff
    have hle := lexicographicMinimumWeight_le weight p
      (MvPolynomial.mem_support_iff.mpr hcoeff)
    rw [hd] at hle
    exact (not_le_of_gt hdegree) hle
  · rfl

end LowerComponents

section SurjectiveBaseChange

variable {R S ι : Type*} [CommRing R] [CommRing S] {h : ℕ}

end SurjectiveBaseChange

section PrincipalKernel

variable {R S ι : Type*} [CommRing R] [CommRing S] {h : ℕ}

/-- A contraction along a map which sends `c` to a unit is saturated by
`c`.
@isnad1 id=mem.2h6v.s8.a647d43ce101 from=translated src=- shape=f4b41739 vocab=c3f7375d
-/
theorem ideal_comap_saturatedBy_of_isUnit_map
    (psi : R →+* S) (L : Ideal S) (c : R)
    (hc : IsUnit (psi c)) {x : R}
    (hx : c * x ∈ L.comap psi) : x ∈ L.comap psi := by
  change psi x ∈ L
  change psi (c * x) ∈ L at hx
  rw [map_mul] at hx
  exact (Ideal.unit_mul_mem_iff_mem L hc).mp hx

/-- A polynomial ideal contracted from a coefficient localization is
saturated by every constant whose coefficient lies in the localization
submonoid.
@isnad1 id=mem.1h6v.s10.e0c709419bf3 from=translated src=- shape=a9117893 vocab=a5c2fdfe
-/
theorem mvPolynomial_localization_comap_saturatedBy_C
    {A : Type*} [CommRing A] (T : Submonoid A)
    (L : Ideal (MvPolynomial ι (Localization T))) (b : T)
    {p : MvPolynomial ι A}
    (hp : MvPolynomial.C (b : A) * p ∈
      L.comap (MvPolynomial.map (algebraMap A (Localization T)))) :
    p ∈ L.comap
      (MvPolynomial.map (algebraMap A (Localization T))) := by
  apply ideal_comap_saturatedBy_of_isUnit_map
    (MvPolynomial.map (algebraMap A (Localization T))) L
      (MvPolynomial.C (b : A))
  · have hb : IsUnit (algebraMap A (Localization T) (b : A)) :=
      IsLocalization.map_units (Localization T) b
    simpa only [MvPolynomial.map_C] using
      hb.map (MvPolynomial.C : Localization T →+*
        MvPolynomial ι (Localization T))
  · exact hp

/-- A principal coefficient kernel remains principal after applying the
multivariate-polynomial functor.
@isnad1 id=eq.1h5v.s8.9956454a2994 from=translated src=- shape=0bdce3a6 vocab=776a6d4a
-/
theorem ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
    (f : R →+* S) (b : R)
    (hfker : RingHom.ker f = Ideal.span {b}) :
    RingHom.ker (MvPolynomial.map (σ := ι) f) =
      Ideal.span {MvPolynomial.C b} := by
  rw [MvPolynomial.ker_map, hfker, Ideal.map_span,
    Set.image_singleton]

/-- Saturation identifies the part of the polynomial-map kernel lying in
`K` with the ideal product `C(b)K`.
@isnad1 id=eq.2h6v.s10.cfe0f6afb162 from=translated src=- shape=eafd56e8 vocab=19e809a7
-/
theorem inf_ker_mvPolynomial_map_eq_principal_mul_of_saturated
    (f : R →+* S) (b : R)
    (hfker : RingHom.ker f = Ideal.span {b})
    (K : Ideal (MvPolynomial ι R))
    (hKsat : ∀ p : MvPolynomial ι R,
      MvPolynomial.C b * p ∈ K → p ∈ K) :
    K ⊓ RingHom.ker (MvPolynomial.map f) =
      Ideal.span {MvPolynomial.C b} * K := by
  apply le_antisymm
  · intro p hp
    have hpCb : p ∈ Ideal.span {MvPolynomial.C b} := by
      rw [← ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
        (ι := ι) f b hfker]
      exact hp.2
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hpCb
    have hCbq : MvPolynomial.C b * q = p := by
      simpa only [mul_comm] using hq
    have hqK : q ∈ K := by
      apply hKsat q
      rw [hCbq]
      exact hp.1
    exact (Ideal.mem_span_singleton_mul).mpr ⟨q, hqK, hCbq⟩
  · intro p hp
    obtain ⟨q, hqK, hCbq⟩ :=
      (Ideal.mem_span_singleton_mul).mp hp
    constructor
    · rw [← hCbq]
      exact K.mul_mem_left (MvPolynomial.C b) hqK
    · rw [ker_mvPolynomial_map_eq_span_C_of_ker_eq_span
        (ι := ι) f b hfker]
      exact Ideal.mem_span_singleton'.mpr
        ⟨q, by simpa only [mul_comm] using hCbq⟩

end PrincipalKernel

end AbelFormalization
