module
public import Tengoku.Seed.RingTheory.Jacobson.Ring
public import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Stafford38.Geometry.ClosedPointOnDivisor

/-- Every principal open meeting a prime closed set in a Jacobson spectrum
contains a closed point of the ambient spectrum.
@isnad1 id=ex.2h3v.s7.06edb011762b from=translated src=- shape=2161f971 vocab=da861d8c
-/
theorem exists_maximal_over_prime_avoiding
    {R : Type*} [CommRing R] [IsJacobsonRing R]
    (p : Ideal R) (hp : p.IsPrime) (f : R) (hf : f ∉ p) :
    ∃ M : Ideal R, M.IsMaximal ∧ p ≤ M ∧ f ∉ M := by
  classical
  have hJ : p.jacobson = p := IsJacobsonRing.out inferInstance hp.isRadical
  by_contra h
  apply hf
  rw [← hJ, Ideal.jacobson, Ideal.mem_sInf]
  intro M hM
  by_contra hnot
  exact h ⟨M, hM.2, hM.1, hnot⟩

/-- The residue field at a closed point of a finite-type algebra over an
algebraically closed field is the ground field as an algebra.
@isnad1 id=nonempty.0h3v.s6.2d8e291a2a4e from=translated src=- shape=05a4c2a0 vocab=6a0c6a08
-/
theorem quotient_algEquiv_ground_of_maximal
    {k R : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (M : Ideal R) [M.IsMaximal] :
    Nonempty ((R ⧸ M) ≃ₐ[k] k) := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  letI : Module.Finite k (R ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ M)
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ M))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

/-- A dense principal open on a prime closed subset of a finite-type affine model
contains a ground-field closed point. The smoothness and parameter conditions
must still be proved to hold on the chosen open.
@isnad1 id=ex.2h4v.s8.9607888403f2 from=translated src=- shape=d1a04118 vocab=80b62fb7
-/
theorem exists_ground_closed_point_over_prime_avoiding
    {k R : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (p : Ideal R) (hp : p.IsPrime) (f : R) (hf : f ∉ p) :
    ∃ (M : Ideal R) (hM : M.IsMaximal), p ≤ M ∧ f ∉ M ∧
      (letI : M.IsMaximal := hM; Nonempty ((R ⧸ M) ≃ₐ[k] k)) := by
  letI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k) (B := R)
  obtain ⟨M, hM, hpM, hfM⟩ := exists_maximal_over_prime_avoiding p hp f hf
  letI : M.IsMaximal := hM
  exact ⟨M, hM, hpM, hfM, quotient_algEquiv_ground_of_maximal M⟩

end Stafford38.Geometry.ClosedPointOnDivisor
