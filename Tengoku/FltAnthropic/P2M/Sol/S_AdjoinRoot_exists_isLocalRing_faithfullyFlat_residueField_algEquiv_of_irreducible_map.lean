import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map

set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace P2mAdjoinRootLocalStep

variable {R : Type u} [CommRing R] [IsLocalRing R] (f : R[X])

noncomputable abbrev J : Ideal (AdjoinRoot f) := (maximalIdeal R).map (AdjoinRoot.of f)

omit [IsLocalRing R] in
/--
@isnad1 id=eq.0h2v.s6.39468a5a7ad6 from=translated src=- shape=89c12dd8 vocab=5dc9aad7
-/
theorem algebraMap_eq_of : algebraMap R (AdjoinRoot f) = AdjoinRoot.of f := rfl

/--
@isnad1 id=isfield.0h2v.s7.050ecfea81dc from=translated src=- shape=8ba74849 vocab=8e5d1a27
-/
theorem isField_quotient_J [Fact (Irreducible (f.map (residue R)))] : IsField (AdjoinRoot f ⧸ J f) := by
  have hK : IsField ((R ⧸ maximalIdeal R)[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (maximalIdeal R))}) :=
    Field.toIsField (AdjoinRoot (f.map (residue R)))
  exact MulEquiv.isField hK (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv

/--
@isnad1 id=ismaxima.0h2v.s7.9e1fd9ddbc6b from=translated src=- shape=3bb4626a vocab=30f4bf9e
-/
theorem isMaximal_J [Fact (Irreducible (f.map (residue R)))] : (J f).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_quotient_J f)

variable {f}

theorem eq_J_of_isMaximal (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    (N : Ideal (AdjoinRoot f)) (hN : N.IsMaximal) : N = J f := by
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R (AdjoinRoot f)
  have hcomap : (N.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
  have hcomap' : N.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomap
  have hle : J f ≤ N := by
    rw [J, ← algebraMap_eq_of, Ideal.map_le_iff_le_comap, hcomap']
  exact ((isMaximal_J f).eq_of_le hN.ne_top hle).symm

/--
@isnad1 id=islocalr.1h2v.s7.32faa22d6bb7 from=translated src=- shape=b991efc4 vocab=70bbddd0
-/
theorem isLocalRing (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] : IsLocalRing (AdjoinRoot f) :=
  IsLocalRing.of_unique_max_ideal ⟨J f, isMaximal_J f, fun N hN => eq_J_of_isMaximal hfm N hN⟩

/--
@isnad1 id=eq.1h2v.s7.edafac1dc68a from=translated src=- shape=096ba935 vocab=312caf74
-/
theorem maximalIdeal_eq (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    @maximalIdeal (AdjoinRoot f) _ (isLocalRing hfm) = J f :=
  letI := isLocalRing hfm
  eq_J_of_isMaximal hfm _ (IsLocalRing.maximalIdeal.isMaximal _)

/--
@isnad1 id=islocalh.1h2v.s8.c1c3b90eb38d from=translated src=- shape=eb815e11 vocab=1d650e27
-/
theorem isLocalHom (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    IsLocalHom (algebraMap R (AdjoinRoot f)) := by
  letI := isLocalRing hfm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
  have hJmem : algebraMap R (AdjoinRoot f) a ∈ maximalIdeal (AdjoinRoot f) := by
    rw [maximalIdeal_eq hfm]
    exact Ideal.mem_map_of_mem _ hmem
  exact (IsLocalRing.mem_maximalIdeal _).1 hJmem ha

/--
@isnad1 id=nonempty.1h2v.s9.8cc41aaa1cbf from=translated src=- shape=3e603501 vocab=7ccc34e5
-/
theorem nonempty_residueField_algEquiv (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    letI := isLocalRing hfm
    letI := isLocalHom hfm
    Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  letI := isLocalRing hfm
  letI := isLocalHom hfm

  let e₁ : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot f ⧸ J f :=
    Ideal.quotientEquivAlgOfEq R (maximalIdeal_eq hfm)
  let e₂ : (AdjoinRoot f ⧸ J f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) :=
    AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)
  let e : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) := e₁.trans e₂

  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun c => ?_⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  have h1 : algebraMap (ResidueField R) (ResidueField (AdjoinRoot f)) (residue R r) =
      algebraMap R (ResidueField (AdjoinRoot f)) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have h2 : algebraMap (ResidueField R) (AdjoinRoot (f.map (residue R))) (residue R r) =
      algebraMap R (AdjoinRoot (f.map (residue R))) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h1, h2]
  exact e.commutes r

end P2mAdjoinRootLocalStep

open P2mAdjoinRootLocalStep in

/--
@isnad1 id=ex.1h2v.s10.5c95491867cc from=translated src=- shape=4b9e66e7 vocab=a527b13a
-/
theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  letI hloc := isLocalRing hfm
  letI hlh := isLocalHom hfm
  haveI : Module.Free R (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  refine ⟨hloc, hlh, inferInstance, inferInstance, Module.FaithfullyFlat.of_flat_of_isLocalHom, ?_,
    nonempty_residueField_algEquiv hfm⟩
  rw [algebraMap_eq_of]
  exact (maximalIdeal_eq hfm).symm
