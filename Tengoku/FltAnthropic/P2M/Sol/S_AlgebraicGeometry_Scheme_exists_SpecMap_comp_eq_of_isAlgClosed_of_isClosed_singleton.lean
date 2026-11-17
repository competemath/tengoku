import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
@isnad1 id=ex.1h5v.s8.1c131584e155 from=translated src=- shape=e6e14966 vocab=940811d9
-/
theorem solution
    {k₀ : Type u} [Field k₀] {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]
    (y : F) (hy : IsClosed ({y} : Set F)) :
    ∃ z : Spec (CommRingCat.of k) ⟶ F,
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ∧ z.base (IsLocalRing.closedPoint k) = y := by

  set g := F.fromSpecResidueField y ≫ f with hg
  have hfin : IsFinite g := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := g)).mpr inferInstance
  let φ : CommRingCat.of k₀ ⟶ F.residueField y := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hint : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  letI : Algebra k₀ (F.residueField y) := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral k₀ (F.residueField y) := ⟨hint⟩

  let ψ : F.residueField y →ₐ[k₀] k := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    exact ψ.commutes a
  · have hmem : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y).base
        (IsLocalRing.closedPoint k) ∈ Set.range (F.fromSpecResidueField y).base :=
      ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem
