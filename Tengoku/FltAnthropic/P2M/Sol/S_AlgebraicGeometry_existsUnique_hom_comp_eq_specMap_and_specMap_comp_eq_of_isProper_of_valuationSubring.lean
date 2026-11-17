import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=existsun.1h7v.s9.dc97d6cc185b from=translated src=- shape=34614095 vocab=913e6e4d
-/
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {K : Type u} [Field K] (A : ValuationSubring K)
    (ρ : R →+* ↥A)
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ)) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom ρ) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by
  have hval : ValuativeCriterion f := by
    have h := congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion X) (Spec (CommRingCat.of R))) f
    have hP : IsProper f := inferInstance
    rw [h] at hP
    exact hP.1.1.1
  have hsq : CommSq x (Spec.map (CommRingCat.ofHom (algebraMap ↥A K))) f (Spec.map (CommRingCat.ofHom ρ)) := ⟨hx⟩
  let S : ValuativeCommSq f :=
    { R := ↥A, K := K, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨huniq⟩ := hval S
  let l := (default : S.commSq.LiftStruct)
  refine ⟨l.l, ⟨l.fac_right, l.fac_left⟩, ?_⟩
  rintro s ⟨hs₁, hs₂⟩
  have : (⟨s, hs₂, hs₁⟩ : S.commSq.LiftStruct) = l := Subsingleton.elim _ _
  exact congrArg CommSq.LiftStruct.l this

