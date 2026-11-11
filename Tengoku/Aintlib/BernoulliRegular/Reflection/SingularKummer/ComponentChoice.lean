module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.SingularPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: choosing a nontrivial lift from a component

This file isolates the elementary group-theoretic part of the later singular-Kummer lift
argument.  Once a character component of the singular group maps onto the
matching character component of `A[p]`, any nontrivial element in the target
component has a lift in the source component with nontrivial image.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ComponentChoice

variable {G H : Type*} [Group G] [Group H]

/-- If `φ` maps the subgroup `S` onto the subgroup `T`, and `T` is nontrivial,
then some element of `S` has nontrivial image.
@isnad1 id=ex.1h5v.s7.d2f2d7998ce3 from=translated src=- shape=a75796fe vocab=5e4a5ada
-/
theorem exists_lift_of_map_eq_of_nontrivial
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    [Nontrivial T] (hmap : S.map φ = T) :
    ∃ x : S, φ x.1 ≠ 1 := by
  obtain ⟨y, hy_mem, hy_ne⟩ := Subgroup.exists_ne_one_of_nontrivial T
  have hy_map : y ∈ S.map φ := by
    simpa [hmap] using hy_mem
  obtain ⟨x, hxS, hx⟩ := hy_map
  refine ⟨⟨x, hxS⟩, ?_⟩
  intro hx_one
  exact hy_ne (by rw [← hx, hx_one])

/-- A version using `T ≠ ⊥` instead of a typeclass `Nontrivial T`.
@isnad1 id=ex.2h5v.s7.6cf9a5a3a87f from=translated src=- shape=e42f8c7c vocab=77be7a3d
-/
theorem exists_lift_of_map_eq_of_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    ∃ x : S, φ x.1 ≠ 1 := by
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT
  exact exists_lift_of_map_eq_of_nontrivial φ S T hmap

/-- Elementwise form: the lift can be viewed in the ambient source group and
its image lies in the target component.
@isnad1 id=ex.2h5v.s7.0f4bddb047af from=translated src=- shape=dd98fca9 vocab=9ed2e2e3
-/
theorem exists_mem_lift_with_nontrivial_image_of_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    ∃ x : G, x ∈ S ∧ φ x ∈ T ∧ φ x ≠ 1 := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot φ S T hmap hT
  refine ⟨x.1, x.2, ?_, hx_ne⟩
  rw [← hmap]
  exact ⟨x.1, x.2, rfl⟩

/-- A surjective component map forces the source component to be nontrivial
whenever the target component is nontrivial.
@isnad1 id=ne.2h5v.s6.7bd89242ce03 from=translated src=- shape=79c91e2b vocab=33d285b0
-/
theorem source_ne_bot_of_map_eq_of_target_ne_bot
    (φ : G →* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : S.map φ = T) (hT : T ≠ ⊥) :
    S ≠ ⊥ := by
  obtain ⟨x, hx_ne⟩ := exists_lift_of_map_eq_of_ne_bot φ S T hmap hT
  exact (Subgroup.nontrivial_iff_ne_bot S).1
    ⟨⟨x, 1, fun h ↦ hx_ne (by simpa using congrArg (fun z : S ↦ φ z.1) h)⟩⟩

open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Singular-sequence form of the component-lifting lemma.  If a chosen
component of the singular group maps onto a chosen component of `A[p]`, then a
nontrivial element of the target component has a singular lift in the source
component.
@isnad1 id=ex.2h5v.s12.3452d0638e80 from=translated src=- shape=ea77cd54 vocab=74b85ed7
-/
theorem exists_singular_lift_of_component_map_eq_of_ne_bot
    (p : ℕ)
    (Scomp : Subgroup (SingularPair.SingularGroup (R := R) (K := K) p))
    (Acomp : Subgroup (SingularPair.classGroupPTorsion (R := R) p))
    (hmap :
      Scomp.map (SingularPair.singularGroupClassMapToPTorsion
        (R := R) (K := K) p) = Acomp)
    (hA : Acomp ≠ ⊥) :
    ∃ x : Scomp,
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x.1 ≠ 1 :=
  exists_lift_of_map_eq_of_ne_bot
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    Scomp Acomp hmap hA

/-- Elementwise singular-sequence form, with membership in the chosen source
and target components recorded explicitly.
@isnad1 id=ex.2h5v.s12.ee335cab56eb from=translated src=- shape=c7ad2737 vocab=1b3d0b42
-/
theorem exists_singular_mem_lift_with_nontrivial_class_of_component_map_eq_of_ne_bot
    (p : ℕ)
    (Scomp : Subgroup (SingularPair.SingularGroup (R := R) (K := K) p))
    (Acomp : Subgroup (SingularPair.classGroupPTorsion (R := R) p))
    (hmap :
      Scomp.map (SingularPair.singularGroupClassMapToPTorsion
        (R := R) (K := K) p) = Acomp)
    (hA : Acomp ≠ ⊥) :
    ∃ x : SingularPair.SingularGroup (R := R) (K := K) p,
      x ∈ Scomp ∧
        SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x ∈ Acomp ∧
          SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x ≠ 1 :=
  exists_mem_lift_with_nontrivial_image_of_ne_bot
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    Scomp Acomp hmap hA

end ComponentChoice

end SingularKummer
end Reflection
end BernoulliRegular

end
