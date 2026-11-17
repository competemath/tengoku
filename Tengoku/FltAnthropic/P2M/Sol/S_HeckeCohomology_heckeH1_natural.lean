import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_TransferHecke
import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeCohomology_heckeH1_natural.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeCohomology_heckeH1_natural

set_option autoImplicit false

namespace TWNatAux

open groupCohomology HeckeCohomology CategoryTheory

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)
  {A B : Rep k Γ} (f : A ⟶ B)

/--
@isnad1 id=eq.0h7v.s13.f3434278488c from=translated src=- shape=69751ea8 vocab=dec87afc
-/
theorem mapCocycles₁_id_apply (y : cocycles₁ A) (g : Γ) :
    (mapCocycles₁ (MonoidHom.id Γ) f y) g = f.hom (y g) := rfl

variable [S₂.FiniteIndex] (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
  (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
  (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a))

include hcomm in

/--
@isnad1 id=eq.3h11v.s14.0de5e6427061 from=translated src=- shape=623fde3b vocab=0f989212
-/
theorem heckeZ1_natural (y : cocycles₁ A) :
    heckeZ1 S₁ S₂ c B φB hφB (mapCocycles₁ (MonoidHom.id Γ) f y) =
      mapCocycles₁ (MonoidHom.id Γ) f (heckeZ1 S₁ S₂ c A φA hφA y) := by
  apply cocycles₁_ext
  intro γ
  rw [heckeZ1_apply, mapCocycles₁_id_apply, heckeZ1_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mapCocycles₁_id_apply, Rep.hom_comm_apply, hcomm]

end TWNatAux

open groupCohomology HeckeCohomology in
/--
@isnad1 id=eq.3h11v.s11.00c78deca609 from=translated src=- shape=b57b2558 vocab=33abbb4a
-/
theorem solution {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) {A B : Rep k Γ} [S₂.FiniteIndex] (f : A ⟶ B)
    (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
    (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
    (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a)) (x : H1 A) :
    heckeH1 S₁ S₂ c B φB hφB (map (MonoidHom.id Γ) f 1 x) =
      map (MonoidHom.id Γ) f 1 (heckeH1 S₁ S₂ c A φA hφA x) := by
  induction x using H1_induction_on with
  | h y =>
    rw [H1π_comp_map_apply, heckeH1_H1π S₁ S₂ c B φB hφB, heckeH1_H1π S₁ S₂ c A φA hφA,
      H1π_comp_map_apply, TWNatAux.heckeZ1_natural S₁ S₂ c f φA hφA φB hφB hcomm]
