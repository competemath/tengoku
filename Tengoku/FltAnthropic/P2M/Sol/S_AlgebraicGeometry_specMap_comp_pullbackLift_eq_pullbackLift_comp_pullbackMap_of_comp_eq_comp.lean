import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Ws23
namespace BCInt

/--
@isnad1 id=eq.5h13v.s9.6d2605869460 from=translated src=- shape=160a700c vocab=31cccd89
-/
theorem main
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) := by

  have h1 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom e) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hea]
  have h2 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom c) = Spec.map (CommRingCat.ofHom c) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hec]

  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, h1, Category.assoc, hι]
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h2]

end Ws23.BCInt

/--
@isnad1 id=eq.5h13v.s9.6d2605869460 from=translated src=- shape=160a700c vocab=31cccd89
-/
theorem solution
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) :=
  Ws23.BCInt.main g s ι E hE e hι a c hsq eA hea hec
