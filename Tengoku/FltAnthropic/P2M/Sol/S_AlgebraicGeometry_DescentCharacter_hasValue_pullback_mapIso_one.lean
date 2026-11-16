import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_DescentCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharOne

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem isBaseScalar_id (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) : IsBaseScalar f (𝟙 M) 1 := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, baseSection_one, one_smul]

theorem translateIso_mapIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    translateIso h ((Scheme.Modules.pullback q).mapIso ι) = (Scheme.Modules.pullback q).mapIso ι := by
  ext : 1
  have nat := (transportNatIso h).hom.naturality ι.hom

  simp only [translateIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, ← transportNatIso_app]
  have nat' : (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback q).map ι.hom) ≫
      (transportNatIso h).hom.app M = (transportNatIso h).hom.app N ≫ (Scheme.Modules.pullback q).map ι.hom := nat
  rw [Iso.inv_comp_eq, Iso.app_hom, Iso.app_hom]
  exact nat'

theorem hasValue_pullback_mapIso_one (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    HasValue f h ((Scheme.Modules.pullback q).mapIso ι) 1 := by
  unfold HasValue discrepancy
  rw [translateIso_mapIso, Iso.symm_self_id]
  exact isBaseScalar_id f _

end KcDescCharOne

theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (ι : N ≅ M) :
    HasValue f h ((Scheme.Modules.pullback q).mapIso ι) 1 :=
  KcDescCharOne.hasValue_pullback_mapIso_one f h ι
