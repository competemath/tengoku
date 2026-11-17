import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_DescentCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_DescentCharacter_hasValue_trans.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_trans

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharTrans

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

/--
@isnad1 id=eq.1h9v.s8.157739fded1d from=translated src=- shape=10f6534e vocab=8a023606
-/
theorem translateIso_trans {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P) :
    translateIso h (β ≪≫ β') = translateIso h β ≪≫ translateIso h β' := by
  ext : 1
  simp [translateIso, Functor.mapIso_trans]

/--
@isnad1 id=eq.1h7v.s7.2ef8ae4b644d from=translated src=- shape=f933ca24 vocab=4fe2bfdd
-/
theorem translateIso_eq {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    translateIso h β = β ≪≫ discrepancy h β := by
  ext : 1
  simp [discrepancy]

/--
@isnad1 id=eq.1h9v.s9.7df62e98a147 from=translated src=- shape=d5f8a74f vocab=5edb57ec
-/
theorem discrepancy_trans_hom {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P) :
    (discrepancy h (β ≪≫ β')).hom = β'.inv ≫ (discrepancy h β).hom ≫ β'.hom ≫ (discrepancy h β').hom := by
  have e1 : (discrepancy h (β ≪≫ β')).hom = β'.inv ≫ β.inv ≫ (translateIso h (β ≪≫ β')).hom := by
    simp [discrepancy]
  rw [e1, translateIso_trans, Iso.trans_hom, translateIso_eq h β, translateIso_eq h β']
  simp

/--
@isnad1 id=isbasesc.2h8v.s6.af3748b73f68 from=translated src=- shape=3c59c54c vocab=68c3b71a
-/
theorem isBaseScalar_comp (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} {σ σ' : M ⟶ M} {c c' : R}
    (hσ : IsBaseScalar f σ c) (hσ' : IsBaseScalar f σ' c') : IsBaseScalar f (σ ≫ σ') (c * c') := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hσ U s, Scheme.Modules.Hom.app_smul, hσ' U,
    smul_smul, baseSection_mul, mul_comm]

/--
@isnad1 id=isbasesc.1h8v.s6.a4723f8a281a from=translated src=- shape=d1e044ca vocab=72bbf91d
-/
theorem isBaseScalar_conj (f : X ⟶ Spec (CommRingCat.of R)) {M M' : X.Modules} (e : M ≅ M') {σ : M ⟶ M} {c : R}
    (hσ : IsBaseScalar f σ c) : IsBaseScalar f (e.inv ≫ σ ≫ e.hom) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, hσ U, Scheme.Modules.Hom.app_smul, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/--
@isnad1 id=hasvalue.3h13v.s7.fc53025d78b5 from=translated src=- shape=da8f9c11 vocab=e1bbaef3
-/
theorem hasValue_trans (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P)
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h (β ≪≫ β') (c * c') := by
  unfold HasValue
  rw [discrepancy_trans_hom]
  have h1 : IsBaseScalar f (β'.inv ≫ (discrepancy h β).hom ≫ β'.hom) c := isBaseScalar_conj f β' hβ
  have h2 := isBaseScalar_comp f h1 hβ'
  simpa [Category.assoc] using h2

end KcDescCharTrans

/--
@isnad1 id=hasvalue.3h13v.s7.fc53025d78b5 from=translated src=- shape=da8f9c11 vocab=e1bbaef3
-/
theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P)
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h (β ≪≫ β') (c * c') :=
  KcDescCharTrans.hasValue_trans f h β β' c c' hβ hβ'
