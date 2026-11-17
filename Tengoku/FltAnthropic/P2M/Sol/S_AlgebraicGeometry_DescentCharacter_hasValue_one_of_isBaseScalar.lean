import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_DescentCharacter
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharAut

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

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
@isnad1 id=isbasesc.0h4v.s5.90dbd27eec10 from=translated src=- shape=953a4131 vocab=e42e04c8
-/
theorem isBaseScalar_id (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) : IsBaseScalar f (𝟙 M) 1 := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, baseSection_one, one_smul]

/--
@isnad1 id=isbasesc.2h7v.s6.b02b24e0fb8f from=translated src=- shape=e4f06ad1 vocab=a17259ac
-/
theorem isBaseScalar_pullback_map_self (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} (hT : T ≫ f = f)
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f ((Scheme.Modules.pullback T).map σ) c := by
  have hg : T ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [hT, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  exact AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map T f f (RingHom.id R) hg hσ

/--
@isnad1 id=hasvalue.3h9v.s7.f2bf7e8dc3d4 from=translated src=- shape=67f7dd9a vocab=250102e0
-/
theorem hasValue_one_of_isBaseScalar (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (hT : T ≫ f = f) {M : Y.Modules}
    (γ : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M) (c : R)
    (hγ : IsBaseScalar f γ.hom c) :
    HasValue f h γ 1 := by
  have htr : IsBaseScalar f (translateIso h γ).hom c := by
    have hpb := isBaseScalar_pullback_map_self f hT hγ
    have := isBaseScalar_conj f (transportIso h M) hpb
    simpa [translateIso] using this
  have heq : (translateIso h γ).hom = γ.hom := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rw [htr U s, hγ U s]
  have hd : (discrepancy h γ).hom = 𝟙 _ := by
    show γ.inv ≫ (translateIso h γ).hom = 𝟙 _
    rw [heq, Iso.inv_hom_id]
  unfold HasValue
  rw [hd]
  exact isBaseScalar_id f _

end KcDescCharAut

/--
@isnad1 id=hasvalue.3h9v.s7.f2bf7e8dc3d4 from=translated src=- shape=67f7dd9a vocab=250102e0
-/
theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (hT : T ≫ f = f) {M : Y.Modules}
    (γ : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M) (c : R)
    (hγ : IsBaseScalar f γ.hom c) :
    HasValue f h γ 1 :=
  KcDescCharAut.hasValue_one_of_isBaseScalar f h hT γ c hγ
