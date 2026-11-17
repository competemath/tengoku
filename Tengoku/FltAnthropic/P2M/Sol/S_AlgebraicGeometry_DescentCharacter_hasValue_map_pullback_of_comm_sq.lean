import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_DescentCharacter
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace HVBC

variable {X Y Z W : Scheme.{u}}

/--
@isnad1 id=eq.1h5v.s7.21feeb80e6a8 from=translated src=- shape=f40cce6d vocab=a08a0a3c
-/
theorem congr_hom_app {g g' : X ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app M =
      eqToHom (show (Scheme.Modules.pullback g).obj M = (Scheme.Modules.pullback g').obj M by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/--
@isnad1 id=eq.1h5v.s7.79a349bf9942 from=translated src=- shape=75d03736 vocab=62e07d46
-/
theorem congr_inv_app {g g' : X ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app M =
      eqToHom (show (Scheme.Modules.pullback g').obj M = (Scheme.Modules.pullback g).obj M by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/--
@isnad1 id=eq.0h8v.s10.63087e6ce412 from=translated src=- shape=6737d789 vocab=79e4b074
-/
@[reassoc]
theorem comp_assoc_app (a : X ⟶ Y) (b : Y ⟶ Z) (r : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback r).obj M) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) r).hom.app M =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b r).hom.app M) ≫
        (Scheme.Modules.pullbackComp a (b ≫ r)).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (a ≫ b ≫ r)).obj M =
            (Scheme.Modules.pullback ((a ≫ b) ≫ r)).obj M by rw [Category.assoc]) := by
  have assoc := congrArg (fun α => NatTrans.app α M) (Scheme.Modules.pseudofunctor_associativity a b r)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    eqToHom_app, Functor.comp_obj, Category.id_comp] at assoc
  rw [← Iso.app_inv, ← Iso.app_inv, ← Functor.mapIso_inv, Iso.inv_comp_eq, Iso.inv_comp_eq] at assoc
  refine assoc.trans ?_
  simp only [Functor.mapIso_hom, Iso.app_hom]

/--
@isnad1 id=eq.0h8v.s10.d5a5efeb1096 from=translated src=- shape=fb4a562c vocab=79e4b074
-/
@[reassoc]
theorem comp_assoc_app' (a : X ⟶ Y) (b : Y ⟶ Z) (r : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b r).hom.app M) ≫
        (Scheme.Modules.pullbackComp a (b ≫ r)).hom.app M =
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback r).obj M) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) r).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback ((a ≫ b) ≫ r)).obj M =
            (Scheme.Modules.pullback (a ≫ b ≫ r)).obj M by rw [Category.assoc]) := by
  have e := reassoc_of% (comp_assoc_app a b r M)
  try dsimp only [Functor.comp_obj] at *
  rw [e, eqToHom_trans, eqToHom_refl, Category.comp_id]

/--
@isnad1 id=eq.1h7v.s9.3210d537b0d6 from=translated src=- shape=c98a1847 vocab=601de1ef
-/
@[reassoc]
theorem map_congr_comp {a : X ⟶ Y} {g g' : Y ⟶ Z} (e : g = g') (M : Z.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp a g').hom.app M =
      (Scheme.Modules.pullbackComp a g).hom.app M ≫
        (Scheme.Modules.pullbackCongr (show a ≫ g = a ≫ g' by rw [e])).hom.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/--
@isnad1 id=eq.1h7v.s9.5d4ca4cedce1 from=translated src=- shape=1e0eaee0 vocab=5abf646c
-/
@[reassoc]
theorem congr_comp {a a' : X ⟶ Y} (e : a = a') (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp a' g).hom.app M =
      (Scheme.Modules.pullbackComp a g).hom.app M ≫
        (Scheme.Modules.pullbackCongr (show a ≫ g = a' ≫ g by rw [e])).hom.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

section

variable {X' Y' : Scheme.{u}} {T : X ⟶ X} {q : X ⟶ Y} {T' : X' ⟶ X'} {q' : X' ⟶ Y'} {gX : X' ⟶ X} {gY : Y' ⟶ Y}

noncomputable def Phi (hq : gX ≫ q = q' ≫ gY) (P : Y.Modules) :
    (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback gY).obj P) ≅
      (Scheme.Modules.pullback gX).obj ((Scheme.Modules.pullback q).obj P) :=
  (Scheme.Modules.pullbackComp q' gY).app P ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app P ≪≫
    ((Scheme.Modules.pullbackComp gX q).app P).symm

noncomputable def Psi (hT : T' ≫ gX = gX ≫ T) :
    Scheme.Modules.pullback gX ⋙ Scheme.Modules.pullback T' ≅ Scheme.Modules.pullback T ⋙ Scheme.Modules.pullback gX :=
  Scheme.Modules.pullbackComp T' gX ≪≫ Scheme.Modules.pullbackCongr hT ≪≫ (Scheme.Modules.pullbackComp gX T).symm

/--
@isnad1 id=eq.1h9v.s9.be222b5765ab from=translated src=- shape=62332553 vocab=e9744c6f
-/
theorem Phi_hom (hq : gX ≫ q = q' ≫ gY) (P : Y.Modules) :
    (Phi hq P).hom = (Scheme.Modules.pullbackComp q' gY).hom.app P ≫ (Scheme.Modules.pullbackCongr hq.symm).hom.app P ≫
      (Scheme.Modules.pullbackComp gX q).inv.app P := rfl

/--
@isnad1 id=eq.1h6v.s9.1d6f83a55fb2 from=translated src=- shape=15c7e71b vocab=759d2e75
-/
theorem Psi_hom_app (hT : T' ≫ gX = gX ≫ T) (P : X.Modules) :
    (Psi hT).hom.app P = (Scheme.Modules.pullbackComp T' gX).hom.app P ≫ (Scheme.Modules.pullbackCongr hT).hom.app P ≫
      (Scheme.Modules.pullbackComp gX T).inv.app P := rfl

/--
@isnad1 id=eq.1h5v.s8.34b03455d97f from=translated src=- shape=2934ad0c vocab=5b884813
-/
theorem transportIso_hom' {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (P : Y.Modules) :
    (transportIso h P).hom = (Scheme.Modules.pullbackComp T q).hom.app P ≫ (Scheme.Modules.pullbackCongr h).hom.app P := rfl

/--
@isnad1 id=eq.4h11v.s11.97719c06204e from=translated src=- shape=d85d72f0 vocab=34e84c72
-/
theorem EL (h : T ≫ q = q) (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T) (N : Y.Modules) :
    ((Scheme.Modules.pullback T').map
        ((Scheme.Modules.pullbackComp q' gY).hom.app N ≫ (Scheme.Modules.pullbackCongr hq.symm).hom.app N ≫
          (Scheme.Modules.pullbackComp gX q).inv.app N) ≫
      ((Scheme.Modules.pullbackComp T' gX).hom.app ((Scheme.Modules.pullback q).obj N) ≫
        (Scheme.Modules.pullbackCongr hT).hom.app ((Scheme.Modules.pullback q).obj N) ≫
        (Scheme.Modules.pullbackComp gX T).inv.app ((Scheme.Modules.pullback q).obj N)) ≫
      (Scheme.Modules.pullback gX).map
        ((Scheme.Modules.pullbackComp T q).hom.app N ≫ (Scheme.Modules.pullbackCongr h).hom.app N)) ≫
      (Scheme.Modules.pullbackComp gX q).hom.app N =
    (Scheme.Modules.pullbackComp T' q').hom.app ((Scheme.Modules.pullback gY).obj N) ≫
      (Scheme.Modules.pullbackComp (T' ≫ q') gY).hom.app N ≫
      eqToHom (show (Scheme.Modules.pullback ((T' ≫ q') ≫ gY)).obj N = (Scheme.Modules.pullback (gX ≫ q)).obj N by
        rw [h', ← hq]) := by
  try dsimp only [Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have e1 := map_congr_comp (a := gX) h N
  have e2 := reassoc_of% (comp_assoc_app' gX T q N)
  have e3 := reassoc_of% (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp gX T) ((Scheme.Modules.pullback q).obj N))
  have e4 := reassoc_of% (congr_comp hT q N)
  have e5 := reassoc_of% (comp_assoc_app T' gX q N)
  have e6 := reassoc_of% (Iso.map_inv_hom_id ((Scheme.Modules.pullbackComp gX q).app N) (Scheme.Modules.pullback T'))
  have e7 := reassoc_of% (map_congr_comp (a := T') hq.symm N)
  have e8 := reassoc_of% (comp_assoc_app' T' q' gY N)
  try dsimp only [Functor.comp_obj, Iso.app_hom, Iso.app_inv] at *
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  simp only [congr_hom_app, eqToHom_trans, eqToHom_trans_assoc]

/--
@isnad1 id=eq.2h10v.s10.a7d1c2b992a8 from=translated src=- shape=a453a4d9 vocab=13dd4a39
-/
theorem ER (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (N : Y.Modules) :
    (((Scheme.Modules.pullbackComp T' q').hom.app ((Scheme.Modules.pullback gY).obj N) ≫
      (Scheme.Modules.pullbackCongr h').hom.app ((Scheme.Modules.pullback gY).obj N)) ≫
      ((Scheme.Modules.pullbackComp q' gY).hom.app N ≫ (Scheme.Modules.pullbackCongr hq.symm).hom.app N ≫
        (Scheme.Modules.pullbackComp gX q).inv.app N)) ≫
      (Scheme.Modules.pullbackComp gX q).hom.app N =
    (Scheme.Modules.pullbackComp T' q').hom.app ((Scheme.Modules.pullback gY).obj N) ≫
      (Scheme.Modules.pullbackComp (T' ≫ q') gY).hom.app N ≫
      eqToHom (show (Scheme.Modules.pullback ((T' ≫ q') ≫ gY)).obj N = (Scheme.Modules.pullback (gX ≫ q)).obj N by
        rw [h', ← hq]) := by
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [congr_comp_assoc h' gY N]
  try dsimp only [Functor.comp_obj]
  simp only [congr_hom_app, eqToHom_trans, eqToHom_trans_assoc]

/--
@isnad1 id=eq.4h11v.s10.0f18593732af from=translated src=- shape=0bbb0e28 vocab=f17856c9
-/
theorem coh (h : T ≫ q = q) (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T) (N : Y.Modules) :
    (Scheme.Modules.pullback T').map (Phi hq N).hom ≫ (Psi hT).hom.app ((Scheme.Modules.pullback q).obj N) ≫
        (Scheme.Modules.pullback gX).map (transportIso h N).hom =
      (transportIso h' ((Scheme.Modules.pullback gY).obj N)).hom ≫ (Phi hq N).hom := by
  rw [Phi_hom, Psi_hom_app, transportIso_hom', transportIso_hom']
  refine (cancel_mono ((Scheme.Modules.pullbackComp gX q).hom.app N)).1 ?_
  exact (EL h h' hq hT N).trans (ER h' hq N).symm

/--
@isnad1 id=eq.4h11v.s10.960d7aefdfbd from=translated src=- shape=94b997e4 vocab=eae2639c
-/
@[reassoc]
theorem C1 (h : T ≫ q = q) (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T) (N : Y.Modules) :
    (Phi hq N).inv ≫ (transportIso h' ((Scheme.Modules.pullback gY).obj N)).inv ≫
        (Scheme.Modules.pullback T').map (Phi hq N).hom =
      (Scheme.Modules.pullback gX).map (transportIso h N).inv ≫ (Psi hT).inv.app ((Scheme.Modules.pullback q).obj N) := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq]
  have hE : (Scheme.Modules.pullback gX).map (transportIso h N).inv ≫ (Psi hT).inv.app ((Scheme.Modules.pullback q).obj N) =
      ((Psi hT).app ((Scheme.Modules.pullback q).obj N) ≪≫ (Scheme.Modules.pullback gX).mapIso (transportIso h N)).inv := rfl
  rw [hE, ← Category.assoc, Iso.eq_comp_inv]
  exact coh h h' hq hT N

/--
@isnad1 id=eq.4h11v.s10.8c3982206f64 from=translated src=- shape=fadb2450 vocab=eae2639c
-/
theorem C2 (h : T ≫ q = q) (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T) (M : Y.Modules) :
    (Scheme.Modules.pullback T').map (Phi hq M).inv ≫ (transportIso h' ((Scheme.Modules.pullback gY).obj M)).hom =
      (Psi hT).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback gX).map (transportIso h M).hom ≫ (Phi hq M).inv := by
  rw [← Functor.mapIso_inv, Iso.inv_comp_eq, Functor.mapIso_hom]
  have e := reassoc_of% (coh h h' hq hT M)
  try dsimp only [Functor.comp_obj] at *
  rw [e, Iso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.1h8v.s9.ad17444ff605 from=translated src=- shape=892f6bf8 vocab=f60e2bcf
-/
@[reassoc]
theorem Psi_nat (hT : T' ≫ gX = gX ≫ T) {A B : X.Modules} (γ : A ⟶ B) :
    (Psi hT).inv.app A ≫ (Scheme.Modules.pullback T').map ((Scheme.Modules.pullback gX).map γ) ≫ (Psi hT).hom.app B =
      (Scheme.Modules.pullback gX).map ((Scheme.Modules.pullback T).map γ) := by
  have nat := (Psi hT).hom.naturality γ
  erw [nat, Iso.inv_hom_id_app_assoc]
  rfl

/--
@isnad1 id=eq.4h13v.s10.5dc29c5d02c3 from=translated src=- shape=ee3c5e55 vocab=1a96860c
-/
theorem key (h : T ≫ q = q) (h' : T' ≫ q' = q')
    (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    (discrepancy h' (Phi hq N ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫ (Phi hq M).symm)).hom =
      (Phi hq M).hom ≫ (Scheme.Modules.pullback gX).map (discrepancy h β).hom ≫ (Phi hq M).inv := by
  simp only [discrepancy, translateIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  have e1 := reassoc_of% (C1 h h' hq hT N)
  have e2 := C2 h h' hq hT M
  have e3 := reassoc_of% (Psi_nat hT β.hom)
  try dsimp only [Functor.comp_obj] at *
  rw [e1, e2, e3]

/--
@isnad1 id=hasvalue.6h19v.s9.ebf3dd271f26 from=translated src=- shape=b9f10879 vocab=138d5f6c
-/
theorem hasValue {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (h : T ≫ q = q) (h' : T' ≫ q' = q') (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T)
    (hf : gX ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {N M : Y.Modules} (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c : R) (hβ : HasValue f h β c) :
    HasValue f' h' (Phi hq N ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫ (Phi hq M).symm) (φ c) := by
  unfold HasValue
  rw [key h h' hq hT β]
  intro U s
  have hσ := AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map gX f f' φ hf hβ
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, hσ U, Scheme.Modules.Hom.app_smul, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, (Phi hq M).hom_inv_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

end

end HVBC

/--
@isnad1 id=hasvalue.6h19v.s10.4a3ef4b561c2 from=translated src=- shape=8a97a02b vocab=a59b047c
-/
theorem solution
    {X Y X' Y' : Scheme.{u}} {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T)
    (hf : gX ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {N M : Y.Modules} (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c : R) (hβ : HasValue f h β c) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      (φ c) := by
  have main := HVBC.hasValue f f' φ h h' hq hT hf β c hβ
  have e : ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm) =
      HVBC.Phi hq N ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫ (HVBC.Phi hq M).symm := by
    apply Iso.ext
    simp only [HVBC.Phi, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_hom, HVBC.congr_hom_app, HVBC.congr_inv_app, Category.assoc]
    try rfl
  exact e ▸ main
