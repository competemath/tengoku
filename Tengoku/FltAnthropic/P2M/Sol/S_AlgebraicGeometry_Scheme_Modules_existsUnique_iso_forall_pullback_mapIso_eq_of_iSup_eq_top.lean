import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.lean`: wrote out 10 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 3 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top

set_option autoImplicit false

open _root_.CategoryTheory open _root_.Opposite open _root_.AlgebraicGeometry

universe u v

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Opens Scheme.Opens.ι_preimage_self Scheme.Opens.opensRange_ι Scheme.Modules.pullbackComp Scheme.Modules.map_homOfLE_pullbackLocalSection Scheme.Modules.pullbackLocalSection_app Scheme.Modules.pullback_hom_ext Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Hom.preimage_inf Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules.pullbackCongr Modules Opens homOfLE_ι Opens.ι_preimage_self Opens.opensRange_ι Modules.pullbackComp Modules.map_homOfLE_pullbackLocalSection Modules.pullbackLocalSection_app Modules.pullback_hom_ext Modules.existsUnique_hom_app_eq_of_iSup_eq_top)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (Hom.app_smul pullback presheaf Hom.comp_app Hom Hom.id_app Hom.app restrictAdjunction pullbackCongr isSheaf pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv pullbackComp pullbackLocalSection pullbackLocalSection_def pullbackLocalSection_add pullbackLocalSection_smul map_homOfLE_pullbackLocalSection pullbackLocalSection_app pullback_hom_ext existsUnique_hom_app_eq_of_iSup_eq_top)
namespace IsoGlueAux
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules open _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules open _root_.TopologicalSpace

universe w

variable {X Y Z : Scheme.{u}}

/--
@isnad1 id=eq.0h8v.s12.4f13e68f4ba5 from=translated src=- shape=33453e5b vocab=c426c32e
-/
lemma app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V x) = φ.app U (M.presheaf.map i.op x) := by
  have h := φ.mapPresheaf.naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, V) → Γ(N, U))) h) x).symm

/--
@isnad1 id=bijectiv.1h5v.s10.e38c44236b40 from=translated src=- shape=a0e6f81c vocab=d3c2860b
-/
lemma map_bijective_of_eq (M : X.Modules) {U V : X.Opens} (e : U = V) (i : U ⟶ V) :
    Function.Bijective (M.presheaf.map i.op) := by
  subst e
  obtain rfl : i = 𝟙 U := Subsingleton.elim _ _
  simp only [op_id]
  exact ⟨fun a b h => by simpa using h, fun b => ⟨b, by simp⟩⟩

/--
@isnad1 id=eq.0h8v.s11.a2655bcf8447 from=translated src=- shape=9737110a vocab=729d4ee2
-/
lemma pullbackComp_inv_app_app_pullbackLocalSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) s) =
      pullbackLocalSection f (pullbackLocalSection g s) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun k => Scheme.Modules.Hom.app k U s) h
  rw [pullbackLocalSection_def, pullbackLocalSection_def, pullbackLocalSection_def]
  exact h'.symm

/--
@isnad1 id=eq.0h8v.s11.9abc0d432be0 from=translated src=- shape=f660a1cd vocab=0aca4a7f
-/
lemma pullbackComp_hom_app_app_pullbackLocalSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (pullbackLocalSection f (pullbackLocalSection g s)) =
      pullbackLocalSection (f ≫ g) s := by
  rw [← pullbackComp_inv_app_app_pullbackLocalSection f g M U s, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/--
@isnad1 id=bijectiv.1h5v.s9.ae23e4741c00 from=translated src=- shape=be64ae3c vocab=3a3e1b38
-/
lemma pullbackLocalSection_bijective_of_le (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (W : Y.Opens) (hW : W ≤ f.opensRange) :
    Function.Bijective (fun s : Γ(M, W) => pullbackLocalSection f s) := by
  have e : f ''ᵁ f ⁻¹ᵁ W = W := by rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have key : ∀ s : Γ(M, W), pullbackLocalSection f s =
      (((restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)).hom.app M).app (f ⁻¹ᵁ W)
        (M.presheaf.map (homOfLE (f.image_preimage_le W)).op s) := by
    intro s
    have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f) (pullbackPushforwardAdjunction f) M
    have h' := congrArg (fun k => Scheme.Modules.Hom.app k W s) h
    rw [pullbackLocalSection_def]
    exact h'.symm
  rw [show (fun s : Γ(M, W) => pullbackLocalSection f s) =
      ((((restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)).hom.app M).app (f ⁻¹ᵁ W)) ∘
        (M.presheaf.map (homOfLE (f.image_preimage_le W)).op) from funext key]
  exact (ConcreteCategory.bijective_of_isIso _).comp (map_bijective_of_eq M e (homOfLE (f.image_preimage_le W)))

/--
@isnad1 id=eq.3h7v.s11.cabd8f94dbf9 from=translated src=- shape=4cfec9fe vocab=e396c4ff
-/
lemma sections_eq_of_cover (M : X.Modules) {K : Type w} (W : X.Opens) (Wk : K → X.Opens)
    (hle : ∀ k, Wk k ≤ W) (hcov : W ≤ ⨆ k, Wk k) (s t : Γ(M, W))
    (h : ∀ k, M.presheaf.map (homOfLE (hle k)).op s = M.presheaf.map (homOfLE (hle k)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨M.presheaf, M.isSheaf⟩ Wk W (fun k => homOfLE (hle k)) hcov s t h

section transport

variable {M N P : X.Modules} {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

def pb (M : X.Modules) {W : X.Opens} (hW : W ≤ f.opensRange) :
    Γ(M, W) ≃ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ W) :=
  Equiv.ofBijective _ (pullbackLocalSection_bijective_of_le f M W hW)

/--
@isnad1 id=eq.1h6v.s11.3706558fabc5 from=translated src=- shape=d9f05d9e vocab=6b1f6c9d
-/
@[scoped simp] lemma pb_apply (M : X.Modules) {W : X.Opens} (hW : W ≤ f.opensRange) (x : Γ(M, W)) :
    pb f M hW x = pullbackLocalSection f x := rfl

def T (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W : X.Opens} (hW : W ≤ f.opensRange) (x : Γ(M, W)) : Γ(N, W) :=
  (pb f N hW).symm (Φ.app (f ⁻¹ᵁ W) (pullbackLocalSection f x))

/--
@isnad1 id=eq.1h8v.s11.f8b3bd09ef99 from=translated src=- shape=923eaa28 vocab=ca9728a2
-/
lemma pullbackLocalSection_T (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W : X.Opens} (hW : W ≤ f.opensRange) (x : Γ(M, W)) :
    pullbackLocalSection f (T f Φ hW x) = Φ.app (f ⁻¹ᵁ W) (pullbackLocalSection f x) :=
  (pb f N hW).apply_symm_apply _

/--
@isnad1 id=eq.1h10v.s8.b9d2f8f43bef from=translated src=- shape=06abad70 vocab=c25f9794
-/
lemma T_comp (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (Φ' : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback f).obj P)
    {W : X.Opens} (hW : W ≤ f.opensRange) (x : Γ(M, W)) :
    T f (Φ ≫ Φ') hW x = T f Φ' hW (T f Φ hW x) := by
  apply (pb f P hW).injective
  simp only [pb_apply, pullbackLocalSection_T, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]

/--
@isnad1 id=eq.1h6v.s8.2e0b47cbe4d8 from=translated src=- shape=aca62f47 vocab=b62f303c
-/
lemma T_id {W : X.Opens} (hW : W ≤ f.opensRange) (x : Γ(M, W)) :
    T f (𝟙 ((Scheme.Modules.pullback f).obj M)) hW x = x := by
  apply (pb f M hW).injective
  simp only [pb_apply, pullbackLocalSection_T, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/--
@isnad1 id=eq.1h9v.s11.161bf9b2577d from=translated src=- shape=9b196bfc vocab=7f09bad0
-/
lemma T_add (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W : X.Opens} (hW : W ≤ f.opensRange) (x y : Γ(M, W)) :
    T f Φ hW (x + y) = T f Φ hW x + T f Φ hW y := by
  apply (pb f N hW).injective
  simp only [pb_apply, pullbackLocalSection_T, pullbackLocalSection_add, map_add]

/--
@isnad1 id=eq.1h9v.s13.132e486919ff from=translated src=- shape=51072ddc vocab=aa967241
-/
lemma T_smul (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W : X.Opens} (hW : W ≤ f.opensRange) (r : Γ(X, W)) (x : Γ(M, W)) :
    T f Φ hW (r • x) = r • T f Φ hW x := by
  apply (pb f N hW).injective
  simp only [pb_apply, pullbackLocalSection_T, pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]

/--
@isnad1 id=eq.2h9v.s11.886527af5453 from=translated src=- shape=a1a59699 vocab=32c1e138
-/
lemma T_restrict (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W W' : X.Opens} (hW : W ≤ f.opensRange) (h : W' ≤ W) (x : Γ(M, W)) :
    N.presheaf.map (homOfLE h).op (T f Φ hW x) = T f Φ (h.trans hW) (M.presheaf.map (homOfLE h).op x) := by
  apply (pb f N (h.trans hW)).injective
  simp only [pb_apply]
  rw [pullbackLocalSection_T, ← map_homOfLE_pullbackLocalSection f h,
    ← map_homOfLE_pullbackLocalSection f h, pullbackLocalSection_T, app_naturality]

def Tlin (Φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {W : X.Opens} (hW : W ≤ f.opensRange) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun := T f Φ hW
  map_add' := T_add f Φ hW
  map_smul' := T_smul f Φ hW

end transport

/--
@isnad1 id=and.4h11v.s10.9c6f777d5e1f from=translated src=- shape=0350a8eb vocab=3b786e3a
-/
lemma T_nest {M N : X.Modules} {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] (j : Y₂ ⟶ Y₁) (hj : j ≫ f₁ = f₂)
    (E₁ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₁).obj N)
    (E₂ : (Scheme.Modules.pullback f₂).obj M ≅ (Scheme.Modules.pullback f₂).obj N)
    (hc : (Scheme.Modules.pullback j).mapIso E₁ =
      ((pullbackComp j f₁).app M ≪≫ (pullbackCongr hj).app M) ≪≫ E₂ ≪≫
        ((pullbackComp j f₁).app N ≪≫ (pullbackCongr hj).app N).symm)
    {W : X.Opens} (hW₁ : W ≤ f₁.opensRange) (hW₂ : W ≤ f₂.opensRange) :
    (∀ x : Γ(M, W), T f₁ E₁.hom hW₁ x = T f₂ E₂.hom hW₂ x) ∧
      (∀ x : Γ(N, W), T f₁ E₁.inv hW₁ x = T f₂ E₂.inv hW₂ x) := by
  subst hj

  have key : ∀ (P : X.Modules) (y : Γ(P, W)),
      ((pullbackComp j f₁).app P ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app P).hom.app ((j ≫ f₁) ⁻¹ᵁ W)
          (pullbackLocalSection j (pullbackLocalSection f₁ y)) =
        pullbackLocalSection (j ≫ f₁) y := by
    intro P y
    have h1 : ((pullbackComp j f₁).app P ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app P).hom.app
        ((j ≫ f₁) ⁻¹ᵁ W) (pullbackLocalSection j (pullbackLocalSection f₁ y)) =
      ((pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).hom.app P).app ((j ≫ f₁) ⁻¹ᵁ W)
        (((pullbackComp j f₁).hom.app P).app ((j ≫ f₁) ⁻¹ᵁ W)
          (pullbackLocalSection j (pullbackLocalSection f₁ y))) := rfl
    rw [h1, pullbackComp_hom_app_app_pullbackLocalSection]
    simp [pullbackCongr]
    rfl

  have hih : ∀ (P : X.Modules) (z : Γ((Scheme.Modules.pullback (j ≫ f₁)).obj P, (j ≫ f₁) ⁻¹ᵁ W)),
      ((pullbackComp j f₁).app P ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app P).hom.app ((j ≫ f₁) ⁻¹ᵁ W)
        (((pullbackComp j f₁).app P ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app P).inv.app ((j ≫ f₁) ⁻¹ᵁ W) z)
        = z := fun P z =>
    congrArg (fun ψ => Scheme.Modules.Hom.app ψ ((j ≫ f₁) ⁻¹ᵁ W) z)
      ((pullbackComp j f₁).app P ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app P).inv_hom_id

  have h2 : ∀ x : Γ(M, W),
      Scheme.Modules.Hom.app (M := (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj M)
          (N := (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj N)
          ((Scheme.Modules.pullback j).map E₁.hom) ((j ≫ f₁) ⁻¹ᵁ W)
          (pullbackLocalSection j (pullbackLocalSection f₁ x)) =
        ((pullbackComp j f₁).app N ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app N).inv.app ((j ≫ f₁) ⁻¹ᵁ W) (E₂.hom.app ((j ≫ f₁) ⁻¹ᵁ W)
          (((pullbackComp j f₁).app M ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app M).hom.app ((j ≫ f₁) ⁻¹ᵁ W) (pullbackLocalSection j (pullbackLocalSection f₁ x)))) := by
    intro x
    have h := congrArg (fun ψ : (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj M ⟶
        (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj N =>
      Scheme.Modules.Hom.app ψ ((j ≫ f₁) ⁻¹ᵁ W) (pullbackLocalSection j (pullbackLocalSection f₁ x)))
      (congrArg Iso.hom hc)
    simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
      CategoryTheory.comp_apply] at h
    exact h
  have h2' : ∀ x : Γ(N, W),
      Scheme.Modules.Hom.app (M := (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj N)
          (N := (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj M)
          ((Scheme.Modules.pullback j).map E₁.inv) ((j ≫ f₁) ⁻¹ᵁ W)
          (pullbackLocalSection j (pullbackLocalSection f₁ x)) =
        ((pullbackComp j f₁).app M ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app M).inv.app ((j ≫ f₁) ⁻¹ᵁ W) (E₂.inv.app ((j ≫ f₁) ⁻¹ᵁ W)
          (((pullbackComp j f₁).app N ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app N).hom.app ((j ≫ f₁) ⁻¹ᵁ W) (pullbackLocalSection j (pullbackLocalSection f₁ x)))) := by
    intro x
    have h := congrArg (fun ψ : (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj N ⟶
        (Scheme.Modules.pullback f₁ ⋙ Scheme.Modules.pullback j).obj M =>
      Scheme.Modules.Hom.app ψ ((j ≫ f₁) ⁻¹ᵁ W) (pullbackLocalSection j (pullbackLocalSection f₁ x)))
      (congrArg Iso.inv hc)
    simp only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, Scheme.Modules.Hom.comp_app,
      CategoryTheory.comp_apply] at h
    exact h
  constructor
  · intro x
    apply (pb (j ≫ f₁) N hW₂).injective
    simp only [pb_apply]
    rw [pullbackLocalSection_T (j ≫ f₁) E₂.hom hW₂,
      ← key N (T f₁ E₁.hom hW₁ x), pullbackLocalSection_T f₁ E₁.hom hW₁,
      pullbackLocalSection_app j E₁.hom (pullbackLocalSection f₁ x), ← key M x,
      ← hih N (E₂.hom.app ((j ≫ f₁) ⁻¹ᵁ W) (((pullbackComp j f₁).app M ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app M).hom.app ((j ≫ f₁) ⁻¹ᵁ W)
        (pullbackLocalSection j (pullbackLocalSection f₁ x))))]
    exact congrArg (fun z => ((pullbackComp j f₁).app N ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app N).hom.app ((j ≫ f₁) ⁻¹ᵁ W) z) (h2 x)
  · intro x
    apply (pb (j ≫ f₁) M hW₂).injective
    simp only [pb_apply]
    rw [pullbackLocalSection_T (j ≫ f₁) E₂.inv hW₂,
      ← key M (T f₁ E₁.inv hW₁ x), pullbackLocalSection_T f₁ E₁.inv hW₁,
      pullbackLocalSection_app j E₁.inv (pullbackLocalSection f₁ x), ← key N x,
      ← hih M (E₂.inv.app ((j ≫ f₁) ⁻¹ᵁ W) (((pullbackComp j f₁).app N ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app N).hom.app ((j ≫ f₁) ⁻¹ᵁ W)
        (pullbackLocalSection j (pullbackLocalSection f₁ x))))]
    exact congrArg (fun z => ((pullbackComp j f₁).app M ≪≫ (pullbackCongr (rfl : j ≫ f₁ = j ≫ f₁)).app M).hom.app ((j ≫ f₁) ⁻¹ᵁ W) z) (h2' x)

section cover

/--
@isnad1 id=le.1h3v.s6.b2ff3a4be01d from=translated src=- shape=0c81daa7 vocab=a1bad4a9
-/
lemma le_opensRange {O W : X.Opens} (hW : W ≤ O) : W ≤ O.ι.opensRange := by
  rwa [Scheme.Opens.opensRange_ι]

variable {M N : X.Modules} {ι : Type v} (U : ι → X.Opens)
  (hB : ∀ i j, U i ⊓ U j ≤ ⨆ (k : {k : ι // U k ≤ U i ⊓ U j}), U k.1)
  (Φ : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶ (Scheme.Modules.pullback (U i).ι).obj N)
  (hn : ∀ (i j : ι) (h : U j ≤ U i) (W : X.Opens) (hW : W ≤ U j) (x : Γ(M, W)),
    T (U i).ι (Φ i) (le_opensRange (hW.trans h)) x = T (U j).ι (Φ j) (le_opensRange hW) x)

include hB hn in

/--
@isnad1 id=eq.4h10v.s10.0a102de13d04 from=translated src=- shape=3ac6df38 vocab=e994e846
-/
lemma T_indep {i j : ι} {W : X.Opens} (hWi : W ≤ U i) (hWj : W ≤ U j) (x : Γ(M, W)) :
    T (U i).ι (Φ i) (le_opensRange hWi) x = T (U j).ι (Φ j) (le_opensRange hWj) x := by
  refine sections_eq_of_cover N W (fun k : {k : ι // U k ≤ U i ⊓ U j} => W ⊓ U k.1)
    (fun k => inf_le_left) ?_ _ _ ?_
  · intro z hz
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hB i j ⟨hWi hz, hWj hz⟩)
    exact Opens.mem_iSup.mpr ⟨k, ⟨hz, hk⟩⟩
  · intro k
    rw [T_restrict, T_restrict]
    exact (hn i k.1 (k.2.trans inf_le_left) (W ⊓ U k.1) inf_le_right _).trans
      (hn j k.1 (k.2.trans inf_le_right) (W ⊓ U k.1) inf_le_right _).symm

def fam (W : X.Opens) (hW : ∃ i, W ≤ U i) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) :=
  Tlin (U hW.choose).ι (Φ hW.choose) (le_opensRange hW.choose_spec)

/--
@isnad1 id=eq.1h8v.s12.c2c96f5e16e8 from=translated src=- shape=5895b8c9 vocab=4eb5d1a7
-/
lemma fam_apply (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)) :
    fam U Φ W hW x = T (U hW.choose).ι (Φ hW.choose) (le_opensRange hW.choose_spec) x := rfl

include hB hn in
/--
@isnad1 id=eq.4h9v.s12.d3700840926a from=translated src=- shape=42b1fd14 vocab=4dc4d61c
-/
lemma fam_eq {i : ι} (W : X.Opens) (hW : ∃ i, W ≤ U i) (hWi : W ≤ U i) (x : Γ(M, W)) :
    fam U Φ W hW x = T (U i).ι (Φ i) (le_opensRange hWi) x := by
  rw [fam_apply]; exact T_indep U hB Φ hn hW.choose_spec hWi x

include hB hn in
/--
@isnad1 id=eq.4h9v.s13.46cc7163bfe5 from=translated src=- shape=461b7f68 vocab=db143d98
-/
lemma fam_restrict (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : Γ(M, W)) :
    N.presheaf.map (homOfLE h).op (fam U Φ W hW x) =
      fam U Φ W' (hW.imp fun _ hi => h.trans hi) (M.presheaf.map (homOfLE h).op x) := by
  rw [fam_apply, fam_apply, T_restrict]
  exact T_indep U hB Φ hn (h.trans hW.choose_spec) (hW.imp fun _ hi => h.trans hi).choose_spec _

end cover

end AlgebraicGeometry.Scheme.Modules.IsoGlueAux
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.IsoGlueAux
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry.Scheme
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules.IsoGlueAux in
/--
@isnad1 id=existsun.3h6v.s11.944e61463f03 from=translated src=- shape=0d36a755 vocab=a367469c
-/
theorem solution
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hB : ∀ i j, U i ⊓ U j ≤ ⨆ (k : {k : ι // U k ≤ U i ⊓ U j}), U k.1)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ (Scheme.Modules.pullback (U i).ι).obj N)
    (he : ∀ (i j : ι) (h : U j ≤ U i),
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso (e i) =
        ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M) ≪≫
          e j ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app N ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app N).symm) :
    ∃! f : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).mapIso f = e i := by

  have hn_hom : ∀ (i j : ι) (h : U j ≤ U i) (W : X.Opens) (hW : W ≤ U j) (x : Γ(M, W)),
      T (U i).ι (e i).hom (le_opensRange (hW.trans h)) x = T (U j).ι (e j).hom (le_opensRange hW) x := by
    intro i j h W hW x
    exact (T_nest (U i).ι (U j).ι (X.homOfLE h) (X.homOfLE_ι h) (e i) (e j) (he i j h)
      (le_opensRange (hW.trans h)) (le_opensRange hW)).1 x
  have hn_inv : ∀ (i j : ι) (h : U j ≤ U i) (W : X.Opens) (hW : W ≤ U j) (x : Γ(N, W)),
      T (U i).ι (e i).inv (le_opensRange (hW.trans h)) x = T (U j).ι (e j).inv (le_opensRange hW) x := by
    intro i j h W hW x
    exact (T_nest (U i).ι (U j).ι (X.homOfLE h) (X.homOfLE_ι h) (e i) (e j) (he i j h)
      (le_opensRange (hW.trans h)) (le_opensRange hW)).2 x

  obtain ⟨F, hF, hFu⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top M N U hU
    (fam U (fun i => (e i).hom)) (fam_restrict U hB (fun i => (e i).hom) hn_hom)
  obtain ⟨G, hG, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top N M U hU
    (fam U (fun i => (e i).inv)) (fam_restrict U hB (fun i => (e i).inv) hn_inv)

  have hid : ∀ (P : X.Modules) (a : P ⟶ P),
      (∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(P, W)), a.app W x = x) → a = 𝟙 P := by
    intro P a ha
    obtain ⟨I, -, hIu⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top P P U hU
      (fun W _ => LinearMap.id) (fun W W' hW h x => rfl)
    exact (hIu a (fun W hW x => ha W hW x)).trans (hIu (𝟙 P) (fun W hW x => rfl)).symm
  have hFG : F ≫ G = 𝟙 M := hid M (F ≫ G) (fun W hW x => by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hF W hW, hG W hW, fam_apply, fam_apply,
      ← T_comp, Iso.hom_inv_id, T_id])
  have hGF : G ≫ F = 𝟙 N := hid N (G ≫ F) (fun W hW x => by
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hG W hW, hF W hW, fam_apply, fam_apply,
      ← T_comp, Iso.inv_hom_id, T_id])
  refine ⟨⟨F, G, hFG, hGF⟩, ?_, ?_⟩
  ·
    intro i
    apply Iso.ext
    show (Scheme.Modules.pullback (U i).ι).map F = (e i).hom
    apply Scheme.Modules.pullback_hom_ext
    intro W s
    rw [← Scheme.Modules.pullbackLocalSection_app]
    have hle : W ⊓ U i ≤ W := inf_le_left
    have heq : (U i).ι ⁻¹ᵁ (W ⊓ U i) = (U i).ι ⁻¹ᵁ W := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    apply (map_bijective_of_eq ((Scheme.Modules.pullback (U i).ι).obj N) heq
      (homOfLE (show (U i).ι ⁻¹ᵁ (W ⊓ U i) ≤ (U i).ι ⁻¹ᵁ W from fun _ hx => hle hx))).1
    rw [Scheme.Modules.map_homOfLE_pullbackLocalSection (U i).ι hle (F.app W s), app_naturality F,
      hF (W ⊓ U i) ⟨i, inf_le_right⟩,
      fam_eq U hB (fun i => (e i).hom) hn_hom (W ⊓ U i) ⟨i, inf_le_right⟩ inf_le_right,
      pullbackLocalSection_T, app_naturality (e i).hom,
      Scheme.Modules.map_homOfLE_pullbackLocalSection (U i).ι hle s]
  ·
    intro f' hf'
    apply Iso.ext
    apply hFu
    intro W hW x
    rw [fam_apply]
    symm
    apply (pb (U hW.choose).ι N (le_opensRange hW.choose_spec)).injective
    rw [pb_apply, pb_apply, pullbackLocalSection_T, Scheme.Modules.pullbackLocalSection_app (U hW.choose).ι f'.hom x,
      ← Functor.mapIso_hom, hf' hW.choose]
