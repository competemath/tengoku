import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Frames of sheaves of modules (core, depending only on Mathlib)

`IsFrame`, the coordinate `coord`, the global/local trivializations `topTrivialization` /
`restrictIso` and their characterizing lemmas. This part does not depend on `IsLineBundle`, so that
the frames of the twisting sheaves on Proj (`WeightedProjCoordinateFormula`) can be built directly on
it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- Restriction of sections (shorthand for `M.presheaf.map`, definitionally equal).-/
abbrev res (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op x

/--
@isnad1 id=eq.2h6v.s8.d7b004fbccda from=translated src=- shape=a2ad4857 vocab=721ff3d9
-/
theorem res_res (M : X.Modules) {W'' W' W : X.Opens} (h' : W'' ≤ W') (h : W' ≤ W) (x : Γ(M, W)) :
    M.res h' (M.res h x) = M.res (h'.trans h) x := by
  unfold res
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]; rfl

/--
@isnad1 id=eq.0h4v.s8.03e2117db872 from=translated src=- shape=05e7af7b vocab=206cf7d0
-/
@[simp] theorem res_self (M : X.Modules) {W : X.Opens} (x : Γ(M, W)) : M.res le_rfl x = x := by
  unfold res
  have : (homOfLE (le_refl W)).op = 𝟙 (op W) := rfl
  rw [this, M.presheaf.map_id]; rfl

/-- Restriction commutes with scalar multiplication.
@isnad1 id=eq.1h6v.s13.a6dbcd01d88c from=translated src=- shape=36ba1779 vocab=c0335f8b
-/
theorem res_smul (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (x : Γ(M, W)) :
    M.res h (r • x) = X.presheaf.map (homOfLE h).op r • M.res h x :=
  Scheme.Modules.map_smul M (homOfLE h) r x

/-- A frame on `W`: `e ∈ Γ(M, W)` such that `r ↦ r • e|` is a bijection on every open inside `W`.-/
def IsFrame (M : X.Modules) (W : X.Opens) (e : Γ(M, W)) : Prop :=
  ∀ (W' : X.Opens) (h : W' ≤ W), Function.Bijective (fun r : Γ(X, W') => r • M.res h e)

namespace IsFrame

variable {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}

/-- The restriction of a frame to a smaller open is a frame.
@isnad1 id=isframe.2h5v.s7.6b47892e90ef from=translated src=- shape=d9911f95 vocab=2dcdf620
-/
theorem restrict (hf : IsFrame M W e) {W₁ : X.Opens} (h : W₁ ≤ W) : IsFrame M W₁ (M.res h e) := by
  intro W' h'
  rw [res_res]
  exact hf W' _

/-- Coordinates in a frame: `Γ(M, W') ≃ₗ Γ(X, W')`, with inverse `r ↦ r • e|_{W'}`.-/
def coordEquiv (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) : Γ(M, W') ≃ₗ[Γ(X, W')] Γ(X, W') :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W') Γ(M, W') (M.res h e)) (hf W' h)).symm

/-- The coordinate of a section `x` in the frame `e`.-/
def coord (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W')) : Γ(X, W') :=
  hf.coordEquiv h x

/--
@isnad1 id=eq.2h6v.s12.4f2c850d287b from=translated src=- shape=62250298 vocab=2ea35d49
-/
@[simp] theorem coord_smul_frame (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W')) :
    hf.coord h x • M.res h e = x :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W') Γ(M, W') (M.res h e)) (hf W' h)).apply_symm_apply x

/--
@isnad1 id=eq.3h7v.s12.1f668c85fc1c from=translated src=- shape=f3c5ddcf vocab=2ea35d49
-/
theorem coord_unique (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W')) (r : Γ(X, W'))
    (hr : r • M.res h e = x) : hf.coord h x = r :=
  (hf W' h).1 ((hf.coord_smul_frame h x).trans hr.symm)

/--
@isnad1 id=eq.2h7v.s12.c4d81d4e7815 from=translated src=- shape=63578d27 vocab=15ed6073
-/
@[simp] theorem coord_smul (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W')) (x : Γ(M, W')) :
    hf.coord h (r • x) = r * hf.coord h x :=
  (hf.coordEquiv h).map_smul r x

/--
@isnad1 id=eq.2h7v.s11.4636f11d9f0e from=translated src=- shape=2c1d07ee vocab=4bb11dcf
-/
@[simp] theorem coord_add (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x y : Γ(M, W')) :
    hf.coord h (x + y) = hf.coord h x + hf.coord h y :=
  (hf.coordEquiv h).map_add x y

/--
@isnad1 id=eq.2h5v.s10.08b8ac95d35f from=translated src=- shape=a4893fc0 vocab=ef013cf4
-/
@[simp] theorem coord_frame (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) :
    hf.coord h (M.res h e) = 1 :=
  hf.coord_unique h _ 1 (one_smul _ _)

/--
@isnad1 id=iff.2h6v.s11.50f90d0a8468 from=translated src=- shape=5ff0522d vocab=15c6b555
-/
theorem coord_eq_zero_iff (hf : IsFrame M W e) {W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W')) :
    hf.coord h x = 0 ↔ x = 0 :=
  (hf.coordEquiv h).map_eq_zero_iff

/-- Coordinates commute with restriction.
@isnad1 id=eq.3h7v.s10.64f91465eee6 from=translated src=- shape=b6cfa2fb vocab=547d08a8
-/
theorem coord_map (hf : IsFrame M W e) {W'' W' : X.Opens} (h' : W'' ≤ W') (h : W' ≤ W) (x : Γ(M, W')) :
    hf.coord (h'.trans h) (M.res h' x) = X.presheaf.map (homOfLE h').op (hf.coord h x) := by
  apply hf.coord_unique
  have hx := congrArg (M.res h') (hf.coord_smul_frame h x)
  rw [← hx, ← res_res M h' h e]
  exact (res_smul M h' (hf.coord h x) (M.res h e)).symm

/-- Two frames differ by a unit: `e' = u • e` with `u` a unit of `Γ(X, W)`.
@isnad1 id=ex.2h5v.s12.1db32acdd2bb from=translated src=- shape=c9bdf8e0 vocab=170f0d19
-/
theorem exists_unit (hf : IsFrame M W e) {e' : Γ(M, W)} (hf' : IsFrame M W e') :
    ∃ u : (Γ(X, W))ˣ, (u : Γ(X, W)) • e = e' := by
  have h1 := hf.coord_smul_frame le_rfl e'
  have h2 := hf'.coord_smul_frame le_rfl e
  rw [res_self] at h1 h2
  refine ⟨⟨hf.coord le_rfl e', hf'.coord le_rfl e, ?_, ?_⟩, h1⟩
  · have := (hf W le_rfl).1 (a₁ := hf.coord le_rfl e' * hf'.coord le_rfl e) (a₂ := 1) (by
      simp only [res_self]
      rw [mul_comm, mul_smul, h1, h2, one_smul])
    exact this
  · have := (hf' W le_rfl).1 (a₁ := hf'.coord le_rfl e * hf.coord le_rfl e') (a₂ := 1) (by
      simp only [res_self]
      rw [mul_comm, mul_smul, h2, h1, one_smul])
    exact this

end IsFrame

/-- The morphism `O_X ⟶ M` determined by a global section `s` (`1 ↦ s`).-/
def homOfSection (M : X.Modules) (s : Γ(M, ⊤)) : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm
    (PresheafOfModules.sectionsMk (fun U ↦ M.res (le_top : U.unop ≤ ⊤) s) (fun U W f ↦ by
      have h : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : W.unop ≤ ⊤)).op := rfl
      show M.presheaf.map f (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s) = _
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, h]))

/--
@isnad1 id=eq.0h4v.s16.42a0e7ca3fee from=translated src=- shape=9accc973 vocab=0fbd4ac9
-/
theorem homOfSection_app_one (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) :
    (homOfSection M s).val.app (op U) (1 : Γ(X, U)) = M.res (le_top : U ≤ ⊤) s := by
  have := SheafOfModules.unitHomEquiv_apply_coe M (homOfSection M s) (op U)
  rw [homOfSection, Equiv.apply_symm_apply] at this
  exact this.symm

/-- On every open, `r ↦ r • s|_U`.
@isnad1 id=eq.0h5v.s16.95f091547e99 from=translated src=- shape=9ecd167f vocab=4e899924
-/
theorem homOfSection_app (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    (homOfSection M s).val.app (op U) r = r • M.res (le_top : U ≤ ⊤) s := by
  rw [← homOfSection_app_one]
  have := ((homOfSection M s).val.app (op U)).hom.map_smul r (1 : Γ(X, U))
  refine Eq.trans ?_ this
  congr 1
  exact (mul_one r).symm

/-- A morphism of sheaves of modules that is bijective on every open is an isomorphism.
@isnad1 id=isiso.1h4v.s16.15538ce71bfd from=translated src=- shape=5d560408 vocab=ba9bbcde
-/
theorem isIso_of_bijective {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Bijective (f.val.app (op U))) : IsIso f := by
  have h1 : IsIso ((PresheafOfModules.toPresheaf _).map f.val) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h U.unop
  have h2 : IsIso f.val := isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have h3 : IsIso ((SheafOfModules.forget X.ringCatSheaf).map f) := h2
  have := (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).reflectsIsomorphisms
  exact isIso_of_reflects_iso f (SheafOfModules.forget X.ringCatSheaf)

/-- A global frame gives a global trivialization `O_X ≅ M`.-/
def IsFrame.topTrivialization {M : X.Modules} {e : Γ(M, ⊤)} (hf : IsFrame M ⊤ e) :
    SheafOfModules.unit X.ringCatSheaf ≅ M :=
  haveI : IsIso (homOfSection M e) := isIso_of_bijective _ fun U ↦ by
    have hfun : (fun r : Γ(X, U) ↦ (homOfSection M e).val.app (op U) r) =
        fun r : Γ(X, U) ↦ r • M.res (le_top : U ≤ ⊤) e := funext (homOfSection_app M e U)
    show Function.Bijective (fun r : Γ(X, U) ↦ (homOfSection M e).val.app (op U) r)
    rw [hfun]
    exact hf U le_top
  asIso (homOfSection M e)

/--
@isnad1 id=le.0h3v.s6.b35e11f2cf95 from=translated src=- shape=86fde1eb vocab=9e9c306d
-/
theorem image_ι_le (W : X.Opens) (O : W.toScheme.Opens) : W.ι ''ᵁ O ≤ W := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- Scalar multiplication and restriction on `M|_W`: on `O ⊆ W`, `r • (e|_⊤)|_O` is `r • e|_{W.ι ''ᵁ O}`
in `M`. All carrier conversions "sections of the restricted sheaf ↔ sections on the image open" are
collected in this lemma (for a variable `M`).
@isnad1 id=eq.0h6v.s14.2d95a529afba from=translated src=- shape=5f4686c3 vocab=6031b44a
-/
theorem restrict_smul_res (M : X.Modules) (W : X.Opens) (e : Γ(M, W)) (O : W.toScheme.Opens)
    (r : Γ(X, W.ι ''ᵁ O)) :
    ((show Γ(W.toScheme, O) from r) •
        (M.restrict W.ι).res (le_top : O ≤ ⊤)
          (show Γ(M.restrict W.ι, ⊤) from M.res (image_ι_le W ⊤) e) : Γ(M.restrict W.ι, O)) =
      (r • M.res (image_ι_le W O) e : Γ(M, W.ι ''ᵁ O)) := by
  have hs : ∀ y : Γ(M.restrict W.ι, O), (show Γ(W.toScheme, O) from r) • y =
      (((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) •
        (show Γ(M, W.ι ''ᵁ O) from y) : Γ(M, W.ι ''ᵁ O)) := fun _ ↦ rfl
  have hr : ((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) = r := by
    rw [Scheme.Opens.ι_appIso]; rfl
  rw [hs, hr]
  congr 1
  have h1 : W.ι ''ᵁ O ≤ W.ι ''ᵁ ⊤ := leOfHom (W.ι.opensFunctor.map (homOfLE (le_top : O ≤ ⊤)))
  show M.presheaf.map (W.ι.opensFunctor.map (homOfLE (le_top : O ≤ ⊤))).op
    (M.res (image_ι_le W ⊤) e) = _
  rw [show W.ι.opensFunctor.map (homOfLE (le_top : O ≤ ⊤)) = homOfLE h1 from Subsingleton.elim _ _]
  exact res_res M h1 _ e

/-- A frame on `W`, viewed as a global frame of `M|_W`.
@isnad1 id=isframe.1h4v.s11.99dbdda5c5a1 from=translated src=- shape=3f76f2f8 vocab=995352ea
-/
theorem IsFrame.restrict_top {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    IsFrame (M.restrict W.ι) ⊤
      (show Γ(M.restrict W.ι, ⊤) from M.res (image_ι_le W ⊤) e) := by
  intro O _
  have hb := hf (W.ι ''ᵁ O) (image_ι_le W O)
  have hfun := restrict_smul_res M W e O
  refine ⟨fun r r' hrr ↦ hb.1 ?_, fun y ↦ ?_⟩
  · exact (hfun r).symm.trans (Eq.trans hrr (hfun r'))
  · obtain ⟨r, hr⟩ := hb.2 y
    exact ⟨r, (hfun r).trans hr⟩

/-- The local trivialization `M|_W ≅ O_W` given by a frame (inverse `1 ↦ e`). The carrier conversion
is hidden in this definition (for a variable `M`); instantiating it at a concrete sheaf shows no
conversion in the type.-/
def IsFrame.restrictIso {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  hf.restrict_top.topTrivialization.symm

/-- The inverse: `r ↦ r • e|` (the scalar transported to `X` through `appIso`).
@isnad1 id=eq.1h6v.s16.8a8aad74d77b from=translated src=- shape=1259a660 vocab=064b585d
-/
theorem IsFrame.restrictIso_inv_app {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) (r : Γ(W.toScheme, V)) :
    hf.restrictIso.inv.val.app (op V) r =
      (((W.ι.appIso V).inv r : Γ(X, W.ι ''ᵁ V)) • M.res (image_ι_le W V) e : Γ(M, W.ι ''ᵁ V)) := by
  have hr : ((W.ι.appIso V).inv r : Γ(X, W.ι ''ᵁ V)) = (show Γ(X, W.ι ''ᵁ V) from r) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  rw [hr]
  exact (homOfSection_app _ _ V r).trans (restrict_smul_res M W e V (show Γ(X, W.ι ''ᵁ V) from r))

/--
@isnad1 id=eq.1h6v.s17.ae9a897bd7a0 from=translated src=- shape=94c324a5 vocab=e7c5199a
-/
theorem IsFrame.restrictIso_inv_hom_apply {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) (s : Γ(M.restrict W.ι, V)) :
    hf.restrictIso.inv.val.app (op V) (hf.restrictIso.hom.val.app (op V) s) = s :=
  congrArg (fun φ : M.restrict W.ι ⟶ M.restrict W.ι ↦ φ.val.app (op V) s) hf.restrictIso.hom_inv_id

/--
@isnad1 id=eq.1h6v.s17.3c8fc4cd0044 from=translated src=- shape=6b39d4f8 vocab=5e39a6a2
-/
theorem IsFrame.restrictIso_hom_inv_apply {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) (r : Γ(W.toScheme, V)) :
    hf.restrictIso.hom.val.app (op V) (hf.restrictIso.inv.val.app (op V) r) = r :=
  congrArg (fun φ : SheafOfModules.unit W.toScheme.ringCatSheaf ⟶ _ ↦ φ.val.app (op V) r)
    hf.restrictIso.inv_hom_id

/-- The forward direction: take the coordinate in the frame (transported back to `W` through
`appIso`).
@isnad1 id=eq.1h6v.s16.0cd4788c36d8 from=translated src=- shape=25daad90 vocab=d74c8f15
-/
theorem IsFrame.restrictIso_hom_app {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) (s : Γ(M.restrict W.ι, V)) :
    hf.restrictIso.hom.val.app (op V) s =
      (W.ι.appIso V).hom (hf.coord (image_ι_le W V) (show Γ(M, W.ι ''ᵁ V) from s)) := by
  have h2 : hf.restrictIso.inv.val.app (op V)
      ((W.ι.appIso V).hom (hf.coord (image_ι_le W V) (show Γ(M, W.ι ''ᵁ V) from s))) = s := by
    refine (hf.restrictIso_inv_app V _).trans ?_
    rw [Iso.hom_inv_id_apply]
    exact hf.coord_smul_frame (image_ι_le W V) _
  exact (congrArg (hf.restrictIso.hom.val.app (op V)) h2).symm.trans
    (hf.restrictIso_hom_inv_apply V _)

/-- `restrictIso_hom_app` in the `Hom.app` + `restrictAppIso` spelling: consumers usually write sections
as `(M.restrictAppIso W.ι V).inv t` and morphisms as `.hom.app V`. For a variable `M` the conversion
between the spellings is free, so it is done here and instantiated directly at concrete sheaves.
@isnad1 id=eq.1h6v.s12.66c87bfb7c6b from=translated src=- shape=6fc24e57 vocab=192b6787
-/
theorem IsFrame.restrictIso_hom_app_restrictAppIso_inv {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) (t : Γ(M, W.ι ''ᵁ V)) :
    hf.restrictIso.hom.app V ((M.restrictAppIso W.ι V).inv t) =
      (W.ι.appIso V).hom (hf.coord (image_ι_le W V) t) :=
  hf.restrictIso_hom_app V _

/-- The forward direction sends the frame itself to `1`.
@isnad1 id=eq.1h5v.s16.68b672f62f24 from=translated src=- shape=73b7646b vocab=d8ae62ee
-/
theorem IsFrame.restrictIso_hom_app_frame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (V : W.toScheme.Opens) :
    hf.restrictIso.hom.val.app (op V)
      (show Γ(M.restrict W.ι, V) from M.res (image_ι_le W V) e) = (1 : Γ(W.toScheme, V)) := by
  rw [hf.restrictIso_hom_app]
  have : hf.coord (image_ι_le W V) (M.res (image_ι_le W V) e) = 1 := hf.coord_frame _
  exact (congrArg (W.ι.appIso V).hom this).trans (map_one _)

end AlgebraicGeometry.Scheme.Modules

end
