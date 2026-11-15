import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

section

variable {L : Y.Modules} {U : Y.Opens}

def pullbackLocalSection (s : Γ(L, U)) : Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U) :=
  ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s

/--
@isnad1 id=eq.0h6v.s11.fb51e4ed2667 from=translated src=- shape=8fe5fc0e vocab=52a30dcf
-/
lemma pullbackLocalSection_def (s : Γ(L, U)) :
    pullbackLocalSection φ s = ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s := rfl

/--
@isnad1 id=eq.0h7v.s11.42986c5e0f23 from=translated src=- shape=36fbd0e4 vocab=4dff688d
-/
@[simp] lemma pullbackLocalSection_add (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s + s') = pullbackLocalSection φ s + pullbackLocalSection φ s' :=
  map_add (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

/--
@isnad1 id=eq.0h5v.s11.97063217b2e5 from=translated src=- shape=ba6f5e2d vocab=e8c50f9c
-/
@[simp] lemma pullbackLocalSection_zero : pullbackLocalSection φ (0 : Γ(L, U)) = 0 :=
  map_zero (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom

/--
@isnad1 id=eq.0h6v.s11.3e4936766503 from=translated src=- shape=cb75733d vocab=e236ea9d
-/
@[simp] lemma pullbackLocalSection_neg (s : Γ(L, U)) : pullbackLocalSection φ (-s) = -pullbackLocalSection φ s :=
  map_neg (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s

/--
@isnad1 id=eq.0h7v.s11.ca953affb677 from=translated src=- shape=36fbd0e4 vocab=6df81733
-/
@[simp] lemma pullbackLocalSection_sub (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s - s') = pullbackLocalSection φ s - pullbackLocalSection φ s' :=
  map_sub (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

/--
@isnad1 id=eq.0h8v.s10.e79e30aac206 from=translated src=- shape=db97ce78 vocab=e2875398
-/
lemma pullbackLocalSection_sum {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) :
    pullbackLocalSection φ (∑ i ∈ S, s i) = ∑ i ∈ S, pullbackLocalSection φ (s i) :=
  map_sum (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s S

/--
@isnad1 id=eq.0h7v.s14.5e4025faeada from=translated src=- shape=5c935f4b vocab=9475b17f
-/
lemma pullbackLocalSection_smul (g : Γ(Y, U)) (s : Γ(L, U)) :
    pullbackLocalSection φ (g • s) = φ.app U g • pullbackLocalSection φ s := by
  rw [pullbackLocalSection_def, Scheme.Modules.Hom.app_smul]
  rfl

/--
@isnad1 id=eq.0h8v.s12.a63420079f35 from=translated src=- shape=274cdec5 vocab=6ed79f91
-/
lemma map_pullbackLocalSection {V : Y.Opens} (i : V ⟶ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map ((Opens.map φ.base).map i).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map i.op s) := by
  have h := (((Modules.pullbackPushforwardAdjunction φ).unit.app L).mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f :
    Γ(L, U) → Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ V))) h) s).symm

/--
@isnad1 id=eq.1h7v.s12.0f515dc1af2f from=translated src=- shape=2eef48a9 vocab=4a8b23b6
-/
lemma map_homOfLE_pullbackLocalSection {V : Y.Opens} (hVU : V ≤ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map
        (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hx => hVU hx)).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map (homOfLE hVU).op s) :=
  map_pullbackLocalSection φ (homOfLE hVU) s

/--
@isnad1 id=eq.0h8v.s12.c254ac65ba78 from=translated src=- shape=da354251 vocab=9b8a2bd2
-/
lemma pullbackLocalSection_app {L' : Y.Modules} (θ : L ⟶ L') (s : Γ(L, U)) :
    pullbackLocalSection φ (θ.app U s) = ((Modules.pullback φ).map θ).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((Modules.pullbackPushforwardAdjunction φ).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

/--
@isnad1 id=eq.0h8v.s12.8d4b88484d59 from=translated src=- shape=d204a838 vocab=aa1f96f1
-/
lemma app_pullbackLocalSection {N : X.Modules} (g : (Modules.pullback φ).obj L ⟶ N) (s : Γ(L, U)) :
    g.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N g).app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/--
@isnad1 id=eq.0h8v.s12.43f51b98c82a from=translated src=- shape=3341489a vocab=152a7d20
-/
lemma homEquiv_symm_app_pullbackLocalSection {N : X.Modules} (k : L ⟶ (Modules.pushforward φ).obj N)
    (s : Γ(L, U)) :
    (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).symm k).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (k.app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [app_pullbackLocalSection, Equiv.apply_symm_apply]

end

/--
@isnad1 id=eq.0h6v.s11.89b8364ddd43 from=translated src=- shape=8d13df84 vocab=a7ad30b7
-/
lemma counit_app_pullbackLocalSection {N : X.Modules} {U : Y.Opens} (n : Γ((Modules.pushforward φ).obj N, U)) :
    ((Modules.pullbackPushforwardAdjunction φ).counit.app N).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ n) =
      (n : Γ(N, φ ⁻¹ᵁ U)) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U n)
    ((Modules.pullbackPushforwardAdjunction φ).right_triangle_components N)
  simp only [Functor.id_obj, Functor.comp_obj, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  exact h

/--
@isnad1 id=eq.1h7v.s12.66b78c7bcdc1 from=translated src=- shape=5c1d0462 vocab=066e51b3
-/
theorem pullback_hom_ext {L : Y.Modules} {N : X.Modules} {g₁ g₂ : (Modules.pullback φ).obj L ⟶ N}
    (h : ∀ (U : Y.Opens) (s : Γ(L, U)),
      g₁.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) = g₂.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s)) :
    g₁ = g₂ := by
  apply ((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have h₁ := app_pullbackLocalSection φ g₁ s
  have h₂ := app_pullbackLocalSection φ g₂ s
  rw [h U s] at h₁
  exact h₁.symm.trans h₂

end AlgebraicGeometry.Scheme.Modules

end
