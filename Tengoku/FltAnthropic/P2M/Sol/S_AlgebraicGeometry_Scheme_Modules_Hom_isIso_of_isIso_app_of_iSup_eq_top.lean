import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.CategoryTheory.Sites.LocallyBijective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=isiso.2h6v.s8.3789002c51e8 from=translated src=- shape=5c5b726a vocab=ec9fac83
-/
theorem solution {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by

  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial)

  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  haveI : (Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{u}) :=
    inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    ·
      refine ⟨fun {W} x y hxy p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    ·
      refine ⟨fun {W} s p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      exact ⟨t, ht⟩

  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  have : IsIso (ψ.hom.app (Opposite.op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
    infer_instance
  exact this
