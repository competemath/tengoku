import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Hom.congr_app Scheme.IdealSheafData.ideal_bot Scheme.IdealSheafData.ideal_mul Scheme.Hom.le_ker_comp Scheme.Hom Scheme Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion IsReduced Scheme.Hom.comp_app IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.IdealSheafData.support_mul IsAffineOpen Scheme.Hom.ker_apply Scheme.Hom.comp_preimage Scheme.IdealSheafData.support_eq_top_iff Scheme.IdealSheafData.ideal_sup Scheme.IdealSheafData)
namespace TwoClosedAux
open _root_.AlgebraicGeometry

variable {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]

/--
@isnad1 id=eq.0h5v.s6.906b3c36be74 from=translated src=- shape=c7b32432 vocab=8f53ee21
-/
theorem ker_pullback_fst_comp :
    (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  apply le_antisymm
  ·
    set J : X.IdealSheafData := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have h₂ : i₂.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let z : J.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ J.subschemeι h₁) (IsClosedImmersion.lift i₂ J.subschemeι h₂)
        (by rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac])
    have hz : z ≫ (pullback.fst i₁ i₂ ≫ i₁) = J.subschemeι := by
      rw [← Category.assoc, pullback.lift_fst, IsClosedImmersion.lift_fac]
    calc (pullback.fst i₁ i₂ ≫ i₁).ker ≤ (z ≫ (pullback.fst i₁ i₂ ≫ i₁)).ker := Scheme.Hom.le_ker_comp _ _
      _ = J := by rw [hz, Scheme.IdealSheafData.ker_subschemeι]
  · refine sup_le (Scheme.Hom.le_ker_comp _ _) ?_
    rw [pullback.condition]
    exact Scheme.Hom.le_ker_comp _ _

/--
@isnad1 id=eq.1h5v.s8.5132744caad4 from=translated src=- shape=9362afa6 vocab=bf385a33
-/
theorem ker_mul_ker_eq_bot [IsReduced X] (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    i₁.ker * i₂.ker = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_mul, eq_top_iff]
  rintro x -
  rcases (Set.eq_univ_iff_forall.mp hcover x) with h | h
  · exact Or.inl (i₁.range_subset_ker_support h)
  · exact Or.inr (i₂.range_subset_ker_support h)

end AlgebraicGeometry.TwoClosedAux

open AlgebraicGeometry.TwoClosedAux in
/--
@isnad1 id=and.2h6v.s14.51e333af1f65 from=translated src=- shape=9830865f vocab=ad72f1e4
-/
theorem solution
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by

  have hk₁ : RingHom.ker (i₁.app U).hom = i₁.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₁ ⟨U, hU⟩).symm
  have hk₂ : RingHom.ker (i₂.app U).hom = i₂.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₂ ⟨U, hU⟩).symm
  have hkπ : RingHom.ker ((pullback.fst i₁ i₂ ≫ i₁).app U).hom = i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
    rw [← Scheme.Hom.ker_apply _ ⟨U, hU⟩, ker_pullback_fst_comp, Scheme.IdealSheafData.ideal_sup]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro f g hfg
    simp only [Prod.mk.injEq] at hfg
    rw [← sub_eq_zero]
    have hmem₁ : f - g ∈ i₁.ker.ideal ⟨U, hU⟩ := by rw [← hk₁, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hfg.1
    have hmem₂ : f - g ∈ i₂.ker.ideal ⟨U, hU⟩ := by rw [← hk₂, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hfg.2
    have hsq : (f - g) * (f - g) ∈ (i₁.ker * i₂.ker).ideal ⟨U, hU⟩ := by
      rw [Scheme.IdealSheafData.ideal_mul]; exact Ideal.mul_mem_mul hmem₁ hmem₂
    rw [ker_mul_ker_eq_bot i₁ i₂ hcover, Scheme.IdealSheafData.ideal_bot] at hsq
    have h0 : (f - g) * (f - g) = 0 := hsq
    exact IsReduced.eq_zero _ ⟨2, by rw [pow_two, h0]⟩
  · intro g₁ g₂ h
    obtain ⟨a₁, rfl⟩ := i₁.app_surjective U hU g₁
    obtain ⟨a₂, rfl⟩ := i₂.app_surjective U hU g₂

    have key : ∀ a : Γ(X, U), (pullback i₁ i₂).presheaf.map
        (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
        ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) a)) = (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) ((i₂.app U) a) := by
      intro a
      change ((i₁.app U ≫ (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U)) ≫ (pullback i₁ i₂).presheaf.map (eqToHom _).op) a =
        (i₂.app U ≫ (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U)) a
      rw [← Scheme.Hom.comp_app, ← Scheme.Hom.comp_app,
        Scheme.Hom.congr_app (pullback.condition (f := i₁) (g := i₂)).symm U]
      rfl
    have hF : (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) a₁) = (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) a₂) := by
      rw [← key a₂] at h
      haveI : IsIso ((pullback i₁ i₂).presheaf.map (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) =
          (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op) := by
        rw [eqToHom_op, eqToHom_map]; infer_instance
      exact (ConcreteCategory.bijective_of_isIso _).1 h
    have hπ : ((pullback.fst i₁ i₂ ≫ i₁).app U) a₁ = ((pullback.fst i₁ i₂ ≫ i₁).app U) a₂ := by
      rw [Scheme.Hom.comp_app]
      exact hF
    have hdiff : a₁ - a₂ ∈ i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
      rw [← hkπ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hπ
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.mp hdiff
    refine ⟨a₁ - u₁, ?_, ?_⟩
    · rw [map_sub, sub_eq_self]
      exact (RingHom.mem_ker.mp (hk₁ ▸ hu₁ : u₁ ∈ RingHom.ker (i₁.app U).hom))
    · have : a₁ - u₁ = a₂ + u₂ := by linear_combination -hu
      rw [this, map_add, add_eq_left]
      exact (RingHom.mem_ker.mp (hk₂ ▸ hu₂ : u₂ ∈ RingHom.ker (i₂.app U).hom))
