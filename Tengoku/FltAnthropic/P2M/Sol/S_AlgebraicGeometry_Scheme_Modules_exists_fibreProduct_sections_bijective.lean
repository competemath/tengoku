import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.lean`: wrote out 9 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Opposite open _root_.TopologicalSpace

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (forget Γ Modules Opens evaluation)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (toPresheaf pullback presheaf)
namespace FibreProductSections
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

noncomputable def evalForget (U : X.Opens) : TopCat.Presheaf Ab X ⥤ Type u :=
  (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget Ab

noncomputable scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (evalForget (X := X) U) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U) ⋙ CategoryTheory.forget Ab.{u}))

noncomputable def sectionsFunctorAt (U : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ evalForget U

noncomputable scoped instance (U : X.Opens) :
    PreservesLimitsOfShape WalkingCospan (sectionsFunctorAt (X := X) U) := by
  unfold sectionsFunctorAt; infer_instance

end AlgebraicGeometry.Scheme.Modules.FibreProductSections
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules.FibreProductSections
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry

open CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FibreProductSections in

theorem solution
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by
  have key : ∀ U : X.Opens, ∃ e : (Γ(Limits.pullback a b, U) : Type u) ≃
      Types.PullbackObj ((sectionsFunctorAt U).map a) ((sectionsFunctorAt U).map b),
      ∀ s, (e s).1.1 = (pullback.fst a b).app U s ∧ (e s).1.2 = (pullback.snd a b).app U s := by
    intro U
    have hc := isLimitPullbackConeMapOfIsLimit (sectionsFunctorAt U) pullback.condition
      (pullbackIsPullback a b)
    exact ⟨PullbackCone.IsLimit.equivPullbackObj hc, fun s =>
      ⟨PullbackCone.IsLimit.equivPullbackObj_apply_fst hc s,
       PullbackCone.IsLimit.equivPullbackObj_apply_snd hc s⟩⟩
  refine ⟨Limits.pullback a b, pullback.fst a b, pullback.snd a b, pullback.condition, ?_, ?_⟩
  · intro U s t hst
    obtain ⟨e, he⟩ := key U
    apply e.injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [(he s).1, (he t).1]; exact congrArg Prod.fst hst
    · rw [(he s).2, (he t).2]; exact congrArg Prod.snd hst
  · intro U s₀ s₁ h
    obtain ⟨e, he⟩ := key U
    refine ⟨e.symm ⟨(s₀, s₁), h⟩, ?_, ?_⟩
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).2
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
