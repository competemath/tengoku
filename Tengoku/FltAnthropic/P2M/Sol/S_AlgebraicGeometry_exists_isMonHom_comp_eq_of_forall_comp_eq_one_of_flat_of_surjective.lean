import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.CategoryTheory.MonoidalCategory open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace P2mIsogFactorDesc

variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]

/--
@isnad1 id=eq.2h9v.s9.f6dbb2cc13aa from=translated src=- shape=294205c4 vocab=0085f32a
-/
theorem comp_eq_comp_of_comp_eq_comp (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A.left) (h : g₁ ≫ f.left = g₂ ≫ f.left) :
    g₁ ≫ g.left = g₂ ≫ g.left := by
  have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
    rw [← Over.w f, reassoc_of% h]
  let T : Over S := Over.mk (g₁ ≫ A.hom)
  let a₁ : T ⟶ A := Over.homMk g₁ rfl
  let a₂ : T ⟶ A := Over.homMk g₂ hw
  have hf : a₁ ≫ f = a₂ ≫ f := Over.OverMorphism.ext (by simpa [a₁, a₂] using h)
  have h1 : (a₁⁻¹ * a₂) ≫ f = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hf, inv_mul_cancel]
  have h2 := hker T _ h1
  rw [MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one] at h2
  have := congrArg CommaMorphism.left h2
  simpa [a₁, a₂] using this

noncomputable def descLeft (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) : B.left ⟶ C.left :=
  EffectiveEpi.desc f.left g.left (fun g₁ g₂ h => comp_eq_comp_of_comp_eq_comp f g hker g₁ g₂ h)

/--
@isnad1 id=eq.1h6v.s9.0ac7c36f3a4b from=translated src=- shape=72407891 vocab=b4d6c4b0
-/
theorem fac_left (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    f.left ≫ descLeft f g hker = g.left :=
  EffectiveEpi.fac _ _ _

end P2mIsogFactorDesc
