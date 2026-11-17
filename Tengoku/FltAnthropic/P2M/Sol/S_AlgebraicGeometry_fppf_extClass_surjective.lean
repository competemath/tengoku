import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_fppf_extClass_surjective.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_fppf_extClass_surjective.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_fppf_extClass_surjective

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Abelian open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

section GeneralAbelian

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]

namespace CategoryTheory export _root_.CategoryTheory (Epi Category ShortComplex.Exact ShortComplex.mk Abelian Abelian.Ext Limits.zero_comp ShortComplex.Exact.lift_f mono_of_mono_fac constantSheaf Injective ShortComplex.exact_of_g_is_cokernel Limits.comp_zero Injective.ι Sheaf HasExt Category.id_comp ShortComplex ShortComplex.ShortExact EnoughInjectives Mono ShortComplex.exact_of_f_is_kernel ShortComplex.ShortExact.extClass_naturality Injective.under Category.assoc) namespace Abelian export _root_.CategoryTheory.Abelian (Ext.homEquiv₀ Ext Ext.comp_mk₀_id Ext.eq_zero_of_injective Ext.mk₀ mk Ext.mk₀_homEquiv₀_apply Ext.covariant_sequence_exact₁) namespace Ext export _root_.CategoryTheory.Abelian.Ext (homEquiv₀ zero_comp comp comp_mk₀_id eq_zero_of_injective comp_zero mk₀ mk₀_homEquiv₀_apply covariant_sequence_exact₁) end CategoryTheory.Abelian.Ext
open scoped _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext in

theorem CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq
    {X Y : C} (e : Ext.{w} X Y 1) :
    ∃ (E : C) (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact), hS.extClass = e := by

  let S : ShortComplex C := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
    (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

  have he0 : e.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective (I := Injective.under Y) _

  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS e he0 (zero_add 1)
  let φ : X ⟶ S.X₃ := Ext.homEquiv₀ x₃
  haveI : Epi S.g := hS.epi_g
  haveI : Mono S.f := hS.mono_f
  have hpc : pullback.fst S.g φ ≫ S.g = pullback.snd S.g φ ≫ φ := pullback.condition

  let ι' : Y ⟶ pullback S.g φ := pullback.lift S.f 0 (by simp)
  have hι'fst : ι' ≫ pullback.fst S.g φ = S.f := pullback.lift_fst _ _ _
  have hι'snd : ι' ≫ pullback.snd S.g φ = 0 := pullback.lift_snd _ _ _
  haveI : Mono ι' := mono_of_mono_fac hι'fst

  let S' : ShortComplex C := ShortComplex.mk ι' (pullback.snd S.g φ) hι'snd
  have hS' : S'.ShortExact := by
    refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_ }
    refine KernelFork.IsLimit.ofι' ι' hι'snd (fun {A} k hk => ⟨?_, ?_⟩)
    · exact hS.exact.lift (k ≫ pullback.fst S.g φ)
        (by rw [Category.assoc, hpc, reassoc_of% hk, Limits.zero_comp])
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hι'fst, ShortComplex.Exact.lift_f]
      · simp only [Category.assoc, hι'snd, Limits.comp_zero, hk]

  let ψ : S' ⟶ S :=
    { τ₁ := 𝟙 Y
      τ₂ := pullback.fst S.g φ
      τ₃ := φ
      comm₁₂ := by dsimp only [S', S]; rw [Category.id_comp, hι'fst]
      comm₂₃ := hpc }
  refine ⟨pullback S.g φ, ι', pullback.snd S.g φ, hι'snd, hS', ?_⟩
  have hnat := ShortComplex.ShortExact.extClass_naturality hS' hS ψ
  rw [show ψ.τ₁ = 𝟙 Y from rfl, Ext.comp_mk₀_id] at hnat
  rw [hnat, show ψ.τ₃ = φ from rfl, show Ext.mk₀ φ = x₃ from Ext.mk₀_homEquiv₀_apply x₃, hx₃]

end GeneralAbelian

theorem solution
    (F : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (e : CategoryTheory.Abelian.Ext
      ((CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ))) F 1) :
    ∃ (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
      (f : F ⟶ E)
      (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)))
      (w : f ≫ g = 0)
      (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact),
      hS.extClass = e :=
  CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq e
