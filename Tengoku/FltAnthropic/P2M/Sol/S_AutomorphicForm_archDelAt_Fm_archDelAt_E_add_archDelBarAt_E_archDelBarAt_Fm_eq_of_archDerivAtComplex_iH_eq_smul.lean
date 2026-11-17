import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

/--
@isnad1 id=eq.3h4v.s9.7d722099c32f from=translated src=- shape=355197c1 vocab=53843599
-/
theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .Fm (archDelAt hw .E φ) + archDelBarAt hw .E (archDelBarAt hw .Fm φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 + Complex.I * m / 2) • φ := by

  obtain ⟨-, -, hEF, -, -, hEiF, hiEF, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ

  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d

  have linSub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u - c • v)) = a • (archDerivAtComplex hw X u - c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, sub_eq_add_neg, ← neg_smul, archDerivAtComplex_add hu (hv.smul _),
      archDerivAtComplex_smul, neg_smul, ← sub_eq_add_neg]
  have linAdd : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u + c • v)) = a • (archDerivAtComplex hw X u + c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul]

  simp only [archDelAt, archDelBarAt, archCasimirAtComplex, archCasimirBarAtComplex, ArchDir.toComplex,
    ArchDir.toComplexI, linSub _ _ _ (hs _) (hs _), linAdd _ _ _ (hs _) (hs _)]

  have hHH : archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) = m • (m • φ) := by
    rw [hm, archDerivAtComplex_smul, hm]
  rw [hHH]
  rw [hm] at hEiF hiEF

  funext g
  have h3 := congrFun hEF g
  have h6 := congrFun hEiF g
  have h7 := congrFun hiEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h6 h7 h12 ⊢
  linear_combination (1 / 4 : ℂ) * h3 - (1 / 4 : ℂ) * h12 - (Complex.I / 4) * h6 - (Complex.I / 4) * h7
    + ((1 / 4 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g
        - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) g) + m ^ 2 * φ g / 8) * Complex.I_sq
