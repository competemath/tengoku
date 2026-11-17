import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.Place.eq_of_comap_eq_of_forall_mem_nonunits_iff
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (P : Place κ F) (W₁ W₂ : Place κ' F')
    (h₁ : W₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (h₂ : W₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hc : ∀ x ∈ Subring.closure
        ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F')),
      x ∈ W₁.toValuationSubring.nonunits ↔ x ∈ W₂.toValuationSubring.nonunits) :
    W₁ = W₂ := by exact @_root_.P2MW.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff.solution κ _ F _ _ κ' _ _ _ _ F' _ _ _ _ _ _ _ hgen P W₁ W₂ h₁ h₂ hc
