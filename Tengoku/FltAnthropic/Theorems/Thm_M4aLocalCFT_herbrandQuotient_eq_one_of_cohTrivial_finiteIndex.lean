import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.GroupTheory.Index
import Tengoku.FltAnthropic.P2M.Sol.S_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.6h4v.s10.54debb404b6c from=translated src=- shape=8bb69444 vocab=28d1688e
-/
theorem M4aLocalCFT.herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
    {M : Type*} [CommGroup M] (D N : M →* M)
    (hDN : ∀ x, D (N x) = 1) (hND : ∀ x, N (D x) = 1)
    (V : Subgroup M) [V.FiniteIndex]
    (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V)
    (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v)
    (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) :
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) =
      Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) ∧
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) ≠ 0 := by exact @_root_.P2MW.S_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex.solution M _ D N hDN hND V _ hDV hNV h0 h1
