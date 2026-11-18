import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
/--
@isnad1 id=le.1h3v.s12.107f7e391b18 from=translated src=- shape=49440925 vocab=e346a7c8
-/
theorem Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
    {G : Fin 2 → Type*} [∀ i, Group (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex] (K : Type) [Field K]
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) :
    Module.finrank K (Additive H →+ K)
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 0)).range))
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 1)).range))
      ≤ H.index + 1 := by exact @_root_.P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.solution G _ H _ K _ hK
