import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.exists_ringHom_extend_of_isAlgClosed
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by exact @_root_.P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.solution L Ω _ _ _ R φ
