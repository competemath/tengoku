import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.1h4v.s9.1e516c0a670b from=translated src=- shape=4fc86ae3 vocab=d8fe247d
-/
theorem Submodule.natCard_torsionBy_quotient_eq_pow_finrank
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by exact @_root_.P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.solution K _ _ V _ _ L _ _ n hn
