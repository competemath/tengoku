import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddCommGroup_natCard_torsionBy_prod_eq_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=eq.0h3v.s8.e217218e5e73 from=translated src=- shape=f28c3c2b vocab=6d73fe48
-/
theorem AddCommGroup.natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by exact @_root_.P2MW.S_AddCommGroup_natCard_torsionBy_prod_eq_mul.solution A B _ _ N
