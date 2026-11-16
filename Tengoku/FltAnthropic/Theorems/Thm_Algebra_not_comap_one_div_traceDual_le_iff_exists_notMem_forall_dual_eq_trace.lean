import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem Algebra.not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime] :
    ¬ ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L) ≤ P) ↔
      ∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y) := by exact @_root_.P2MW.S_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace.solution A _ _ _ _ K _ _ _ B _ _ _ _ _ _ L _ _ _ _ _ _ _ _ P _
