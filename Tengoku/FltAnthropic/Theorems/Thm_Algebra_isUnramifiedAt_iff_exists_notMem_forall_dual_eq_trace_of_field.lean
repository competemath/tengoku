import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=iff.0h3v.s8.1585a5be3e04 from=translated src=- shape=2fbdcfa9 vocab=526a06aa
-/
theorem Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
    (κ : Type u) [Field κ] (T : Type u) [CommRing T] [Algebra κ T] [Module.Finite κ T]
    (Q : Ideal T) [Q.IsPrime] :
    Algebra.IsUnramifiedAt κ Q ↔
      ∃ s ∉ Q, ∀ φ : Module.Dual κ T, ∃ x : T, ∀ y : T, φ (s * y) = Algebra.trace κ T (x * y) := by exact @_root_.P2MW.S_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field.solution κ _ T _ _ _ Q _
