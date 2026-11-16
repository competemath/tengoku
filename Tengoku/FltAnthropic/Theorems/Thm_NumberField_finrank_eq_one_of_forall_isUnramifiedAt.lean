import Tengoku.Seed.NumberTheory.NumberField.Discriminant.Different
import Tengoku.Seed.RingTheory.DedekindDomain.Different
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped NumberField in
theorem NumberField.finrank_eq_one_of_forall_isUnramifiedAt
    (K : Type*) [Field K] [NumberField K]
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 := by exact @_root_.P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.solution K _ _ H
