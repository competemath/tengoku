import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.MvPolynomial hiding exists_skew_eq_sum_mul_X_of_sum_mul_X_eq_zero

/--
@isnad1 id=mem.4h7v.s11.a8e355fc756f from=translated src=- shape=8de28c67 vocab=1345e3a2
-/
theorem MvPolynomial.relation_mem_span_of_forall_isHomogeneous_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hspan : ∀ w : MvPolynomial (Fin (n + 1)) K, w.IsHomogeneous m → w ∈ Submodule.span K (Set.range F))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by exact @_root_.P2MW.S_MvPolynomial_relation_mem_span_of_forall_isHomogeneous_mem_span.solution n m g K _ F hF hspan d c hc hcF
