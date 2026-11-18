import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial

/--
@isnad1 id=mem.7h8v.s12.1f81893a6aab from=translated src=- shape=96715da7 vocab=759e4c1a
-/
theorem MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (k : ℕ) (hk : m ≤ k) (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous k)
    (h : ℓ * f ∈ Ideal.span (Set.range F)) : f ∈ Ideal.span (Set.range F) := by exact @_root_.P2MW.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span.solution n m g K _ F hF ℓ hℓ hcol hrel k hk f hf h
