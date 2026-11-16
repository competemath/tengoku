import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation
import Tengoku.FltAnthropic.P2M.Sol.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem AffineDilatation.nonempty_algEquiv_mvPolynomial_sum
    {R : Type u} [CommRing R] (π : R) (hπ : IsSMulRegular R π) (σ : Type v) (τ : Type v) :
    ∃ e : AffineDilatation.Ring
          (Ideal.span (insert (MvPolynomial.C π) (Set.range fun j : τ => (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R))))
          (MvPolynomial.C π) ≃ₐ[R] MvPolynomial (σ ⊕ τ) R,
      (∀ i : σ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X (Sum.inl i)) ∧
      (∀ j : τ, e (AffineDilatation.divElem _ (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j))
          (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))) = MvPolynomial.X (Sum.inr j)) ∧
      (∀ j : τ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inr j))) =
          MvPolynomial.C π * MvPolynomial.X (Sum.inr j)) := by exact @_root_.P2MW.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.solution R _ π hπ σ τ
