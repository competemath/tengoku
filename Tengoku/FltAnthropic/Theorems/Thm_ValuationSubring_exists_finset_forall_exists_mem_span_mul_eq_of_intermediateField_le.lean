import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.5h8v.s11.57f308270504 from=translated src=- shape=94a61d2c vocab=cc093fb0
-/
theorem ValuationSubring.exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
    {k L : Type*} [Field k] [Field L] [Algebra k L] [CharZero k] (A : ValuationSubring L)
    (K₀ K' : IntermediateField k L) [FiniteDimensional k ↥K₀] [FiniteDimensional k ↥K'] (hK : K₀ ≤ K')
    (C : Subring L) (hCK₀ : ∀ c : L, c ∈ C ↔ c ∈ A ∧ c ∈ K₀) [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (C' : Subring L) (hC'K' : ∀ c : L, c ∈ C' ↔ c ∈ A ∧ c ∈ K')
    (t : L) (htC' : t ∈ C') (htinv : t⁻¹ ∉ C') :
    ∃ G : Finset L, (↑G ⊆ (C' : Set L)) ∧
      ∀ c : L, c ∈ C' → ∃ y z : L, y ∈ Submodule.span ↥C (G : Set L) ∧ z ∈ Submodule.span ↥C (G : Set L) ∧
        z ∈ C' ∧ z⁻¹ ∈ C' ∧ z ≠ 0 ∧ c * z = y := by exact @_root_.P2MW.S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.solution k L _ _ _ _ A K₀ K' _ _ hK C hCK₀ _ _ C' hC'K' t htC' htinv
