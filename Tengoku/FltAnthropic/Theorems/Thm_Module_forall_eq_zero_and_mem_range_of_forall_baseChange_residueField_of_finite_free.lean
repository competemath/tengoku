import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : ∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0,
      (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K (i + 1)),
      (δ (i + 1)).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
        z ∈ LinearMap.range ((δ i).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) :
    (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by exact @_root_.P2MW.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free.solution R _ _ n K _ _ _ _ hbdd δ hdd h0 hS
