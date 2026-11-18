import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_basis_tateOort_two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_basis_tateOort_two.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v
theorem HopfAlgebra.exists_basis_tateOort_two {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H] (hrank : Module.finrank R H = 2) :
    ∃ (e : Module.Basis (Fin 2) R H) (a b : R),
      e 0 = 1 ∧ a * b = 2 ∧ Coalgebra.counit (R := R) (e 1) = 0 ∧ e 1 * e 1 = a • e 1 ∧
      Coalgebra.comul (R := R) (e 1) = e 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] e 1 - b • (e 1 ⊗ₜ[R] e 1) ∧
      HopfAlgebra.antipode R (e 1) = e 1 := by exact @_root_.P2MW.S_HopfAlgebra_exists_basis_tateOort_two.solution R _ H _ _ _ _ hrank
