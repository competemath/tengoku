import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_choose_two_le_of_basis_ker_linearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_choose_two_le_of_basis_ker_linearCombination.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators

/--
@isnad1 id=le.1h5v.s9.96103c8826b2 from=translated src=- shape=54b3a68f vocab=7c2dc511
-/
theorem IsLocalRing.choose_two_le_of_basis_ker_linearCombination
    {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (σ : Fin m → R)
    (hσ : ∀ c : Fin m → R, ∑ i, c i * σ i ∈ IsLocalRing.maximalIdeal R ^ 2 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal R)
    {ρ : ℕ} (η : Module.Basis (Fin ρ) R (LinearMap.ker (Fintype.linearCombination R σ))) :
    m.choose 2 ≤ ρ := by exact @_root_.P2MW.S_IsLocalRing_choose_two_le_of_basis_ker_linearCombination.solution R _ _ m σ hσ ρ η
