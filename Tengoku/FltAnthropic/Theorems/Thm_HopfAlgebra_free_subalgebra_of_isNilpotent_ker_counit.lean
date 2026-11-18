import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val))) :
    Module.Free ↥K H := by exact @_root_.P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.solution k _ H _ _ K hΔ hS hnil
