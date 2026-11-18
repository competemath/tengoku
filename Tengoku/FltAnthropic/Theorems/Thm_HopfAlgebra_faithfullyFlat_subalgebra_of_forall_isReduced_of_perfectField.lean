import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

/--
@isnad1 id=faithful.4h4v.s13.faea8b3e514f from=translated src=- shape=42637607 vocab=929d5af4
-/
theorem HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (hred : ∀ K' : Subalgebra k H,
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) →
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') → K'.FG → IsReduced ↥K' →
      Module.FaithfullyFlat ↥K' H)
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    Module.FaithfullyFlat ↥K H := by exact @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField.solution k _ _ p _ _ H _ _ _ hred K hΔ hS hfg
