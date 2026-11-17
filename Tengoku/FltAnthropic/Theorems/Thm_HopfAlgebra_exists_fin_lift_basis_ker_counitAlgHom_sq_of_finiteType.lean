import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.0h2v.s12.5aac4493504a from=translated src=- shape=9b6a52bb vocab=c231abbc
-/
theorem HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) := by exact @_root_.P2MW.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.solution K _ A _ _ _
