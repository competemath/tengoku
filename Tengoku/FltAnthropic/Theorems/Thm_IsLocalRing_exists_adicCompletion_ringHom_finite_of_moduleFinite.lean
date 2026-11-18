import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem IsLocalRing.exists_adicCompletion_ringHom_finite_of_moduleFinite
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    ∃ φ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ r : R, φ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap R S r)) ∧
      φ.Finite ∧
      (Function.Injective (algebraMap R S) → Function.Injective φ) ∧

      ∃ e : TensorProduct R (AdicCompletion (IsLocalRing.maximalIdeal R) R) S ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal S) S,
        (∀ x : AdicCompletion (IsLocalRing.maximalIdeal R) R, e (x ⊗ₜ[R] (1 : S)) = φ x) ∧
        (∀ s : S, e ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] s) =
          algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s) := by exact @_root_.P2MW.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite.solution R S _ _ _ _ _ _ _ _
