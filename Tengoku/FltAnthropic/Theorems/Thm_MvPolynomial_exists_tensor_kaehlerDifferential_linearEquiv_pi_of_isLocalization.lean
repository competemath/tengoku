import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P]
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K] :
    ∃ e : K ⊗[P] Ω[P⁄R] ≃ₗ[K] (Fin n → K),
      ∀ a : MvPolynomial (Fin n) R,
        e ((1 : K) ⊗ₜ[P] KaehlerDifferential.D R P (algebraMap (MvPolynomial (Fin n) R) P a)) =
          fun i => algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv i a) := by exact @_root_.P2MW.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization.solution R _ n M P _ _ _ _ _ K _ _ _ _
