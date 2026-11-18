import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P] :
    Algebra.FormallySmooth R P ∧ Module.Free P Ω[P⁄R] ∧ Module.Finite P Ω[P⁄R] := by exact @_root_.P2MW.S_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization.solution R _ n M P _ _ _ _ _
