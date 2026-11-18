import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

/--
@isnad1 id=dvd.3h4v.s12.e6033d9bebf6 from=translated src=- shape=88ed308b vocab=36cf611f
-/
theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z)
    (n : ℤ) (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by exact @_root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.solution Γ hdet F τ hF n hn
