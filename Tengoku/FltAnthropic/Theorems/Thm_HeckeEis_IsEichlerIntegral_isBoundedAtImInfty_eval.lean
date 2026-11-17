import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

/--
@isnad1 id=isbounde.6h4v.s12.3c96ea02002f from=translated src=- shape=31ac93e5 vocab=1116fcba
-/
theorem HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by exact @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.solution n g G hG h hh hper hhol hbdd hT
