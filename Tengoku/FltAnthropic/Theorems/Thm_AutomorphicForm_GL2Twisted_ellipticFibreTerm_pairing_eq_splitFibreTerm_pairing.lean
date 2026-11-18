import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import Tengoku.Seed.RingTheory.Polynomial.Chebyshev
import Tengoku.Seed.Analysis.SpecialFunctions.Arcosh
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AutomorphicForm.GL2Twisted Polynomial

theorem
AutomorphicForm.GL2Twisted.ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
    (k : ℕ) (hk : 2 ≤ k) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)) := by exact @_root_.P2MW.S_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing.solution k hk r T hr hT
