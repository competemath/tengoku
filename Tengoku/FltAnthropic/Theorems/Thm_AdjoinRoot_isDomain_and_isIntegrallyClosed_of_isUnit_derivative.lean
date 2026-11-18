import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open Polynomial in

theorem AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (f : R[X]) (hfm : f.Monic) (hfi : Irreducible f)
    (hu : IsUnit (AdjoinRoot.mk f (derivative f))) :
    IsDomain (AdjoinRoot f) ∧ IsIntegrallyClosed (AdjoinRoot f) := by exact @_root_.P2MW.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative.solution R _ _ _ f hfm hfi hu
