import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LaurentPolynomial_uniqueFactorizationMonoid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LaurentPolynomial_uniqueFactorizationMonoid.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open LaurentPolynomial

universe u

theorem LaurentPolynomial.uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] := by exact @_root_.P2MW.S_LaurentPolynomial_uniqueFactorizationMonoid.solution R _ _ _
