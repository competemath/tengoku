import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_isDirectLimit_of_finitePresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_isDirectLimit_of_finitePresentation.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.exists_isDirectLimit_of_finitePresentation
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (S : ι → Type u) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, Algebra R (S i))
      (_ : ∀ i, Algebra.FinitePresentation R (S i))
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) (c : ∀ i, S i →ₐ[R] A)
      (_ : DirectedSystem S fun i j h => ⇑(t i j h)),
      IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i) := by exact @_root_.P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation.solution R _ A _ _
