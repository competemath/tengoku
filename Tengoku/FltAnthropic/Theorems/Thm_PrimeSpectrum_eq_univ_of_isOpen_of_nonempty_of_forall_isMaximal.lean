import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by exact @_root_.P2MW.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.solution A _ _ U hU hne htrans
