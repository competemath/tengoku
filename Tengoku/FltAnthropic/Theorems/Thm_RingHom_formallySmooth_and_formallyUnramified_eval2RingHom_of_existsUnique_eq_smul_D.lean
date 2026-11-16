import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    {A S : Type} [CommRing A] [CommRing S] (i : A →+* S) (hi : i.FormallySmooth) (t : S)
    (hdt : letI : Algebra A S := i.toAlgebra;
      ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified := by exact @_root_.P2MW.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D.solution A S _ _ i hi t hdt
