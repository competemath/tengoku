import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct

universe u
theorem Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B]
    (n : ℕ) (hn : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin n → R')) := by exact @_root_.P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.solution R _ B _ _ _ _ n hn
