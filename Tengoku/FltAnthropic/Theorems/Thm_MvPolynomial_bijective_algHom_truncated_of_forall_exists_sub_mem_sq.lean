import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=bijectiv.1h4v.s15.8690a7339f38 from=translated src=- shape=e318c77a vocab=7727b657
-/
theorem MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (θ : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
    (hθ : ∀ j : Fin N, ∃ t, θ t - Ideal.Quotient.mk _ (MvPolynomial.X j) ∈
      (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k))) ^ 2) :
    Function.Bijective θ := by exact @_root_.P2MW.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq.solution k _ N M θ hθ
