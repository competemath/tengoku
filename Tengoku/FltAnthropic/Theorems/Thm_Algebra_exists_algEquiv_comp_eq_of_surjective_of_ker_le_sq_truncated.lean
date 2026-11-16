import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Algebra.exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (e M : ℕ)
    (α β : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    (hαk : RingHom.ker α ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2)
    (hβk : RingHom.ker β ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2) :
    ∃ θ : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) ≃ₐ[k]
        (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)),
      β.comp (θ : _ →ₐ[k] _) = α := by exact @_root_.P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.solution k _ C _ _ _ _ e M α β hα hβ hαk hβk
