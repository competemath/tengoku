import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (x : (MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
    (hx₁ : x ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)))
    (hx₂ : x ∉ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k))) ^ 2) :
    Nonempty (((MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)) ⧸ Ideal.span ({x} : Set _)) ≃ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1))) := by exact @_root_.P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.solution k _ N M x hx₁ hx₂
