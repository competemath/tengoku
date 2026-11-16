import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.3h8v.s14.c75bc5d71169 from=translated src=- shape=ffe2757d vocab=08865226
-/
theorem Algebra.exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (M : ℕ)
    (r : ℕ) (β : (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hβ : Function.Surjective β)
    (gβ : Fin r → (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)))
    (hgβ : RingHom.ker β = Ideal.span (Set.range gβ))
    (N : ℕ) (α : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) :
    ∃ h : Fin N → (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)),
      RingHom.ker α = Ideal.span (Set.range h) := by exact @_root_.P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.solution k _ C _ _ _ _ M r β hβ gβ hgβ N α hα
