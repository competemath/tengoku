import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=isintegr.1h3v.s7.2bd6e36c171c from=translated src=- shape=72053461 vocab=cf6545c2
-/
theorem IsIntegral.of_forall_isPrime_isIntegral_quotient_mk
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] (a : A)
    (h : ∀ (p : Ideal A), p.IsPrime → IsIntegral R (Ideal.Quotient.mk p a)) :
    IsIntegral R a := by exact @_root_.P2MW.S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk.solution R A _ _ _ a h
