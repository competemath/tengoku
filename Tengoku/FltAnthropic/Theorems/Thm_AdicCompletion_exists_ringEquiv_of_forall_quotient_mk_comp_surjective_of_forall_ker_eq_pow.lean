import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))
    (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k) :
    ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, e (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by exact @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.solution R S _ _ I J f hsurj hker
