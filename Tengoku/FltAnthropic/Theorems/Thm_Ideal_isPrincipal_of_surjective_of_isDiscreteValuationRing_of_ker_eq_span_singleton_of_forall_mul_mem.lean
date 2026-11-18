import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=isprinci.3h5v.s8.4d5e19b4fc3d from=translated src=- shape=923b6f53 vocab=0f795401
-/
theorem Ideal.isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) (hf : Function.Surjective f) (t : R) (hker : RingHom.ker f = Ideal.span {t})
    (P : Ideal R) (hP : ∀ r : R, t * r ∈ P → r ∈ P) :
    Submodule.IsPrincipal P := by exact @_root_.P2MW.S_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem.solution R _ _ _ S _ _ _ f hf t hker P hP
