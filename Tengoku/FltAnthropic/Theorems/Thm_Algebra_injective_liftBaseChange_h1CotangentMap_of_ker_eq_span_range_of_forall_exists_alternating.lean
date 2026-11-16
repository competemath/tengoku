import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

/--
@isnad1 id=injectiv.3h7v.s11.b415986bf721 from=translated src=- shape=9fdea496 vocab=d09c289d
-/
theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    {ι : Type w'} (x : ι → T)
    (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T))
    {n : ℕ} (f : Fin n → MvPolynomial ι S)
    (hf : RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T) =
      Ideal.span (Set.range f))
    (hsyz : ∀ c : Fin n → MvPolynomial ι S, ∑ j, c j * f j = 0 →
      ∃ d : Fin n → Fin n → MvPolynomial ι S,
        (∀ j, d j j = 0) ∧ (∀ j l, d j l = -d l j) ∧ ∀ j, c j = ∑ l, f l * d j l) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by exact @_root_.P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.solution R _ S _ _ T _ _ _ _ _ ι x hx n f hf hsyz
