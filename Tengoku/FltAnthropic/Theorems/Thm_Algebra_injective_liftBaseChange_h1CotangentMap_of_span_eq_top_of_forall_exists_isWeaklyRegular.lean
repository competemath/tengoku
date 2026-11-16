import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

/--
@isnad1 id=injectiv.2h4v.s12.412a5d302ae6 from=translated src=- shape=98c38695 vocab=a5fbbea3
-/
theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (s : Set T) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, ∃ (ι : Type w') (x : ι → Localization.Away g) (f : List (MvPolynomial ι S)),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) ∧
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) =
        Ideal.ofList f ∧
      ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by exact @_root_.P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.solution R _ S _ _ T _ _ _ _ _ s hs H
