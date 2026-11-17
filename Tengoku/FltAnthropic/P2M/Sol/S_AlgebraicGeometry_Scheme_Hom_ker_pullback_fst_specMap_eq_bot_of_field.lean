import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=eq.0h5v.s7.8b3c6f5e8330 from=translated src=- shape=7823bcd2 vocab=229538ea
-/
theorem solution
    {k₀ : Type} [Field k₀] {Bb : Type} [CommRing Bb] [Nontrivial Bb] (ψ : k₀ →+* Bb)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) :
    (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker = ⊥ := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [isDominant_iff]
    have hr : Set.range (Spec.map (CommRingCat.ofHom ψ)).base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y⟩ := (inferInstance : Nonempty (PrimeSpectrum Bb))
      exact ⟨y, Subsingleton.elim _ _⟩
    rw [DenseRange, hr]
    exact dense_univ
  haveI : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom ψ)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : Flat t := inferInstance
  exact (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker_eq_bot
