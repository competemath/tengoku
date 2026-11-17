import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=ex.2h7v.s7.b965ce5b5367 from=translated src=- shape=d6ed08c8 vocab=f06b81db
-/
theorem solution
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H) (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by
  refine ⟨pullback (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q),
    pullback.fst (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q), inferInstance, fun ψ => ⟨fun h => ?_, fun ⟨ψ', hψ'⟩ => ?_⟩⟩
  · refine ⟨pullback.lift ψ (ψ ≫ u) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  · have hc := pullback.condition (f := pullback.lift u v (hu.trans hv.symm)) (g := pullback.diagonal q)
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q q) hc
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q q) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [← hψ', Category.assoc, Category.assoc, h1, h2]
