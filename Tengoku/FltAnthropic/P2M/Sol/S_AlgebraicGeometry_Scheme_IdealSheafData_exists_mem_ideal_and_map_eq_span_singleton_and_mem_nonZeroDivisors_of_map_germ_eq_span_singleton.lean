import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_mem_ideal_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_germ_eq_span_singleton.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_mem_ideal_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_germ_eq_span_singleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

/--
@isnad1 id=ex.3h5v.s16.bee69817f98a from=translated src=- shape=b2eb70aa vocab=28b1a251
-/
theorem solution
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (x : ↥X) (hx : x ∈ (U : X.Opens))
    (π : X.presheaf.stalk x) (hgen : (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom = Ideal.span {π})
    (hπ : π ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃ g : Γ(X, U), g ∈ I.ideal U ∧
      (I.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) g} ∧
      algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by  classical
  letI alg : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hx⟩

  let e : X.presheaf.stalk x ≃ₐ[Γ(X, U)] Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
    IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  have halg : (algebraMap Γ(X, U) (X.presheaf.stalk x)) = (X.presheaf.germ (U : X.Opens) x hx).hom := rfl
  have hcomp : (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) =
      e.toRingEquiv.toRingHom.comp (X.presheaf.germ (U : X.Opens) x hx).hom := by
    ext s
    rw [RingHom.comp_apply, ← halg]
    exact (e.commutes s).symm

  have hgen' : (I.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)) =
      Ideal.span {e π} := by
    rw [hcomp, ← Ideal.map_map, hgen, Ideal.map_span, Set.image_singleton]
    rfl
  have hπ' : e π ∈ nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, map_eq_zero_iff _ e.injective] at hy
    rw [(mem_nonZeroDivisors_iff_right.mp hπ) y' hy, map_zero]
  obtain ⟨g, hg, h1, h2⟩ := Ideal.exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton
    (I.ideal U) (e π) hgen' hπ'
  exact ⟨g, hg, h1, h2⟩
