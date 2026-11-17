import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=existsun.1h5v.s8.4c11a1fe2e2b from=translated src=- shape=1eec74b7 vocab=2296dc8b
-/
theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [IsSeparated f]
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by exact @_root_.P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated.solution R _ _ _ K _ _ _ X f _ _ x hx
