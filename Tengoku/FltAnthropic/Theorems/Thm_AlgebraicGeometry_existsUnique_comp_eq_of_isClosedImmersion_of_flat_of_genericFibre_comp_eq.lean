import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ Z)
    (hψK : ψK ≫ ι = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ ι = φ := by exact @_root_.P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq.solution R _ _ K _ _ _ X Y Z f _ ι _ φ ψK hψK
