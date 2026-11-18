import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=isreduce.0h4v.s6.a6bb5484a7b0 from=translated src=- shape=8df6b58c vocab=6ca5177f
-/
theorem AlgebraicGeometry.isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsReduced X := by exact @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing.solution R _ _ K _ _ _ X f _ _
