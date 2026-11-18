import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_TwoChartCech_Mumford_bijective_kerMapBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

open scoped TensorProduct

/--
@isnad1 id=bijectiv.0h5v.s17.aafa82f7719b from=translated src=- shape=ea4bb07d vocab=3c7b2571
-/
theorem TwoChartCech.Mumford.bijective_kerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) := by exact @_root_.P2MW.S_TwoChartCech_Mumford_bijective_kerMapBaseChange.solution R _ C0 C1 _ _ _ _ _ d _ A _ _
