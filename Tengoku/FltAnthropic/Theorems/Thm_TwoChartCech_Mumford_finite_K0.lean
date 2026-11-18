import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Tengoku.Seed.RingTheory.Noetherian.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_TwoChartCech_Mumford_finite_K0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_TwoChartCech_Mumford_finite_K0.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

open scoped TensorProduct

/--
@isnad1 id=finite.0h4v.s10.87e1ab97e14a from=translated src=- shape=c31830e2 vocab=6940f3e4
-/
theorem TwoChartCech.Mumford.finite_K0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Finite R (TwoChartCech.Mumford.K0 d) := by exact @_root_.P2MW.S_TwoChartCech_Mumford_finite_K0.solution R _ _ C0 C1 _ _ _ _ d _ _
