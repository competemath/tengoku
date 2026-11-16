import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorPushPull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_pairwiseDisjoint_fiber.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by
  intro v₁ _ v₂ _ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
  exact hne ((Place.mem_fiber.mp hw₁).symm.trans (Place.mem_fiber.mp hw₂))
