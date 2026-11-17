import Tengoku.SingularityCompleteLean.Singularity.CayleyMetric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Disk limits at finite real boundary points

The Cayley formula extends continuously to every real boundary coordinate, and
its boundary restriction is injective. No geometric Martin identification is
used in these elementary boundary-coordinate statements.
-/

noncomputable section
open Filter
open scoped Topology UpperHalfPlane
namespace Singularity

def realBoundaryCayley (ξ : ℝ) : ℂ := ((ξ : ℂ) - Complex.I) / ((ξ : ℂ) + Complex.I)

/--
@isnad1 id=ne.0h1v.s4.952e4014531f from=translated src=- shape=ff3278d8 vocab=b6df9cf2
-/
theorem realBoundaryCayley_denominator_ne_zero (ξ : ℝ) : (ξ : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi

/--
@isnad1 id=injectiv.0h0v.s2.cbdd0609ecb9 from=translated src=- shape=54c8eceb vocab=2185648a
-/
theorem realBoundaryCayley_injective : Function.Injective realBoundaryCayley := by
  intro ξ η h
  unfold realBoundaryCayley at h
  have he := (div_eq_div_iff (realBoundaryCayley_denominator_ne_zero ξ)
    (realBoundaryCayley_denominator_ne_zero η)).mp h
  have hp : ((ξ : ℂ) - (η : ℂ)) * Complex.I = 0 := by linear_combination he / 2
  exact Complex.ofReal_injective (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right Complex.I_ne_zero))

/-- Convergence to a finite real point implies convergence to its disk boundary coordinate.
@isnad1 id=tendsto.1h4v.s6.c44e5e5be9c0 from=translated src=- shape=7a28574a vocab=16b333aa
-/
theorem halfPlaneCayley_tendsto_real {α : Type*} {l : Filter α} (z : α → ℍ) (ξ : ℝ)
    (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => halfPlaneCayley (z n)) l (𝓝 (realBoundaryCayley ξ)) :=
  (hz.sub tendsto_const_nhds).div (hz.add tendsto_const_nhds)
    (realBoundaryCayley_denominator_ne_zero ξ)

end Singularity
