import Tengoku.SingularityCompleteLean.Singularity.NorthSouthPingPong
import Tengoku.SingularityCompleteLean.Singularity.CompactBoundary
import Tengoku.SingularityCompleteLean.Singularity.DilationOrbit
import Tengoku.Seed.Analysis.Normed.Group.Bounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform north--south dynamics of a hyperbolic dilation

The compact boundary action is x ↦ exp(t) x, fixing zero and infinity.
A compact subset of the real chart is bounded, while the complement of a
neighborhood of zero is bounded away from zero. Exponential growth then gives
uniform convergence towards infinity outside every neighborhood of zero.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups

namespace Singularity

/-- The compact boundary formula for a diagonal matrix at a finite point.
@isnad1 id=eq.0h2v.s7.fa02ce3a865f from=translated src=- shape=fcb845f7 vocab=9a809446
-/
theorem compactBoundary_dilation_coe (t x : ℝ) :
    dilationMatrix t • (x : OnePoint ℝ) = (Real.exp t * x : ℝ) := by
  rw [compactBoundary_smul_finite _ _ (by simp [dilationMatrix]),
    realBoundaryMobius_dilationMatrix]

/-- Every diagonal dilation fixes the point at infinity.
@isnad1 id=eq.0h1v.s7.a626965660b6 from=translated src=- shape=4dfbab66 vocab=fae1590f
-/
theorem compactBoundary_dilation_infty (t : ℝ) :
    dilationMatrix t • (∞ : OnePoint ℝ) = ∞ := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ (dilationMatrix t)) • (∞ : OnePoint ℝ) = _
  rw [OnePoint.smul_infty_eq_ite]
  change (if (dilationMatrix t) 1 0 = 0 then (∞ : OnePoint ℝ) else
    ((dilationMatrix t) 0 0 / (dilationMatrix t) 1 0 : ℝ)) = ∞
  simp [dilationMatrix]

/-- A neighborhood of infinity contains every real point outside a sufficiently large interval.
@isnad1 id=ex.1h1v.s6.1a3ff95f7d1a from=translated src=- shape=7708094e vocab=59b8ed92
-/
theorem compactBoundary_nhds_infty_bound (U : Set (OnePoint ℝ)) (hU : U ∈ nhds ∞) :
    ∃ R : ℝ, 0 < R ∧ ∞ ∈ U ∧ ∀ x : ℝ, R < |x| → (x : OnePoint ℝ) ∈ U := by
  obtain ⟨K, ⟨hclosed, hcompact⟩, hKU⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨R, hR, mem_of_mem_nhds hU, fun x hx => hKU (Or.inl ?_)⟩
  refine ⟨x, ?_, rfl⟩
  intro hxK
  have h := hbound x hxK
  rw [Real.norm_eq_abs] at h
  exact (not_le_of_gt hx) h

/-- A neighborhood of zero contains a real interval around zero.
@isnad1 id=ex.1h1v.s6.600f971625cf from=translated src=- shape=5079f4d7 vocab=b3defaa4
-/
theorem compactBoundary_nhds_zero_bound (V : Set (OnePoint ℝ))
    (hV : V ∈ nhds ((0 : ℝ) : OnePoint ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → (x : OnePoint ℝ) ∈ V := by
  have hpre : ((↑) : ℝ → OnePoint ℝ) ⁻¹' V ∈ nhds (0 : ℝ) :=
    OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hV
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hpre
  exact ⟨ε, hε, fun x hx => he (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx)⟩

/-- Positive dilations have uniform north--south dynamics on the full compact boundary.
@isnad1 id=uniformn.1h1v.s6.62e2fbf1197d from=translated src=- shape=617d1d6e vocab=4752c3a6
-/
theorem dilationMatrix_northSouth {t : ℝ} (ht : 0 < t) :
    UniformNorthSouth (dilationMatrix t) (∞ : OnePoint ℝ) ((0 : ℝ) : OnePoint ℝ) := by
  intro U hU V hV
  obtain ⟨R, hR, hinfty, hbound⟩ := compactBoundary_nhds_infty_bound U hU
  obtain ⟨ε, hε, hsmall⟩ := compactBoundary_nhds_zero_bound V hV
  have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ht)
  filter_upwards [htend.eventually (eventually_gt_atTop (R / ε))] with n hn
  intro x hx
  have hpow : dilationMatrix t ^ n = dilationMatrix ((n : ℝ) * t) := by
    simpa using (dilationMatrix_zpow t (n : ℤ)).symm
  rw [hpow]
  cases x with
  | infty => simpa only [compactBoundary_dilation_infty] using hinfty
  | coe x =>
    rw [compactBoundary_dilation_coe]
    apply hbound
    have hεx : ε ≤ |x| := le_of_not_gt (fun h => hx (hsmall x h))
    have hexp : 0 < Real.exp ((n : ℝ) * t) := Real.exp_pos _
    rw [abs_mul, abs_of_pos hexp]
    exact ((div_lt_iff₀ hε).mp hn).trans_le (mul_le_mul_of_nonneg_left hεx hexp.le)

end Singularity
