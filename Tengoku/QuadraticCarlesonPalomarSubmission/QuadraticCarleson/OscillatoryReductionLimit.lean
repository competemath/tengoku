/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OscillatoryReductionMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The regular difference between quadratic and ordinary Hilbert truncations

For every bounded compactly supported measurable input, every observation
point, and every nonzero modulation, subtracting the ordinary Hilbert
truncation leaves a convergent quantity. The only classical principal-value
existence issue is therefore that of the ordinary Hilbert transform.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

/--
@isnad1 id=tendsto.0h3v.s5.6f303964d2ab from=translated src=- shape=0432a853 vocab=13eaf344
-/
theorem tendsto_smallPhaseKernel (lam ρ t : ℝ) :
    Tendsto (fun ε : ℝ ↦ smallPhaseKernel lam ε ρ t) (𝓝[>] 0)
      (𝓝 (smallPhaseKernel lam 0 ρ t)) := by
  by_cases ht : t = 0
  · subst t
    simp only [smallPhaseKernel, sq, mul_zero, phase_zero, sub_self, Complex.ofReal_zero,
      zero_div, ite_self]
    exact tendsto_const_nhds
  · have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < |t| :=
      (eventually_lt_nhds (abs_pos.mpr ht)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with ε hε
    simp only [smallPhaseKernel, hε, abs_pos.mpr ht, true_and]

/--
@isnad1 id=tendsto.1h3v.s7.552e09713829 from=translated src=- shape=0e27ef69 vocab=1a09c72a
-/
theorem tendsto_smallPhaseIntegral (lam : ℝ) (hlam : lam ≠ 0)
    (f : L0Infinity) (x : ℝ) :
    Tendsto (fun ε : ℝ ↦
      ∫ y, smallPhaseKernel lam ε (innerRadius lam hlam) (x - y) * f y) (𝓝[>] 0)
      (𝓝 (∫ y, smallPhaseKernel lam 0 (innerRadius lam hlam) (x - y) * f y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y ↦ ((2 * Real.pi) / innerRadius lam hlam) * ‖f y‖)
  · filter_upwards with ε
    exact (((measurable_smallPhaseKernel lam ε _).comp
      (measurable_const.sub measurable_id)).mul f.measurable_toFun).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (smallPhaseKernel_norm_le lam ε hlam (x - y))
      (norm_nonneg (f y))
  · exact f.integrable.norm.const_mul _
  · filter_upwards with y
    exact (tendsto_smallPhaseKernel lam (innerRadius lam hlam) (x - y)).mul_const (f y)

noncomputable def regularRemainder (lam : ℝ) (hlam : lam ≠ 0)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  paperOscillatoryAction lam hlam f x +
    (∫ y, cutoffBoundaryKernel lam (innerRadius lam hlam) (x - y) * f y) -
    quadraticHilbertTrunc 0 (innerRadius lam hlam) f x +
    ∫ y, smallPhaseKernel lam 0 (innerRadius lam hlam) (x - y) * f y

/-- An unconditional truncation-limit theorem on the paper's entire test
domain. No existence assertion about a Hilbert principal value is assumed.
@isnad1 id=tendsto.1h3v.s6.d94f42a8bfb3 from=translated src=- shape=00b79cc7 vocab=dfc248c7
-/
theorem tendsto_quadraticHilbertTrunc_sub_hilbert
    (lam : ℝ) (hlam : lam ≠ 0) (f : L0Infinity) (x : ℝ) :
    Tendsto (fun ε : ℝ ↦ quadraticHilbertTrunc lam ε f x - quadraticHilbertTrunc 0 ε f x)
      (𝓝[>] 0) (𝓝 (regularRemainder lam hlam f x)) := by
  have hlim := (tendsto_smallPhaseIntegral lam hlam f x).const_add
    (paperOscillatoryAction lam hlam f x +
      (∫ y, cutoffBoundaryKernel lam (innerRadius lam hlam) (x - y) * f y) -
      quadraticHilbertTrunc 0 (innerRadius lam hlam) f x)
  apply hlim.congr'
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < innerRadius lam hlam :=
    (eventually_lt_nhds (innerRadius_pos lam hlam)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with ε hε hερ
  rw [quadraticHilbertTrunc_eq_oscillatory_reduction lam ε hlam hε hερ.le f x]
  ring

/-- The principal value exists precisely when the ordinary Hilbert
principal value exists. This is an equivalence, not an existence assumption
inserted into the oscillatory reduction.
@isnad1 id=iff.1h3v.s5.560575782adc from=translated src=- shape=fef5d6eb vocab=228a0c09
-/
theorem exists_quadraticPrincipalValue_iff_hilbert
    (lam : ℝ) (hlam : lam ≠ 0) (f : L0Infinity) (x : ℝ) :
    (∃ z : ℂ, HasQuadraticPrincipalValue lam f x z) ↔
      ∃ z : ℂ, HasQuadraticPrincipalValue 0 f x z := by
  have hd := tendsto_quadraticHilbertTrunc_sub_hilbert lam hlam f x
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - regularRemainder lam hlam f x, ?_⟩
    have hh := hz.sub hd
    unfold HasQuadraticPrincipalValue
    convert hh using 1
    funext ε
    ring
  · rintro ⟨z, hz⟩
    refine ⟨z + regularRemainder lam hlam f x, ?_⟩
    have hh := hz.add hd
    unfold HasQuadraticPrincipalValue
    convert hh using 1
    funext ε
    ring

/-- A single ordinary Hilbert principal value supplies all nonzero
quadratic principal values at the same point.
@isnad1 id=iff.0h2v.s5.d7a23c55e765 from=translated src=- shape=66915ec0 vocab=222542ee
-/
theorem forall_nonzero_principalValue_iff_hilbert (f : L0Infinity) (x : ℝ) :
    (∀ lam : {lam : ℝ // lam ≠ 0}, ∃ z : ℂ, HasQuadraticPrincipalValue lam.1 f x z) ↔
      ∃ z : ℂ, HasQuadraticPrincipalValue 0 f x z := by
  constructor
  · intro h
    exact (exists_quadraticPrincipalValue_iff_hilbert 1 (by norm_num) f x).mp
      (h ⟨1, by norm_num⟩)
  · intro h lam
    exact (exists_quadraticPrincipalValue_iff_hilbert lam.1 lam.2 f x).mpr h

end OscillatoryReduction
end QuadraticCarleson
