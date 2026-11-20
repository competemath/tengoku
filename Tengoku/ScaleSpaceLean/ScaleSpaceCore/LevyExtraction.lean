/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Tightness
import Tengoku.Seed.MeasureTheory.Measure.Prokhorov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `thm:increments-levy`, part three: the test function and the limiting pair

Home: line:thm:increments-levy

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, third step of the proof
("the limit").

`NullArray` produced `∫ (1 - cos ωx) dΠ_n → g_{s,t}(ω)` with each `Π_n` finite,
and `Tightness` produced the two bounds that hold uniformly in `n`. What
remains is to extract a limiting pair `(a, ν)` from `(Π_n)`, and the obstruction is that the
masses `Π_n(ℝ) = n` diverge: mass piles up at the origin, and that pile is exactly the Gaussian
coefficient `a` the pair is allowed to have.

## The weighting and the test function

`ϱ_n := (1 ∧ x²)\,\widetilde\Pi_n` on `[0,∞)`, where `\widetilde\Pi_n` is the image of `Π_n`
under `x ↦ |x|`. The weight vanishes at the origin at the rate that turns piled-up mass into a
Gaussian coefficient, and `Tightness.lean` bounds the masses of the `ϱ_n` and their tails
uniformly.

Under the weighting the observable `1 - cos ωx` becomes

  `k_ω(x) = (1 - cos ωx)/(1 ∧ x²)`,   `k_ω(0) = ω²/2`,

with a removable singularity at the origin whose filled-in value is what turns mass at `0` into
`a ω²`. It is written here in the closed form

  `levyTest ω x = (ω²/2)\,\mathrm{sinc}(ωx/2)^2\,(1 ∨ x²)`,

which needs no `if`: the half-angle identity `1 - \cos u = 2\sin^2(u/2)` makes it equal to
`k_ω` off the origin, `\mathrm{sinc}` is continuous everywhere, and the removable singularity
is filled in by `\mathrm{sinc}(0) = 1` rather than by a case split. **This is a divergence from
the blueprint's route and it is a simplification, not a change of the mathematics**: the
blueprint fills the singularity by hand and appeals to `1 - \cos u = u²/2 + O(u^4)`, and the
closed form makes both the continuity and the boundedness one-liners.

## The extraction

Mathlib's Prokhorov theorem for finite measures,
`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`, is applied with the *monotone*
compacts `K_n = [0, n+1]` and the tolerances `u_n` supplied by the tightness bound. It returns a
cluster point rather than a limit, since `FiniteMeasure ℝ` carries no metrizability instance;
nothing is lost, because every observable used is a continuous real function of the measure that
already converges along the full sequence, and a convergent sequence has one cluster value
(`eq_of_mapClusterPt`, Paper I's). The same constraint that gives tightness also gives that the
cluster point charges no negative half-line, so no portmanteau argument is needed for the
folding.

twin: `Hemigroup.CascadeCore.exists_limit_measure` (`Hemigroup/LevyLimit.lean`) and
`Hemigroup.CascadeCore.exponent_hasLevyRep` (`Hemigroup/LevyTriple.lean`). The causal
development compactifies `[0,∞]` by `1 - e^{-x}` and needs no tightness at all; here the test
function oscillates at infinity and does not extend to a compactification, so tightness replaces
the change of variable. That is the one new idea of the node.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/LevyExtraction.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology NNReal

/-! ## The test function -/

/-- `k_ω(x) = (1 - \cos ωx)/(1 ∧ x²)`, with the removable singularity at the origin filled in
by its limit `ω²/2`, written in a closed form that makes the filling automatic.-/
noncomputable def levyTest (ω x : ℝ) : ℝ :=
  ω ^ 2 / 2 * Real.sinc (ω * x / 2) ^ 2 * max 1 (x ^ 2)

lemma continuous_levyTest (ω : ℝ) : Continuous (levyTest ω) := by
  unfold levyTest
  exact ((continuous_const.mul ((Real.continuous_sinc.comp (by fun_prop)).pow 2)).mul
    (continuous_const.max (continuous_pow 2)))

@[simp] lemma levyTest_zero (ω : ℝ) : levyTest ω 0 = ω ^ 2 / 2 := by
  simp [levyTest]

/-- **The defining identity**: `k_ω(x)\,(1 ∧ x²) = 1 - \cos ωx`, at *every* `x`, the origin
included (where both sides vanish).-/
theorem levyTest_mul_min (ω x : ℝ) :
    levyTest ω x * min 1 (x ^ 2) = 1 - Real.cos (ω * x) := by
  have hmaxmin : max 1 (x ^ 2) * min 1 (x ^ 2) = x ^ 2 := by
    rcases le_total (1 : ℝ) (x ^ 2) with h | h
    · rw [max_eq_right h, min_eq_left h, mul_one]
    · rw [max_eq_left h, min_eq_right h, one_mul]
  have hhalf : 1 - Real.cos (ω * x) = 2 * Real.sin (ω * x / 2) ^ 2 := by
    have := Real.sin_sq_eq_half_sub (ω * x / 2)
    have hdouble : 2 * (ω * x / 2) = ω * x := by ring
    rw [hdouble] at this
    linarith
  rw [levyTest, mul_assoc, hmaxmin, hhalf]
  rcases eq_or_ne (ω * x / 2) 0 with h | h
  · have hzero : ω * x = 0 := by linarith
    have hsq : ω ^ 2 * x ^ 2 = 0 := by nlinarith [hzero]
    rw [h, Real.sinc_zero, Real.sin_zero]
    linear_combination hsq / 2
  · have hω : ω ≠ 0 := by
      intro h0
      exact h (by rw [h0]; ring)
    have hx : x ≠ 0 := by
      intro h0
      exact h (by rw [h0]; ring)
    rw [Real.sinc_of_ne_zero h]
    field_simp

lemma levyTest_nonneg (ω x : ℝ) : 0 ≤ levyTest ω x := by
  refine mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ?_
  exact le_trans zero_le_one (le_max_left _ _)

/-- The test function is bounded by `\max(ω²/2, 2)`: below `1` the weight is `x²` and the sinc
factor is at most `1`; above it the identity reads `k_ω = 1 - \cos ωx`.-/
theorem levyTest_le (ω x : ℝ) : levyTest ω x ≤ max (ω ^ 2 / 2) 2 := by
  rcases le_total (1 : ℝ) (x ^ 2) with h | h
  · have hmin : min 1 (x ^ 2) = 1 := min_eq_left h
    have := levyTest_mul_min ω x
    rw [hmin, mul_one] at this
    refine le_trans (le_of_eq this) (le_trans ?_ (le_max_right _ _))
    linarith [Real.neg_one_le_cos (ω * x)]
  · have hmax : max 1 (x ^ 2) = 1 := max_eq_left h
    have hsinc : Real.sinc (ω * x / 2) ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one (ω * x / 2)
      nlinarith [abs_nonneg (Real.sinc (ω * x / 2)), sq_abs (Real.sinc (ω * x / 2))]
    refine le_trans ?_ (le_max_left _ _)
    rw [levyTest, hmax, mul_one]
    nlinarith [sq_nonneg ω, hsinc]

/-- The test function as a bounded continuous function, the shape weak convergence needs.-/
noncomputable def levyTestBdd (ω : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (levyTest ω) (continuous_levyTest ω)
    (max (ω ^ 2 / 2) 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (levyTest_nonneg ω x)]
      exact levyTest_le ω x)

@[simp] lemma levyTestBdd_apply (ω x : ℝ) : levyTestBdd ω x = levyTest ω x := rfl

/-! ## A cluster point is pinned by what already converges

twin: `Hemigroup.eq_of_mapClusterPt`, verbatim. The extraction below produces a *cluster* point
rather than a limit, because the space of finite measures on `ℝ` carries no metrizability
instance in Mathlib; nothing is lost, since every observable used converges along the full
sequence.
-/

/-- If `Φ ∘ P` converges and `a` is a cluster point of `P`, then `Φ a` is the limit.-/
theorem eq_of_mapClusterPt {α : Type*} [TopologicalSpace α] {P : ℕ → α} {a : α} {Φ : α → ℝ}
    {L : ℝ} (hcl : MapClusterPt a atTop P) (hΦ : Continuous Φ)
    (hlim : Tendsto (fun n => Φ (P n)) atTop (𝓝 L)) : Φ a = L :=
  eq_of_nhds_neBot ((hcl.continuousAt_comp hΦ.continuousAt).clusterPt.mono hlim)

/-! ## The weighted partition measures -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

/-- `\widetilde\Pi_n`, the image of `Π_n` under `x ↦ |x|`.-/
noncomputable def foldedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  (partitionMeasure μ s t n).map (fun x => |x|)

/-- `ϱ_n = (1 ∧ x²)\,\widetilde\Pi_n`, the weighted approximant.-/
noncomputable def weightedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  (foldedPartition μ s t n).withDensity fun x => ENNReal.ofReal (min 1 (x ^ 2))

/-! ## The two uniform bounds, in the shape Prokhorov asks for -/

/-! ## The limiting measure

Mathlib's Prokhorov theorem for finite measures is applied with the monotone compacts
`K_n = [0, n+1]` and the tolerances the tightness bound supplies. It returns a cluster point,
and the same membership condition that gives tightness also gives that the cluster point charges
no negative half-line — so the folding survives the limit without a portmanteau argument.
-/

/-- The value of a `FiniteMeasure` on a set, as a real number.-/
lemma finiteMeasure_apply_coe (ν : FiniteMeasure ℝ) (A : Set ℝ) :
    ((ν A : ℝ≥0) : ℝ) = (ν : Measure ℝ).real A := by
  rw [measureReal_def, ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]

end ScaleSpace
